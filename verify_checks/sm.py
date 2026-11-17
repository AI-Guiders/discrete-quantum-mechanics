"""verify_checks.sm — extracted from verify_principles"""
from __future__ import annotations

import math
import re
from pathlib import Path

import torch

from mt_ca.cauchy_riemann import cauchy_riemann_energy
from mt_ca.config import MConfig
from mt_ca.metrics import field_amplitude, norm_drift, total_norm_squared
from mt_ca.seeds import SeedClass, make_seed
from mt_ca.simulator import LatticeFluidSimulator
from mt_ca.linear import linear_step, linear_step_local_ca
from mt_ca.reversible import evolve_canonical
from mt_ca.spinor import (
    arg_phase_defect,
    apply_saturating_phase_collision,
    saturating_phase,
    holonomy_zeta,
    spinor_neighbor_sum,
    su2_apply,
)
from mt_ca.update import apply_heisenberg_floor, vacuum_phase, wrapped_phase_diff


def check_compton_electron(device: str = "cpu") -> dict:
    from mt_ca.si_constants import SI, compton_wavelength, reduced_compton_wavelength

    m_e = SI.m_e_CODATA
    lambda_bar = reduced_compton_wavelength(m_e)
    lambda_c = compton_wavelength(m_e)
    codata_lambda_c = 2.426310238e-12
    rel = abs(lambda_c - codata_lambda_c) / codata_lambda_c
    ok = rel < 1e-6
    return {
        "id": "Compton_e",
        "lambda_bar_m": lambda_bar,
        "lambda_C_m": lambda_c,
        "codata_rel_err": rel,
        "ok": ok,
    }

def check_electron_anchor(device: str = "cpu") -> dict:
    from mt_ca.m_to_t import electron_planck_cell_anchor

    row = electron_planck_cell_anchor()
    ok = row["rel_err"] < 1e-9
    return {"id": "M2T_e", "f_geometry": row["f_geometry"], "rel_err": row["rel_err"], "ok": ok}

def check_saturation_bc(device: str = "cpu") -> dict:
    """§8.4.2-C′′′ — live D_★ strain vs Newton; hinge = mismatch, not stitch."""
    from mt_ca.si_constants import SI
    from mt_ca.strain_metric import saturation_core_probe

    alg = SI.saturation_bc_row()
    live = saturation_core_probe(size=64, device=device)
    # Pass = hinge confirmed (near ≫ Newton), algebra↔field agree on order
    hinge = live["near_over_newton"] > 100.0 and alg["near_over_newton"] > 100.0
    agree = abs(math.log10(live["near_over_newton"] + 1e-30) - math.log10(alg["near_over_newton"] + 1e-30)) < 0.5
    ok = hinge and agree
    return {
        "id": "SatBC_Cppp",
        "h_star_near": live["h_star_near"],
        "h_star_newton": live["h_star_newton"],
        "near_over_newton": live["near_over_newton"],
        "alg_near_over_newton": alg["near_over_newton"],
        "far_R2_ratio": live["far_R2_ratio"],
        "far_R8_ratio": live["far_R8_ratio"],
        "ok": ok,
        "note": "C′′′: |h_near/h_Newton|≫1 on A5-floor; far 1/R not claimed",
    }

def check_higgs_mass(device: str = "cpu") -> dict:
    from mt_ca.si_constants import SI

    del device
    row = SI.higgs_mass_row()
    ok = (
        abs(row["m_H_bare_GeV"] - row["m_H_direct_GeV"]) / row["m_H_bare_GeV"] < 1e-12
        and abs(row["m_H_over_v_bare"] - 0.5) < 1e-12
        and row["N_hier"] == 8.0
        and abs(row["delta_lambda_stack"] - 8.0 * row["delta_lambda_quantum"]) < 1e-15
        and row["m_H_rel_err"] < 0.001
        and row["m_H_bare_rel_err"] < 0.03
    )
    return {
        "id": "Higgs_mass",
        "m_H_bare_GeV": row["m_H_bare_GeV"],
        "m_H_GeV": row["m_H_GeV"],
        "v_GeV": row["v_GeV"],
        "lambda_bare": row["lambda_bare"],
        "lambda_quartic": row["lambda_quartic"],
        "delta_lambda_stack": row["delta_lambda_stack"],
        "m_H_rel_err": row["m_H_rel_err"],
        "ok": ok,
        "note": row["note"],
    }

def check_proton_mass(device: str = "cpu") -> dict:
    from mt_ca.si_constants import KAPPA_FCC_1TICK, N12_FCC_CAUSAL_LINKS, SI

    del device
    row = SI.proton_mass_row()
    delta_pack = (KAPPA_FCC_1TICK ** 2) / float(N12_FCC_CAUSAL_LINKS)
    ok = (
        abs(row["m_p_over_m_H_bare"] - row["alpha_preferred"]) < 1e-12
        and abs(row["m_p_bare_GeV"] - row["alpha_preferred"] * row["m_H_bare_GeV"]) < 1e-12
        and abs(row["kappa_FCC"] - KAPPA_FCC_1TICK) < 1e-15
        and row["N12"] == float(N12_FCC_CAUSAL_LINKS)
        and abs(row["delta_pack"] - delta_pack) < 1e-15
        and abs(row["pack_stack_factor"] - (1.0 + delta_pack)) < 1e-15
        and abs(row["m_p_GeV"] - row["m_p_bare_GeV"] * row["pack_stack_factor"]) < 1e-12
        and row["m_p_bare_rel_err"] < 0.05
        and row["m_p_rel_err"] < 0.005
        and bool(row.get("floor2_cliques_and_moments_ok", False))
    )
    return {
        "id": "Proton_mass",
        "m_p_bare_GeV": row["m_p_bare_GeV"],
        "m_p_GeV": row["m_p_GeV"],
        "m_H_bare_GeV": row["m_H_bare_GeV"],
        "v_GeV": row["v_GeV"],
        "delta_pack": row["delta_pack"],
        "mu_p_pred_muN": row["mu_p_pred_muN"],
        "mu_n_pred_muN": row["mu_n_pred_muN"],
        "mu_isoscalar_sum_pred_muN": row["mu_isoscalar_sum_pred_muN"],
        "m_p_bare_rel_err": row["m_p_bare_rel_err"],
        "m_p_rel_err": row["m_p_rel_err"],
        "ok": ok,
        "note": row["note"],
    }

def check_electron_mass(device: str = "cpu") -> dict:
    from mt_ca.si_constants import PLANCK_CELL, SI

    del device
    row = SI.electron_mass_row()
    n_phi = float(PLANCK_CELL.N_phi)
    a2 = row["alpha_preferred"] ** 2
    ok = (
        row["N_phi"] == n_phi
        and n_phi == 13.0
        and abs(row["m_e_bare_GeV"] - a2 * row["m_H_bare_GeV"] / n_phi) < 1e-18
        and abs(row["m_e_GeV"] - a2 * row["m_H_GeV"] / n_phi) < 1e-18
        and row["m_e_bare_rel_err"] < 0.02
        and row["m_e_rel_err"] < 0.005
    )
    return {
        "id": "Electron_mass",
        "m_e_bare_GeV": row["m_e_bare_GeV"],
        "m_e_GeV": row["m_e_GeV"],
        "m_H_GeV": row["m_H_GeV"],
        "N_phi": row["N_phi"],
        "f_geom": row["f_geom"],
        "m_e_bare_rel_err": row["m_e_bare_rel_err"],
        "m_e_rel_err": row["m_e_rel_err"],
        "ok": ok,
        "note": row["note"],
    }

def check_neutrino_mass(device: str = "cpu") -> dict:
    from mt_ca.si_constants import PLANCK_CELL, SI

    del device
    row = SI.neutrino_mass_row()
    n_phi = float(PLANCK_CELL.N_phi)
    n_hier = float(row["N_hier"])
    a = row["alpha_preferred"]
    expected = (a**5) * (2.0 * row["m_H_GeV"]) / (n_hier * n_phi) * 1e9
    bare = (a**5) * row["v_GeV"] / (n_hier * n_phi) * 1e9
    bridge = (a**3) * row["m_e_GeV"] / (n_hier / 2.0) * 1e9
    ok = (
        row["N_phi"] == n_phi
        and n_phi == 13.0
        and n_hier == 8.0
        and abs(row["m_nu_atm_eV"] - expected) / expected < 1e-12
        and abs(row["m_nu_atm_bare_eV"] - bare) / bare < 1e-12
        and abs(row["m_nu_atm_eV"] - bridge) / bridge < 1e-12
        and row["bridge_equals_stack"] < 1e-12
        and row["m_nu_atm_bare_rel_err"] < 0.03
        and row["m_nu_atm_rel_err"] < 0.005
    )
    return {
        "id": "Neutrino_mass",
        "m_nu_atm_bare_eV": row["m_nu_atm_bare_eV"],
        "m_nu_atm_eV": row["m_nu_atm_eV"],
        "m_nu_sol_lemma_eV": row["m_nu_sol_lemma_eV"],
        "m_nu_lightest_lemma_eV": row["m_nu_lightest_lemma_eV"],
        "N_hier": row["N_hier"],
        "N_phi": row["N_phi"],
        "m_nu_atm_bare_rel_err": row["m_nu_atm_bare_rel_err"],
        "m_nu_atm_rel_err": row["m_nu_atm_rel_err"],
        "ok": ok,
        "note": row["note"],
    }

def check_neutron_mass(device: str = "cpu") -> dict:
    from mt_ca.si_constants import SI

    del device
    row = SI.neutron_mass_row()
    ok = (
        row["k"] == 2
        and abs(row["delta_GeV"] - 2.0 * row["m_e_GeV"]) < 1e-18
        and abs(row["m_n_GeV"] - (row["m_p_GeV"] + row["delta_GeV"])) < 1e-18
        and row["beta_downhill"] is True
        and row["m_n_GeV"] > row["threshold_m_p_plus_m_e_GeV"]
        and abs(row["m_n_GeV"] - (row["m_p_GeV"] + 2.0 * row["m_e_GeV"])) < 1e-18
        and row["m_n_rel_err"] < 0.01
    )
    return {
        "id": "Neutron_mass",
        "m_n_GeV": row["m_n_GeV"],
        "m_p_GeV": row["m_p_GeV"],
        "m_e_GeV": row["m_e_GeV"],
        "k": row["k"],
        "delta_GeV": row["delta_GeV"],
        "beta_downhill": row["beta_downhill"],
        "m_n_rel_err": row["m_n_rel_err"],
        "delta_rel_err": row["delta_rel_err"],
        "ok": ok,
        "note": row["note"],
    }


def check_annihilation_pdg_tau_strict(device: str = "cpu") -> dict:
    """§5.0.3 — strict PDG τ: upstream m_e, ortho/para ratio, anti-CODATA circularity."""
    from mt_ca.si_constants import SI

    row = SI.annihilation_pdg_tau_strict_row(device=device)
    en_up = float(row.get("E_n_upstream", 0.0))
    ok = (
        bool(row["checks_ok"])
        and bool(row["anti_circular_mass"])
        and bool(row["tracks_mass_error"])
        and float(row["ortho_para_ratio_rel_err"]) <= 0.27
        and bool(row.get("codata_not_sole_winner", False))
        and en_up <= 2.5
    )
    return {
        "id": "Annihilation_PDG_tau_strict",
        "tau_rel_err_upstream": row["tau_rel_err_upstream"],
        "tau_rel_err_CODATA_m_e": row["tau_rel_err_CODATA_m_e"],
        "ortho_para_ratio_rel_err": row["ortho_para_ratio_rel_err"],
        "E_n_upstream": en_up,
        "E_n_CODATA_m_e_path": row.get("E_n_CODATA_m_e_path"),
        "derivation_closed": row["derivation_closed"],
        "ok": ok,
        "note": row["note"],
    }


def check_annihilation_pdg_tau_bridge(device: str = "cpu") -> dict:
    """§5.0.3 — PDG para-Ps τ vs QED leading and N_c/α⁵ ladder (not collision τ_M)."""
    from mt_ca.si_constants import SI

    row = SI.annihilation_pdg_tau_row(device=device)
    ok = (
        bool(row["checks_ok"])
        and bool(row["qed_matches_PDG"])
        and bool(row["ladder_matches_PDG"])
        and bool(row["collision_clock_separate_from_PDG"])
    )
    return {
        "id": "Annihilation_PDG_tau_bridge",
        "tau_qed_rel_err": row["tau_qed_rel_err"],
        "tau_ladder_rel_err": row["tau_ladder_rel_err"],
        "tau_M_over_tau_PDG": row["tau_M_over_tau_PDG"],
        "derivation_closed": row["derivation_closed"],
        "ok": ok,
        "note": row["note"],
    }


def check_annihilation_m_t_bundle(device: str = "cpu") -> dict:
    """§5.0.3 — floor1 pm coarse dipole + Annihilation_T_stats (linked instruments)."""
    from mt_ca.annihilation_m_t_bundle import run_annihilation_m_t_bundle

    row = run_annihilation_m_t_bundle(device=device)
    ok = (
        bool(row["checks_ok"])
        and bool(row["link_dual_front_both_paths"])
        and bool(row["link_shared_dipole_instrument"])
    )
    return {
        "id": "Annihilation_M_T_bundle",
        "m_peaks": row["m_floor1_pm"]["pm_peaks_on_delta"],
        "t_peaks": row["t_head_on"]["peaks_on_delta"],
        "link_dual_front_both_paths": row["link_dual_front_both_paths"],
        "link_shared_dipole_instrument": row["link_shared_dipole_instrument"],
        "ok": ok,
        "note": row["note"],
    }


def check_annihilation_t_stats(device: str = "cpu") -> dict:
    """§5.0.3 T-layer: lattice τ_M, dipole 2γ proxy, ensemble ⟨dσ/dΩ⟩ isotropy."""
    from mt_ca.annihilation_t_stats import annihilation_t_stats_probe

    row = annihilation_t_stats_probe(size=160, steps=64, block=8, ensemble=12, device=device)
    ok = (
        bool(row["back_to_back_proxy"])
        and bool(row["axis_tracks_pi"])
        and bool(row["ensemble_isotropic"])
    )
    return {
        "id": "Annihilation_T_stats",
        "probe_path": row["probe_path"],
        "tick_focus": row["tick_focus"],
        "tau_M_s": row["tau_M_s"],
        "tau_M_over_tau_PDG": row["tau_M_over_tau_PDG"],
        "peaks_on_delta": row["peaks_on_delta"],
        "elongation_delta": row["elongation_delta"],
        "ensemble_axis_hist_cv": row["ensemble_axis_hist_cv"],
        "mean_axis_tracking_err_rad": row["mean_axis_tracking_err_rad"],
        "back_to_back_proxy": row["back_to_back_proxy"],
        "ensemble_isotropic": row["ensemble_isotropic"],
        "axis_tracks_injection": row["axis_tracks_injection"],
        "axis_tracks_pi": row["axis_tracks_pi"],
        "ok": ok,
        "note": row["note"],
    }


def check_sm_vortex_clique_atlas(device: str = "cpu") -> dict:
    """§5.0.4-C — Unified SM vortex & clique atlas (K_2=12, K_3=24, K_4=8, CKM, PMNS, μ_p, μ_n, τ_μ, τ_n)."""
    from mt_ca.si_constants import SI

    del device
    row = SI.floor2_baryon_cliques_and_moments_row()
    ok = bool(row["checks_ok"])
    return {
        "id": "SM_vortex_clique_atlas",
        "cliques_K_m": row["cliques_K_m"],
        "mu_p_pred_muN": row["mu_p_pred_muN"],
        "mu_n_pred_muN": row["mu_n_pred_muN"],
        "m_mu_over_m_e_pred": row["m_mu_over_m_e_pred"],
        "m_tau_over_m_e_pred": row["m_tau_over_m_e_pred"],
        "ckm_gamma_deg": row["ckm_gamma_deg"],
        "pmns_sin2_12": row["pmns_sin2_12"],
        "pmns_sin2_23": row["pmns_sin2_23"],
        "pmns_sin2_13": row["pmns_sin2_13"],
        "tau_mu_s": row["tau_mu_s"],
        "tau_n_s": row["tau_n_s"],
        "ok": ok,
        "note": "§5.0.4-C: K_2=12, K_3=24, K_4=8, K_>=5=0; 3 orthogonal planes; μ_p=67/24, μ_n=-23/12; Koide; CKM/PMNS; τ_μ, τ_n",
    }


def check_periodic_and_fcc_graph_dirac(device: str = "cpu") -> dict:
    """Floor 3 / Chemistry — Periodic Table periods, Pb-208, N=184 island, discrete Gauss edges, and FCC Graph Dirac."""
    from mt_ca.si_constants import SI

    del device
    row = SI.periodic_table_and_fcc_graph_dirac_row()
    ok = bool(row["ok"])
    return {
        "id": "Chem_periodic_and_fcc_dirac",
        "noble_gas_closures": row["noble_gas_closures"],
        "nuclear_magic_all": row["nuclear_magic_all"],
        "terminal_stable_Pb208": row["terminal_stable_Pb208"],
        "island_of_stability_N184": row["island_of_stability_N184"],
        "z_core_zero_crossing": row["z_core_zero_crossing"],
        "z_core_continuum_diving": row["z_core_continuum_diving"],
        "e_1s_shell_at_137": row["e_1s_shell_at_137"],
        "ok": ok,
        "note": row["note"],
    }


def check_four_channel_nilpotent_cascade(device: str = "cpu") -> dict:
    """§4.1.1-HL(H4b) — 4-channel nilpotent cascade M_chan = I_4 + N_nil (N_nil^3=0), exact inverse, and gas dynamics."""
    from mt_ca.si_constants import SI

    del device
    row = SI.four_channel_nilpotent_cascade_and_gas_row()
    ok = bool(row["ok"])
    return {
        "id": "Compute_four_channel_cascade",
        "cascade_determinant": row["cascade_determinant"],
        "cascade_inverse_diag_24": row["cascade_inverse_diag_24"],
        "channel_retention_ticks": row["channel_retention_ticks"],
        "two_step_vortex_amplitude": row["two_step_vortex_amplitude"],
        "reconstructed_source_s1": row["reconstructed_source_s1"],
        "prandtl_numbers": row["prandtl_numbers"],
        "critical_mach_number": row["critical_mach_number"],
        "ok": ok,
        "note": row["note"],
    }


def check_bio_frustration_and_three_life_types(device: str = "cpu") -> dict:
    """Floor 3 / Biology — Geometric frustration arccos(1/3)+arccos(-1/3)=pi and 5:6:7 scale law for 3 planetary life types."""
    from mt_ca.si_constants import SI

    del device
    row = SI.bio_frustration_and_three_life_types_row()
    ok = bool(row["ok"])
    return {
        "id": "Bio_frustration_three_life_types",
        "frustration_gap_deg": row["frustration_gap_deg"],
        "scale_invariants_5_6_7": row["scale_invariants_5_6_7"],
        "backbone_bond_angstrom": row["backbone_bond_angstrom"],
        "membrane_tm18_angstrom": row["membrane_tm18_angstrom"],
        "ok": ok,
        "note": row["note"],
    }


def check_local_gates_solid_neuro_photo(device: str = "cpu") -> dict:
    """Compute / Bio / Chem — Local Heisenberg (81=3^4 deadband) & Pauli (256-tick mirror, 2-tick S_1 delay) gates, Cauchy/FQHE, Hodgkin-Huxley, photosynthesis, and 12=7+5 harmony."""
    import torch
    from mt_ca.config import MConfig
    from mt_ca.fixed_point import encode_spinor, leapfrog_invert
    from mt_ca.laplacian import _FCC_OFFSETS
    from mt_ca.projected_collision import (
        apply_heisenberg_floor_signed,
        pauli_phi_int,
        projected_step_fixed,
    )
    from mt_ca.seeds import universe_iv_9bit_spinor_3d
    from mt_ca.si_constants import SI

    row = SI.local_gates_solid_neuro_photo_row()
    dev = torch.device(device if (device == "cuda" and torch.cuda.is_available()) else "cpu")
    cfg_on = MConfig.for_stencil("fcc", heisenberg_floor=True, pauli_exclusion=True)
    cfg_h_off = MConfig.for_stencil("fcc", heisenberg_floor=False, pauli_exclusion=True)

    # 1. Verify exact 81 = 3^4 local Heisenberg deadband on Z_512 and bitwise reversibility on canonical 3D seed
    n_ring = 1 << cfg_on.phase_bits
    half_ring = n_ring >> 1
    phi_all = torch.arange(-half_ring, half_ring, dtype=torch.int64, device=dev)
    phi_gated = apply_heisenberg_floor_signed(phi_all, int(row["heisenberg_deadband_states"] + 1) // 2)
    deadband_sim = int((phi_gated == 0).sum().item())

    grid_n = 2 * cfg_on.phase_bits - 2  # 16
    z0 = universe_iv_9bit_spinor_3d(grid_n, grid_n, grid_n, device=dev)
    f0 = encode_spinor(z0, frac_bits=cfg_on.frac_bits, mod_bits=cfg_on.mod_bits)

    fc_on, fp_on = f0.clone(), f0.clone()
    fc_off, fp_off = f0.clone(), f0.clone()
    impulses = []
    n_test_steps = cfg_on.frac_bits + 2  # 8 steps
    for _ in range(n_test_steps):
        fc_on, fp_on, imp_on = projected_step_fixed(fc_on, fp_on, cfg_on)
        fc_off, fp_off, imp_off = projected_step_fixed(fc_off, fp_off, cfg_h_off)
        impulses.append(imp_on)

    ballistic_cells_h_on = int((impulses[-1].abs().max(dim=-1).values == 0).sum().item())
    ballistic_cells_h_off = int((imp_off.abs().max(dim=-1).values == 0).sum().item())

    # Unwind 8 steps backward to verify 0 bit error
    fc_rev, fp_rev = fc_on.clone(), fp_on.clone()
    for imp in reversed(impulses):
        fp_prev = leapfrog_invert(fp_rev, fc_rev, imp, mod_bits=cfg_on.mod_bits)
        fc_rev, fp_rev = fp_rev, fp_prev
    rev_max_err = int((fc_rev - f0).abs().max().item())

    # 2. Verify 2-tick causal light-cone delay of local Pauli gate for disjoint S_1 parallel spinors
    c = grid_n // 2
    f_curr_p = f0.clone()
    f_past_p = f0.clone()
    f_curr_p[c, c, c] = torch.tensor([28, 8, 28, 8], dtype=torch.int64, device=dev)
    f_past_p[c, c, c] = torch.tensor([20, 4, 20, 4], dtype=torch.int64, device=dev)
    for idx, (dz, dy, dx) in enumerate(_FCC_OFFSETS):
        if idx < len(_FCC_OFFSETS) // 2:
            f_curr_p[c + dz, c + dy, c + dx] = torch.tensor([60, 16, 24, 6], dtype=torch.int64, device=dev)
            f_past_p[c + dz, c + dy, c + dx] = torch.tensor([48, 12, 18, 4], dtype=torch.int64, device=dev)
        else:
            f_curr_p[c + dz, c + dy, c + dx] = torch.tensor([24, 6, 60, 16], dtype=torch.int64, device=dev)
            f_past_p[c + dz, c + dy, c + dx] = torch.tensor([18, 4, 48, 12], dtype=torch.int64, device=dev)

    c13_pts = [(0, 0, 0)] + list(_FCC_OFFSETS)
    pauli_c13_t0 = sum(int(pauli_phi_int(f_curr_p, cfg_on)[c + dz, c + dy, c + dx] > 0) for dz, dy, dx in c13_pts)
    f_curr_p, f_past_p, _ = projected_step_fixed(f_curr_p, f_past_p, cfg_on)
    pauli_c13_t1 = sum(int(pauli_phi_int(f_curr_p, cfg_on)[c + dz, c + dy, c + dx] > 0) for dz, dy, dx in c13_pts)
    f_curr_p, f_past_p, _ = projected_step_fixed(f_curr_p, f_past_p, cfg_on)
    pauli_c13_t2 = sum(int(pauli_phi_int(f_curr_p, cfg_on)[c + dz, c + dy, c + dx] > 0) for dz, dy, dx in c13_pts)

    # 3. Verify 64x64 unitary DFT template-basis bridge and exact Weyl-Schwinger relation U_Q V_P = omega_64^-1 V_P U_Q
    k_p = 1 << cfg_on.frac_bits  # 64
    eye_kp = torch.eye(k_p, dtype=torch.complex128, device=dev)
    u_q = torch.roll(eye_kp, shifts=1, dims=0)
    f_dft = torch.fft.ifft(eye_kp, dim=0) * (float(k_p) ** 0.5)
    v_p = f_dft.conj().T @ u_q @ f_dft
    omega_inv = f_dft[1, 1].conj() * (float(k_p) ** 0.5)
    weyl_comm_err = float((u_q @ v_p - omega_inv * (v_p @ u_q)).abs().max().item())

    ok = (
        bool(row["ok"])
        and deadband_sim == row["heisenberg_deadband_states"]
        and rev_max_err == 0
        and ballistic_cells_h_on > 10 * ballistic_cells_h_off
        and pauli_c13_t0 == 0
        and pauli_c13_t1 == 0
        and pauli_c13_t2 >= 5
        and weyl_comm_err < 1e-14
    )
    return {
        "id": "Local_gates_solid_neuro_photo",
        "heisenberg_deadband_states": deadband_sim,
        "ballistic_cells_h_on_vs_off": (ballistic_cells_h_on, ballistic_cells_h_off),
        "pauli_c13_t0_t1_t2": (pauli_c13_t0, pauli_c13_t1, pauli_c13_t2),
        "weyl_pq_commutator_max_err": weyl_comm_err,
        "info_equiv_macro_cell_bits": row["info_equiv_macro_cell_bits"],
        "neuron_potentials_mv": row["neuron_potentials_mv"],
        "photosynthesis_wavelengths_nm": row["photosynthesis_wavelengths_nm"],
        "ok": ok,
        "note": row["note"],
    }
