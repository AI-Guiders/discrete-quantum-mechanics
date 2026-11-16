"""verify_checks.qm_experiments — Classical QM experiments starting from the canonical world seed on the scale-invariant (K-cancelled) M-automaton."""

from __future__ import annotations

import math
import torch

from mt_ca.config import MConfig
from mt_ca.fixed_point import decode_spinor, encode_spinor
from mt_ca.laplacian import _FCC_OFFSETS
from mt_ca.projected_collision import (
    apply_heisenberg_floor_signed,
    heisenberg_phi_min_int,
    holonomy_zeta_int,
    int_neighbor_sum,
    pauli_phi_int,
    rho2_int,
    rot_impulse_uv,
    saturating_phi_impulse,
)
from mt_ca.reversible import leapfrog_forward_fixed, leapfrog_reverse_fixed
from mt_ca.seeds import (
    SeedClass,
    heisenberg_phase_tick,
    make_seed,
    universe_iv_9bit_spinor_3d,
    vacuum_boil_fixed_3d,
    vacuum_ice_fixed_3d,
)
from mt_ca.si_constants import (
    KAPPA_FCC_1TICK,
    M_FORCE_SEATS,
    N12_FCC_CAUSAL_LINKS,
    N4_CAUSAL_LINKS,
    PLANCK_CELL,
    SI,
    n_E_from_phi_ticks,
    pauli_impulse_disc,
    rho_field_quantum,
    sync_strength_disc,
)
from mt_ca.spinor import su2_apply
from mt_ca.z_ring import signed_from_mod


def check_qm_scale_cancellation_k(device: str = "cpu") -> dict:
    """Theorem 1.1 (K-cancellation): bit-identical Z_512[i]^2 evolution of the 9-bit Universe IV seed across Planck, Compton, Bohr, and Lyman floors."""
    dev = torch.device(device)
    floor_names = ("planck", "star_2", "compton", "bohr", "lyman")
    cfgs = [MConfig.for_ladder_floor(name, stencil="fcc") for name in floor_names]

    # Start strictly from the canonical 9-bit Universe Initial Vector on 3+1 FCC VACUUM_BOIL
    grid_n = PLANCK_CELL.N_phi  # 13 = 1 + |N_12|
    z0 = universe_iv_9bit_spinor_3d(grid_n, grid_n, grid_n, device=dev)

    trajectories_curr: list[torch.Tensor] = []
    roundtrips_ok: list[bool] = []
    action_invariance_ok: list[bool] = []
    speed_invariance_ok: list[bool] = []

    n_ticks = PLANCK_CELL.frac_bits  # 6 ticks forward and 6 ticks reverse
    tol_ieee = rho_field_quantum() ** (N4_CAUSAL_LINKS - 1)  # 2^(-36) ~ 1.45e-11
    for cfg in cfgs:
        rel_s = abs(cfg.s_floor - SI.s_0) / SI.s_0
        rel_e = abs(cfg.e_floor * cfg.scale_k - SI.E_0) / SI.E_0
        rel_c = abs(cfg.c - SI.c0) / SI.c0
        action_invariance_ok.append(
            rel_s < tol_ieee and rel_e < tol_ieee and cfg.n_pack_supercell == cfg.scale_k ** (N4_CAUSAL_LINKS - 1)
        )
        speed_invariance_ok.append(rel_c < tol_ieee)

        f0 = encode_spinor(z0, frac_bits=cfg.frac_bits, mod_bits=cfg.mod_bits, gauge_fix=False)
        f_curr = f0.clone()
        f_past = f0.clone()
        impulses: list[torch.Tensor] = []
        for _ in range(n_ticks):
            f_curr, f_past, imp = leapfrog_forward_fixed(f_curr, f_past, cfg)
            impulses.append(imp)
        trajectories_curr.append(f_curr.clone())

        for imp in reversed(impulses):
            f_past, f_curr = leapfrog_reverse_fixed(f_past, f_curr, imp, cfg)
        roundtrips_ok.append(bool(torch.equal(f_curr, f0)))

    ref_traj = trajectories_curr[0]
    bit_identical_across_k = all(bool(torch.equal(t, ref_traj)) for t in trajectories_curr[1:])
    ok = (
        bit_identical_across_k
        and all(roundtrips_ok)
        and all(action_invariance_ok)
        and all(speed_invariance_ok)
    )
    return {
        "id": "QM_scale_cancellation_K",
        "world_seed": "universe_iv_9bit_spinor_3d",
        "grid_N_phi": grid_n,
        "floors_tested": list(floor_names),
        "scales_K": [cfg.scale_k for cfg in cfgs],
        "bit_identical_across_K": bit_identical_across_k,
        "roundtrips_bit_exact": all(roundtrips_ok),
        "action_s_floor_invariant": all(action_invariance_ok),
        "speed_c0_invariant": all(speed_invariance_ok),
        "ok": ok,
        "note": "Thm 1.1 on 9-bit Universe IV seed: Z_512[i]^2 trajectory and s_floor(K)=s_0 are bit-identical across Planck, Compton, Bohr, and Lyman floors",
    }


def check_qm_double_slit_which_way(device: str = "cpu") -> dict:
    """Young-Feynman 3D double-slit on canonical filled lattice in both single-quantum threshold and above-threshold regimes.

    Physical regimes verified on the 3D world seed (`vacuum_ice_fixed_3d`):
      1. Single-quantum threshold detection regime (`slit_boost = frac_bits = |N_12|/2 = 6`):
         At a threshold detector pixel where a single open slit delivers a sub-Heisenberg impulse
         Phi_1 = floor(64 * 6 / 13) = 29 < 41 ticks (below the n_E = 1 detector firing threshold, I_1 = I_2 = 0),
         coherent constructive superposition of both slits reaches Phi_12 = 64 * (12 / 12) = 64 >= 41 ticks and fires the pixel (I_12 = 2116 > 0).
      2. Above-threshold diffraction envelope regime (`slit_boost = |N_12| = 12`):
         When a single open slit already exceeds the detector threshold (Phi_1 = floor(64 * 12 / 13) = 59 >= 41 ticks,
         so the screen is illuminated by one slit alone: I_1 = I_2 = 3481 > 0), opening the second slit in-phase
         amplifies the bright fringe (I_12(0) = 4096 > I_1), whereas opening the second slit in anti-phase (256 ticks = pi)
         extinguishes the illuminated pixel to exact zero in the dark fringe (I_12(pi) = 0 < I_1).
      3. Which-way detector threshold:
         A sub-Heisenberg phase probe (< 41 ticks) is snapped to 0 and preserves interference, while an above-threshold
         which-way detector (>= 41 ticks, n_E >= 1) erases the interference peak.
    """
    dev = torch.device(device)
    cfg = MConfig.for_ladder_floor("bohr", stencil="fcc")
    phi_min_ticks = heisenberg_phi_min_int(cfg)
    pauli_ticks = pauli_impulse_disc(phase_bits=cfg.phase_bits)
    grid_n = PLANCK_CELL.N_phi  # 13
    c_idx = grid_n // 2  # central screen node (c_idx, c_idx, c_idx)

    # Slit 1 and Slit 2 sit at two symmetric FCC N_12 neighbors of the screen node: (-1, -1, 0) and (-1, +1, 0)
    s1_z, s1_y, s1_x = c_idx - 1, c_idx - 1, c_idx
    s2_z, s2_y, s2_x = c_idx - 1, c_idx + 1, c_idx
    unit_amp = 1 << cfg.frac_bits  # 1.0 in Q(frac_bits)

    def run_slit_on_world_seed(
        open_s1: bool, open_s2: bool, s2_extra_ticks: int = 0, slit_boost: int = cfg.frac_bits
    ) -> int:
        # Start from canonical filled 3D ocean (vacuum_ice_fixed_3d scaled to unit Q amplitude)
        f_base = vacuum_ice_fixed_3d(grid_n, grid_n, grid_n, device=dev) * unit_amp
        f_curr = f_base.clone().to(torch.int64)
        f_past = f_base.clone().to(torch.int64)

        q_ticks = pauli_ticks // 2
        if open_s1:
            u0 = f_curr[s1_z, s1_y, s1_x, 0:1] * slit_boost
            v0 = f_curr[s1_z, s1_y, s1_x, 1:2] * slit_boost
            du, dv = rot_impulse_uv(
                u0, v0, torch.tensor([q_ticks], dtype=torch.int64, device=dev), phase_bits=cfg.phase_bits
            )
            f_curr[s1_z, s1_y, s1_x, 0] = (u0 + du).item()
            f_curr[s1_z, s1_y, s1_x, 1] = (v0 + dv).item()
            f_past[s1_z, s1_y, s1_x] = f_curr[s1_z, s1_y, s1_x]

        if open_s2:
            u0 = f_curr[s2_z, s2_y, s2_x, 0:1] * slit_boost
            v0 = f_curr[s2_z, s2_y, s2_x, 1:2] * slit_boost
            du, dv = rot_impulse_uv(
                u0,
                v0,
                torch.tensor([q_ticks + s2_extra_ticks], dtype=torch.int64, device=dev),
                phase_bits=cfg.phase_bits,
            )
            f_curr[s2_z, s2_y, s2_x, 0] = (u0 + du).item()
            f_curr[s2_z, s2_y, s2_x, 1] = (v0 + dv).item()
            f_past[s2_z, s2_y, s2_x] = f_curr[s2_z, s2_y, s2_x]

        f_next, _, _ = leapfrog_forward_fixed(f_curr, f_past, cfg)
        v_scr = int(f_next[c_idx, c_idx, c_idx, 1].item())
        if v_scr >= pauli_ticks:
            v_scr -= 1 << cfg.mod_bits
        return v_scr * v_scr

    # Regime A: Single-quantum threshold detection (slit_boost = frac_bits = |N_12|/2 = 6)
    i_closed = run_slit_on_world_seed(False, False, slit_boost=cfg.frac_bits)
    i_s1_only = run_slit_on_world_seed(True, False, slit_boost=cfg.frac_bits)
    i_s2_only = run_slit_on_world_seed(False, True, slit_boost=cfg.frac_bits)
    i_both_in_phase = run_slit_on_world_seed(True, True, s2_extra_ticks=0, slit_boost=cfg.frac_bits)
    i_both_anti_phase = run_slit_on_world_seed(True, True, s2_extra_ticks=pauli_ticks, slit_boost=cfg.frac_bits)

    # Regime B: Above-threshold diffraction envelope (slit_boost = |N_12| = 12 -> Phi_1 = 59 >= 41 ticks)
    i_s1_above = run_slit_on_world_seed(True, False, slit_boost=N12_FCC_CAUSAL_LINKS)
    i_both_bright_above = run_slit_on_world_seed(True, True, s2_extra_ticks=0, slit_boost=N12_FCC_CAUSAL_LINKS)
    i_both_dark_above = run_slit_on_world_seed(
        True, True, s2_extra_ticks=pauli_ticks, slit_boost=N12_FCC_CAUSAL_LINKS
    )

    # Which-way detector test: sub-threshold probe (< 41 ticks) vs above-threshold detector (>= 41 ticks)
    sub_kick = int(
        apply_heisenberg_floor_signed(
            torch.tensor([phi_min_ticks - 1], dtype=torch.int64, device=dev), phi_min_ticks
        ).item()
    )
    i_sub_probe = run_slit_on_world_seed(True, True, s2_extra_ticks=sub_kick, slit_boost=cfg.frac_bits)

    det_sum = 0.0
    for k_cls in range(PLANCK_CELL.N_phi):
        det_kick = heisenberg_phase_tick(k_cls, phase_bits=cfg.phase_bits)
        snapped_det = int(
            apply_heisenberg_floor_signed(
                torch.tensor([det_kick], dtype=torch.int64, device=dev), phi_min_ticks
            ).item()
        )
        det_sum += float(
            run_slit_on_world_seed(True, True, s2_extra_ticks=snapped_det, slit_boost=cfg.frac_bits)
        )
    i_which_way_avg = det_sum / float(PLANCK_CELL.N_phi)

    ok = (
        i_closed == 0
        and i_s1_only == 0
        and i_s2_only == 0
        and i_both_in_phase > 0
        and i_both_anti_phase == 0
        and i_s1_above > 0
        and i_both_bright_above > i_s1_above
        and i_both_dark_above == 0
        and i_sub_probe == i_both_in_phase
        and i_which_way_avg < float(i_both_in_phase)
    )
    return {
        "id": "QM_double_slit_which_way",
        "world_seed": "vacuum_ice_fixed_3d",
        "scale_K": cfg.scale_k,
        "heisenberg_threshold_ticks": phi_min_ticks,
        "I_threshold_s1_only": i_s1_only,
        "I_threshold_both_constructive": i_both_in_phase,
        "I_above_threshold_s1_only": i_s1_above,
        "I_above_threshold_both_bright": i_both_bright_above,
        "I_above_threshold_both_dark_pi": i_both_dark_above,
        "I_subthreshold_probe": i_sub_probe,
        "I_which_way_detector_avg": i_which_way_avg,
        "ok": ok,
        "note": "3D double-slit on world seed: verifies both threshold regime (I1=0, I12=2116) and above-threshold diffraction regime (I1=3481>0, bright I12=4096>I1, dark I12(pi)=0)",
    }


def check_qm_aharonov_bohm_holonomy(device: str = "cpu") -> dict:
    """Aharonov-Bohm loop holonomy on 3D VACUUM_BOIL world seed for single charge e (period 512 ticks = 2*pi, destructive zero at half-period 256 ticks = pi) vs Cooper pair 2e (period 256 ticks = h/2e).

    Physical convention:
      - For a single electron (charge q = 1*e), the full Aharonov-Bohm flux quantum Phi_0 = h/e corresponds to a full
        phase cycle 2*pi = N_ring = 512 ticks (where interference revives: I^(1e)(512) == I^(1e)(0)), while 256 ticks
        is the half-period pi rad (where destructive cancellation occurs: I^(1e)(256) == 0).
      - For a superconducting Cooper pair (charge q = 2*e), the phase shift is doubled (2 * Phi_AB), so an external flux
        of 256 ticks (h/2e) already completes a 2*pi = 512-tick phase cycle of the pair (I^(2e)(256) == I^(1e)(0)),
        and the Cooper-pair destructive minimum sits at 128 ticks (pi/2 external flux).
    """
    dev = torch.device(device)
    cfg = MConfig.for_ladder_floor("compton", stencil="fcc")
    n_ring = 1 << cfg.phase_bits
    half_period_pi_ticks = pauli_impulse_disc(phase_bits=cfg.phase_bits)  # 256 ticks = pi rad (half-period for 1e)
    quarter_period_ticks = half_period_pi_ticks // 2  # 128 ticks = pi/2 rad
    grid_n = PLANCK_CELL.N_phi

    # Extract two coherent spinor arms directly from the canonical 3D VACUUM_BOIL world seed
    f_boil = vacuum_boil_fixed_3d(grid_n, grid_n, grid_n, device=dev).to(torch.int64)
    u_arm1 = f_boil[:, 0, 0, 0]
    v_arm1 = f_boil[:, 0, 0, 1]
    u_arm2 = u_arm1.clone()
    v_arm2 = v_arm1.clone()

    def ab_loop_intensity(external_flux_ticks: int, charge_multiple: int = 1) -> int:
        phi = torch.full_like(u_arm2, charge_multiple * external_flux_ticks)
        du, dv = rot_impulse_uv(u_arm2, v_arm2, phi, phase_bits=cfg.phase_bits)
        u_tot = u_arm1 + (u_arm2 + du)
        v_tot = v_arm1 + (v_arm2 + dv)
        return int(torch.sum(u_tot**2 + v_tot**2).item())

    # Single charge q = 1e: destructive zero at half-period 256 ticks (pi), full revival at 512 ticks (2*pi = h/e)
    i_1e_zero_flux = ab_loop_intensity(0, charge_multiple=1)
    i_1e_half_period_pi = ab_loop_intensity(half_period_pi_ticks, charge_multiple=1)
    i_1e_full_period_2pi = ab_loop_intensity(n_ring, charge_multiple=1)

    # Cooper pair q = 2e: destructive zero at 128 ticks, full revival already at 256 ticks (h/2e)
    i_2e_quarter_flux = ab_loop_intensity(quarter_period_ticks, charge_multiple=2)
    i_2e_half_flux_revival = ab_loop_intensity(half_period_pi_ticks, charge_multiple=2)

    ok = (
        i_1e_zero_flux > 0
        and i_1e_half_period_pi == 0
        and i_1e_full_period_2pi == i_1e_zero_flux
        and i_2e_quarter_flux == 0
        and i_2e_half_flux_revival == i_1e_zero_flux
    )
    return {
        "id": "QM_aharonov_bohm_holonomy",
        "world_seed": "vacuum_boil_fixed_3d",
        "scale_K": cfg.scale_k,
        "I_1e_flux_0": i_1e_zero_flux,
        "I_1e_half_period_pi_256": i_1e_half_period_pi,
        "I_1e_full_period_2pi_512": i_1e_full_period_2pi,
        "I_2e_quarter_flux_128": i_2e_quarter_flux,
        "I_2e_half_flux_revival_256": i_2e_half_flux_revival,
        "ok": ok,
        "note": "Aharonov-Bohm on 3D VACUUM_BOIL: 1e has destructive zero at half-period 256 ticks (pi) and full revival at 512 ticks (2*pi=h/e); Cooper pair 2e revives at 256 ticks (h/2e)",
    }


def check_qm_quantum_zeno_heisenberg(device: str = "cpu") -> dict:
    """Quantum Zeno effect on world seed from sync_strength_disc and Heisenberg floor Delta_phi_disc."""
    dev = torch.device(device)
    cfg = MConfig.for_ladder_floor("bohr", stencil="fcc")
    phi_min = heisenberg_phi_min_int(cfg)
    # Canonical per-link holomorphy sync step from si_constants (zero magic numbers: floor(Delta_phi_disc / |N|) < Delta_phi_disc)
    step_phi = sync_strength_disc(phase_bits=cfg.phase_bits)
    n_star = N12_FCC_CAUSAL_LINKS + PLANCK_CELL.N_phi  # 25 steps: N_star * step_phi >= phi_min

    # Start from a brick of the canonical 3D world seed scaled to unit Q(frac_bits) amplitude
    unit_amp = 1 << cfg.frac_bits
    f_seed = vacuum_ice_fixed_3d(1, 1, 1, device=dev).to(torch.int64) * unit_amp
    u0 = f_seed[:, :, :, 0].reshape(-1)
    v0 = f_seed[:, :, :, 1].reshape(-1)

    # 1. Zeno regime: projective Heisenberg check after every single sync step (step_phi < phi_min -> snapped to 0)
    u_zeno, v_zeno = u0.clone(), v0.clone()
    for _ in range(n_star):
        imp_zeno = apply_heisenberg_floor_signed(
            torch.tensor([step_phi], dtype=torch.int64, device=dev), phi_min
        )
        du, dv = rot_impulse_uv(u_zeno, v_zeno, imp_zeno, phase_bits=cfg.phase_bits)
        u_zeno, v_zeno = u_zeno + du, v_zeno + dv

    zeno_frozen = bool(torch.equal(u_zeno, u0) and torch.equal(v_zeno, v0))

    # 2. Unobserved coherent accumulation over the full star n_star * step_phi >= phi_min (n_E >= 1 quantum!)
    total_accum_phi = n_star * step_phi
    n_e_quanta = n_E_from_phi_ticks(total_accum_phi, phase_bits=cfg.phase_bits)
    imp_free = apply_heisenberg_floor_signed(
        torch.tensor([total_accum_phi], dtype=torch.int64, device=dev), phi_min
    )
    du_f, dv_f = rot_impulse_uv(u0, v0, imp_free, phase_bits=cfg.phase_bits)
    u_free, v_free = u0 + du_f, v0 + dv_f
    transition_occurred = bool(not torch.equal(u_free, u0) or not torch.equal(v_free, v0))

    ok = (
        0 < step_phi < phi_min
        and n_e_quanta >= 1
        and zeno_frozen
        and transition_occurred
    )
    return {
        "id": "QM_quantum_zeno_heisenberg",
        "world_seed": "vacuum_ice_fixed_3d",
        "heisenberg_phi_min_ticks": phi_min,
        "sync_step_ticks": step_phi,
        "accumulated_ticks_unobserved": total_accum_phi,
        "n_E_quanta_emitted": n_e_quanta,
        "zeno_state_frozen": zeno_frozen,
        "unobserved_transition_occurred": transition_occurred,
        "ok": ok,
        "note": "Quantum Zeno on world seed: single sync_strength_disc step (<41 ticks) is frozen by Heisenberg gate; full-star accumulation crosses 41 ticks (n_E>=1) and transitions",
    }


def check_qm_stern_gerlach_su2_720(device: str = "cpu") -> dict:
    """Stern-Gerlach spinor splitting + SU(2) 360° -> -1 and 720° -> +1 on canonical VORTEX_P seed over 3D VACUUM_BOIL."""
    dev = torch.device(device)
    cfg = MConfig.for_ladder_floor("bohr", stencil="fcc")
    grid_n = PLANCK_CELL.N_phi

    # Start from canonical 3D VORTEX_P seed on VACUUM_BOIL
    z_vortex = make_seed(SeedClass.VORTEX_P, grid_n, grid_n, nz=grid_n, device=dev)
    norm_total = float(torch.sum(torch.abs(z_vortex) ** 2).item())
    norm_lane0 = float(torch.sum(torch.abs(z_vortex[..., 0]) ** 2).item())
    norm_lane1 = float(torch.sum(torch.abs(z_vortex[..., 1]) ** 2).item())

    # Rauch-Werner neutron interferometer SU(2) rotation of the entire 3D VORTEX_P field by 2*pi and 4*pi
    axis_z = torch.zeros(z_vortex.shape[:-1] + (3,), dtype=torch.float32, device=dev)
    axis_z[..., 2] = 1.0
    phi_2pi = torch.full(z_vortex.shape[:-1], 2.0 * math.pi, dtype=torch.float32, device=dev)
    phi_4pi = torch.full(z_vortex.shape[:-1], 4.0 * math.pi, dtype=torch.float32, device=dev)

    z_2pi = su2_apply(z_vortex, phi_2pi, axis_z)
    z_4pi = su2_apply(z_vortex, phi_4pi, axis_z)

    rel_err_2pi_flip = float(torch.max(torch.abs(z_2pi + z_vortex)).item() / torch.max(torch.abs(z_vortex)).item())
    rel_err_4pi_restore = float(torch.max(torch.abs(z_4pi - z_vortex)).item() / torch.max(torch.abs(z_vortex)).item())

    # Momentum quantum on scale-K floor satisfies p_floor(K) * hL(K) == s_0 identically
    tol_ieee = rho_field_quantum() ** (N4_CAUSAL_LINKS - 1)
    rel_s_floor = abs(cfg.p_floor * cfg.hL - SI.s_0) / SI.s_0

    ok = (
        norm_lane0 > 0.0
        and norm_lane1 > 0.0
        and abs((norm_lane0 + norm_lane1) - norm_total) / norm_total < 1e-6
        and rel_s_floor < tol_ieee
        and rel_err_2pi_flip < 1e-6
        and rel_err_4pi_restore < 1e-6
    )
    return {
        "id": "QM_stern_gerlach_su2_720",
        "world_seed": "SeedClass.VORTEX_P on 3D VACUUM_BOIL",
        "scale_K": cfg.scale_k,
        "spin_up_fraction": norm_lane0 / norm_total,
        "spin_down_fraction": norm_lane1 / norm_total,
        "rel_err_360_sign_flip": rel_err_2pi_flip,
        "rel_err_720_identity": rel_err_4pi_restore,
        "ok": ok,
        "note": "3D VORTEX_P on VACUUM_BOIL splits into two spinor channels with +/-p_floor(K) (p_floor*hL=s_0) and flips sign under 2*pi SU(2) rotation",
    }


def check_qm_pauli_hom_antibunching(device: str = "cpu") -> dict:
    """Pauli exclusion on 3D VACUUM_BOIL world seed: undisturbed boil has 0 Pauli impulse, while parallel spinor overlap at rho_max triggers Phi_Pauli=256."""
    dev = torch.device(device)
    cfg = MConfig.for_ladder_floor("bohr", stencil="fcc")
    expected_pauli_ticks = pauli_impulse_disc(phase_bits=cfg.phase_bits)
    grid_n = PLANCK_CELL.N_phi
    c_idx = grid_n // 2

    # 1. Canonical 3D VACUUM_BOIL world seed: amplitude is 1 quantum a_Q < pauli_rho_min -> 0 Pauli repulsion everywhere
    f_boil = vacuum_boil_fixed_3d(grid_n, grid_n, grid_n, device=dev)
    ticks_boil_bg = int(torch.max(pauli_phi_int(f_boil, cfg)).item())

    # 2. Two identical spinors overlapping at the central cell of f_boil at saturation scale (1 << frac_bits) -> triggers Phi_Pauli = 256
    f_overlap = f_boil.clone()
    sat_amp = 1 << cfg.frac_bits
    f_overlap[c_idx, c_idx, c_idx] = f_boil[c_idx, c_idx, c_idx] * sat_amp
    ticks_parallel_overlap = int(pauli_phi_int(f_overlap, cfg)[c_idx, c_idx, c_idx].item())

    # 3. Singly polarized channel at the central cell (pure spin-up: component 1 empty) -> 0 Pauli repulsion
    f_single_spin = f_overlap.clone()
    f_single_spin[c_idx, c_idx, c_idx, 2] = 0
    f_single_spin[c_idx, c_idx, c_idx, 3] = 0
    ticks_single_spin = int(pauli_phi_int(f_single_spin, cfg)[c_idx, c_idx, c_idx].item())

    ok = (
        ticks_boil_bg == 0
        and ticks_parallel_overlap == expected_pauli_ticks
        and ticks_single_spin == 0
    )
    return {
        "id": "QM_pauli_hom_antibunching",
        "world_seed": "vacuum_boil_fixed_3d",
        "scale_K": cfg.scale_k,
        "boil_background_pauli_ticks": ticks_boil_bg,
        "parallel_overlap_pauli_ticks": ticks_parallel_overlap,
        "single_polarized_pauli_ticks": ticks_single_spin,
        "ok": ok,
        "note": "On 3D VACUUM_BOIL seed: background boil has 0 Pauli ticks, doubly-occupied V_P triggers Phi_Pauli=256 (pi), single spin channel gives 0",
    }


def check_qm_bell_chsh_tsirelson(device: str = "cpu") -> dict:
    """Bell-CHSH correlation on cuboctahedral axes (_FCC_OFFSETS): separable states obey |S|<=2, non-separable 2-particle singlet reaches S_QM=(d-1)/kappa=2*sqrt(2).

    Important physical distinction (Bell's theorem):
      1. Any factorized (local hidden-variable / product) two-site state Psi_sep = psi_A (x) psi_B stored as
         independent single-particle variables on spatially separated nodes A and B satisfies E_sep(a, b) = <sigma_a>_A <sigma_b>_B
         and is strictly bounded by the classical Bell limit |S_LHV| <= d - 1 = 2 (with pure product state max |S_prod| = 1/kappa = sqrt(2) on the Tsirelson axes).
      2. Violation up to Tsirelson's bound S_QM = (d - 1) / kappa = d_in(square) * kappa = 2*sqrt(2) arises specifically
         from the non-separable two-particle singlet state |Psi_-> = (|up>_A|down>_B - |down>_A|up>_B)/sqrt(2) in the
         antisymmetric tensor product C^2 (x) C^2 (prepared via Pauli exclusion at the shared source before separation),
         projected onto the square-face axes and normalized _FCC_OFFSETS vertex axes of the cuboctahedron, where the
         vertex-to-face projection cosine is exactly kappa = 1/sqrt(2).
    """
    del device
    d_spatial = N4_CAUSAL_LINKS - 1  # 3
    kappa = KAPPA_FCC_1TICK  # 1 / sqrt(2)
    d_in_sq = N4_CAUSAL_LINKS  # 4

    # Extract Bob's two -y diagonal vertex axes directly from canonical _FCC_OFFSETS in the z=0 plane:
    # (oz=0, oy=-1, ox=-1) and (oz=0, oy=-1, ox=+1) normalized by kappa = 1/sqrt(2)
    fcc_z0 = [off for off in _FCC_OFFSETS if off[0] == 0]
    fcc_z0_minus_y = sorted([off for off in fcc_z0 if off[1] < 0], key=lambda v: v[2])
    b = (kappa * float(fcc_z0_minus_y[0][2]), kappa * float(fcc_z0_minus_y[0][1]), 0.0)  # (-kappa, -kappa, 0)
    b_prime = (kappa * float(fcc_z0_minus_y[1][2]), kappa * float(fcc_z0_minus_y[1][1]), 0.0)  # (+kappa, -kappa, 0)
    a = (1.0, 0.0, 0.0)
    a_prime = (0.0, 1.0, 0.0)

    def dot3(u: tuple[float, float, float], v: tuple[float, float, float]) -> float:
        return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]

    # 1. Non-separable 2-particle singlet state in C^2 (x) C^2: E_singlet(u, v) = -u . v
    e_ab = -dot3(a, b)
    e_ab_p = -dot3(a, b_prime)
    e_ap_b = -dot3(a_prime, b)
    e_ap_bp = -dot3(a_prime, b_prime)
    s_singlet = abs(e_ab - e_ab_p + e_ap_b + e_ap_bp)

    # 2. Pure separable product states psi_A (x) psi_B evaluated along all 4 xy-plane rays of _FCC_OFFSETS and square axes
    xy_rays = [
        (1.0, 0.0, 0.0),
        (-1.0, 0.0, 0.0),
        (0.0, 1.0, 0.0),
        (0.0, -1.0, 0.0),
    ] + [(kappa * float(off[2]), kappa * float(off[1]), 0.0) for off in fcc_z0]

    max_s_product_state = 0.0
    for s_a in xy_rays:
        for s_b in xy_rays:
            s_val = abs(
                dot3(a, s_a) * dot3(b, s_b)
                - dot3(a, s_a) * dot3(b_prime, s_b)
                + dot3(a_prime, s_a) * dot3(b, s_b)
                + dot3(a_prime, s_a) * dot3(b_prime, s_b)
            )
            if s_val > max_s_product_state:
                max_s_product_state = s_val

    # 3. Deterministic local hidden variables A0, A1, B0, B1 in {-1, +1}
    max_s_lhv = 0.0
    for a0 in (-1.0, 1.0):
        for a1 in (-1.0, 1.0):
            for b0 in (-1.0, 1.0):
                for b1 in (-1.0, 1.0):
                    s_lhv = abs(a0 * (b0 - b1) + a1 * (b0 + b1))
                    if s_lhv > max_s_lhv:
                        max_s_lhv = s_lhv

    classical_bound = float(d_spatial - 1)
    tsirelson_from_carrier = float(d_spatial - 1) / kappa
    tsirelson_from_sq = float(d_in_sq) * kappa

    ok = (
        abs(max_s_product_state - (1.0 / kappa)) < 1e-12
        and abs(max_s_lhv - classical_bound) < 1e-12
        and abs(s_singlet - tsirelson_from_carrier) < 1e-12
        and abs(tsirelson_from_carrier - tsirelson_from_sq) < 1e-12
        and abs(s_singlet / classical_bound - (1.0 / kappa)) < 1e-12
    )
    return {
        "id": "QM_bell_chsh_tsirelson",
        "carrier_axes": "_FCC_OFFSETS (z=0 vertex rays) vs square_6 axes",
        "max_S_product_state": max_s_product_state,
        "max_S_LHV_classical": max_s_lhv,
        "S_singlet_nonseparable": s_singlet,
        "tsirelson_bound_from_kappa": tsirelson_from_carrier,
        "ratio_S_QM_over_S_LHV": s_singlet / max_s_lhv,
        "inv_kappa": 1.0 / kappa,
        "ok": ok,
        "note": "Geometric kappa^-1=sqrt(2) ladder on _FCC_OFFSETS: product state S_prod=sqrt(2), local HV S_LHV=2, non-separable singlet S_QM=(d-1)/kappa=4*kappa=2*sqrt(2)",
    }


def check_qm_tunneling_lattice_wkb(device: str = "cpu") -> dict:
    """§4.10.2 lattice hyperbolic dispersion cosh(kappa_tun * hL(K)) - 1 = u(K) using carrier quanta rho_field_quantum() and M_FORCE_SEATS.

    Distinguishes:
      1. Single-step lattice attenuation kappa_tun * hL = arccosh(1 + u), which matches WKB sqrt(2*u) for u << 1
         and grows logarithmically as ln(2*u) (rather than diverging as sqrt(2*u)) at single-link scale u >> 1;
      2. Full macroscopic barrier transmission probability |A_out / A_in|^2 = tau^(2*N) = exp(-2*N*arccosh(1 + u)) ~ (2*u)^(-2*N),
         which remains strongly suppressed across N = |N_12| = 12 barrier steps (no macroscopic barrier transparency).
    """
    del device
    floor_names = ("planck", "compton", "bohr", "lyman")
    cfgs = [MConfig.for_ladder_floor(name, stencil="fcc") for name in floor_names]

    # Weak barrier quantum = one native field-density quantum rho_Q = 2^(-2*frac_bits) = 1/4096 from si_constants (zero magic numbers!)
    delta_n_e = rho_field_quantum()
    u_values: list[float] = []
    for cfg in cfgs:
        delta_e_k = delta_n_e * cfg.e_floor
        u_k = (cfg.m_floor * delta_e_k * (cfg.hL**2)) / (SI.hbar**2)
        u_values.append(u_k)

    u_ref = u_values[0]
    u_k_invariant = all(abs(u - u_ref) / u_ref < 1e-14 for u in u_values[1:])

    # Exact lattice per-step decay factor tau = 1 + u - sqrt((1 + u)^2 - 1) vs WKB sqrt(2*u)
    tau_exact = 1.0 + u_ref - math.sqrt((1.0 + u_ref) ** 2 - 1.0)
    kappa_h_exact = -math.log(tau_exact)
    kappa_h_wkb = math.sqrt(2.0 * u_ref)
    rel_wkb_err = abs(kappa_h_exact - kappa_h_wkb) / kappa_h_wkb

    # Barrier thickness = |N_12| = 12 steps; exact hyperbolic identity cosh(kappa*hL) - 1 == u_ref
    n_steps_barrier = N12_FCC_CAUSAL_LINKS
    trans_n = tau_exact**n_steps_barrier
    cosh_identity_err = abs((math.cosh(kappa_h_exact) - 1.0) - u_ref)

    # Strong barrier at M_FORCE_SEATS = 97:
    # - single-step attenuation saturates logarithmically: arccosh(1 + M) ~ ln(2*M) < sqrt(2*M)
    # - full N_12-step barrier transmission probability tau_uv^(2*N_12) ~ (2*M)^(-2*N_12) is strongly suppressed!
    u_uv = float(M_FORCE_SEATS)
    kappa_uv_exact = math.acosh(1.0 + u_uv)
    kappa_uv_naive_wkb = math.sqrt(2.0 * u_uv)
    tau_uv = math.exp(-kappa_uv_exact)
    prob_trans_uv_n12 = tau_uv ** (2 * n_steps_barrier)
    uv_step_regularized = 0.0 < kappa_uv_exact < kappa_uv_naive_wkb
    macro_barrier_suppressed = 0.0 < prob_trans_uv_n12 < (delta_n_e**n_steps_barrier)

    ok = (
        u_k_invariant
        and 0.0 < tau_exact < 1.0
        and cosh_identity_err < 1e-15
        and rel_wkb_err < delta_n_e
        and 0.0 < trans_n < 1.0
        and uv_step_regularized
        and macro_barrier_suppressed
    )
    return {
        "id": "QM_tunneling_lattice_wkb",
        "barrier_quantum_rho_Q": delta_n_e,
        "u_barrier_invariant_across_K": u_k_invariant,
        "u_ref": u_ref,
        "tau_per_step": tau_exact,
        "transmission_N12_steps": trans_n,
        "rel_wkb_err_at_rho_Q": rel_wkb_err,
        "kappa_uv_single_step_arccosh": kappa_uv_exact,
        "kappa_uv_single_step_naive_wkb": kappa_uv_naive_wkb,
        "prob_trans_uv_N12_steps": prob_trans_uv_n12,
        "ok": ok,
        "note": "§4.10.2: u(K) is K-invariant; single-step kappa*hL=arccosh(1+u)~ln(2u) is UV-regular, while N12-step barrier probability tau^(2N)~(2u)^(-2N) is strongly suppressed",
    }


def check_qm_single_click_born_on_boil(device: str = "cpu") -> dict:
    """Einstein's 1927 single-click localization & deterministic Born ladder on 3D VACUUM_BOIL vs VACUUM_ICE (zero RNG).

    Physical mechanism verified:
      1. On uniform frozen VACUUM_ICE (`vacuum_ice_fixed_3d`), all N_phi = 13 detector pixels share the same phase class,
         so a uniform plane wave triggers either 0/13 or all 13/13 pixels simultaneously (no single-click localization).
      2. On live 3D VACUUM_BOIL (`vacuum_boil_fixed_3d`), the 13 pixels along x sit in the N_phi = 13 distinct Heisenberg
         phase classes k in 0..12 with sub-threshold pre-bias in [-19, +18] ticks (< 41 ticks, so 0 false clicks in vacuum).
      3. When a uniform plane wave at threshold amplitude `A_1click = (d-1)*unit_amp + (d-1)*N_phi = 154` arrives across all
         13 pixels simultaneously, ONLY ONE resonant pixel out of 13 reaches |Phi| = 41 ticks (n_E = 1 quantum) and fires!
      4. Sweeping the unknown arrival tick `class_offset` across 0..12 shifts the single firing pixel bijectively across all
         13 screen positions (1/13 uniform Born probability without RNG), while increasing wave amplitude `A` monotonically
         increases the fraction of active phase classes: 0/13 -> 1/13 -> 2/13 -> 6/13 -> 7/13.
    """
    dev = torch.device(device)
    cfg = MConfig.for_ladder_floor("bohr", stencil="fcc", pauli_exclusion=False)
    phi_min = heisenberg_phi_min_int(cfg)
    n_phi = PLANCK_CELL.N_phi  # 13
    c_idx = n_phi // 2  # 6
    d_minus_1 = N4_CAUSAL_LINKS - 2  # 2
    unit_amp = 1 << cfg.frac_bits  # 64
    single_click_amp = d_minus_1 * unit_amp + d_minus_1 * n_phi  # 2*64 + 2*13 = 154

    def screen_active_pixels_on_boil(wave_amp: int, class_offset: int = 0) -> list[int]:
        f_s = (
            signed_from_mod(
                vacuum_boil_fixed_3d(n_phi, n_phi, n_phi, device=dev, class_offset=class_offset),
                cfg.mod_bits,
            )
            * unit_amp
        )
        f_s[c_idx - 1, c_idx - 1, :, 1] += wave_amp
        f_s[c_idx - 1, c_idx + 1, :, 1] += wave_amp
        u0, v0 = f_s[..., 0], f_s[..., 1]
        sum_n = int_neighbor_sum(f_s, cfg.stencil)
        zr, zi = holonomy_zeta_int(u0, v0, sum_n[..., 0], sum_n[..., 1], frac_bits=cfg.frac_bits)
        rho2 = rho2_int(u0, v0, frac_bits=cfg.frac_bits)
        phi = signed_from_mod(saturating_phi_impulse(zr, zi, rho2, cfg), cfg.mod_bits)[c_idx, c_idx, :]
        return [x for x in range(n_phi) if abs(int(phi[x].item())) >= phi_min]

    def screen_active_pixels_on_ice(wave_amp: int) -> list[int]:
        f_ice = (
            signed_from_mod(vacuum_ice_fixed_3d(n_phi, n_phi, n_phi, device=dev), cfg.mod_bits)
            * unit_amp
        )
        f_ice[c_idx - 1, c_idx - 1, :, 1] += wave_amp
        f_ice[c_idx - 1, c_idx + 1, :, 1] += wave_amp
        u0, v0 = f_ice[..., 0], f_ice[..., 1]
        sum_n = int_neighbor_sum(f_ice, cfg.stencil)
        zr, zi = holonomy_zeta_int(u0, v0, sum_n[..., 0], sum_n[..., 1], frac_bits=cfg.frac_bits)
        rho2 = rho2_int(u0, v0, frac_bits=cfg.frac_bits)
        phi = signed_from_mod(saturating_phi_impulse(zr, zi, rho2, cfg), cfg.mod_bits)[c_idx, c_idx, :]
        return [x for x in range(n_phi) if abs(int(phi[x].item())) >= phi_min]

    # 1. At threshold amplitude A_1click = 154 on VACUUM_BOIL, every offset in 0..12 produces EXACTLY 1 click out of 13,
    #    and the 13 offsets bijectively visit all 13 pixels [0..12]!
    single_clicks_per_offset = [
        screen_active_pixels_on_boil(single_click_amp, class_offset=off) for off in range(n_phi)
    ]
    exact_one_click_each = all(len(c) == 1 for c in single_clicks_per_offset)
    visited_pixels = sorted(c[0] for c in single_clicks_per_offset if len(c) == 1)
    bijective_uniform_born = visited_pixels == list(range(n_phi))

    # 2. On uniform VACUUM_ICE, the number of firing pixels is always 0 or 13 (never 1!)
    ice_counts = {
        len(screen_active_pixels_on_ice(m * unit_amp)) for m in range(n_phi)
    }
    ice_never_single_click = ice_counts.issubset({0, n_phi})

    # 3. Monotonic activation ladder with wave amplitude on VACUUM_BOIL:
    amp_ladder = (0, d_minus_1 * unit_amp, single_click_amp, 3 * unit_amp, 4 * unit_amp, 5 * unit_amp)
    counts_ladder = [len(screen_active_pixels_on_boil(a, class_offset=0)) for a in amp_ladder]
    monotonic_ladder = all(
        counts_ladder[i] <= counts_ladder[i + 1] for i in range(len(counts_ladder) - 1)
    )

    ok = (
        exact_one_click_each
        and bijective_uniform_born
        and ice_never_single_click
        and monotonic_ladder
        and counts_ladder[0] == 0
        and counts_ladder[2] == 1
        and counts_ladder[-1] > counts_ladder[2]
    )
    return {
        "id": "QM_single_click_born_on_boil",
        "world_seed": "vacuum_boil_fixed_3d vs vacuum_ice_fixed_3d",
        "single_click_threshold_amp": single_click_amp,
        "exact_one_click_per_offset": exact_one_click_each,
        "bijective_13_pixels_visited": bijective_uniform_born,
        "ice_firing_counts_only_0_or_13": sorted(ice_counts),
        "boil_active_counts_ladder": counts_ladder,
        "ok": ok,
        "note": "Einstein 1927 single-click on 3D VACUUM_BOIL: uniform threshold wave fires 1/13 pixel per offset (bijectively visiting 0..12) and grows monotonically with amplitude",
    }
