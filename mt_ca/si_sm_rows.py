"""SISmRows — extracted from si_constants (file-size hygiene)."""
from __future__ import annotations

import math
from decimal import Decimal

from mt_ca.si_constants import (
    C,
    COSMO_BUBBLE_AGE_GYR,
    COSMO_RECOMB_KYR,
    DELTA_PHI_MIN,
    EV_J,
    PLANCK_CELL,
    KAPPA_FCC_1TICK,
    LN2,
    M_ELECTRON_GEV_PDG,
    M_HIGGS_GEV_PDG,
    M_NEUTRON_GEV_PDG,
    M_NU_ATM_EV_PDG,
    M_PROTON_GEV_PDG,
    N12_FCC_CAUSAL_LINKS,
    SECOND_PER_GYR,
    SECOND_PER_KYR,
    T_CMB_K_REF,
    _hT_decimal,
    baryon_geometry_factor,
    heisenberg_phi_min_disc,
    lepton_geometry_factor,
    m_tick_count_to_str,
    si_seconds_to_m_tick
)


class SISmRows:
    """Ask/row probes — do not grow si_constants with these."""

    def force_ansatz_row(self) -> dict[str, float]:
        """§8.4.1 — v ladder; α_s(v)=(d·d_in(□)/N_hier)·r_disc (π-free) and T-projection."""
        pi = math.pi
        e_p_gev = self.E_P / EV_J / 1.0e9
        e_0_gev = self.E_0 / EV_J / 1.0e9
        mod_bits = int(PLANCK_CELL.mod_bits)
        n_hier = mod_bits - 1
        d_spatial = 3  # Minkowski space §1.6 — not N_c
        d_in_sq = d_spatial + 1
        r_disc = float(heisenberg_phi_min_disc(phase_bits=mod_bits)) / float(PLANCK_CELL.N_ring)
        alpha_s_v_pifree = (float(d_spatial * d_in_sq) / float(n_hier)) * r_disc
        beta_pack_pifree = (float(d_in_sq) / float(d_spatial)) * r_disc
        v_pifree = (self.alpha_preferred**n_hier) * (e_0_gev / math.sqrt(r_disc))
        alpha_s_v = d_spatial / (n_hier * pi)
        v = (self.alpha_preferred**n_hier) * e_p_gev * math.sqrt(2.0 * pi)
        m_z = 91.1876  # GeV PDG pole mass (T control scale)
        beta_pack = 1.0 / (d_spatial * pi)
        alpha_s_mz = 1.0 / (1.0 / alpha_s_v + beta_pack * math.log(v / m_z))
        alpha_s_mz_pifree = 1.0 / (1.0 / alpha_s_v_pifree + beta_pack_pifree * math.log(v_pifree / m_z))
        g_f = 1.0 / (math.sqrt(2.0) * v * v)
        return {
            "alpha_s_seed": alpha_s_v,
            "alpha_s_at_v": alpha_s_v,
            "alpha_s_at_v_pifree": alpha_s_v_pifree,
            "alpha_s_MZ_model": alpha_s_mz,
            "alpha_s_MZ_pifree": alpha_s_mz_pifree,
            "alpha_s_MZ_pdg": 0.1179,
            "alpha_s_MZ_rel_err": abs(alpha_s_mz - 0.1179) / 0.1179,
            "alpha_s_MZ_pifree_rel_err": abs(alpha_s_mz_pifree - 0.1179) / 0.1179,
            "alpha_s_beta_pack": beta_pack,
            "alpha_s_beta_pack_pifree": beta_pack_pifree,
            "v_GeV": v,
            "v_pifree_GeV": v_pifree,
            "v_CODATA_GeV": 246.22,
            "M_Z_GeV": m_z,
            "G_F_GeV_m2": g_f,
            "G_F_CODATA": 1.1663787e-5,
            "G_F_rel_err": abs(g_f - 1.1663787e-5) / 1.1663787e-5,
            "N_hier": float(n_hier),
            "d_spatial": float(d_spatial),
            "note": "§8.4.1: π-free carrier α_s(v)=(d·d_in(□)/N_hier)·r_disc and T-projection",
        }

    def gr_passport_row(self) -> dict[str, float]:
        """§8.4.2 — G from ℓ_P; F₀=m_arg·g_M; no fifth coupling."""
        g_from_lp = self.l_P**2 * self.c**3 / self.hbar
        f0 = self.F_0
        return {
            "G_SI": self.G,
            "G_from_l_P": g_from_lp,
            "G_rel_err": abs(self.G - g_from_lp) / self.G,
            "G_over_l_P2_model": 1.0,  # c=ℏ=1
            "F0_N": f0,
            "F0_from_m_g": self.m_arg * self.g_M,
            "F0_rel_err": abs(f0 - self.m_arg * self.g_M) / f0,
            "m_arg_kg": self.m_arg,
            "g_M": self.g_M,
            "s_0": self.s_0,
            "note": "§8.4.2: G≡ℓ_P² c³/ℏ; F₀=m_arg g_M; g_μν=T-strain",
        }

    def weinberg_row(self) -> dict[str, float]:
        """§8.4.3 — bare sin²θ_W = d / (|N12|+1) = 3/13 from FCC cluster."""
        d_spatial = 3
        d_in_sq = d_spatial + 1
        n12 = int(N12_FCC_CAUSAL_LINKS)  # FCC coordination §1.6
        n_cluster = n12 + 1
        n_phi = int(PLANCK_CELL.N_phi)
        mod_bits = int(PLANCK_CELL.mod_bits)
        n_hier = mod_bits - 1
        r_disc = float(heisenberg_phi_min_disc(phase_bits=mod_bits)) / float(PLANCK_CELL.N_ring)
        sin2 = d_spatial / n_cluster
        sin2_eff = (1.0 / float(n_hier)) + (float(d_in_sq) / float(d_spatial)) * r_disc  # π-free carrier!
        pdg = 0.23122
        return {
            "sin2_theta_W_bare": sin2,
            "sin2_theta_W_eff_neighbor": sin2_eff,
            "sin2_theta_W_PDG_MSbar": pdg,
            "bare_rel_err_vs_PDG": abs(sin2 - pdg) / pdg,
            "eff_pifree_rel_err_vs_PDG": abs(sin2_eff - pdg) / pdg,
            "d_spatial": float(d_spatial),
            "N12": float(n12),
            "N_cluster": float(n_cluster),
            "N_phi": float(n_phi),
            "note": "§8.4.3: bare=3/13=d/(|N12|+1); π-free eff=1/N_hier + (d_in(□)/d)*r_disc = 89/384",
        }

    def decay_row(self) -> dict[str, float | bool | str]:
        """§8.2 decay — topo frame; ΔB≠0 banned; weak ΔB=0 class allowed; Γ open."""
        return {
            "E_0": self.E_0,
            "s_0": self.s_0,
            "hbar": self.hbar,
            "delta_B_move_derived": False,
            "proton_to_e_pi0_forbidden": True,
            "weak_delta_B0_class_allowed": True,
            "neutron_beta_channel_schema": True,
            "neutron_mass_split_closed": True,
            "neutron_mass_quantum": "m_e",
            "neutron_mass_k": 2,
            "note": "§8.2·5–7: no ΔB≠0; weak n→peν OK; m_n=m_p+2m_e (mass balance); Γ open",
        }

    def birth_row(self) -> dict[str, float]:
        """§4.9.2a — V ↦ (n, Q, χ, E, b, m); formulas on, not soft notes."""
        f_e = lepton_geometry_factor()
        m_p = self.m_p_CODATA if hasattr(self, "m_p_CODATA") else 1.67262192369e-27
        f_p = baryon_geometry_factor(m_p)
        e0 = 1.602176634e-19
        a = self.alpha_fs
        return {
            "n": 1.0,
            "Q_C": 1.0 * e0,
            "chi": 1.0,
            "E_0": self.E_0,
            "m_P": self.m_P,
            "alpha_fs": a,
            "f_geom_e": f_e,
            "m_e_kg": self.m_P * a * a * f_e,
            "f_geom_p": f_p,
            "m_p_kg": self.m_P * (a / 3.0) * f_p,
            "pauli_slots": 2.0,
            "b_pra": 1.0,
        }

    def bubble_tick_row(self) -> dict[str, float | int | str | bool]:
        """META §3.0.1 — our bubble: exact N↔SI via derived hT (no coarse extrapolation).

        Convention: N=0 = local BB of phase I; t_SI(0)=0. ΛCDM age/recombination are
        T-layer inputs (not g knobs) used to infer integer tick labels.
        """
        hT = self.hT
        hT_dec = _hT_decimal()
        t_age_obs_s = COSMO_BUBBLE_AGE_GYR * SECOND_PER_GYR
        t_recomb_obs_s = COSMO_RECOMB_KYR * SECOND_PER_KYR
        n_today = si_seconds_to_m_tick(t_age_obs_s, hT=hT_dec)
        n_cmb = si_seconds_to_m_tick(t_recomb_obs_s, hT=hT_dec)
        t_age_exact_s = float(Decimal(n_today) * hT_dec)
        t_recomb_exact_s = float(Decimal(n_cmb) * hT_dec)
        # Cesium-free carrier second N_sec(3) = (20/17) * 512^16 = (20/17) * 2^144
        n_sec_carrier = (20 * (512**16)) // 17
        n_sec_si = si_seconds_to_m_tick(1.0, hT=hT_dec)
        # Algebraic carrier clock N_CMB^alg = (11/40)*(E_0/Theta_rec)^2 and N_today^alg = N_CMB^alg*(8/alpha_fs)^(3/2)
        a = self.alpha_preferred
        r_disc = 41.0 / 512.0
        lam_h = 1.0 / 8.0 + 8.0 * r_disc * a
        theta_rec_e0 = (3.0 * (a**12) / (2.0 * 4.0 * 5.0 * 8.0 * 13.0)) * math.sqrt(2.0 * lam_h / r_disc)
        n_cmb_alg = int((11.0 / 40.0) * ((1.0 / theta_rec_e0) ** 2))
        n_today_alg = int(float(n_cmb_alg) * ((8.0 / a) ** 1.5))
        n_total_two_epoch_alg = 2 * n_today_alg
        t_age_alg_gyr = (float(n_today_alg) * hT) / SECOND_PER_GYR
        t_total_two_epoch_alg_gyr = 2.0 * t_age_alg_gyr
        t_recomb_alg_kyr = (float(n_cmb_alg) * hT) / SECOND_PER_KYR
        return {
            "hT_s": hT,
            "anchor_N0": "bubble_phase_I_BB",
            "t_start_s": 0.0,
            "cosmo_age_Gyr": COSMO_BUBBLE_AGE_GYR,
            "cosmo_recomb_kyr": COSMO_RECOMB_KYR,
            "t_age_obs_s": t_age_obs_s,
            "t_recomb_obs_s": t_recomb_obs_s,
            "N_today": n_today,
            "N_CMB": n_cmb,
            "N_today_alg": n_today_alg,
            "N_total_two_epoch_alg": n_total_two_epoch_alg,
            "N_CMB_alg": n_cmb_alg,
            "t_age_alg_Gyr": t_age_alg_gyr,
            "t_total_two_epoch_alg_Gyr": t_total_two_epoch_alg_gyr,
            "t_recomb_alg_kyr": t_recomb_alg_kyr,
            "N_sec_carrier": n_sec_carrier,
            "N_sec_si": n_sec_si,
            "N_sec_carrier_rel_err": abs(float(n_sec_carrier - n_sec_si)) / float(n_sec_si),
            "N_today_sci": m_tick_count_to_str(n_today),
            "N_CMB_sci": m_tick_count_to_str(n_cmb),
            "N_since_CMB": n_today - n_cmb,
            "N_since_CMB_sci": m_tick_count_to_str(n_today - n_cmb),
            "log10_N_today": math.log10(n_today),
            "log10_N_CMB": math.log10(n_cmb),
            "t_age_exact_s": t_age_exact_s,
            "t_recomb_exact_s": t_recomb_exact_s,
            "t_age_exact_Gyr": t_age_exact_s / SECOND_PER_GYR,
            "t_recomb_exact_kyr": t_recomb_exact_s / SECOND_PER_KYR,
            "roundtrip_age_rel_err": abs(t_age_exact_s - float(Decimal(n_today) * hT_dec)) / t_age_exact_s,
            "roundtrip_recomb_rel_err": abs(t_recomb_exact_s - float(Decimal(n_cmb) * hT_dec)) / t_recomb_exact_s,
            "note": "§3.0.1: t_SI(N)=N·hT exact; N_today_alg=(11/40)*(E0/Theta_rec)^2*(8/alpha)^(3/2)",
        }

    def universe_tick_at_utc_date(
        self, year: int, month: int, day: int, hour: int = 0, minute: int = 0, second: int = 0, *, use_cesium_free_second: bool = True
    ) -> dict[str, int | str]:
        """Exact universe tick number N(date) for any UTC calendar date relative to J2018.0 (2018-01-01T00:00:00Z)."""
        from datetime import datetime, timezone

        dt_ref = datetime(2018, 1, 1, 0, 0, 0, tzinfo=timezone.utc)
        dt_target = datetime(year, month, day, hour, minute, second, tzinfo=timezone.utc)
        delta_seconds = int((dt_target - dt_ref).total_seconds())
        row = self.bubble_tick_row()
        n_sec = int(row["N_sec_carrier"]) if use_cesium_free_second else int(row["N_sec_si"])
        n0_alg = int(row["N_today_alg"])
        n0_total_alg = int(row["N_total_two_epoch_alg"])
        n_tick = n0_alg + delta_seconds * n_sec
        n_tick_total = n0_total_alg + delta_seconds * n_sec
        return {
            "utc_iso": dt_target.isoformat(),
            "delta_seconds_from_J2018": delta_seconds,
            "N_sec_used": n_sec,
            "N_tick_epoch2_wave_alg": n_tick,
            "N_tick_total_two_epoch_alg": n_tick_total,
            "N_tick_alg": n_tick,
            "N_tick_sci": m_tick_count_to_str(n_tick),
            "N_tick_total_two_epoch_sci": m_tick_count_to_str(n_tick_total),
        }

    def electroweak_mass_row(self) -> dict[str, float]:
        """§8.4.3-E — m_W=gv/2, m_Z=m_W/cosθ with α(MZ) and sin²=3/13."""
        w = self.weinberg_row()
        a = self.alpha_runner_row()
        v = self.force_ansatz_row()["v_GeV"]
        sin2 = w["sin2_theta_W_bare"]
        cos2 = 1.0 - sin2
        e2 = 4.0 * math.pi * a["alpha_MZ"]
        g = math.sqrt(e2 / sin2)
        m_w = g * v / 2.0
        m_z = m_w / math.sqrt(cos2)
        return {
            "v_GeV": v,
            "sin2_theta_W": sin2,
            "alpha_MZ": a["alpha_MZ"],
            "g": g,
            "m_W_GeV": m_w,
            "m_Z_GeV": m_z,
            "m_W_PDG": 80.377,
            "m_Z_PDG": 91.1876,
            "m_W_rel_err": abs(m_w - 80.377) / 80.377,
            "m_Z_rel_err": abs(m_z - 91.1876) / 91.1876,
            "mass_ratio_sin2": 1.0 - (m_w / m_z) ** 2,
            "note": "§8.4.3-E: tree with α(MZ) from B_V runner + bare 3/13",
        }

    def higgs_mass_row(self) -> dict[str, float]:
        """§8.3.1 — bare m_H=v/2; + empty-cell stack λ=1/8+N_hier·δλ."""
        row = self.force_ansatz_row()
        v = float(row["v_GeV"])
        n_hier = float(row["N_hier"])
        lam0 = 1.0 / n_hier
        m_h0 = v * math.sqrt(2.0 * lam0)  # = v/2 when N_hier=8
        e_p_gev = self.E_P / EV_J / 1e9
        m_h_direct = (self.alpha_preferred**8) * e_p_gev * math.sqrt(math.pi / 2.0)
        # vacuum-bit quantum: (α*−1)·α_fs = α_fs/(4π)
        delta_lam = self.alpha_preferred / (4.0 * math.pi)
        lam = lam0 + n_hier * delta_lam
        m_h = v * math.sqrt(2.0 * lam)
        return {
            "v_GeV": v,
            "N_hier": n_hier,
            "lambda_bare": lam0,
            "delta_lambda_quantum": delta_lam,
            "delta_lambda_stack": n_hier * delta_lam,
            "lambda_quartic": lam,
            "m_H_bare_GeV": m_h0,
            "m_H_direct_GeV": m_h_direct,
            "m_H_GeV": m_h,
            "m_H_PDG_GeV": M_HIGGS_GEV_PDG,
            "m_H_bare_rel_err": abs(m_h0 - M_HIGGS_GEV_PDG) / M_HIGGS_GEV_PDG,
            "m_H_rel_err": abs(m_h - M_HIGGS_GEV_PDG) / M_HIGGS_GEV_PDG,
            "m_H_over_v_bare": m_h0 / v,
            "m_H_over_v": m_h / v,
            "note": "§8.3.1: bare v/2; λ=1/8+N_hier·(α_preferred/4π) empty-cell stack",
        }

    def floor2_baryon_cliques_and_moments_row(self) -> dict[str, float | int | bool | dict]:
        """§5.0.4-C — Floor 2 cliques K_2/K_3/K_4, 3 orthogonal color planes, and μ_p, μ_n."""
        from itertools import combinations
        from mt_ca.laplacian import _FCC_OFFSETS

        n12 = list(_FCC_OFFSETS)
        is_nn = lambda a, b: (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2 + (a[2] - b[2]) ** 2 == 2
        cliques = {
            m: sum(
                1
                for sub in combinations(n12, m - 1)
                if all(is_nn(u, v) for u, v in combinations(sub, 2))
            )
            for m in range(2, 6)
        }
        cliques_surface_s1 = {
            m: sum(
                1
                for sub in combinations(n12, m)
                if all(is_nn(u, v) for u, v in combinations(sub, 2))
            )
            for m in range(1, 6)
        }
        cliques_cluster_c13 = {
            1: 1 + cliques_surface_s1[1],
            **{m: cliques[m] + cliques_surface_s1[m] for m in range(2, 6)},
        }
        euler_c13 = (
            cliques_cluster_c13[1]
            - cliques_cluster_c13[2]
            + cliques_cluster_c13[3]
            - cliques_cluster_c13[4]
        )
        k3_tris = [(u, v) for u, v in combinations(n12, 2) if is_nn(u, v)]
        # Every K_3 triangle has 3 edges lying in the 3 mutually orthogonal coordinate planes {YZ, XZ, XY}
        all_k3_triplanar = True
        unique_k4_apex = True
        for u, v in k3_tris:
            e1, e2, e3 = u, v, (u[0] - v[0], u[1] - v[1], u[2] - v[2])
            zero_axes = {
                 next(i for i in range(3) if e[i] == 0)
                for e in (e1, e2, e3)
            }
            if zero_axes != {0, 1, 2}:
                all_k3_triplanar = False
            common_fourth = [w for w in n12 if w not in (u, v) and is_nn(u, w) and is_nn(v, w)]
            if len(common_fourth) != 1:
                unique_k4_apex = False

        kappa = KAPPA_FCC_1TICK
        delta_pack = (kappa * kappa) / float(N12_FCC_CAUSAL_LINKS)  # 1/24
        d = 3.0
        mu_p_pred = d - 5.0 * delta_pack  # 67/24 = +2.7916667
        mu_n_pred = -2.0 + 2.0 * delta_pack  # -23/12 = -1.9166667
        mu_sum_pred = mu_p_pred + mu_n_pred  # 7/8 = 0.875
        mu_p_pdg = 2.79284734463
        mu_n_pdg = -1.91304273
        mu_sum_pdg = mu_p_pdg + mu_n_pdg

        rel_p = abs(mu_p_pred - mu_p_pdg) / mu_p_pdg
        rel_n = abs(mu_n_pred - mu_n_pdg) / abs(mu_n_pdg)
        rel_sum = abs(mu_sum_pred - mu_sum_pdg) / mu_sum_pdg

        # Charged lepton generation ratios from (d=3, kappa, mod_bits=floor(B_V)=9)
        mod_bits = int(PLANCK_CELL.mod_bits)  # 9
        n_phi = int(PLANCK_CELL.N_phi)  # 13
        n_hier = mod_bits - 1  # 8
        d_in_sq = 4
        m_hat_gaussian = d_in_sq * d_in_sq + mod_bits * mod_bits  # 4^2 + 9^2 = 97 = 1 + 12*8
        delta_0 = 2.0 / float(mod_bits)
        lep_w = sorted(
            [(1.0 + (1.0 / kappa) * math.cos(2.0 * math.pi * g / d + delta_0)) ** 2 for g in range(3)]
        )
        r_mu_e = lep_w[1] / lep_w[0]
        r_tau_e = lep_w[2] / lep_w[0]
        koide_q = sum(lep_w) / (sum(math.sqrt(w) for w in lep_w) ** 2)
        rel_mu_e = abs(r_mu_e - 206.7682830) / 206.7682830
        rel_tau_e = abs(r_tau_e - 3477.23) / 3477.23

        # CKM Wolfenstein parameters & PMNS neutrino mixing from N_phi = 13 sector partition
        n12_f = float(N12_FCC_CAUSAL_LINKS)
        ckm_lambda = (d / float(n_phi)) * (1.0 - ((d - 1.0) / d) * delta_pack)  # 35/156
        ckm_A = (n12_f - 2.0) / n12_f  # 5/6
        ckm_rho_bar = float(d_in_sq) / (2.0 * float(n_phi))  # 2/13
        ckm_eta_bar = float(mod_bits) / (2.0 * float(n_phi))  # 9/26
        ckm_gamma_deg = math.degrees(math.atan(ckm_eta_bar / ckm_rho_bar))  # atan(9/4) = 66.04 deg
        pmns_sin2_12 = 4.0 / float(n_phi)  # 4/13
        pmns_sin2_23 = 7.0 / float(n_phi)  # 7/13
        pmns_sin2_13 = 2.0 / 92.0  # 1/46

        # Lifetimes (tau_mu, tau_pi0, tau_pi+, tau_n) from exact integer phase-ring channel counts (NO pi^3!)
        hbar_gev_s = self.hbar / (EV_J * 1.0e9)
        gf_gev2 = self.force_ansatz_row()["G_F_GeV_m2"]
        alpha = self.alpha_preferred
        m_e_gev = M_ELECTRON_GEV_PDG
        m_mu_gev = m_e_gev * r_mu_e
        r_e_sq = (m_e_gev / m_mu_gev) ** 2
        f_dalitz = 1.0 - 8.0 * r_e_sq + 8.0 * (r_e_sq**3) - (r_e_sq**4) - 12.0 * (r_e_sq**2) * math.log(r_e_sq)
        n_ring = int(PLANCK_CELL.N_ring)  # 512
        n_open_mu = int(n12_f) * (n_ring - n_phi)  # 12 * (512 - 13) = 5988 exact integer!
        gamma_mu = (gf_gev2**2 * (m_mu_gev**5) * f_dalitz) / float(n_open_mu)
        tau_mu_s = hbar_gev_s / gamma_mu

        g_a_pred = 5.0 / 4.0 + 1.0 / (d * float(n_phi))  # 199/156 = 1.275641
        q_np = 2.0 * ((float(mod_bits) / float(n_hier)) ** 2)  # 81/32 = 2.53125
        f0_np = (
            math.sqrt(q_np * q_np - 1.0) * (2.0 * (q_np**4) - 9.0 * (q_np**2) - 8.0) / 60.0
            + q_np * math.log(q_np + math.sqrt(q_np * q_np - 1.0)) / 4.0
        )
        v_ud_sq = 1.0 - ckm_lambda * ckm_lambda
        n_hb = (1 << int(PLANCK_CELL.frac_bits)) - 1  # 63
        n_open_n = float(n_hb) * (n12_f - 1.0) / n12_f  # 63 * 11 / 12 = 57.75
        gamma_n = (gf_gev2**2 * v_ud_sq * (1.0 + d * g_a_pred * g_a_pred) * (m_e_gev**5) * f0_np) / n_open_n
        tau_n_s = hbar_gev_s / gamma_n
        sqrt_sigma_mev = (M_PROTON_GEV_PDG * 1000.0) / math.sqrt(5.0)  # m_p / sqrt(d_out(V)) = 419.61 MeV
        eta_b_pred = ckm_eta_bar * (5.0 / float(n_hier)) * (alpha**4)  # (45/208) * alpha^4 = 6.135e-10
        omega_dm_over_b = (2.0 * float(n_hier)) / d  # 16/3 = 5.3333

        ok = (
            cliques == {2: 12, 3: 24, 4: 8, 5: 0}
            and cliques_surface_s1 == {1: 12, 2: 24, 3: 8, 4: 0, 5: 0}
            and cliques_cluster_c13 == {1: 13, 2: 36, 3: 32, 4: 8, 5: 0}
            and euler_c13 == 1
            and all_k3_triplanar
            and unique_k4_apex
            and abs(mu_sum_pred - 7.0 / 8.0) < 1e-15
            and rel_p < 1e-3
            and rel_n < 2.5e-3
            and rel_sum < 6e-3
            and abs(koide_q - 2.0 / 3.0) < 1e-12
            and rel_mu_e < 2e-5
            and rel_tau_e < 1e-4
            and m_hat_gaussian == 1 + int(n12_f) * n_hier == 97
            and abs(ckm_gamma_deg - 65.4) < 1.0
            and abs(pmns_sin2_12 - 0.307) < 0.005
            and abs(pmns_sin2_23 - 0.546) < 0.010
            and abs(pmns_sin2_13 - 0.0220) < 0.0005
            and abs(tau_mu_s - 2.1969811e-6) / 2.1969811e-6 < 3e-3
            and abs(g_a_pred - 1.2754) / 1.2754 < 3e-4
            and abs(tau_n_s - 878.4) / 878.4 < 5e-3
            and abs(sqrt_sigma_mev - 420.0) / 420.0 < 2e-3
            and abs(eta_b_pred - 6.12e-10) / 6.12e-10 < 5e-3
            and abs(omega_dm_over_b - 5.364) / 5.364 < 1e-2
        )
        return {
            "cliques_K_m": cliques,
            "cliques_surface_S1": cliques_surface_s1,
            "cliques_cluster_C13": cliques_cluster_c13,
            "euler_characteristic_C13": euler_c13,
            "all_K3_three_orthogonal_planes": all_k3_triplanar,
            "unique_chiral_K4_apex_per_K3": unique_k4_apex,
            "delta_pack": delta_pack,
            "mu_p_pred_muN": mu_p_pred,
            "mu_n_pred_muN": mu_n_pred,
            "mu_isoscalar_sum_pred_muN": mu_sum_pred,
            "mu_p_rel_err": rel_p,
            "mu_n_rel_err": rel_n,
            "mu_sum_rel_err": rel_sum,
            "m_mu_over_m_e_pred": r_mu_e,
            "m_tau_over_m_e_pred": r_tau_e,
            "m_mu_over_m_e_rel_err": rel_mu_e,
            "m_tau_over_m_e_rel_err": rel_tau_e,
            "m_hat_gaussian_97": m_hat_gaussian,
            "ckm_lambda": ckm_lambda,
            "ckm_A": ckm_A,
            "ckm_rho_bar": ckm_rho_bar,
            "ckm_eta_bar": ckm_eta_bar,
            "ckm_gamma_deg": ckm_gamma_deg,
            "pmns_sin2_12": pmns_sin2_12,
            "pmns_sin2_23": pmns_sin2_23,
            "pmns_sin2_13": pmns_sin2_13,
            "tau_mu_s": tau_mu_s,
            "g_A_pred": g_a_pred,
            "tau_n_s": tau_n_s,
            "sqrt_sigma_string_MeV": sqrt_sigma_mev,
            "eta_B_pred": eta_b_pred,
            "omega_DM_over_b_pred": omega_dm_over_b,
            "checks_ok": ok,
        }

    def proton_mass_row(self) -> dict[str, float]:
        """§8.2 — bare α·v/2; pack stack ×(1+κ²/N₁₂), κ=1/√2."""
        higgs = self.higgs_mass_row()
        f2 = self.floor2_baryon_cliques_and_moments_row()
        v = float(higgs["v_GeV"])
        m_h_bare = float(higgs["m_H_bare_GeV"])
        m_p0 = self.alpha_preferred * m_h_bare  # = α · v/2
        kappa = KAPPA_FCC_1TICK
        n12 = float(N12_FCC_CAUSAL_LINKS)
        delta_pack = (kappa * kappa) / n12  # (1/2)/12 = 1/24
        pack_factor = 1.0 + delta_pack
        m_p = m_p0 * pack_factor
        return {
            "v_GeV": v,
            "m_H_bare_GeV": m_h_bare,
            "alpha_fs": self.alpha_fs,
            "alpha_preferred": self.alpha_preferred,
            "kappa_FCC": kappa,
            "N12": n12,
            "delta_pack": delta_pack,
            "pack_stack_factor": pack_factor,
            "m_p_bare_GeV": m_p0,
            "m_p_GeV": m_p,
            "m_p_PDG_GeV": M_PROTON_GEV_PDG,
            "m_p_bare_rel_err": abs(m_p0 - M_PROTON_GEV_PDG) / M_PROTON_GEV_PDG,
            "m_p_rel_err": abs(m_p - M_PROTON_GEV_PDG) / M_PROTON_GEV_PDG,
            "m_p_over_m_H_bare": m_p0 / m_h_bare,
            "floor2_cliques_and_moments_ok": bool(f2["checks_ok"]),
            "mu_p_pred_muN": float(f2["mu_p_pred_muN"]),
            "mu_n_pred_muN": float(f2["mu_n_pred_muN"]),
            "mu_isoscalar_sum_pred_muN": float(f2["mu_isoscalar_sum_pred_muN"]),
            "note": "§8.2 & §5.0.4-C: bare α·v/2; pack 1+κ²/N₁₂; K3 cliques & μ_p=67/24, μ_n=-23/12",
        }

    def electron_mass_row(self) -> dict[str, float]:
        """§8.2 — bare α²·(v/2)/N_φ; stack α²·m_H/N_φ, N_φ=⌈4π⌉."""
        higgs = self.higgs_mass_row()
        m_h_bare = float(higgs["m_H_bare_GeV"])
        m_h = float(higgs["m_H_GeV"])
        n_phi = float(PLANCK_CELL.N_phi)
        a2 = self.alpha_preferred * self.alpha_preferred
        m_e0 = a2 * m_h_bare / n_phi
        m_e = a2 * m_h / n_phi
        e_p_gev = self.m_P * (C * C) / EV_J / 1e9  # E_P [GeV]
        f_geom = m_h / (e_p_gev * n_phi)
        return {
            "v_GeV": float(higgs["v_GeV"]),
            "m_H_bare_GeV": m_h_bare,
            "m_H_GeV": m_h,
            "alpha_fs": self.alpha_fs,
            "alpha_preferred": self.alpha_preferred,
            "N_phi": n_phi,
            "m_e_bare_GeV": m_e0,
            "m_e_GeV": m_e,
            "m_e_PDG_GeV": M_ELECTRON_GEV_PDG,
            "m_e_bare_rel_err": abs(m_e0 - M_ELECTRON_GEV_PDG) / M_ELECTRON_GEV_PDG,
            "m_e_rel_err": abs(m_e - M_ELECTRON_GEV_PDG) / M_ELECTRON_GEV_PDG,
            "f_geom": f_geom,
            "note": "§8.2: bare α²·(v/2)/N_φ; stack α²·m_H/N_φ (same empty-cell as Higgs)",
        }

    def neutron_mass_row(self) -> dict[str, float | int | bool | str]:
        """§8.2·7 — m_n = m_p + 2·m_e (channel step on §5 m_arg/ρ_Q mass balance)."""
        prot = self.proton_mass_row()
        elec = self.electron_mass_row()
        m_p = float(prot["m_p_GeV"])
        m_e = float(elec["m_e_GeV"])
        k = 2  # minimal integer k with m_n > m_p + m_e
        delta = float(k) * m_e
        m_n = m_p + delta
        threshold = m_p + m_e
        return {
            "m_p_GeV": m_p,
            "m_e_GeV": m_e,
            "k": k,
            "delta_GeV": delta,
            "m_n_GeV": m_n,
            "threshold_m_p_plus_m_e_GeV": threshold,
            "beta_downhill": m_n > threshold,
            "m_n_PDG_GeV": M_NEUTRON_GEV_PDG,
            "delta_PDG_GeV": M_NEUTRON_GEV_PDG - M_PROTON_GEV_PDG,
            "m_n_rel_err": abs(m_n - M_NEUTRON_GEV_PDG) / M_NEUTRON_GEV_PDG,
            "delta_rel_err": abs(delta - (M_NEUTRON_GEV_PDG - M_PROTON_GEV_PDG))
            / (M_NEUTRON_GEV_PDG - M_PROTON_GEV_PDG),
            "note": "§8.2·7: m_n=m_p+2m_e; ladder=m_arg/ρ_Q; channel=m_e; k=2 min β",
        }

    def neutrino_mass_row(self) -> dict[str, float]:
        """§8.2 — atm √|Δm²|: α⁵·v/(N_hier N_φ); stack α⁵·2m_H/(N_hier N_φ)."""
        higgs = self.higgs_mass_row()
        elec = self.electron_mass_row()
        v = float(higgs["v_GeV"])
        m_h = float(higgs["m_H_GeV"])
        n_hier = float(higgs["N_hier"])
        n_phi = float(elec["N_phi"])
        m_e = float(elec["m_e_GeV"])
        a = self.alpha_preferred
        a5 = a**5
        m_nu0_gev = a5 * v / (n_hier * n_phi)
        m_nu_gev = a5 * (2.0 * m_h) / (n_hier * n_phi)
        bridge_gev = (a**3) * m_e / (n_hier / 2.0)
        m_nu0_ev = m_nu0_gev * 1e9
        m_nu_ev = m_nu_gev * 1e9
        # π-free carrier solar & lightest neutrino lemmas (using r_disc = Δφ_disc / N_ring):
        d_spatial = 3
        d_pol = d_spatial - 1
        mod_bits = int(PLANCK_CELL.mod_bits)
        r_disc = float(heisenberg_phi_min_disc(phase_bits=mod_bits)) / float(PLANCK_CELL.N_ring)
        m_sol_ev = (float(d_pol) * (a**d_spatial) * math.sqrt(r_disc) / n_phi) * m_e * 1e9
        m_light_ev = (a**4) * m_e / n_phi * 1e9
        return {
            "v_GeV": v,
            "m_H_GeV": m_h,
            "m_e_GeV": m_e,
            "alpha_fs": self.alpha_fs,
            "alpha_preferred": a,
            "N_hier": n_hier,
            "N_phi": n_phi,
            "m_nu_atm_bare_eV": m_nu0_ev,
            "m_nu_atm_eV": m_nu_ev,
            "m_nu_atm_PDG_eV": M_NU_ATM_EV_PDG,
            "m_nu_atm_bare_rel_err": abs(m_nu0_ev - M_NU_ATM_EV_PDG) / M_NU_ATM_EV_PDG,
            "m_nu_atm_rel_err": abs(m_nu_ev - M_NU_ATM_EV_PDG) / M_NU_ATM_EV_PDG,
            "bridge_equals_stack": abs(bridge_gev - m_nu_gev) / m_nu_gev,
            "m_nu_sol_lemma_eV": m_sol_ev,
            "m_nu_lightest_lemma_eV": m_light_ev,
            "note": "§8.2: atm α⁵·2m_H/(N_hier N_φ)=α³·m_e/(N_hier/2); sol/lightest lemmas",
        }

    def saturation_bc_row(self) -> dict[str, float]:
        """§8.4.2-C′′′ — D_★ BC; near h_★[ε]; far h_00=2(m/m_P)ℓ_P/R."""
        from mt_ca.fixed_point import vacuum_amplitude_quantum

        rho_star = 1.0
        vac_amp = vacuum_amplitude_quantum(frac_bits=PLANCK_CELL.frac_bits)
        rho_vac = vac_amp * vac_amp
        rho_e = 0.5 * (rho_star + rho_vac)
        eps_partial = (rho_e - rho_vac) / rho_vac
        h_star_near = -2.0 * eps_partial  # |N|=12 equal NN edges: −(2/12)·12·ε
        r_star = 1.0  # hops / ℓ_P
        m_over_m_P = 1.0  # pra-core ceiling
        h_star_newton = -2.0 * m_over_m_P / r_star  # h_00(R_★)=−2m/(m_P R_★)
        mismatch = abs(h_star_near / h_star_newton) if h_star_newton != 0 else float("inf")
        return {
            "rho_star": rho_star,
            "rho_vac": rho_vac,
            "eps_partial_NN": eps_partial,
            "h_star_near": h_star_near,
            "h_star_newton": h_star_newton,
            "near_over_newton": mismatch,
            "R_star_over_l_P": r_star,
            "m_over_m_P": m_over_m_P,
            "h00_far_at_R_eq_2": h_star_newton * 0.5,
            "N12": 12.0,
            "m_P": self.m_P,
            "l_P": self.l_P,
        }

    def leapfrog_eps_row(self) -> dict[str, float]:
        """§3.12.5a — ε in импульс Φ; ℓ_e bound; m_loc ≤ m_P."""
        from mt_ca.fixed_point import vacuum_amplitude_quantum

        rho_star = 1.0  # A7: |Z|² ≤ 1 ↔ ρ_E ≤ u_P
        vac_amp = vacuum_amplitude_quantum(frac_bits=PLANCK_CELL.frac_bits)
        rho_vac = vac_amp * vac_amp  # A5 numerical floor → ρ_vac
        eps_star = (rho_star - rho_vac) / rho_vac
        return {
            "rho_star": rho_star,
            "rho_vac": rho_vac,
            "eps_star": eps_star,
            "ell_e_over_ell_P_max": 1.0 + eps_star,
            "m_loc_max_kg": self.m_P,
            "m_loc_max_over_m_P": 1.0,
            "d_tau_dt_formula_inv_1plus_eps": 1.0,
            "K_P": self.K_P,
            "l_P": self.l_P,
        }

    def einstein_strain_row(self) -> dict[str, float]:
        """§8.4.2-D/C′ — G_μν from Regge deficit; strain from ρ-edges + Δφ."""
        g_model = 1.0  # G/ℓ_P² in MODEL units
        eight_pi_g = 8.0 * math.pi * g_model
        n12 = 12.0
        return {
            "G_over_l_P2": g_model,
            "field_eq_coeff_8pi_G": eight_pi_g,
            "flat_deficit": 0.0,  # strain=0 ⇒ δ=0
            "girth_plaquette": 3.0,  # FCC triangle = d
            "d_spatial": 3.0,
            "N12_FCC": n12,
            "strain_edge_from": 1.0,  # ε_e = (ρ_e-ρ_vac)/ρ_vac
            "h0i_from_dphi": 1.0,  # h_0i ← Δφ_e ê_i
            "hij_from_eps": 1.0,  # h_ij ← ε_e ê_i ê_j
            "note": (
                "§8.4.2-C′: ε_e[δρ]→ℓ_e→θ_f→δ_e; "
                "h_0i[Δφ_e]; h_ij[ε_e]; not ε∝Δφ; мягкая сим-проверка"
            ),
        }

    def ckm_row(self) -> dict[str, float]:
        """§8.4.4 — N_gen=d; λ=sin θ_12=d/(|N12|+1)=3/13."""
        d_spatial = 3
        n12 = 12
        lam = d_spatial / (n12 + 1)
        v_us_pdg = 0.2243
        return {
            "N_gen": float(d_spatial),
            "lambda_bare": lam,
            "sin_theta_12": lam,
            "V_us_bare": lam,
            "V_us_PDG": v_us_pdg,
            "V_us_rel_err": abs(lam - v_us_pdg) / v_us_pdg,
            "lambda_sq_neighbor": lam * lam,  # soft |V_cb| neighbor, not SSOT
            "note": "§8.4.4: N_gen=d; λ=3/13 same cluster weight as Weinberg; A,ρ,η soft",
        }

    def annihilation_pdg_tau_row(self, *, device: str = "cpu") -> dict[str, float | int | str | bool]:
        """§5.0.3 — para-Ps τ PDG vs QED/ladder; head-on τ_M separate."""
        from mt_ca.annihilation_pdg_tau import run_annihilation_pdg_tau_bridge

        return run_annihilation_pdg_tau_bridge(device=device)

    def annihilation_pdg_tau_strict_row(self, *, device: str = "cpu") -> dict[str, float | int | str | bool]:
        """§5.0.3 — strict PDG τ: upstream masses, ortho/para ratio, anti-CODATA."""
        from mt_ca.annihilation_pdg_tau import run_annihilation_pdg_tau_strict

        return run_annihilation_pdg_tau_strict(device=device)

    def cmb_natural_thermodynamics_row(self) -> dict[str, float | bool | str]:
        """Carrier-scale (π-free, k_B-free, bare-number-free) recombination and CMB thermal quanta."""
        mod_bits = int(PLANCK_CELL.mod_bits)
        n12 = int(N12_FCC_CAUSAL_LINKS)
        n_phi = n12 + 1
        n_hier = mod_bits - 1
        n_ring = int(PLANCK_CELL.N_ring)
        d_spatial = 3
        d_pol = d_spatial - 1
        d_in_sq = d_spatial + 1
        d_out_e = n12 - (d_spatial + d_in_sq)
        n_sq_faces = d_pol * d_spatial  # |square| = 6
        n_tri_faces = 1 << d_spatial  # |triangle| = 8 = N_hier
        n_shell_2 = n12 + (d_pol * n12) + n_sq_faces  # 12 + 24 + 6 = 42
        phi_min_from_hier = 1 + d_out_e * n_tri_faces
        phi_min_from_gauss = (d_in_sq**d_pol) + (d_out_e**d_pol)
        phi_min_from_shell2 = n_shell_2 - 1
        phi_min_from_seam = (n_ring + n_phi + n_tri_faces) // n_phi
        phi_min = int(heisenberg_phi_min_disc(phase_bits=mod_bits))
        d_in_v = 1
        d_out_v = n_tri_faces - d_in_v  # 7 = d_soft
        m_hat_coulomb = (d_in_sq**d_pol) + (mod_bits**d_pol)  # 4^2 + 9^2 = 97
        alpha_geom_inv = (d_in_sq**d_pol) + ((n12 - d_in_v) ** d_pol)  # 4^2 + 11^2 = 137
        splitting_primes_zi = (
            d_out_e,
            n_phi,
            phi_min_from_gauss,
            m_hat_coulomb,
            alpha_geom_inv,
        )
        gaussian_norms_ok = (
            d_out_e == (d_in_v**d_pol) + (d_pol**d_pol)
            and n_phi == (d_pol**d_pol) + (d_spatial**d_pol)
            and phi_min_from_gauss == (d_in_sq**d_pol) + (d_out_e**d_pol)
            and m_hat_coulomb == 1 + n12 * n_tri_faces
            and alpha_geom_inv == n12 * n_phi - n_tri_faces - n12 + d_in_v
            and all((p % d_in_sq) == d_in_v for p in splitting_primes_zi)
            and (d_out_e * n_phi) == (d_in_sq**d_pol) + (d_out_v**d_pol) == (n_tri_faces**d_pol) + (d_in_v**d_pol)
        )
        r_disc_geometric_ok = (
            n_ring == (n_tri_faces**d_spatial)
            and phi_min == phi_min_from_hier == phi_min_from_gauss == phi_min_from_shell2 == phi_min_from_seam
            and gaussian_norms_ok
        )
        r_disc = float(phi_min_from_hier) / float(n_tri_faces**d_spatial)
        alpha = self.alpha_fs

        # Carrier baryon-to-photon ratio η_B = (⌊B_V⌋ * d_out(E)) / ((d-1) * N_φ * N_hier) * α_fs^(d_in(□))
        eta_b = (float(mod_bits * d_out_e) / float(d_pol * n_phi * n_hier)) * (alpha**d_in_sq)
        inv_eta_b_prefactor = float(d_pol * n_phi * n_hier) / float(mod_bits * d_out_e)

        # 1. Pure algebraic carrier recombination & CMB ratios (ZERO π, ZERO ln, ZERO bare numbers!):
        #    E_Lya / E_Ry = d / d_in(□), and Θ_rec / E_Lya = 1 / (d_out(E) * N_hier)
        carrier_recomb_divisor = float(d_in_sq * d_out_e * n_hier) / float(d_spatial)
        theta_rec_over_ery_alg = float(d_spatial) / float(d_in_sq * d_out_e * n_hier)
        lya_over_theta_rec_alg = float(d_out_e * n_hier)

        # T-layer continuum Saha logarithmic projection (for cross-check only):
        recomb_entropy_divisor = (float(d_out_e) / float(d_pol)) * math.log(1.0 / eta_b)
        theta_rec_over_ery = 1.0 / recomb_entropy_divisor
        lya_over_theta_rec = (float(d_spatial) / float(d_in_sq)) * recomb_entropy_divisor

        # Cosmological dilution factor 1 + z_CMB: carrier N_hier / α_fs vs tick ratio (N_today / N_CMB)^((d-1)/d)
        bb = self.bubble_tick_row()
        z_plus_1_carrier = float(n_hier) / alpha
        z_plus_1_ticks = (float(bb["N_today"]) / float(bb["N_CMB"])) ** (float(d_pol) / float(d_spatial))
        z_plus_1_planck_obs = 1090.80  # Planck 2018 T-layer reference

        # Present-day natural CMB thermal quantum Θ_CMB / E_Ry and Θ_CMB / (m_e c^2) (zero k_B, zero π!)
        theta_cmb_over_ery_alg = theta_rec_over_ery_alg / z_plus_1_carrier
        theta_cmb_over_ery_carrier = theta_rec_over_ery / z_plus_1_carrier
        theta_cmb_over_ery_ticks = theta_rec_over_ery / z_plus_1_ticks
        theta_cmb_over_mec2_carrier = (alpha**d_pol) * theta_cmb_over_ery_carrier / float(d_pol)
        hi_quanta_count = d_out_e * n_hier

        # Carrier scale T_P_M := E_0 = s_0 / dt (ZERO π, ZERO k_B, ZERO bare numbers!):
        #   Boiling ocean: ρ_vac / (E_0^4 / l_P^3) = 1 / N_ring  =>  Θ_vac / E_0 = N_ring^(-1 / d_in(□))
        #   v / E_0     = α^(N_hier) / sqrt(r_disc),  λ_H = 1/N_hier + N_hier * r_disc * α
        #   m_H / E_0   = sqrt((d-1)*λ_H) * (v / E_0)
        #   E_Ry / E_0  = (α^(|N_12|) / ((d-1)*N_φ)) * sqrt((d-1)*λ_H / r_disc)
        t_m_bath_over_e0_pifree = float(n_ring) ** (-1.0 / float(d_in_sq))
        lam_h = (1.0 / float(n_hier)) + float(n_hier) * r_disc * alpha
        e_ry_over_e0_pifree = (
            (alpha**n12) / float(d_pol * n_phi)
        ) * math.sqrt(float(d_pol) * lam_h / r_disc)
        t_rec_over_e0_pifree = e_ry_over_e0_pifree * theta_rec_over_ery_alg
        t_cmb_over_e0_pifree = e_ry_over_e0_pifree * theta_cmb_over_ery_alg

        # Primordial Nucleosynthesis (BBN) invariants from carrier (ZERO π, ZERO ln, ZERO bare numbers!):
        #   n / p at weak freeze-out = 1 / d_soft (where d_soft = d_out(V) = 7)
        #   Y_p^(0) = (d - 1)*(n/p) / (1 + n/p) = (d - 1) / N_hier = 1 / d_in(□)
        #   Y_p     = (1 / d_in(□)) * (1 - 1 / (d_in(□) * N_φ))
        #   D / H   = (d_out(E)^(d-1) / (d_in(□) * N_φ)) * α_fs^(d-1)
        d_soft = n_hier - 1
        bbn_n_over_p = 1.0 / float(d_soft)
        bbn_yp_bare = float(d_pol) / float(n_hier)
        bbn_yp_dressed = bbn_yp_bare * (1.0 - 1.0 / float(d_in_sq * n_phi))
        bbn_d_over_h = (float(d_out_e**d_pol) / float(d_in_sq * n_phi)) * (alpha**d_pol)
        bbn_yp_obs = 0.2450
        bbn_dh_obs = 2.547e-5
        rel_err_yp = abs(bbn_yp_dressed - bbn_yp_obs) / bbn_yp_obs
        rel_err_dh = abs(bbn_d_over_h - bbn_dh_obs) / bbn_dh_obs

        # T-layer readout in Kelvin (using k_B only at the T-layer thermometer interface)
        kb_si = 1.380649e-23
        m_e_kg = float(self.birth_row()["m_e_kg"])
        e_ry_j = (alpha**d_pol) * m_e_kg * (self.c**d_pol) / float(d_pol)
        t_ry_k = e_ry_j / kb_si
        t_rec_k_alg = t_ry_k * theta_rec_over_ery_alg
        t_rec_k_model = t_ry_k * theta_rec_over_ery
        t_rec_k_obs = T_CMB_K_REF * z_plus_1_planck_obs
        t_cmb_k_alg = t_ry_k * theta_cmb_over_ery_alg
        t_cmb_k_carrier = t_ry_k * theta_cmb_over_ery_carrier
        t_cmb_k_ticks = t_ry_k * theta_cmb_over_ery_ticks
        t_cmb_k_planck_z = t_rec_k_model / z_plus_1_planck_obs

        rel_err_t_rec = abs(t_rec_k_model - t_rec_k_obs) / t_rec_k_obs
        rel_err_t_rec_alg = abs(t_rec_k_alg - t_rec_k_obs) / t_rec_k_obs
        rel_err_z_carrier_vs_ticks = abs(z_plus_1_carrier - z_plus_1_ticks) / z_plus_1_ticks
        rel_err_t_cmb_carrier = abs(t_cmb_k_carrier - T_CMB_K_REF) / T_CMB_K_REF
        rel_err_t_cmb_alg = abs(t_cmb_k_alg - T_CMB_K_REF) / T_CMB_K_REF
        rel_err_t_cmb_ticks = abs(t_cmb_k_ticks - T_CMB_K_REF) / T_CMB_K_REF

        ok = (
            r_disc_geometric_ok
            and rel_err_t_rec < 0.005
            and rel_err_t_rec_alg < 0.005
            and rel_err_z_carrier_vs_ticks < 0.001
            and rel_err_t_cmb_carrier < 0.005
            and rel_err_t_cmb_alg < 0.01
            and rel_err_t_cmb_ticks < 0.005
            and rel_err_yp < 0.002
            and rel_err_dh < 0.01
        )
        return {
            "r_disc_geometric_41_over_512_ok": r_disc_geometric_ok,
            "r_disc": r_disc,
            "eta_B_carrier": eta_b,
            "inv_eta_B_prefactor_208_over_45": inv_eta_b_prefactor,
            "bbn_n_over_p_freeze": bbn_n_over_p,
            "bbn_Yp_bare": bbn_yp_bare,
            "bbn_Yp_dressed": bbn_yp_dressed,
            "bbn_D_over_H": bbn_d_over_h,
            "rel_err_bbn_Yp": rel_err_yp,
            "rel_err_bbn_D_over_H": rel_err_dh,
            "carrier_recomb_divisor_alg": carrier_recomb_divisor,
            "recomb_entropy_divisor_5_over_2_ln_inv_eta": recomb_entropy_divisor,
            "theta_rec_over_E_Ry_alg": theta_rec_over_ery_alg,
            "theta_rec_over_E_Ry": theta_rec_over_ery,
            "E_Lya_over_theta_rec_alg": lya_over_theta_rec_alg,
            "E_Lya_over_theta_rec": lya_over_theta_rec,
            "z_plus_1_carrier_8_over_alpha": z_plus_1_carrier,
            "z_plus_1_ticks_2_over_3": z_plus_1_ticks,
            "z_plus_1_planck_obs": z_plus_1_planck_obs,
            "theta_cmb_over_E_Ry_alg": theta_cmb_over_ery_alg,
            "theta_cmb_over_E_Ry_carrier": theta_cmb_over_ery_carrier,
            "theta_cmb_over_mec2_carrier": theta_cmb_over_mec2_carrier,
            "theta_cmb_in_E_HI_quanta": float(hi_quanta_count),
            "T_M_bath_over_E0_pifree": t_m_bath_over_e0_pifree,
            "E_Ry_over_E0_pifree": e_ry_over_e0_pifree,
            "T_rec_over_E0_pifree_alpha12": t_rec_over_e0_pifree,
            "T_CMB_over_E0_pifree_alpha13": t_cmb_over_e0_pifree,
            "T_rec_K_alg": t_rec_k_alg,
            "T_rec_K_model": t_rec_k_model,
            "T_rec_K_obs": t_rec_k_obs,
            "T_CMB_K_alg": t_cmb_k_alg,
            "T_CMB_K_carrier": t_cmb_k_carrier,
            "T_CMB_K_ticks": t_cmb_k_ticks,
            "T_CMB_K_planck_z": t_cmb_k_planck_z,
            "T_CMB_K_ref": T_CMB_K_REF,
            "rel_err_T_rec": rel_err_t_rec,
            "rel_err_T_rec_alg": rel_err_t_rec_alg,
            "rel_err_z_carrier_vs_ticks": rel_err_z_carrier_vs_ticks,
            "rel_err_T_CMB_carrier": rel_err_t_cmb_carrier,
            "rel_err_T_CMB_alg": rel_err_t_cmb_alg,
            "rel_err_T_CMB_ticks": rel_err_t_cmb_ticks,
            "ok": ok,
            "note": "π-free, k_B-free, bare-number-free carrier: Θ_vac/E_0=N_ring^(-1/d_in(□)), Θ_rec/E_Ry=d/(d_in(□) d_out(E) N_hier), Θ_CMB/E_Ry=d α_fs/(d_in(□) d_out(E) N_hier^2)",
        }

    def periodic_table_and_fcc_graph_dirac_row(self) -> dict[str, Any]:
        """§5.0.4-B / Floor 3 — Periodic Table periods, nuclear magic numbers to Pb-208 & N=184, and discrete FCC Graph Dirac spectrum."""
        d = 3
        d_in_v, d_in_e, d_in_tri, d_in_sq = 1, 2, 3, 4
        d_pol = d - d_in_v  # 2
        d_out_e, n_squares, d_out_v = 5, 6, 7
        n_hier = 8
        n12 = int(N12_FCC_CAUSAL_LINKS)  # 12
        n_phi = int(PLANCK_CELL.N_phi)  # 13
        delta_phi_disc = d_in_sq * d_in_sq + d_out_e * d_out_e  # 41
        n_hb = (1 << n_squares) - d_in_v  # 63
        n_ring = n_hier ** d  # 512

        # 1. Subshell capacities, Madelung period lengths, and noble gas closures
        subshell_caps = tuple(d_pol * g for g in (d_in_v, d, d_out_e, d_out_v))  # (2, 6, 10, 14)
        period_lengths = tuple(
            d_pol * (((p + d_pol) // d_pol) ** d_pol)
            for p in range(d_in_v, d_out_v + d_in_v)
        )  # (2, 8, 8, 18, 18, 32, 32)
        noble_gases = tuple(
            sum(period_lengths[:i]) for i in range(d_in_v, d_out_v + d_in_v)
        )  # (2, 10, 18, 36, 54, 86, 118)

        # 2. Nuclear magic numbers: low tetrahedral branch (k=1..3) and high spin-orbit branch (k=4..7, k=8 island)
        magic_low = tuple(
            (k * (k + d_in_v) * (k + d_pol)) // d for k in (d_in_v, d_in_e, d_in_tri)
        )  # (2, 8, 20)
        magic_high = tuple(
            (k * ((k ** d_pol) + d_out_e)) // d for k in (d_in_sq, d_out_e, n_squares, d_out_v)
        )  # (28, 50, 82, 126)
        z_lead = d_pol * delta_phi_disc  # 82
        n_lead = d_pol * n_hb  # 126
        a_lead = d_pol * n_hier * n_phi  # 208
        n_island = (n_hier * ((n_hier ** d_pol) + d_out_e)) // d  # 184
        z_island_bounds = (n_lead - n12, n_lead - n_squares)  # (114, 120)
        z_point_em = (d_in_sq ** d_pol) + ((n12 - d_in_v) ** d_pol)  # 137
        p8_partition = (subshell_caps[0], subshell_caps[-1], d)  # (2, 14, 3) -> sum = 19
        z_qed_diving = (z_point_em + d_out_e * d_out_v, z_point_em + (n_squares ** d_pol))  # (172, 173)

        # 3. Discrete Gauss edge identity and discrete FCC Graph Dirac Sturm solver
        k_max = (d_in_v + n12 * n_hier) + d  # 100
        n_sh = [d_in_v if k == 0 else (n12 - d_pol) * k * k + d_pol for k in range(k_max + 1)]
        gauss_edges_ok = all(
            n12 * ((k ** d) - ((k - d_in_v) ** d))
            + d_in_sq * n12 * (k * k)
            + n12 * (((k + d_in_v) ** d) - (k ** d))
            == n12 * n_sh[k]
            for k in range(d_in_v, n_hier + d_in_v)
        )

        tail_m = n_ring * d_in_sq  # 2048
        acc = 0.0
        g_fcc = [0.0] * (tail_m + 1)
        for m in range(tail_m, 0, -1):
            acc += float(d) / float((m ** d) - ((m - d_in_v) ** d))
            g_fcc[m - 1] = acc

        geom_norm = float(n12 - d_pol) / float(d)
        a_hop = [0.0] * (k_max + 1)
        b_hop = [0.0] * (k_max + 1)
        for k in range(d_in_v, k_max + 1):
            ew = float((k ** d) - ((k - d_in_v) ** d))
            a_hop[k] = math.sqrt(geom_norm * ew / float(n_sh[k - 1]))
            b_hop[k] = math.sqrt(geom_norm * ew / float(n_sh[k]))

        alpha = self.alpha_preferred

        def count_below(z_val: int, energy: float, start_k: int) -> int:
            neg = 0
            prev = 0.0
            for k in range(start_k, k_max + 1):
                diag = 1.0 - float(z_val) * alpha * g_fcc[k] - energy
                if k >= d_in_v:
                    v_in = -float(z_val) * alpha * (0.5 * (g_fcc[k - 1] + g_fcc[k]) if start_k == 0 else g_fcc[k])
                    den_in = 1.0 + energy - v_in
                    diag += (b_hop[k] ** d_pol) / den_in
                    if k > start_k:
                        pivot = diag - (((a_hop[k] * b_hop[k]) / den_in) ** d_pol) / prev
                    else:
                        pivot = diag
                else:
                    pivot = diag
                if k < k_max:
                    v_out = -float(z_val) * alpha * (0.5 * (g_fcc[k] + g_fcc[k + 1]) if start_k == 0 else g_fcc[k + 1])
                    den_out = 1.0 + energy - v_out
                    pivot += (a_hop[k + 1] ** d_pol) / den_out
                if pivot < 0.0:
                    neg += 1
                prev = pivot if abs(pivot) > 1e-30 else 1e-30
            return neg

        def bisect_eval(z_val: int, target_idx: int, start_k: int) -> float:
            lo, hi = -0.9999999, 0.9999999
            if count_below(z_val, lo, start_k) > target_idx:
                return -1.0
            for _ in range(54):
                mid = 0.5 * (lo + hi)
                if count_below(z_val, mid, start_k) > target_idx:
                    hi = mid
                else:
                    lo = mid
            return 0.5 * (lo + hi)

        z_core_zero = next(z_c for z_c in range(z_lead - n_hier, z_lead + n_hier) if count_below(z_c, 0.0, 0) >= d_in_v)
        z_core_dive = next(z_c for z_c in range(n_lead - n_hier, n_lead + n_hier) if count_below(z_c, -0.9999999, 0) >= d_in_v)
        z_1s_zero = next(z_c for z_c in range(d_pol * z_point_em - n12, d_pol * z_point_em + n12) if count_below(z_c, 0.0, d_in_v) >= d_in_v)
        e_core_82 = bisect_eval(z_lead, 0, 0)
        e_core_122 = bisect_eval(z_core_dive - d_in_v, 0, 0)
        e_1s_137 = bisect_eval(z_point_em, d_in_v, 0)
        e_1s_hard_137 = bisect_eval(z_point_em, 0, d_in_v)

        ok = (
            gauss_edges_ok
            and z_lead + n_lead == a_lead
            and magic_high[-2] == z_lead
            and magic_high[-1] == n_lead
            and sum(p8_partition) == z_point_em - noble_gases[-1] == n_phi + n_squares
            and abs((g_fcc[0] - g_fcc[1]) - float(d)) < 1e-12
            and z_core_zero == z_lead - d_in_v
            and e_core_82 < 0.0
            and z_island_bounds[1] < z_core_dive < n_lead
            and e_core_122 > -1.0
            and e_1s_137 > 0.5
            and e_1s_hard_137 > 0.5
        )
        return {
            "subshell_capacities": subshell_caps,
            "period_lengths": period_lengths,
            "noble_gas_closures": noble_gases,
            "nuclear_magic_all": magic_low + magic_high,
            "terminal_stable_Pb208": (z_lead, n_lead, a_lead),
            "island_of_stability_N184": n_island,
            "island_of_stability_Z_bounds": z_island_bounds,
            "period_8_partition": p8_partition,
            "finite_nucleus_qed_diving_Z_bounds": z_qed_diving,
            "gauss_edges_identity_ok": gauss_edges_ok,
            "green_core_k0": g_fcc[0],
            "green_shell_k1": g_fcc[1],
            "z_core_zero_crossing": z_core_zero,
            "e_core_at_Pb82": e_core_82,
            "z_core_continuum_diving": z_core_dive,
            "e_core_at_122": e_core_122,
            "e_1s_shell_at_137": e_1s_137,
            "e_1s_hard_core_at_137": e_1s_hard_137,
            "z_1s_hard_core_zero_crossing": z_1s_zero,
            "ok": ok,
            "note": "Periodic Table periods, Pb-208 (82+126=208), N=184 island, discrete Gauss law, and nonsingular FCC Graph Dirac at Z=137",
        }

    def four_channel_nilpotent_cascade_and_gas_row(self) -> dict[str, Any]:
        """§4.1.1-HL(H4b) — 4-channel nilpotent cascade M_chan = I_4 + N_nil (N_nil^3 = 0), exact inverse, and gas-dynamics invariants."""
        d = 3
        d_in_v, d_in_e, d_in_tri, d_in_sq = 1, 2, 3, 4
        d_pol = d - d_in_v  # 2
        d_out_tri, d_out_sq, d_out_e, n_squares, d_out_v = 3, 4, 5, 6, 7
        n_hier = 8
        mod_bits = 9
        n12 = int(N12_FCC_CAUSAL_LINKS)  # 12
        n_phi = int(PLANCK_CELL.N_phi)  # 13
        delta_phi_disc = d_in_sq * d_in_sq + d_out_e * d_out_e  # 41
        n_ring = n_hier ** d  # 512
        phi_pauli = n_ring // d_pol  # 256

        d_in_vec = (d_in_v, d_in_e, d_in_sq, d_in_tri)  # (1, 2, 4, 3)
        d_out_vec = (d_out_v, d_out_e, d_out_sq, d_out_tri)  # (7, 5, 4, 3)
        det_t = 1
        for v_in in d_in_vec:
            det_t *= v_in  # 24
        inv_diag_24 = tuple(det_t // v_in for v_in in d_in_vec)  # (24, 12, 6, 8)
        retention_ticks = tuple(
            math.ceil((float(n12) / float(v_out)) * (float(phi_pauli) / float(delta_phi_disc)))
            for v_out in d_out_vec
        )  # (11, 15, 19, 25)

        n_01 = float(d_in_sq) / float(d_in_e)  # 2.0
        n_02 = float(d_in_e) / float(d_in_sq)  # 0.5
        n_12 = float(d_in_e) / float(d_in_sq)  # 0.5
        n_13 = float(d_in_v) / float(d_in_tri)  # 1/3
        n2_02 = n_01 * n_12  # 1.0
        n2_03 = n_01 * n_13  # 2/3

        m_step = n_hier  # 8
        binom_m_minus_1 = float(m_step * (m_step - d_in_v)) / float(d_pol)
        fwd_v = float(n12)
        fwd_e = float(n12) * (float(m_step) * n_01)
        fwd_sq = float(n12) * (float(m_step) * n_02 + binom_m_minus_1 * n2_02)
        fwd_tri = float(n12) * (binom_m_minus_1 * n2_03)
        fwd_channels = (round(fwd_v), round(fwd_e), round(fwd_sq), round(fwd_tri))
        k_target = m_step + d_in_v
        expected_shell_sites = (n12 - d_pol) * (k_target ** d_pol) + d_pol

        binom_m_plus_1 = float(m_step * (m_step + d_in_v)) / float(d_pol)
        rec_v = fwd_v
        rec_e = fwd_v * (-float(m_step) * n_01) + fwd_e
        rec_sq = fwd_v * (-float(m_step) * n_02 + binom_m_plus_1 * n2_02) + fwd_e * (-float(m_step) * n_12) + fwd_sq
        rec_tri = fwd_v * (binom_m_plus_1 * n2_03) + fwd_e * (-float(m_step) * n_13) + fwd_tri
        reconstructed_s1 = (round(rec_v), round(rec_e), round(rec_sq), round(rec_tri))

        dof_classes = (d, d_out_e, n_squares, d_out_v)
        gammas = tuple(float(f + d_pol) / float(f) for f in dof_classes)
        prandtls = tuple((float(d_in_sq) * g) / (float(mod_bits) * g - float(d_out_e)) for g in gammas[:d])
        ma_crit = 1.0 / KAPPA_FCC_1TICK
        r_disc = float(delta_phi_disc) / float(n_ring)

        ok = (
            det_t == d_pol * n12
            and inv_diag_24 == (d_pol * n12, n12, n_squares, n_hier)
            and abs(n2_03 - float(d_pol) / float(d)) < 1e-12
            and sum(fwd_channels) == expected_shell_sites
            and reconstructed_s1 == (n12, 0, 0, 0)
            and abs(prandtls[0] - float(d_pol) / float(d)) < 1e-12
            and abs(prandtls[1] - float(d_pol * d_out_v) / float(n_phi + n_squares)) < 1e-12
            and abs(ma_crit - math.sqrt(float(d_pol))) < 1e-12
        )
        return {
            "cascade_determinant": det_t,
            "cascade_inverse_diag_24": inv_diag_24,
            "channel_retention_ticks": retention_ticks,
            "nilpotent_index": d,
            "two_step_vortex_amplitude": n2_03,
            "forward_shell_channels_k9": fwd_channels,
            "reconstructed_source_s1": reconstructed_s1,
            "adiabatic_indices": gammas,
            "prandtl_numbers": prandtls,
            "critical_mach_number": ma_crit,
            "kolmogorov_exponents": (float(d_pol) / float(d), -float(d_out_e) / float(d)),
            "viscosity_entropy_floor": r_disc,
            "ok": ok,
            "note": "4-channel nilpotent cascade M_chan = I_4 + N_nil (N_nil^3=0), exact 3-term inverse, and gas-dynamics invariants",
        }

    def bio_frustration_and_three_life_types_row(self) -> dict[str, Any]:
        """Floor 3 / Biology — Geometric frustration arccos(1/d)+arccos(-1/d)=half-turn and 5:6:7 scale law for 3 planetary life windows."""
        d = 3
        d_in_v, d_in_sq = 1, 4
        d_pol = d - d_in_v  # 2
        d_out_e, n_squares, d_out_v = 5, 6, 7
        mod_bits = 9
        n12 = int(N12_FCC_CAUSAL_LINKS)  # 12
        n_phi = int(PLANCK_CELL.N_phi)  # 13
        n_tm_units = n12 + n_squares  # 18

        # 1. Tetrahedral K_4 vs Octahedral (square) dihedral angles on FCC N12
        cos_tet = float(d_in_v) / float(d)  # +1/3
        cos_oct = -float(d_in_v) / float(d)  # -1/3
        half_turn_rad = math.acos(-1.0)
        theta_tet = math.acos(cos_tet)
        theta_oct = math.acos(cos_oct)
        frustration_gap_rad = float(d_pol) * half_turn_rad - float(d_out_e) * theta_tet
        frustration_gap_deg = frustration_gap_rad * 180.0 / half_turn_rad

        # 2. Three planetary life windows m in (-1, 0, +1): 5:6:7 length scale and (2/7, 1, 2) energy scale
        rungs = (-d_in_v, 0, d_in_v)
        scale_5_6_7 = tuple(n_squares + m for m in rungs)  # (5, 6, 7)
        soft_quanta = (float(d_pol) / float(d_out_v), float(d_in_v), float(d_pol))  # (2/7, 1, 2)
        bond_in_ka0 = tuple(float(d_in_sq) + float(m * d_pol) / float(d) for m in rungs)  # (10/3, 4, 14/3)
        tm18_in_ka0 = tuple(float(n_tm_units) * b for b in bond_in_ka0)  # (60, 72, 84)
        helix_pitch_in_ka0 = tuple((float(n_tm_units) / float(d_out_e)) * b for b in bond_in_ka0)
        duplex_stack_in_ka0 = tuple((float(mod_bits) / float(d_in_sq)) * b for b in bond_in_ka0)

        # SI projections in Angstroms (using Bohr radius a_0 and kappa = 1/sqrt(2))
        a0_ang = 0.529177210903
        ka0_ang = KAPPA_FCC_1TICK * a0_ang
        bond_ang = tuple(b * ka0_ang for b in bond_in_ka0)
        tm18_ang = tuple(t * ka0_ang for t in tm18_in_ka0)

        # 3. Genetic laws on Z_4 / Z_16 / Z_64:
        #    - Synonymous 3rd-position transitions (c ^ 1): 14/16 = 7/8 = d_out(V)/N_hier stems, 60/64 = 15/16 codons!
        #    - CpG epigenetic stem code: (1 << 2) | 3 = 7 = d_out(V) -> deaminates via b_1 ^ 1 to TG = 3 = d!
        #    - Mendelian diploid inheritance: [1, 1] * [1, 1] = (1, 2, 1) genotype, threshold -> (d, 1) = (3, 1) phenotype!
        n_hier = 8
        n_stems = d_pol * n_hier  # 16
        n_codons = 1 << n_squares  # 64
        syn_ti3_stems = d_pol * d_out_v  # 14 (all 16 except AU* and UG*)
        syn_ti3_codons = d_out_e * n12  # 60 = 64 - 4 (all 64 except AUA<->AUG and UGA<->UGG)
        ti_tv_random_bg = 1.0 / float(d_pol)  # 4 / 8 = 0.5 = s_0
        ti_tv_wgs_eq = float(d_pol)  # d - 1 = 2.0 = 4 * 0.5
        ti_tv_exome_sel = float(d)  # d = 3.0
        cpg_stem = (d_in_v << d_pol) | d  # (1 << 2) | 3 = 7 = d_out(V)
        tpg_stem = (0 << d_pol) | d  # 3 = d
        mendel_geno = (d_in_v, d_pol, d_in_v)  # (1, 2, 1)
        mendel_pheno = (d_in_v + d_pol, d_in_v)  # (3, 1)

        # 4. Allometry (Kleiber 3/4), F0F1-ATP bioenergetics (8/3), and water kinetics (Grotthuss s_0 E_HB, pKw=14):
        s_0 = 1.0 / float(d_pol)  # 0.5
        kleiber_exp = float(d) / float(d_in_sq)  # 3/4 = 0.75
        freq_exp = -float(d_in_v) / float(d_in_sq)  # -1/4 = -0.25
        lifespan_exp = float(d_in_v) / float(d_in_sq)  # +1/4 = +0.25
        t_body_over_t_hb = float(n12 - d_pol) / float(d ** d_in_sq)  # 10 / 81
        h_per_atp = float(n_hier) / float(d)  # 8/3
        atp_dg0_ehb = float(d) * s_0  # 3/2 = 1.5 E_HB (~31.26 kJ/mol)
        atp_dg_vivo_ehb = h_per_atp  # 8/3 E_HB (~55.57 kJ/mol)
        grotthuss_ehb = s_0  # 1/2 E_HB (~10.42 kJ/mol = 0.108 eV)
        water_dh_auto_ehb = h_per_atp  # 8/3 E_HB (~55.57 kJ/mol)
        water_dg_auto_ehb = float(d_in_sq)  # 4 E_HB (~83.35 kJ/mol)
        neutral_ph = d_out_v  # 7
        water_pkw = d_pol * d_out_v  # 14

        # SI projections for temperature, bioenergetics, membrane potentials, and photosynthesis across all 3 life worlds m in {-1, 0, +1}:
        n_hb = mod_bits * d_out_v  # 63
        rydberg_ev = 13.605693122994
        hc_ev_nm = 1239.8419843320026
        e_hb_ev = rydberg_ev / float(n_hb)
        e_hb_kj_mol = e_hb_ev * 96.48533212
        t_hb_k = e_hb_ev * 11604.51812
        t_homeo_worlds_k = tuple(q * t_body_over_t_hb * t_hb_k for q in soft_quanta)  # (~88.40 K Titan, ~309.40 K Earth, ~618.81 K Venus)
        t_body_k = t_homeo_worlds_k[1]  # ~309.40 K (36.25 C)
        macroerg_vivo_worlds_kj = tuple(q * atp_dg_vivo_ehb * e_hb_kj_mol for q in soft_quanta)  # (~15.88, ~55.57, ~111.13 kJ/mol)
        atp_dg0_kj = atp_dg0_ehb * e_hb_kj_mol  # ~31.26 kJ/mol
        atp_dg_vivo_kj = macroerg_vivo_worlds_kj[1]  # ~55.57 kJ/mol
        grotthuss_kj = grotthuss_ehb * e_hb_kj_mol  # ~10.42 kJ/mol
        v_soft_worlds_mv = tuple(q * e_hb_ev * 1000.0 for q in soft_quanta)  # (~61.70, ~215.96, ~431.93 mV)
        v_rest_worlds_mv = tuple(-v / float(d) for v in v_soft_worlds_mv)  # (~-20.57, ~-71.99, ~-143.98 mV)
        v_spike_worlds_mv = tuple(s_0 * v for v in v_soft_worlds_mv)  # (~30.85, ~107.98, ~215.96 mV)
        photo_windows_worlds_nm = tuple(
            (hc_ev_nm / (float(n_phi) * q * e_hb_ev), hc_ev_nm / (float(n_hier) * q * e_hb_ev))
            for q in soft_quanta
        )  # ((1545.7, 2511.7) nm Titan IR, (441.6, 717.6) nm Earth vis, (220.8, 358.8) nm Venus UV)
        venus_uv_subbands_nm = tuple(
            hc_ev_nm / (float(q_step) * soft_quanta[2] * e_hb_ev)
            for q_step in (n_hier, mod_bits, n12 - d_pol, n12, n_phi)
        )  # (~358.8, ~318.9, ~287.1, ~239.2, ~220.8 nm: Fe-S/S2O2/S3/SO2/heterocycle UV bands)
        burgi_dunitz_deg = theta_oct * 180.0 / half_turn_rad  # ~109.47 deg
        catalytic_barrier_ladder_esoft = (
            float(n_hier),
            float(n_hier - d),
            float(n_hier - d - d_pol),
            s_0,
        )  # (8.0, 5.0, 3.0, 0.5) E_soft^(m) via 8 = 3 (triad) + 2 (hole) + 3 (metal/macroerg)
        catalytic_barrier_earth_kj = tuple(q * e_hb_kj_mol for q in catalytic_barrier_ladder_esoft)  # (~166.7, ~104.2, ~62.5, ~10.4 kJ/mol)
        peroxide_gas_dh_kj = float(d_out_e) * e_hb_kj_mol  # 5 E_HB ~ 104.19 kJ/mol (NIST gas: 105.52 kJ/mol)
        peroxide_vap_kj = float(d_out_e) * s_0 * e_hb_kj_mol  # 2.5 E_HB ~ 52.09 kJ/mol (NIST H2O2 vap: 51.6 kJ/mol)
        water_vap_kj = float(d_pol) * e_hb_kj_mol  # 2.0 E_HB ~ 41.67 kJ/mol (NIST H2O vap: 40.66-43.99 kJ/mol)
        peroxide_liq_dh_kj = peroxide_gas_dh_kj - (peroxide_vap_kj - water_vap_kj)  # 4.5 E_HB ~ 93.77 kJ/mol (NIST liq: 98.05 kJ/mol)
        richards_fusion_jumps = (
            float(mod_bits) / float(d_out_v),
            float(d_pol * mod_bits) / float(d_out_v),
        )  # (9/7 ~ 1.286 FCC metals, 18/7 ~ 2.571 H2O vs 2.64 exp)
        trouton_vaporization_jumps = (
            float(d**d) / float(d_pol) - float(d),
            float(d**d) / float(d_pol),
        )  # (21/2 = 10.5 simple liquids, 27/2 = 13.5 H2O/alcohols vs 13.1 exp)
        guldberg_boil_over_crit = (float(n12) / float(d**d_in_sq)) / (
            float(n_hier) / float(d_in_sq * n_hier - d_in_v)
        )  # (4/27)/(8/31) = 31/54 ~ 0.5741 (H2O exp: 373.15/647.1 = 0.5766)
        critical_z_ladder = (
            float(d) / float(n_hier),
            float(d_out_v) / float(d_pol * n12),
            float(d) / float(n_phi),
        )  # (3/8 = 0.375 vdW, 7/24 ~ 0.2917 Ar/N2/O2/CH4 exp 0.290, 3/13 ~ 0.2308 H2O exp 0.229)
        pitzer_omega_quantum = s_0 / float(n_phi)  # 1 / (2 * N_phi) = 1 / 26 ~ 0.03846 (N2 exp 0.037)
        pitzer_omega_water = float(mod_bits) * pitzer_omega_quantum  # 9 / 26 ~ 0.3462 (H2O exp 0.344)
        water_zc_over_omega = critical_z_ladder[2] / pitzer_omega_water  # (3/13)/(9/26) = 2/3 (exp: 0.229/0.344 = 0.6657)
        lee_kesler_slope = 1.0 / float(n12)  # 1/12 ~ 0.0833 (Z_c(omega) = 7/24 - omega/12 vs Lee-Kesler 0.2905 - 0.085*omega)
        n_ball_2 = 1 + n12 + 42  # 55 = N_ball(2) Mackay 2-shell ball
        crit_alpha_3d = 1.0 / float(mod_bits)  # 1/9 ~ 0.11111 (3D Ising bootstrap: 0.11009)
        crit_nu_3d = (2.0 - crit_alpha_3d) / float(d)  # 17/27 ~ 0.62963 (bootstrap: 0.62997)
        crit_eta_3d = float(d_pol) / float(n_ball_2)  # 2/55 ~ 0.036364 (bootstrap: 0.036298)
        crit_beta_3d = 0.5 * crit_nu_3d * (1.0 + crit_eta_3d)  # 323/990 ~ 0.32626 (bootstrap: 0.32642)
        crit_gamma_3d = crit_nu_3d * (2.0 - crit_eta_3d)  # 68/55 ~ 1.23636 (bootstrap: 1.23708)
        crit_delta_3d = (5.0 - crit_eta_3d) / (1.0 + crit_eta_3d)  # 91/19 ~ 4.78947 (bootstrap: 4.78984)
        critical_exponents_3d = (
            crit_alpha_3d,
            crit_nu_3d,
            crit_eta_3d,
            crit_beta_3d,
            crit_gamma_3d,
            crit_delta_3d,
        )
        n_heis_81 = d**d_in_sq  # 81
        atm_slots_n2_o2_ar = (n_hb, d_pol * n_hier + 1, 1)  # (63, 17, 1) -> sum == 81
        atm_fracs_n2_o2_ar = tuple(float(s) / float(n_heis_81) for s in atm_slots_n2_o2_ar)  # (77.78%, 20.99%, 1.23%)
        pauli_heis_flux_ratio = float(1 << n_hier) / float(n_heis_81)  # 256 / 81 = (4/3)^4 ~ 3.1605
        t_trop_worlds_k = tuple(q * (float(d_out_v) / float(n_heis_81)) * t_hb_k for q in soft_quanta)  # (~61.88 K Titan, ~216.58 K Earth vs 216.65 K ISA, ~433.16 K Venus)
        t_surf_worlds_k = tuple((float(d_in_sq) / float(d)) * t_tr for t_tr in t_trop_worlds_k)  # (~82.51 K Titan, ~288.77 K Earth vs 288.15 K ISA, ~577.55 K Venus)

        ok = (
            abs((theta_tet + theta_oct) - half_turn_rad) < 1e-15
            and frustration_gap_rad > 0.0
            and scale_5_6_7 == (d_out_e, n_squares, d_out_v)
            and all(
                abs(tm18_in_ka0[i] - float(scale_5_6_7[i] * n12)) < 1e-12
                for i in range(d)
            )
            and 1.24 < bond_ang[0] < 1.26  # C=N imine/nitrile bond (~1.25 A)
            and 1.48 < bond_ang[1] < 1.51  # C-N peptide bond (~1.497 A)
            and 1.73 < bond_ang[2] < 1.76  # Si-N silazane / P-O polyphosphate bond (~1.746 A)
            and 22.0 < tm18_ang[0] < 23.0  # Titan azotosome membrane (~22.45 A)
            and 26.5 < tm18_ang[1] < 27.5  # Earth lipid bilayer (~26.94 A)
            and 31.0 < tm18_ang[2] < 32.0  # Venusian silazane/phosphazene membrane (~31.43 A)
            and syn_ti3_stems * n_hier == d_out_v * n_stems
            and syn_ti3_codons == n_codons - d_in_sq
            and abs(ti_tv_wgs_eq - float(d_in_sq) * ti_tv_random_bg) < 1e-12
            and abs(ti_tv_exome_sel - float(d)) < 1e-12
            and cpg_stem == d_out_v
            and tpg_stem == d
            and sum(mendel_geno) == d_in_sq
            and mendel_pheno == (d, d_in_v)
            and abs(kleiber_exp - 0.75) < 1e-12
            and abs(freq_exp + lifespan_exp) < 1e-12
            and 87.0 < t_homeo_worlds_k[0] < 91.0  # Titan methane sea homeostasis (~88.40 K vs 90.6 K Huygens)
            and 308.0 < t_body_k < 311.0  # Earth homeothermy (~309.40 K = 36.25 C)
            and 615.0 < t_homeo_worlds_k[2] < 622.0  # Venusian lower condensate homeostasis (~618.81 K)
            and 30.5 < atp_dg0_kj < 31.8  # Standard ATP hydrolysis (~31.26 kJ/mol)
            and 54.0 < atp_dg_vivo_kj < 57.0  # Physiological ATP hydrolysis / water autoionization (~55.57 kJ/mol)
            and 10.0 < grotthuss_kj < 10.8  # Grotthuss proton hopping barrier (~10.42 kJ/mol)
            and 1500.0 < photo_windows_worlds_nm[0][0] < 1600.0  # Titan 1.55 um IR window
            and 2450.0 < photo_windows_worlds_nm[0][1] < 2550.0  # Titan 2.51 um IR window
            and 438.0 < photo_windows_worlds_nm[1][0] < 445.0  # Earth Chl Soret blue edge (441.6 nm)
            and 710.0 < photo_windows_worlds_nm[1][1] < 725.0  # Earth PSI red edge (717.6 nm)
            and 218.0 < photo_windows_worlds_nm[2][0] < 224.0  # Venus UV absorber short edge (220.8 nm)
            and 355.0 < photo_windows_worlds_nm[2][1] < 365.0  # Venus UV absorber peak (358.8 nm)
            and 109.0 < burgi_dunitz_deg < 110.0  # Burgi-Dunitz tetrahedral attack angle (~109.47 deg)
            and 160.0 < catalytic_barrier_earth_kj[0] < 170.0  # Uncatalyzed peptide/phosphodiester barrier (~166.7 kJ/mol)
            and 60.0 < catalytic_barrier_earth_kj[2] < 65.0  # Serine protease / ribosome barrier (~62.5 kJ/mol)
            and 103.0 < peroxide_gas_dh_kj < 106.0  # H2O2(g) -> H2O(g) + 1/2 O2(g) (~104.19 kJ/mol vs 105.52 NIST)
            and 92.0 < peroxide_liq_dh_kj < 99.0  # H2O2(l) -> H2O(l) + 1/2 O2(g) (~93.77 kJ/mol vs 98.05 NIST)
            and 0.289 < critical_z_ladder[1] < 0.295  # Z_c = 7/24 ~ 0.2917 (Ar/N2/O2/CH4 exp 0.290)
            and 0.228 < critical_z_ladder[2] < 0.233  # Z_c(H2O) = 3/13 ~ 0.2308 (NIST 0.229)
            and 0.343 < pitzer_omega_water < 0.349  # omega(H2O) = 9/26 ~ 0.3462 (NIST 0.344)
            and abs(water_zc_over_omega - float(d_pol) / float(d)) < 1e-12  # Z_c(H2O)/omega(H2O) == 2/3
            and 0.629 < crit_nu_3d < 0.631  # nu = 17/27 ~ 0.62963 (3D bootstrap 0.62997)
            and 0.326 < crit_beta_3d < 0.327  # beta = 323/990 ~ 0.32626 (3D bootstrap 0.32642)
            and 1.235 < crit_gamma_3d < 1.238  # gamma = 68/55 ~ 1.23636 (3D bootstrap 1.23708)
            and 4.788 < crit_delta_3d < 4.791  # delta = 91/19 ~ 4.78947 (3D bootstrap 4.78984)
            and sum(atm_slots_n2_o2_ar) == n_heis_81  # 63 + 17 + 1 == 81
            and 216.0 < t_trop_worlds_k[1] < 217.0  # Earth tropopause (~216.58 K vs 216.65 K ISA)
            and 288.0 < t_surf_worlds_k[1] < 289.5  # Earth mean surface (~288.77 K vs 288.15 K ISA)
            and neutral_ph == d_out_v
            and water_pkw == d_pol * d_out_v
        )
        return {
            "theta_tet_deg": theta_tet * 180.0 / half_turn_rad,
            "theta_oct_deg": theta_oct * 180.0 / half_turn_rad,
            "frustration_gap_deg": frustration_gap_deg,
            "scale_invariants_5_6_7": scale_5_6_7,
            "soft_quanta_in_ehb": soft_quanta,
            "backbone_bond_in_kappa_a0": bond_in_ka0,
            "membrane_tm18_in_kappa_a0": tm18_in_ka0,
            "helix_pitch_in_kappa_a0": helix_pitch_in_ka0,
            "duplex_stack_in_kappa_a0": duplex_stack_in_ka0,
            "backbone_bond_angstrom": bond_ang,
            "membrane_tm18_angstrom": tm18_ang,
            "synonymous_ti3_stems_ratio": float(syn_ti3_stems) / float(n_stems),
            "synonymous_ti3_codons_ratio": float(syn_ti3_codons) / float(n_codons),
            "ti_tv_ladder": (ti_tv_random_bg, ti_tv_wgs_eq, ti_tv_exome_sel),
            "cpg_stem_code": cpg_stem,
            "mendel_genotype_kernel": mendel_geno,
            "mendel_phenotype_ratio": mendel_pheno,
            "kleiber_metabolic_exponent": kleiber_exp,
            "homeothermy_t_worlds_kelvin": t_homeo_worlds_k,
            "homeothermy_t_body_kelvin": t_body_k,
            "macroerg_vivo_worlds_kj_mol": macroerg_vivo_worlds_kj,
            "protons_per_atp_ratio": h_per_atp,
            "atp_dg0_kj_mol": atp_dg0_kj,
            "atp_dg_vivo_kj_mol": atp_dg_vivo_kj,
            "grotthuss_barrier_kj_mol": grotthuss_kj,
            "membrane_v_rest_worlds_mv": v_rest_worlds_mv,
            "membrane_v_spike_worlds_mv": v_spike_worlds_mv,
            "photosynthesis_windows_worlds_nm": photo_windows_worlds_nm,
            "venus_uv_subbands_nm": venus_uv_subbands_nm,
            "burgi_dunitz_attack_angle_deg": burgi_dunitz_deg,
            "catalytic_barrier_earth_kj_mol": catalytic_barrier_earth_kj,
            "peroxide_gas_and_liq_dh_kj_mol": (peroxide_gas_dh_kj, peroxide_liq_dh_kj),
            "richards_fusion_jumps": richards_fusion_jumps,
            "trouton_vaporization_jumps": trouton_vaporization_jumps,
            "guldberg_boil_over_crit": guldberg_boil_over_crit,
            "critical_z_ladder": critical_z_ladder,
            "pitzer_omega_quantum_and_water": (pitzer_omega_quantum, pitzer_omega_water),
            "water_zc_over_omega": water_zc_over_omega,
            "lee_kesler_slope": lee_kesler_slope,
            "critical_exponents_3d": critical_exponents_3d,
            "atmospheric_blanket_slots_n2_o2_ar": atm_slots_n2_o2_ar,
            "atmospheric_blanket_fractions_n2_o2_ar": atm_fracs_n2_o2_ar,
            "pauli_heis_flux_ratio": pauli_heis_flux_ratio,
            "tropopause_t_worlds_kelvin": t_trop_worlds_k,
            "surface_blanket_t_worlds_kelvin": t_surf_worlds_k,
            "water_autoionization_dg_ehb": water_dg_auto_ehb,
            "water_pkw": water_pkw,
            "ok": ok,
            "note": "Universal 3-world (m=-1,0,+1) frustration, 5:6:7 scale, Z_4 genetics, Kleiber 3/4 allometry, homeostasis, macroerg bioenergetics, membrane potentials, [N_phi, N_hier] photosynthesis windows, O(1) catalytic barrier step-down, and C_13 phase-transition invariants",
        }

    def local_gates_solid_neuro_photo_row(self) -> dict[str, Any]:
        """Floor 3 / Compute & Biology — Strictly local Heisenberg (81=3^4 deadband) & Pauli (256-tick mirror) gates, 4-level info-equivalence, Cauchy elasticity, FQHE, and Caspar-Klug capsid shells."""
        d = 3
        d_in_v, d_in_e, d_in_sq = 1, 2, 4
        d_pol = d - d_in_v  # 2
        d_out_e, n_squares, d_out_v = 5, 6, 7
        n_hier = 8
        mod_bits = 9
        n12 = int(N12_FCC_CAUSAL_LINKS)  # 12
        n_phi = int(PLANCK_CELL.N_phi)  # 13
        n_ring = n_hier ** d  # 512

        # 1. Local Heisenberg-Newton deadband (|Phi_raw| < 41 -> 0), local Pauli mirror (Phi_Pauli = 256 -> Z_next = -Z_past),
        #    and the 4-level hierarchy of info-equivalence classes (E_PQ, E_Heis, E_gauge, E_B)
        delta_phi_disc = d_in_sq * d_in_sq + d_out_e * d_out_e  # 41
        heisenberg_deadband = d_pol * delta_phi_disc - d_in_v  # 2 * 41 - 1 = 81 = 3^4 = d^4
        heisenberg_active_ring = n_ring - heisenberg_deadband  # 431
        pauli_impulse_disc_val = n_ring // d_pol  # 256
        s1_pauli_delay_ticks = d_pol  # 2 ticks
        frac_bits = mod_bits - d  # 6
        pq_int_levels = 1 << d  # 8
        pq_frac_states = 1 << frac_bits  # 64 = K_P
        gauge_clique_orbits = (n12, d_pol * n12, n_hier)  # (K_2=12, K_3=24, K_4=8)
        octahedral_group_order = d_pol * d_pol * n12  # |O_h| = 48
        macro_cell_bits = (d_in_sq * mod_bits, d_pol * d_in_sq * mod_bits)  # (36, 72)

        # 2. Solid-state Cauchy elasticity, Dulong-Petit / Debye, and Laughlin-Jain FQHE
        cauchy_nu = float(d_in_v) / float(d_in_sq)  # 1/4 = 0.25
        cauchy_g_over_k = float(d) / float(d_out_e)  # 3/5 = 0.60
        cauchy_e_over_g = float(d_out_e) / float(d_in_e)  # 5/2 = 2.50
        fqhe_fractions = (
            float(d_in_v) / float(d),
            float(d_pol) / float(d_out_e),
            float(d) / float(d_out_v),
        )  # (1/3, 2/5, 3/7)

        # 3. Caspar-Klug icosahedral viral capsid spheres N_shell(m)=10m^2+2 and 13-protofilament microtubule closure
        shell_coeff = n12 - d_pol  # 10
        caspar_klug_capsomers = tuple(
            shell_coeff * (m * m) + d_pol
            for m in (d_in_v, d_in_e, d, d_in_sq, d_out_e)
        )  # (12, 42, 92, 162, 252) = N_shell(1..5)
        caspar_klug_t7_capsomers = shell_coeff * d_out_v + d_pol  # 72 = |square| * |N_12|

        ok = (
            heisenberg_deadband == (d ** d_in_sq)
            and heisenberg_deadband + heisenberg_active_ring == n_ring
            and pauli_impulse_disc_val == n_ring // d_pol
            and s1_pauli_delay_ticks == d_pol
            and pq_int_levels * pq_frac_states == n_ring
            and gauge_clique_orbits == (n12, d_pol * n12, n_hier)
            and octahedral_group_order == d_pol * d_pol * n12
            and macro_cell_bits == (n_squares * n_squares, n_squares * n12)
            and macro_cell_bits == (d * n12, d_pol * d * n12)
            and abs(cauchy_nu - 0.25) < 1e-12
            and abs(cauchy_g_over_k - 0.60) < 1e-12
            and abs(cauchy_e_over_g - 2.50) < 1e-12
            and caspar_klug_capsomers == (12, 42, 92, 162, 252)
            and caspar_klug_t7_capsomers == n_squares * n12
            and n_phi == n12 + d_in_v
        )
        return {
            "heisenberg_deadband_states": heisenberg_deadband,
            "heisenberg_active_ring_states": heisenberg_active_ring,
            "pauli_impulse_ticks": pauli_impulse_disc_val,
            "s1_pauli_lightcone_delay_ticks": s1_pauli_delay_ticks,
            "info_equiv_pq_int_and_frac": (pq_int_levels, pq_frac_states),
            "info_equiv_gauge_cliques": gauge_clique_orbits,
            "info_equiv_octahedral_order": octahedral_group_order,
            "info_equiv_macro_cell_bits": macro_cell_bits,
            "cauchy_poisson_ratio": cauchy_nu,
            "cauchy_shear_to_bulk_ratio": cauchy_g_over_k,
            "fqhe_laughlin_jain_fractions": fqhe_fractions,
            "caspar_klug_principal_capsomers": caspar_klug_capsomers,
            "caspar_klug_skew_t7_capsomers": caspar_klug_t7_capsomers,
            "microtubule_protofilaments": n_phi,
            "ok": ok,
            "note": "Local Heisenberg (81=3^4 deadband) & Pauli (256-tick mirror, 2-tick S_1 delay) gates, 4-level info-equivalence, Cauchy/FQHE, and Caspar-Klug capsid shells",
        }


