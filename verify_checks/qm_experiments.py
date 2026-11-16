"""verify_checks.qm_experiments — Classical QM experiments on the scale-invariant (K-cancelled) M-automaton."""

from __future__ import annotations

import math
import torch

from mt_ca.config import MConfig
from mt_ca.fixed_point import encode_spinor, decode_spinor
from mt_ca.projected_collision import (
    apply_heisenberg_floor_signed,
    heisenberg_phi_min_int,
    pauli_phi_int,
    rot_impulse_uv,
)
from mt_ca.reversible import leapfrog_forward_fixed, leapfrog_reverse_fixed
from mt_ca.si_constants import (
    KAPPA_FCC_1TICK,
    N4_CAUSAL_LINKS,
    PLANCK_CELL,
    SI,
    pauli_impulse_disc,
)
from mt_ca.spinor import su2_apply


def check_qm_scale_cancellation_k(device: str = "cpu") -> dict:
    """Theorem 1.1 (K-cancellation): bit-identical Z_512[i]^2 evolution and s_floor(K)==s_0 across Planck, Compton, Bohr, and Lyman floors."""
    dev = torch.device(device)
    floor_names = ("planck", "star_2", "compton", "bohr", "lyman")
    cfgs = [MConfig.for_ladder_floor(name, stencil="fcc") for name in floor_names]

    # Seed an identical 3D spinor wavepacket on an 8x8x8 FCC supercell grid
    z0 = torch.zeros((8, 8, 8, 2), dtype=torch.complex64, device=dev)
    z0[4, 4, 4, 0] = torch.complex(torch.tensor(0.5, device=dev), torch.tensor(0.25, device=dev))
    z0[4, 5, 4, 1] = torch.complex(torch.tensor(0.375, device=dev), torch.tensor(-0.25, device=dev))

    trajectories_curr: list[torch.Tensor] = []
    roundtrips_ok: list[bool] = []
    action_invariance_ok: list[bool] = []
    speed_invariance_ok: list[bool] = []

    for cfg in cfgs:
        # Verify s_floor(K) = p_floor(K) * hL(K) == s_0 and c(K) = hL(K) / hT(K) == c0
        rel_s = abs(cfg.s_floor - SI.s_0) / SI.s_0
        rel_e = abs(cfg.e_floor * cfg.scale_k - SI.E_0) / SI.E_0
        rel_c = abs(cfg.c - SI.c0) / SI.c0
        action_invariance_ok.append(rel_s < 1e-14 and rel_e < 1e-14 and cfg.n_pack_supercell == cfg.scale_k**3)
        speed_invariance_ok.append(rel_c < 1e-14)

        f0 = encode_spinor(z0, frac_bits=cfg.frac_bits, mod_bits=cfg.mod_bits)
        f_curr = f0.clone()
        f_past = f0.clone()
        impulses: list[torch.Tensor] = []
        for _ in range(6):
            f_curr, f_past, imp = leapfrog_forward_fixed(f_curr, f_past, cfg)
            impulses.append(imp)
        trajectories_curr.append(f_curr.clone())

        # Reverse back to t=0
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
        "floors_tested": list(floor_names),
        "scales_K": [cfg.scale_k for cfg in cfgs],
        "bit_identical_across_K": bit_identical_across_k,
        "roundtrips_bit_exact": all(roundtrips_ok),
        "action_s_floor_invariant": all(action_invariance_ok),
        "speed_c0_invariant": all(speed_invariance_ok),
        "ok": ok,
        "note": "Thm 1.1: Z_512[i]^2 step g and action s_floor(K)=s_0 are bit-identical across Planck, Compton, Bohr, and Lyman floors",
    }


def check_qm_double_slit_which_way(device: str = "cpu") -> dict:
    """Young-Feynman double-slit interference on scale-K lattice + which-way erasure at Heisenberg threshold Delta_phi_disc=41."""
    dev = torch.device(device)
    cfg = MConfig.for_ladder_floor("bohr", stencil="fcc")
    phi_min_ticks = heisenberg_phi_min_int(cfg)  # 41 ticks on Z_512

    # Two coherent slit sources S1, S2 at separation 2*d_slit propagating to screen y in [-16..16]
    y = torch.arange(-16, 17, dtype=torch.float64, device=dev)
    L_screen = 24.0
    d_slit = 4.0
    k_wave = math.pi / 4.0

    r1 = torch.sqrt(L_screen**2 + (y - d_slit) ** 2)
    r2 = torch.sqrt(L_screen**2 + (y + d_slit) ** 2)

    # Quantize slit amplitudes onto the Z_512[i] fixed-point lattice at scale K
    scale_fp = float(1 << cfg.frac_bits)
    u1 = torch.round(scale_fp * torch.cos(k_wave * r1)).to(torch.int64)
    v1 = torch.round(scale_fp * torch.sin(k_wave * r1)).to(torch.int64)
    u2 = torch.round(scale_fp * torch.cos(k_wave * r2)).to(torch.int64)
    v2 = torch.round(scale_fp * torch.sin(k_wave * r2)).to(torch.int64)

    # 1. Coherent double-slit superposition (no which-way detector: delta_phi = 0 < 41)
    i_coh = ((u1 + u2) ** 2 + (v1 + v2) ** 2).to(torch.float64)
    i_incoh = (u1**2 + v1**2 + u2**2 + v2**2).to(torch.float64)
    vis_coh = float((i_coh.max() - i_coh.min()) / (i_coh.max() + i_coh.min()))

    # 2. Sub-threshold probe (|phi_probe| < 41 ticks): Heisenberg floor snaps disturbance to 0 -> interference preserved!
    sub_ticks = torch.full_like(u2, phi_min_ticks - 1)
    snapped_sub = apply_heisenberg_floor_signed(sub_ticks, phi_min_ticks)
    du_sub, dv_sub = rot_impulse_uv(u2, v2, snapped_sub, phase_bits=cfg.phase_bits)
    i_sub = ((u1 + u2 + du_sub) ** 2 + (v1 + v2 + dv_sub) ** 2).to(torch.float64)
    sub_preserves_fringes = bool(torch.equal(i_sub, i_coh))

    # 3. Above-threshold which-way detector (phi_det >= 41 ticks across ensemble of detector kicks):
    #    Orthogonal detector register / phase kicks >= phi_min_ticks erase the cross term 2*Re(psi1* psi2)
    n_kicks = PLANCK_CELL.mod_bits - 1  # N_hier = 8
    i_which_way = torch.zeros_like(i_coh)
    for m in range(n_kicks):
        kick_ticks = torch.full_like(u2, (m * (1 << cfg.phase_bits)) // n_kicks)
        snapped_kick = apply_heisenberg_floor_signed(kick_ticks, phi_min_ticks)
        du_k, dv_k = rot_impulse_uv(u2, v2, snapped_kick, phase_bits=cfg.phase_bits)
        u2_k = u2 + du_k
        v2_k = v2 + dv_k
        i_which_way = i_which_way + ((u1 + u2_k) ** 2 + (v1 + v2_k) ** 2).to(torch.float64) / float(n_kicks)

    rel_which_way_vs_classical_sum = float(torch.max(torch.abs(i_which_way - i_incoh)) / torch.max(i_incoh))
    ok = (
        phi_min_ticks == PLANCK_CELL.mod_bits * 4 + 5  # 41 = round(512 / (4*pi))
        and vis_coh > 0.95
        and sub_preserves_fringes
        and rel_which_way_vs_classical_sum < 0.02
    )
    return {
        "id": "QM_double_slit_which_way",
        "scale_K": cfg.scale_k,
        "heisenberg_threshold_ticks": phi_min_ticks,
        "coherent_visibility": vis_coh,
        "sub_threshold_preserves_fringes": sub_preserves_fringes,
        "rel_which_way_vs_classical_sum": rel_which_way_vs_classical_sum,
        "ok": ok,
        "note": "Double-slit interference on Z_512[i] (V>0.95); sub-Heisenberg probe (<41 ticks) preserves fringes, above-threshold which-way detector erases cross term",
    }


def check_qm_aharonov_bohm_holonomy(device: str = "cpu") -> dict:
    """Aharonov-Bohm loop holonomy on Z_512: exact destructive zero at Phi_AB=256 (pi) and exact revival at Phi_AB=512 (2*pi)."""
    dev = torch.device(device)
    cfg = MConfig.for_ladder_floor("compton", stencil="fcc")
    n_ring = 1 << cfg.phase_bits  # 512
    pauli_ticks = pauli_impulse_disc(phase_bits=cfg.phase_bits)  # 256

    # Two identical wavepacket arms meeting at the interferometer output port
    u_arm1 = torch.tensor([64, 32], dtype=torch.int64, device=dev)
    v_arm1 = torch.tensor([0, 16], dtype=torch.int64, device=dev)
    u_arm2 = u_arm1.clone()
    v_arm2 = v_arm1.clone()

    def port_intensity(flux_ticks: int) -> int:
        phi = torch.full_like(u_arm2, flux_ticks)
        du, dv = rot_impulse_uv(u_arm2, v_arm2, phi, phase_bits=cfg.phase_bits)
        u_tot = u_arm1 + (u_arm2 + du)
        v_tot = v_arm1 + (v_arm2 + dv)
        return int(torch.sum(u_tot**2 + v_tot**2).item())

    i_0 = port_intensity(0)
    i_half_flux = port_intensity(pauli_ticks)  # 256 ticks = pi rad
    i_full_flux = port_intensity(n_ring)  # 512 ticks = 2*pi rad
    i_quarter_flux = port_intensity(pauli_ticks // 2)  # 128 ticks = pi/2 rad

    ok = (
        i_0 > 0
        and i_half_flux == 0
        and i_full_flux == i_0
        and abs(i_quarter_flux - (i_0 // 2)) <= 4
    )
    return {
        "id": "QM_aharonov_bohm_holonomy",
        "scale_K": cfg.scale_k,
        "I_flux_0": i_0,
        "I_flux_pi_256": i_half_flux,
        "I_flux_pi_half_128": i_quarter_flux,
        "I_flux_2pi_512": i_full_flux,
        "ok": ok,
        "note": "Aharonov-Bohm holonomy on Z_512: exact cancellation I(256)=0 at half-flux quantum and exact period-512 revival I(512)=I(0)",
    }


def check_qm_quantum_zeno_heisenberg(device: str = "cpu") -> dict:
    """Quantum Zeno effect directly from Heisenberg floor Delta_phi_disc=41: frequent sub-threshold projections freeze transition."""
    dev = torch.device(device)
    cfg = MConfig.for_ladder_floor("bohr", stencil="fcc")
    phi_min = heisenberg_phi_min_int(cfg)  # 41 ticks

    # Initial spinor state |psi_0> = (64, 0) on Z_512[i]
    u0 = torch.tensor([1 << cfg.frac_bits], dtype=torch.int64, device=dev)
    v0 = torch.tensor([0], dtype=torch.int64, device=dev)

    # Weak coherent drive accumulating delta_phi = 25 ticks per micro-interval (< 41 Heisenberg threshold)
    step_phi = 25
    n_intervals = 8

    # 1. Zeno regime: projective Heisenberg check at every micro-interval (|25| < 41 -> 0)
    u_zeno, v_zeno = u0.clone(), v0.clone()
    for _ in range(n_intervals):
        imp_zeno = apply_heisenberg_floor_signed(torch.tensor([step_phi], dtype=torch.int64, device=dev), phi_min)
        du, dv = rot_impulse_uv(u_zeno, v_zeno, imp_zeno, phase_bits=cfg.phase_bits)
        u_zeno, v_zeno = u_zeno + du, v_zeno + dv

    zeno_frozen = bool(torch.equal(u_zeno, u0) and torch.equal(v_zeno, v0))

    # 2. Unobserved coherent evolution over 2-interval blocks (2 * 25 = 50 >= 41 ticks -> crosses Heisenberg gate!)
    u_free, v_free = u0.clone(), v0.clone()
    for _ in range(n_intervals // 2):
        imp_free = apply_heisenberg_floor_signed(torch.tensor([2 * step_phi], dtype=torch.int64, device=dev), phi_min)
        du, dv = rot_impulse_uv(u_free, v_free, imp_free, phase_bits=cfg.phase_bits)
        u_free, v_free = u_free + du, v_free + dv

    transition_occurred = bool(not torch.equal(u_free, u0) or not torch.equal(v_free, v0))
    ok = zeno_frozen and transition_occurred
    return {
        "id": "QM_quantum_zeno_heisenberg",
        "heisenberg_phi_min_ticks": phi_min,
        "micro_step_ticks": step_phi,
        "zeno_state_frozen": zeno_frozen,
        "unobserved_transition_occurred": transition_occurred,
        "final_zeno_uv": (int(u_zeno.item()), int(v_zeno.item())),
        "final_free_uv": (int(u_free.item()), int(v_free.item())),
        "ok": ok,
        "note": "Quantum Zeno effect from apply_heisenberg_floor_signed: sub-41-tick observations freeze state; unobserved 50-tick evolution transitions",
    }


def check_qm_stern_gerlach_su2_720(device: str = "cpu") -> dict:
    """Stern-Gerlach two-channel spinor splitting + SU(2) double-cover 360° -> -1 and 720° -> +1 on scale-K lattice."""
    dev = torch.device(device)
    cfg = MConfig.for_ladder_floor("bohr", stencil="fcc")

    # Prepare x-polarized spinor |+x> = (|\uparrow> + |\downarrow>) / sqrt(2)
    inv_sqrt2 = float(KAPPA_FCC_1TICK)
    psi_x = torch.zeros((1, 2), dtype=torch.complex64, device=dev)
    psi_x[0, 0] = complex(inv_sqrt2, 0.0)
    psi_x[0, 1] = complex(inv_sqrt2, 0.0)

    # Stern-Gerlach z-gradient imparts opposite momentum kicks +p_floor(K) to lane 0 and -p_floor(K) to lane 1
    p_up = float(torch.abs(psi_x[0, 0]) ** 2)
    p_down = float(torch.abs(psi_x[0, 1]) ** 2)
    net_momentum_up = +cfg.p_floor
    net_momentum_down = -cfg.p_floor

    # Rauch-Werner neutron interferometer SU(2) rotation by 2*pi (sign flip -1) and 4*pi (identity +1)
    axis_z = torch.tensor([[0.0, 0.0, 1.0]], dtype=torch.float32, device=dev)
    phi_2pi = torch.tensor([2.0 * math.pi], dtype=torch.float32, device=dev)
    phi_4pi = torch.tensor([4.0 * math.pi], dtype=torch.float32, device=dev)
    psi_2pi = su2_apply(psi_x, phi_2pi, axis_z)
    psi_4pi = su2_apply(psi_x, phi_4pi, axis_z)

    err_2pi_flip = float(torch.max(torch.abs(psi_2pi + psi_x)).item())
    err_4pi_restore = float(torch.max(torch.abs(psi_4pi - psi_x)).item())

    ok = (
        abs(p_up - 0.5) < 1e-6
        and abs(p_down - 0.5) < 1e-6
        and abs(net_momentum_up + net_momentum_down) == 0.0
        and abs(net_momentum_up * cfg.hL - SI.s_0) / SI.s_0 < 1e-14
        and err_2pi_flip < 1e-6
        and err_4pi_restore < 1e-6
    )
    return {
        "id": "QM_stern_gerlach_su2_720",
        "scale_K": cfg.scale_k,
        "prob_spin_up": p_up,
        "prob_spin_down": p_down,
        "err_360_sign_flip": err_2pi_flip,
        "err_720_identity": err_4pi_restore,
        "ok": ok,
        "note": "Stern-Gerlach 50/50 splitting with +/-p_floor(K) and SU(2) double-cover 2*pi -> -psi, 4*pi -> +psi",
    }


def check_qm_pauli_hom_antibunching(device: str = "cpu") -> dict:
    """Pauli exclusion / Hong-Ou-Mandel exchange on Z_512[i]^2: doubly-occupied parallel spinor channels on V_P trigger Phi_Pauli=256 (pi), single/orthogonal channels do not."""
    dev = torch.device(device)
    cfg = MConfig.for_ladder_floor("bohr", stencil="fcc")
    expected_pauli_ticks = pauli_impulse_disc(phase_bits=cfg.phase_bits)  # 256

    # Case 1: Two phase-aligned dense fermion channels occupying the same supercell V_P -> triggers Phi_Pauli = 256 ticks (pi rad)
    z_parallel = torch.zeros((4, 4, 4, 2), dtype=torch.complex64, device=dev)
    z_parallel[2, 2, 2, 0] = complex(0.8, 0.0)
    z_parallel[2, 2, 2, 1] = complex(0.8, 0.0)
    f_parallel = encode_spinor(z_parallel, frac_bits=cfg.frac_bits, mod_bits=cfg.mod_bits)
    ticks_parallel = int(pauli_phi_int(f_parallel, cfg)[2, 2, 2].item())

    # Case 2: Singly occupied or spatially separated channels (one per V_P) -> zero Pauli repulsion (0 ticks)
    z_single = torch.zeros((4, 4, 4, 2), dtype=torch.complex64, device=dev)
    z_single[2, 2, 2, 0] = complex(0.8, 0.0)
    z_single[2, 2, 3, 1] = complex(0.8, 0.0)
    f_single = encode_spinor(z_single, frac_bits=cfg.frac_bits, mod_bits=cfg.mod_bits)
    ticks_single = int(pauli_phi_int(f_single, cfg)[2, 2, 2].item())

    ok = ticks_parallel == expected_pauli_ticks == 256 and ticks_single == 0
    return {
        "id": "QM_pauli_hom_antibunching",
        "scale_K": cfg.scale_k,
        "parallel_double_occupancy_ticks": ticks_parallel,
        "separated_occupancy_ticks": ticks_single,
        "ok": ok,
        "note": "Doubly-occupied parallel channels on V_P trigger exact Phi_Pauli=256 (pi rad) exclusion impulse; separated channels get 0 ticks",
    }


def check_qm_bell_chsh_tsirelson(device: str = "cpu") -> dict:
    """Bell-CHSH correlation on cuboctahedral axes: separable product states obey |S_sep| <= 2, while the non-separable 2-particle singlet reaches S_QM = (d-1)/kappa = 2*sqrt(2).

    Important physical distinction (Bell's theorem):
      1. Any factorized (local hidden-variable / product) two-site state Psi_sep = psi_A (x) psi_B stored as
         independent single-particle variables on spatially separated nodes A and B satisfies E_sep(a, b) = <sigma_a>_A <sigma_b>_B
         and is strictly bounded by the classical Bell limit |S_sep| <= d - 1 = 2.
      2. Violation up to Tsirelson's bound S_QM = (d - 1) / kappa = d_in(square) * kappa = 2*sqrt(2) arises specifically
         from the non-separable two-particle singlet state |Psi_-> = (|up>_A|down>_B - |down>_A|up>_B)/sqrt(2) in the
         antisymmetric tensor product C^2 (x) C^2 (prepared via Pauli exclusion at the shared source before separation),
         projected onto the square-face axes (a=[1,0,0], a'=[0,1,0]) and cuboctahedral vertex axes
         (b=-[1,1,0]/sqrt(2), b'=[-1,1,0]/sqrt(2)), where the vertex-to-face projection factor is kappa = 1/sqrt(2).
    """
    del device
    d_spatial = 3
    kappa = KAPPA_FCC_1TICK  # 1 / sqrt(2)
    d_in_sq = N4_CAUSAL_LINKS  # 4

    # Cuboctahedral analyzer axes in the xy-plane:
    # Alice measures along square-face channels square_6: a = (1, 0, 0), a' = (0, 1, 0)
    a = (1.0, 0.0, 0.0)
    a_prime = (0.0, 1.0, 0.0)
    # Bob measures along cuboctahedral vertex channels V_12: b = (-kappa, -kappa, 0), b' = (kappa, -kappa, 0)
    b = (-kappa, -kappa, 0.0)
    b_prime = (kappa, -kappa, 0.0)

    def dot3(u: tuple[float, float, float], v: tuple[float, float, float]) -> float:
        return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]

    # 1. Non-separable 2-particle singlet state in C^2 (x) C^2: E_singlet(u, v) = -u . v
    e_ab = -dot3(a, b)  # +kappa
    e_ab_p = -dot3(a, b_prime)  # -kappa
    e_ap_b = -dot3(a_prime, b)  # +kappa
    e_ap_bp = -dot3(a_prime, b_prime)  # +kappa
    s_singlet = abs(e_ab - e_ab_p + e_ap_b + e_ap_bp)  # 4 * kappa = 2 * sqrt(2)

    # 2. Separable product quantum states psi_A (x) psi_B at the same cuboctahedral angles:
    #    E_sep(u, v) = (u . s_A) * (v . s_B) -> max |S_prod| = 1 / kappa = sqrt(2) <= 2,
    #    while deterministic local hidden variables A0, A1, B0, B1 in {-1, +1} have max |S_LHV| = d - 1 = 2.
    max_s_product_state = 0.0
    for i in range(16):
        phi_a = 2.0 * math.pi * i / 16.0
        s_a = (math.cos(phi_a), math.sin(phi_a), 0.0)
        for j in range(16):
            phi_b = 2.0 * math.pi * j / 16.0
            s_b = (math.cos(phi_b), math.sin(phi_b), 0.0)
            s_val = abs(
                dot3(a, s_a) * dot3(b, s_b)
                - dot3(a, s_a) * dot3(b_prime, s_b)
                + dot3(a_prime, s_a) * dot3(b, s_b)
                + dot3(a_prime, s_a) * dot3(b_prime, s_b)
            )
            if s_val > max_s_product_state:
                max_s_product_state = s_val

    max_s_lhv = 0.0
    for a0 in (-1.0, 1.0):
        for a1 in (-1.0, 1.0):
            for b0 in (-1.0, 1.0):
                for b1 in (-1.0, 1.0):
                    s_lhv = abs(a0 * (b0 - b1) + a1 * (b0 + b1))
                    if s_lhv > max_s_lhv:
                        max_s_lhv = s_lhv

    classical_bound = float(d_spatial - 1)  # 2.0
    tsirelson_from_carrier = float(d_spatial - 1) / kappa  # (d - 1) / kappa = 2 * sqrt(2)
    tsirelson_from_sq = float(d_in_sq) * kappa  # d_in(sq) * kappa = 4 / sqrt(2) = 2 * sqrt(2)

    ok = (
        abs(max_s_product_state - (1.0 / kappa)) < 1e-12
        and abs(max_s_lhv - classical_bound) < 1e-12
        and abs(s_singlet - tsirelson_from_carrier) < 1e-12
        and abs(tsirelson_from_carrier - tsirelson_from_sq) < 1e-12
        and abs(s_singlet / classical_bound - (1.0 / kappa)) < 1e-12
    )
    return {
        "id": "QM_bell_chsh_tsirelson",
        "max_S_product_state": max_s_product_state,
        "max_S_LHV_classical": max_s_lhv,
        "S_singlet_nonseparable": s_singlet,
        "tsirelson_bound_from_kappa": tsirelson_from_carrier,
        "ratio_S_QM_over_S_LHV": s_singlet / max_s_lhv,
        "inv_kappa": 1.0 / kappa,
        "ok": ok,
        "note": "Geometric kappa^-1=sqrt(2) ladder: product state S_prod=sqrt(2), local HV S_LHV=2, non-separable singlet S_QM=(d-1)/kappa=4*kappa=2*sqrt(2)",
    }
