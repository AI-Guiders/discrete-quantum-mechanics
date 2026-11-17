"""verify_checks.cosmology — ISM screen / CMB-forward dogfood (META §3.0.1 exploratory)."""

from __future__ import annotations

from mt_ca.ism_screen import evaluate_ism_screen_v1, evaluate_ism_screen_v2
from mt_ca.si_constants import SI


def check_ism_screen_v0(device: str = "cpu") -> dict:
    """Fast verify: v1 gates (v2 physics, no sim decay / N_CMB)."""
    del device
    bath = SI.vacuum_bath_row()
    log10_gap = float(bath["log10_T_M_bath_over_CMB"])
    row = evaluate_ism_screen_v1(log10_T_M_over_CMB=log10_gap)
    row["T_M_bath_K"] = bath["T_M_bath_K"]
    return row


def check_ism_screen_v0_sim(size: int = 32, device: str = "cpu") -> dict:
    """Heavier row: wall rms + ν decay extrapolation to N_CMB (v2)."""
    import sys
    from pathlib import Path

    import torch

    from mt_ca.config import MConfig
    from mt_ca.simulator import LatticeFluidSimulator
    from mt_ca.t_validation import nu_coarse_passes

    scripts = Path(__file__).resolve().parents[1] / "scripts"
    if str(scripts) not in sys.path:
        sys.path.insert(0, str(scripts))
    from run_cmb_forward_envelope import calibrate_wall_row  # noqa: WPS433

    if device == "cuda" and not torch.cuda.is_available():
        device = "cpu"

    block = 4
    nz = size
    cfg = MConfig.for_stencil("fcc")
    sim = LatticeFluidSimulator(nz, nz, cfg, nz=nz, device=device)
    nu_list = [1, 4, 16, 64, 256]
    cal = calibrate_wall_row(
        sim,
        cfg,
        nz=nz,
        relaxation=128,
        delta_angle=0.125,
        axis="x",
        block=block,
        iz=nz // 2,
        nu_passes=nu_list,
    )
    bath = SI.vacuum_bath_row()
    bubble = SI.bubble_tick_row()
    nu_ncmb = float(nu_coarse_passes(int(bubble["N_CMB"]), block))
    row = evaluate_ism_screen_v2(
        log10_T_M_over_CMB=float(bath["log10_T_M_bath_over_CMB"]),
        rms_rel_wall=float(cal["rms_rel"]),
        smooth_decay=cal["smooth_decay"],
        nu_at_N_CMB=nu_ncmb,
        block=block,
    )
    row["dims"] = f"{nz}^3"
    row["relaxation"] = cal["relaxation"]
    row["delta_angle"] = cal["delta_angle"]
    row["measured_max_rel"] = cal["max_rel"]
    row["N_CMB_sci"] = bubble["N_CMB_sci"]
    return row


def check_cmb_natural_thermodynamics(device: str = "cpu") -> dict:
    """Verify closed natural-scale (k_B-free) recombination and CMB thermal quanta from η_B = (45/208)α_fs^4."""
    del device
    row = dict(SI.cmb_natural_thermodynamics_row())
    row["id"] = "Cosmo_CMB_natural_thermodynamics"
    return row


def check_iv263_two_epoch_bottleneck(device: str = "cpu") -> dict:
    """Verify two-epoch evolution of IV=263 through the t=256=N_ring/2 bottleneck, relic photon bath, and FCC NN seed growth."""
    import math
    import torch

    from mt_ca.config import MConfig
    from mt_ca.fixed_point import decode_spinor, encode_spinor
    from mt_ca.matter_survey import planckon_instrument
    from mt_ca.projected_collision import heisenberg_phi_min_int, projected_phi_int
    from mt_ca.seeds import boil_ocean_spinor_3d
    from mt_ca.si_constants import N12_FCC_CAUSAL_LINKS, PLANCK_CELL, heisenberg_phi_min_disc
    from mt_ca.simulator import LatticeFluidSimulator
    from mt_ca.z_ring import signed_from_mod

    dev = torch.device("cuda" if (device == "cuda" or torch.cuda.is_available()) else "cpu")
    cfg = MConfig.for_stencil("fcc")
    n_ring = int(PLANCK_CELL.N_ring)  # 512
    n_hier = int(PLANCK_CELL.mod_bits) - 1  # 8
    d_spatial = 3
    phi_min = heisenberg_phi_min_int(cfg)  # 41

    # Use L = 36 with target_center_class = 11 (proven 100% identical to L = 48, 54, 60)
    size = 36
    c = size // 2
    target_center_class = 11
    off = (target_center_class - c) % int(PLANCK_CELL.N_phi)
    z_boil = boil_ocean_spinor_3d(size, size, size, device=dev, class_offset=off)

    zz, yy, xx = torch.meshgrid(
        torch.arange(size, device=dev, dtype=torch.int64),
        torch.arange(size, device=dev, dtype=torch.int64),
        torch.arange(size, device=dev, dtype=torch.int64),
        indexing="ij",
    )
    octant_idx = ((zz >= c).long() << 2) | ((yy >= c).long() << 1) | (xx >= c).long()
    mask8 = (1 << d_spatial) - 1  # 7 (K_3 trihedral corner)
    radius = 2 * d_spatial  # 6
    r2 = (zz - c) ** 2 + (yy - c) ** 2 + (xx - c) ** 2
    ball_mask = (r2 <= radius**2).to(torch.float32)
    step_rad = 2.0 * math.pi * (float(heisenberg_phi_min_disc(phase_bits=cfg.phase_bits)) / float(n_ring))
    bit_m = ((mask8 >> octant_idx) & 1).to(torch.float32)
    bit_m2 = ((mask8 >> (octant_idx ^ d_spatial)) & 1).to(torch.float32)
    phi1 = bit_m * (float(d_spatial) * step_rad) * ball_mask
    phi2 = bit_m2 * (float(d_spatial) * step_rad) * ball_mask
    boost = 1.0 + float(N12_FCC_CAUSAL_LINKS) * ball_mask
    z = z_boil.clone()
    z[..., 0] = z[..., 0] * boost * torch.exp(1j * phi1).to(torch.complex64)
    z[..., 1] = z[..., 1] * boost * torch.exp(1j * phi2).to(torch.complex64)
    f0 = encode_spinor(z, frac_bits=cfg.frac_bits, mod_bits=cfg.phase_bits, gauge_fix=False)
    z0 = decode_spinor(f0, frac_bits=cfg.frac_bits, mod_bits=cfg.phase_bits).to(torch.complex64)

    sim = LatticeFluidSimulator(size, size, cfg, nz=size, device=dev)
    sim.set_field(z0)

    def _snapshot() -> tuple[list[dict], int]:
        inst = planckon_instrument(sim.z, cfg=cfg)
        rows = [r for r in inst["survey"] if r["b"] > 0]
        phi_abs = signed_from_mod(projected_phi_int(sim._f_curr, cfg), cfg.phase_bits).abs()
        photons_ne = int((phi_abs // phi_min).sum().item())
        return rows, photons_ne

    # 1. t = 8 = N_hier: internal dark/photon bottleneck (b_hits = 0, pure photon ball)
    sim.step(n_hier, record_impulses=False)
    rows_8, photons_8 = _snapshot()

    # 2. t = 64: Epoch I peak (b_hits = 6, w_max = 1)
    sim.step(64 - sim.tick, record_impulses=False)
    rows_64, photons_64 = _snapshot()

    # 3. t = 256 = N_ring / 2: half-ring bottleneck (b_hits = 1 relic seed + relic photon bath)
    t_neck = n_ring // 2
    sim.step(t_neck - sim.tick, record_impulses=False)
    ckpt_256 = sim.checkpoint_dict()
    rows_256, photons_256 = _snapshot()
    relic_offset = (
        (rows_256[0]["iz"] - c, rows_256[0]["y"] - c, rows_256[0]["x"] - c)
        if rows_256
        else (0, 0, 0)
    )

    # 4. Epoch II (t = 272..512, step 2*N_hier = 16): BBN winding census |w| in {1, 2, 3},
    #    t = 336 3-quantum core (w_max = d) at 1 FCC NN step from relic_offset, and t = 352 peak (b_hits = N_hier)
    counts_by_w = {1: 0, 2: 0, 3: 0}
    mass_by_w = {1: 0, 2: 0, 3: 0}
    w_max_336 = 0.0
    fcc_l1_dist_to_relic = 999
    rows_352: list[dict] = []

    step_stride = (d_spatial - 1) * n_hier  # 16
    for target_t in range(t_neck + step_stride, n_ring + 1, step_stride):
        sim.step(target_t - sim.tick, record_impulses=False)
        rows_t, _ = _snapshot()
        for r in rows_t:
            w_int = round(abs(r["w_auto"]))
            if w_int in counts_by_w:
                counts_by_w[w_int] += 1
                mass_by_w[w_int] += w_int
        if target_t == 336:
            w_max_336 = max((abs(r["w_auto"]) for r in rows_t), default=0.0)
            core3_rows = [r for r in rows_t if round(abs(r["w_auto"])) == d_spatial]
            if core3_rows:
                fcc_l1_dist_to_relic = (
                    abs((core3_rows[0]["iz"] - c) - relic_offset[0])
                    + abs((core3_rows[0]["y"] - c) - relic_offset[1])
                    + abs((core3_rows[0]["x"] - c) - relic_offset[2])
                )
        elif target_t == 352:
            rows_352 = rows_t

    total_winding_mass = sum(mass_by_w.values())
    w2_mass_share = float(mass_by_w[2]) / float(total_winding_mass) if total_winding_mass > 0 else 0.0
    one_quantum_w2_mass_step = float(d_spatial - 1) / float(total_winding_mass) if total_winding_mass > 0 else 1.0
    yp_bare = 1.0 / float(d_spatial + 1)  # 1 / d_in(□) = 0.25

    # Verify bit-exact resume from t = 256 checkpoint to t = 512
    sim_resumed = LatticeFluidSimulator.from_checkpoint(ckpt_256, device=dev)
    sim_resumed.step(n_ring - t_neck, record_impulses=False)
    ckpt_resume_ok = bool(
        torch.equal(sim_resumed._f_curr, sim._f_curr)
        and torch.equal(sim_resumed._f_past, sim._f_past)
    )

    ok = (
        len(rows_8) == 0
        and photons_8 > 1000
        and len(rows_64) == 6
        and len(rows_256) == 1
        and photons_256 > 2500
        and round(w_max_336) == d_spatial
        and fcc_l1_dist_to_relic == (d_spatial - 1)  # exact 1 nearest-neighbor FCC edge |(±1, ±1, 0)|_1 = 2
        and len(rows_352) == n_hier
        and counts_by_w == {1: 61, 2: 11, 3: 1}
        and abs(w2_mass_share - yp_bare) < one_quantum_w2_mass_step
        and ckpt_resume_ok
    )
    return {
        "id": "Cosmo_IV263_two_epoch_bottleneck",
        "world_seed": "universe_iv_9bit_spinor_3d",
        "t8_b_hits": len(rows_8),
        "t8_photon_quanta": photons_8,
        "t64_b_hits": len(rows_64),
        "t256_neck_b_hits": len(rows_256),
        "t256_relic_offset_from_center": relic_offset,
        "t256_relic_photon_quanta": photons_256,
        "t336_w_max": w_max_336,
        "t336_core3_fcc_l1_dist_to_relic": fcc_l1_dist_to_relic,
        "t352_peak_b_hits": len(rows_352),
        "epoch2_winding_node_counts": counts_by_w,
        "epoch2_w2_winding_mass_share": w2_mass_share,
        "epoch2_one_quantum_w2_mass_step": one_quantum_w2_mass_step,
        "checkpoint_256_resume_bit_exact": ckpt_resume_ok,
        "ok": ok,
        "note": "CE-C-04: IV=263 two-epoch cascade through t=256=N_ring/2 bottleneck, w=3 seed growth, and BBN w=2 mass share 22/86 within 1 discrete quantum of 1/d_in(□)",
    }

