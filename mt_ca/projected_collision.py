"""Projected collision — Z_N[i] modular DA holonomy + saturating Φ + LUT rot (§3.12.5–6)."""

from __future__ import annotations

import torch

from mt_ca.carrier_core import (
    CANONICAL_CARRIER,
    carrier_collision_impulse,
    carrier_gate_phi,
    carrier_reverse,
    carrier_step,
    edge_proj_cos_int,
    edge_proj_sin_int,
    face_quadrant_ticks,
    int_neighbor_sum_core,
    pauli_phi_core,
    signed_lanes_core,
    wrap_ring_signed,
)
from mt_ca.config import MConfig
from mt_ca.si_constants import heisenberg_phi_min_disc
from mt_ca.z_ring import mod_lane

LUT_BITS = CANONICAL_CARRIER.mod_bits
LUT_SIZE = CANONICAL_CARRIER.n_ring
TRIG_SHIFT = CANONICAL_CARRIER.n_tri - 1  # = 7 so Q_□ = 2^TRIG_SHIFT = 128


def _build_trig_lut(device: torch.device) -> tuple[torch.Tensor, torch.Tensor]:
    """Closed integer face-projection LUT (C(Δφ), S(Δφ)) on Z_{N_ring} (no math.pi / torch.cos / torch.sin)."""
    idx = torch.arange(LUT_SIZE, device=device, dtype=torch.int64)
    cu = edge_proj_cos_int(idx, LUT_BITS)
    sv = edge_proj_sin_int(idx, LUT_BITS)
    return cu, sv


_TRIG_CACHE: dict[str, tuple[torch.Tensor, torch.Tensor]] = {}


def trig_lut(device: torch.device) -> tuple[torch.Tensor, torch.Tensor]:
    key = str(device)
    if key not in _TRIG_CACHE:
        _TRIG_CACHE[key] = _build_trig_lut(device)
    return _TRIG_CACHE[key]


def k_p_int(cfg: MConfig) -> int:
    """K_P = 2^frac_bits = 2^|□| = 64 integer quanta on M."""
    return 1 << cfg.frac_bits


def heisenberg_phi_min_int(cfg: MConfig) -> int:
    """Δφ_min = ½ rad → integer ticks mod N_ring (§3.12.6)."""
    return heisenberg_phi_min_disc(
        phase_bits=cfg.phase_bits,
        delta_phi_min=cfg.heisenberg_phi_min,
    )


def signed_lanes(f: torch.Tensor, cfg: MConfig) -> torch.Tensor:
    """Delegate to carrier_core.signed_lanes_core."""
    return signed_lanes_core(f, cfg.mod_bits)


def int_neighbor_sum(f: torch.Tensor, stencil: str) -> torch.Tensor:
    """Delegate to carrier_core.int_neighbor_sum_core."""
    return int_neighbor_sum_core(f, stencil)


def apply_heisenberg_floor_signed(
    phi_signed: torch.Tensor,
    phi_min: int,
) -> torch.Tensor:
    """Delegate Heisenberg deadband to carrier_core.apply_heisenberg_floor_core."""
    from mt_ca.carrier_core import apply_heisenberg_floor_core

    return apply_heisenberg_floor_core(phi_signed, phi_min)


def saturating_phi_impulse(
    zeta_r: torch.Tensor,
    zeta_i: torch.Tensor,
    rho2: torch.Tensor,
    cfg: MConfig,
) -> torch.Tensor:
    """Delegate saturating gate Φ to carrier_core.carrier_saturating_gate_core."""
    from mt_ca.carrier_core import carrier_saturating_gate_core

    kp = k_p_int(cfg)
    return carrier_saturating_gate_core(
        zeta_r,
        zeta_i,
        rho2,
        scale_ticks=kp,
        eps_quanta2=kp,
        mod_bits=cfg.mod_bits,
        heisenberg_floor=cfg.heisenberg_floor,
        phi_min=heisenberg_phi_min_int(cfg),
    )


def pauli_phi_int(f: torch.Tensor, cfg: MConfig) -> torch.Tensor:
    """Delegate to carrier_core.pauli_phi_core."""
    return pauli_phi_core(
        f,
        mod_bits=cfg.mod_bits,
        frac_bits=cfg.frac_bits,
        phi_min=heisenberg_phi_min_int(cfg),
        enabled=cfg.pauli_exclusion,
    )


def projected_phi_int(f: torch.Tensor, cfg: MConfig) -> torch.Tensor:
    """Delegate to carrier_core.carrier_gate_phi."""
    return carrier_gate_phi(f, cfg)


def projected_collision_impulse(f: torch.Tensor, cfg: MConfig) -> torch.Tensor:
    """Delegate to carrier_core.carrier_collision_impulse."""
    return carrier_collision_impulse(f, cfg)


def projected_step(
    f_curr: torch.Tensor,
    f_past: torch.Tensor,
    cfg: MConfig,
) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """Delegate to carrier_core.carrier_step (exact bijection on Z_{N_ring}[i]^2)."""
    return carrier_step(f_curr, f_past, cfg)


def projected_reverse(
    f_curr: torch.Tensor,
    f_next: torch.Tensor,
    cfg: MConfig,
) -> tuple[torch.Tensor, torch.Tensor]:
    """Delegate to carrier_core.carrier_reverse (literal reverse without impulse stack)."""
    return carrier_reverse(f_curr, f_next, cfg)


projected_step_fixed = projected_step
projected_reverse_fixed = projected_reverse


# ---------------------------------------------------------------------------
# Polar cell register (μ, φ_disc) ∈ Z_{2^frac_bits} × Z_{2^mod_bits}
# and closed trig-free face projections C(A), S(A) on cuboctahedron faces
# (Book def:internal-coords & Theorem thm:trig-free-face-projections, §3.12.5d:
# Q_□ = N_ring / d_in(□) = 2^(|△|−1) = 2·K_P = 128, Φ_Pauli = N_ring/2 = 256,
# C(A) = Q_□ − |A|, S(A) = C(wrap(A − Q_□)), |C(A)| + |S(A)| ≡ Q_□.)
# ---------------------------------------------------------------------------


def ring_trig_lut(n_ring: int, device: torch.device) -> tuple[torch.Tensor, torch.Tensor]:
    """Delegate to carrier_core.ring_face_lut_core."""
    from mt_ca.carrier_core import ring_face_lut_core

    return ring_face_lut_core(n_ring, device)


def encode_polar_spinor(
    z: torch.Tensor,
    *,
    frac_bits: int,
    mod_bits: int,
) -> torch.Tensor:
    """Delegate complex->polar encoding to the M↔T bridge (mt_ca.m_to_t)."""
    from mt_ca.m_to_t import encode_polar_spinor_bridge

    return encode_polar_spinor_bridge(z, frac_bits=frac_bits, mod_bits=mod_bits)


def decode_polar_spinor(
    p: torch.Tensor,
    *,
    frac_bits: int,
    mod_bits: int,
) -> torch.Tensor:
    """Delegate polar->complex decoding to the M↔T bridge (mt_ca.m_to_t)."""
    from mt_ca.m_to_t import decode_polar_spinor_bridge

    return decode_polar_spinor_bridge(p, frac_bits=frac_bits, mod_bits=mod_bits)


def polar_phi_int(p: torch.Tensor, cfg: MConfig) -> torch.Tensor:
    """Delegate to carrier_core.polar_phi_core."""
    from mt_ca.carrier_core import polar_phi_core

    return polar_phi_core(p, cfg)


def polar_edge_flux_step_q(
    mu: torch.Tensor,
    phi: torch.Tensor,
    cfg: MConfig,
) -> tuple[torch.Tensor, torch.Tensor]:
    """Delegate to carrier_core.polar_edge_flux_step_q_core."""
    from mt_ca.carrier_core import polar_edge_flux_step_q_core

    return polar_edge_flux_step_q_core(mu, phi, cfg)


def polar_step_fixed(
    p_curr: torch.Tensor,
    p_past: torch.Tensor,
    cfg: MConfig,
) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """Delegate to carrier_core.polar_step_core."""
    from mt_ca.carrier_core import polar_step_core

    return polar_step_core(p_curr, p_past, cfg)


def polar_reverse_fixed(
    p_curr: torch.Tensor,
    p_next: torch.Tensor,
    cfg: MConfig,
) -> tuple[torch.Tensor, torch.Tensor]:
    """Delegate to carrier_core.polar_reverse_core."""
    from mt_ca.carrier_core import polar_reverse_core

    return polar_reverse_core(p_curr, p_next, cfg)
