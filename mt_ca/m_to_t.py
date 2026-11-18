"""M→T anchor checks (§4.0.1, §5, §5.0.1)."""

from __future__ import annotations

from typing import TYPE_CHECKING

import torch

if TYPE_CHECKING:
    from mt_ca.config import MConfig

from mt_ca.si_constants import SI, lepton_geometry_factor
from mt_ca.spinor import arg_phase_defect, spinor_density
from mt_ca.topology import winding_nearest_int, winding_robust
from mt_ca.t_validation import macro_mass


def electron_planck_cell_anchor(*, m_e: float | None = None) -> dict[str, float]:
    """Compare CODATA m_e to m_P·α²·f_geometry — one V_P planckon (§4), not fitted."""
    m_e = m_e if m_e is not None else SI.m_e_CODATA
    f = lepton_geometry_factor(m_e)
    predicted = SI.m_P * SI.alpha_fs**2 * f
    rel = abs(predicted - m_e) / m_e
    return {
        "m_e_CODATA": m_e,
        "f_geometry": f,
        "m_P_alpha2_f": predicted,
        "rel_err": rel,
    }


def zigzag_activity(
    z: torch.Tensor,
    cfg: MConfig,
    *,
    rho_quantile: float | None = None,
) -> float:
    """Mean |Δφ| weighted by ρ — Arg-carrier load (§5.0.1). Optional quantile mask for core-only."""
    phase = arg_phase_defect(z, cfg, apply_floor=False)
    rho = spinor_density(z)
    if rho_quantile is not None:
        flat = rho.reshape(-1)
        if flat.numel() == 0:
            return 0.0
        thresh = torch.quantile(flat, rho_quantile)
        mask = rho >= thresh
        if not mask.any():
            return 0.0
        return float(phase[mask].abs().mean().item())
    mass = float(rho.sum().item())
    if mass <= 1e-12:
        return 0.0
    return float((phase.abs() * rho).sum().item() / mass)


def arg_mass_load(z: torch.Tensor, cfg: MConfig) -> float:
    """|n|·Σ|Δφ|·ρ on defect core — topological Arg load; foam excluded (§5.0.1)."""
    w = winding_robust(z)
    if w != w or abs(w) < 0.5:
        return 0.0
    n = abs(winding_nearest_int(w))
    phase = arg_phase_defect(z, cfg, apply_floor=False).abs()
    rho = spinor_density(z)
    floor = float(torch.quantile(rho.reshape(-1), 0.75).item())
    mask = rho >= floor
    if not bool(mask.any()):
        return 0.0
    circulation = float((phase * rho)[mask].sum().item())
    return float(n) * circulation


def m_rest_macro(z: torch.Tensor, block: int = 8) -> float:
    """Integrated macro amplitude Σ|Φ|² — T macro mass (§5, §5.0.1)."""
    return macro_mass(z, block)


def zigzag_mass_row(z: torch.Tensor, cfg: MConfig, *, block: int = 8) -> dict[str, float]:
    """Joint M Arg-activity + T m_rest macro for correlation UoW."""
    return {
        "zigzag_activity": zigzag_activity(z, cfg),
        "arg_mass_load": arg_mass_load(z, cfg),
        "m_rest": m_rest_macro(z, block),
    }


def vacuum_amplitude_quantum(*, frac_bits: int = 6) -> float:
    """Smallest nonzero |z| = 1 / K_P = 2^{-frac_bits} on the M↔T readout boundary."""
    return 1.0 / float(1 << frac_bits)


def gauge_fix_u1_global(z: torch.Tensor, eps: float = 1e-15) -> torch.Tensor:
    """Remove global U(1) phase on T before carrier encode — preserves spatial ζ (A5, §3.11)."""
    ref = z[..., 0].mean()
    if float(ref.abs().item()) < eps:
        ref = z[..., 1].mean()
    if float(ref.abs().item()) < eps:
        return z
    phase = torch.angle(ref)
    factor = torch.exp(-1j * phase.to(z.real.dtype))
    return z * factor


def gauge_fix_u1(z: torch.Tensor, eps: float = 1e-15, *, per_cell: bool = False) -> torch.Tensor:
    """U(1) gauge helper on the M↔T boundary."""
    if not per_cell:
        return gauge_fix_u1_global(z, eps)
    ref = z[..., 0]
    fallback = z[..., 1]
    use_fallback = ref.abs() < eps
    ref = torch.where(use_fallback, fallback, ref)
    mag = ref.abs()
    phase = torch.angle(ref)
    factor = torch.exp(-1j * phase.to(z.real.dtype))
    mask = mag > eps
    return torch.where(mask.unsqueeze(-1), z * factor.unsqueeze(-1), z)


def encode_to_carrier(
    z: torch.Tensor,
    cfg: MConfig | None = None,
    *,
    frac_bits: int = 6,
    mod_bits: int = 9,
    gauge_fix: bool = False,
) -> torch.Tensor:
    """T→M boundary encoder: complex spinor (..., 2) → polar integer register [μ₀, φ₀, μ₁, φ₁] on M."""
    _ = (cfg, gauge_fix)
    return encode_polar_spinor_bridge(z, frac_bits=frac_bits, mod_bits=mod_bits)


def decode_from_carrier(
    state: torch.Tensor,
    cfg: MConfig | None = None,
    *,
    frac_bits: int = 6,
    mod_bits: int = 9,
) -> torch.Tensor:
    """M→T boundary decoder: polar integer register [μ₀, φ₀, μ₁, φ₁] on M → complex spinor (..., 2) on T."""
    _ = cfg
    return decode_polar_spinor_bridge(state, frac_bits=frac_bits, mod_bits=mod_bits)


def encode_polar_spinor_bridge(
    z: torch.Tensor,
    *,
    frac_bits: int,
    mod_bits: int,
) -> torch.Tensor:
    """T→M boundary encoder: complex spinor (..., 2) → polar integer register [μ₀, φ₀, μ₁, φ₁].

    The 2π circle conversion lives strictly on the M↔T bridge, never inside M-layer gates.
    """
    import math
    from mt_ca.carrier_core import mod_lane_core

    s = float(1 << frac_bits)
    q_max = 1 << frac_bits
    n_ring = 1 << mod_bits
    mu0_raw = torch.floor(z[..., 0].abs() * s + 0.5).to(torch.int64)
    mu1_raw = torch.floor(z[..., 1].abs() * s + 0.5).to(torch.int64)
    mu0 = torch.where(mu0_raw > q_max, torch.full_like(mu0_raw, q_max), torch.where(mu0_raw < 1, torch.ones_like(mu0_raw), mu0_raw))
    mu1 = torch.where(mu1_raw > q_max, torch.full_like(mu1_raw, q_max), torch.where(mu1_raw < 1, torch.ones_like(mu1_raw), mu1_raw))
    phi0 = mod_lane_core(torch.floor(torch.angle(z[..., 0]) * (n_ring / (2.0 * math.pi)) + 0.5).to(torch.int64), mod_bits)
    phi1 = mod_lane_core(torch.floor(torch.angle(z[..., 1]) * (n_ring / (2.0 * math.pi)) + 0.5).to(torch.int64), mod_bits)
    return torch.stack([mu0.to(torch.int32), phi0, mu1.to(torch.int32), phi1], dim=-1)


def decode_polar_spinor_bridge(
    p: torch.Tensor,
    *,
    frac_bits: int,
    mod_bits: int,
) -> torch.Tensor:
    """M→T boundary decoder: polar integer register [μ₀, φ₀, μ₁, φ₁] → complex spinor (..., 2)."""
    import math

    inv_s = 1.0 / float(1 << frac_bits)
    n_ring = float(1 << mod_bits)
    mu0 = p[..., 0].to(torch.float32) * inv_s
    ang0 = (p[..., 1].to(torch.int64) % int(n_ring)).to(torch.float32) * (2.0 * math.pi / n_ring)
    mu1 = p[..., 2].to(torch.float32) * inv_s
    ang1 = (p[..., 3].to(torch.int64) % int(n_ring)).to(torch.float32) * (2.0 * math.pi / n_ring)
    z0 = torch.polar(mu0, ang0)
    z1 = torch.polar(mu1, ang1)
    return torch.stack([z0, z1], dim=-1)
