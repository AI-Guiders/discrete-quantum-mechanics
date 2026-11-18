"""Modular ring Z_{N_ring} delegation module — SSOT lives in mt_ca.carrier_core (§3.12.6)."""

from __future__ import annotations

import torch

from mt_ca.carrier_core import (
    CANONICAL_CARRIER,
    carrier_reverse_core,
    carrier_step_core,
    mod_lane_core as mod_lane,
    signed_from_mod_core as signed_from_mod,
)


def add(a: torch.Tensor, b: torch.Tensor, *, mod_bits: int = CANONICAL_CARRIER.mod_bits) -> torch.Tensor:
    return mod_lane(a.to(torch.int64) + b.to(torch.int64), mod_bits)


def sub(a: torch.Tensor, b: torch.Tensor, *, mod_bits: int = CANONICAL_CARRIER.mod_bits) -> torch.Tensor:
    return mod_lane(a.to(torch.int64) - b.to(torch.int64), mod_bits)


def double(a: torch.Tensor, *, mod_bits: int = CANONICAL_CARRIER.mod_bits) -> torch.Tensor:
    return mod_lane(a.to(torch.int64) << 1, mod_bits)


def leapfrog_next(
    z: torch.Tensor,
    z_past: torch.Tensor,
    n_impulse: torch.Tensor,
    *,
    mod_bits: int = CANONICAL_CARRIER.mod_bits,
) -> torch.Tensor:
    """Delegate forward modular step to carrier_core.carrier_step_core."""
    return carrier_step_core(z, z_past, n_impulse, mod_bits=mod_bits)[0]


def leapfrog_past(
    z: torch.Tensor,
    z_next: torch.Tensor,
    n_impulse: torch.Tensor,
    *,
    mod_bits: int = CANONICAL_CARRIER.mod_bits,
) -> torch.Tensor:
    """Delegate literal reverse modular step to carrier_core.carrier_reverse_core."""
    return carrier_reverse_core(z, z_next, n_impulse, mod_bits=mod_bits)[0]


def leapfrog_identity_holds(
    z: torch.Tensor,
    z_past: torch.Tensor,
    z_next: torch.Tensor,
    n_impulse: torch.Tensor,
    *,
    mod_bits: int = CANONICAL_CARRIER.mod_bits,
) -> bool:
    """Check φ⁺ + φ⁻ = 2φ + Φ (mod N_ring) on the phase lanes of [μ₀, φ₀, μ₁, φ₁]."""
    if z.shape[-1] == 4 and n_impulse.shape == z.shape:
        lhs0 = add(z_next[..., 1], z_past[..., 1], mod_bits=mod_bits)
        rhs0 = add(double(z[..., 1], mod_bits=mod_bits), n_impulse[..., 1], mod_bits=mod_bits)
        lhs1 = add(z_next[..., 3], z_past[..., 3], mod_bits=mod_bits)
        rhs1 = add(double(z[..., 3], mod_bits=mod_bits), n_impulse[..., 3], mod_bits=mod_bits)
        return bool(torch.equal(lhs0, rhs0) and torch.equal(lhs1, rhs1))
    lhs = add(z_next, z_past, mod_bits=mod_bits)
    rhs = add(double(z, mod_bits=mod_bits), n_impulse, mod_bits=mod_bits)
    return bool(torch.equal(lhs, rhs))


lane = mod_lane
