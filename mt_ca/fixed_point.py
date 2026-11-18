"""M↔T boundary delegation module — SSOT lives in mt_ca.m_to_t and mt_ca.carrier_core."""

from __future__ import annotations

import torch

from mt_ca.carrier_core import (
    CANONICAL_CARRIER,
    carrier_reverse_core,
    carrier_step_core,
    enforce_planck_cell_floor_core as enforce_planck_cell_floor,
)
from mt_ca.m_to_t import (
    decode_from_carrier,
    encode_to_carrier,
    gauge_fix_u1,
    gauge_fix_u1_global,
    vacuum_amplitude_quantum,
)

DEFAULT_FRAC_BITS = CANONICAL_CARRIER.frac_bits
DEFAULT_MOD_BITS = CANONICAL_CARRIER.mod_bits


def scale(frac_bits: int = DEFAULT_FRAC_BITS) -> float:
    return float(1 << frac_bits)


def encode_spinor(
    z: torch.Tensor,
    *,
    frac_bits: int = DEFAULT_FRAC_BITS,
    mod_bits: int = DEFAULT_MOD_BITS,
    gauge_fix: bool = False,
) -> torch.Tensor:
    return encode_to_carrier(z, frac_bits=frac_bits, mod_bits=mod_bits, gauge_fix=gauge_fix)


def decode_spinor(
    f: torch.Tensor,
    *,
    frac_bits: int = DEFAULT_FRAC_BITS,
    mod_bits: int = DEFAULT_MOD_BITS,
) -> torch.Tensor:
    return decode_from_carrier(f, frac_bits=frac_bits, mod_bits=mod_bits)


def quantize_impulse(
    delta: torch.Tensor,
    *,
    frac_bits: int = DEFAULT_FRAC_BITS,
    mod_bits: int = DEFAULT_MOD_BITS,
) -> torch.Tensor:
    return encode_to_carrier(delta, frac_bits=frac_bits, mod_bits=mod_bits)


def leapfrog_combine(
    f_curr: torch.Tensor,
    f_past: torch.Tensor,
    f_impulse: torch.Tensor,
    *,
    mod_bits: int = DEFAULT_MOD_BITS,
) -> torch.Tensor:
    return carrier_step_core(f_curr, f_past, f_impulse, mod_bits=mod_bits)[0]


def leapfrog_invert(
    f_curr: torch.Tensor,
    f_next: torch.Tensor,
    f_impulse: torch.Tensor,
    *,
    mod_bits: int = DEFAULT_MOD_BITS,
) -> torch.Tensor:
    return carrier_reverse_core(f_curr, f_next, f_impulse, mod_bits=mod_bits)[0]
