"""Second-order reversible CA on the M-layer carrier (§3.12 · Chapter 11).

Delegates M-layer evolution to mt_ca.carrier_core and M↔T boundary conversion to mt_ca.m_to_t.
"""

from __future__ import annotations

import torch

from mt_ca.carrier_core import carrier_reverse, carrier_step
from mt_ca.config import MConfig
from mt_ca.m_to_t import decode_from_carrier, encode_to_carrier


def canonicalize(z: torch.Tensor, cfg: MConfig) -> torch.Tensor:
    return decode_from_carrier(encode_to_carrier(z, cfg), cfg)


def evolve_canonical(
    z: torch.Tensor,
    cfg: MConfig,
    steps: int = 1,
    *,
    z_past: torch.Tensor | None = None,
) -> torch.Tensor:
    """Apply g^steps on the M-layer carrier register; decode to ℂ² for T readout only."""
    state_curr = encode_to_carrier(z, cfg)
    state_past = encode_to_carrier(z_past if z_past is not None else z, cfg)
    for _ in range(steps):
        state_curr, state_past, _ = carrier_step(state_curr, state_past, cfg)
    return decode_from_carrier(state_curr, cfg)


def leapfrog_forward(
    z_curr: torch.Tensor,
    z_past: torch.Tensor,
    cfg: MConfig,
) -> tuple[torch.Tensor, torch.Tensor]:
    state_curr = encode_to_carrier(z_curr, cfg)
    state_past = encode_to_carrier(z_past, cfg)
    state_next, state_prev, _ = carrier_step(state_curr, state_past, cfg)
    return (
        decode_from_carrier(state_next, cfg),
        decode_from_carrier(state_prev, cfg),
    )


def micro_step_reversible(
    z_curr: torch.Tensor,
    z_past: torch.Tensor,
    cfg: MConfig,
) -> tuple[torch.Tensor, torch.Tensor]:
    return leapfrog_forward(z_curr, z_past, cfg)


def unwind_carrier_steps(
    state_past: torch.Tensor,
    state_curr: torch.Tensor,
    steps: list[torch.Tensor] | int,
    cfg: MConfig,
) -> torch.Tensor:
    """Literal n-step M-layer reverse from (state_past, state_curr) without any impulse stack."""
    n_steps = steps if isinstance(steps, int) else len(steps)
    s_p, s_c = state_past, state_curr
    for _ in range(n_steps):
        s_p, s_c = carrier_reverse(s_p, s_c, cfg)
    return s_c


def bit_exact_roundtrip_report(
    size: int = 64,
    steps: int = 32,
    device: str = "cpu",
    *,
    seed_class=None,
) -> dict:
    from mt_ca.seeds import SeedClass, make_seed
    from mt_ca.topology import winding_nearest_int, winding_robust

    if seed_class is None:
        seed_class = SeedClass.IMPULSE

    dev = torch.device(device)
    cfg = MConfig.for_stencil("hex", evolution="leapfrog", use_projected_collision=True)
    z0 = make_seed(seed_class, size, size, device=dev)
    s0 = encode_to_carrier(z0, cfg)
    s_past = s0.clone()
    s_curr = s0.clone()
    w0 = winding_robust(decode_from_carrier(s0, cfg))
    n0 = winding_nearest_int(w0) if w0 == w0 and seed_class != SeedClass.IMPULSE else 0

    for _ in range(steps):
        s_curr, s_past, _ = carrier_step(s_curr, s_past, cfg)

    s_back = unwind_carrier_steps(s_past, s_curr, steps, cfg)
    exact = bool(torch.equal(s0, s_back))
    z_back = decode_from_carrier(s_back, cfg)
    z_ref = decode_from_carrier(s0, cfg)
    rel = float((z_back - z_ref).abs().max().item() / (z_ref.abs().max().item() + 1e-12))
    w_back = winding_robust(z_back)
    n_back = winding_nearest_int(w_back) if w_back == w_back and seed_class != SeedClass.IMPULSE else 0

    ok = exact or rel < 1e-6
    return {
        "id": "Leapfrog_bit_exact",
        "seed": seed_class.value if hasattr(seed_class, "value") else str(seed_class),
        "steps": steps,
        "bit_exact": exact,
        "max_rel_err": rel,
        "n0": n0,
        "n_back": n_back,
        "n_stable": n0 == n_back or seed_class == SeedClass.IMPULSE,
        "ok": ok,
        "note": "Literal M-layer bijection g and g⁻¹ without impulse stack (§3.12)",
    }


# Delegation aliases for callers being migrated to carrier_core / m_to_t
canonical_fixed = encode_to_carrier
leapfrog_forward_fixed = carrier_step


def leapfrog_reverse_fixed(
    state_curr: torch.Tensor,
    state_next: torch.Tensor,
    f_impulse: torch.Tensor | None = None,
    cfg: MConfig | None = None,
) -> tuple[torch.Tensor, torch.Tensor]:
    _ = f_impulse
    return carrier_reverse(state_curr, state_next, cfg or MConfig())


unwind_with_impulses = unwind_carrier_steps
