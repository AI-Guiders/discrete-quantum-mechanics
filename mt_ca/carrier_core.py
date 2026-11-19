"""Closed M-layer carrier core — derived purely from spatial dimension d=3 (zero free parameters).

Implements:
- Theorem 11.12 (Catalan lock 1 + 2^d = d^2 = 9, Heisenberg lock 533 / 13 = 41, Gaussian lock 4^2 + 9^2 = 97):
  `CarrierSpec.from_d(d=3)` derives every integer invariant of the carrier from `d` alone.
- Theorem 11.11 (Closed trig-free face projections on cuboctahedron faces):
  `edge_proj_cos_int`, `edge_proj_sin_int` with exact L1 identity `|C(A)| + |S(A)| == Q_□ = 128`.
- Theorem 11.5 & 11.9 (Orthogonal holonomy split & discrete Maxwell equations without sources):
  `HolonomyReadout` and `wrap_ring_signed` providing a single source of truth (SSOT) for signed
  phase impulses Φ ∈ (−Φ_Pauli, +Φ_Pauli] and energy quantum numbers n_E.
"""

from __future__ import annotations

from dataclasses import dataclass

import torch


@dataclass(frozen=True, slots=True)
class CarrierSpec:
    """Complete integer passport of the M-layer carrier derived from a single integer d=3."""

    d: int
    n_links: int          # |N_12| = 2d(d-1) = 12
    n_tri: int            # |△| = 2^d = 8
    n_sq: int             # |□| = 2d = 6
    d_in_square: int      # d_in(□) = |N_12|/d = 2(d-1) = 4
    mod_bits: int         # 1 + |△| = d^2 = 9
    frac_bits: int        # mod_bits - d = |□| = 6
    n_ring: int           # 2^mod_bits = 512
    k_p: int              # 2^frac_bits = 64
    q_square: int         # N_ring / d_in(□) = 2^(|△|-1) = 2*K_P = 128
    pauli_ticks: int      # N_ring / 2 = 2^|△| = d_in(□)*K_P = 256
    n_phi: int            # 1 + |N_12| = 13
    dphi_min_ticks: int   # (N_ring + N_phi + |△|) // N_phi = 41
    seam_ticks: int           # N_phi * dphi_min_ticks - N_ring = N_phi + |△| = 21
    m_hat_coulomb: int        # 1 + |N_12|*|△| = d_in(□)^2 + mod_bits^2 = 97
    iv_9bit: int              # 2^(2^d) + (2^d - 1) = 256 + 7 = 263 = 0b1_00000111
    iv_radius: int            # |□| = 2d = 6
    iv_amplitude_mu: int      # N_phi = 1 + |N_12| = 13
    iv_phase_shift_ticks: int # d * dphi_min_ticks = 3 * 41 = 123
    catalan_lock_ok: bool
    heisenberg_lock_ok: bool
    gaussian_lock_ok: bool

    @classmethod
    def from_d(cls, d: int = 3) -> CarrierSpec:
        if d < 2:
            raise ValueError(f"Spatial dimension d must be >= 2, got {d}")
        n_links = 2 * d * (d - 1)
        n_tri = 1 << d
        n_sq = 2 * d
        d_in_sq = n_links // d
        mod_bits = 1 + n_tri
        frac_bits = mod_bits - d
        n_ring = 1 << mod_bits
        k_p = 1 << frac_bits
        q_sq = n_ring // d_in_sq
        pauli = n_ring // 2
        n_phi = 1 + n_links
        num_h = n_ring + n_phi + n_tri
        dphi_min = num_h // n_phi
        seam = n_phi * dphi_min - n_ring
        m_hat = 1 + n_links * n_tri
        iv_9bit = (1 << n_tri) | ((1 << d) - 1)
        iv_radius = n_sq
        iv_amp = n_phi
        iv_shift = d * dphi_min

        catalan_ok = (1 + n_tri) == (d * d)
        heisenberg_ok = (num_h % n_phi) == 0
        gaussian_ok = m_hat == (d_in_sq * d_in_sq + mod_bits * mod_bits)

        return cls(
            d=d,
            n_links=n_links,
            n_tri=n_tri,
            n_sq=n_sq,
            d_in_square=d_in_sq,
            mod_bits=mod_bits,
            frac_bits=frac_bits,
            n_ring=n_ring,
            k_p=k_p,
            q_square=q_sq,
            pauli_ticks=pauli,
            n_phi=n_phi,
            dphi_min_ticks=dphi_min,
            seam_ticks=seam,
            m_hat_coulomb=m_hat,
            iv_9bit=iv_9bit,
            iv_radius=iv_radius,
            iv_amplitude_mu=iv_amp,
            iv_phase_shift_ticks=iv_shift,
            catalan_lock_ok=catalan_ok,
            heisenberg_lock_ok=heisenberg_ok,
            gaussian_lock_ok=gaussian_ok,
        )


CARRIER = CarrierSpec.from_d(3)
CANONICAL_CARRIER = CARRIER


def mod_lane_core(x: torch.Tensor, mod_bits: int = CANONICAL_CARRIER.mod_bits) -> torch.Tensor:
    """Project integer tensor into Z_{2^mod_bits} = [0, N_ring)."""
    n = 1 << mod_bits
    return (x.to(torch.int64) % n).to(torch.int32)


def signed_from_mod_core(u: torch.Tensor, mod_bits: int = CANONICAL_CARRIER.mod_bits) -> torch.Tensor:
    """Interpret ring element in [0, N_ring) as signed integer in (−N_ring/2, N_ring/2]."""
    n = 1 << mod_bits
    half = n >> 1
    x = u.to(torch.int64) % n
    return torch.where(x > half, x - n, x)


def wrap_ring_signed(ticks: torch.Tensor, mod_bits: int = CANONICAL_CARRIER.mod_bits) -> torch.Tensor:
    """Fold any integer tick tensor into the canonical signed interval (−Φ_Pauli, +Φ_Pauli]."""
    return signed_from_mod_core(ticks, mod_bits)


def face_quadrant_ticks(mod_bits: int = CANONICAL_CARRIER.mod_bits, d_in_square: int = CANONICAL_CARRIER.d_in_square) -> int:
    """Q_□ = N_ring / d_in(□) = 128."""
    return (1 << mod_bits) // d_in_square


def edge_proj_cos_int(a_xy: torch.Tensor, mod_bits: int = CANONICAL_CARRIER.mod_bits) -> torch.Tensor:
    """Closed even edge projection C(A_xy) = Q_□ − |wrap(A_xy)| ∈ [−Q_□, +Q_□] (Theorem 11.11)."""
    q_sq = face_quadrant_ticks(mod_bits)
    return q_sq - wrap_ring_signed(a_xy, mod_bits).abs()


def edge_proj_sin_int(a_xy: torch.Tensor, mod_bits: int = CANONICAL_CARRIER.mod_bits) -> torch.Tensor:
    """Closed odd edge projection S(A_xy) = C(wrap(A_xy − Q_□)) = −S(A_yx) ∈ [−Q_□, +Q_□] (Theorem 11.11)."""
    q_sq = face_quadrant_ticks(mod_bits)
    return edge_proj_cos_int(a_xy.to(torch.int64) - q_sq, mod_bits)


def pythagorean_rotator_int(
    phi_ticks: torch.Tensor,
    mod_bits: int = CANONICAL_CARRIER.mod_bits,
) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """Exact integer Pythagorean triple (P_x, P_y, P_r) on Z_{N_ring} without pi/cos/sin (Theorem 11.11).

    For any tick A ∈ Z_{N_ring}, using C = C(A) and S = S(A) with |C| + |S| = Q_□:
      P_x(A) = sgn(C) · (Q_□² − S²),   P_y(A) = 2 · Q_□ · S,   P_r(A) = Q_□² + S²,
    which satisfies the exact integer identity P_x(A)² + P_y(A)² ≡ P_r(A)² for all A.
    At A = Δφ_disc = 41 and Q_□ = 128, gives the Heisenberg Pythagorean triple (14703, 10496, 18065).
    """
    q_sq = face_quadrant_ticks(mod_bits)
    c_l1 = edge_proj_cos_int(phi_ticks, mod_bits)
    s_l1 = edge_proj_sin_int(phi_ticks, mod_bits)
    q2 = q_sq * q_sq
    s2 = s_l1 * s_l1
    sgn_c = torch.where(c_l1 < 0, -torch.ones_like(c_l1), torch.ones_like(c_l1))
    px = torch.where(c_l1 == 0, torch.zeros_like(c_l1), sgn_c * (q2 - s2))
    py = 2 * q_sq * s_l1
    pr = q2 + s2
    return px, py, pr


def isqrt_int64(n: torch.Tensor) -> torch.Tensor:
    """Exact integer floor square root ⌊√n⌋ for non-negative int64 tensors (Newton-Heron in ℤ, no float)."""
    x = n.to(torch.int64)
    est = torch.ones_like(x) << 6
    for _ in range(7):
        den = torch.where(est > 0, est, torch.ones_like(est))
        est = (est + x // den) >> 1
    est = torch.where(est * est > x, est - 1, est)
    est = torch.where((est + 1) * (est + 1) <= x, est + 1, est)
    return torch.where(x <= 0, torch.zeros_like(x), est)


def signed_phi_ticks(phi: torch.Tensor, mod_bits: int = CANONICAL_CARRIER.mod_bits) -> torch.Tensor:
    """Fold integer ring ticks Φ ∈ Z_{N_ring} into signed ticks ∈ (−Φ_Pauli, +Φ_Pauli]."""
    return wrap_ring_signed(phi.to(torch.int64), mod_bits)


def apply_heisenberg_floor_core(
    phi_signed: torch.Tensor,
    phi_min: int = CANONICAL_CARRIER.dphi_min_ticks,
) -> torch.Tensor:
    """Zero out sub-threshold impulses |Φ| < Δφ_disc without CPU-GPU sync."""
    return torch.where(phi_signed.abs() < phi_min, torch.zeros_like(phi_signed), phi_signed)


def carrier_saturating_gate_core(
    zeta_r: torch.Tensor,
    zeta_i: torch.Tensor,
    rho2: torch.Tensor,
    *,
    scale_ticks: int = CANONICAL_CARRIER.k_p,
    eps_quanta2: int = CANONICAL_CARRIER.k_p,
    mod_bits: int = CANONICAL_CARRIER.mod_bits,
    heisenberg_floor: bool = True,
    phi_min: int = CANONICAL_CARRIER.dphi_min_ticks,
) -> torch.Tensor:
    """Single source of truth (SSOT) for the M-layer saturating holonomy gate Φ in Z_{N_ring}.

    All inputs (zeta_r, zeta_i, rho2, eps_quanta2) are integer quanta² on M;
    scale_ticks converts the dimensionless ratio into phase-ring ticks before
    folding into (−Φ_Pauli, +Φ_Pauli] and applying the Heisenberg deadband Δφ_disc.
    Returns unsigned ring representative in [0, 2^mod_bits).
    """
    denom = zeta_r + rho2 + eps_quanta2
    denom = torch.where(denom > 0, denom, torch.ones_like(denom))
    phi = (int(scale_ticks) * zeta_i) // denom
    phi_signed = wrap_ring_signed(phi, mod_bits)
    if heisenberg_floor:
        phi_signed = apply_heisenberg_floor_core(phi_signed, phi_min)
    return mod_lane_core(phi_signed, mod_bits)


def enforce_planck_cell_floor_core(
    state: torch.Tensor,
    *,
    mod_bits: int = CANONICAL_CARRIER.mod_bits,
) -> torch.Tensor:
    """A5 + §3.12.6: no hV cell is exact zero — minimum 1 amplitude quantum on M (no CPU-GPU sync)."""
    dead = state.abs().sum(dim=-1) == 0
    out = state.clone()
    out[..., 0] = torch.where(dead, torch.ones_like(out[..., 0]), out[..., 0])
    return mod_lane_core(out, mod_bits)


def signed_lanes_core(state: torch.Tensor, mod_bits: int = CANONICAL_CARRIER.mod_bits) -> torch.Tensor:
    """Ring lanes [0, N_ring) → signed integer representatives in (−N_ring/2, N_ring/2]."""
    return torch.stack(
        [signed_from_mod_core(state[..., i], mod_bits) for i in range(state.shape[-1])],
        dim=-1,
    )


def int_neighbor_sum_core(state_signed: torch.Tensor, stencil: str = "fcc") -> torch.Tensor:
    """Σ_{y∈N(x)} on each integer lane without float conversion."""
    from mt_ca.laplacian import neighbor_sum

    out = torch.zeros_like(state_signed, dtype=torch.int64)
    f64 = state_signed.to(torch.int64)
    for lane_i in range(state_signed.shape[-1]):
        out[..., lane_i] = neighbor_sum(f64[..., lane_i], stencil)
    return out


def pauli_phi_core(
    state: torch.Tensor,
    *,
    mod_bits: int = CANONICAL_CARRIER.mod_bits,
    frac_bits: int = CANONICAL_CARRIER.frac_bits,
    phi_min: int = CANONICAL_CARRIER.dphi_min_ticks,
    enabled: bool = True,
) -> torch.Tensor:
    """§3.10.4: parallel spinors on V_P in polar register [μ₀, φ₀, μ₁, φ₁] → Φ_Pauli = N_ring/2 ticks."""
    return pauli_polar_phi_core(
        state,
        mod_bits=mod_bits,
        frac_bits=frac_bits,
        phi_min=phi_min,
        enabled=enabled,
    )


def carrier_gate_phi(
    state: torch.Tensor,
    cfg=None,
    *,
    include_even_deficit: bool = True,
) -> torch.Tensor:
    """Single source of truth for the M-layer holonomy gate Φ ∈ Z_{N_ring} on polar register [μ₀, φ₀, μ₁, φ₁]."""
    return polar_phi_core(state, cfg, include_even_deficit=include_even_deficit)


def carrier_collision_impulse(state: torch.Tensor, cfg=None) -> torch.Tensor:
    """Gate impulse Φ ∈ Z_{N_ring} applied additively to the phase lanes [0, Φ, 0, Φ] of [μ₀, φ₀, μ₁, φ₁]."""
    phi = polar_phi_core(state, cfg)
    z = torch.zeros_like(phi)
    return torch.stack([z, phi, z, phi], dim=-1)


def carrier_step_core(
    state_curr: torch.Tensor,
    state_past: torch.Tensor,
    n_impulse: torch.Tensor,
    *,
    mod_bits: int = CANONICAL_CARRIER.mod_bits,
) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """Exact M-layer modular bijection on polar register [μ₀, φ₀, μ₁, φ₁]:
    φ_c⁺ = (2φ_c + Φ − φ_c⁻) mod N_ring, μ_c⁺ = μ_c.
    """
    mu0 = state_curr[..., 0]
    mu1 = state_curr[..., 2]
    phi0_next = mod_lane_core(
        2 * state_curr[..., 1].to(torch.int64) + n_impulse[..., -1].to(torch.int64) - state_past[..., 1].to(torch.int64),
        mod_bits,
    )
    phi1_next = mod_lane_core(
        2 * state_curr[..., 3].to(torch.int64) + n_impulse[..., -1].to(torch.int64) - state_past[..., 3].to(torch.int64),
        mod_bits,
    )
    state_next = torch.stack([mu0, phi0_next, mu1, phi1_next], dim=-1)
    return state_next, state_curr, n_impulse


def carrier_reverse_core(
    state_curr: torch.Tensor,
    state_next: torch.Tensor,
    n_impulse: torch.Tensor,
    *,
    mod_bits: int = CANONICAL_CARRIER.mod_bits,
) -> tuple[torch.Tensor, torch.Tensor]:
    """Literal M-layer reverse on polar register [μ₀, φ₀, μ₁, φ₁]:
    φ_c⁻ = (2φ_c + Φ − φ_c⁺) mod N_ring, μ_c⁻ = μ_c.
    """
    mu0 = state_curr[..., 0]
    mu1 = state_curr[..., 2]
    phi0_past = mod_lane_core(
        2 * state_curr[..., 1].to(torch.int64) + n_impulse[..., -1].to(torch.int64) - state_next[..., 1].to(torch.int64),
        mod_bits,
    )
    phi1_past = mod_lane_core(
        2 * state_curr[..., 3].to(torch.int64) + n_impulse[..., -1].to(torch.int64) - state_next[..., 3].to(torch.int64),
        mod_bits,
    )
    state_past = torch.stack([mu0, phi0_past, mu1, phi1_past], dim=-1)
    return state_past, state_curr


def carrier_step(
    state_curr: torch.Tensor,
    state_past: torch.Tensor,
    cfg=None,
) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """Full M-layer forward tick g on polar register [μ₀, φ₀, μ₁, φ₁]."""
    return polar_step_core(state_curr, state_past, cfg)


def carrier_reverse(
    state_curr: torch.Tensor,
    state_next: torch.Tensor,
    cfg=None,
) -> tuple[torch.Tensor, torch.Tensor]:
    """Full M-layer literal reverse tick g⁻¹ on polar register [μ₀, φ₀, μ₁, φ₁] without any impulse stack."""
    return polar_reverse_core(state_curr, state_next, cfg)


_RING_FACE_CACHE: dict[tuple[str, int], tuple[torch.Tensor, torch.Tensor]] = {}


def ring_face_lut_core(n_ring: int, device: torch.device) -> tuple[torch.Tensor, torch.Tensor]:
    """Closed integer face-projection tables (C(Δφ), S(Δφ)) on Z_{N_ring} (no math.pi / torch.cos / torch.sin)."""
    key = (str(device), int(n_ring))
    if key not in _RING_FACE_CACHE:
        mod_bits = (int(n_ring) - 1).bit_length()
        idx = torch.arange(n_ring, device=device, dtype=torch.int64)
        cu = edge_proj_cos_int(idx, mod_bits)
        sv = edge_proj_sin_int(idx, mod_bits)
        _RING_FACE_CACHE[key] = (cu, sv)
    return _RING_FACE_CACHE[key]


def polar_neighbor_holonomy_core(
    mu: torch.Tensor,
    phi: torch.Tensor,
    stencil: str = "fcc",
    n_ring: int = CANONICAL_CARRIER.n_ring,
) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """(ζ_real, ζ_imag, sum_mu) on polar register (μ, φ_disc) in a single fused pass over neighbors."""
    from mt_ca.laplacian import _FCC_OFFSETS, _parity_mask

    cu, sv = ring_face_lut_core(n_ring, mu.device)
    zr_raw = torch.zeros_like(mu, dtype=torch.int64)
    zi_raw = torch.zeros_like(mu, dtype=torch.int64)
    sum_mu = torch.zeros_like(mu, dtype=torch.int64)

    if stencil == "fcc":
        for dz, dy, dx in _FCC_OFFSETS:
            mu_n = torch.roll(mu, shifts=(dz, dy, dx), dims=(0, 1, 2))
            phi_n = torch.roll(phi, shifts=(dz, dy, dx), dims=(0, 1, 2))
            dphi = (phi_n - phi) % n_ring
            zr_raw = zr_raw + mu_n * cu[dphi]
            zi_raw = zi_raw + mu_n * sv[dphi]
            sum_mu = sum_mu + mu_n
    elif stencil == "n4":
        for dy, dx in ((-1, 0), (1, 0), (0, 1), (0, -1)):
            mu_n = torch.roll(mu, shifts=(dy, dx), dims=(0, 1))
            phi_n = torch.roll(phi, shifts=(dy, dx), dims=(0, 1))
            dphi = (phi_n - phi) % n_ring
            zr_raw = zr_raw + mu_n * cu[dphi]
            zi_raw = zi_raw + sv[dphi] * mu_n
            sum_mu = sum_mu + mu_n
    elif stencil == "hex":
        even = _parity_mask(mu.shape[0], mu.shape[1], mu.device)
        if mu.dim() == 3:
            even = even.unsqueeze(-1)
        for dy, dx in ((-1, 0), (1, 0), (0, 1), (0, -1)):
            mu_n = torch.roll(mu, shifts=(dy, dx), dims=(0, 1))
            phi_n = torch.roll(phi, shifts=(dy, dx), dims=(0, 1))
            dphi = (phi_n - phi) % n_ring
            zr_raw = zr_raw + mu_n * cu[dphi]
            zi_raw = zi_raw + mu_n * sv[dphi]
            sum_mu = sum_mu + mu_n
        for (dy_e, dx_e), (dy_o, dx_o) in (((-1, -1), (-1, 1)), ((1, 1), (1, -1))):
            mu_e = torch.roll(mu, shifts=(dy_e, dx_e), dims=(0, 1))
            phi_e = torch.roll(phi, shifts=(dy_e, dx_e), dims=(0, 1))
            mu_o = torch.roll(mu, shifts=(dy_o, dx_o), dims=(0, 1))
            phi_o = torch.roll(phi, shifts=(dy_o, dx_o), dims=(0, 1))
            mu_n = torch.where(even, mu_e, mu_o)
            phi_n = torch.where(even, phi_e, phi_o)
            dphi = (phi_n - phi) % n_ring
            zr_raw = zr_raw + mu_n * cu[dphi]
            zi_raw = zi_raw + mu_n * sv[dphi]
            sum_mu = sum_mu + mu_n
    else:
        raise ValueError(f"Unknown stencil: {stencil!r}")

    return zr_raw * mu, zi_raw * mu, sum_mu


def polar_component_phi_core(
    mu: torch.Tensor,
    phi: torch.Tensor,
    cfg=None,
    *,
    include_even_deficit: bool = True,
) -> tuple[torch.Tensor, torch.Tensor]:
    """Signed Φ ticks and odd flux divergence ζ_imag // Q_□ for polar channel(s) (μ, φ_disc)."""
    mod_bits = CANONICAL_CARRIER.mod_bits
    stencil = "fcc" if cfg is None else cfg.stencil
    h_floor = True if cfg is None else cfg.heisenberg_floor
    phi_min = CANONICAL_CARRIER.dphi_min_ticks

    n_ring = CANONICAL_CARRIER.n_ring
    q_sq = CANONICAL_CARRIER.q_square
    zr, zi, sum_mu = polar_neighbor_holonomy_core(mu, phi, stencil, n_ring)
    r2 = (mu * mu) * q_sq
    kp = CANONICAL_CARRIER.k_p
    eps = kp * q_sq
    if include_even_deficit:
        deficit = mu * sum_mu * q_sq - zr
        sgn = torch.where(zi < 0, -torch.ones_like(zi), torch.ones_like(zi))
        z_drive = zi + sgn * deficit
    else:
        z_drive = zi
    denom = zr + r2 + eps
    denom = torch.where(denom > 0, denom, torch.full_like(denom, eps))
    phi_imp = (kp * z_drive) // denom
    phi_imp = wrap_ring_signed(phi_imp, mod_bits)
    if h_floor:
        phi_imp = apply_heisenberg_floor_core(phi_imp, phi_min)
    return phi_imp, zi // q_sq


def pauli_polar_phi_core(
    p: torch.Tensor,
    *,
    mod_bits: int = CANONICAL_CARRIER.mod_bits,
    frac_bits: int = CANONICAL_CARRIER.frac_bits,
    phi_min: int = CANONICAL_CARRIER.dphi_min_ticks,
    enabled: bool = True,
) -> torch.Tensor:
    """§3.10.4: parallel spinors on V_P in polar register [μ₀, φ₀, μ₁, φ₁] → Φ_Pauli = N_ring/2 ticks."""
    if not enabled:
        return torch.zeros(p.shape[:-1], device=p.device, dtype=torch.int64)
    mu0 = p[..., 0].to(torch.int64)
    phi0 = p[..., 1].to(torch.int64)
    mu1 = p[..., 2].to(torch.int64)
    phi1 = p[..., 3].to(torch.int64)
    kp = 1 << frac_bits
    rho_min_q = (kp * kp) // 2
    dense = (mu0 * mu0 > rho_min_q) & (mu1 * mu1 > rho_min_q)
    parallel = wrap_ring_signed(phi1 - phi0, mod_bits).abs() < phi_min
    bad = dense & parallel
    pauli_ticks = (1 << mod_bits) >> 1
    return torch.where(bad, torch.full_like(mu0, pauli_ticks), torch.zeros_like(mu0))


def polar_phi_core(p: torch.Tensor, cfg=None, *, include_even_deficit: bool = True) -> torch.Tensor:
    """Gate Φ ∈ Z_{N_ring} on polar register [μ₀, φ₀, μ₁, φ₁] — both components fused in one pass."""
    mod_bits = CANONICAL_CARRIER.mod_bits
    frac_bits = CANONICAL_CARRIER.frac_bits
    pauli_on = True if cfg is None else cfg.pauli_exclusion
    phi_min = CANONICAL_CARRIER.dphi_min_ticks
    n_ring = CANONICAL_CARRIER.n_ring
    mu_both = p[..., 0::2].to(torch.int64)
    phi_both = p[..., 1::2].to(torch.int64) % n_ring
    p_both, _ = polar_component_phi_core(mu_both, phi_both, cfg, include_even_deficit=include_even_deficit)
    p0, p1 = p_both[..., 0], p_both[..., 1]
    phi_imp = torch.where(p1.abs() > p0.abs(), p1, p0)
    if pauli_on:
        p_pauli = pauli_polar_phi_core(
            p,
            mod_bits=mod_bits,
            frac_bits=frac_bits,
            phi_min=phi_min,
            enabled=True,
        )
        phi_imp = wrap_ring_signed(phi_imp + p_pauli, mod_bits)
    return mod_lane_core(phi_imp, mod_bits)


def polar_edge_flux_step_q_core(
    mu: torch.Tensor,
    phi: torch.Tensor,
    cfg=None,
) -> tuple[torch.Tensor, torch.Tensor]:
    """Conservative edge-flux transport of cell weight q = μ² along lattice links (Theorem 11.4)."""
    from mt_ca.laplacian import _FCC_OFFSETS, stencil_n_links

    mod_bits = CANONICAL_CARRIER.mod_bits
    frac_bits = CANONICAL_CARRIER.frac_bits
    stencil = "fcc" if cfg is None else cfg.stencil

    n_ring = 1 << mod_bits
    q_sq = face_quadrant_ticks(mod_bits)
    n_links = stencil_n_links(stencil)
    q_max = 1 << (2 * frac_bits)
    _, sv = ring_face_lut_core(n_ring, mu.device)

    q = mu.to(torch.int64) * mu.to(torch.int64)
    div_j = torch.zeros_like(q, dtype=torch.int64)

    if stencil == "fcc":
        for dz, dy, dx in _FCC_OFFSETS[:6]:
            mu_n = torch.roll(torch.roll(torch.roll(mu.to(torch.int64), shifts=dz, dims=-3), shifts=dy, dims=-2), shifts=dx, dims=-1)
            phi_n = torch.roll(torch.roll(torch.roll(phi.to(torch.int64), shifts=dz, dims=-3), shifts=dy, dims=-2), shifts=dx, dims=-1)
            dphi_xy = (phi.to(torch.int64) - phi_n) % n_ring
            j_raw = (mu.to(torch.int64) * mu_n * sv[dphi_xy]) // (n_links * q_sq)
            q_n = torch.roll(torch.roll(torch.roll(q, shifts=dz, dims=-3), shifts=dy, dims=-2), shifts=dx, dims=-1)
            cap_pos = torch.minimum((q - 1) // 6, (q_max - q_n) // 6)
            cap_neg = torch.minimum((q_n - 1) // 6, (q_max - q) // 6)
            j_edge = torch.where(j_raw >= 0, torch.minimum(j_raw, cap_pos), -torch.minimum(-j_raw, cap_neg))
            j_back = torch.roll(torch.roll(torch.roll(j_edge, shifts=-dz, dims=-3), shifts=-dy, dims=-2), shifts=-dx, dims=-1)
            div_j = div_j + j_edge - j_back
    elif stencil in ("n4", "hex"):
        for dy, dx in ((-1, 0), (0, 1)):
            mu_n = torch.roll(torch.roll(mu.to(torch.int64), shifts=dy, dims=-2), shifts=dx, dims=-1)
            phi_n = torch.roll(torch.roll(phi.to(torch.int64), shifts=dy, dims=-2), shifts=dx, dims=-1)
            dphi_xy = (phi.to(torch.int64) - phi_n) % n_ring
            j_raw = (mu.to(torch.int64) * mu_n * sv[dphi_xy]) // (n_links * q_sq)
            q_n = torch.roll(torch.roll(q, shifts=dy, dims=-2), shifts=dx, dims=-1)
            cap_pos = torch.minimum((q - 1) // 2, (q_max - q_n) // 2)
            cap_neg = torch.minimum((q_n - 1) // 2, (q_max - q) // 2)
            j_edge = torch.where(j_raw >= 0, torch.minimum(j_raw, cap_pos), -torch.minimum(-j_raw, cap_neg))
            j_back = torch.roll(torch.roll(j_edge, shifts=-dy, dims=-2), shifts=-dx, dims=-1)
            div_j = div_j + j_edge - j_back
    else:
        raise ValueError(f"Unknown stencil: {stencil!r}")

    q_next = q - div_j
    mu_next = isqrt_int64(q_next).to(torch.int32)
    return mu_next, div_j


def polar_step_core(
    p_curr: torch.Tensor,
    p_past: torch.Tensor,
    cfg=None,
) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """Second-order Verlet step on the polar phase ring Z_{N_ring} (exact Z_{N_ring} rotation by addition):

      φ₀(t+1) = (2·φ₀(t) − φ₀(t−1) + Φ₀(p_curr)) mod N_ring,
      φ₁(t+1) = (2·φ₁(t) − φ₁(t−1) + Φ₁(p_curr) + Φ_Pauli) mod N_ring,   μ_c(t+1) = μ_c(t).
    """
    mod_bits = CANONICAL_CARRIER.mod_bits if cfg is None else cfg.mod_bits
    frac_bits = CANONICAL_CARRIER.frac_bits if cfg is None else cfg.frac_bits
    pauli_on = True if cfg is None else cfg.pauli_exclusion
    phi_min = CANONICAL_CARRIER.dphi_min_ticks
    phi_imp = polar_phi_core(p_curr, cfg)
    p_pauli = pauli_polar_phi_core(p_curr, mod_bits=mod_bits, frac_bits=frac_bits, phi_min=phi_min, enabled=pauli_on)
    mu0 = p_curr[..., 0]
    mu1 = p_curr[..., 2]
    phi0_next = mod_lane_core(
        2 * p_curr[..., 1].to(torch.int64) - p_past[..., 1].to(torch.int64) + (phi_imp.to(torch.int64) - p_pauli),
        mod_bits,
    )
    phi1_next = mod_lane_core(
        2 * p_curr[..., 3].to(torch.int64) - p_past[..., 3].to(torch.int64) + phi_imp.to(torch.int64),
        mod_bits,
    )
    p_next = torch.stack([mu0, phi0_next, mu1, phi1_next], dim=-1)
    return p_next, p_curr, phi_imp


def polar_reverse_core(
    p_curr: torch.Tensor,
    p_next: torch.Tensor,
    cfg=None,
) -> tuple[torch.Tensor, torch.Tensor]:
    """Literal reverse on the polar phase ring Z_{N_ring} without an impulse stack."""
    mod_bits = CANONICAL_CARRIER.mod_bits if cfg is None else cfg.mod_bits
    frac_bits = CANONICAL_CARRIER.frac_bits if cfg is None else cfg.frac_bits
    pauli_on = True if cfg is None else cfg.pauli_exclusion
    phi_min = CANONICAL_CARRIER.dphi_min_ticks
    phi_imp = polar_phi_core(p_curr, cfg)
    p_pauli = pauli_polar_phi_core(p_curr, mod_bits=mod_bits, frac_bits=frac_bits, phi_min=phi_min, enabled=pauli_on)
    mu0 = p_curr[..., 0]
    mu1 = p_curr[..., 2]
    phi0_past = mod_lane_core(
        2 * p_curr[..., 1].to(torch.int64) - p_next[..., 1].to(torch.int64) + (phi_imp.to(torch.int64) - p_pauli),
        mod_bits,
    )
    phi1_past = mod_lane_core(
        2 * p_curr[..., 3].to(torch.int64) - p_next[..., 3].to(torch.int64) + phi_imp.to(torch.int64),
        mod_bits,
    )
    p_past = torch.stack([mu0, phi0_past, mu1, phi1_past], dim=-1)
    return p_past, p_curr


def universe_iv_carrier_3d(
    nz: int,
    ny: int,
    nx: int,
    *,
    device: torch.device,
    iv_9bit: int = CARRIER.iv_9bit,
    radius: int = CARRIER.iv_radius,
    class_offset: int = 0,
) -> torch.Tensor:
    """Unique parameter-free initial state Ψ⁰ = IV(d=3) = 263 in polar register [μ₀, φ₀, μ₁, φ₁] on ℤ (no pi/float/exp)."""
    c = CARRIER
    zz, yy, xx = torch.meshgrid(
        torch.arange(nz, device=device, dtype=torch.int64),
        torch.arange(ny, device=device, dtype=torch.int64),
        torch.arange(nx, device=device, dtype=torch.int64),
        indexing="ij",
    )
    phase_class = (xx + int(class_offset)) % c.n_phi
    phi_bg = (phase_class * c.dphi_min_ticks) % c.n_ring

    cz, cy, cx = nz // 2, ny // 2, nx // 2
    octant_idx = ((zz >= cz).long() << 2) | ((yy >= cy).long() << 1) | (xx >= cx).long()
    b_chir = (int(iv_9bit) >> (c.mod_bits - 1)) & 1
    mask8 = int(iv_9bit) & ((1 << (c.mod_bits - 1)) - 1)
    sgn = 2 * b_chir - 1

    r2 = (zz - cz) ** 2 + (yy - cy) ** 2 + (xx - cx) ** 2
    in_ball = r2 <= int(radius) ** 2
    bit_m1 = (mask8 >> octant_idx) & 1
    bit_m2 = (mask8 >> (octant_idx ^ c.d)) & 1

    dphi1 = torch.where(in_ball, sgn * bit_m1 * c.iv_phase_shift_ticks, torch.zeros_like(phi_bg))
    dphi2 = torch.where(in_ball, sgn * bit_m2 * c.iv_phase_shift_ticks, torch.zeros_like(phi_bg))

    mu = torch.where(in_ball, torch.full_like(phi_bg, c.iv_amplitude_mu), torch.ones_like(phi_bg)).to(torch.int32)
    phi0 = mod_lane_core(phi_bg + dphi1, c.mod_bits)
    phi1 = mod_lane_core(phi_bg + dphi2, c.mod_bits)
    return torch.stack([mu, phi0, mu, phi1], dim=-1)


