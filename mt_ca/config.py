from __future__ import annotations

from dataclasses import dataclass, replace
import math

from mt_ca.si_constants import (
    DELTA_PHI_MIN,
    PLANCK_CELL,
    N12_FCC_CAUSAL_LINKS,
    SI,
    elementary_quanta_row,
    kappa_link,
    pauli_impulse_rad,
    pauli_overlap_cos,
    pauli_rho_min_natural,
    sync_strength_rad,
)
from mt_ca.carrier_core import CANONICAL_CARRIER
from mt_ca.laplacian import stencil_n_links


def vacuum_amplitude_quantum(frac_bits: int = CANONICAL_CARRIER.frac_bits) -> float:
    return 1.0 / float(1 << frac_bits)


@dataclass(frozen=True)
class MConfig:
    """Planck-lattice M-layer parameters in natural units (hL=l_P, hT=t_P, c=1)."""

    # hL / hT in SI — semantic anchors for T-layer reporting (simulation uses natural units)
    hL: float = SI.l_P
    hT: float = SI.hT

    # linear_mode: isotropic (§3.6 default) | local_ca (§3.6 bond-sweeps) | diffusive (A3↔A6 anti-pattern)
    linear_mode: str = "isotropic"

    # Kinetic coupling: γ = κ_link = 1/|N| (§5.2.2 · §1.6 canon |N|=12)
    gamma: float = kappa_link(n_links=N12_FCC_CAUSAL_LINKS)

    # Saturating phase (§7.1): ε=1 ↔ u_P; numerator 1+r from tick budget
    epsilon: float = SI.epsilon
    phase_saturation: float = SI.phase_saturation

    # A8: extra macro suppression w(ρ)=1/(1+ρ/ρ_macro); 0 = saturating-phase asymptotics only
    macro_rho: float = 1.0
    macro_weight: bool = True

    # t=0 «первичный бульон»: one Q(frac_bits) quanta (§3.12.6)
    vacuum_amplitude: float = vacuum_amplitude_quantum(frac_bits=PLANCK_CELL.frac_bits)

    # A9: discrete CR coupling — cr_strength = κ_link (§5.2.2)
    cr_strength: float = kappa_link(n_links=N12_FCC_CAUSAL_LINKS)

    # §3.9 global holomorphy sync on same Δt — κ_link·Δφ_min (§5.2.3)
    holomorphy_sync: bool = True
    sync_strength: float = sync_strength_rad()

    # §3.10.4 Pauli pressure on same V_P — π impulse, κ_link·ρ_max thresholds (§5.2.3)
    pauli_exclusion: bool = True
    pauli_impulse: float = pauli_impulse_rad()
    pauli_rho_min: float = pauli_rho_min_natural()
    pauli_overlap_cos: float = pauli_overlap_cos()

    # A7 hard Planck density ceiling (|z|² in natural units)
    rho_max: float = 1.0

    # §3.7.2 Heisenberg physical floor: Δφ_min = s₀/ℏ = ½ rad (Planck, not 1/2^F)
    heisenberg_floor: bool = True
    heisenberg_phi_min: float = DELTA_PHI_MIN

    # §1.6 шаблон соседства (поле stencil): fcc N₁₂ · hex = срез 2+1 · n4 = архив
    stencil: str = "fcc"

    # §3.12 M-canonical evolution: leapfrog + projected collision on Z_N[i] (§3.12.6)
    evolution: str = "leapfrog"
    mod_bits: int = PLANCK_CELL.mod_bits
    frac_bits: int = PLANCK_CELL.frac_bits
    use_projected_collision: bool = True
    phase_bits: int = PLANCK_CELL.phase_bits
    scale_k: int = 1

    @property
    def is_leapfrog(self) -> bool:
        return True

    @property
    def c(self) -> float:
        return self.hL / self.hT

    @property
    def e_floor(self) -> float:
        """Floor energy quantum at supercell scale K: E_floor(K) = E_0 / K [J in SI]."""
        return SI.E_0 / float(self.scale_k)

    @property
    def p_floor(self) -> float:
        """Floor momentum quantum at supercell scale K: p_floor(K) = p_0 / K [kg·m/s in SI]."""
        return (SI.s_0 / SI.l_P) / float(self.scale_k)

    @property
    def m_floor(self) -> float:
        """Floor inertia quantum at supercell scale K: m_floor(K) = m_arg / K [kg in SI]."""
        return SI.m_arg / float(self.scale_k)

    @property
    def s_floor(self) -> float:
        """Floor action quantum: s_floor(K) = p_floor(K) * hL(K) = E_floor(K) * hT(K) == s_0 (K-invariant)."""
        return self.p_floor * self.hL

    @property
    def n_pack_supercell(self) -> int:
        """Exact number of Planck Voronoi cells inside one scale-K supercell: K^3 in Z."""
        return int(self.scale_k) ** 3

    @property
    def omega(self) -> float:
        """One full vacuum phase cycle per tick: ω = 2π/hT [rad/s in SI]."""
        return SI.omega if self.hT == SI.hT else 2.0 * math.pi / self.hT

    @property
    def phase_scale(self) -> float:
        """hT·ω = 2π — dimensionless tick phase (λ absorbed into hT)."""
        return self.hT * self.omega

    @classmethod
    def for_scale_k(cls, scale_k: int = 1, stencil: str = "fcc", **kw: object) -> "MConfig":
        """Construct MConfig at coherent supercell scale K (hL = K*l_P, hT = K*hT; Z_512[i]^2 step g invariant)."""
        k_int = max(1, int(scale_k))
        return cls.for_stencil(
            stencil,
            scale_k=k_int,
            hL=SI.l_P * float(k_int),
            hT=SI.hT * float(k_int),
            **kw,
        )

    @classmethod
    def for_ladder_floor(cls, floor_name: str = "planck", stencil: str = "fcc", **kw: object) -> "MConfig":
        """Construct MConfig for a named scale floor of §6.0 (`planck`, `compton`, `bohr`, `lyman`, `ir_hb`)."""
        alpha = SI.alpha_preferred
        n_c = int(round(SI.m_P / SI.m_e_CODATA))
        n_a0 = int(round(n_c / alpha))
        d_minus_1 = 2
        n_hb = (1 << PLANCK_CELL.frac_bits) - 1  # 63
        floors: dict[str, int] = {
            "planck": 1,
            "star_1": N12_FCC_CAUSAL_LINKS,
            "star_2": N12_FCC_CAUSAL_LINKS**2,
            "star_3": N12_FCC_CAUSAL_LINKS**3,
            "compton": n_c,
            "bohr": n_a0,
            "lyman": int(round(d_minus_1 * n_a0 / alpha)),
            "ir_hb": int(round(d_minus_1 * n_hb * n_a0 / alpha)),
        }
        if floor_name not in floors:
            raise KeyError(f"Unknown ladder floor {floor_name!r}; expected one of {sorted(floors)}")
        return cls.for_scale_k(floors[floor_name], stencil=stencil, **kw)

    @classmethod
    def for_neighbor_template(cls, neighbor_template: str = "fcc", **kw: object) -> "MConfig":
        """κ_link = 1/|N| для шаблона соседства (§1.6 · §5.2.2)."""
        return cls.for_stencil(neighbor_template, **kw)

    @classmethod
    def for_neighbor_scheme(cls, neighbor_scheme: str = "fcc", **kw: object) -> "MConfig":
        """Совместимость → ``for_neighbor_template``."""
        return cls.for_neighbor_template(neighbor_scheme, **kw)

    @classmethod
    def for_stencil(cls, stencil: str = "fcc", **kw: object) -> "MConfig":
        """Совместимость: ``stencil`` = шаблон соседства n4|hex|fcc."""
        n = stencil_n_links(stencil)
        k = kappa_link(n_links=n)
        base = cls(stencil=stencil, gamma=k, cr_strength=k)
        return replace(base, **kw) if kw else base  # type: ignore[arg-type]
