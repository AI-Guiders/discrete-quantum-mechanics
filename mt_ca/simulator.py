"""Layer 3 (Instruments / Lab) — LatticeFluidSimulator driving M-layer carrier_core with T-layer readout."""

from __future__ import annotations

from dataclasses import asdict
from pathlib import Path
from typing import Any

import torch

from mt_ca.carrier_core import carrier_reverse, carrier_step
from mt_ca.config import MConfig
from mt_ca.m_to_t import decode_from_carrier, encode_to_carrier
from mt_ca.metrics import field_amplitude, total_norm_squared
from mt_ca.seeds import SeedClass, make_seed


class LatticeFluidSimulator:
    def __init__(
        self,
        ny: int,
        nx: int,
        cfg: MConfig | None = None,
        *,
        nz: int | None = None,
        device: str | torch.device | None = None,
        dtype: torch.dtype = torch.complex64,
    ) -> None:
        self.cfg = cfg or MConfig()
        self.ny = ny
        self.nx = nx
        if self.cfg.stencil == "fcc":
            self.nz = ny if nz is None else nz
        else:
            self.nz = None if nz is None else nz
        if device is None:
            device = "cuda" if torch.cuda.is_available() else "cpu"
        self.device = torch.device(device)
        self.dtype = dtype
        self._z_cache: torch.Tensor | None = torch.zeros(*self.spatial_shape, 2, device=self.device, dtype=dtype)
        self._z_past_cache: torch.Tensor | None = torch.zeros_like(self._z_cache)
        self._state_curr: torch.Tensor | None = None
        self._state_past: torch.Tensor | None = None
        self._norm0: float | None = None
        self.tick: int = 0

    @property
    def spatial_shape(self) -> tuple[int, ...]:
        if self.cfg.stencil == "fcc":
            assert self.nz is not None
            return (self.nz, self.ny, self.nx)
        return (self.ny, self.nx)

    @property
    def z(self) -> torch.Tensor:
        """Lazy T-layer readout: decoded from M-layer integer state_curr only when requested."""
        if self._z_cache is None and self._state_curr is not None:
            self._z_cache = decode_from_carrier(self._state_curr, self.cfg).to(
                device=self.device, dtype=self.dtype
            )
        assert self._z_cache is not None
        return self._z_cache

    @z.setter
    def z(self, val: torch.Tensor) -> None:
        self._z_cache = val

    @property
    def z_past(self) -> torch.Tensor:
        """Lazy T-layer prior-tick readout."""
        if self._z_past_cache is None and self._state_past is not None:
            self._z_past_cache = decode_from_carrier(self._state_past, self.cfg).to(
                device=self.device, dtype=self.dtype
            )
        assert self._z_past_cache is not None
        return self._z_past_cache

    @z_past.setter
    def z_past(self, val: torch.Tensor) -> None:
        self._z_past_cache = val

    @property
    def state_curr(self) -> torch.Tensor:
        """Direct access to the current M-layer integer cell register."""
        if self._state_curr is None:
            self._state_curr = encode_to_carrier(self.z, self.cfg)
        return self._state_curr

    @property
    def state_past(self) -> torch.Tensor:
        """Direct access to the prior-tick M-layer integer cell register."""
        if self._state_past is None:
            self._state_past = encode_to_carrier(self.z_past, self.cfg)
        return self._state_past

    @property
    def f_curr(self) -> torch.Tensor:
        return self.state_curr

    @property
    def f_past(self) -> torch.Tensor:
        return self.state_past

    def _sync_t_readout(self) -> None:
        """Invalidate T-layer complex readout caches after M-layer integer ticks."""
        self._z_cache = None
        self._z_past_cache = None

    def _init_carrier_state(self, z: torch.Tensor) -> None:
        s0 = encode_to_carrier(z, self.cfg)
        self._state_curr = s0.clone()
        self._state_past = s0.clone()
        self.tick = 0
        self._sync_t_readout()

    def reset(self, seed_class: SeedClass = SeedClass.VACUUM_BOIL) -> None:
        kw: dict = {
            "device": self.device,
            "dtype": self.dtype,
            "mod_bits": self.cfg.mod_bits,
            "frac_bits": self.cfg.frac_bits,
            "phase_bits": self.cfg.phase_bits,
        }
        if self.cfg.stencil == "fcc":
            kw["nz"] = self.nz
        self.z = make_seed(seed_class, self.ny, self.nx, **kw)
        self.z_past = self.z.clone()
        self._init_carrier_state(self.z)
        self._norm0 = total_norm_squared(self.z)

    def set_field(
        self,
        z: torch.Tensor,
        *,
        z_past: torch.Tensor | None = None,
        momentum_k: tuple[float, ...] | None = None,
    ) -> None:
        expected = (*self.spatial_shape, 2)
        if tuple(z.shape) != expected:
            raise ValueError(f"Expected {expected}, got {tuple(z.shape)}")
        self.z = z.to(device=self.device, dtype=self.dtype)
        if z_past is not None:
            self.z_past = z_past.to(device=self.device, dtype=self.dtype)
        elif momentum_k is not None:
            if self.cfg.stencil == "fcc":
                kz, ky, kx = (momentum_k + (0.0, 0.0, 0.0))[:3]
                rolled = torch.roll(self.z, shifts=(1, 1, 1), dims=(0, 1, 2))
                phase = torch.exp(
                    torch.tensor(-1j * (kz + ky + kx), device=self.device, dtype=self.dtype)
                )
            else:
                ky, kx = momentum_k[:2]
                rolled = torch.roll(self.z, shifts=(1, 1), dims=(0, 1))
                phase = torch.exp(
                    torch.tensor(-1j * (ky + kx), device=self.device, dtype=self.dtype)
                )
            self.z_past = rolled * phase
            n0 = total_norm_squared(self.z)
            n_p = total_norm_squared(self.z_past)
            if n_p > 1e-12:
                self.z_past = self.z_past * (n0 / n_p) ** 0.5
        else:
            self.z_past = self.z.clone()
        self._state_curr = encode_to_carrier(self.z, self.cfg)
        self._state_past = encode_to_carrier(self.z_past, self.cfg)
        self.tick = 0
        self._sync_t_readout()
        self._norm0 = total_norm_squared(self.z)

    def step(self, steps: int = 1) -> torch.Tensor:
        assert self._state_curr is not None and self._state_past is not None
        if steps <= 0:
            return self.z
        for _ in range(steps):
            s_next, s_prev, _ = carrier_step(self._state_curr, self._state_past, self.cfg)
            self._state_curr = s_next
            self._state_past = s_prev
        self.tick += int(steps)
        self._sync_t_readout()
        return self.z

    def step_reverse(self, steps: int = 1) -> torch.Tensor:
        """Literal M-layer reverse Z⁻ = (2Z + ⌊𝒩(Z)⌋ − Z⁺) mod N directly from (state_past, state_curr)."""
        assert self._state_curr is not None and self._state_past is not None
        if steps <= 0:
            return self.z
        for _ in range(steps):
            s_past, s_curr = carrier_reverse(self._state_past, self._state_curr, self.cfg)
            self._state_past = s_past
            self._state_curr = s_curr
        self.tick -= int(steps)
        self._sync_t_readout()
        return self.z

    def checkpoint_dict(self) -> dict[str, Any]:
        """Serialize exact integer Markov pair (state_curr, state_past), tick, and MConfig for bit-exact resume."""
        if self._state_curr is None or self._state_past is None:
            raise ValueError("Simulator state is uninitialized; call reset() or set_field() first")
        return {
            "tick": int(self.tick),
            "ny": int(self.ny),
            "nx": int(self.nx),
            "nz": None if self.nz is None else int(self.nz),
            "cfg": asdict(self.cfg),
            "norm0": self._norm0,
            "f_curr": self._state_curr.detach().cpu(),
            "f_past": self._state_past.detach().cpu(),
        }

    def save_checkpoint(self, path: str | Path) -> Path:
        """Save bit-exact integer state (state_curr, state_past) to disk so simulation can resume from `tick`."""
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        torch.save(self.checkpoint_dict(), p)
        return p

    def load_checkpoint(self, path_or_dict: str | Path | dict[str, Any]) -> None:
        """Load bit-exact integer state (state_curr, state_past) into this simulator instance."""
        ckpt = (
            path_or_dict
            if isinstance(path_or_dict, dict)
            else torch.load(Path(path_or_dict), map_location="cpu", weights_only=False)
        )
        self.cfg = MConfig(**ckpt["cfg"])
        self.ny = int(ckpt["ny"])
        self.nx = int(ckpt["nx"])
        self.nz = None if ckpt["nz"] is None else int(ckpt["nz"])
        self.tick = int(ckpt["tick"])
        self._norm0 = ckpt.get("norm0")
        self._state_curr = ckpt["f_curr"].to(device=self.device)
        self._state_past = ckpt["f_past"].to(device=self.device)
        self._sync_t_readout()

    @classmethod
    def from_checkpoint(
        cls,
        path_or_dict: str | Path | dict[str, Any],
        *,
        device: str | torch.device | None = None,
        dtype: torch.dtype = torch.complex64,
    ) -> "LatticeFluidSimulator":
        """Instantiate a LatticeFluidSimulator directly from a saved checkpoint file or dict."""
        ckpt = (
            path_or_dict
            if isinstance(path_or_dict, dict)
            else torch.load(Path(path_or_dict), map_location="cpu", weights_only=False)
        )
        cfg = MConfig(**ckpt["cfg"])
        sim = cls(
            int(ckpt["ny"]),
            int(ckpt["nx"]),
            cfg,
            nz=ckpt["nz"],
            device=device,
            dtype=dtype,
        )
        sim.load_checkpoint(ckpt)
        return sim

    @property
    def norm0(self) -> float:
        if self._norm0 is None:
            return 0.0
        return self._norm0

    def norm(self) -> float:
        return total_norm_squared(self.z)

    def snapshot_amplitude(self) -> torch.Tensor:
        return field_amplitude(self.z).detach().cpu()
