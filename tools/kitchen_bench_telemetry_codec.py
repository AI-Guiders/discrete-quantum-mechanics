"""
Acousto-Optical Telemetry Codec for the 12-Beam Cuboctahedron Kitchen Bench
(`tools/kitchen_bench_telemetry_codec.py`).

Proves and verifies 100% lossless recovery of all 512 ring phases dphi in Z_512
directly from the two non-invasive physical bench measurements:
  1. BaTiO3 Piezo-Hydrophone Acoustic Standing Wave Pressure:
       P_sound(dphi) = mu0 * mu1 * (128 - C_3(dphi))
  2. Crossed-Polarizer (I_3^- PVA film) Chiral Optical Reaction Current:
       J_rxn(dphi)   = mu0 * mu1 * S_3(dphi)
  3. Optical Absorption Peak Wavelength on USB Webcam:
       lambda_nm(dphi) = 579 + (139 * C_3(dphi)) // 128 in [440, 718] nm.
"""

from __future__ import annotations
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "hardware"))

import cuboctahedron_mcp_server as mcp  # noqa: E402


def encode_bench_telemetry(dphi: int, mu0: int = 13, mu1: int = 13) -> dict:
    p = dphi % 512
    c_val = mcp.proj_c(p)
    s_val = mcp.proj_s(p)
    amp = max(1, int(mu0) * int(mu1))
    p_sound = amp * (128 - c_val)
    j_rxn = amp * s_val
    lambda_nm = 579 + (139 * c_val) // 128
    return {
        "dphi_tx": p,
        "c3": c_val,
        "s3": s_val,
        "p_sound": p_sound,
        "j_rxn": j_rxn,
        "lambda_nm": lambda_nm,
    }


def decode_bench_telemetry(p_sound: int, j_rxn: int, mu0: int = 13, mu1: int = 13) -> int:
    amp = max(1, int(mu0) * int(mu1))
    c_rec = 128 - (int(p_sound) // amp)
    s_rec = int(j_rxn) // amp
    if s_rec > 0 and c_rec >= 0:
        return s_rec
    if s_rec >= 0 and c_rec < 0:
        return 256 - s_rec
    if s_rec < 0 and c_rec <= 0:
        return 256 - s_rec
    return (512 + s_rec) % 512


def verify_all_512_ring_states() -> dict:
    recovered = 0
    for dphi in range(512):
        pkt = encode_bench_telemetry(dphi, mu0=13, mu1=13)
        rec = decode_bench_telemetry(pkt["p_sound"], pkt["j_rxn"], mu0=13, mu1=13)
        if rec == dphi:
            recovered += 1
    return {
        "total_ring_states_tested": 512,
        "bit_exact_recovered_states": recovered,
        "all_512_recovered": recovered == 512,
        "sample_stage_telemetry": {
            "stage0_1_2_4_collapse_139": encode_bench_telemetry(139),
            "stage3_ultrasonic_folding_128": encode_bench_telemetry(128),
            "stage5_phase_stasis_0": encode_bench_telemetry(0),
            "dry_clean_pauli_mirror_256": encode_bench_telemetry(256),
        },
    }


def main() -> int:
    res = verify_all_512_ring_states()
    print(json.dumps(res, indent=2, ensure_ascii=False))
    return 0 if res["all_512_recovered"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
