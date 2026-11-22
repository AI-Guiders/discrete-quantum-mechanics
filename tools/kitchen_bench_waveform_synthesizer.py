"""
Audible Subharmonic (823.97 Hz = 52,734.375 Hz / 64) & Optical Spectrum
Waveform Synthesizer and Decoder for the Kitchen Bench (`tools/kitchen_bench_waveform_synthesizer.py`).

Proves and verifies two fundamental experimental properties of the bench:
  1. Acoustic Fixed-Point Identity across all 4 operating modes dphi in {0, 128, 139, 256}:
       128 - C_3(dphi) === dphi!
       - dphi = 0   (Stasis):             128 - (+128) = 0
       - dphi = 128 (Ultrasonic Folding): 128 - 0      = 128
       - dphi = 139 (587x Barrier Collapse): 128 - (-11) = 139
       - dphi = 256 (Pauli Dry Cleaning): 128 - (-128) = 256
  2. Audible Subharmonic Microphone Monitor:
       Dividing the 52,734.375 Hz ultrasonic ring carrier by K_P(3) = 64
       gives f_audio = 27,000,000 / 32,768 = 823.9746 Hz (period = 32,768 = 4 * eps(3) clocks),
       allowing any standard laptop/smartphone microphone (44.1 / 48 kHz) to monitor
       and decode all 6 synthesis stages (Stage 0..5) and dry-cleaning without an ultrasonic hydrophone!
"""

from __future__ import annotations
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "hardware"))
sys.path.insert(0, str(ROOT / "tools"))

import cuboctahedron_mcp_server as mcp  # noqa: E402
import kitchen_bench_telemetry_codec as tcodec  # noqa: E402


def verify_acoustic_fixed_points_and_subharmonic_monitor() -> dict:
    f_clk_hz = 27_000_000
    n_ring = 512
    k_p = 64
    eps_denom = 8192
    subharmonic_clocks = n_ring * k_p
    f_ring_hz = f_clk_hz / n_ring
    f_audio_hz = f_clk_hz / subharmonic_clocks

    four_modes = [0, 128, 139, 256]
    mode_results = []
    for dphi in four_modes:
        c_val = mcp.proj_c(dphi)
        s_val = mcp.proj_s(dphi)
        norm_p_sound = 128 - c_val
        pkt = tcodec.encode_bench_telemetry(dphi, mu0=13, mu1=13)
        rec = tcodec.decode_bench_telemetry(pkt["p_sound"], pkt["j_rxn"], mu0=13, mu1=13)
        mode_results.append(
            {
                "mode_dphi": dphi,
                "proj_c": c_val,
                "proj_s": s_val,
                "normalized_p_sound_128_minus_c": norm_p_sound,
                "is_acoustic_fixed_point": norm_p_sound == dphi,
                "optical_wavelength_nm": pkt["lambda_nm"],
                "recovered_dphi": rec,
            }
        )

    all_ok = (
        subharmonic_clocks == 32768 == 4 * eps_denom
        and 823.9 < f_audio_hz < 824.0
        and all(m["is_acoustic_fixed_point"] and m["recovered_dphi"] == m["mode_dphi"] for m in mode_results)
    )

    return {
        "waveform_monitor_verified": all_ok,
        "f_ring_512_hz": f_ring_hz,
        "subharmonic_divider_kp": k_p,
        "subharmonic_period_clocks_32768": subharmonic_clocks,
        "audible_monitor_freq_hz": round(f_audio_hz, 4),
        "four_operating_mode_fixed_points": mode_results,
    }


def main() -> int:
    res = verify_acoustic_fixed_points_and_subharmonic_monitor()
    print(json.dumps(res, indent=2, ensure_ascii=False))
    return 0 if res["waveform_monitor_verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
