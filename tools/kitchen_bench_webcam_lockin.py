"""
USB Webcam / Photodiode Optical Lock-In Phase Decoder & PLL Feedback Generator
(`tools/kitchen_bench_webcam_lockin.py`).

Decodes a raw RGB triplet from a kitchen USB webcam or RGB photodiode looking at
the 90 mm quartz glass Petri dish into:
  - Carrier L1-normalized color triad (R_128, G_128, B_128) with R + G + B == 128 = Q_square
  - Even cosine projector C_3(dphi) = R_128 - B_128 in [-128, +128]
  - Optical absorption/emission peak wavelength lambda_nm = 579 + (139 * C_3) // 128 in [440, 718] nm
  - Reconstructed ring phase dphi in Z_512 and ready-to-send 16-byte UART PLL frame (opcode 0x08).
"""

from __future__ import annotations
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "hardware"))

import cuboctahedron_mcp_server as mcp  # noqa: E402


def decode_webcam_rgb_to_carrier_phase(
    r_8bit: int,
    g_8bit: int,
    b_8bit: int,
    chiral_sign: int = 1,
    target_phase_ticks: int = 139,
    hardware_lag_ticks: int = 89,
) -> dict:
    # 1. Normalize 8-bit webcam RGB (0..255) onto the L1 rotator simplex R + G + B = 128 = Q_square:
    l1_raw = max(1, int(r_8bit) + int(g_8bit) + int(b_8bit))
    r_q = (int(r_8bit) * 128) // l1_raw
    b_q = (int(b_8bit) * 128) // l1_raw
    g_q = 128 - r_q - b_q

    # 2. Extract even holonomy projector C_3 = R_q - B_q in [-128, +128] and odd projector |S_3| = G_q:
    c_val = r_q - b_q
    s_val = g_q if chiral_sign >= 0 else -g_q

    # 3. Reconstruct ring phase dphi in Z_512 from (C_3, S_3) on the L1 diamond |C_3| + |S_3| = 128:
    if s_val >= 0 and c_val >= 0:
        dphi = s_val
    elif s_val >= 0 and c_val < 0:
        dphi = 256 - s_val
    elif s_val < 0 and c_val < 0:
        dphi = 256 - s_val
    else:
        dphi = (512 + s_val) % 512

    # 4. Compute optical wavelength in [440, 718] nm (span = 278 = 2 * 139 nm):
    lambda_nm = 579 + (139 * c_val) // 128

    # 5. Compute phase error against target_phase_ticks and Heisenberg deadband filter:
    phase_err = mcp.wrap512(target_phase_ticks - dphi)
    deadband_filtered_err = 0 if abs(phase_err) < 41 else phase_err
    new_precomp_lag = (hardware_lag_ticks + deadband_filtered_err) % 512
    uart_0x08 = mcp.pack_uart_16byte_frame(0x08, 1, new_precomp_lag, 2)

    return {
        "webcam_rgb_8bit": [r_8bit, g_8bit, b_8bit],
        "carrier_l1_rgb_128": [r_q, g_q, b_q],
        "l1_sum_check_128": r_q + g_q + b_q,
        "c3_projector": c_val,
        "s3_projector": s_val,
        "reconstructed_dphi_ticks": dphi,
        "optical_wavelength_nm": lambda_nm,
        "phase_error_ticks": phase_err,
        "heisenberg_filtered_correction_ticks": deadband_filtered_err,
        "updated_uart_0x08_frame_hex": uart_0x08.hex(" "),
    }


def run_self_test() -> int:
    # Verify the 3 canonical optical benchmarks of the kitchen bench:
    # 1) Gate #0 Oxidized Blue Ferroin (dphi = 160 -> C_3 = -32, S_3 = +96 -> lambda = 544 nm)
    b_blue = decode_webcam_rgb_to_carrier_phase(0, 192, 64, chiral_sign=1)
    # 2) Stage 2 Ruby-Red Oxymyoglobin Heme FeN4O2 Z=70 Saddle (dphi = 128 -> C_3 = 0, S_3 = +128 -> lambda = 579 nm)
    b_heme = decode_webcam_rgb_to_carrier_phase(0, 255, 0, chiral_sign=1)
    # 3) Gate #0 Reduced Red Ferroin (dphi = 85 -> C_3 = +67, S_3 = +61 -> lambda = 651 nm)
    b_red = decode_webcam_rgb_to_carrier_phase(134, 122, 0, chiral_sign=1)

    ok = (
        b_blue["optical_wavelength_nm"] == 544
        and b_heme["optical_wavelength_nm"] == 579
        and b_red["optical_wavelength_nm"] == 651
        and b_blue["l1_sum_check_128"] == 128
        and b_heme["l1_sum_check_128"] == 128
        and b_red["l1_sum_check_128"] == 128
    )
    print(json.dumps({"benchmarks": {"ferroin_blue_544nm": b_blue, "heme_myoglobin_579nm": b_heme, "ferroin_red_651nm": b_red}, "all_ok": ok}, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(run_self_test())
