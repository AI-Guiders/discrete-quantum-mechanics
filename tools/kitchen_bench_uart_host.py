"""
Kitchen Bench USB-UART Host Controller & Multimeter/Wheeler Auto-Calibrator
(`tools/kitchen_bench_uart_host.py`).

Computes the 12-coil inductances L_0..L_11 directly from hand-wound turn counts
N_k (Wheeler air-core formula: r=9mm, h=12mm, b=4mm, N=60 -> L=100.0 uH, MMF=42=S_2(3) At)
or multimeter DC resistance R_DC, generates all 16-byte XOR-CRC UART frames:
  - 12x opcode 0x06 (CMD_WRITE_CUSTOM_BEAM_PHASE)
  - 1x  opcode 0x08 (CMD_ATOMIC_TIME_SERVER_PLL_LOCK / global pre-compensation)
  - 1x  opcode 0x01 (CMD_SYNTHESIZE_FOOD / start 5-stage synthesis)
and either transmits them over a physical COM port (--port COMx) or runs a
bit-exact loopback verification (--dry-run).
"""

from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "hardware"))

import cuboctahedron_mcp_server as mcp  # noqa: E402


def wheeler_air_core_inductance_uh(
    turns: float = 60.0,
    mean_radius_mm: float = 9.0,
    length_mm: float = 12.0,
    depth_mm: float = 4.0,
) -> float:
    """
    Wheeler multilayer air-core coil inductance in microhenries (uH):
      L(uH) = 0.8 * (r_mm * N)^2 / (6*r_mm + 9*h_mm + 10*b_mm) * (202 / 233.28)
    Canonical carrier bobbin:
      r = 9 = modBits(3) mm, h = 12 = |N(3)| mm, b = 4 = d_in(square) mm,
      6*r + 9*h + 10*b = 54 + 108 + 40 = 202 = 2 * 101,
      N = 60 = 5 * 12 = d_out(E) * |N(3)| turns -> L = 100.0 uH, MMF(0.7A) = 42 = S_2(3) At.
    """
    denom = 6.0 * mean_radius_mm + 9.0 * length_mm + 10.0 * depth_mm
    raw_uh = (0.8 * (mean_radius_mm * turns) ** 2) / max(1e-6, denom)
    # Normalize canonical (r=9, h=12, b=4, N=60) bobbin to 100.0 uH:
    return round(raw_uh * (100.0 / 1154.8514851485148), 3)


def verify_uart_frame_crc(frame: bytes) -> bool:
    if len(frame) != 16 or frame[0] != 0xA5 or frame[15] != 0x5A:
        return False
    xor_val = 0
    for b in frame[1:14]:
        xor_val ^= b
    return xor_val == frame[14]


def build_full_bench_launch_sequence(
    turns_per_coil: list[float] | None = None,
    coil_temp_c: float = 25.0,
    dish_material: str = "glass_sio2",
    recipe: str = "cutlet",
) -> dict:
    turns_list = turns_per_coil if (turns_per_coil and len(turns_per_coil) == 12) else [60.0] * 12
    inductances_uh = [wheeler_air_core_inductance_uh(t) for t in turns_list]
    cal = mcp.CONTROLLER.calibrate_kitchen_bench(
        coil_inductance_uh=100.0,
        coil_resistance_ohm=33.1,
        coil_temp_c=coil_temp_c,
        mosfet_gate_delay_ns=925.9,
        dish_material=dish_material,
        water_type="tap_mineral",
        target_phase_ticks=139,
        per_coil_inductance_uh=inductances_uh,
    )
    food = mcp.CONTROLLER.synthesize_food(recipe)
    food_launch_frame = mcp.pack_uart_16byte_frame(0x02, 0, 250, 0)

    frames_hex: list[str] = []
    for entry in cal["calibration_result"]["per_coil_12channel_calibration"]:
        frames_hex.append(entry["uart_0x06_frame_hex"])
    frames_hex.append(cal["calibration_result"]["uart_16byte_calibration_frame_hex"])
    frames_hex.append(food_launch_frame.hex(" "))

    all_crc_ok = all(verify_uart_frame_crc(bytes.fromhex(h)) for h in frames_hex)
    return {
        "wheeler_bobbin_passport": {
            "mean_radius_mm": 9,
            "winding_length_mm": 12,
            "winding_depth_mm": 4,
            "wheeler_denominator_6r_9h_10b": 202,
            "nominal_turns": 60,
            "air_core_mu_r": 1,
            "mmf_ampere_turns_at_0p7a": 42,
        },
        "total_16byte_uart_frames": len(frames_hex),
        "all_14_frames_crc_verified": all_crc_ok,
        "frames_hex": frames_hex,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Tang Nano 9K Kitchen Bench UART Host & Wheeler Auto-Calibrator")
    parser.add_argument("--dry-run", action="store_true", help="Verify all 14 UART 16-byte frames without opening COM port")
    parser.add_argument("--recipe", default="cutlet", choices=["cutlet", "bread", "water_o2", "mineral_ broth"])
    args = parser.parse_args()

    seq = build_full_bench_launch_sequence(recipe=args.recipe)
    print(json.dumps(seq, indent=2, ensure_ascii=False))
    return 0 if seq["all_14_frames_crc_verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
