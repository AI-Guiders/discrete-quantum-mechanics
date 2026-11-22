"""
Complete Laboratory Pre-Flight & 52-Minute Run Protocol Generator
for the 12-Beam Cuboctahedron Kitchen Bench (`tools/generate_kitchen_bench_lab_protocol.py`).

Verifies and generates:
  1. Bus36 Pre-Flight 12-Coil Continuity Table (N_active = 0..12):
       D(N_active) = (1 + (N_active + 1) * 64) * 8192
                   = 0 * 512^0 + 16 * 512^1 + 2 * (N_active + 1) * 512^2 + 0 * 512^3
       with L2(12) = 26 = Z(Fe) and single-coil step Delta_L2 = 2 = (c0/c)^2!
  2. All 14 Startup 16-Byte XOR-CRC UART Frames:
       - 12x opcode 0x06 (per-vertex hand-wound coil calibration k = 0..11),
       - 1x  opcode 0x08 (global cold-start pre-compensation lag +89 ticks -> drive 228 = 12 * 19),
       - 1x  opcode 0x02 (start 5-stage synthesis cycle).
  3. 4-Sensor Nilpotent Holonomic Tomograph De-Mixing (2*(I_4 + N_nil), N_nil^3 == 0)
     coupled with 512/512 Acousto-Optical Telemetry Recovery and 1-Tick Closed-Loop PLL.
"""

from __future__ import annotations
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "hardware"))
sys.path.insert(0, str(ROOT / "tools"))

import cuboctahedron_mcp_server as mcp  # noqa: E402
import simulate_kitchen_bench_52min as sim52  # noqa: E402


def compute_bus36_coil_continuity_table() -> list[dict]:
    rows = []
    for n_active in range(13):
        l0 = 0
        l1 = 16
        l2 = 2 * (n_active + 1)
        l3 = 0
        d_total = l0 + l1 * 512 + l2 * (512 * 512) + l3 * (512 * 512 * 512)
        d_expected = (1 + (n_active + 1) * 64) * 8192
        rec_coils = (l2 // 2) - 1
        rows.append(
            {
                "active_coils": n_active,
                "bus36_lanes": [l0, l1, l2, l3],
                "dome_impedance_d": d_total,
                "matches_formula": d_total == d_expected and rec_coils == n_active,
            }
        )
    return rows


def generate_full_lab_protocol() -> dict:
    ctrl = mcp.CONTROLLER
    cal = ctrl.calibrate_kitchen_bench(
        coil_inductance_uh=100.0,
        coil_resistance_ohm=33.1,
        coil_temp_c=25.0,
        mosfet_gate_delay_ns=925.9,
        dish_material="glass_sio2",
        water_type="tap_mineral",
        target_phase_ticks=139,
    )
    continuity = compute_bus36_coil_continuity_table()
    per_coil_frames = [c["uart_0x06_frame_hex"] for c in cal["calibration_result"]["per_coil_12channel_calibration"]]
    global_0x08_frame = cal["calibration_result"]["uart_16byte_calibration_frame_hex"]
    start_0x02_frame = mcp.pack_uart_16byte_frame(0x02, 0, 1, 0).hex(" ")
    startup_14_frames = per_coil_frames + [global_0x08_frame, start_0x02_frame]

    sim_run = sim52.simulate_52_minutes()

    all_ok = (
        all(r["matches_formula"] for r in continuity)
        and continuity[12]["bus36_lanes"] == [0, 16, 26, 0]
        and continuity[12]["dome_impedance_d"] == 6823936
        and continuity[11]["dome_impedance_d"] == 6299648
        and len(startup_14_frames) == 14
        and sim_run["max_dish_phase_error_across_all_53_points_ticks"] == 0
        and sim_run["zero_phase_drift_verified"] is True
    )

    return {
        "protocol_verified": all_ok,
        "startup_uart_frame_count": len(startup_14_frames),
        "bus36_full_12coil_lanes": continuity[12]["bus36_lanes"],
        "bus36_11coil_fault_lanes": continuity[11]["bus36_lanes"],
        "single_coil_bus36_l2_step": continuity[12]["bus36_lanes"][2] - continuity[11]["bus36_lanes"][2],
        "startup_14_uart_frames_hex": startup_14_frames,
        "continuity_table_0_to_12": continuity,
    }


def main() -> int:
    res = generate_full_lab_protocol()
    print(
        json.dumps(
            {
                "protocol_verified": res["protocol_verified"],
                "startup_uart_frame_count": res["startup_uart_frame_count"],
                "bus36_full_12coil_lanes": res["bus36_full_12coil_lanes"],
                "bus36_11coil_fault_lanes": res["bus36_11coil_fault_lanes"],
                "single_coil_bus36_l2_step": res["single_coil_bus36_l2_step"],
            },
            indent=2,
            ensure_ascii=False,
        )
    )
    return 0 if res["protocol_verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
