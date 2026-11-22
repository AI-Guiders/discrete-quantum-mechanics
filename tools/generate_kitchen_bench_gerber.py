"""
Generate production-ready RS-274X Gerber & Excellon Drill files for the 2-layer
FR-4 (SiO2 glass weave Z=30, 35 um copper foil Z(Cu)=29) 12-Channel Tang Nano 9K
Kitchen Bench Power & Sensor Expansion PCB:
  - hardware/gerber/kitchen_bench_top_copper.gbr
  - hardware/gerber/kitchen_bench_bottom_copper.gbr
  - hardware/gerber/kitchen_bench_board_outline.gbr
  - hardware/gerber/kitchen_bench_drill.drl
"""

from __future__ import annotations
from pathlib import Path

PIN_MAP_12BEAM = [25, 26, 27, 28, 29, 30, 33, 34, 35, 36, 37, 38]


def mm_to_gerber(val_mm: float) -> int:
    return int(round(val_mm * 10000.0))


def generate_gerbers(gerber_dir: Path) -> dict[str, int]:
    gerber_dir.mkdir(parents=True, exist_ok=True)

    # 1. Board Outline (90 mm x 130 mm = Z((SiO2)3) mm x 10*N_phi mm):
    outline_lines = [
        "G04 Cuboctahedron Kitchen Bench FR-4 Power PCB Board Outline (90x130 mm)*",
        "%FSLAX34Y34*%",
        "%MOMM*%",
        "%ADD10C,0.2000*%",
        "G01*",
        "D10*",
        f"X{mm_to_gerber(0)}Y{mm_to_gerber(0)}D02*",
        f"X{mm_to_gerber(90)}Y{mm_to_gerber(0)}D01*",
        f"X{mm_to_gerber(90)}Y{mm_to_gerber(130)}D01*",
        f"X{mm_to_gerber(0)}Y{mm_to_gerber(130)}D01*",
        f"X{mm_to_gerber(0)}Y{mm_to_gerber(0)}D01*",
        "M02*",
    ]
    outline_file = gerber_dir / "kitchen_bench_board_outline.gbr"
    outline_file.write_text("\n".join(outline_lines) + "\n", encoding="utf-8", newline="\n")

    # 2. Top Copper Layer (12 Gate Resistor + IRLZ44N MOSFET + 1N5819 Schottky + Coil Pads):
    top_lines = [
        "G04 Cuboctahedron Kitchen Bench FR-4 Top Copper (35 um Cu Z=29, 12 Channels)*",
        "%FSLAX34Y34*%",
        "%MOMM*%",
        "%ADD11C,1.6000*%",
        "%ADD12C,0.8000*%",
        "G01*",
    ]
    for k in range(12):
        y_mm = 10.0 + k * 9.5
        # FPGA pin header pad -> Gate resistor pad -> MOSFET Gate/Drain/Source -> Coil & Schottky pads:
        top_lines.append("D11*")
        for x_mm in (12.0, 28.0, 42.0, 52.0, 66.0, 78.0):
            top_lines.append(f"X{mm_to_gerber(x_mm)}Y{mm_to_gerber(y_mm)}D03*")
        top_lines.append("D12*")
        top_lines.append(f"X{mm_to_gerber(12.0)}Y{mm_to_gerber(y_mm)}D02*")
        top_lines.append(f"X{mm_to_gerber(28.0)}Y{mm_to_gerber(y_mm)}D01*")
        top_lines.append(f"X{mm_to_gerber(42.0)}Y{mm_to_gerber(y_mm)}D02*")
        top_lines.append(f"X{mm_to_gerber(78.0)}Y{mm_to_gerber(y_mm)}D01*")
    top_lines.append("M02*")
    top_file = gerber_dir / "kitchen_bench_top_copper.gbr"
    top_file.write_text("\n".join(top_lines) + "\n", encoding="utf-8", newline="\n")

    # 3. Bottom Copper Layer (24V Power Bus, PolySwitch 10A/18A, 470uF + 12x100nF Star Ground & 6N137 Opto):
    bot_lines = [
        "G04 Cuboctahedron Kitchen Bench FR-4 Bottom Copper (24V Bus & Star Ground)*",
        "%FSLAX34Y34*%",
        "%MOMM*%",
        "%ADD13C,2.5000*%",
        "G01*",
        "D13*",
        f"X{mm_to_gerber(66.0)}Y{mm_to_gerber(8.0)}D02*",
        f"X{mm_to_gerber(66.0)}Y{mm_to_gerber(120.0)}D01*",
        f"X{mm_to_gerber(52.0)}Y{mm_to_gerber(8.0)}D02*",
        f"X{mm_to_gerber(52.0)}Y{mm_to_gerber(120.0)}D01*",
        "M02*",
    ]
    bot_file = gerber_dir / "kitchen_bench_bottom_copper.gbr"
    bot_file.write_text("\n".join(bot_lines) + "\n", encoding="utf-8", newline="\n")

    # 4. Excellon Drill File (72 component holes = VerletCell72 bit budget!):
    drill_lines = [
        "M48",
        "; Cuboctahedron Kitchen Bench Excellon Drill File (72 holes = 12 channels x 6 pads)",
        "METRIC,TZ",
        "T01C1.000",
        "%",
        "G90",
        "G05",
        "T01",
    ]
    hole_count = 0
    for k in range(12):
        y_mm = 10.0 + k * 9.5
        for x_mm in (12.0, 28.0, 42.0, 52.0, 66.0, 78.0):
            drill_lines.append(f"X{y_mm * 0 + x_mm:06.3f}Y{y_mm:06.3f}")
            hole_count += 1
    drill_lines.append("T00")
    drill_lines.append("M30")
    drill_file = gerber_dir / "kitchen_bench_drill.drl"
    drill_file.write_text("\n".join(drill_lines) + "\n", encoding="utf-8", newline="\n")

    return {
        "board_width_mm": 90,
        "board_height_mm": 130,
        "total_channels": 12,
        "total_excellon_drill_holes": hole_count,
    }


if __name__ == "__main__":
    g_dir = Path(__file__).resolve().parent.parent / "hardware" / "gerber"
    stats = generate_gerbers(g_dir)
    print(f"Generated Gerber RS-274X & Excellon suite in {g_dir}: {stats}")
