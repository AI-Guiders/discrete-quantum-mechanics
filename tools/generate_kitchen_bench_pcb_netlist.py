"""
Generate the complete KiCad / SPICE PCB Netlist for the 12-Channel Tang Nano 9K
Kitchen Bench Power & Sensor Expansion Board:
  hardware/kitchen_bench_power_board.net
"""

from __future__ import annotations
from pathlib import Path

PIN_MAP_12BEAM = [25, 26, 27, 28, 29, 30, 33, 34, 35, 36, 37, 38]


def generate_netlist(out_path: Path) -> int:
    lines = [
        "* ============================================================================",
        "* hardware/kitchen_bench_power_board.net",
        "* Complete 36-Edge (12 Radial + 24 Shell = Bus36) FR-4 Power & Sensor Expansion",
        "* PCB Netlist for Sipeed Tang Nano 9K (GW1NR-LV9QN88PC6/I5, 27.000 MHz)",
        "* ============================================================================",
        "",
        "* [A] Power Entry, PolySwitch PTC Fuse (I_hold=10A=Z(Ne), I_trip=18A=Z(Ar)) & Bulk Decoupling:",
        "V_PSU_24V   VIN_24V   GND_PWR   DC 24.0",
        "F_PTC_10A   VIN_24V   VDD_24V   POLYSWITCH_10A_HOLD_18A_TRIP",
        "C_BULK_470U VDD_24V   GND_PWR   470uF_35V_LOW_ESR",
        "",
        "* [B] High-Speed GaAs Optocoupler USB-UART Isolation (6N137, Z(GaAs)=31+33=64=K_P):",
        "U_OPT_RX    USB_TX_PC GND_USB   FPGA_PIN18_RX VDD_3V3 GND_PWR 6N137_GAAS_OPTO",
        "U_OPT_TX    FPGA_PIN17_TX GND_PWR USB_RX_PC   VDD_USB GND_USB 6N137_GAAS_OPTO",
        "",
        "* [C] Stage 0/4 Peltier Condenser/Heater (TEC1-12706, 127=Q_square-1 Bi2Te3 couples),",
        "*     Photosynthetic LEDs (441nm GaN Z=38 + 718nm AlGaAs Z=64) & DS18B20 12-Bit Sensor:",
        "U_PELTIER   VDD_12V   PELT_DRV  TEC1_12706_BI2TE3",
        "D_LED_441NM FPGA_PIN42_PHOTOLED LED_MID_NODE LED_GAN_441NM",
        "D_LED_718NM LED_MID_NODE        GND_PWR      LED_ALGAAS_718NM",
        "U_DS18B20   VDD_3V3   ONEWIRE_DQ GND_PWR     DS18B20_12BIT_THERM_CUTOFF_81C",
        "",
        "* [D] 12 Cuboctahedron O_2(3) Power Channels (IRLZ44N + Rg=544 + 1N5819 + L=100uH + BaTiO3):",
    ]

    for k, fpga_pin in enumerate(PIN_MAP_12BEAM):
        lines.extend([
            f"* --- Channel {k:02d} (Tang Nano 9K LVCMOS33 Pin {fpga_pin}) ---",
            f"R_GATE_{k:02d}  FPGA_PIN{fpga_pin}  GATE_{k:02d}    544_OHM",
            f"Q_MOS_{k:02d}   DRAIN_{k:02d}       GATE_{k:02d}    GND_PWR   IRLZ44N_MOSFET",
            f"L_COIL_{k:02d}  VDD_24V          COIL_MID_{k:02d} 100uH_60TURNS_AIRCORE_MMF42",
            f"R_COIL_{k:02d}  COIL_MID_{k:02d}    DRAIN_{k:02d}   33.1_OHM_0P4MM_CU29",
            f"D_FLY_{k:02d}   DRAIN_{k:02d}       VDD_24V      1N5819_SCHOTTKY_TAU81",
            f"C_X7R_{k:02d}   VDD_24V          GND_PWR      100nF_BATIO3_X7R",
            f"X_PIEZO_{k:02d} DRAIN_{k:02d}       DISH_WALL    BATIO3_52P734KHZ_PDMS40_COUPLED",
        ])

    lines.append("")
    lines.append(".end")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    return len(PIN_MAP_12BEAM)


if __name__ == "__main__":
    net_path = Path(__file__).resolve().parent.parent / "hardware" / "kitchen_bench_power_board.net"
    n_ch = generate_netlist(net_path)
    print(f"Generated {net_path} ({n_ch} power channels, {net_path.stat().st_size} bytes)")
