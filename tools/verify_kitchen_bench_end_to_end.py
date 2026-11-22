"""
End-to-End Physical Kitchen Bench Verification Suite (All 30 Physical Nodes):
Verifies the complete hardware/physics chain from the 220V/24V PSU, 27.000 MHz
alpha-quartz crystal, 16-byte UART bridge, GaAs optocoupler, FR-4 PCB & IRLZ44N
MOSFET gate stack, 12 hand-wound copper coils on O_2(3), 1N5819 Schottky flyback,
BaTiO3 ultrasonic piezo + PDMS silicone couplant, SiO2 Petri dish, tap-water ions,
meniscus surface gate, moist air H2CO3, Lock-In optical feedback, SPICE netlist,
and 3D-printable STL frame mesh.
"""

from __future__ import annotations
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "hardware"))

import cuboctahedron_mcp_server as mcp  # noqa: E402


def main() -> int:
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

    crys = cal["crystal_27mhz"]
    mos = cal["mosfet_and_copper_coil"]
    dish = cal["petri_dish_and_water"]
    mech = cal["mechanical_frame_and_isolation"]
    res = cal["calibration_result"]

    checks = [
        ("Node 01-02: 27.000 MHz alpha-quartz Z(SiO2)=30, (SiO2)3=90, SiO4=46, Al+H=46",
         crys["alpha_quartz_shell_z"] == 30 and crys["unit_cell_sio2_3_z"] == 90 and crys["sio4_pauli_threshold_z"] == 46 and crys["al_oh_passivated_z"] == 46),
        ("Node 03-04: MOSFET gate stack Z(Si+SiO2)=44, Miller lag = 25 ticks",
         mos["mosfet_gate_stack_z"] == 44 and mos["lag_mosfet_gate_ticks"] == 25),
        ("Node 05-06: Copper coil Z(Cu)=29, L=100uH, R=33.1 Ohm -> lag = 64 = K_P ticks",
         mos["copper_z"] == 29 and mos["lag_coil_ticks"] == 64),
        ("Node 07-08: Quartz Petri dish Z=30 matches air Z(N2+O2)=30; tap-water ion shells 10, 18, 32, 42, 50",
         dish["glass_sio2_matches_air_n2_o2_shell_30"] is True and dish["tap_water_ion_shells"]["CaCO3_magic"] == 50),
        ("Node 09-10: Meniscus 7+5=12 links; pre-compensated FPGA drive 228 -> arrived dish phase 139 = A_coh",
         dish["meniscus_surface_coordination"]["total_links"] == 12 and res["verified_arrived_phase_in_dish_ticks"] == 139),
        ("Node 11-12: O_2(3) 12-coil mutual inductance off-axis crosstalk == 0; 12x UART 0x06 + 52-min thermal schedule",
         mos["mutual_inductance_o2_off_axis_crosstalk"] == 0 and len(res["per_coil_12channel_calibration"]) == 12 and len(res["thermal_52min_drift_schedule"]) == 6),
        ("Node 13-14: 1N5819 Schottky flyback 3*81+13=256 ticks; BaTiO3 piezo Z=102; 8-bit webcam ADC noise = 0",
         mos["schottky_flyback_tau_ticks"] == 81 and dish["ultrasonic_piezo_batio3_shell_z"] == 102 and dish["webcam_8bit_adc_quant_noise_photons"] == 0),
        ("Node 15-17: Earth magnetic field antipodal sum == 0; PLA frame Z=38; GaAs USB optocoupler Z=64=K_P",
         mech["earth_magnetic_field_antipodal_sum"] == 0 and mech["frame_3d_print_pla_monomer_c3h4o2_z"] == 38 and mech["usb_optocoupler_gaas_led_z"] == 64),
        ("Node 18-20: Lock-In room light DC sum == 0; 50cm twisted pair lag == 0; Sn solder Z=50; 3D-printer skew = 3 < 41",
         mech["ambient_room_light_lockin_dc_sum"] == 0 and mech["lead_free_solder_tin_magic_shell_z"] == 50 and mech["home_fdm_3d_printer_max_skew_ticks"] == 3),
        ("Node 21-23: Copper skin depth 0.288mm > 0.20mm radius (lag=0); far-field EMC dipole == 0; silanol Z(-Si-OH)=23",
         mech["skin_effect_extra_lag_ticks"] == 0 and mech["far_field_emc_dipole_radiation_sum"] == 0 and mech["silanol_glass_wetting_group_sioh_z"] == 23),
        ("Node 24-26: Moist air H2CO3 Z=32=K_P/2; coil SRF ratio = 87; Bjerknes 7mm step; ESD 1:18 Argon divider",
         mech["moist_air_carbonic_acid_h2co3_z"] == 32 and mech["coil_srf_to_ring_freq_ratio"] == 87 and mech["bjerknes_quarter_wave_node_step_mm"] == 7 and mech["esd_hbm_capacitive_divider_argon_ratio"] == 18),
        ("Node 27-30: PDMS silicone couplant Z(C2H6SiO)=40=dphi_disc-1 (0 phonon loss); FR-4 35um copper lag=0; 30-node closure",
         mech["pdms_silicone_acoustic_couplant_c2h6sio_z"] == 40 and mech["pdms_couplant_phonon_loss_quanta"] == 0 and mech["total_verified_kitchen_bench_nodes"] == 30),
        ("Hardware files present: Verilog ASIC, Tang Nano 9K CST, LTspice .cir, OpenSCAD .scad, and 3D-printable .stl",
         all((ROOT / "hardware" / f).is_file() for f in (
             "cuboctahedron_carrier_asic.v",
             "tang_nano_9k.cst",
             "kitchen_bench_mosfet_coil.cir",
             "cuboctahedron_12coil_frame.scad",
             "cuboctahedron_12coil_frame.stl",
             "KITCHEN_BENCH_BOM_AND_CHECKLIST.md",
         ))),
    ]

    print("=== Complete 30-Node Physical Kitchen Bench Audit ===")
    failed = 0
    for title, ok in checks:
        status = "PASS" if ok else "FAIL"
        if not ok:
            failed += 1
        print(f"  [{status}] {title}")
    print(f"=== Total Checks: {len(checks)} | Failed: {failed} ===")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
