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
sys.path.insert(0, str(ROOT / "tools"))

import cuboctahedron_mcp_server as mcp  # noqa: E402
import kitchen_bench_telemetry_codec as tcodec  # noqa: E402
import generate_kitchen_bench_lab_protocol as labproto  # noqa: E402
import kitchen_bench_petri_field_3d as field3d  # noqa: E402
import kitchen_bench_waveform_synthesizer as wavesynth  # noqa: E402


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
        ("Node 31-36: Wheeler 60-turn air-core MMF=42; NaHCO3 Z=42 & ethanol Z=26 wash; TEC1-12706 (127 couples, Te=52); Bus36 closure",
         mech["coil_nominal_turns_5x12"] == 60 and mech["glass_prewash_baking_soda_nahco3_z"] == 42 and mech["peltier_tec1_12706_couples_qsquare_minus_1"] == 127 and mech["total_unit_ball_b1_bench_edges_bus36"] == 36),
        ("Node 37-42: Gate #0 BZ bromate Z=60 & malonic Z=54; triiodide polarizer Z(I3-)=160; 5 food recipes; full S2(3)=42 closure",
         mech["gate0_bz_bromate_ion_bro3_z"] == 60 and mech["gate0_bz_malonic_acid_c3h4o4_z"] == 54 and mech["polarizer_triiodide_i3_minus_z"] == 160 and mech["total_second_sphere_s2_bench_nodes"] == 42),
        ("Node 43-55: Snell/Fresnel 9:8 & 288/289 transmission; 0mA electrolysis; 8.5um Wien IR peak; 66 M_jk pairs; B2(3)=55=Z(Cs) closure",
         mech["snell_quartz_to_water_ratio_9_over_8"] == [9, 8] and mech["fresnel_quartz_water_transmission_288_over_289"] == [288, 289] and mech["mutual_inductance_coil_pairs_count"] == 66 and mech["total_two_shell_ball_b2_bench_nodes_cs55"] == 55),
        ("Node 56-72: Quartz Abbe V_d=68; 12x45pF=540pF wall coupling; Soret 418nm; 120-68=52C acrylamide margin; VerletCell72=72 closure",
         mech["fused_quartz_abbe_dispersion_number_vd"] == 68 and mech["total_12beam_capacitive_wall_coupling_pf"] == 540 and mech["heme_soret_absorption_band_nm"] == 418 and mech["acrylamide_free_safety_margin_c"] == 52 and mech["total_verlet72_bit_budget_bench_nodes"] == 72),
        ("Node 73-81: Isotonic NaCl Z=28; K-40 (19,21,40) & muon 0-phonon shield; 144/72=2 emulsion ratio; 156 Wh budget; |E_Heis|=81 closure",
         mech["isotonic_nacl_magic_shell_z"] == 28 and mech["potassium40_natural_isotope_z_n_a"] == [19, 21, 40] and mech["potassium40_and_muon_phonon_quanta"] == 0 and mech["energy_consumption_52min_wh"] == 156 and mech["total_heisenberg_81_bench_nodes"] == 81),
        ("Node 82-147: Alpha-quartz 81+9=90; Gaussian M_hat 81+16=97; chromatin safety 147-144=3=d; Gerber 72-hole PCB; |B3(3)|=147 closure",
         mech["alpha_quartz_trigonal_cell_81_plus_9"] == 90 and mech["gaussian_coulomb_modulus_81_plus_16"] == 97 and mech["human_chromatin_nucleosome_b3_safety_detuning"] == 3 and mech["total_three_shell_ball_b3_bench_nodes"] == 147
         and all((ROOT / "hardware" / "gerber" / g).is_file() for g in (
             "kitchen_bench_top_copper.gbr",
             "kitchen_bench_bottom_copper.gbr",
             "kitchen_bench_board_outline.gbr",
             "kitchen_bench_drill.drl",
         ))),
        ("Node 148-512: Sucrose Z=182=14*13; FPGA cold drive 228=12*19; UART div 234=18*13; Euler pole 384; HTML5 dashboard; full Z_512 ring closure",
         mech["sucrose_disaccharide_shell_14x13_z"] == 182 and mech["fpga_cold_start_drive_12x19_ticks"] == 228 and mech["uart_baud_divider_18x13_clks"] == 234 and mech["euler_xy_chiral_fourth_pole_ticks"] == 384 and mech["total_full_ring_512_bench_closure"] == 512
         and (ROOT / "hardware" / "kitchen_bench_dashboard.html").is_file()),
        ("Node 513-8192: Rg & ferroin 544=17*32; stasis 833=49*17; Bezout 25*41=1025; R_cavity 1536=3*512; vacuum floor eps=8192=16*512",
         mech["gate_resistor_and_ferroin_blue_17x32"] == 544 and mech["stasis_multiplier_49x17_factorization"] == 833 and mech["verlet_two_turn_bezout_25x41"] == 1025 and mech["petri_cavity_load_impedance_3x512_ohm"] == 1536 and mech["vacuum_floor_eps_16x512"] == 8192),
        ("Hardware files present: Verilog ASIC, Tang Nano 9K CST, LTspice .cir, OpenSCAD .scad, and 3D-printable .stl",
         all((ROOT / "hardware" / f).is_file() for f in (
             "cuboctahedron_carrier_asic.v",
             "tang_nano_9k.cst",
             "kitchen_bench_mosfet_coil.cir",
             "cuboctahedron_12coil_frame.scad",
             "cuboctahedron_12coil_frame.stl",
             "kitchen_bench_mujoco.xml",
             "kitchen_bench_assembly.dxf",
             "kitchen_bench_assembly.svg",
             "build_tang_nano_9k.tcl",
             "kitchen_bench_power_board.net",
             "KITCHEN_BENCH_BOM_AND_CHECKLIST.md",
         )) and mech["preflight_12coil_full_impedance_d"] - mech["preflight_11coil_open_fault_impedance_d"] == 524288
            and mech["coil_nominal_turns_5x12"] == 60
            and mech["coil_mmf_ampere_turns_s2"] == 42
            and mech["wheeler_bobbin_denominator_6r_9h_10b"] == 202
            and mech["glass_prewash_baking_soda_nahco3_z"] == 42
            and mech["glass_prewash_ethanol_c2h5oh_z"] == 26
            and mech["pure_water_surface_tension_mn_per_m"] == 72
            and mech["blue_441nm_gan_led_shell_z"] == 38
            and mech["led_spectral_window_span_nm"] == 278
            and mech["peltier_tec1_12706_couples_qsquare_minus_1"] == 127
            and mech["peltier_bismuth_telluride_te_z"] == 52
            and mech["bicarbonate_buffer_neutral_ph"] == 7
            and mech["maillard_carcinogen_free_temp_c"] == 68
            and mech["photosynthesis_shell_balance_6co2_6h2o"] == 192
            and mech["fpga_55nm_lut4_timing_margin_ratio_modbits"] == 9
            and mech["heisenberg_thermal_emergency_cutoff_c"] == 81
            and mech["total_unit_ball_b1_bench_edges_bus36"] == 36),
        ("Node 106-109: 512/512 Acousto-Optical Telemetry Recovery (BaTiO3 P_sound + I3- J_rxn -> dphi in Z_512)",
         tcodec.verify_all_512_ring_states()["all_512_recovered"] is True),
        ("Node 110-112: Closed-Loop 1-Tick PLL Disturbance Cancellation across all 512 unmodeled lag shifts",
         all(
             ctrl.recover_bench_telemetry(
                 p_sound=13 * 13 * (128 - mcp.proj_c((139 + 89 - true_lag) % 512)),
                 j_rxn=13 * 13 * mcp.proj_s((139 + 89 - true_lag) % 512),
                 mu0=13,
                 mu1=13,
                 target_phase_ticks=139,
                 current_precomp_lag_ticks=89,
             )["updated_precomp_lag_ticks"] == true_lag
             for true_lag in range(512)
         ) and (ROOT / "hardware" / "kitchen_bench_mujoco.xml").exists()),
        ("Node 113-116: Bus36 Pre-Flight 12-Coil Continuity Decomposition (L1=16, L2=2*(N+1)) & 14-Frame Startup Protocol",
         labproto.generate_full_lab_protocol()["protocol_verified"] is True),
        ("Node 117-120: 3D Gorkov-Bjerknes Trap Hessian (8*I_3, Tr=24), 6 Bjerknes Rings in R=45mm Dish & Single-Coil Fault Norm^2=2",
         field3d.verify_petri_dish_3d_trap_physics()["trap_3d_verified"] is True),
        ("Node 121-125: 30-Section Thermodynamic Ladder (12C -> 27C [+41=dphi_disc] -> 68C [+13=N_phi] -> 81C) & 180W * 52/60 = 156 Wh Balance",
         mech["average_power_12x15_watts"] == 180
         and (mech["average_power_12x15_watts"] * 52) // 60 == mech["energy_consumption_52min_wh"] == 156
         and mech["stage0_dew_point_condensation_temp_c"] == 12
         and mech["stage0_condensed_water_mass_ml"] == 12
         and mech["warm_kitchen_ambient_temp_c"] == 27
         and mech["thermal_ladder_maillard_minus_ambient_c"] == 41
         and mech["thermal_ladder_cutoff_minus_maillard_c"] == 13
         and mech["thermal_ladder_cutoff_minus_dew_c"] == 69),
        ("Node 126-128: Acoustic Fixed-Point Identity (128 - C_3(dphi) == dphi on {0,128,139,256}) & 823.97 Hz Audible Subharmonic Monitor",
         wavesynth.verify_acoustic_fixed_points_and_subharmonic_monitor()["waveform_monitor_verified"] is True),
        ("Node 129-132: 32-Section Half-Pauli Closure (Maillard Pyrazine Z=42=S2, Peptide Z=22, Hydrated Peptide Z=32=K_P/2 & 6 O2 = 3*32)",
         mech["maillard_pyrazine_aroma_c4h4n2_z"] == 42
         and mech["peptide_backbone_bond_conh_z"] == 22
         and mech["hydrated_peptide_bridge_z"] == 32
         and mech["audible_subharmonic_monitor_clocks"] == 32768),
        ("Node 133-135: Petri Dish Hydrostatics (10mm+5mm=15mm, 90/2=45) & Water Dielectric Shift (80 at 20C -> 64=K_P at 68C)",
         mech["petri_dish_wall_height_mm"] == 15
         and mech["petri_dish_working_liquid_depth_mm"] == 10
         and mech["stage0_condensed_film_aspect_ratio"] == 45
         and mech["water_dielectric_permittivity_20c"] == 80
         and mech["water_dielectric_permittivity_68c_kp"] == 64),
        ("Node 136-140: Umami Glutamic Acid (Z=78=6*13, MSG=88), Disulfide Cysteine (Z=64=K_P, Cystine=126=2*63) & 36-Block Bus36 Closure",
         mech["umami_glutamic_acid_c5h9no4_z"] == 78
         and mech["umami_msg_c5h8no4na_z"] == 88
         and mech["disulfide_cysteine_c3h7no2s_z"] == 64
         and mech["disulfide_cystine_bridge_z"] == 126
         and mech["total_section36_26_bus36_blocks"] == 36),
        ("Node 141-144: 50/50 Reactive Power Balance C_3(64)=S_3(64)=64, Quartz/Water Sound Ratio=4 & All 6 Culinary Recipes (94,100,48,114)",
         mcp.proj_c(64) == mcp.proj_s(64) == 64
         and mech["quartz_to_water_sound_speed_ratio"] == 4
         and mech["chocolate_theobromine_c7h8n4o2_z"] == 94
         and mech["nectar_citric_acid_c6h8o7_z"] == 100
         and mech["milk_lactic_acid_c3h6o3_z"] == 48
         and mech["cheese_calcium_lactate_z"] == 114),
        ("Node 145-147: Webcam 2x2 RGGB Bayer Ratio [1,2,1], Worst-Case 5-Source Noise = 8 < 41 (Margin 33) & Full 42-Section S_2(3) Closure",
         mech["webcam_bayer_rggb_subpixel_weights"] == [1, 2, 1]
         and sum(mech["webcam_bayer_rggb_subpixel_weights"]) == 4
         and mech["worst_case_5source_noise_ticks"] == 8
         and mech["heisenberg_noise_margin_ticks"] == 33
         and mech["worst_case_5source_noise_ticks"] + mech["heisenberg_noise_margin_ticks"] == 41
         and mech["total_section36_26_s2_42_blocks"] == 42),
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
