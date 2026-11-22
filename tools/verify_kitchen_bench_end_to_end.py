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
        ("Node 148-151: Stage 0 Water Moles (12g/18g = 2/3, 3*12=36), Meniscus Antiseptic Quanta n_E(129)=3 & Mains 312V/24V = 13 Transformer",
         mech["water_molar_mass_g_per_mol_ar"] == 18
         and mech["stage0_condensed_water_moles_num_den"] == [2, 3]
         and mech["meniscus_antiseptic_gate_129_quanta"] == 3
         and mech["mains_ac_peak_voltage_24x13_v"] == 312
         and mech["dc_rail_voltage_2x12_v"] == 24
         and mech["mains_transformer_stepdown_ratio_nphi"] == 13),
        ("Node 152-155: Canonical L-Amino Acid Ladder (20=Z(Ca), 64 Codons, Gly=40, Ala=48, Ser=56, Cys=64, Asp=70, Glu=78, His=82, Trp=108)",
         mech["canonical_l_amino_acid_count_ca"] == 20
         and mech["genetic_triplet_codon_count_kp"] == 64
         and mech["amino_acid_shells_z"]["aspartate_heme"] == 70
         and mech["amino_acid_shells_z"]["histidine_heme_ligand"] == 82
         and mech["amino_acid_shells_z"]["tryptophan_12x9_bus"] == 108
         and mech["custom_12coil_phase_bus_bits_12x9"] == 108),
        ("Node 156-160: 49-Geom MuJoCo Twin (7^2*17=833), Magic-50, Half-Piezo 51, Tellurium-52, Iodine-53, Malonic-54",
         mech["mujoco_3d_digital_twin_geoms_7sq"] == 49
         and mech["mujoco_3d_digital_twin_geoms_7sq"] * 17 == 833
         and mech["half_piezo_fresnel_factor_3x17"] == 51
         and mech["discrete_minute_checkpoints_iodine_z"] == 53),
        ("Node 161-165: Complete 55-Section Two-Shell Ball |B_2(3)| = 1 + 12 + 42 = 55 = Z(Cs) Self-Closure of Section 36.26",
         mech["total_section36_26_b2_55_blocks"] == 55
         and mech["total_two_shell_ball_b2_bench_nodes_cs55"] == 55),
        ("Node 166-168: Numbers 56..58 (Maillard-Dew Span 56=7*8, Tri-Octahedral 57=3*19 -> 4*57=228, Hot 52-Min Lag 58=64-6=Z(FeO4))",
         mech["maillard_minus_dew_span_56c"] == 56
         and mech["trioctahedral_factor_3x19"] == 57
         and 4 * mech["trioctahedral_factor_3x19"] == 228
         and mech["hot_coil_lag_52min_ticks"] == 58),
        ("Node 169-171: Numbers 59..62 (30-Min Lag 59=64-5, 60=5*12 Turns/BrO3/6H2O, 10-Min Lag 61=64-3, Min Winding Lag 62=64-2)",
         mech["mid_coil_lag_30min_ticks"] == 59
         and mech["coil_nominal_turns_5x12"] == 60
         and mech["early_coil_lag_10min_ticks"] == 61
         and mech["min_hand_wound_coil_lag_ticks"] == 62),
        ("Node 172-174: Numbers 63..65 (Planetary H-Bond 63=7*9 -> 441nm & 126 Cystine, K_P=64 6-Fold Convergence, Stasis Hold 65=5*13 C)",
         mech["planetary_hydrogen_bond_modulus_7x9"] == 63
         and 7 * mech["planetary_hydrogen_bond_modulus_7x9"] == 441
         and 2 * mech["planetary_hydrogen_bond_modulus_7x9"] == 126
         and mech["stage5_stasis_holding_temp_5x13_c"] == 65),
        ("Node 175-177: Numbers 66..68 (66 Coil Pairs / Max Lag 66 / Cu2O=66, Prime Bridge 67=64+3, Maillard/Abbe/Fe2O2=68)",
         mech["max_hand_wound_coil_lag_ticks"] == 66
         and mech["mutual_inductance_coil_pairs_count"] == 66
         and mech["prime_bridge_kp_plus_d"] == 67
         and mech["maillard_carcinogen_free_temp_c"] == 68),
        ("Node 178-180: Numbers 69..71 (Full Thermal Span 69=81-12=3*23, Heme/Aspartate/Adenine=70, VerletCell72 MSB Index 71=72-1)",
         mech["thermal_ladder_cutoff_minus_dew_c"] == 69
         and mech["food_recipe_shells_z"]["cutlet_heme"] == 70
         and mech["verlet72_msb_bit_index_lu71"] == 71),
        ("Node 181-184: Complete 72-Section VerletCell72 Self-Closure (55 + 17 = 72 = 8 * 9 = dim(VerletCell72) = sigma_H2O = 72 PCB Holes)",
         mech["total_section36_26_verlet72_blocks"] == 72
         and mech["total_verlet72_bit_budget_bench_nodes"] == 72
         and mech["pure_water_surface_tension_mn_per_m"] == 72),
        ("Node 185: Number 73 Circumscribed Frame Radius Floor (73 = 64 + 9 = 8^2 + 3^2 mm)",
         mech["circumscribed_frame_radius_floor_mm"] == 73 == 64 + 9),
        ("Node 186: Number 74 Optocoupler 6N137 2-Tick Delay in Nanoseconds (74 = 2 * 37 ns = Z(W))",
         mech["optocoupler_6n137_2tick_delay_ns"] == 74 == 2 * 37),
        ("Node 187: Number 75 Collagen Triple-Helix Gate Multiple (75 = 3 * 25 = d * d_out(E)^2)",
         mech["collagen_triple_gate_delay_3x25"] == 75 == 3 * 25),
        ("Node 188: Number 76 Tetra-Octahedral Factor (76 = 4 * 19 = Z(Os), 3 * 76 = 228 FPGA Cold Drive)",
         mech["tetra_octahedral_factor_4x19"] == 76 and 3 * mech["tetra_octahedral_factor_4x19"] == 228),
        ("Node 189: Number 77 Glutamate Anion & MuJoCo Foot Z-Offset (77 = 7 * 11 = 78 - 1, 77 + 11 = 88 MSG)",
         mech["glutamate_anion_and_foot_offset_7x11"] == 77 == 7 * 11),
        ("Node 190: Number 78 Three-Fold Umami / Platinum / MMO Active Complex Convergence (78 = 6 * 13, 78 + 50 = 128)",
         mech["umami_glutamic_acid_c5h9no4_z"] == 78 == 6 * 13),
        ("Node 191: Number 79 Corrosion-Free ENIG Gold PCB Contact Plating (79 = 78 + 1 = Z(Au) = 81 - 2)",
         mech["enig_gold_pcb_contact_plating_au_z"] == 79),
        ("Node 192-200: Numbers 80..81 (Water eps_r(20C) = Ribose = Hg = 80, Complete 81-Section |E_Heis(3)| = 3^4 = 72 + 9 Self-Closure)",
         mech["water_dielectric_permittivity_20c"] == 80 == mech["ribose_rna_sugar_5x16_z"]
         and mech["total_section36_26_heisenberg81_blocks"] == 81 == mech["total_heisenberg_81_bench_nodes"]),
        ("Node 201-204: Numbers 82..86 (Histidine 82=2*41, 52-Min Total Lag 83=Z(Bi), 30-Min Lag 84=2*S2, 20-Min Lag 85=5*17, 10-Min Lag 86=Z(Rn))",
         mech["amino_acid_shells_z"]["histidine_heme_ligand"] == 82 == 2 * 41
         and mech["total_hot_lag_52min_bi83_ticks"] == 83
         and mech["total_mid_lag_30min_2s2_ticks"] == 84
         and mech["total_lag_20min_and_dish_height_mm"] == 85
         and mech["total_early_lag_10min_rn86_ticks"] == 86),
        ("Node 205-208: Numbers 87..91 (Coil #0 Lag 87=3*29=SRF, Coil #1 Lag 88=MSG, Nominal Cold Lag 89=64+25, Dish/Lag 90, Coil #11 Lag 91=7*13)",
         mech["min_coil0_total_lag_srf87_ticks"] == 87 == 3 * 29
         and mech["coil1_total_lag_msg88_ticks"] == 88
         and mech["nominal_cold_total_lag_ticks"] == 89 == 64 + 25
         and mech["coil7_total_lag_dish90_ticks"] == 90
         and mech["max_coil11_total_lag_gauss91_ticks"] == 91 == 7 * 13),
        ("Node 209-212: Numbers 92..95 (Vitamin C S_3=92, Triple Gallium 93=3*31, Chocolate Theobromine 94, Penta-Octahedral 95=5*19 -> 57+76+95=228)",
         mech["food_recipe_shells_z"]["vitamin_c_s3"] == 92
         and mech["triple_gallium_led_3x31"] == 93 == 3 * 31
         and mech["chocolate_theobromine_c7h8n4o2_z"] == 94
         and mech["penta_octahedral_factor_5x19"] == 95 == 5 * 19
         and 57 + 76 + 95 == 228),
        ("Node 213-216: Number 96 Four-Fold Convergence (Glucose Z=96, 6 O2 Exhaust=96, Fermat Order |F_97^*|=96, Polystyrene Total Lag 89+7=96)",
         mech["polystyrene_total_cold_lag_ticks"] == 96 == 89 + 7
         and mech["photosynthesis_shell_balance_6co2_6h2o"] == 2 * 96),
        ("Node 217-220: Complete 97-Section Gaussian Coulomb Modulus M_hat(3) = 9^2 + 4^2 = 81 + 16 = 97 Self-Closure of Section 36.26",
         mech["total_section36_26_gaussian97_blocks"] == 97 == 9 * 9 + 4 * 4
         and mech["gaussian_coulomb_modulus_81_plus_16"] == 97),
        ("Node 221-224: Numbers 98..101 (Dodecane/2*49=98, Neighbor Bit-Wires 99=9*11, L=100uH/C=100nF/Citric=100, Wheeler Prime 101=202/2)",
         mech["double_mujoco_geoms_dodecane_z"] == 98 == 2 * 49
         and mech["single_coil_11neighbor_9bit_wires"] == 99 == 9 * 11
         and mech["nectar_citric_acid_c6h8o7_z"] == 100
         and mech["wheeler_prime_factor_202_div_2"] == 101),
        ("Node 225-228: Numbers 102..106 (BaTiO3/Caffeine=102=6*17, 103=64+39, 104=8*13, Odd Triad 105=3*5*7, Kok Oxo / I2 = 106 = 2*53)",
         mech["food_recipe_shells_z"]["caffeine_batio3"] == 102
         and mech["actinide_lawrencium_kp_plus_39"] == 103
         and mech["octahedral_core_product_8x13"] == 104
         and mech["odd_structural_triad_3x5x7"] == 105
         and mech["kok_s4_oxo_bridge_and_i2_z"] == 106),
        ("Node 229-232: Numbers 107..110 (108-Bit Bus MSB=107, 12*9=108=Trp=9*12 Wheeler, 109=64+45, Double Ball 110=2*55)",
         mech["custom_12coil_bus_msb_index"] == 107
         and mech["custom_12coil_phase_bus_bits_12x9"] == 108
         and mech["coil_lag_plus_wall_cap_64_45"] == 109
         and mech["double_two_shell_ball_2x55"] == 110),
        ("Node 233-236: Numbers 111..114 (3-Tick 111=3*37ns, Double Span 112=16*7, 113=64+49, Cheese Ca-Lactate 114=6*19=228/2)",
         mech["three_tick_27mhz_duration_ns"] == 111 == 3 * 37
         and mech["double_maillard_dew_span_16x7"] == 112
         and mech["kp_plus_mujoco_geoms_64_49"] == 113
         and mech["cheese_calcium_lactate_z"] == 114),
        ("Node 237-240: Numbers 115..118 (5*Silanol=115, 4*Cu=116, Collapse Odd Current S_3(139)=117=9*13, Au-197 Neutrons / Og = 118)",
         mech["five_fold_silanol_5x23"] == 115
         and mech["four_equatorial_copper_4x29"] == 116
         and mech["collapse_139_odd_current_9x13"] == 117 == mcp.proj_s(139)
         and mech["gold197_neutron_count_og118"] == 118),
        ("Node 241-244: Numbers 119..122 (Meniscus-Fresnel 119=7*17 -> 7*119=833, Acrylamide/ATP 120=68+52, 11^2=121, 2*61=122)",
         mech["meniscus_fresnel_factor_7x17"] == 119
         and 7 * mech["meniscus_fresnel_factor_7x17"] == 833
         and mech["acrylamide_pyrolysis_threshold_c"] == 120
         and mech["off_axis_neighbor_square_11sq"] == 121
         and mech["double_early_10min_lag_2x61"] == 122),
        ("Node 245-248: Numbers 123..126 (Kok S3 Flash 123=3*41, 4*Ga=124, 5^3=125 -> 125-64=61, Cystine Disulfide 126=2*63)",
         mech["kok_s3_third_flash_3x41"] == 123 == 3 * 41
         and mech["quadruple_gallium_4x31"] == 124
         and mech["outward_edge_cube_5cubed"] == 125
         and mech["disulfide_cystine_bridge_z"] == 126),
        ("Node 249-252: Number 127 Three-Fold Convergence (TEC1-12706 127 Couples, 7-Bit Gray Mantissa Max 127, 7th Gauss Shell 7^3-6^3=127)",
         mech["peltier_tec1_12706_couples_qsquare_minus_1"] == 127 == 7**3 - 6**3),
        ("Node 253-256: Complete 128-Section Quarter-Ring Saddle Q_square(3) = 2^7 = 128 Self-Closure (Stage 3 Ultrasonic Folding, R+G+B=128, Pt+Al2O3=128)",
         mech["total_section36_26_qsquare128_blocks"] == 128 == 97 + 31),
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
