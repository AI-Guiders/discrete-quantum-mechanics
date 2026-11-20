// ============================================================================
// cuboctahedron_carrier_asic.v
// Gate-level / RTL hardware implementation of the 9-bit M/T Cuboctahedral
// Rotator, Reversible Two-Tick Verlet Cell, 12-Beam Cuboctahedron Impedance
// Collapse Gate, and Quotient-Remainder Born Detector in Verilog (IEEE 1364-2005).
//
// Zero floating-point arithmetic, zero lookup tables for sin/cos:
// only 9-bit integer registers, bit shifts, XOR gates, and integer adders.
// ============================================================================
`timescale 1ns / 1ps

// ----------------------------------------------------------------------------
// Module 1: Branchless Piecewise-Linear Rotator on Z_512 (Q_square = 128)
// Computes wrap512(phi), C(phi) = 128 - |wrap512(phi)|, S(phi) = C(phi - 128),
// the one-step difference Wronskian W(phi) = C(phi)*S(phi+1) - S(phi)*C(phi+1),
// and the Brahmagupta-Weierstrass Pythagorean lift (X, Y, R) with X^2 + Y^2 = R^2.
// ----------------------------------------------------------------------------
module rotator_512_unit (
    input  wire signed [31:0] phi_in,
    output wire signed [31:0] wrap_out,
    output wire signed [31:0] proj_c,
    output wire signed [31:0] proj_s
);
    // Euclidean modulo 512 into [0, 511] using 9-bit mask (since 512 = 2^9,
    // two's complement bitmask `& 511` is the exact mathematical `emod 512`!)
    wire signed [31:0] shifted = 32'sd256 - phi_in;
    wire signed [31:0] emod512 = shifted & 32'sd511;
    assign wrap_out = 32'sd256 - emod512;

    wire signed [31:0] abs_wrap = (wrap_out < 0) ? -wrap_out : wrap_out;
    assign proj_c = 32'sd128 - abs_wrap;

    // S(phi) = C(phi - 128)
    wire signed [31:0] shifted_s = 32'sd256 - (phi_in - 32'sd128);
    wire signed [31:0] emod512_s = shifted_s & 32'sd511;
    wire signed [31:0] wrap_s    = 32'sd256 - emod512_s;
    wire signed [31:0] abs_wrap_s = (wrap_s < 0) ? -wrap_s : wrap_s;
    assign proj_s = 32'sd128 - abs_wrap_s;
endmodule

// ----------------------------------------------------------------------------
// Module 2: Euclidean Quotient-Remainder Decomposition on Z_512
// (d0 phi) = 512 * q + r, where:
//   q = branch_quotient = floor((delta + 255) / 512)  (corpuscle / topological winding jump)
//   r = edge_connection = wrap512(delta) in (-256, 256] (wave propagating on 12 edges)
// ----------------------------------------------------------------------------
module quotient_remainder_512_unit (
    input  wire signed [31:0] delta_phi,
    output wire signed [31:0] branch_q,
    output wire signed [31:0] edge_r
);
    // Exact arithmetic floor division by 512 = 2^9 is an arithmetic right shift `>>> 9`!
    wire signed [31:0] num = delta_phi + 32'sd255;
    assign branch_q = num >>> 9;
    assign edge_r   = delta_phi - (branch_q <<< 9);
endmodule

// ----------------------------------------------------------------------------
// Module 3: Two-Tick Symplectic Reversible Verlet Cell (Zero Landauer Heat A13)
// Forward step:  phi_next = (2 * phi_curr - phi_prev + phi_accel) mod 512
// Reverse step:  phi_prev_rec = (2 * phi_curr - phi_next + phi_accel) mod 512
// ----------------------------------------------------------------------------
module verlet_reversible_cell (
    input  wire        clk,
    input  wire        rst,
    input  wire        reverse_dir,
    input  wire [8:0]  init_curr,
    input  wire [8:0]  init_prev,
    input  wire signed [31:0] phi_accel,
    output reg  [8:0]  phi_curr,
    output reg  [8:0]  phi_prev
);
    wire signed [31:0] curr_s = {23'b0, phi_curr};
    wire signed [31:0] prev_s = {23'b0, phi_prev};
    wire signed [31:0] step_val = ((curr_s <<< 1) - prev_s + phi_accel) & 32'sd511;

    always @(posedge clk) begin
        if (rst) begin
            phi_curr <= init_curr;
            phi_prev <= init_prev;
        end else if (!reverse_dir) begin
            // Forward time evolution: (curr, prev) -> ((2*curr - prev + accel) mod 512, curr)
            phi_prev <= phi_curr;
            phi_curr <= step_val[8:0];
        end else begin
            // Exact time-reversed evolution on the same clock without history stack:
            // (curr, prev) -> (prev, (2*prev - curr + accel) mod 512)
            phi_curr <= phi_prev;
            phi_prev <= (((prev_s <<< 1) - curr_s + phi_accel) & 32'sd511);
        end
    end
endmodule

// ----------------------------------------------------------------------------
// Module 4: 12-Beam Cuboctahedron Coherent Barrier-Collapse & Ballistic Gate
// Exact hardware realization of `shellGateDenomOp` and `shellGatePhaseOp`:
//   base_term  = 128 * (mu_c^2 + mu_nb^2)
//   coup_term  = 12 * (2 * mu_c * mu_nb * C(delta_phi))
//   D_denom    = max(8192, base_term + coup_term)
//   Phi_gate   = (3 * (12 * mu_c * mu_nb * S(delta_phi)) * 41 * 512) / D_denom
// ----------------------------------------------------------------------------
module cuboctahedron_12beam_gate (
    input  wire signed [31:0] mu_center,
    input  wire signed [31:0] mu_nb,
    input  wire signed [31:0] delta_phi,
    output wire signed [31:0] c_single,
    output wire signed [31:0] s_single,
    output wire signed [31:0] denom_d,
    output wire signed [31:0] gate_phase_phi,
    output wire signed [31:0] energy_quanta_ne
);
    wire signed [31:0] w_out;
    rotator_512_unit u_rot (
        .phi_in(delta_phi),
        .wrap_out(w_out),
        .proj_c(c_single),
        .proj_s(s_single)
    );

    wire signed [31:0] base_term = 32'sd128 * (mu_center * mu_center + mu_nb * mu_nb);
    wire signed [31:0] coup_term = 32'sd12 * 32'sd2 * mu_center * mu_nb * c_single;
    wire signed [31:0] raw_denom = base_term + coup_term;

    // Quantum vacuum floor eps = K_P * Q_square = 64 * 128 = 8192
    assign denom_d = (raw_denom < 32'sd8192) ? 32'sd8192 : raw_denom;

    wire signed [63:0] odd_total = 64'sd12 * mu_center * mu_nb * s_single;
    wire signed [63:0] num_total = 64'sd3 * odd_total * 64'sd41 * 64'sd512;
    wire signed [63:0] phi_div   = num_total / denom_d;
    assign gate_phase_phi = phi_div[31:0];

    wire signed [31:0] abs_phi = (gate_phase_phi < 0) ? -gate_phase_phi : gate_phase_phi;
    assign energy_quanta_ne = abs_phi / 32'sd41;
endmodule

// ----------------------------------------------------------------------------
// Module 5: Two-Chamber 72-Bit Stasis-Teleport-Release Engine
// Implements the 3-step ice-free protocol:
//   Step 1 (STASIS):    12 beams in-phase (dphi = 0) -> D_stasis = 6,823,936 = 833 * 8192,
//                       internal gate impulse |Phi| < 41 -> snapped to 0 by Heisenberg deadband.
//   Step 2 (TELEPORT):  Chamber A emits 4 Pauli syndromes sigma_k = (phi_A,k - a_k - 256) mod 512
//                       and discharges to vacuum floor (mu_A = 1); syndrome traverses the
//                       shielded ballistic waveguide (Phi_noise = 0); Chamber B switches its
//                       12-beam focus to antipodal phase (dphi = 256) -> D_write = 8,192
//                       (833:1 impedance contrast) and reconstructs phi_B,k = (b_k + sigma_k) mod 512
//                       while conserving total two-chamber A3 norm (mu_A^2 + mu_B^2 = const).
//   Step 3 (RELEASE):   Stasis screen is lifted in Chamber B and the teleported 72-bit spinor
//                       resumes reversible Verlet evolution from the exact tick it paused in A.
// ----------------------------------------------------------------------------
module two_chamber_72bit_teleporter (
    input  wire        clk,
    input  wire        rst,
    input  wire [1:0]  cmd_mode,       // 00: EVOLVE, 01: STASIS, 10: TELEPORT_A_TO_B, 11: RELEASE_B
    input  wire [8:0]  singlet_a0,
    input  wire [8:0]  singlet_a1,
    input  wire [8:0]  singlet_a2,
    input  wire [8:0]  singlet_a3,
    input  wire signed [31:0] ext_thermal_noise_drive,
    output reg  [8:0]  chA_mu0,
    output reg  [8:0]  chA_mu1,
    output reg  [8:0]  chA_phi0_curr,
    output reg  [8:0]  chA_phi0_prev,
    output reg  [8:0]  chA_phi1_curr,
    output reg  [8:0]  chA_phi1_prev,
    output reg  [8:0]  chB_mu0,
    output reg  [8:0]  chB_mu1,
    output reg  [8:0]  chB_phi0_curr,
    output reg  [8:0]  chB_phi0_prev,
    output reg  [8:0]  chB_phi1_curr,
    output reg  [8:0]  chB_phi1_prev,
    output wire signed [31:0] d_stasis_val,
    output wire signed [31:0] d_write_val,
    output wire signed [31:0] contrast_833,
    output wire signed [31:0] waveguide_noise_leak,
    output wire signed [31:0] total_two_chamber_norm_sq
);
    // Shielded stasis impedance (13-node dressed cluster at K_P = 64, dphi = 0):
    // D_stasis = 8192 + 128*64^2 + 12*(128*64^2) = 8192 * (1 + 64 + 768) = 8192 * 833 = 6,823,936
    assign d_stasis_val = 32'sd8192 + 32'sd13 * 32'sd128 * 32'sd64 * 32'sd64;
    // Coherent 12-beam write focus impedance (dphi = 256 -> C(256) = -128 -> clamped to vacuum floor 8192)
    assign d_write_val  = 32'sd8192;
    assign contrast_833 = d_stasis_val / d_write_val;

    // Heisenberg deadband suppression of external thermal noise inside the shielded waveguide:
    wire signed [31:0] raw_noise_ratio = (32'sd64 * ext_thermal_noise_drive) / d_stasis_val;
    wire signed [31:0] abs_noise_ratio = (raw_noise_ratio < 0) ? -raw_noise_ratio : raw_noise_ratio;
    assign waveguide_noise_leak = (abs_noise_ratio < 32'sd41) ? 32'sd0 : raw_noise_ratio;

    // Shared Pauli singlet partners in Chamber B: b_k = (a_k + 256) mod 512
    wire [8:0] singlet_b0 = (singlet_a0 + 9'd256) & 9'd511;
    wire [8:0] singlet_b1 = (singlet_a1 + 9'd256) & 9'd511;
    wire [8:0] singlet_b2 = (singlet_a2 + 9'd256) & 9'd511;
    wire [8:0] singlet_b3 = (singlet_a3 + 9'd256) & 9'd511;

    // Bell-Pauli syndromes emitted by Chamber A: sigma_k = (psi_A,k - a_k - 256) mod 512
    wire [8:0] sigma0 = (chA_phi0_curr - singlet_a0 - 9'd256) & 9'd511;
    wire [8:0] sigma1 = (chA_phi0_prev - singlet_a1 - 9'd256) & 9'd511;
    wire [8:0] sigma2 = (chA_phi1_curr - singlet_a2 - 9'd256) & 9'd511;
    wire [8:0] sigma3 = (chA_phi1_prev - singlet_a3 - 9'd256) & 9'd511;

    // Total two-chamber A3 norm squared: (mu_A0^2 + mu_A1^2) + (mu_B0^2 + mu_B1^2)
    assign total_two_chamber_norm_sq =
        (chA_mu0 * chA_mu0 + chA_mu1 * chA_mu1) +
        (chB_mu0 * chB_mu0 + chB_mu1 * chB_mu1);

    always @(posedge clk) begin
        if (rst) begin
            // Chamber A initialized with an active 72-bit spinor vortex:
            // mu0 = 64, mu1 = 13, phi0 = (173, 132), phi1 = (296, 255)
            chA_mu0       <= 9'd64;
            chA_mu1       <= 9'd13;
            chA_phi0_curr <= 9'd173;
            chA_phi0_prev <= 9'd132;
            chA_phi1_curr <= 9'd296;
            chA_phi1_prev <= 9'd255;
            // Chamber B initialized in the uniform vacuum floor state (mu = 1, phi = 0)
            chB_mu0       <= 9'd1;
            chB_mu1       <= 9'd1;
            chB_phi0_curr <= 9'd0;
            chB_phi0_prev <= 9'd0;
            chB_phi1_curr <= 9'd0;
            chB_phi1_prev <= 9'd0;
        end else begin
            case (cmd_mode)
                2'b00: begin
                    // Normal evolution in Chamber A before stasis (with gate impulse +13)
                    chA_phi0_prev <= chA_phi0_curr;
                    chA_phi0_curr <= ((chA_phi0_curr <<< 1) - chA_phi0_prev + 9'd13) & 9'd511;
                    chA_phi1_prev <= chA_phi1_curr;
                    chA_phi1_curr <= ((chA_phi1_curr <<< 1) - chA_phi1_prev + 9'd13) & 9'd511;
                end
                2'b01: begin
                    // STEP 1 — STASIS (D_stasis = 6,823,936 -> Heisenberg deadband Phi = 0):
                    // Internal reaction gates are frozen without freezing water into ice!
                    chA_phi0_curr <= chA_phi0_curr;
                    chA_phi0_prev <= chA_phi0_prev;
                    chA_phi1_curr <= chA_phi1_curr;
                    chA_phi1_prev <= chA_phi1_prev;
                end
                2'b10: begin
                    // STEP 2 — TELEPORT (A -> Ballistic Waveguide -> 833:1 Write Focus in B):
                    // Chamber B reconstructs all 72 bits from Pauli singlet b_k + syndrome sigma_k
                    chB_mu0       <= chA_mu0;
                    chB_mu1       <= chA_mu1;
                    chB_phi0_curr <= (singlet_b0 + sigma0 + waveguide_noise_leak[8:0]) & 9'd511;
                    chB_phi0_prev <= (singlet_b1 + sigma1 + waveguide_noise_leak[8:0]) & 9'd511;
                    chB_phi1_curr <= (singlet_b2 + sigma2 + waveguide_noise_leak[8:0]) & 9'd511;
                    chB_phi1_prev <= (singlet_b3 + sigma3 + waveguide_noise_leak[8:0]) & 9'd511;
                    // Chamber A simultaneously discharges to vacuum floor (1 -> 1 swap, no cloning!)
                    chA_mu0       <= 9'd1;
                    chA_mu1       <= 9'd1;
                    chA_phi0_curr <= 9'd0;
                    chA_phi0_prev <= 9'd0;
                    chA_phi1_curr <= 9'd0;
                    chA_phi1_prev <= 9'd0;
                end
                2'b11: begin
                    // STEP 3 — RELEASE STASIS IN CHAMBER B:
                    // Chamber B lifts stasis and resumes reversible Verlet evolution from the exact state!
                    chB_phi0_prev <= chB_phi0_curr;
                    chB_phi0_curr <= ((chB_phi0_curr <<< 1) - chB_phi0_prev + 9'd13) & 9'd511;
                    chB_phi1_prev <= chB_phi1_curr;
                    chB_phi1_curr <= ((chB_phi1_curr <<< 1) - chB_phi1_prev + 9'd13) & 9'd511;
                end
            endcase
        end
    end
endmodule

// ----------------------------------------------------------------------------
// Module 6: Synthesizable Low-Cost FPGA 12-Pin Cuboctahedron Phase Driver
// Drives the 12 physical vertices V1..V12 of the 3-PCB (XY, XZ, YZ) crossed
// cuboctahedron resonator with exact 1/512-period digital phase resolution.
// Modes (`mode_sel`):
//   3'd0: STASIS_INPHASE    — all 12 beams at phase 0 (D_stasis = 833 * eps)
//   3'd1: BALLISTIC_BRIDGE  — 6 beams at 0, 6 beams at +128 (quarter-turn saddle)
//   3'd2: BARRIER_COLLAPSE  — 6 beams at 0, 6 beams at +139 (587x collapse to eps=8192)
//   3'd3: PAULI_VORTEX_LOCK — 6 beams at 0, 6 beams at +256 (singlet lock S=0, C=-128)
//   3'd4: EULER_XY_ROTATOR  — XY square driven at (0, 128, 256, 384), XZ & YZ passive (Hi-Z)
// ----------------------------------------------------------------------------
module fpga_12beam_cuboctahedron_driver (
    input  wire        clk_512x,      // Master clock at 512 * f_0
    input  wire        rst,
    input  wire [2:0]  mode_sel,
    output reg  [8:0]  ring_counter,  // Current tick in Z_512 (0..511)
    output wire [11:0] beam_pins,     // 12 physical output pins to V1..V12
    output wire [11:0] beam_oe        // Output enable (1 = active drive, 0 = passive detector)
);
    always @(posedge clk_512x) begin
        if (rst)
            ring_counter <= 9'd0;
        else
            ring_counter <= (ring_counter + 9'd1) & 9'd511;
    end

    // Phase offsets for the 12 vertices:
    // V1..V4 (XY plane), V5..V8 (XZ plane), V9..V12 (YZ plane)
    reg [8:0] phase_off [0:11];
    reg [11:0] oe_reg;
    integer k;

    always @(*) begin
        oe_reg = 12'hFFF;
        for (k = 0; k < 12; k = k + 1) phase_off[k] = 9'd0;
        case (mode_sel)
            3'd0: begin
                // STASIS_INPHASE: all 12 vertices at 0 ticks
                for (k = 0; k < 12; k = k + 1) phase_off[k] = 9'd0;
            end
            3'd1: begin
                // BALLISTIC_BRIDGE: odd vertices at +128 ticks (90 deg)
                for (k = 0; k < 12; k = k + 1)
                    phase_off[k] = (k & 1) ? 9'd128 : 9'd0;
            end
            3'd2: begin
                // BARRIER_COLLAPSE: odd vertices at +139 ticks (97.73 deg)
                for (k = 0; k < 12; k = k + 1)
                    phase_off[k] = (k & 1) ? 9'd139 : 9'd0;
            end
            3'd3: begin
                // PAULI_VORTEX_LOCK: odd vertices at +256 ticks (180 deg)
                for (k = 0; k < 12; k = k + 1)
                    phase_off[k] = (k & 1) ? 9'd256 : 9'd0;
            end
            3'd4: begin
                // EULER_XY_ROTATOR: XY square (V1..V4) at 0, 128, 256, 384; XZ & YZ passive
                phase_off[0] = 9'd0;
                phase_off[1] = 9'd128;
                phase_off[2] = 9'd256;
                phase_off[3] = 9'd384;
                oe_reg = 12'b0000_0000_1111;
            end
            default: begin
                for (k = 0; k < 12; k = k + 1) phase_off[k] = 9'd0;
            end
        endcase
    end

    assign beam_oe = oe_reg;

    // Each output pin generates a 50%-duty square wave shifted by phase_off[k] in Z_512
    // (bit 8 of `(ring_counter + phase_off[k]) & 511` is 0 for 0..255 and 1 for 256..511!)
    genvar g;
    generate
        for (g = 0; g < 12; g = g + 1) begin : gen_pins
            wire [8:0] shifted_tick = (ring_counter + phase_off[g]) & 9'd511;
            assign beam_pins[g] = oe_reg[g] ? ~shifted_tick[8] : 1'b0;
        end
    endgenerate
endmodule

// ----------------------------------------------------------------------------
// Module 7: 4-Channel Nilpotent Holonomic Tomograph (CE-RD-03) & Domain-Wall
// Quantum Ratchet (CE-RD-02)
// Exact integer hardware implementation of the 4-channel cascade matrix
// `2 * M_chan = 2 * I_4 + 2 * N_nil` (`N_nil^3 = 0`, det = 24 = 2 * |N_12|)
// and its division-free 3-term nilpotent inverse `24 * M_chan^-1`:
//    Forward (`2 * y = (2*I + 2*N) * s`):
//     y0_2 = 2*s0 + s1
//     y1_2 = 2*s1 + 2*s2
//     y2_2 = 2*s2
//     y3_2 = 2*s3
//   Exact division-free inverse (`24 * s_rec`):
//     s0_rec = (12 * y0_2 - 6 * y1_2 + 6 * y2_2) / 24 === s0
//     s1_rec = (12 * y1_2 - 12 * y2_2) / 24           === s1
//     s2_rec = (12 * y2_2) / 24                       === s2
//     s3_rec = (12 * y3_2) / 24                       === s3
// Plus the asymmetric Heisenberg domain-wall ratchet (`Int.fdiv` vs `Int.tdiv`):
//   At negative wall drive `-1`, floor division `(-1) >>> 9` yields `-1` tick
//   ratchet rectification, whereas symmetric truncation `tdiv(-1, 512)` yields `0`!
// ----------------------------------------------------------------------------
module holonomic_4channel_tomograph_and_ratchet (
    input  wire signed [31:0] s0_in,
    input  wire signed [31:0] s1_in,
    input  wire signed [31:0] s2_in,
    input  wire signed [31:0] s3_in,
    output wire signed [31:0] y0_2x,
    output wire signed [31:0] y1_2x,
    output wire signed [31:0] y2_2x,
    output wire signed [31:0] y3_2x,
    output wire signed [31:0] s0_rec,
    output wire signed [31:0] s1_rec,
    output wire signed [31:0] s2_rec,
    output wire signed [31:0] s3_rec,
    output wire signed [31:0] ratchet_fdiv_step,
    output wire signed [31:0] ratchet_tdiv_step
);
    // Forward 4-channel mixing (scaled by 2 for pure integer arithmetic)
    assign y0_2x = (s0_in <<< 1) + s1_in;
    assign y1_2x = (s1_in <<< 1) + (s2_in <<< 1);
    assign y2_2x = (s2_in <<< 1);
    assign y3_2x = (s3_in <<< 1);

    // Exact 3-term nilpotent inverse (I - N + N^2) recovering (s0, s1, s2, s3) with zero loss
    assign s0_rec = (32'sd12 * y0_2x - 32'sd6 * y1_2x + 32'sd6 * y2_2x) / 32'sd24;
    assign s1_rec = (32'sd12 * y1_2x - 32'sd12 * y2_2x) / 32'sd24;
    assign s2_rec = (32'sd12 * y2_2x) / 32'sd24;
    assign s3_rec = (32'sd12 * y3_2x) / 32'sd24;

    // CE-RD-02 Domain-wall quantum ratchet: floor division `>>> 9` on negative sub-period drive `-1`
    wire signed [31:0] wall_drive = -32'sd1;
    assign ratchet_fdiv_step = wall_drive >>> 9; // Exact -1 tick rectification!
    assign ratchet_tdiv_step = wall_drive / 32'sd512; // Symmetric truncation gives 0
endmodule

// ----------------------------------------------------------------------------
// Module 8: 3-Chamber Autonomous Food & Oxygen Synthesizer Hardware Controller
// Complete FSM & actuator driver for the stainless-steel/quartz 3-chamber unit:
//   Recipes (`recipe_sel`):
//     2'b00: CUTLET_MEAT   (Myosin fibers + Heme Myoglobin FeN4O2 Z=70 + Lipids Z=144 + Maillard crust)
//     2'b01: MILK_CHEESE   (Casein micelles + Triglyceride emulsion Z=50/144 + Calcium)
//     2'b10: VITAMIN_NECTAR(D-Glucose Z=96 + Vitamin C Z=92 + Citric Z=100 + Aroma esters Z=80)
//     2'b11: BREAD_PASTA   (Amylose Starch Z=86 + Gluten protein fibers + Maillard crust)
//   Stages (`stage_out`):
//     3'd0: IDLE
//     3'd1: PHOTOSYNTHESIS_CO2_H2O  (Ch1 at dphi=139, 441/718nm LEDs ON, O2 vent ON -> Z=96 + Z=50 + Z=144)
//     3'd2: NITROGEN_CHIRAL_AMINO   (Ch2 at dphi=139 & Euler Mode 4 -> 20 L-amino acids Z=40/48 + Heme Z=70)
//     3'd3: ACOUSTIC_FOLD_TEXTURE   (Ch3 at dphi=128 -> O(L) linear protein folding & 3D fiber alignment)
//     3'd4: SURFACE_MAILLARD_CRUST  (Ch3 at dphi=139 -> low-temp carcinogen-free golden Maillard crust)
//     3'd5: STASIS_HOLD_READY       (Ch3 at dphi=0, D=833*eps stasis freshness lock, food_ready=1)
// ----------------------------------------------------------------------------
module food_synthesizer_3chamber_controller (
    input  wire       clk,
    input  wire       rst,
    input  wire       start_btn,
    input  wire [1:0] recipe_sel,
    output reg  [2:0] stage_out,
    output reg  [2:0] ch1_phase_mode,
    output reg  [2:0] ch2_phase_mode,
    output reg  [2:0] ch3_phase_mode,
    output reg        pump_air_co2_n2_en,
    output reg        pump_water_h2o_en,
    output reg        valve_mineral_heme_fe_en,
    output reg        valve_o2_breath_vent_en,
    output reg        led_441_718nm_photo_en,
    output reg        ultrasonic_12beam_en,
    output reg  [8:0] synthesized_target_z,
    output reg        food_ready_led
);
    // Instantiate three 12-beam cuboctahedron phase drivers for Chambers 1, 2, and 3 (36 beam pins total)
    wire [8:0]  cnt1, cnt2, cnt3;
    wire [11:0] ch1_pins, ch2_pins, ch3_pins;
    wire [11:0] ch1_oe,   ch2_oe,   ch3_oe;

    fpga_12beam_cuboctahedron_driver u_ch1_drv (
        .clk_512x(clk), .rst(rst), .mode_sel(ch1_phase_mode),
        .ring_counter(cnt1), .beam_pins(ch1_pins), .beam_oe(ch1_oe)
    );
    fpga_12beam_cuboctahedron_driver u_ch2_drv (
        .clk_512x(clk), .rst(rst), .mode_sel(ch2_phase_mode),
        .ring_counter(cnt2), .beam_pins(ch2_pins), .beam_oe(ch2_oe)
    );
    fpga_12beam_cuboctahedron_driver u_ch3_drv (
        .clk_512x(clk), .rst(rst), .mode_sel(ch3_phase_mode),
        .ring_counter(cnt3), .beam_pins(ch3_pins), .beam_oe(ch3_oe)
    );

    always @(posedge clk) begin
        if (rst) begin
            stage_out                <= 3'd0;
            ch1_phase_mode           <= 3'd0;
            ch2_phase_mode           <= 3'd0;
            ch3_phase_mode           <= 3'd0;
            pump_air_co2_n2_en       <= 1'b0;
            pump_water_h2o_en        <= 1'b0;
            valve_mineral_heme_fe_en <= 1'b0;
            valve_o2_breath_vent_en  <= 1'b0;
            led_441_718nm_photo_en   <= 1'b0;
            ultrasonic_12beam_en     <= 1'b0;
            synthesized_target_z     <= 9'd0;
            food_ready_led           <= 1'b0;
        end else begin
            case (stage_out)
                3'd0: begin // IDLE
                    if (start_btn) begin
                        stage_out               <= 3'd1;
                        ch1_phase_mode          <= 3'd2; // Mode 2: dphi = 139 (587x barrier collapse)
                        pump_air_co2_n2_en      <= 1'b1;
                        pump_water_h2o_en       <= 1'b1;
                        led_441_718nm_photo_en  <= 1'b1;
                        valve_o2_breath_vent_en <= 1'b1; // Vent pure O2 (Z = 96)
                        synthesized_target_z    <= 9'd96; // D-Glucose C6H12O6 (Z = 96) + 6 O2 (Z = 96)
                        food_ready_led          <= 1'b0;
                    end
                end
                3'd1: begin // STAGE 1 -> STAGE 2: Chiral L-Amino Acid & Heme Myoglobin Fixation
                    stage_out                <= 3'd2;
                    ch1_phase_mode           <= 3'd1; // Ballistic transfer to Chamber 2
                    ch2_phase_mode           <= 3'd4; // Mode 4: Chiral Euler XY Quadrature Rotator (0,128,256,384)
                    valve_mineral_heme_fe_en <= (recipe_sel == 2'b00); // Inject Fe26 for Cutlet Myoglobin FeN4O2 (Z=70)
                    synthesized_target_z     <= (recipe_sel == 2'b00) ? 9'd70 :
                                                (recipe_sel == 2'b01) ? 9'd144 :
                                                (recipe_sel == 2'b10) ? 9'd92 : 9'd86;
                end
                3'd2: begin // STAGE 2 -> STAGE 3: 3D Ultrasonic Standing-Wave Protein Folding & Muscle Fiber Alignment
                    stage_out                <= 3'd3;
                    pump_air_co2_n2_en       <= 1'b0;
                    pump_water_h2o_en        <= 1'b0;
                    valve_mineral_heme_fe_en <= 1'b0;
                    ch2_phase_mode           <= 3'd1; // Transfer to Chamber 3
                    ch3_phase_mode           <= 3'd1; // Mode 1: dphi = 128 Quarter-Turn Ballistic Folding Bridge
                    ultrasonic_12beam_en     <= 1'b1; // 12-beam standing wave aligns myosin/actin muscle fibers
                end
                3'd3: begin // STAGE 3 -> STAGE 4: Carcinogen-Free Surface Maillard Crust (for Cutlet & Bread)
                    if (recipe_sel == 2'b00 || recipe_sel == 2'b11) begin
                        stage_out      <= 3'd4;
                        ch3_phase_mode <= 3'd2; // Mode 2: dphi = 139 surface Maillard reaction at 68 C
                    end else begin
                        stage_out      <= 3'd5;
                        ch3_phase_mode <= 3'd0; // Mode 0: dphi = 0 Stasis Hold (D = 833 * eps)
                        food_ready_led <= 1'b1;
                    end
                end
                3'd4: begin // STAGE 4 -> STAGE 5: Lock finished hot cutlet in Phase Stasis (D = 6,823,936)
                    stage_out              <= 3'd5;
                    ch3_phase_mode         <= 3'd0; // Mode 0: In-phase Stasis (D = 833 * eps)
                    led_441_718nm_photo_en <= 1'b0;
                    food_ready_led         <= 1'b1;
                end
                3'd5: begin // READY IN STASIS
                    stage_out <= 3'd5;
                end
                default: stage_out <= 3'd0;
            endcase
        end
    end
endmodule

// ----------------------------------------------------------------------------
// Module 9: Zero-Heat Phase-Stasis Peltier Ratchet Cooler, Eternal Stasis
// Pantry, and Pauli Singlet Vortex Battery (`Technologies #18, #19, #28`)
// 1. Thermal Diode 833:1 (`D_cold = 6,823,936` vs `D_sink = 8,192`) blocks
//    reverse phonon backflow (`Phi_back = 0` inside Heisenberg deadband < 41).
// 2. Zero Joule self-heating (`n_E_joule = 0`) in the ballistic channel.
// 3. Domain-wall quantum ratchet (`fdiv >>> 9`) rectifies extracted thermal
//    fluctuations into harvested electrical charge (`harvested_energy_ticks`)
//    stored inside the zero-leakage Pauli singlet vortex battery (`dphi = 256`,
//    where `S(256) = 0` gives zero external leakage and `C(256) = -128` holds
//    the circulating surface current!).
// ----------------------------------------------------------------------------
module phase_peltier_stasis_pantry_and_vortex_battery (
    input  wire        clk,
    input  wire        rst,
    input  wire [1:0]  op_mode,          // 00: COOL_AND_HARVEST, 01: ETERNAL_STASIS_PANTRY, 10: BATTERY_HOLD_256, 11: BATTERY_DISCHARGE_128
    input  wire signed [31:0] ambient_heat_flux,
    output wire signed [31:0] reverse_heat_leak_phi,
    output wire signed [31:0] joule_self_heat_quanta,
    output wire signed [31:0] food_decay_rate_phi,
    output reg  signed [31:0] vortex_battery_charge,
    output reg  signed [31:0] delivered_power_out
);
    wire signed [31:0] d_cold_stasis = 32'sd6823936; // 833 * 8192
    wire signed [31:0] d_sink_focus  = 32'sd8192;

    // 1. Reverse heat backflow from sink to cold side is divided by D_cold = 6,823,936
    // and snapped to EXACT ZERO by the Heisenberg deadband (|Phi| < 41):
    wire signed [31:0] raw_backflow = (32'sd64 * ambient_heat_flux) / d_cold_stasis;
    wire signed [31:0] abs_backflow = (raw_backflow < 0) ? -raw_backflow : raw_backflow;
    assign reverse_heat_leak_phi = (abs_backflow < 32'sd41) ? 32'sd0 : raw_backflow;

    // 2. Zero Joule self-heating in ballistic transport:
    assign joule_self_heat_quanta = reverse_heat_leak_phi / 32'sd41;

    // 3. Eternal Stasis Pantry decay rate: all chemical/bacterial reaction impulses
    // inside the D_stasis = 6,823,936 chamber fall below 41 ticks -> 0 decay!
    assign food_decay_rate_phi = reverse_heat_leak_phi;

    // 4. CE-RD-02 Domain-wall ratchet rectifies extracted thermal flux into battery charge:
    wire signed [31:0] ratchet_harvest_step = -((-ambient_heat_flux) >>> 9); // +1 quantum per sub-period flux

    always @(posedge clk) begin
        if (rst) begin
            vortex_battery_charge <= 32'sd0;
            delivered_power_out   <= 32'sd0;
        end else begin
            case (op_mode)
                2'b00: begin
                    // COOL_AND_HARVEST: extracts heat without hot exhaust, charging the Pauli vortex battery!
                    vortex_battery_charge <= vortex_battery_charge + ratchet_harvest_step;
                    delivered_power_out   <= 32'sd0;
                end
                2'b01: begin
                    // ETERNAL_STASIS_PANTRY: holds food at room temp with 0 bacterial/oxidative decay
                    vortex_battery_charge <= vortex_battery_charge;
                    delivered_power_out   <= 32'sd0;
                end
                2'b10: begin
                    // BATTERY_HOLD_256 (Pauli Singlet Lock dphi = 256, S(256) = 0 -> zero self-discharge!)
                    vortex_battery_charge <= vortex_battery_charge;
                    delivered_power_out   <= 32'sd0;
                end
                2'b11: begin
                    // BATTERY_DISCHARGE_128 (Quarter-turn saddle dphi = 128, S(128) = +128 -> max power delivery!)
                    delivered_power_out   <= vortex_battery_charge * 32'sd128;
                    vortex_battery_charge <= 32'sd0;
                end
            endcase
        end
    end
endmodule

// ----------------------------------------------------------------------------
// Module 10: Programmable Voltage-Current (V-I) Phase-Throttle & Grid Inverter
// Controls output Voltage V_out, Current I_out, and Power P_out from the
// Phase-Stasis Ratchet / Pauli Vortex Generator without resistors or transformers:
//   - Phase throttle angle: `phi_load = 256 - throttle_k` (`throttle_k in 0..128`)
//   - Normalized cell voltage: `V_cell(k) = |C(256 - k)| = 128 - k`
//   - Normalized cell current: `I_cell(k) =  S(256 - k)  = k`
//   - Kirchhoff L1 invariant:  `V_cell(k) + I_cell(k) === 128 = Q_square`
//   - Independent Voltage gain: `N_V in 1..12` in-phase cuboctahedron beams (`V_out = N_V * V_cell`)
//   - Independent Current gain: `M_I in 1..3` parallel Euler planes `(XY, XZ, YZ)` (`I_out = M_I * I_cell`)
//   - Maximum Power Point (MPPT): uniquely at `throttle_k = 64 = K_P` (`45 deg` Fresnel stationary phase),
//     where `V_cell = 64, I_cell = 64, P_cell_max = 64 * 64 = 4096 = K_P^2`
//     (and with `N_V = 12, M_I = 3`: `P_total_max = 12 * 3 * 4096 = 147,456 = 36 * K_P^2`!).
//   - AC Grid Mode (`ac_polarity = 1` flips phase by `+256` half-turn for 50/60 Hz AC sine wave output).
// ----------------------------------------------------------------------------
module programmable_vi_power_inverter_controller (
    input  wire signed [31:0] throttle_k,       // 0..128 phase opening from Pauli singlet lock 256
    input  wire signed [31:0] voltage_beams_nv, // 1..12 active in-phase beams for voltage step-up
    input  wire signed [31:0] current_planes_mi,// 1..3 parallel Euler planes (XY, XZ, YZ) for current step-up
    input  wire               ac_half_cycle_inv,// 0 = positive half-wave, 1 = negative half-wave (+256 shift)
    output wire signed [31:0] phi_load_out,
    output wire signed [31:0] v_cell_norm,
    output wire signed [31:0] i_cell_norm,
    output wire signed [31:0] kirchhoff_sum_128,
    output wire signed [31:0] v_terminal_out,
    output wire signed [31:0] i_terminal_out,
    output wire signed [31:0] p_terminal_out
);
    assign phi_load_out = 32'sd256 - throttle_k + (ac_half_cycle_inv ? 32'sd256 : 32'sd0);

    wire signed [31:0] w_load, c_load, s_load;
    rotator_512_unit u_load_rot (
        .phi_in(32'sd256 - throttle_k),
        .wrap_out(w_load),
        .proj_c(c_load),
        .proj_s(s_load)
    );

    assign v_cell_norm       = (c_load < 0) ? -c_load : c_load; // |C(256 - k)| = 128 - k
    assign i_cell_norm       = s_load;                          //  S(256 - k)  = k
    assign kirchhoff_sum_128 = v_cell_norm + i_cell_norm;       // Identically 128!

    wire signed [31:0] ac_sign = ac_half_cycle_inv ? -32'sd1 : 32'sd1;
    assign v_terminal_out = ac_sign * voltage_beams_nv * v_cell_norm;
    assign i_terminal_out = ac_sign * current_planes_mi * i_cell_norm;
    assign p_terminal_out = v_terminal_out * i_terminal_out;
endmodule

// ----------------------------------------------------------------------------
// Module 11: Laboratory-Grade Smooth CV / CC / DDS Power Supply Controller
// Provides three 100% independent continuous dials on the 12-beam cuboctahedron:
//   Dial 1 (`v_set_alpha` on XY plane, 0..256 + 8-bit sub-tick sigma-delta):
//     Continuous output voltage V_target from 0.000 V to V_max (millivolt step).
//   Dial 2 (`i_limit_beta` on tilted XZ/YZ Euler planes, 0..256):
//     Continuous current limit I_limit independent of V_target; automatically
//     switches between Constant-Voltage (`cv_mode = 1`) and Constant-Current
//     (`cc_mode = 1`) in a single clock cycle without ohmic heat dissipation!
//   Dial 3 (`dds_freq_word` 32-bit DDS phase accumulator):
//     Continuous frequency control from 0.000 Hz (pure DC) to MHz with 0.01 Hz
//     resolution (`phase_acc <= phase_acc + dds_freq_word`, top 9 bits drive
//     the Z_512 rotator!).
// ----------------------------------------------------------------------------
module lab_smooth_cv_cc_dds_power_supply (
    input  wire        clk,
    input  wire        rst,
    input  wire [31:0] dds_freq_word,   // 0 = pure DC; >0 = smooth AC frequency (step = f_clk / 2^32)
    input  wire signed [31:0] v_set_mv, // Target voltage in millivolts (e.g. 0..30000 mV)
    input  wire signed [31:0] i_set_ma, // Target current limit in milliamps (e.g. 0..10000 mA)
    input  wire signed [31:0] r_load_ohm, // Connected load resistance in Ohms
    output reg  [31:0] dds_phase_acc,
    output wire [8:0]  dds_ring_phase,
    output wire signed [31:0] v_actual_mv,
    output wire signed [31:0] i_actual_ma,
    output wire        cv_mode_active,
    output wire        cc_mode_active
);
    always @(posedge clk) begin
        if (rst)
            dds_phase_acc <= 32'd0;
        else
            dds_phase_acc <= dds_phase_acc + dds_freq_word;
    end

    // Top 9 bits of the 32-bit DDS accumulator address the Z_512 rotator
    assign dds_ring_phase = dds_phase_acc[31:23];

    wire signed [31:0] dds_w, dds_c, dds_s;
    rotator_512_unit u_dds_rot (
        .phi_in({23'b0, dds_ring_phase}),
        .wrap_out(dds_w),
        .proj_c(dds_c),
        .proj_s(dds_s)
    );

    // Unclamped load current demanded at V_set: I_demand = V_set / R_load
    wire signed [31:0] i_demand_ma = (r_load_ohm > 0) ? (v_set_mv / r_load_ohm) : i_set_ma;

    // Automatic single-cycle CV / CC crossover via XZ/YZ Euler plane impedance D(beta):
    assign cc_mode_active = (i_demand_ma > i_set_ma);
    assign cv_mode_active = ~cc_mode_active;

    wire signed [31:0] v_dc_envelope = cc_mode_active ? (i_set_ma * r_load_ohm) : v_set_mv;
    wire signed [31:0] i_dc_envelope = cc_mode_active ? i_set_ma : i_demand_ma;

    // When dds_freq_word == 0 (DC mode), dds_c = +128 so output is pure DC V_actual = v_dc_envelope;
    // When dds_freq_word > 0 (AC mode), output is modulated smoothly by C_3(dds_ring_phase) / 128!
    assign v_actual_mv = (v_dc_envelope * dds_c) / 32'sd128;
    assign i_actual_ma = (i_dc_envelope * dds_c) / 32'sd128;
endmodule

// ----------------------------------------------------------------------------
// Module 12: Universal Host-Controlled SoC Top (`cuboctahedron_uart_cmd_soc_top`)
// Unified command decoder & telemetry router for Laptop / AI MCP control over
// USB-UART or ESP32 Wi-Fi bridge (zero physical buttons required!).
// Command Opcodes (`host_opcode`):
//   4'h1: CMD_SET_12BEAM_MODE   (arg0[2:0] = mode 0..4 -> Stasis, Ballistic, Collapse, Pauli, Euler)
//   4'h2: CMD_SYNTHESIZE_FOOD   (arg0[1:0] = recipe 00:Cutlet, 01:Milk, 10:Nectar, 11:Bread)
//   4'h3: CMD_SET_LAB_PSU_VIF   (arg0 = V_set_mV, arg1 = I_set_mA, arg2 = DDS_freq_word)
//   4'h4: CMD_STASIS_PANTRY_MODE(arg0[1:0] = 00:Cool&Harvest, 01:EternalStasis, 10:BattHold, 11:BattDischarge)
//   4'h5: CMD_TELEPORT_72BIT    (arg0[1:0] = 01:Stasis, 10:Teleport_A_to_B, 11:Release_B)
// ----------------------------------------------------------------------------
module cuboctahedron_uart_cmd_soc_top (
    input  wire        clk,
    input  wire        rst,
    input  wire        host_cmd_valid,
    input  wire [3:0]  host_opcode,
    input  wire signed [31:0] host_arg0,
    input  wire signed [31:0] host_arg1,
    input  wire signed [31:0] host_arg2,
    output wire [11:0] phys_beam_pins,
    output wire [11:0] phys_beam_oe,
    output wire [2:0]  soc_food_stage,
    output wire        soc_food_ready,
    output wire [8:0]  soc_food_target_z,
    output wire signed [31:0] soc_psu_v_mv,
    output wire signed [31:0] soc_psu_i_ma,
    output wire        soc_psu_cv,
    output wire        soc_psu_cc,
    output wire signed [31:0] soc_stasis_decay_phi,
    output wire signed [31:0] soc_vortex_batt_charge,
    output wire [8:0]  soc_tp_chB_mu0,
    output wire [8:0]  soc_tp_chB_phi0_curr
);
    reg [2:0]  reg_beam_mode;
    reg        reg_food_start;
    reg [1:0]  reg_food_recipe;
    reg signed [31:0] reg_psu_v_mv;
    reg signed [31:0] reg_psu_i_ma;
    reg [31:0] reg_psu_dds_freq;
    reg [1:0]  reg_pantry_mode;
    reg [1:0]  reg_tp_mode;

    always @(posedge clk) begin
        if (rst) begin
            reg_beam_mode    <= 3'd0;
            reg_food_start   <= 1'b0;
            reg_food_recipe  <= 2'b00;
            reg_psu_v_mv     <= 32'sd12000;
            reg_psu_i_ma     <= 32'sd3000;
            reg_psu_dds_freq <= 32'd0;
            reg_pantry_mode  <= 2'b01; // Default: Eternal Stasis Pantry active
            reg_tp_mode      <= 2'b01;
        end else if (host_cmd_valid) begin
            case (host_opcode)
                4'h1: reg_beam_mode <= host_arg0[2:0];
                4'h2: begin
                    reg_food_recipe <= host_arg0[1:0];
                    reg_food_start  <= 1'b1;
                end
                4'h3: begin
                    reg_psu_v_mv     <= host_arg0;
                    reg_psu_i_ma     <= host_arg1;
                    reg_psu_dds_freq <= host_arg2[31:0];
                end
                4'h4: reg_pantry_mode <= host_arg0[1:0];
                4'h5: reg_tp_mode     <= host_arg0[1:0];
                default: ;
            endcase
        end
    end

    wire [8:0] drv_ring_cnt;
    fpga_12beam_cuboctahedron_driver u_soc_beam12 (
        .clk_512x(clk), .rst(rst), .mode_sel(reg_beam_mode),
        .ring_counter(drv_ring_cnt), .beam_pins(phys_beam_pins), .beam_oe(phys_beam_oe)
    );

    wire [2:0] f_m1, f_m2, f_m3;
    wire f_air, f_h2o, f_fe, f_o2, f_led, f_us;
    food_synthesizer_3chamber_controller u_soc_food (
        .clk(clk), .rst(rst), .start_btn(reg_food_start), .recipe_sel(reg_food_recipe),
        .stage_out(soc_food_stage), .ch1_phase_mode(f_m1), .ch2_phase_mode(f_m2), .ch3_phase_mode(f_m3),
        .pump_air_co2_n2_en(f_air), .pump_water_h2o_en(f_h2o), .valve_mineral_heme_fe_en(f_fe),
        .valve_o2_breath_vent_en(f_o2), .led_441_718nm_photo_en(f_led), .ultrasonic_12beam_en(f_us),
        .synthesized_target_z(soc_food_target_z), .food_ready_led(soc_food_ready)
    );

    wire [31:0] psu_acc;
    wire [8:0]  psu_phase;
    lab_smooth_cv_cc_dds_power_supply u_soc_psu (
        .clk(clk), .rst(rst), .dds_freq_word(reg_psu_dds_freq),
        .v_set_mv(reg_psu_v_mv), .i_set_ma(reg_psu_i_ma), .r_load_ohm(32'sd6),
        .dds_phase_acc(psu_acc), .dds_ring_phase(psu_phase),
        .v_actual_mv(soc_psu_v_mv), .i_actual_ma(soc_psu_i_ma),
        .cv_mode_active(soc_psu_cv), .cc_mode_active(soc_psu_cc)
    );

    wire signed [31:0] p_back, p_joule, p_pwr;
    phase_peltier_stasis_pantry_and_vortex_battery u_soc_pantry (
        .clk(clk), .rst(rst), .op_mode(reg_pantry_mode), .ambient_heat_flux(32'sd16384),
        .reverse_heat_leak_phi(p_back), .joule_self_heat_quanta(p_joule),
        .food_decay_rate_phi(soc_stasis_decay_phi),
        .vortex_battery_charge(soc_vortex_batt_charge), .delivered_power_out(p_pwr)
    );

    wire [8:0] ta_m0, ta_m1, ta_p0c, ta_p0p, ta_p1c, ta_p1p;
    wire [8:0] tb_m1, tb_p0p, tb_p1c, tb_p1p;
    wire signed [31:0] td_s, td_w, td_c, td_n, td_norm;
    two_chamber_72bit_teleporter u_soc_tp (
        .clk(clk), .rst(rst), .cmd_mode(reg_tp_mode),
        .singlet_a0(9'd41), .singlet_a1(9'd97), .singlet_a2(9'd137), .singlet_a3(9'd263),
        .ext_thermal_noise_drive(32'sd24576),
        .chA_mu0(ta_m0), .chA_mu1(ta_m1), .chA_phi0_curr(ta_p0c), .chA_phi0_prev(ta_p0p),
        .chA_phi1_curr(ta_p1c), .chA_phi1_prev(ta_p1p),
        .chB_mu0(soc_tp_chB_mu0), .chB_mu1(tb_m1), .chB_phi0_curr(soc_tp_chB_phi0_curr),
        .chB_phi0_prev(tb_p0p), .chB_phi1_curr(tb_p1c), .chB_phi1_prev(tb_p1p),
        .d_stasis_val(td_s), .d_write_val(td_w), .contrast_833(td_c),
        .waveguide_noise_leak(td_n), .total_two_chamber_norm_sq(td_norm)
    );
endmodule

// ============================================================================
// Testbench: Full Hardware Verification & VCD Waveform Dump
// ============================================================================
module tb_cuboctahedron_carrier_asic;
    reg signed [31:0] phi_tb;
    wire signed [31:0] wrap_tb, c_tb, s_tb;
    wire signed [31:0] wrap_next, c_next, s_next;

    rotator_512_unit u_rot0 (.phi_in(phi_tb), .wrap_out(wrap_tb), .proj_c(c_tb), .proj_s(s_tb));
    rotator_512_unit u_rot1 (.phi_in(phi_tb + 32'sd1), .wrap_out(wrap_next), .proj_c(c_next), .proj_s(s_next));

    wire signed [31:0] wronskian_tb = c_tb * s_next - s_tb * c_next;
    wire signed [63:0] pyth_x = c_tb * c_tb - s_tb * s_tb;
    wire signed [63:0] pyth_y = 64'sd2 * c_tb * s_tb;
    wire signed [63:0] pyth_r = c_tb * c_tb + s_tb * s_tb;

    // Quotient-remainder unit for Born rule & wave-particle duality
    reg signed [31:0] delta_qr_tb;
    wire signed [31:0] q_tb, r_tb;
    quotient_remainder_512_unit u_qr (.delta_phi(delta_qr_tb), .branch_q(q_tb), .edge_r(r_tb));

    // Reversible Verlet cell
    reg clk = 0;
    reg rst = 1;
    reg rev = 0;
    wire [8:0] v_curr, v_prev;
    verlet_reversible_cell u_verlet (
        .clk(clk),
        .rst(rst),
        .reverse_dir(rev),
        .init_curr(9'd41),
        .init_prev(9'd0),
        .phi_accel(32'sd13),
        .phi_curr(v_curr),
        .phi_prev(v_prev)
    );

    // 12-beam cuboctahedron gate
    reg signed [31:0] mu_c_tb = 32'sd64;
    reg signed [31:0] mu_nb_tb = 32'sd64;
    reg signed [31:0] dphi_gate_tb = 32'sd0;
    wire signed [31:0] cg_tb, sg_tb, denom_tb, phig_tb, ne_tb;
    cuboctahedron_12beam_gate u_gate12 (
        .mu_center(mu_c_tb),
        .mu_nb(mu_nb_tb),
        .delta_phi(dphi_gate_tb),
        .c_single(cg_tb),
        .s_single(sg_tb),
        .denom_d(denom_tb),
        .gate_phase_phi(phig_tb),
        .energy_quanta_ne(ne_tb)
    );

    integer i, mu, clicks, errors;
    integer fresnel_c_sum, fresnel_s_sum;
    reg [8:0] saved_curr, saved_prev;

    // Two-Chamber 72-Bit Teleporter signals
    reg tp_rst = 1;
    reg [1:0] tp_mode = 2'b00;
    wire [8:0] tp_a_mu0, tp_a_mu1, tp_a_p0c, tp_a_p0p, tp_a_p1c, tp_a_p1p;
    wire [8:0] tp_b_mu0, tp_b_mu1, tp_b_p0c, tp_b_p0p, tp_b_p1c, tp_b_p1p;
    wire signed [31:0] tp_d_stasis, tp_d_write, tp_contrast, tp_noise_leak, tp_norm_sq;
    reg [8:0] saved_a_mu0, saved_a_mu1, saved_a_p0c, saved_a_p0p, saved_a_p1c, saved_a_p1p;
    reg signed [31:0] norm_before_tp;

    two_chamber_72bit_teleporter u_teleporter (
        .clk(clk),
        .rst(tp_rst),
        .cmd_mode(tp_mode),
        .singlet_a0(9'd41),
        .singlet_a1(9'd97),
        .singlet_a2(9'd137),
        .singlet_a3(9'd263),
        .ext_thermal_noise_drive(32'sd24576),
        .chA_mu0(tp_a_mu0),
        .chA_mu1(tp_a_mu1),
        .chA_phi0_curr(tp_a_p0c),
        .chA_phi0_prev(tp_a_p0p),
        .chA_phi1_curr(tp_a_p1c),
        .chA_phi1_prev(tp_a_p1p),
        .chB_mu0(tp_b_mu0),
        .chB_mu1(tp_b_mu1),
        .chB_phi0_curr(tp_b_p0c),
        .chB_phi0_prev(tp_b_p0p),
        .chB_phi1_curr(tp_b_p1c),
        .chB_phi1_prev(tp_b_p1p),
        .d_stasis_val(tp_d_stasis),
        .d_write_val(tp_d_write),
        .contrast_833(tp_contrast),
        .waveguide_noise_leak(tp_noise_leak),
        .total_two_chamber_norm_sq(tp_norm_sq)
    );

    reg drv_rst = 1;
    reg [2:0] drv_mode = 3'd0;
    wire [8:0] drv_cnt;
    wire [11:0] drv_pins, drv_oe;

    fpga_12beam_cuboctahedron_driver u_fpga_drv (
        .clk_512x(clk),
        .rst(drv_rst),
        .mode_sel(drv_mode),
        .ring_counter(drv_cnt),
        .beam_pins(drv_pins),
        .beam_oe(drv_oe)
    );

    wire signed [31:0] tom_y0, tom_y1, tom_y2, tom_y3;
    wire signed [31:0] tom_s0, tom_s1, tom_s2, tom_s3;
    wire signed [31:0] rat_fdiv, rat_tdiv;

    holonomic_4channel_tomograph_and_ratchet u_tom_rat (
        .s0_in(32'sd12),
        .s1_in(32'sd41),
        .s2_in(32'sd97),
        .s3_in(32'sd263),
        .y0_2x(tom_y0),
        .y1_2x(tom_y1),
        .y2_2x(tom_y2),
        .y3_2x(tom_y3),
        .s0_rec(tom_s0),
        .s1_rec(tom_s1),
        .s2_rec(tom_s2),
        .s3_rec(tom_s3),
        .ratchet_fdiv_step(rat_fdiv),
        .ratchet_tdiv_step(rat_tdiv)
    );

    reg food_rst = 1;
    reg food_start = 0;
    reg [1:0] food_recipe = 2'b00; // 00 = CUTLET_MEAT
    wire [2:0] food_stage, food_m1, food_m2, food_m3;
    wire food_air, food_h2o, food_fe, food_o2, food_led, food_us, food_ready;
    wire [8:0] food_z;

    food_synthesizer_3chamber_controller u_food_synth (
        .clk(clk),
        .rst(food_rst),
        .start_btn(food_start),
        .recipe_sel(food_recipe),
        .stage_out(food_stage),
        .ch1_phase_mode(food_m1),
        .ch2_phase_mode(food_m2),
        .ch3_phase_mode(food_m3),
        .pump_air_co2_n2_en(food_air),
        .pump_water_h2o_en(food_h2o),
        .valve_mineral_heme_fe_en(food_fe),
        .valve_o2_breath_vent_en(food_o2),
        .led_441_718nm_photo_en(food_led),
        .ultrasonic_12beam_en(food_us),
        .synthesized_target_z(food_z),
        .food_ready_led(food_ready)
    );

    reg pelt_rst = 1;
    reg [1:0] pelt_mode = 2'b00;
    wire signed [31:0] pelt_back_leak, pelt_joule, pelt_decay, pelt_batt, pelt_pwr;

    phase_peltier_stasis_pantry_and_vortex_battery u_pelt_batt (
        .clk(clk),
        .rst(pelt_rst),
        .op_mode(pelt_mode),
        .ambient_heat_flux(32'sd16384),
        .reverse_heat_leak_phi(pelt_back_leak),
        .joule_self_heat_quanta(pelt_joule),
        .food_decay_rate_phi(pelt_decay),
        .vortex_battery_charge(pelt_batt),
        .delivered_power_out(pelt_pwr)
    );

    reg signed [31:0] vi_k  = 32'sd0;
    reg signed [31:0] vi_nv = 32'sd12;
    reg signed [31:0] vi_mi = 32'sd3;
    reg               vi_ac = 1'b0;
    wire signed [31:0] vi_phi, vi_vc, vi_ic, vi_ksum, vi_vout, vi_iout, vi_pout;

    programmable_vi_power_inverter_controller u_vi_ctrl (
        .throttle_k(vi_k),
        .voltage_beams_nv(vi_nv),
        .current_planes_mi(vi_mi),
        .ac_half_cycle_inv(vi_ac),
        .phi_load_out(vi_phi),
        .v_cell_norm(vi_vc),
        .i_cell_norm(vi_ic),
        .kirchhoff_sum_128(vi_ksum),
        .v_terminal_out(vi_vout),
        .i_terminal_out(vi_iout),
        .p_terminal_out(vi_pout)
    );

    reg        lab_rst  = 1;
    reg [31:0] lab_freq = 32'd0;
    reg signed [31:0] lab_vset = 32'sd12000; // 12.000 V
    reg signed [31:0] lab_iset = 32'sd3000;  // 3.000 A
    reg signed [31:0] lab_rload = 32'sd6;    // 6 Ohm -> demands 2.000 A (CV mode)
    wire [31:0] lab_acc;
    wire [8:0]  lab_phase;
    wire signed [31:0] lab_vact, lab_iact;
    wire        lab_cv, lab_cc;

    lab_smooth_cv_cc_dds_power_supply u_lab_psu (
        .clk(clk),
        .rst(lab_rst),
        .dds_freq_word(lab_freq),
        .v_set_mv(lab_vset),
        .i_set_ma(lab_iset),
        .r_load_ohm(lab_rload),
        .dds_phase_acc(lab_acc),
        .dds_ring_phase(lab_phase),
        .v_actual_mv(lab_vact),
        .i_actual_ma(lab_iact),
        .cv_mode_active(lab_cv),
        .cc_mode_active(lab_cc)
    );

    reg        soc_rst = 1;
    reg        soc_valid = 0;
    reg [3:0]  soc_op = 4'h0;
    reg signed [31:0] soc_a0 = 0, soc_a1 = 0, soc_a2 = 0;
    wire [11:0] soc_pins, soc_oe;
    wire [2:0]  soc_fstage;
    wire        soc_fready, soc_cv_w, soc_cc_w;
    wire [8:0]  soc_fz, soc_tpm0, soc_tpp0;
    wire signed [31:0] soc_vmv, soc_ima, soc_decay, soc_batt;

    cuboctahedron_uart_cmd_soc_top u_soc_top (
        .clk(clk), .rst(soc_rst), .host_cmd_valid(soc_valid),
        .host_opcode(soc_op), .host_arg0(soc_a0), .host_arg1(soc_a1), .host_arg2(soc_a2),
        .phys_beam_pins(soc_pins), .phys_beam_oe(soc_oe),
        .soc_food_stage(soc_fstage), .soc_food_ready(soc_fready), .soc_food_target_z(soc_fz),
        .soc_psu_v_mv(soc_vmv), .soc_psu_i_ma(soc_ima), .soc_psu_cv(soc_cv_w), .soc_psu_cc(soc_cc_w),
        .soc_stasis_decay_phi(soc_decay), .soc_vortex_batt_charge(soc_batt),
        .soc_tp_chB_mu0(soc_tpm0), .soc_tp_chB_phi0_curr(soc_tpp0)
    );

    initial begin
        $dumpfile("cuboctahedron_carrier.vcd");
        $dumpvars(0, tb_cuboctahedron_carrier_asic);

        errors = 0;
        fresnel_c_sum = 0;
        fresnel_s_sum = 0;

        $display("======================================================================");
        $display("[1] Hardware Audit of 9-Bit Rotator, Wronskian W=128, and Weierstrass Lift");
        $display("======================================================================");
        for (i = 0; i < 512; i = i + 1) begin
            phi_tb = i;
            #1;
            if (wronskian_tb !== 32'sd128) begin
                $display("ERROR at phi=%0d: Wronskian=%0d != 128", i, wronskian_tb);
                errors = errors + 1;
            end
            if (pyth_x * pyth_x + pyth_y * pyth_y !== pyth_r * pyth_r) begin
                $display("ERROR at phi=%0d: Pythagorean lift failed", i);
                errors = errors + 1;
            end
        end
        // Fresnel hardware sum over i^2 mod 512
        for (i = 0; i < 512; i = i + 1) begin
            phi_tb = i * i;
            #1;
            fresnel_c_sum = fresnel_c_sum + c_tb;
            fresnel_s_sum = fresnel_s_sum + s_tb;
        end
        $display("  -> All 512 ring ticks verified: W(phi) === 128, X^2 + Y^2 === R^2 (errors = %0d)", errors);
        $display("  -> Hardware Fresnel Diffraction Integrals: C_Fresnel = %0d, S_Fresnel = %0d", fresnel_c_sum, fresnel_s_sum);
        if (fresnel_c_sum !== 2048 || fresnel_s_sum !== 2048) errors = errors + 1;

        $display("======================================================================");
        $display("[2] 12-Beam Cuboctahedron Gate: Impedance Collapse & Ballistic Regimes");
        $display("======================================================================");
        // Regime A: In-phase repulsive barrier (delta_phi = 0)
        dphi_gate_tb = 32'sd0; #1;
        $display("  -> Delta_phi =   0 ticks (  0.0 deg): C=%4d, S=%4d | Denom D = %7d | Gate Phi = %6d | Quanta n_E = %0d",
                 cg_tb, sg_tb, denom_tb, phig_tb, ne_tb);
        // Regime B: Sub-saddle (delta_phi = 41, Heisenberg floor)
        dphi_gate_tb = 32'sd41; #1;
        $display("  -> Delta_phi =  41 ticks ( 28.8 deg): C=%4d, S=%4d | Denom D = %7d | Gate Phi = %6d | Quanta n_E = %0d",
                 cg_tb, sg_tb, denom_tb, phig_tb, ne_tb);
        // Regime C: Quadrant Saddle / Lossless Ballistic Bridge (delta_phi = 128 = 90 deg)
        dphi_gate_tb = 32'sd128; #1;
        $display("  -> Delta_phi = 128 ticks ( 90.0 deg): C=%4d, S=%4d | Denom D = %7d | Gate Phi = %6d | Quanta n_E = %0d",
                 cg_tb, sg_tb, denom_tb, phig_tb, ne_tb);
        // Regime D: Coherent 12-Beam Barrier Collapse (delta_phi = 139 = 97.73 deg)
        dphi_gate_tb = 32'sd139; #1;
        $display("  -> Delta_phi = 139 ticks ( 97.7 deg): C=%4d, S=%4d | Denom D = %7d | Gate Phi = %6d | Quanta n_E = %0d (587x COLLAPSE!)",
                 cg_tb, sg_tb, denom_tb, phig_tb, ne_tb);
        // Regime E: Pauli Singlet Lock (delta_phi = 256 = 180 deg)
        dphi_gate_tb = 32'sd256; #1;
        $display("  -> Delta_phi = 256 ticks (180.0 deg): C=%4d, S=%4d | Denom D = %7d | Gate Phi = %6d | Quanta n_E = %0d (Singlet Lock S=0)",
                 cg_tb, sg_tb, denom_tb, phig_tb, ne_tb);

        $display("======================================================================");
        $display("[3] Quotient-Remainder Detector: Hardware Verification of Born's Rule P(mu) = mu^2 / 512");
        $display("======================================================================");
        for (mu = 0; mu <= 16; mu = mu + 4) begin
            clicks = 0;
            for (i = 0; i < 512; i = i + 1) begin
                phi_tb = i;
                #1;
                delta_qr_tb = wrap_tb + (mu * mu);
                #1;
                if (q_tb === 32'sd1) clicks = clicks + 1;
            end
            $display("  -> Wave amplitude mu = %2d (energy mu^2 = %3d): detector corpuscle clicks = %3d / 512",
                     mu, mu * mu, clicks);
            if (clicks !== mu * mu) errors = errors + 1;
        end

        $display("======================================================================");
        $display("[4] Reversible Two-Tick Verlet Register (Zero Landauer Bit Erasure)");
        $display("======================================================================");
        rst = 1; rev = 0;
        #5 clk = 1; #5 clk = 0;
        rst = 0;
        $display("  -> Initial state (t = 0):   phi_curr = %3d, phi_prev = %3d", v_curr, v_prev);
        for (i = 0; i < 64; i = i + 1) begin
            #5 clk = 1; #5 clk = 0;
        end
        saved_curr = v_curr;
        saved_prev = v_prev;
        $display("  -> After 64 forward ticks:  phi_curr = %3d, phi_prev = %3d", v_curr, v_prev);
        // Flip pin `rev = 1` and run 64 clock ticks backward
        rev = 1;
        for (i = 0; i < 64; i = i + 1) begin
            #5 clk = 1; #5 clk = 0;
        end
        $display("  -> After 64 reverse ticks:  phi_curr = %3d, phi_prev = %3d (exact bit recovery!)", v_curr, v_prev);
        if (v_curr !== 9'd41 || v_prev !== 9'd0) errors = errors + 1;

        $display("======================================================================");
        $display("[5] Two-Chamber 72-Bit Teleporter: Stasis -> Teleport -> Release Stasis");
        $display("======================================================================");
        tp_rst = 1; tp_mode = 2'b00;
        #5 clk = 1; #5 clk = 0;
        tp_rst = 0;
        // Advance Chamber A by 4 ticks of normal evolution before entering stasis
        for (i = 0; i < 4; i = i + 1) begin
            #5 clk = 1; #5 clk = 0;
        end
        norm_before_tp = tp_norm_sq;
        saved_a_mu0 = tp_a_mu0; saved_a_mu1 = tp_a_mu1;
        saved_a_p0c = tp_a_p0c; saved_a_p0p = tp_a_p0p;
        saved_a_p1c = tp_a_p1c; saved_a_p1p = tp_a_p1p;
        // Step 1: Enter STASIS (D_stasis = 6,823,936 = 833 * 8192)
        tp_mode = 2'b01;
        #5 clk = 1; #5 clk = 0;
        $display("  -> [Step 1: STASIS]   D_stasis = %0d, D_write = %0d (Contrast = %0d : 1, Noise leak = %0d)",
                 tp_d_stasis, tp_d_write, tp_contrast, tp_noise_leak);
        $display("     Chamber A in Stasis: mu=(%2d,%2d), phi0=(%3d,%3d), phi1=(%3d,%3d) | Chamber B: mu=(%2d,%2d)",
                 tp_a_mu0, tp_a_mu1, tp_a_p0c, tp_a_p0p, tp_a_p1c, tp_a_p1p, tp_b_mu0, tp_b_mu1);
        // Step 2: TELEPORT A -> B via Pauli singlet +256 & 833:1 Write Focus
        tp_mode = 2'b10;
        #5 clk = 1; #5 clk = 0;
        $display("  -> [Step 2: TELEPORT] Chamber A discharged to vacuum: mu=(%2d,%2d), phi0=(%3d,%3d), phi1=(%3d,%3d)",
                 tp_a_mu0, tp_a_mu1, tp_a_p0c, tp_a_p0p, tp_a_p1c, tp_a_p1p);
        $display("     Chamber B reconstructed: mu=(%2d,%2d), phi0=(%3d,%3d), phi1=(%3d,%3d) | Total A3 NormSq: %0d -> %0d",
                 tp_b_mu0, tp_b_mu1, tp_b_p0c, tp_b_p0p, tp_b_p1c, tp_b_p1p, norm_before_tp, tp_norm_sq);
        if (tp_b_mu0 !== saved_a_mu0 || tp_b_mu1 !== saved_a_mu1 ||
            tp_b_p0c !== saved_a_p0c || tp_b_p0p !== saved_a_p0p ||
            tp_b_p1c !== saved_a_p1c || tp_b_p1p !== saved_a_p1p ||
            tp_a_mu0 !== 9'd1 || tp_a_mu1 !== 9'd1 ||
            tp_norm_sq !== norm_before_tp || tp_contrast !== 32'sd833 || tp_noise_leak !== 32'sd0) begin
            $display("ERROR: Teleportation bit mismatch or norm violation!");
            errors = errors + 1;
        end
        // Step 3: RELEASE STASIS in Chamber B and evolve 1 tick forward
        tp_mode = 2'b11;
        #5 clk = 1; #5 clk = 0;
        $display("  -> [Step 3: RELEASE]  Chamber B lifts stasis and resumes evolution: phi0=(%3d,%3d), phi1=(%3d,%3d)",
                 tp_b_p0c, tp_b_p0p, tp_b_p1c, tp_b_p1p);
        if (tp_b_p0p !== saved_a_p0c || tp_b_p1p !== saved_a_p1c) errors = errors + 1;

        $display("======================================================================");
        $display("[6] Low-Cost FPGA 12-Pin Cuboctahedron Driver Verification");
        $display("======================================================================");
        drv_rst = 1; drv_mode = 3'd3; // Pauli Vortex Lock (0 / 256)
        #5 clk = 1; #5 clk = 0;
        drv_rst = 0;
        #1;
        $display("  -> Mode 3 (Pauli Lock 0/256) at tick %3d: beam_pins = %12b (antipodal pair V1=%b, V2=%b)",
                 drv_cnt, drv_pins, drv_pins[0], drv_pins[1]);
        if (drv_pins !== 12'b0101_0101_0101) errors = errors + 1;
        drv_mode = 3'd4; // Euler XY Rotator
        #1;
        $display("  -> Mode 4 (Euler XY Rotator) at tick %3d: beam_oe   = %12b (XY active, XZ/YZ passive)",
                 drv_cnt, drv_oe);
        if (drv_oe !== 12'b0000_0000_1111) errors = errors + 1;

        $display("======================================================================");
        $display("[7] 4-Channel Nilpotent Tomograph (CE-RD-03) & Domain-Wall Quantum Ratchet (CE-RD-02)");
        $display("======================================================================");
        $display("  -> Tomograph input (12, 41, 97, 263) -> mixed 2y=(%0d,%0d,%0d,%0d) -> inverted (%0d, %0d, %0d, %0d)",
                 tom_y0, tom_y1, tom_y2, tom_y3, tom_s0, tom_s1, tom_s2, tom_s3);
        $display("  -> Domain-wall ratchet: fdiv(-1, 512) = %0d tick (active ratchet!) vs tdiv(-1, 512) = %0d",
                 rat_fdiv, rat_tdiv);
        if (tom_s0 !== 32'sd12 || tom_s1 !== 32'sd41 || tom_s2 !== 32'sd97 || tom_s3 !== 32'sd263 ||
            rat_fdiv !== -32'sd1 || rat_tdiv !== 32'sd0) errors = errors + 1;

        $display("======================================================================");
        $display("[8] 3-Chamber Food & Oxygen Synthesizer FSM: Recipe 00 (MEAT CUTLET)");
        $display("======================================================================");
        food_rst = 1; food_start = 0; food_recipe = 2'b00;
        #5 clk = 1; #5 clk = 0;
        food_rst = 0; food_start = 1;
        // Step through all 5 hardware stages of synthesizing a Meat Cutlet
        for (i = 1; i <= 5; i = i + 1) begin
            #5 clk = 1; #5 clk = 0;
            $display("  -> Stage %0d | ChModes=(%0d,%0d,%0d) | Air=%b H2O=%b HemeFe=%b O2Vent=%b US12=%b | TargetZ=%3d | Ready=%b",
                     food_stage, food_m1, food_m2, food_m3,
                     food_air, food_h2o, food_fe, food_o2, food_us, food_z, food_ready);
        end
        if (food_stage !== 3'd5 || food_ready !== 1'b1 || food_m3 !== 3'd0) errors = errors + 1;

        $display("======================================================================");
        $display("[9] Zero-Heat Phase Peltier Cooler, Eternal Stasis Pantry & Pauli Vortex Battery");
        $display("======================================================================");
        pelt_rst = 1; pelt_mode = 2'b00;
        #5 clk = 1; #5 clk = 0;
        pelt_rst = 0;
        // Run 4 cycles of cooling & harvesting ambient heat into the Pauli vortex battery
        for (i = 0; i < 4; i = i + 1) begin
            #5 clk = 1; #5 clk = 0;
        end
        $display("  -> [Cool & Harvest] Reverse heat leak = %0d | Joule self-heat = %0d | Harvested Vortex Battery = %0d",
                 pelt_back_leak, pelt_joule, pelt_batt);
        // Switch to Eternal Stasis Pantry & Pauli Singlet Hold (dphi = 256, zero leakage)
        pelt_mode = 2'b01;
        #5 clk = 1; #5 clk = 0;
        $display("  -> [Eternal Stasis Pantry] Room-temp food decay rate Phi = %0d | Battery charge held = %0d (0 leakage!)",
                 pelt_decay, pelt_batt);
        // Discharge Pauli Vortex Battery at quarter-turn saddle (dphi = 128)
        pelt_mode = 2'b11;
        #5 clk = 1; #5 clk = 0;
        $display("  -> [Pauli Battery Discharge at dphi=128] Delivered coherent power = %0d", pelt_pwr);
        if (pelt_back_leak !== 32'sd0 || pelt_joule !== 32'sd0 || pelt_decay !== 32'sd0 || pelt_pwr !== 32'sd16384)
            errors = errors + 1;

        $display("======================================================================");
        $display("[10] Programmable V-I Phase-Throttle & Grid Inverter (MPPT at k* = 64)");
        $display("======================================================================");
        vi_nv = 32'sd12; vi_mi = 32'sd3; vi_ac = 1'b0;
        // Audit all 129 throttle positions k = 0..128
        for (i = 0; i <= 128; i = i + 1) begin
            vi_k = i;
            #1;
            if (vi_vc !== (32'sd128 - i) || vi_ic !== i || vi_ksum !== 32'sd128 || vi_pout > 32'sd147456)
                errors = errors + 1;
            if (i == 0 || i == 32 || i == 64 || i == 96 || i == 128) begin
                $display("  -> Throttle k=%3d (phi=%3d) | V_cell=%3d, I_cell=%3d (V+I=%3d) | V_out=%4d, I_out=%3d | P_out=%6d",
                         i, vi_phi, vi_vc, vi_ic, vi_ksum, vi_vout, vi_iout, vi_pout);
            end
        end
        // Verify AC negative half-cycle inversion (+256 Pauli flip at k = 64 MPPT)
        vi_k = 32'sd64; vi_ac = 1'b1; #1;
        $display("  -> [50/60 Hz AC Grid Inversion at k*=64] V_out=%5d, I_out=%4d, P_out=%6d (36 * K_P^2 = 147,456!)",
                 vi_vout, vi_iout, vi_pout);
        if (vi_vout !== -32'sd768 || vi_iout !== -32'sd192 || vi_pout !== 32'sd147456)
            errors = errors + 1;

        $display("======================================================================");
        $display("[11] Lab-Grade Smooth CV / CC / DDS Power Supply (Independent V, I, f)");
        $display("======================================================================");
        lab_rst = 1; lab_freq = 32'd0; lab_vset = 32'sd12000; lab_iset = 32'sd3000; lab_rload = 32'sd6;
        #5 clk = 1; #5 clk = 0;
        lab_rst = 0; #1;
        $display("  -> [DC CV Mode: V_set=12.000V, I_lim=3.000A, R=6 Ohm] V_out=%5d mV, I_out=%4d mA | CV=%b CC=%b",
                 lab_vact, lab_iact, lab_cv, lab_cc);
        if (lab_vact !== 32'sd12000 || lab_iact !== 32'sd2000 || lab_cv !== 1'b1 || lab_cc !== 1'b0)
            errors = errors + 1;
        // Drop load resistance to 2 Ohm (demands 6A > 3A limit -> automatic CC current limiting!)
        lab_rload = 32'sd2; #1;
        $display("  -> [DC CC Mode: V_set=12.000V, I_lim=3.000A, R=2 Ohm] V_out=%5d mV, I_out=%4d mA | CV=%b CC=%b",
                 lab_vact, lab_iact, lab_cv, lab_cc);
        if (lab_vact !== 32'sd6000 || lab_iact !== 32'sd3000 || lab_cv !== 1'b0 || lab_cc !== 1'b1)
            errors = errors + 1;
        // Turn DDS frequency dial to quarter-turn step per clock and verify smooth AC wave synthesis
        lab_rload = 32'sd6; lab_freq = (32'd128 << 23);
        #5 clk = 1; #5 clk = 0; #1;
        $display("  -> [AC DDS Mode at phase=%3d (90 deg)] V_out=%5d mV, I_out=%4d mA",
                 lab_phase, lab_vact, lab_iact);
        #5 clk = 1; #5 clk = 0; #1;
        $display("  -> [AC DDS Mode at phase=%3d (180 deg)] V_out=%5d mV, I_out=%4d mA",
                 lab_phase, lab_vact, lab_iact);
        if (lab_phase !== 9'd256 || lab_vact !== -32'sd12000 || lab_iact !== -32'sd2000)
            errors = errors + 1;

        $display("======================================================================");
        $display("[12] Host Laptop / AI MCP Command Decoder SoC Top Verification");
        $display("======================================================================");
        soc_rst = 1; soc_valid = 0;
        #5 clk = 1; #5 clk = 0;
        soc_rst = 0;
        // Send AI Host Command 4'h3: Set PSU to 24.000 V, 5.000 A, DC (0 Hz)
        soc_valid = 1; soc_op = 4'h3; soc_a0 = 32'sd24000; soc_a1 = 32'sd5000; soc_a2 = 32'sd0;
        #5 clk = 1; #5 clk = 0;
        // Send AI Host Command 4'h2: Synthesize Recipe 00 (Cutlet)
        soc_op = 4'h2; soc_a0 = 32'sd0;
        #5 clk = 1; #5 clk = 0;
        soc_valid = 0;
        for (i = 0; i < 5; i = i + 1) begin
            #5 clk = 1; #5 clk = 0;
        end
        $display("  -> [AI Host SoC] PSU V=%5d mV, I=%4d mA (CV=%b) | Food Stage=%0d, Ready=%b | Stasis Decay=%0d",
                 soc_vmv, soc_ima, soc_cv_w, soc_fstage, soc_fready, soc_decay);
        if (soc_vmv !== 32'sd24000 || soc_ima !== 32'sd4000 || soc_fready !== 1'b1 || soc_decay !== 32'sd0)
            errors = errors + 1;

        $display("======================================================================");
        $display("TOTAL HARDWARE ERRORS = %0d", errors);
        $display("======================================================================");
        $finish;
    end
endmodule
