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
        $display("TOTAL HARDWARE ERRORS = %0d", errors);
        $display("======================================================================");
        $finish;
    end
endmodule
