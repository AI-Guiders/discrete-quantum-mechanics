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
        $display("TOTAL HARDWARE ERRORS = %0d", errors);
        $display("======================================================================");
        $finish;
    end
endmodule
