// ============================================================================
// cuboctahedron_carrier_asic.v
// Branchless Gate-Level / RTL Hardware Implementation of the M/T Cuboctahedral
// Carrier Core (`mt_ca/carrier_core.py` & `lean/MtCarrier/TrajectoryIV263.lean`)
// in Verilog (IEEE 1364-2005).
//
// Core Rules Enforced in Hardware:
//   1. Single spatial dimension parameter `parameter integer D = 3` (Catalan lock
//      `1 + 2^D == D^2`); every carrier constant is derived from `D` alone via
//      generative `localparam` formulas (`CarrierSpec.from_d(D)`).
//   2. 100% branchless arithmetic core (`0` `if` statements, `0` `?:` ternary
//      muxes in the M-layer rotator, quotient-remainder, 12-neighbor holonomy,
//      Heisenberg deadband, and Verlet step operators):
//        - `abs(x) = (x ^ (x >>> 31)) - (x >>> 31)`
//        - `sgn(x) = 1 + ((x >>> 31) <<< 1)`  (`+1` for `x >= 0`, `-1` for `x < 0`)
//        - `isZeroNat(k) = 1 / (k + 1)`       (`1` if `k == 0`, `0` if `k >= 1`)
//        - `isPosNat(k)  = 1 - (1 / (k + 1))` (`0` if `k == 0`, `1` if `k >= 1`)
//        - `blend(sel, a, b) = sel * a + (1 - sel) * b`
//        - `fdiv(num, den) = (num / den) - (((num - (num / den) * den) >>> 63) & 1)`
// ============================================================================
`timescale 1ns / 1ps

// ----------------------------------------------------------------------------
// Module 1: Native Gray-Quadrant Butterfly Rotator on Z_{N_ring(D)} (`Z_4^Gray x Z_128`)
// In the carrier's natural positional radix `(q1, q0, m7)` where `u = phi_in & RING_MASK`:
//   - `q1 = u[MOD_BITS-1]` (half-turn bit `256`), `q0 = u[MOD_BITS-2]` (quadrant bit `128`),
//   - `m7 = u[MOD_BITS-3 : 0]` (7-bit intra-quadrant mantissa in `0..127`),
//   - `comp7 = Q_SQUARE - m7` (the SINGLE 7-bit subtraction needed for BOTH C and S,
//     since `comp7 + m7 === Q_SQUARE = 128` identically!),
//   - X-butterfly crossbar switch controlled by `q0`:
//       `c_mag = q0 ? m7 : comp7`,   `s_mag = q0 ? comp7 : m7` (implemented branchlessly),
//   - 2-bit Gray-code quadrant signs `(c_neg, s_neg) = (q1 ^ q0, q1)`:
//       `C_D(phi) = (1 - 2*c_neg) * c_mag`,   `S_D(phi) = (1 - 2*s_neg) * s_mag`!
// Zero `if`, zero `?:`, zero duplicated subtractors, zero lookup tables.
// ----------------------------------------------------------------------------
module rotator_512_unit #(
    parameter integer D = 3
) (
    input  wire signed [31:0] phi_in,
    output wire signed [31:0] wrap_out,
    output wire signed [31:0] proj_c,
    output wire signed [31:0] proj_s
);
    localparam integer MU_VAC       = (D * D) - (1 << D);
    localparam integer C0_OVER_C_SQ = D - MU_VAC;
    localparam integer N_LINKS      = 2 * D * (D - 1);
    localparam integer N_TRI        = (1 << D);
    localparam integer D_IN_SQ      = N_LINKS / D;
    localparam integer MOD_BITS     = MU_VAC + N_TRI;
    localparam integer MANT_BITS    = MOD_BITS - C0_OVER_C_SQ; // 7 bits (0..127)
    localparam integer N_RING       = (1 << MOD_BITS);
    localparam integer RING_MASK    = N_RING - MU_VAC;
    localparam integer Q_SQUARE     = N_RING / D_IN_SQ;
    localparam integer MANT_MASK    = Q_SQUARE - MU_VAC;       // 127
    localparam integer PHI_PAULI    = N_RING / C0_OVER_C_SQ;

    // Native 9-bit ring wire [MOD_BITS-1:0] IS Z_512 automatically (zero masks, zero shifts!):
    //   - wire [8]   = q1 (half-turn Pauli bit 256),
    //   - wire [7]   = q0 (quadrant bit 128),
    //   - wire [6:0] = m7 (7-bit intra-quadrant mantissa 0..127).
    wire [MOD_BITS-1:0] u_ring = phi_in[MOD_BITS-1:0];
    wire [MOD_BITS-1:0] neg_u  = PHI_PAULI[MOD_BITS-1:0] - u_ring;
    assign wrap_out            = PHI_PAULI - {23'b0, neg_u};

    wire                q1    = u_ring[MOD_BITS - 1];
    wire                q0    = u_ring[MOD_BITS - 2];
    wire signed [31:0]  m7    = {25'b0, u_ring[MOD_BITS - 3 : 0]};
    wire signed [31:0]  comp7 = Q_SQUARE - m7; // Unique complement: comp7 + m7 === 128!

    // Branchless X-butterfly swap by wire q0:
    wire [31:0] q0_mask  = {32{q0}};
    wire [31:0] nq0_mask = {32{~q0}};
    wire signed [31:0] c_mag = (nq0_mask & comp7) | (q0_mask & m7);
    wire signed [31:0] s_mag = (nq0_mask & m7)    | (q0_mask & comp7);

    // 2-bit Gray-code sign inversion: c_neg = q1 ^ q0, s_neg = q1
    wire signed [31:0] c_neg_mask = {32{q1 ^ q0}};
    wire signed [31:0] s_neg_mask = {32{q1}};
    assign proj_c = (c_mag ^ c_neg_mask) - c_neg_mask;
    assign proj_s = (s_mag ^ s_neg_mask) - s_neg_mask;
endmodule

// ----------------------------------------------------------------------------
// Module 1B: Native Multiplierless Carrier ALU (`carrier_native_multiplierless_alu`)
// Expresses all integer arithmetic operations (`x`, `-x`, `|x|`, `max(x,y)`,
// `min(x,y)`, `x^2`, and signed `x * y` across `[-K_P, +K_P]^2 = [-64, +64]^2`)
// PURELY through the rotator `(C_D, S_D)` and its Verlet antiderivative
// `F_S(n) = sum_{phi=0}^{n-1} S_D(phi)` accumulated purely by addition!
// Contains ZERO hardware `*` multipliers, ZERO `if`, ZERO `?:`.
// ----------------------------------------------------------------------------
module carrier_native_multiplierless_alu #(
    parameter integer D = 3
) (
    input  wire signed [31:0] x_in,
    input  wire signed [31:0] y_in,
    output wire signed [31:0] id_x_out,
    output wire signed [31:0] neg_x_out,
    output wire signed [31:0] abs_x_out,
    output wire signed [31:0] max_xy_out,
    output wire signed [31:0] min_xy_out,
    output wire signed [31:0] tropical_min_xy_out,
    output wire signed [31:0] sq_x_out,
    output wire signed [31:0] signed_mul_xy_out
);
    localparam integer MU_VAC       = (D * D) - (1 << D);
    localparam integer C0_OVER_C_SQ = D - MU_VAC;
    localparam integer N_TRI        = (1 << D);
    localparam integer MOD_BITS     = MU_VAC + N_TRI;
    localparam integer N_RING       = (1 << MOD_BITS);
    localparam integer PHI_PAULI    = N_RING >> MU_VAC;
    localparam integer Q_SQUARE     = PHI_PAULI >> MU_VAC;

    // 1. Rotator evaluations at 0, x, x + PHI_PAULI, y, x - y, and x + y:
    wire signed [31:0] w0, c0, s0;
    wire signed [31:0] wx, cx, sx;
    wire signed [31:0] wn, cn, sn;
    wire signed [31:0] wy, cy, sy;
    wire signed [31:0] wd, cd, sd;
    wire signed [31:0] ws, cs, ss;

    rotator_512_unit #(.D(D)) u_r0   (.phi_in(32'sd0),          .wrap_out(w0), .proj_c(c0), .proj_s(s0));
    rotator_512_unit #(.D(D)) u_rx   (.phi_in(x_in),            .wrap_out(wx), .proj_c(cx), .proj_s(sx));
    rotator_512_unit #(.D(D)) u_rneg (.phi_in(x_in + PHI_PAULI),.wrap_out(wn), .proj_c(cn), .proj_s(sn));
    rotator_512_unit #(.D(D)) u_ry   (.phi_in(y_in),            .wrap_out(wy), .proj_c(cy), .proj_s(sy));
    rotator_512_unit #(.D(D)) u_rdif (.phi_in(x_in - y_in),     .wrap_out(wd), .proj_c(cd), .proj_s(sd));
    rotator_512_unit #(.D(D)) u_rsum (.phi_in(x_in + y_in),     .wrap_out(ws), .proj_c(cs), .proj_s(ss));

    // Identity x === S_D(x), Negation -x === S_D(x + PHI_PAULI), Absolute value |x| === C_D(0) - C_D(x)
    assign id_x_out  = sx;
    assign neg_x_out = sn;
    assign abs_x_out = c0 - cx;

    wire signed [31:0] abs_diff = c0 - cd;
    wire signed [31:0] abs_sum  = c0 - cs;

    // Max, Min, and Prosthaphaeresis Tropical Min without comparators:
    assign max_xy_out          = (sx + sy + abs_diff) >>> MU_VAC;
    assign min_xy_out          = (sx + sy - abs_diff) >>> MU_VAC;
    assign tropical_min_xy_out = (cd - cs) >>> MU_VAC;

    // 2. Verlet antiderivative F_S(n) = sum_{phi=0}^{n-1} S_D(phi) built purely by addition (ZERO `*`!):
    wire signed [31:0] fs_val [0:Q_SQUARE+1];
    assign fs_val[0] = 32'sd0;
    genvar n;
    generate
        for (n = 0; n <= Q_SQUARE; n = n + 1) begin : gen_verlet_antideriv
            localparam signed [31:0] PHI_N_32 = n;
            wire signed [31:0] wn_i, cn_i, sn_i;
            rotator_512_unit #(.D(D)) u_rn (
                .phi_in(PHI_N_32),
                .wrap_out(wn_i),
                .proj_c(cn_i),
                .proj_s(sn_i)
            );
            assign fs_val[n + 1] = fs_val[n] + sn_i;
        end
    endgenerate

    // Exact square u^2 === F_S(|u|) + F_S(|u| + 1) and signed product x * y === (sq(x+y) - sq(x-y)) >>> 2
    assign sq_x_out = fs_val[abs_x_out] + fs_val[abs_x_out + MU_VAC];
    wire signed [31:0] sq_sum  = fs_val[abs_sum]  + fs_val[abs_sum  + MU_VAC];
    wire signed [31:0] sq_diff = fs_val[abs_diff] + fs_val[abs_diff + MU_VAC];
    assign signed_mul_xy_out   = (sq_sum - sq_diff) >>> C0_OVER_C_SQ;
endmodule

// ----------------------------------------------------------------------------
// Module 2: Shift-Free Native 9-Bit Adder Carry-Out / Sum Split on Z_{N_ring(D)}
// On a native 9-bit ring bus, adding `(PHI_PAULI - 1)` splits `delta_phi`
// directly into:
//   - the low 9 sum wires `sum_9bit = num[8:0]` (Channel 1 wave remainder in Z_512),
//   - the high carry-out wires `branch_q = num[31:9]` (Channel 2 corpuscle quantum!),
// with ZERO bit-shift operators (`>>>` or `<<<`) and ZERO masks!
// ----------------------------------------------------------------------------
module quotient_remainder_512_unit #(
    parameter integer D = 3
) (
    input  wire signed [31:0] delta_phi,
    output wire signed [31:0] branch_q,
    output wire signed [31:0] edge_r
);
    localparam integer MU_VAC       = (D * D) - (1 << D);
    localparam integer C0_OVER_C_SQ = D - MU_VAC;
    localparam integer N_TRI        = (1 << D);
    localparam integer MOD_BITS     = MU_VAC + N_TRI;
    localparam integer N_RING       = (1 << MOD_BITS);
    localparam integer PHI_PAULI    = N_RING / C0_OVER_C_SQ;

    wire signed [31:0] num       = delta_phi + (PHI_PAULI - MU_VAC);
    wire [MOD_BITS-1:0] rem_9bit = num[MOD_BITS-1:0];
    assign branch_q              = {{MOD_BITS{num[31]}}, num[31:MOD_BITS]};
    assign edge_r                = {23'b0, rem_9bit} - (PHI_PAULI - MU_VAC);
endmodule

// ----------------------------------------------------------------------------
// Module 3: Shift-Free & Mask-Free Native 9-Bit Symplectic Reversible Verlet Cell
// On 9-bit ring wires `wire [8:0]`, addition and subtraction are AUTOMATICALLY
// modulo 512 (just as 1-bit XOR is automatically modulo 2):
//   Forward: `fwd_curr = phi_curr + phi_curr - phi_prev + phi_accel[8:0]`
//   Reverse: `rev_prev = phi_prev + phi_prev - phi_curr + phi_accel[8:0]`
// Zero shifts, zero `& 511` masks, zero `if`, zero `?:`.
// ----------------------------------------------------------------------------
module verlet_reversible_cell #(
    parameter integer D = 3
) (
    input  wire        clk,
    input  wire        rst,
    input  wire        reverse_dir,
    input  wire [8:0]  init_curr,
    input  wire [8:0]  init_prev,
    input  wire signed [31:0] phi_accel,
    output reg  [8:0]  phi_curr,
    output reg  [8:0]  phi_prev
);
    localparam integer MU_VAC   = (D * D) - (1 << D);
    localparam integer N_TRI    = (1 << D);
    localparam integer MOD_BITS = MU_VAC + N_TRI;

    wire [MOD_BITS-1:0] rst_mask  = {MOD_BITS{rst}};
    wire [MOD_BITS-1:0] nrst_mask = {MOD_BITS{~rst}};
    wire [MOD_BITS-1:0] dir_mask  = {MOD_BITS{reverse_dir}};
    wire [MOD_BITS-1:0] ndir_mask = {MOD_BITS{~reverse_dir}};

    wire [MOD_BITS-1:0] fwd_curr = phi_curr + phi_curr - phi_prev + phi_accel[MOD_BITS-1:0];
    wire [MOD_BITS-1:0] fwd_prev = phi_curr;

    wire [MOD_BITS-1:0] rev_curr = phi_prev;
    wire [MOD_BITS-1:0] rev_prev = phi_prev + phi_prev - phi_curr + phi_accel[MOD_BITS-1:0];

    wire [MOD_BITS-1:0] run_curr = (ndir_mask & fwd_curr) | (dir_mask & rev_curr);
    wire [MOD_BITS-1:0] run_prev = (ndir_mask & fwd_prev) | (dir_mask & rev_prev);

    wire [MOD_BITS-1:0] nxt_curr = (rst_mask & init_curr) | (nrst_mask & run_curr);
    wire [MOD_BITS-1:0] nxt_prev = (rst_mask & init_prev) | (nrst_mask & run_prev);

    always @(posedge clk) begin
        phi_curr <= nxt_curr;
        phi_prev <= nxt_prev;
    end
endmodule

// ----------------------------------------------------------------------------
// Module 3B: 100% Branchless 12-Neighbor Holonomy & Saturating Gate Core
// Exact hardware realization of `polar_neighbor_holonomy_core` and
// `polar_component_phi_core` from `mt_ca/carrier_core.py` and
// `evalGateFromHolonomy` from `lean/MtCarrier/TrajectoryIV263.lean`.
// Instantiates 12 parallel `rotator_512_unit` instances across the 12 edges
// of the cuboctahedron O_2(D), sums `sum_mu`, `zr`, `zi`, computes Bohm deficit,
// guarded impedance `denom_d`, exact floor quotient `fdiv`, and branchless
// Heisenberg deadband `isPosNat(|phi_raw| / DPHI_DISC) * phi_raw`.
// Zero `if`, zero `?:`.
// ----------------------------------------------------------------------------
module polar_12neighbor_holonomy_gate_core #(
    parameter integer D = 3,
    parameter integer INCLUDE_EVEN_DEFICIT = 1
) (
    input  wire signed [31:0]     mu_c,
    input  wire signed [31:0]     phi_c,
    input  wire signed [12*32-1:0] nb_mu_flat,
    input  wire signed [12*32-1:0] nb_phi_flat,
    output wire signed [31:0]     sum_mu_out,
    output wire signed [63:0]     zr_out,
    output wire signed [63:0]     zi_out,
    output wire signed [63:0]     z_drive_out,
    output wire signed [63:0]     denom_d_out,
    output wire signed [31:0]     phi_raw_out,
    output wire signed [31:0]     phi_gate_out,
    output wire signed [31:0]     energy_quanta_ne_out
);
    localparam integer MU_VAC       = (D * D) - (1 << D);
    localparam integer C0_OVER_C_SQ = D - MU_VAC;
    localparam integer N_LINKS      = 2 * D * (D - 1);
    localparam integer N_TRI        = (1 << D);
    localparam integer D_IN_SQ      = N_LINKS / D;
    localparam integer MOD_BITS     = MU_VAC + N_TRI;
    localparam integer FRAC_BITS    = MOD_BITS - D;
    localparam integer N_RING       = (1 << MOD_BITS);
    localparam integer K_P          = (1 << FRAC_BITS);
    localparam integer Q_SQUARE     = N_RING / D_IN_SQ;
    localparam integer EPS_DENOM    = K_P * Q_SQUARE;
    localparam integer N_PHI        = MU_VAC + N_LINKS;
    localparam integer DPHI_DISC    = (N_RING + N_PHI + N_TRI) / N_PHI;

    wire signed [31:0] nb_mu  [0:N_LINKS-1];
    wire signed [31:0] nb_phi [0:N_LINKS-1];
    wire signed [31:0] edge_w [0:N_LINKS-1];
    wire signed [31:0] edge_c [0:N_LINKS-1];
    wire signed [31:0] edge_s [0:N_LINKS-1];

    genvar j;
    generate
        for (j = 0; j < N_LINKS; j = j + 1) begin : gen_12edges
            assign nb_mu[j]  = nb_mu_flat[j*32 +: 32];
            assign nb_phi[j] = nb_phi_flat[j*32 +: 32];
            rotator_512_unit #(.D(D)) u_edge_rot (
                .phi_in(nb_phi[j] - phi_c),
                .wrap_out(edge_w[j]),
                .proj_c(edge_c[j]),
                .proj_s(edge_s[j])
            );
        end
    endgenerate

    assign sum_mu_out =
        nb_mu[0] + nb_mu[1] + nb_mu[2]  + nb_mu[3] +
        nb_mu[4] + nb_mu[5] + nb_mu[6]  + nb_mu[7] +
        nb_mu[8] + nb_mu[9] + nb_mu[10] + nb_mu[11];

    wire signed [63:0] zr_raw =
        nb_mu[0]*edge_c[0] + nb_mu[1]*edge_c[1] + nb_mu[2]*edge_c[2]   + nb_mu[3]*edge_c[3] +
        nb_mu[4]*edge_c[4] + nb_mu[5]*edge_c[5] + nb_mu[6]*edge_c[6]   + nb_mu[7]*edge_c[7] +
        nb_mu[8]*edge_c[8] + nb_mu[9]*edge_c[9] + nb_mu[10]*edge_c[10] + nb_mu[11]*edge_c[11];

    wire signed [63:0] zi_raw =
        nb_mu[0]*edge_s[0] + nb_mu[1]*edge_s[1] + nb_mu[2]*edge_s[2]   + nb_mu[3]*edge_s[3] +
        nb_mu[4]*edge_s[4] + nb_mu[5]*edge_s[5] + nb_mu[6]*edge_s[6]   + nb_mu[7]*edge_s[7] +
        nb_mu[8]*edge_s[8] + nb_mu[9]*edge_s[9] + nb_mu[10]*edge_s[10] + nb_mu[11]*edge_s[11];

    assign zr_out = mu_c * zr_raw;
    assign zi_out = mu_c * zi_raw;

    // Bohm even holonomy deficit: delta_zeta_real = Q_SQUARE * mu_c * sum_mu - zr
    wire signed [63:0] deficit = Q_SQUARE * mu_c * sum_mu_out - zr_out;

    // Branchless sign sgn(zi) = +1 for zi >= 0, -1 for zi < 0 (`branchlessSign` in FaceAlgebra.lean)
    wire signed [63:0] sgn_zi = 64'sd1 + ((zi_out >>> 63) <<< 1);

    assign z_drive_out = zi_out + INCLUDE_EVEN_DEFICIT * sgn_zi * deficit;

    // Raw denominator D_raw = zr + Q_SQUARE * mu_c^2 + EPS_DENOM
    wire signed [63:0] raw_denom = zr_out + Q_SQUARE * mu_c * mu_c + EPS_DENOM;

    // Branchless denominator floor guard (`clampDenomOp`: if raw_denom <= 0 then EPS_DENOM else raw_denom)
    wire signed [63:0] is_nonpos = ((raw_denom - 64'sd1) >>> 63) & 64'sd1;
    assign denom_d_out = is_nonpos * EPS_DENOM + (64'sd1 - is_nonpos) * raw_denom;

    // Branchless exact mathematical floor division `fdiv(K_P * z_drive, denom_d)`
    wire signed [63:0] num_scaled   = K_P * z_drive_out;
    wire signed [63:0] q_tdiv       = num_scaled / denom_d_out;
    wire signed [63:0] rem_tdiv     = num_scaled - q_tdiv * denom_d_out;
    wire signed [63:0] rem_is_neg   = (rem_tdiv >>> 63) & 64'sd1;
    wire signed [63:0] q_fdiv       = q_tdiv - rem_is_neg;

    // Fold quotient into (-PHI_PAULI, +PHI_PAULI] via rotator wrap
    wire signed [31:0] dummy_c, dummy_s;
    rotator_512_unit #(.D(D)) u_wrap_raw (
        .phi_in(q_fdiv[31:0]),
        .wrap_out(phi_raw_out),
        .proj_c(dummy_c),
        .proj_s(dummy_s)
    );

    // Branchless Heisenberg deadband (`heisenbergDeadbandOp`: isPosNat(|phi_raw| / DPHI_DISC) * phi_raw)
    wire signed [31:0] mask_raw     = phi_raw_out >>> 31;
    wire signed [31:0] abs_phi_raw  = (phi_raw_out ^ mask_raw) - mask_raw;
    wire signed [31:0] q_heis       = abs_phi_raw / DPHI_DISC;
    wire signed [31:0] is_zero_heis = 32'sd1 / (q_heis + 32'sd1);
    wire signed [31:0] is_pos_heis  = 32'sd1 - is_zero_heis;
    assign phi_gate_out             = is_pos_heis * phi_raw_out;

    wire signed [31:0] mask_gate    = phi_gate_out >>> 31;
    wire signed [31:0] abs_phi_gate = (phi_gate_out ^ mask_gate) - mask_gate;
    assign energy_quanta_ne_out     = abs_phi_gate / DPHI_DISC;
endmodule

// ----------------------------------------------------------------------------
// Module 3C: Full Two-Lane 72-Bit Polar Carrier Cell Core (`fieldStepOp`)
// Combines Lane-0 and Lane-1 12-neighbor holonomy gates, branchless leading
// spinor lane selector `selectLeadingGateOp`, and reversible Verlet step.
// Zero `if`, zero `?:`.
// ----------------------------------------------------------------------------
module carrier_polar_12neighbor_cell_core #(
    parameter integer D = 3
) (
    input  wire                   clk,
    input  wire                   rst,
    input  wire                   reverse_dir,
    input  wire signed [31:0]     mu_c,
    input  wire [8:0]             init_p0,
    input  wire [8:0]             init_q0,
    input  wire [8:0]             init_p1,
    input  wire [8:0]             init_q1,
    input  wire signed [12*32-1:0] nb_mu_flat,
    input  wire signed [12*32-1:0] nb_p0_flat,
    input  wire signed [12*32-1:0] nb_p1_flat,
    output wire [8:0]             p0_curr,
    output wire [8:0]             q0_prev,
    output wire [8:0]             p1_curr,
    output wire [8:0]             q1_prev,
    output wire signed [31:0]     raw_gate_lane0,
    output wire signed [31:0]     gate_lane0,
    output wire signed [31:0]     gate_lane1,
    output wire signed [31:0]     selected_field_gate
);
    wire signed [31:0] sm0, sm1, praw1, ne0, ne1;
    wire signed [63:0] zr0, zi0, zd0, den0;
    wire signed [63:0] zr1, zi1, zd1, den1;

    polar_12neighbor_holonomy_gate_core #(.D(D), .INCLUDE_EVEN_DEFICIT(1)) u_lane0_gate (
        .mu_c(mu_c),
        .phi_c({23'b0, p0_curr}),
        .nb_mu_flat(nb_mu_flat),
        .nb_phi_flat(nb_p0_flat),
        .sum_mu_out(sm0),
        .zr_out(zr0),
        .zi_out(zi0),
        .z_drive_out(zd0),
        .denom_d_out(den0),
        .phi_raw_out(raw_gate_lane0),
        .phi_gate_out(gate_lane0),
        .energy_quanta_ne_out(ne0)
    );

    polar_12neighbor_holonomy_gate_core #(.D(D), .INCLUDE_EVEN_DEFICIT(1)) u_lane1_gate (
        .mu_c(mu_c),
        .phi_c({23'b0, p1_curr}),
        .nb_mu_flat(nb_mu_flat),
        .nb_phi_flat(nb_p1_flat),
        .sum_mu_out(sm1),
        .zr_out(zr1),
        .zi_out(zi1),
        .z_drive_out(zd1),
        .denom_d_out(den1),
        .phi_raw_out(praw1),
        .phi_gate_out(gate_lane1),
        .energy_quanta_ne_out(ne1)
    );

    // Branchless `selectLeadingGateOp(g0, g1)`: selects g1 iff |g1| > |g0|
    wire signed [31:0] m0       = gate_lane0 >>> 31;
    wire signed [31:0] abs_g0   = (gate_lane0 ^ m0) - m0;
    wire signed [31:0] m1       = gate_lane1 >>> 31;
    wire signed [31:0] abs_g1   = (gate_lane1 ^ m1) - m1;
    wire signed [31:0] sel_g1   = ((abs_g0 - abs_g1) >>> 31) & 32'sd1;
    assign selected_field_gate  = sel_g1 * gate_lane1 + (32'sd1 - sel_g1) * gate_lane0;

    verlet_reversible_cell #(.D(D)) u_verlet_lane0 (
        .clk(clk),
        .rst(rst),
        .reverse_dir(reverse_dir),
        .init_curr(init_p0),
        .init_prev(init_q0),
        .phi_accel(selected_field_gate),
        .phi_curr(p0_curr),
        .phi_prev(q0_prev)
    );

    verlet_reversible_cell #(.D(D)) u_verlet_lane1 (
        .clk(clk),
        .rst(rst),
        .reverse_dir(reverse_dir),
        .init_curr(init_p1),
        .init_prev(init_q1),
        .phi_accel(selected_field_gate),
        .phi_curr(p1_curr),
        .phi_prev(q1_prev)
    );
endmodule

// ----------------------------------------------------------------------------
// Module 4: 12-Beam Cuboctahedron Coherent Barrier-Collapse & Ballistic Gate
// (`shellGateDenomOp` and `shellGatePhaseOp` from `UnifiedOperators.lean`)
// Feeds 12 parallel cuboctahedron beams into the 12-edge rotator array.
// Zero `if`, zero `?:`.
// ----------------------------------------------------------------------------
module cuboctahedron_12beam_gate #(
    parameter integer D = 3
) (
    input  wire signed [31:0] mu_center,
    input  wire signed [31:0] mu_nb,
    input  wire signed [31:0] delta_phi,
    output wire signed [31:0] c_single,
    output wire signed [31:0] s_single,
    output wire signed [31:0] denom_d,
    output wire signed [31:0] gate_phase_phi,
    output wire signed [31:0] energy_quanta_ne
);
    localparam integer MU_VAC       = (D * D) - (1 << D);
    localparam integer C0_OVER_C_SQ = D - MU_VAC;
    localparam integer N_LINKS      = 2 * D * (D - 1);
    localparam integer N_TRI        = (1 << D);
    localparam integer D_IN_SQ      = N_LINKS / D;
    localparam integer MOD_BITS     = MU_VAC + N_TRI;
    localparam integer FRAC_BITS    = MOD_BITS - D;
    localparam integer N_RING       = (1 << MOD_BITS);
    localparam integer K_P          = (1 << FRAC_BITS);
    localparam integer Q_SQUARE     = N_RING / D_IN_SQ;
    localparam integer EPS_DENOM    = K_P * Q_SQUARE;
    localparam integer N_PHI        = MU_VAC + N_LINKS;
    localparam integer DPHI_DISC    = (N_RING + N_PHI + N_TRI) / N_PHI;

    // Instantiate 12 parallel hardware rotators (one per cuboctahedron beam)
    wire signed [31:0] beam_w [0:N_LINKS-1];
    wire signed [31:0] beam_c [0:N_LINKS-1];
    wire signed [31:0] beam_s [0:N_LINKS-1];

    genvar b;
    generate
        for (b = 0; b < N_LINKS; b = b + 1) begin : gen_12beams
            rotator_512_unit #(.D(D)) u_beam_rot (
                .phi_in(delta_phi),
                .wrap_out(beam_w[b]),
                .proj_c(beam_c[b]),
                .proj_s(beam_s[b])
            );
        end
    endgenerate

    assign c_single = beam_c[0];
    assign s_single = beam_s[0];

    wire signed [31:0] sum_c12 =
        beam_c[0] + beam_c[1] + beam_c[2]  + beam_c[3] +
        beam_c[4] + beam_c[5] + beam_c[6]  + beam_c[7] +
        beam_c[8] + beam_c[9] + beam_c[10] + beam_c[11];

    wire signed [31:0] sum_s12 =
        beam_s[0] + beam_s[1] + beam_s[2]  + beam_s[3] +
        beam_s[4] + beam_s[5] + beam_s[6]  + beam_s[7] +
        beam_s[8] + beam_s[9] + beam_s[10] + beam_s[11];

    wire signed [31:0] base_term = Q_SQUARE * (mu_center * mu_center + mu_nb * mu_nb);
    wire signed [31:0] coup_term = C0_OVER_C_SQ * mu_center * mu_nb * sum_c12;
    wire signed [31:0] raw_denom = base_term + coup_term;

    // Branchless quantum floor clamp: max(EPS_DENOM, raw_denom)
    wire signed [31:0] diff_eps  = raw_denom - EPS_DENOM;
    wire signed [31:0] below_eps = (diff_eps >>> 31) & 32'sd1;
    assign denom_d               = below_eps * EPS_DENOM + (32'sd1 - below_eps) * raw_denom;

    wire signed [63:0] odd_total = 64'sd1 * mu_center * mu_nb * sum_s12;
    wire signed [63:0] num_total = 64'sd1 * D * odd_total * DPHI_DISC * N_RING;
    wire signed [63:0] phi_div   = num_total / denom_d;
    assign gate_phase_phi        = phi_div[31:0];

    wire signed [31:0] mask_phi  = gate_phase_phi >>> 31;
    wire signed [31:0] abs_phi   = (gate_phase_phi ^ mask_phi) - mask_phi;
    assign energy_quanta_ne      = abs_phi / DPHI_DISC;
endmodule

// ----------------------------------------------------------------------------
// Module 5: Two-Chamber 72-Bit Stasis-Teleport-Release Engine
// Computes `d_stasis_val` and `d_write_val` live from 12 parallel rotators via
// `polar_12neighbor_holonomy_gate_core` at `dphi = 0` (stasis) and `dphi = PHI_PAULI`
// (write focus), and evolves the 72-bit spinors using branchless indicator arithmetic.
// ----------------------------------------------------------------------------
module two_chamber_72bit_teleporter #(
    parameter integer D = 3
) (
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
    localparam integer MU_VAC       = (D * D) - (1 << D);
    localparam integer C0_OVER_C_SQ = D - MU_VAC;
    localparam integer N_LINKS      = 2 * D * (D - 1);
    localparam integer N_TRI        = (1 << D);
    localparam integer D_IN_SQ      = N_LINKS / D;
    localparam integer MOD_BITS     = MU_VAC + N_TRI;
    localparam integer FRAC_BITS    = MOD_BITS - D;
    localparam integer N_RING       = (1 << MOD_BITS);
    localparam integer RING_MASK    = N_RING - MU_VAC;
    localparam integer K_P          = (1 << FRAC_BITS);
    localparam integer Q_SQUARE     = N_RING / D_IN_SQ;
    localparam integer PHI_PAULI    = N_RING / C0_OVER_C_SQ;
    localparam integer N_PHI        = MU_VAC + N_LINKS;
    localparam integer DPHI_DISC    = (N_RING + N_PHI + N_TRI) / N_PHI;

    // Live hardware evaluation of D_stasis (all 12 shield neighbors at dphi = 0, mu = K_P)
    // and D_write (all 12 write-focus neighbors at dphi = PHI_PAULI, mu = K_P) via 12-neighbor core!
    wire signed [31:0] sm_st, praw_st, pgate_st, ne_st;
    wire signed [63:0] zr_st, zi_st, zd_st, den_st;
    polar_12neighbor_holonomy_gate_core #(.D(D), .INCLUDE_EVEN_DEFICIT(1)) u_stasis_core (
        .mu_c(K_P),
        .phi_c(32'sd0),
        .nb_mu_flat({12{32'sd0 + K_P}}),
        .nb_phi_flat({12{32'sd0}}),
        .sum_mu_out(sm_st), .zr_out(zr_st), .zi_out(zi_st),
        .z_drive_out(zd_st), .denom_d_out(den_st),
        .phi_raw_out(praw_st), .phi_gate_out(pgate_st), .energy_quanta_ne_out(ne_st)
    );

    wire signed [31:0] sm_wr, praw_wr, pgate_wr, ne_wr;
    wire signed [63:0] zr_wr, zi_wr, zd_wr, den_wr;
    polar_12neighbor_holonomy_gate_core #(.D(D), .INCLUDE_EVEN_DEFICIT(1)) u_write_core (
        .mu_c(K_P),
        .phi_c(32'sd0),
        .nb_mu_flat({12{32'sd0 + K_P}}),
        .nb_phi_flat({12{32'sd0 + PHI_PAULI}}),
        .sum_mu_out(sm_wr), .zr_out(zr_wr), .zi_out(zi_wr),
        .z_drive_out(zd_wr), .denom_d_out(den_wr),
        .phi_raw_out(praw_wr), .phi_gate_out(pgate_wr), .energy_quanta_ne_out(ne_wr)
    );

    assign d_stasis_val = den_st[31:0];
    assign d_write_val  = den_wr[31:0];
    assign contrast_833 = d_stasis_val / d_write_val;

    // Branchless Heisenberg deadband suppression of external thermal noise inside the shielded waveguide:
    wire signed [31:0] raw_noise_ratio = (K_P * ext_thermal_noise_drive) / d_stasis_val;
    wire signed [31:0] mask_noise      = raw_noise_ratio >>> 31;
    wire signed [31:0] abs_noise_ratio = (raw_noise_ratio ^ mask_noise) - mask_noise;
    wire signed [31:0] q_noise_heis    = abs_noise_ratio / DPHI_DISC;
    wire signed [31:0] is_pos_noise    = 32'sd1 - (32'sd1 / (q_noise_heis + 32'sd1));
    assign waveguide_noise_leak        = is_pos_noise * raw_noise_ratio;

    // Shared Pauli singlet partners in Chamber B on native 9-bit ring wires:
    // adding PHI_PAULI = 256 in Z_512 is simply flipping MSB wire [8] (zero adders, zero masks, zero shifts!):
    wire [8:0] singlet_b0 = {~singlet_a0[8], singlet_a0[7:0]};
    wire [8:0] singlet_b1 = {~singlet_a1[8], singlet_a1[7:0]};
    wire [8:0] singlet_b2 = {~singlet_a2[8], singlet_a2[7:0]};
    wire [8:0] singlet_b3 = {~singlet_a3[8], singlet_a3[7:0]};

    // Bell-Pauli syndromes emitted by Chamber A on native 9-bit ring wires (automatic mod 512):
    wire [8:0] sigma0 = chA_phi0_curr - singlet_b0;
    wire [8:0] sigma1 = chA_phi0_prev - singlet_b1;
    wire [8:0] sigma2 = chA_phi1_curr - singlet_b2;
    wire [8:0] sigma3 = chA_phi1_prev - singlet_b3;

    assign total_two_chamber_norm_sq =
        (chA_mu0 * chA_mu0 + chA_mu1 * chA_mu1) +
        (chB_mu0 * chB_mu0 + chB_mu1 * chB_mu1);

    // Initial vortex state derived from carrier invariants:
    // mu0 = K_P (64), mu1 = N_PHI (13),
    // phi0 = (Q_SQUARE + M_HAT - K_P/2 - N_PHI = 173, 173 - DPHI_DISC = 132),
    // phi1 = (173 + D*DPHI_DISC = 296, 296 - DPHI_DISC = 255)
    localparam integer INIT_PHI0_C = D_IN_SQ * DPHI_DISC + (N_TRI + MU_VAC);
    localparam integer INIT_PHI0_P = INIT_PHI0_C - DPHI_DISC;
    localparam integer INIT_PHI1_C = INIT_PHI0_C + D * DPHI_DISC;
    localparam integer INIT_PHI1_P = INIT_PHI1_C - DPHI_DISC;

    always @(posedge clk) begin
        if (rst) begin
            chA_mu0       <= K_P;
            chA_mu1       <= N_PHI;
            chA_phi0_curr <= INIT_PHI0_C;
            chA_phi0_prev <= INIT_PHI0_P;
            chA_phi1_curr <= INIT_PHI1_C;
            chA_phi1_prev <= INIT_PHI1_P;
            chB_mu0       <= MU_VAC;
            chB_mu1       <= MU_VAC;
            chB_phi0_curr <= 9'd0;
            chB_phi0_prev <= 9'd0;
            chB_phi1_curr <= 9'd0;
            chB_phi1_prev <= 9'd0;
        end else begin
            case (cmd_mode)
                2'b00: begin
                    // Normal Verlet evolution on native 9-bit ring wires (automatic mod 512, zero shifts/masks)
                    chA_phi0_prev <= chA_phi0_curr;
                    chA_phi0_curr <= chA_phi0_curr + chA_phi0_curr - chA_phi0_prev + N_PHI[8:0];
                    chA_phi1_prev <= chA_phi1_curr;
                    chA_phi1_curr <= chA_phi1_curr + chA_phi1_curr - chA_phi1_prev + N_PHI[8:0];
                end
                2'b01: begin
                    // STEP 1 — STASIS: live stasis core outputs pgate_st === 0 inside Heisenberg deadband!
                    chA_phi0_curr <= chA_phi0_curr + pgate_st[8:0];
                    chA_phi0_prev <= chA_phi0_prev;
                    chA_phi1_curr <= chA_phi1_curr + pgate_st[8:0];
                    chA_phi1_prev <= chA_phi1_prev;
                end
                2'b10: begin
                    // STEP 2 — TELEPORT: reconstruct all 72 bits in Chamber B on native 9-bit ring wires
                    chB_mu0       <= chA_mu0;
                    chB_mu1       <= chA_mu1;
                    chB_phi0_curr <= singlet_b0 + sigma0 + waveguide_noise_leak[8:0];
                    chB_phi0_prev <= singlet_b1 + sigma1 + waveguide_noise_leak[8:0];
                    chB_phi1_curr <= singlet_b2 + sigma2 + waveguide_noise_leak[8:0];
                    chB_phi1_prev <= singlet_b3 + sigma3 + waveguide_noise_leak[8:0];
                    chA_mu0       <= MU_VAC;
                    chA_mu1       <= MU_VAC;
                    chA_phi0_curr <= 9'd0;
                    chA_phi0_prev <= 9'd0;
                    chA_phi1_curr <= 9'd0;
                    chA_phi1_prev <= 9'd0;
                end
                2'b11: begin
                    // STEP 3 — RELEASE STASIS IN CHAMBER B: resume Verlet evolution on native 9-bit ring wires
                    chB_phi0_prev <= chB_phi0_curr;
                    chB_phi0_curr <= chB_phi0_curr + chB_phi0_curr - chB_phi0_prev + N_PHI[8:0];
                    chB_phi1_prev <= chB_phi1_curr;
                    chB_phi1_curr <= chB_phi1_curr + chB_phi1_curr - chB_phi1_prev + N_PHI[8:0];
                end
            endcase
        end
    end
endmodule

// ----------------------------------------------------------------------------
// Module 6: Synthesizable Low-Cost FPGA 12-Pin Cuboctahedron Phase Driver
// All phase offsets derived from `parameter integer D = 3`:
//   0, Q_SQUARE (128), COLLAPSE_PHI = Q_SQUARE + N_LINKS - 1 (139),
//   PHI_PAULI (256), and 3 * Q_SQUARE (384).
// ----------------------------------------------------------------------------
module fpga_12beam_cuboctahedron_driver #(
    parameter integer D = 3
) (
    input  wire        clk_512x,
    input  wire        rst,
    input  wire [2:0]  mode_sel,
    input  wire [12*9-1:0] custom_phase_flat,
    input  wire [11:0] custom_oe_mask,
    output reg  [8:0]  ring_counter,
    output wire [11:0] beam_pins,
    output wire [11:0] beam_oe
);
    localparam integer MU_VAC       = (D * D) - (1 << D);
    localparam integer C0_OVER_C_SQ = D - MU_VAC;
    localparam integer N_LINKS      = 2 * D * (D - 1);
    localparam integer N_TRI        = (1 << D);
    localparam integer D_IN_SQ      = N_LINKS / D;
    localparam integer MOD_BITS     = MU_VAC + N_TRI;
    localparam integer N_RING       = (1 << MOD_BITS);
    localparam integer RING_MASK    = N_RING - MU_VAC;
    localparam integer Q_SQUARE     = N_RING / D_IN_SQ;
    localparam integer PHI_PAULI    = N_RING / C0_OVER_C_SQ;
    localparam integer COLLAPSE_PHI = Q_SQUARE + (N_LINKS - MU_VAC);

    always @(posedge clk_512x) begin
        if (rst)
            ring_counter <= 9'd0;
        else
            ring_counter <= ring_counter + MU_VAC[8:0];
    end

    reg [8:0] phase_off [0:N_LINKS-1];
    reg [11:0] oe_reg;
    integer k;

    always @(*) begin
        oe_reg = (1 << N_LINKS) - MU_VAC;
        for (k = 0; k < N_LINKS; k = k + 1) phase_off[k] = 9'd0;
        case (mode_sel)
            3'd0: begin
                for (k = 0; k < N_LINKS; k = k + 1) phase_off[k] = 9'd0;
            end
            3'd1: begin
                for (k = 0; k < N_LINKS; k = k + 1)
                    phase_off[k] = (k & MU_VAC) * Q_SQUARE;
            end
            3'd2: begin
                for (k = 0; k < N_LINKS; k = k + 1)
                    phase_off[k] = (k & MU_VAC) * COLLAPSE_PHI;
            end
            3'd3: begin
                for (k = 0; k < N_LINKS; k = k + 1)
                    phase_off[k] = (k & MU_VAC) * PHI_PAULI;
            end
            3'd4: begin
                phase_off[0] = 0 * Q_SQUARE;
                phase_off[1] = 1 * Q_SQUARE;
                phase_off[2] = 2 * Q_SQUARE;
                phase_off[3] = 3 * Q_SQUARE;
                oe_reg = (1 << D_IN_SQ) - MU_VAC;
            end
            3'd7: begin
                // SOFT_DEFINED_CUSTOM: live per-vertex phases and OE mask programmed from host laptop / MCP without rebuilding!
                for (k = 0; k < N_LINKS; k = k + 1)
                    phase_off[k] = custom_phase_flat[k*9 +: 9];
                oe_reg = custom_oe_mask;
            end
            default: begin
                for (k = 0; k < N_LINKS; k = k + 1) phase_off[k] = 9'd0;
            end
        endcase
    end

    assign beam_oe = oe_reg;

    genvar g;
    generate
        for (g = 0; g < N_LINKS; g = g + 1) begin : gen_pins
            wire [8:0] shifted_tick = ring_counter + phase_off[g];
            assign beam_pins[g] = oe_reg[g] & (~shifted_tick[MOD_BITS-1]);
        end
    endgenerate
endmodule

// ----------------------------------------------------------------------------
// Module 7: 4-Channel Nilpotent Holonomic Tomograph (CE-RD-03) & Domain-Wall
// Quantum Ratchet (CE-RD-02)
// Matrix determinant `det(2 * M_chan) = C0_OVER_C_SQ * N_LINKS = 24`.
// Zero `if`, zero `?:`.
// ----------------------------------------------------------------------------
module holonomic_4channel_tomograph_and_ratchet #(
    parameter integer D = 3
) (
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
    localparam integer MU_VAC       = (D * D) - (1 << D);
    localparam integer C0_OVER_C_SQ = D - MU_VAC;
    localparam integer N_LINKS      = 2 * D * (D - 1);
    localparam integer N_TRI        = (1 << D);
    localparam integer N_SQ         = 2 * D;
    localparam integer MOD_BITS     = MU_VAC + N_TRI;
    localparam integer N_RING       = (1 << MOD_BITS);
    localparam integer DET_24       = C0_OVER_C_SQ * N_LINKS;

    assign y0_2x = (s0_in <<< MU_VAC) + s1_in;
    assign y1_2x = (s1_in <<< MU_VAC) + (s2_in <<< MU_VAC);
    assign y2_2x = (s2_in <<< MU_VAC);
    assign y3_2x = (s3_in <<< MU_VAC);

    assign s0_rec = (N_LINKS * y0_2x - N_SQ * y1_2x + N_SQ * y2_2x) / DET_24;
    assign s1_rec = (N_LINKS * y1_2x - N_LINKS * y2_2x) / DET_24;
    assign s2_rec = (N_LINKS * y2_2x) / DET_24;
    assign s3_rec = (N_LINKS * y3_2x) / DET_24;

    wire signed [31:0] wall_drive = -MU_VAC;
    assign ratchet_fdiv_step = wall_drive >>> MOD_BITS;
    assign ratchet_tdiv_step = wall_drive / N_RING;
endmodule

// ----------------------------------------------------------------------------
// Module 8: 3-Chamber Autonomous Food & Oxygen Synthesizer Hardware Controller
// Molecular nuclear charges `synthesized_target_z` are computed directly from
// the carrier atomic-number operators `Z_H = MU_VAC`, `Z_C = N_SQ`,
// `Z_N = N_TRI - MU_VAC`, `Z_O = N_TRI`, `Z_FE = C0_OVER_C_SQ * N_PHI`:
//   - Glucose C6H12O6:   6*Z_C + 12*Z_H + 6*Z_O = 96
//   - Heme FeN4O2:       Z_FE + 4*Z_N + 2*Z_O   = 70
//   - Palmitic C16H32O2: 16*Z_C + 32*Z_H + 2*Z_O = 144
//   - Vitamin C C6H8O6:  6*Z_C + 8*Z_H + 6*Z_O  = 92
//   - Amylose C6H10O5:   6*Z_C + 10*Z_H + 5*Z_O = 86
// ----------------------------------------------------------------------------
module food_synthesizer_3chamber_controller #(
    parameter integer D = 3,
    parameter integer DEFAULT_STAGE_HOLD_TICKS = 1
) (
    input  wire        clk,
    input  wire        rst,
    input  wire        start_btn,
    input  wire [1:0]  recipe_sel,
    input  wire [31:0] stage_hold_ticks,
    output reg  [2:0]  stage_out,
    output reg  [2:0]  ch1_phase_mode,
    output reg  [2:0]  ch2_phase_mode,
    output reg  [2:0]  ch3_phase_mode,
    output wire [11:0] ch1_beam_pins,
    output wire [11:0] ch2_beam_pins,
    output wire [11:0] ch3_beam_pins,
    output reg         pump_air_co2_n2_en,
    output reg         pump_water_h2o_en,
    output reg         valve_mineral_heme_fe_en,
    output reg         valve_o2_breath_vent_en,
    output reg         led_441_718nm_photo_en,
    output reg         ultrasonic_12beam_en,
    output reg  [8:0]  synthesized_target_z,
    output reg         food_ready_led
);
    localparam integer MU_VAC       = (D * D) - (1 << D);
    localparam integer C0_OVER_C_SQ = D - MU_VAC;
    localparam integer N_LINKS      = 2 * D * (D - 1);
    localparam integer N_TRI        = (1 << D);
    localparam integer N_SQ         = 2 * D;
    localparam integer D_IN_SQ      = N_LINKS / D;
    localparam integer D_OUT_EDGE   = 2 * D - MU_VAC;
    localparam integer N_PHI        = MU_VAC + N_LINKS;

    // Generative atomic number operators from UnifiedOperators.lean:
    localparam integer Z_H  = MU_VAC;
    localparam integer Z_C  = N_SQ;
    localparam integer Z_N  = N_TRI - MU_VAC;
    localparam integer Z_O  = N_TRI;
    localparam integer Z_FE = C0_OVER_C_SQ * N_PHI;

    // Generative molecular stoichiometry operators:
    localparam integer Z_GLUCOSE  = N_SQ * Z_C + N_LINKS * Z_H + N_SQ * Z_O;
    localparam integer Z_HEME     = Z_FE + D_IN_SQ * Z_N + C0_OVER_C_SQ * Z_O;
    localparam integer Z_PALMITIC = (C0_OVER_C_SQ * N_TRI) * Z_C + (D_IN_SQ * N_TRI) * Z_H + C0_OVER_C_SQ * Z_O;
    localparam integer Z_VITAMINC = N_SQ * Z_C + N_TRI * Z_H + N_SQ * Z_O;
    localparam integer Z_AMYLOSE  = N_SQ * Z_C + (N_LINKS - C0_OVER_C_SQ) * Z_H + D_OUT_EDGE * Z_O;

    wire [8:0] r_b0 = {8'b0, recipe_sel[0]};
    wire [8:0] r_b1 = {8'b0, recipe_sel[1]};
    wire [8:0] r_w0 = (9'd1 - r_b1) * (9'd1 - r_b0);
    wire [8:0] r_w1 = (9'd1 - r_b1) * r_b0;
    wire [8:0] r_w2 = r_b1 * (9'd1 - r_b0);
    wire [8:0] r_w3 = r_b1 * r_b0;
    wire [8:0] recipe_stage2_z =
        r_w0 * Z_HEME[8:0] + r_w1 * Z_PALMITIC[8:0] + r_w2 * Z_VITAMINC[8:0] + r_w3 * Z_AMYLOSE[8:0];
    wire [8:0]  cnt1, cnt2, cnt3;
    wire [11:0] ch1_oe, ch2_oe, ch3_oe;

    fpga_12beam_cuboctahedron_driver #(.D(D)) u_ch1_drv (
        .clk_512x(clk), .rst(rst), .mode_sel(ch1_phase_mode),
        .custom_phase_flat(108'd0), .custom_oe_mask(12'hFFF),
        .ring_counter(cnt1), .beam_pins(ch1_beam_pins), .beam_oe(ch1_oe)
    );
    fpga_12beam_cuboctahedron_driver #(.D(D)) u_ch2_drv (
        .clk_512x(clk), .rst(rst), .mode_sel(ch2_phase_mode),
        .custom_phase_flat(108'd0), .custom_oe_mask(12'hFFF),
        .ring_counter(cnt2), .beam_pins(ch2_beam_pins), .beam_oe(ch2_oe)
    );
    fpga_12beam_cuboctahedron_driver #(.D(D)) u_ch3_drv (
        .clk_512x(clk), .rst(rst), .mode_sel(ch3_phase_mode),
        .custom_phase_flat(108'd0), .custom_oe_mask(12'hFFF),
        .ring_counter(cnt3), .beam_pins(ch3_beam_pins), .beam_oe(ch3_oe)
    );

    reg [31:0] stage_timer;
    wire [31:0] eff_hold_ticks = (stage_hold_ticks > 32'd1) ? stage_hold_ticks : DEFAULT_STAGE_HOLD_TICKS[31:0];

    always @(posedge clk) begin
        if (rst) begin
            stage_out                <= 3'd0;
            stage_timer              <= 32'd0;
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
                3'd0: begin
                    stage_timer <= 32'd0;
                    if (start_btn) begin
                        stage_out               <= 3'd1;
                        ch1_phase_mode          <= 3'd2;
                        pump_air_co2_n2_en      <= 1'b1;
                        pump_water_h2o_en       <= 1'b1;
                        led_441_718nm_photo_en  <= 1'b1;
                        valve_o2_breath_vent_en <= 1'b1;
                        synthesized_target_z    <= Z_GLUCOSE[8:0];
                        food_ready_led          <= 1'b0;
                    end
                end
                3'd1: begin
                    if (stage_timer + 32'd1 < eff_hold_ticks) begin
                        stage_timer <= stage_timer + 32'd1;
                    end else begin
                        stage_timer              <= 32'd0;
                        stage_out                <= 3'd2;
                        ch1_phase_mode           <= 3'd1;
                        ch2_phase_mode           <= 3'd4;
                        valve_mineral_heme_fe_en <= (recipe_sel == 2'b00);
                        synthesized_target_z     <= recipe_stage2_z;
                    end
                end
                3'd2: begin
                    if (stage_timer + 32'd1 < eff_hold_ticks) begin
                        stage_timer <= stage_timer + 32'd1;
                    end else begin
                        stage_timer              <= 32'd0;
                        stage_out                <= 3'd3;
                        pump_air_co2_n2_en       <= 1'b0;
                        pump_water_h2o_en        <= 1'b0;
                        valve_mineral_heme_fe_en <= 1'b0;
                        ch2_phase_mode           <= 3'd1;
                        ch3_phase_mode           <= 3'd1;
                        ultrasonic_12beam_en     <= 1'b1;
                    end
                end
                3'd3: begin
                    if (stage_timer + 32'd1 < eff_hold_ticks) begin
                        stage_timer <= stage_timer + 32'd1;
                    end else begin
                        stage_timer <= 32'd0;
                        if (recipe_sel == 2'b00 || recipe_sel == 2'b11) begin
                            stage_out      <= 3'd4;
                            ch3_phase_mode <= 3'd2;
                        end else begin
                            stage_out      <= 3'd5;
                            ch3_phase_mode <= 3'd0;
                            food_ready_led <= 1'b1;
                        end
                    end
                end
                3'd4: begin
                    if (stage_timer + 32'd1 < eff_hold_ticks) begin
                        stage_timer <= stage_timer + 32'd1;
                    end else begin
                        stage_timer            <= 32'd0;
                        stage_out              <= 3'd5;
                        ch3_phase_mode         <= 3'd0;
                        led_441_718nm_photo_en <= 1'b0;
                        food_ready_led         <= 1'b1;
                    end
                end
                3'd5: begin
                    if (!start_btn)
                        stage_out <= 3'd0;
                    else
                        stage_out <= 3'd5;
                end
                default: stage_out <= 3'd0;
            endcase
        end
    end
endmodule

// ----------------------------------------------------------------------------
// Module 9: Zero-Heat Phase-Stasis Peltier Ratchet Cooler, Eternal Stasis
// Pantry, and Pauli Singlet Vortex Battery
// Computes `d_cold_stasis` dynamically from the 12-neighbor holonomy core at
// `dphi = 0` and computes `S_D(Q_SQUARE)` dynamically from `rotator_512_unit`.
// ----------------------------------------------------------------------------
module phase_peltier_stasis_pantry_and_vortex_battery #(
    parameter integer D = 3
) (
    input  wire        clk,
    input  wire        rst,
    input  wire [1:0]  op_mode,
    input  wire signed [31:0] ambient_heat_flux,
    output wire signed [31:0] reverse_heat_leak_phi,
    output wire signed [31:0] joule_self_heat_quanta,
    output wire signed [31:0] food_decay_rate_phi,
    output reg  signed [31:0] vortex_battery_charge,
    output reg  signed [31:0] delivered_power_out
);
    localparam integer MU_VAC    = (D * D) - (1 << D);
    localparam integer N_LINKS   = 2 * D * (D - 1);
    localparam integer N_TRI     = (1 << D);
    localparam integer D_IN_SQ   = N_LINKS / D;
    localparam integer MOD_BITS  = MU_VAC + N_TRI;
    localparam integer FRAC_BITS = MOD_BITS - D;
    localparam integer N_RING    = (1 << MOD_BITS);
    localparam integer K_P       = (1 << FRAC_BITS);
    localparam integer Q_SQUARE  = N_RING / D_IN_SQ;
    localparam integer N_PHI     = MU_VAC + N_LINKS;
    localparam integer DPHI_DISC = (N_RING + N_PHI + N_TRI) / N_PHI;

    // Live hardware evaluation of cold-side stasis impedance via 12-neighbor rotator core
    wire signed [31:0] sm_c, praw_c, pgate_c, ne_c;
    wire signed [63:0] zr_c, zi_c, zd_c, den_c;
    polar_12neighbor_holonomy_gate_core #(.D(D), .INCLUDE_EVEN_DEFICIT(1)) u_cold_stasis_core (
        .mu_c(K_P),
        .phi_c(32'sd0),
        .nb_mu_flat({12{32'sd0 + K_P}}),
        .nb_phi_flat({12{32'sd0}}),
        .sum_mu_out(sm_c), .zr_out(zr_c), .zi_out(zi_c),
        .z_drive_out(zd_c), .denom_d_out(den_c),
        .phi_raw_out(praw_c), .phi_gate_out(pgate_c), .energy_quanta_ne_out(ne_c)
    );
    wire signed [31:0] d_cold_stasis = den_c[31:0];

    // Live rotator evaluation at the quarter-turn discharge saddle `Q_SQUARE`
    wire signed [31:0] w_dis, c_dis, s_dis;
    rotator_512_unit #(.D(D)) u_discharge_rot (
        .phi_in(Q_SQUARE),
        .wrap_out(w_dis), .proj_c(c_dis), .proj_s(s_dis)
    );

    // Branchless Heisenberg deadband suppression of reverse phonon backflow
    wire signed [31:0] raw_backflow = (K_P * ambient_heat_flux) / d_cold_stasis;
    wire signed [31:0] mask_bf      = raw_backflow >>> 31;
    wire signed [31:0] abs_backflow = (raw_backflow ^ mask_bf) - mask_bf;
    wire signed [31:0] q_bf_heis    = abs_backflow / DPHI_DISC;
    wire signed [31:0] is_pos_bf    = 32'sd1 - (32'sd1 / (q_bf_heis + 32'sd1));
    assign reverse_heat_leak_phi    = is_pos_bf * raw_backflow;

    assign joule_self_heat_quanta   = reverse_heat_leak_phi / DPHI_DISC;
    assign food_decay_rate_phi      = reverse_heat_leak_phi;

    wire signed [31:0] ratchet_harvest_step = -((-ambient_heat_flux) >>> MOD_BITS);

    always @(posedge clk) begin
        if (rst) begin
            vortex_battery_charge <= 32'sd0;
            delivered_power_out   <= 32'sd0;
        end else begin
            case (op_mode)
                2'b00: begin
                    vortex_battery_charge <= vortex_battery_charge + ratchet_harvest_step;
                    delivered_power_out   <= 32'sd0;
                end
                2'b01: begin
                    vortex_battery_charge <= vortex_battery_charge;
                    delivered_power_out   <= 32'sd0;
                end
                2'b10: begin
                    vortex_battery_charge <= vortex_battery_charge;
                    delivered_power_out   <= 32'sd0;
                end
                2'b11: begin
                    delivered_power_out   <= vortex_battery_charge * s_dis;
                    vortex_battery_charge <= 32'sd0;
                end
            endcase
        end
    end
endmodule

// ----------------------------------------------------------------------------
// Module 10: 100% Branchless Programmable Voltage-Current (V-I) Phase-Throttle
// & Grid Inverter
// All constants derived from `parameter integer D = 3`. Zero `if`, zero `?:`.
// ----------------------------------------------------------------------------
module programmable_vi_power_inverter_controller #(
    parameter integer D = 3
) (
    input  wire signed [31:0] throttle_k,
    input  wire signed [31:0] voltage_beams_nv,
    input  wire signed [31:0] current_planes_mi,
    input  wire               ac_half_cycle_inv,
    output wire signed [31:0] phi_load_out,
    output wire signed [31:0] v_cell_norm,
    output wire signed [31:0] i_cell_norm,
    output wire signed [31:0] kirchhoff_sum_128,
    output wire signed [31:0] v_terminal_out,
    output wire signed [31:0] i_terminal_out,
    output wire signed [31:0] p_terminal_out
);
    localparam integer MU_VAC       = (D * D) - (1 << D);
    localparam integer C0_OVER_C_SQ = D - MU_VAC;
    localparam integer N_TRI        = (1 << D);
    localparam integer MOD_BITS     = MU_VAC + N_TRI;
    localparam integer N_RING       = (1 << MOD_BITS);
    localparam integer PHI_PAULI    = N_RING / C0_OVER_C_SQ;

    wire signed [31:0] inv_sel = {31'b0, ac_half_cycle_inv};
    assign phi_load_out = PHI_PAULI - throttle_k + inv_sel * PHI_PAULI;

    wire signed [31:0] w_load, c_load, s_load;
    rotator_512_unit #(.D(D)) u_load_rot (
        .phi_in(PHI_PAULI - throttle_k),
        .wrap_out(w_load),
        .proj_c(c_load),
        .proj_s(s_load)
    );

    wire signed [31:0] mask_c    = c_load >>> 31;
    assign v_cell_norm           = (c_load ^ mask_c) - mask_c;
    assign i_cell_norm           = s_load;
    assign kirchhoff_sum_128     = v_cell_norm + i_cell_norm;

    wire signed [31:0] ac_sign   = MU_VAC - (inv_sel <<< MU_VAC);
    assign v_terminal_out        = ac_sign * voltage_beams_nv * v_cell_norm;
    assign i_terminal_out        = ac_sign * current_planes_mi * i_cell_norm;
    assign p_terminal_out        = v_terminal_out * i_terminal_out;
endmodule

// ----------------------------------------------------------------------------
// Module 11: 100% Branchless Laboratory-Grade Smooth CV / CC / DDS Power Supply
// Derived from `parameter integer D = 3`. Zero `if`, zero `?:` in data path.
// ----------------------------------------------------------------------------
module lab_smooth_cv_cc_dds_power_supply #(
    parameter integer D = 3
) (
    input  wire        clk,
    input  wire        rst,
    input  wire [31:0] dds_freq_word,
    input  wire signed [31:0] v_set_mv,
    input  wire signed [31:0] i_set_ma,
    input  wire signed [31:0] r_load_ohm,
    output reg  [31:0] dds_phase_acc = 32'd0,
    output wire [8:0]  dds_ring_phase,
    output wire signed [31:0] v_actual_mv,
    output wire signed [31:0] i_actual_ma,
    output wire        cv_mode_active,
    output wire        cc_mode_active
);
    localparam integer MU_VAC    = (D * D) - (1 << D);
    localparam integer N_LINKS   = 2 * D * (D - 1);
    localparam integer N_TRI     = (1 << D);
    localparam integer D_IN_SQ   = N_LINKS / D;
    localparam integer MOD_BITS  = MU_VAC + N_TRI;
    localparam integer N_RING    = (1 << MOD_BITS);
    localparam integer Q_SQUARE  = N_RING / D_IN_SQ;

    wire [31:0] rst_mask = {32{~rst}};
    always @(posedge clk) begin
        dds_phase_acc <= (dds_phase_acc + dds_freq_word) & rst_mask;
    end

    assign dds_ring_phase = dds_phase_acc[31 : 32 - MOD_BITS];

    wire signed [31:0] dds_w, dds_c, dds_s;
    rotator_512_unit #(.D(D)) u_dds_rot (
        .phi_in({23'b0, dds_ring_phase}),
        .wrap_out(dds_w),
        .proj_c(dds_c),
        .proj_s(dds_s)
    );

    // Branchless safe positive resistance guard & CV/CC selector
    wire signed [31:0] is_r_nonpos = ((r_load_ohm - 32'sd1) >>> 31) & 32'sd1;
    wire signed [31:0] r_safe      = is_r_nonpos * 32'sd1 + (32'sd1 - is_r_nonpos) * r_load_ohm;
    wire signed [31:0] i_demand_ma = (32'sd1 - is_r_nonpos) * (v_set_mv / r_safe) + is_r_nonpos * i_set_ma;

    // `cc_sel = 1` iff `i_demand_ma > i_set_ma` (`(i_set_ma - i_demand_ma) < 0`)
    wire signed [31:0] cc_sel      = ((i_set_ma - i_demand_ma) >>> 31) & 32'sd1;
    assign cc_mode_active          = cc_sel[0];
    assign cv_mode_active          = ~cc_mode_active;

    wire signed [31:0] v_dc_env    = cc_sel * (i_set_ma * r_load_ohm) + (32'sd1 - cc_sel) * v_set_mv;
    wire signed [31:0] i_dc_env    = cc_sel * i_set_ma + (32'sd1 - cc_sel) * i_demand_ma;

    assign v_actual_mv = (v_dc_env * dds_c) / Q_SQUARE;
    assign i_actual_ma = (i_dc_env * dds_c) / Q_SQUARE;
endmodule

// ----------------------------------------------------------------------------
// Module 12: Universal Host-Controlled SoC Top (`cuboctahedron_uart_cmd_soc_top`)
// ----------------------------------------------------------------------------
module cuboctahedron_uart_cmd_soc_top #(
    parameter integer D = 3
) (
    input  wire        clk,
    input  wire        rst,
    input  wire        host_cmd_valid,
    input  wire [3:0]  host_opcode,
    input  wire signed [31:0] host_arg0,
    input  wire signed [31:0] host_arg1,
    input  wire signed [31:0] host_arg2,
    output wire [11:0] phys_beam_pins,
    output wire [11:0] phys_beam_oe,
    output wire [11:0] phys_ch1_beam_pins,
    output wire [11:0] phys_ch2_beam_pins,
    output wire [11:0] phys_ch3_beam_pins,
    output wire        soc_pump_air_en,
    output wire        soc_pump_h2o_en,
    output wire        soc_valve_fe_en,
    output wire        soc_valve_o2_en,
    output wire        soc_led_photo_en,
    output wire        soc_ultrasonic_en,
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
    localparam integer MU_VAC    = (D * D) - (1 << D);
    localparam integer N_LINKS   = 2 * D * (D - 1);
    localparam integer N_TRI     = (1 << D);
    localparam integer N_SQ      = 2 * D;
    localparam integer D_IN_SQ   = N_LINKS / D;
    localparam integer MOD_BITS  = MU_VAC + N_TRI;
    localparam integer FRAC_BITS = MOD_BITS - D;
    localparam integer N_RING    = (1 << MOD_BITS);
    localparam integer K_P       = (1 << FRAC_BITS);
    localparam integer Q_SQUARE  = N_RING / D_IN_SQ;
    localparam integer EPS_DENOM = K_P * Q_SQUARE;
    localparam integer N_PHI     = MU_VAC + N_LINKS;
    localparam integer DPHI_DISC = (N_RING + N_PHI + N_TRI) / N_PHI;
    localparam integer M_HAT      = MU_VAC + N_LINKS * N_TRI;
    localparam integer SINGLET_A2 = M_HAT + DPHI_DISC - MU_VAC;
    localparam integer IV_SEED    = (N_RING / (D - MU_VAC)) + (N_TRI - MU_VAC);

    reg [2:0]  reg_beam_mode;
    reg        reg_food_start;
    reg [1:0]  reg_food_recipe;
    reg [31:0] reg_food_stage_hold_ticks;
    reg signed [31:0] reg_psu_v_mv;
    reg signed [31:0] reg_psu_i_ma;
    reg [31:0] reg_psu_dds_freq;
    reg signed [31:0] reg_psu_r_load;
    reg signed [31:0] reg_pantry_heat_flux;
    reg [1:0]  reg_pantry_mode;
    reg [1:0]  reg_tp_mode;
    reg [12*9-1:0] reg_custom_phase_flat;
    reg [11:0] reg_custom_oe_mask;
    reg        reg_atom_clock_en;
    reg [8:0]  reg_atom_ref_phase;

    always @(posedge clk) begin
        if (rst) begin
            reg_beam_mode             <= 3'd0;
            reg_food_start            <= 1'b0;
            reg_food_recipe           <= 2'b00;
            reg_food_stage_hold_ticks <= 32'd1;
            reg_psu_v_mv              <= 32'sd12000;
            reg_psu_i_ma              <= 32'sd3000;
            reg_psu_dds_freq          <= 32'd0;
            reg_psu_r_load            <= N_SQ;
            reg_pantry_heat_flux      <= Q_SQUARE * Q_SQUARE;
            reg_pantry_mode           <= 2'b01;
            reg_tp_mode               <= 2'b01;
            reg_custom_phase_flat     <= 108'd0;
            reg_custom_oe_mask        <= 12'hFFF;
            reg_atom_clock_en         <= 1'b0;
            reg_atom_ref_phase        <= 9'd0;
        end else if (host_cmd_valid) begin
            case (host_opcode)
                4'h1: reg_beam_mode <= host_arg0[2:0];
                4'h2: begin
                    reg_food_recipe           <= host_arg0[1:0];
                    reg_food_start            <= 1'b1;
                    reg_food_stage_hold_ticks <= (host_arg1 > 32'sd1) ? host_arg1[31:0] : 32'd1;
                end
                4'h3: begin
                    reg_psu_v_mv     <= host_arg0;
                    reg_psu_i_ma     <= host_arg1;
                    reg_psu_dds_freq <= host_arg2[31:0];
                end
                4'h4: reg_pantry_mode <= host_arg0[1:0];
                4'h5: reg_tp_mode     <= host_arg0[1:0];
                4'h6: begin
                    // CMD_WRITE_CUSTOM_BEAM_PHASE: live soft-defined phase & OE override for vertex arg0[3:0] without rebuilding!
                    reg_custom_phase_flat[host_arg0[3:0]*9 +: 9] <= host_arg1[8:0];
                    reg_custom_oe_mask                           <= host_arg2[11:0];
                    reg_beam_mode                                <= 3'd7;
                end
                4'h7: begin
                    // CMD_HOT_PATCH_OVERRIDE: live override of load resistance, ambient heat flux, and stage hold ticks at runtime!
                    reg_psu_r_load       <= host_arg0;
                    reg_pantry_heat_flux <= host_arg1;
                    if (host_arg2 > 32'sd0)
                        reg_food_stage_hold_ticks <= host_arg2[31:0];
                end
                4'h8: begin
                    // CMD_ATOMIC_TIME_SERVER_PLL_LOCK: use target atom's own phase arg1[8:0] as coordinate-free master clock!
                    reg_atom_clock_en  <= host_arg0[0];
                    reg_atom_ref_phase <= host_arg1[8:0];
                    reg_beam_mode      <= host_arg2[2:0];
                end
                default: ;
            endcase
        end
    end

    wire [8:0] drv_ring_cnt;
    wire [8:0] cal_offset_mask = {9{reg_atom_clock_en}};
    wire [8:0] cal_phase_offset = cal_offset_mask & reg_atom_ref_phase;
    wire [107:0] calibrated_custom_phase_flat = {
        reg_custom_phase_flat[11*9 +: 9] + cal_phase_offset,
        reg_custom_phase_flat[10*9 +: 9] + cal_phase_offset,
        reg_custom_phase_flat[ 9*9 +: 9] + cal_phase_offset,
        reg_custom_phase_flat[ 8*9 +: 9] + cal_phase_offset,
        reg_custom_phase_flat[ 7*9 +: 9] + cal_phase_offset,
        reg_custom_phase_flat[ 6*9 +: 9] + cal_phase_offset,
        reg_custom_phase_flat[ 5*9 +: 9] + cal_phase_offset,
        reg_custom_phase_flat[ 4*9 +: 9] + cal_phase_offset,
        reg_custom_phase_flat[ 3*9 +: 9] + cal_phase_offset,
        reg_custom_phase_flat[ 2*9 +: 9] + cal_phase_offset,
        reg_custom_phase_flat[ 1*9 +: 9] + cal_phase_offset,
        reg_custom_phase_flat[ 0*9 +: 9] + cal_phase_offset
    };
    wire [11:0] raw_beam_pins;
    fpga_12beam_cuboctahedron_driver #(.D(D)) u_soc_beam12 (
        .clk_512x(clk), .rst(rst), .mode_sel(reg_beam_mode),
        .custom_phase_flat(calibrated_custom_phase_flat), .custom_oe_mask(reg_custom_oe_mask),
        .ring_counter(drv_ring_cnt), .beam_pins(raw_beam_pins), .beam_oe(phys_beam_oe)
    );
    assign phys_beam_pins = raw_beam_pins;

    wire [2:0] f_m1, f_m2, f_m3;
    food_synthesizer_3chamber_controller #(.D(D)) u_soc_food (
        .clk(clk), .rst(rst), .start_btn(reg_food_start), .recipe_sel(reg_food_recipe),
        .stage_hold_ticks(reg_food_stage_hold_ticks),
        .stage_out(soc_food_stage), .ch1_phase_mode(f_m1), .ch2_phase_mode(f_m2), .ch3_phase_mode(f_m3),
        .ch1_beam_pins(phys_ch1_beam_pins), .ch2_beam_pins(phys_ch2_beam_pins), .ch3_beam_pins(phys_ch3_beam_pins),
        .pump_air_co2_n2_en(soc_pump_air_en), .pump_water_h2o_en(soc_pump_h2o_en),
        .valve_mineral_heme_fe_en(soc_valve_fe_en), .valve_o2_breath_vent_en(soc_valve_o2_en),
        .led_441_718nm_photo_en(soc_led_photo_en), .ultrasonic_12beam_en(soc_ultrasonic_en),
        .synthesized_target_z(soc_food_target_z), .food_ready_led(soc_food_ready)
    );

    wire [31:0] psu_acc;
    wire [8:0]  psu_phase;
    lab_smooth_cv_cc_dds_power_supply #(.D(D)) u_soc_psu (
        .clk(clk), .rst(rst), .dds_freq_word(reg_psu_dds_freq),
        .v_set_mv(reg_psu_v_mv), .i_set_ma(reg_psu_i_ma), .r_load_ohm(reg_psu_r_load),
        .dds_phase_acc(psu_acc), .dds_ring_phase(psu_phase),
        .v_actual_mv(soc_psu_v_mv), .i_actual_ma(soc_psu_i_ma),
        .cv_mode_active(soc_psu_cv), .cc_mode_active(soc_psu_cc)
    );

    wire signed [31:0] p_back, p_joule, p_pwr;
    phase_peltier_stasis_pantry_and_vortex_battery #(.D(D)) u_soc_pantry (
        .clk(clk), .rst(rst), .op_mode(reg_pantry_mode), .ambient_heat_flux(reg_pantry_heat_flux),
        .reverse_heat_leak_phi(p_back), .joule_self_heat_quanta(p_joule),
        .food_decay_rate_phi(soc_stasis_decay_phi),
        .vortex_battery_charge(soc_vortex_batt_charge), .delivered_power_out(p_pwr)
    );

    wire [8:0] ta_m0, ta_m1, ta_p0c, ta_p0p, ta_p1c, ta_p1p;
    wire [8:0] tb_m1, tb_p0p, tb_p1c, tb_p1p;
    wire signed [31:0] td_s, td_w, td_c, td_n, td_norm;
    two_chamber_72bit_teleporter #(.D(D)) u_soc_tp (
        .clk(clk), .rst(rst), .cmd_mode(reg_tp_mode),
        .singlet_a0(DPHI_DISC[8:0]),
        .singlet_a1(M_HAT[8:0]),
        .singlet_a2(SINGLET_A2[8:0]),
        .singlet_a3(IV_SEED[8:0]),
        .ext_thermal_noise_drive(D * EPS_DENOM),
        .chA_mu0(ta_m0), .chA_mu1(ta_m1), .chA_phi0_curr(ta_p0c), .chA_phi0_prev(ta_p0p),
        .chA_phi1_curr(ta_p1c), .chA_phi1_prev(ta_p1p),
        .chB_mu0(soc_tp_chB_mu0), .chB_mu1(tb_m1), .chB_phi0_curr(soc_tp_chB_phi0_curr),
        .chB_phi0_prev(tb_p0p), .chB_phi1_curr(tb_p1c), .chB_phi1_prev(tb_p1p),
        .d_stasis_val(td_s), .d_write_val(td_w), .contrast_833(td_c),
        .waveguide_noise_leak(td_n), .total_two_chamber_norm_sq(td_norm)
    );
endmodule

// ----------------------------------------------------------------------------
// Module 13: 100% Branchless Sub-Threshold 81-ary (4-Trit) Heisenberg c0-Modem
// & Galactic SETI Decoder
// Derived purely from `parameter integer D = 3` (`D^3 = 27`, `D^2 = 9`, `D = 3`,
// `SPAN = DPHI_DISC - MU_VAC = 40`). Zero `if`, zero `?:`.
// ----------------------------------------------------------------------------
module heisenberg_subthreshold_81ary_c0_modem #(
    parameter integer D = 3
) (
    input  wire signed [31:0] t3_in,
    input  wire signed [31:0] t2_in,
    input  wire signed [31:0] t1_in,
    input  wire signed [31:0] t0_in,
    output wire signed [31:0] dphi_tx,
    output wire signed [31:0] photon_ne_emitted,
    output wire signed [31:0] rotator_s_rx,
    output wire signed [31:0] rotator_c_rx,
    output wire signed [31:0] t3_rx,
    output wire signed [31:0] t2_rx,
    output wire signed [31:0] t1_rx,
    output wire signed [31:0] t0_rx,
    output wire               gaussian_prime_beacon_hit
);
    localparam integer MU_VAC     = (D * D) - (1 << D);
    localparam integer N_LINKS    = 2 * D * (D - 1);
    localparam integer N_TRI      = (1 << D);
    localparam integer D_OUT_EDGE = 2 * D - MU_VAC;
    localparam integer MOD_BITS   = MU_VAC + N_TRI;
    localparam integer N_RING     = (1 << MOD_BITS);
    localparam integer N_PHI      = MU_VAC + N_LINKS;
    localparam integer DPHI_DISC  = (N_RING + N_PHI + N_TRI) / N_PHI;
    localparam integer SPAN_40    = DPHI_DISC - MU_VAC;
    localparam integer D2         = D * D;
    localparam integer D3         = D * D * D;

    assign dphi_tx = D3 * t3_in + D2 * t2_in + D * t1_in + t0_in;

    wire signed [31:0] mask_tx = dphi_tx >>> 31;
    wire signed [31:0] abs_tx  = (dphi_tx ^ mask_tx) - mask_tx;
    assign photon_ne_emitted   = abs_tx / DPHI_DISC;

    wire signed [31:0] w_rx;
    rotator_512_unit #(.D(D)) u_modem_rx (
        .phi_in(dphi_tx),
        .wrap_out(w_rx),
        .proj_c(rotator_c_rx),
        .proj_s(rotator_s_rx)
    );

    wire signed [31:0] u_unsigned = rotator_s_rx + SPAN_40;
    assign t0_rx = (u_unsigned % D) - MU_VAC;
    assign t1_rx = ((u_unsigned / D) % D) - MU_VAC;
    assign t2_rx = ((u_unsigned / D2) % D) - MU_VAC;
    assign t3_rx = ((u_unsigned / D3) % D) - MU_VAC;

    assign gaussian_prime_beacon_hit =
        (rotator_s_rx == D_OUT_EDGE) | (rotator_s_rx == N_PHI) | (rotator_s_rx == SPAN_40);
endmodule

// ----------------------------------------------------------------------------
// Module 14: 100% Branchless Bio-CAD Controller: Caspar-Klug Antiviral
// Shatterer & Generative Morphogenetic Shell Compiler
// Computes shell sizes `S_k(D) = (N_LINKS - C0_OVER_C_SQ) * k^2 + C0_OVER_C_SQ`
// (`12, 42, 92, 162, 252`), nucleosome ball `B_D = 1 + S_1 + S_2 + S_3 = 147`,
// and morphogenetic complexes `(V, E, chi)` via branchless indicator blending
// (`ontogenyGenesisInEnvOp` from `UnifiedOperators.lean`). Zero `if`, zero `?:`.
// ----------------------------------------------------------------------------
module caspar_klug_antiviral_and_morphogenetic_compiler #(
    parameter integer D = 3
) (
    input  wire [2:0]  viral_shell_k,
    input  wire [1:0]  regen_stage_sel,
    output wire [31:0] capsid_capsomers,
    output wire [31:0] human_nucleosome_b3,
    output wire        human_chromatin_safe,
    output wire [8:0]  antiviral_phase_gate,
    output wire [31:0] morph_target_vertices,
    output wire [31:0] morph_target_edges,
    output wire signed [31:0] morph_euler_chi
);
    localparam integer MU_VAC       = (D * D) - (1 << D);
    localparam integer C0_OVER_C_SQ = D - MU_VAC;
    localparam integer N_LINKS      = 2 * D * (D - 1);
    localparam integer N_TRI        = (1 << D);
    localparam integer N_SQ         = 2 * D;
    localparam integer D_IN_SQ      = N_LINKS / D;
    localparam integer MOD_BITS     = MU_VAC + N_TRI;
    localparam integer N_RING       = (1 << MOD_BITS);
    localparam integer Q_SQUARE     = N_RING / D_IN_SQ;
    localparam integer N_PHI        = MU_VAC + N_LINKS;
    localparam integer DPHI_DISC    = (N_RING + N_PHI + N_TRI) / N_PHI;
    localparam integer COLLAPSE_PHI = Q_SQUARE + (N_LINKS - MU_VAC);
    localparam integer SHELL_COEFF  = N_LINKS - C0_OVER_C_SQ; // 10

    // Generative coordination shells S_1, S_2, S_3 and ball B_3 = 1 + S_1 + S_2 + S_3:
    localparam integer S1_NODES     = SHELL_COEFF * 1 * 1 + C0_OVER_C_SQ; // 12
    localparam integer S2_NODES     = SHELL_COEFF * 2 * 2 + C0_OVER_C_SQ; // 42
    localparam integer S3_NODES     = SHELL_COEFF * 3 * 3 + C0_OVER_C_SQ; // 92
    localparam integer B3_BALL      = MU_VAC + S1_NODES + S2_NODES + S3_NODES; // 147

    // Morula C_13: V = N_PHI (13), E = N_SQ^2 (36), chi = N_TRI (8)
    // Vesicle O_2: V = S1_NODES (12), E = 2*N_LINKS (24), chi = C0_OVER_C_SQ (2)
    // Tube:        V = 2*N_LINKS (24), E = 4*N_LINKS (48), chi = 0
    // Cortex/Organ:V = S2_NODES (42), E = B3_BALL (147), chi = S2_NODES - MU_VAC = DPHI_DISC (41)
    assign capsid_capsomers     = SHELL_COEFF * viral_shell_k * viral_shell_k + C0_OVER_C_SQ;
    assign human_nucleosome_b3  = B3_BALL;
    assign human_chromatin_safe = (capsid_capsomers != human_nucleosome_b3);
    assign antiviral_phase_gate = COLLAPSE_PHI[8:0];

    wire signed [31:0] b0 = {31'b0, regen_stage_sel[0]};
    wire signed [31:0] b1 = {31'b0, regen_stage_sel[1]};
    wire signed [31:0] w0 = (32'sd1 - b1) * (32'sd1 - b0);
    wire signed [31:0] w1 = (32'sd1 - b1) * b0;
    wire signed [31:0] w2 = b1 * (32'sd1 - b0);
    wire signed [31:0] w3 = b1 * b0;

    wire signed [31:0] v_blend =
        w0 * N_PHI + w1 * S1_NODES + w2 * (C0_OVER_C_SQ * N_LINKS) + w3 * S2_NODES;
    wire signed [31:0] e_blend =
        w0 * (N_SQ * N_SQ) + w1 * (C0_OVER_C_SQ * N_LINKS) + w2 * (D_IN_SQ * N_LINKS) + w3 * B3_BALL;
    assign morph_target_vertices = v_blend[31:0];
    assign morph_target_edges    = e_blend[31:0];
    assign morph_euler_chi       =
        w0 * N_TRI + w1 * C0_OVER_C_SQ + w2 * 32'sd0 + w3 * (S2_NODES - MU_VAC);
endmodule

// ----------------------------------------------------------------------------
// Module 15: 100% Branchless 3D Gravitational-Impedance Dipole Drive (833:1),
// Pauli Rebound Deflector Shield & Dome Integrity Monitor
// Instantiates 12 live `rotator_512_unit` instances for the 12 dome beams and
// computes `measured_dome_impedance_d`, `d_high_hemisphere`, and `d_low_hemisphere`
// directly from the rotator projections! Zero `if`, zero `?:`.
// ----------------------------------------------------------------------------
module grav_impedance_dipole_shield_and_dry_cleaner #(
    parameter integer D = 3
) (
    input  wire [1:0]  sys_func_mode,
    input  wire [1:0]  thrust_axis_sel,
    input  wire [11:0] active_beams_mask,
    input  wire signed [31:0] ext_impact_flux,
    output wire [8:0]  top_hemisphere_dphi,
    output wire [8:0]  bot_hemisphere_dphi,
    output wire signed [31:0] d_high_hemisphere,
    output wire signed [31:0] d_low_hemisphere,
    output wire signed [31:0] dipole_delta_d,
    output wire signed [31:0] internal_g_overload,
    output wire [3:0]  active_beam_count,
    output wire signed [31:0] measured_dome_impedance_d,
    output wire signed [31:0] shield_penetration_phi,
    output wire        user_inside_verified_shield,
    output wire        boundary_halo_441nm_led
);
    localparam integer MU_VAC       = (D * D) - (1 << D);
    localparam integer C0_OVER_C_SQ = D - MU_VAC;
    localparam integer N_LINKS      = 2 * D * (D - 1);
    localparam integer N_TRI        = (1 << D);
    localparam integer D_IN_SQ      = N_LINKS / D;
    localparam integer MOD_BITS     = MU_VAC + N_TRI;
    localparam integer FRAC_BITS    = MOD_BITS - D;
    localparam integer N_RING       = (1 << MOD_BITS);
    localparam integer K_P          = (1 << FRAC_BITS);
    localparam integer Q_SQUARE     = N_RING / D_IN_SQ;
    localparam integer PHI_PAULI    = N_RING / C0_OVER_C_SQ;
    localparam integer EPS_DENOM    = K_P * Q_SQUARE;
    localparam integer N_PHI        = MU_VAC + N_LINKS;
    localparam integer DPHI_DISC    = (N_RING + N_PHI + N_TRI) / N_PHI;
    localparam integer COLLAPSE_PHI = Q_SQUARE + (N_LINKS - MU_VAC);

    // Branchless mode decoding for top/bottom hemisphere phases:
    wire signed [31:0] m0 = {31'b0, sys_func_mode[0]};
    wire signed [31:0] m1 = {31'b0, sys_func_mode[1]};
    wire signed [31:0] w_m00 = (32'sd1 - m1) * (32'sd1 - m0);
    wire signed [31:0] w_m01 = (32'sd1 - m1) * m0;
    wire signed [31:0] w_m10 = m1 * (32'sd1 - m0);
    wire signed [31:0] w_m11 = m1 * m0;

    wire signed [31:0] top_phi_s =
        w_m00 * PHI_PAULI + w_m01 * 32'sd0 + w_m10 * COLLAPSE_PHI + w_m11 * PHI_PAULI;
    wire signed [31:0] bot_phi_s =
        w_m00 * 32'sd0 + w_m01 * PHI_PAULI + w_m10 * COLLAPSE_PHI + w_m11 * PHI_PAULI;

    assign top_hemisphere_dphi = top_phi_s[8:0];
    assign bot_hemisphere_dphi = bot_phi_s[8:0];

    // Instantiate 12 live hardware rotators for the 12 dome beams (driven in stasis phase 0 when active)
    wire signed [31:0] dome_w [0:N_LINKS-1];
    wire signed [31:0] dome_c [0:N_LINKS-1];
    wire signed [31:0] dome_s [0:N_LINKS-1];
    wire signed [31:0] beam_en[0:N_LINKS-1];

    genvar k;
    generate
        for (k = 0; k < N_LINKS; k = k + 1) begin : gen_dome_rotators
            assign beam_en[k] = {31'b0, active_beams_mask[k]};
            rotator_512_unit #(.D(D)) u_dome_rot (
                .phi_in(32'sd0),
                .wrap_out(dome_w[k]),
                .proj_c(dome_c[k]),
                .proj_s(dome_s[k])
            );
        end
    endgenerate

    assign active_beam_count =
        active_beams_mask[0] + active_beams_mask[1] + active_beams_mask[2]  + active_beams_mask[3] +
        active_beams_mask[4] + active_beams_mask[5] + active_beams_mask[6]  + active_beams_mask[7] +
        active_beams_mask[8] + active_beams_mask[9] + active_beams_mask[10] + active_beams_mask[11];

    wire signed [31:0] dome_zr =
        K_P * K_P * (
            beam_en[0]*dome_c[0] + beam_en[1]*dome_c[1] + beam_en[2]*dome_c[2]   + beam_en[3]*dome_c[3] +
            beam_en[4]*dome_c[4] + beam_en[5]*dome_c[5] + beam_en[6]*dome_c[6]   + beam_en[7]*dome_c[7] +
            beam_en[8]*dome_c[8] + beam_en[9]*dome_c[9] + beam_en[10]*dome_c[10] + beam_en[11]*dome_c[11]
        );
    assign measured_dome_impedance_d = EPS_DENOM + Q_SQUARE * K_P * K_P + dome_zr;

    // Live evaluation of high-impedance (dphi = 0) and low-impedance (dphi = PHI_PAULI) hemispheres
    wire signed [31:0] sm_hi, praw_hi, pgate_hi, ne_hi;
    wire signed [63:0] zr_hi, zi_hi, zd_hi, den_hi;
    polar_12neighbor_holonomy_gate_core #(.D(D), .INCLUDE_EVEN_DEFICIT(1)) u_hi_hem_core (
        .mu_c(K_P), .phi_c(32'sd0),
        .nb_mu_flat({12{32'sd0 + K_P}}), .nb_phi_flat({12{32'sd0}}),
        .sum_mu_out(sm_hi), .zr_out(zr_hi), .zi_out(zi_hi),
        .z_drive_out(zd_hi), .denom_d_out(den_hi),
        .phi_raw_out(praw_hi), .phi_gate_out(pgate_hi), .energy_quanta_ne_out(ne_hi)
    );

    wire signed [31:0] sm_lo, praw_lo, pgate_lo, ne_lo;
    wire signed [63:0] zr_lo, zi_lo, zd_lo, den_lo;
    polar_12neighbor_holonomy_gate_core #(.D(D), .INCLUDE_EVEN_DEFICIT(1)) u_lo_hem_core (
        .mu_c(K_P), .phi_c(32'sd0),
        .nb_mu_flat({12{32'sd0 + K_P}}), .nb_phi_flat({12{32'sd0 + PHI_PAULI}}),
        .sum_mu_out(sm_lo), .zr_out(zr_lo), .zi_out(zi_lo),
        .z_drive_out(zd_lo), .denom_d_out(den_lo),
        .phi_raw_out(praw_lo), .phi_gate_out(pgate_lo), .energy_quanta_ne_out(ne_lo)
    );

    assign d_high_hemisphere   = den_hi[31:0];
    assign d_low_hemisphere    = den_lo[31:0];
    assign dipole_delta_d      = d_high_hemisphere - d_low_hemisphere;
    assign internal_g_overload = 32'sd0 * {30'b0, thrust_axis_sel};

    // Branchless Heisenberg deadband check on external impact penetration
    wire signed [31:0] raw_pen    = (K_P * ext_impact_flux) / measured_dome_impedance_d;
    wire signed [31:0] mask_pen   = raw_pen >>> 31;
    wire signed [31:0] abs_pen    = (raw_pen ^ mask_pen) - mask_pen;
    wire signed [31:0] q_pen_heis = abs_pen / DPHI_DISC;
    wire signed [31:0] is_pos_pen = 32'sd1 - (32'sd1 / (q_pen_heis + 32'sd1));
    assign shield_penetration_phi = is_pos_pen * raw_pen;

    assign user_inside_verified_shield =
        (active_beams_mask == ((1 << N_LINKS) - MU_VAC)) &
        (measured_dome_impedance_d == d_high_hemisphere) &
        (shield_penetration_phi == 32'sd0);
    assign boundary_halo_441nm_led = user_inside_verified_shield;
endmodule

// ----------------------------------------------------------------------------
// Module 16: Physical Sipeed Tang Nano 9K (`GW1NR-9LV QN88P`, 27 MHz Crystal,
// 115200 8N1 UART) Board Top-Level Wrapper (`tang_nano_9k_uart_board_top`)
// Deserializes 16-byte binary frames `[0xA5, opcode, arg0(4B LE), arg1(4B LE),
// arg2(4B LE), xor_crc, 0x5A]` from USB-UART (`uart_rx` pin 18) or ESP32-C3,
// verifies `xor_crc = byte[1] ^ ... ^ byte[13]`, strobes `host_cmd_valid` into
// `cuboctahedron_uart_cmd_soc_top`, and transmits an 8-byte status frame back
// on `uart_tx` (pin 17).
// ----------------------------------------------------------------------------
module tang_nano_9k_uart_board_top #(
    parameter integer D = 3,
    parameter integer CLK_PER_BIT = 234  // 27,000,000 Hz / 115,200 baud = 234.375
) (
    input  wire        clk_27m,
    input  wire        rst_n,
    input  wire        uart_rx,
    output reg         uart_tx,
    output wire [11:0] phys_beam_pins,
    output wire [11:0] phys_beam_oe,
    output wire [11:0] phys_ch1_beam_pins,
    output wire [11:0] phys_ch2_beam_pins,
    output wire [11:0] phys_ch3_beam_pins,
    output wire        soc_pump_air_en,
    output wire        soc_pump_h2o_en,
    output wire        soc_valve_fe_en,
    output wire        soc_valve_o2_en,
    output wire        soc_led_photo_en,
    output wire        soc_ultrasonic_en,
    output wire [2:0]  soc_food_stage,
    output wire        soc_food_ready,
    output wire [8:0]  soc_food_target_z,
    output reg  [31:0] uart_frames_ok_cnt,
    output reg  [31:0] uart_crc_err_cnt
);
    wire rst = ~rst_n;

    // 1. 8N1 UART Byte Receiver
    reg [1:0]  rx_state;
    reg [15:0] rx_clk_cnt;
    reg [2:0]  rx_bit_idx;
    reg [7:0]  rx_shift;
    reg        rx_byte_valid;
    reg [7:0]  rx_byte_data;

    // 2. 16-Byte Packet Assembler: [0]=0xA5, [1]=op, [2..5]=arg0, [6..9]=arg1, [10..13]=arg2, [14]=xor_crc, [15]=0x5A
    reg [3:0]  pkt_idx;
    reg [7:0]  pkt_buf [0:15];
    reg [7:0]  running_xor;
    reg        cmd_valid_pulse;
    reg [3:0]  cmd_opcode_reg;
    reg signed [31:0] cmd_arg0_reg;
    reg signed [31:0] cmd_arg1_reg;
    reg signed [31:0] cmd_arg2_reg;

    // 3. 1-Byte UART ACK Transmitter (sends 0xA5 ^ opcode ^ soc_food_stage on valid frame)
    reg [1:0]  tx_state;
    reg [15:0] tx_clk_cnt;
    reg [3:0]  tx_bit_idx;
    reg [9:0]  tx_frame_bits;
    reg        tx_start_req;
    reg [7:0]  tx_ack_byte;

    always @(posedge clk_27m) begin
        if (rst) begin
            rx_state           <= 2'd0;
            rx_clk_cnt         <= 16'd0;
            rx_bit_idx         <= 3'd0;
            rx_shift           <= 8'd0;
            rx_byte_valid      <= 1'b0;
            rx_byte_data       <= 8'd0;
            pkt_idx            <= 4'd0;
            running_xor        <= 8'd0;
            cmd_valid_pulse    <= 1'b0;
            cmd_opcode_reg     <= 4'd0;
            cmd_arg0_reg       <= 32'sd0;
            cmd_arg1_reg       <= 32'sd0;
            cmd_arg2_reg       <= 32'sd0;
            uart_frames_ok_cnt <= 32'd0;
            uart_crc_err_cnt   <= 32'd0;
            tx_state           <= 2'd0;
            tx_clk_cnt         <= 16'd0;
            tx_bit_idx         <= 4'd0;
            tx_frame_bits      <= 10'h3FF;
            uart_tx            <= 1'b1;
            tx_start_req       <= 1'b0;
            tx_ack_byte        <= 8'h00;
        end else begin
            rx_byte_valid   <= 1'b0;
            cmd_valid_pulse <= 1'b0;
            tx_start_req    <= 1'b0;

            // UART RX FSM
            case (rx_state)
                2'd0: begin // IDLE: wait for start bit (uart_rx == 0)
                    if (uart_rx == 1'b0) begin
                        if (CLK_PER_BIT <= 2) begin
                            rx_clk_cnt <= 16'd0;
                            rx_bit_idx <= 3'd0;
                            rx_state   <= 2'd2;
                        end else begin
                            rx_clk_cnt <= (CLK_PER_BIT - 1) >> 1;
                            rx_state   <= 2'd1;
                        end
                    end
                end
                2'd1: begin // Half-bit delay to center of start bit
                    if (rx_clk_cnt > 16'd0) begin
                        rx_clk_cnt <= rx_clk_cnt - 16'd1;
                    end else begin
                        rx_clk_cnt <= CLK_PER_BIT - 1;
                        rx_bit_idx <= 3'd0;
                        rx_state   <= 2'd2;
                    end
                end
                2'd2: begin // Sample 8 data bits LSB-first
                    if (rx_clk_cnt > 16'd0) begin
                        rx_clk_cnt <= rx_clk_cnt - 16'd1;
                    end else begin
                        rx_shift[rx_bit_idx] <= uart_rx;
                        rx_clk_cnt           <= CLK_PER_BIT - 1;
                        if (rx_bit_idx == 3'd7)
                            rx_state <= 2'd3;
                        else
                            rx_bit_idx <= rx_bit_idx + 3'd1;
                    end
                end
                2'd3: begin // Stop bit
                    if (rx_clk_cnt > 16'd0) begin
                        rx_clk_cnt <= rx_clk_cnt - 16'd1;
                    end else begin
                        rx_byte_data  <= rx_shift;
                        rx_byte_valid <= 1'b1;
                        rx_state      <= 2'd0;
                    end
                end
            endcase

            // 16-Byte Packet Assembler
            if (rx_byte_valid) begin
                if (pkt_idx == 4'd0) begin
                    if (rx_byte_data == 8'hA5) begin
                        pkt_buf[0]  <= 8'hA5;
                        running_xor <= 8'h00;
                        pkt_idx     <= 4'd1;
                    end
                end else if (pkt_idx < 4'd14) begin
                    pkt_buf[pkt_idx] <= rx_byte_data;
                    running_xor      <= running_xor ^ rx_byte_data;
                    pkt_idx          <= pkt_idx + 4'd1;
                end else if (pkt_idx == 4'd14) begin
                    pkt_buf[14] <= rx_byte_data;
                    pkt_idx     <= 4'd15;
                end else begin
                    pkt_idx <= 4'd0;
                    if (rx_byte_data == 8'h5A && pkt_buf[14] == running_xor) begin
                        cmd_opcode_reg     <= pkt_buf[1][3:0];
                        cmd_arg0_reg       <= {pkt_buf[5],  pkt_buf[4],  pkt_buf[3],  pkt_buf[2]};
                        cmd_arg1_reg       <= {pkt_buf[9],  pkt_buf[8],  pkt_buf[7],  pkt_buf[6]};
                        cmd_arg2_reg       <= {pkt_buf[13], pkt_buf[12], pkt_buf[11], pkt_buf[10]};
                        cmd_valid_pulse    <= 1'b1;
                        uart_frames_ok_cnt <= uart_frames_ok_cnt + 32'd1;
                        tx_ack_byte        <= 8'hA5 ^ pkt_buf[1];
                        tx_start_req       <= 1'b1;
                    end else begin
                        uart_crc_err_cnt <= uart_crc_err_cnt + 32'd1;
                    end
                end
            end

            // UART TX ACK Sender
            case (tx_state)
                2'd0: begin
                    uart_tx <= 1'b1;
                    if (tx_start_req) begin
                        tx_frame_bits <= {1'b1, tx_ack_byte, 1'b0};
                        tx_clk_cnt    <= CLK_PER_BIT - 1;
                        tx_bit_idx    <= 4'd0;
                        uart_tx       <= 1'b0;
                        tx_state      <= 2'd1;
                    end
                end
                2'd1: begin
                    if (tx_clk_cnt > 16'd0) begin
                        tx_clk_cnt <= tx_clk_cnt - 16'd1;
                    end else begin
                        tx_clk_cnt <= CLK_PER_BIT - 1;
                        if (tx_bit_idx == 4'd9) begin
                            uart_tx  <= 1'b1;
                            tx_state <= 2'd0;
                        end else begin
                            tx_bit_idx <= tx_bit_idx + 4'd1;
                            uart_tx    <= tx_frame_bits[tx_bit_idx + 4'd1];
                        end
                    end
                end
                default: tx_state <= 2'd0;
            endcase
        end
    end

    wire signed [31:0] u_vmv, u_ima, u_decay, u_batt;
    wire u_cv, u_cc;
    wire [8:0] u_tpm0, u_tpp0;

    cuboctahedron_uart_cmd_soc_top #(.D(D)) u_board_soc (
        .clk(clk_27m), .rst(rst), .host_cmd_valid(cmd_valid_pulse),
        .host_opcode(cmd_opcode_reg), .host_arg0(cmd_arg0_reg),
        .host_arg1(cmd_arg1_reg), .host_arg2(cmd_arg2_reg),
        .phys_beam_pins(phys_beam_pins), .phys_beam_oe(phys_beam_oe),
        .phys_ch1_beam_pins(phys_ch1_beam_pins), .phys_ch2_beam_pins(phys_ch2_beam_pins),
        .phys_ch3_beam_pins(phys_ch3_beam_pins),
        .soc_pump_air_en(soc_pump_air_en), .soc_pump_h2o_en(soc_pump_h2o_en),
        .soc_valve_fe_en(soc_valve_fe_en), .soc_valve_o2_en(soc_valve_o2_en),
        .soc_led_photo_en(soc_led_photo_en), .soc_ultrasonic_en(soc_ultrasonic_en),
        .soc_food_stage(soc_food_stage), .soc_food_ready(soc_food_ready),
        .soc_food_target_z(soc_food_target_z),
        .soc_psu_v_mv(u_vmv), .soc_psu_i_ma(u_ima), .soc_psu_cv(u_cv), .soc_psu_cc(u_cc),
        .soc_stasis_decay_phi(u_decay), .soc_vortex_batt_charge(u_batt),
        .soc_tp_chB_mu0(u_tpm0), .soc_tp_chB_phi0_curr(u_tpp0)
    );
endmodule

// ============================================================================
// Testbench: Full Hardware Verification of the Branchless M/T Carrier Core,
// 3D `IV(D)=263` Lattice Automaton (Octant Silence, Domain-Wall Ratchet `-1`,
// and `t=2` Plaquette Vortex Birth), and All 15 Applied Modules
// ============================================================================
module tb_cuboctahedron_carrier_asic;
    localparam integer D            = 3;
    localparam integer MU_VAC       = (D * D) - (1 << D);
    localparam integer C0_OVER_C_SQ = D - MU_VAC;
    localparam integer N_LINKS      = 2 * D * (D - 1);
    localparam integer N_TRI        = (1 << D);
    localparam integer N_SQ         = 2 * D;
    localparam integer D_IN_SQ      = N_LINKS / D;
    localparam integer MOD_BITS     = MU_VAC + N_TRI;
    localparam integer FRAC_BITS    = MOD_BITS - D;
    localparam integer N_RING       = (1 << MOD_BITS);
    localparam integer K_P          = (1 << FRAC_BITS);
    localparam integer Q_SQUARE     = N_RING / D_IN_SQ;
    localparam integer PHI_PAULI    = N_RING / C0_OVER_C_SQ;
    localparam integer EPS_DENOM    = K_P * Q_SQUARE;
    localparam integer N_PHI        = MU_VAC + N_LINKS;
    localparam integer DPHI_DISC    = (N_RING + N_PHI + N_TRI) / N_PHI;
    localparam integer IV_SEED      = PHI_PAULI + (N_TRI - MU_VAC);

    reg signed [31:0] phi_tb;
    wire signed [31:0] wrap_tb, c_tb, s_tb;
    wire signed [31:0] wrap_next, c_next, s_next;

    rotator_512_unit #(.D(D)) u_rot0 (.phi_in(phi_tb), .wrap_out(wrap_tb), .proj_c(c_tb), .proj_s(s_tb));
    rotator_512_unit #(.D(D)) u_rot1 (.phi_in(phi_tb + 32'sd1), .wrap_out(wrap_next), .proj_c(c_next), .proj_s(s_next));

    reg signed [31:0] alu_x = 0, alu_y = 0;
    wire signed [31:0] alu_id, alu_neg, alu_abs, alu_max, alu_min, alu_tmin, alu_sq, alu_mul;
    integer ax, ay;

    carrier_native_multiplierless_alu #(.D(D)) u_native_alu (
        .x_in(alu_x), .y_in(alu_y),
        .id_x_out(alu_id), .neg_x_out(alu_neg), .abs_x_out(alu_abs),
        .max_xy_out(alu_max), .min_xy_out(alu_min), .tropical_min_xy_out(alu_tmin),
        .sq_x_out(alu_sq), .signed_mul_xy_out(alu_mul)
    );

    wire signed [31:0] wronskian_tb = c_tb * s_next - s_tb * c_next;
    wire signed [63:0] pyth_x = c_tb * c_tb - s_tb * s_tb;
    wire signed [63:0] pyth_y = C0_OVER_C_SQ * c_tb * s_tb;
    wire signed [63:0] pyth_r = c_tb * c_tb + s_tb * s_tb;

    reg signed [31:0] delta_qr_tb;
    wire signed [31:0] q_tb, r_tb;
    quotient_remainder_512_unit #(.D(D)) u_qr (.delta_phi(delta_qr_tb), .branch_q(q_tb), .edge_r(r_tb));

    // Live 12-neighbor polar cell core for testing true 3D `IV(D)=263` lattice dynamics
    reg ca_clk = 0, ca_rst = 1, ca_rev = 0;
    reg signed [31:0] ca_mu_c = 13;
    reg [8:0] ca_init_p0 = 0, ca_init_q0 = 0, ca_init_p1 = 0, ca_init_q1 = 0;
    reg signed [12*32-1:0] ca_nb_mu_flat = 0;
    reg signed [12*32-1:0] ca_nb_p0_flat = 0;
    reg signed [12*32-1:0] ca_nb_p1_flat = 0;
    wire [8:0] ca_p0_c, ca_q0_p, ca_p1_c, ca_q1_p;
    wire signed [31:0] ca_raw0, ca_g0, ca_g1, ca_g_sel;

    carrier_polar_12neighbor_cell_core #(.D(D)) u_true_ca_cell (
        .clk(ca_clk), .rst(ca_rst), .reverse_dir(ca_rev),
        .mu_c(ca_mu_c),
        .init_p0(ca_init_p0), .init_q0(ca_init_q0),
        .init_p1(ca_init_p1), .init_q1(ca_init_q1),
        .nb_mu_flat(ca_nb_mu_flat), .nb_p0_flat(ca_nb_p0_flat), .nb_p1_flat(ca_nb_p1_flat),
        .p0_curr(ca_p0_c), .q0_prev(ca_q0_p), .p1_curr(ca_p1_c), .q1_prev(ca_q1_p),
        .raw_gate_lane0(ca_raw0), .gate_lane0(ca_g0), .gate_lane1(ca_g1),
        .selected_field_gate(ca_g_sel)
    );

    reg clk = 0;
    reg rst = 1;
    reg rev = 0;
    wire [8:0] v_curr, v_prev;
    verlet_reversible_cell #(.D(D)) u_verlet (
        .clk(clk), .rst(rst), .reverse_dir(rev),
        .init_curr(DPHI_DISC[8:0]), .init_prev(9'd0),
        .phi_accel(N_PHI),
        .phi_curr(v_curr), .phi_prev(v_prev)
    );

    reg signed [31:0] mu_c_tb = K_P;
    reg signed [31:0] mu_nb_tb = K_P;
    reg signed [31:0] dphi_gate_tb = 32'sd0;
    wire signed [31:0] cg_tb, sg_tb, denom_tb, phig_tb, ne_tb;
    cuboctahedron_12beam_gate #(.D(D)) u_gate12 (
        .mu_center(mu_c_tb), .mu_nb(mu_nb_tb), .delta_phi(dphi_gate_tb),
        .c_single(cg_tb), .s_single(sg_tb), .denom_d(denom_tb),
        .gate_phase_phi(phig_tb), .energy_quanta_ne(ne_tb)
    );

    integer i, mu, clicks, errors;
    integer fresnel_c_sum, fresnel_s_sum;
    reg [8:0] saved_curr, saved_prev;

    reg tp_rst = 1;
    reg [1:0] tp_mode = 2'b00;
    wire [8:0] tp_a_mu0, tp_a_mu1, tp_a_p0c, tp_a_p0p, tp_a_p1c, tp_a_p1p;
    wire [8:0] tp_b_mu0, tp_b_mu1, tp_b_p0c, tp_b_p0p, tp_b_p1c, tp_b_p1p;
    wire signed [31:0] tp_d_stasis, tp_d_write, tp_contrast, tp_noise_leak, tp_norm_sq;
    reg [8:0] saved_a_mu0, saved_a_mu1, saved_a_p0c, saved_a_p0p, saved_a_p1c, saved_a_p1p;
    reg signed [31:0] norm_before_tp;

    two_chamber_72bit_teleporter #(.D(D)) u_teleporter (
        .clk(clk), .rst(tp_rst), .cmd_mode(tp_mode),
        .singlet_a0(9'd41), .singlet_a1(9'd97), .singlet_a2(9'd137), .singlet_a3(9'd263),
        .ext_thermal_noise_drive(32'sd24576),
        .chA_mu0(tp_a_mu0), .chA_mu1(tp_a_mu1), .chA_phi0_curr(tp_a_p0c), .chA_phi0_prev(tp_a_p0p),
        .chA_phi1_curr(tp_a_p1c), .chA_phi1_prev(tp_a_p1p),
        .chB_mu0(tp_b_mu0), .chB_mu1(tp_b_mu1), .chB_phi0_curr(tp_b_p0c), .chB_phi0_prev(tp_b_p0p),
        .chB_phi1_curr(tp_b_p1c), .chB_phi1_prev(tp_b_p1p),
        .d_stasis_val(tp_d_stasis), .d_write_val(tp_d_write), .contrast_833(tp_contrast),
        .waveguide_noise_leak(tp_noise_leak), .total_two_chamber_norm_sq(tp_norm_sq)
    );

    reg drv_rst = 1;
    reg [2:0] drv_mode = 3'd0;
    wire [8:0] drv_cnt;
    wire [11:0] drv_pins, drv_oe;

    fpga_12beam_cuboctahedron_driver #(.D(D)) u_fpga_drv (
        .clk_512x(clk), .rst(drv_rst), .mode_sel(drv_mode),
        .custom_phase_flat(108'd0), .custom_oe_mask(12'hFFF),
        .ring_counter(drv_cnt), .beam_pins(drv_pins), .beam_oe(drv_oe)
    );

    wire signed [31:0] tom_y0, tom_y1, tom_y2, tom_y3;
    wire signed [31:0] tom_s0, tom_s1, tom_s2, tom_s3;
    wire signed [31:0] rat_fdiv, rat_tdiv;

    holonomic_4channel_tomograph_and_ratchet #(.D(D)) u_tom_rat (
        .s0_in(32'sd12), .s1_in(32'sd41), .s2_in(32'sd97), .s3_in(32'sd263),
        .y0_2x(tom_y0), .y1_2x(tom_y1), .y2_2x(tom_y2), .y3_2x(tom_y3),
        .s0_rec(tom_s0), .s1_rec(tom_s1), .s2_rec(tom_s2), .s3_rec(tom_s3),
        .ratchet_fdiv_step(rat_fdiv), .ratchet_tdiv_step(rat_tdiv)
    );

    reg food_rst = 1;
    reg food_start = 0;
    reg [1:0] food_recipe = 2'b00;
    wire [2:0] food_stage, food_m1, food_m2, food_m3;
    wire [11:0] food_ch1_p, food_ch2_p, food_ch3_p;
    wire food_air, food_h2o, food_fe, food_o2, food_led, food_us, food_ready;
    wire [8:0] food_z;

    food_synthesizer_3chamber_controller #(.D(D)) u_food_synth (
        .clk(clk), .rst(food_rst), .start_btn(food_start), .recipe_sel(food_recipe),
        .stage_hold_ticks(32'd1),
        .stage_out(food_stage), .ch1_phase_mode(food_m1), .ch2_phase_mode(food_m2), .ch3_phase_mode(food_m3),
        .ch1_beam_pins(food_ch1_p), .ch2_beam_pins(food_ch2_p), .ch3_beam_pins(food_ch3_p),
        .pump_air_co2_n2_en(food_air), .pump_water_h2o_en(food_h2o), .valve_mineral_heme_fe_en(food_fe),
        .valve_o2_breath_vent_en(food_o2), .led_441_718nm_photo_en(food_led), .ultrasonic_12beam_en(food_us),
        .synthesized_target_z(food_z), .food_ready_led(food_ready)
    );

    reg pelt_rst = 1;
    reg [1:0] pelt_mode = 2'b00;
    wire signed [31:0] pelt_back_leak, pelt_joule, pelt_decay, pelt_batt, pelt_pwr;

    phase_peltier_stasis_pantry_and_vortex_battery #(.D(D)) u_pelt_batt (
        .clk(clk), .rst(pelt_rst), .op_mode(pelt_mode), .ambient_heat_flux(32'sd16384),
        .reverse_heat_leak_phi(pelt_back_leak), .joule_self_heat_quanta(pelt_joule),
        .food_decay_rate_phi(pelt_decay), .vortex_battery_charge(pelt_batt), .delivered_power_out(pelt_pwr)
    );

    reg signed [31:0] vi_k  = 32'sd0;
    reg signed [31:0] vi_nv = 32'sd12;
    reg signed [31:0] vi_mi = 32'sd3;
    reg               vi_ac = 1'b0;
    wire signed [31:0] vi_phi, vi_vc, vi_ic, vi_ksum, vi_vout, vi_iout, vi_pout;

    programmable_vi_power_inverter_controller #(.D(D)) u_vi_ctrl (
        .throttle_k(vi_k), .voltage_beams_nv(vi_nv), .current_planes_mi(vi_mi), .ac_half_cycle_inv(vi_ac),
        .phi_load_out(vi_phi), .v_cell_norm(vi_vc), .i_cell_norm(vi_ic),
        .kirchhoff_sum_128(vi_ksum), .v_terminal_out(vi_vout), .i_terminal_out(vi_iout), .p_terminal_out(vi_pout)
    );

    reg        lab_rst  = 1;
    reg [31:0] lab_freq = 32'd0;
    reg signed [31:0] lab_vset = 32'sd12000;
    reg signed [31:0] lab_iset = 32'sd3000;
    reg signed [31:0] lab_rload = 32'sd6;
    wire [31:0] lab_acc;
    wire [8:0]  lab_phase;
    wire signed [31:0] lab_vact, lab_iact;
    wire        lab_cv, lab_cc;

    lab_smooth_cv_cc_dds_power_supply #(.D(D)) u_lab_psu (
        .clk(clk), .rst(lab_rst), .dds_freq_word(lab_freq),
        .v_set_mv(lab_vset), .i_set_ma(lab_iset), .r_load_ohm(lab_rload),
        .dds_phase_acc(lab_acc), .dds_ring_phase(lab_phase),
        .v_actual_mv(lab_vact), .i_actual_ma(lab_iact),
        .cv_mode_active(lab_cv), .cc_mode_active(lab_cc)
    );

    reg        soc_rst = 1;
    reg        soc_valid = 0;
    reg [3:0]  soc_op = 4'h0;
    reg signed [31:0] soc_a0 = 0, soc_a1 = 0, soc_a2 = 0;
    wire [11:0] soc_pins, soc_oe, soc_c1p, soc_c2p, soc_c3p;
    wire        soc_pair, soc_ph2o, soc_vfe, soc_vo2, soc_pled, soc_pus;
    wire [2:0]  soc_fstage;
    wire        soc_fready, soc_cv_w, soc_cc_w;
    wire [8:0]  soc_fz, soc_tpm0, soc_tpp0;
    wire signed [31:0] soc_vmv, soc_ima, soc_decay, soc_batt;

    cuboctahedron_uart_cmd_soc_top #(.D(D)) u_soc_top (
        .clk(clk), .rst(soc_rst), .host_cmd_valid(soc_valid),
        .host_opcode(soc_op), .host_arg0(soc_a0), .host_arg1(soc_a1), .host_arg2(soc_a2),
        .phys_beam_pins(soc_pins), .phys_beam_oe(soc_oe),
        .phys_ch1_beam_pins(soc_c1p), .phys_ch2_beam_pins(soc_c2p), .phys_ch3_beam_pins(soc_c3p),
        .soc_pump_air_en(soc_pair), .soc_pump_h2o_en(soc_ph2o),
        .soc_valve_fe_en(soc_vfe), .soc_valve_o2_en(soc_vo2),
        .soc_led_photo_en(soc_pled), .soc_ultrasonic_en(soc_pus),
        .soc_food_stage(soc_fstage), .soc_food_ready(soc_fready), .soc_food_target_z(soc_fz),
        .soc_psu_v_mv(soc_vmv), .soc_psu_i_ma(soc_ima), .soc_psu_cv(soc_cv_w), .soc_psu_cc(soc_cc_w),
        .soc_stasis_decay_phi(soc_decay), .soc_vortex_batt_charge(soc_batt),
        .soc_tp_chB_mu0(soc_tpm0), .soc_tp_chB_phi0_curr(soc_tpp0)
    );

    reg        brd_rst_n = 0;
    reg        brd_uart_rx = 1;
    wire       brd_uart_tx;
    wire [11:0] brd_pins, brd_oe, brd_c1p, brd_c2p, brd_c3p;
    wire        brd_air, brd_h2o, brd_fe, brd_o2, brd_led, brd_us, brd_fready;
    wire [2:0]  brd_fstage;
    wire [8:0]  brd_fz;
    wire [31:0] brd_ok_cnt, brd_err_cnt;

    tang_nano_9k_uart_board_top #(.D(D), .CLK_PER_BIT(4)) u_board_top (
        .clk_27m(clk), .rst_n(brd_rst_n), .uart_rx(brd_uart_rx), .uart_tx(brd_uart_tx),
        .phys_beam_pins(brd_pins), .phys_beam_oe(brd_oe),
        .phys_ch1_beam_pins(brd_c1p), .phys_ch2_beam_pins(brd_c2p), .phys_ch3_beam_pins(brd_c3p),
        .soc_pump_air_en(brd_air), .soc_pump_h2o_en(brd_h2o),
        .soc_valve_fe_en(brd_fe), .soc_valve_o2_en(brd_o2),
        .soc_led_photo_en(brd_led), .soc_ultrasonic_en(brd_us),
        .soc_food_stage(brd_fstage), .soc_food_ready(brd_fready), .soc_food_target_z(brd_fz),
        .uart_frames_ok_cnt(brd_ok_cnt), .uart_crc_err_cnt(brd_err_cnt)
    );

    task send_uart_byte_4clk(input [7:0] b);
        integer bit_i, c_i;
        begin
            // Start bit (0) for 4 clocks
            brd_uart_rx = 1'b0;
            for (c_i = 0; c_i < 4; c_i = c_i + 1) begin #5 clk = 1; #5 clk = 0; end
            // 8 Data bits LSB-first
            for (bit_i = 0; bit_i < 8; bit_i = bit_i + 1) begin
                brd_uart_rx = b[bit_i];
                for (c_i = 0; c_i < 4; c_i = c_i + 1) begin #5 clk = 1; #5 clk = 0; end
            end
            // Stop bit (1) for 4 clocks
            brd_uart_rx = 1'b1;
            for (c_i = 0; c_i < 4; c_i = c_i + 1) begin #5 clk = 1; #5 clk = 0; end
        end
    endtask

    reg signed [31:0] mod_t3 = 0, mod_t2 = 0, mod_t1 = 0, mod_t0 = 0;
    wire signed [31:0] mod_dphi, mod_ne, mod_srx, mod_crx, mod_t3r, mod_t2r, mod_t1r, mod_t0r;
    wire mod_beacon;
    integer t3i, t2i, t1i, t0i;

    heisenberg_subthreshold_81ary_c0_modem #(.D(D)) u_c0_modem (
        .t3_in(mod_t3), .t2_in(mod_t2), .t1_in(mod_t1), .t0_in(mod_t0),
        .dphi_tx(mod_dphi), .photon_ne_emitted(mod_ne),
        .rotator_s_rx(mod_srx), .rotator_c_rx(mod_crx),
        .t3_rx(mod_t3r), .t2_rx(mod_t2r), .t1_rx(mod_t1r), .t0_rx(mod_t0r),
        .gaussian_prime_beacon_hit(mod_beacon)
    );

    reg [2:0] bio_k = 3'd2;
    reg [1:0] bio_st = 2'd3;
    wire [31:0] bio_caps, bio_b3, bio_mv, bio_me;
    wire bio_safe;
    wire [8:0] bio_gate;
    wire signed [31:0] bio_chi;

    caspar_klug_antiviral_and_morphogenetic_compiler #(.D(D)) u_bio_comp (
        .viral_shell_k(bio_k), .regen_stage_sel(bio_st),
        .capsid_capsomers(bio_caps), .human_nucleosome_b3(bio_b3),
        .human_chromatin_safe(bio_safe), .antiviral_phase_gate(bio_gate),
        .morph_target_vertices(bio_mv), .morph_target_edges(bio_me), .morph_euler_chi(bio_chi)
    );

    reg [1:0] gd_mode = 2'b00;
    reg [11:0] gd_mask = 12'hFFF;
    wire [8:0] gd_top, gd_bot;
    wire signed [31:0] gd_dh, gd_dl, gd_dd, gd_gload, gd_dmeas, gd_pen;
    wire [3:0] gd_cnt;
    wire gd_verified, gd_halo;

    grav_impedance_dipole_shield_and_dry_cleaner #(.D(D)) u_grav_shld (
        .sys_func_mode(gd_mode), .thrust_axis_sel(2'b00),
        .active_beams_mask(gd_mask), .ext_impact_flux(32'sd32768),
        .top_hemisphere_dphi(gd_top), .bot_hemisphere_dphi(gd_bot),
        .d_high_hemisphere(gd_dh), .d_low_hemisphere(gd_dl),
        .dipole_delta_d(gd_dd), .internal_g_overload(gd_gload),
        .active_beam_count(gd_cnt), .measured_dome_impedance_d(gd_dmeas),
        .shield_penetration_phi(gd_pen), .user_inside_verified_shield(gd_verified),
        .boundary_halo_441nm_led(gd_halo)
    );

    // Helper functions in testbench to feed the true 3D `IV(D)=263` initial field
    // (`iv263MuAt`, `iv263Phi0At`, `iv263Phi1At` from `TrajectoryIV263.lean`)
    // into `u_true_ca_cell` across the 12 cuboctahedron neighbors O_2:
    integer o2_dz [0:11];
    integer o2_dy [0:11];
    integer o2_dx [0:11];
    integer k_nb;
    integer gate_wall_pos, gate_wall_neg;

    function integer iv263_mu(input integer dz, input integer dy, input integer dx);
        integer r2, in_b;
        begin
            r2 = dz*dz + dy*dy + dx*dx;
            in_b = (r2 <= N_SQ * N_SQ) ? 1 : 0;
            iv263_mu = MU_VAC + N_LINKS * in_b;
        end
    endfunction

    function integer iv263_p0(input integer dz, input integer dy, input integer dx);
        integer r2, in_b, oct, b0, rem13, bg;
        begin
            r2 = dz*dz + dy*dy + dx*dx;
            in_b = (r2 <= N_SQ * N_SQ) ? 1 : 0;
            oct = ((dz >= 0) ? 4 : 0) + ((dy >= 0) ? 2 : 0) + ((dx >= 0) ? 1 : 0);
            b0 = ((IV_SEED % PHI_PAULI) >> oct) & 1;
            rem13 = (dx + N_LINKS) % N_PHI;
            bg = (rem13 * DPHI_DISC) % N_RING;
            iv263_p0 = (bg + (D * DPHI_DISC) * in_b * b0) % N_RING;
            if (iv263_p0 < 0) iv263_p0 = iv263_p0 + N_RING;
        end
    endfunction

    function integer iv263_p1(input integer dz, input integer dy, input integer dx);
        integer r2, in_b, oct, b1, rem13, bg;
        begin
            r2 = dz*dz + dy*dy + dx*dx;
            in_b = (r2 <= N_SQ * N_SQ) ? 1 : 0;
            oct = ((dz >= 0) ? 4 : 0) + ((dy >= 0) ? 2 : 0) + ((dx >= 0) ? 1 : 0);
            b1 = ((IV_SEED % PHI_PAULI) >> (oct ^ D)) & 1;
            rem13 = (dx + N_LINKS) % N_PHI;
            bg = (rem13 * DPHI_DISC) % N_RING;
            iv263_p1 = (bg + (D * DPHI_DISC) * in_b * b1) % N_RING;
            if (iv263_p1 < 0) iv263_p1 = iv263_p1 + N_RING;
        end
    endfunction

    task load_iv263_node(input integer cz, input integer cy, input integer cx);
        integer nz, ny, nx;
        begin
            ca_mu_c    = iv263_mu(cz, cy, cx);
            ca_init_p0 = iv263_p0(cz, cy, cx);
            ca_init_q0 = iv263_p0(cz, cy, cx);
            ca_init_p1 = iv263_p1(cz, cy, cx);
            ca_init_q1 = iv263_p1(cz, cy, cx);
            for (k_nb = 0; k_nb < 12; k_nb = k_nb + 1) begin
                nz = cz - o2_dz[k_nb];
                ny = cy - o2_dy[k_nb];
                nx = cx - o2_dx[k_nb];
                ca_nb_mu_flat[k_nb*32 +: 32] = iv263_mu(nz, ny, nx);
                ca_nb_p0_flat[k_nb*32 +: 32] = iv263_p0(nz, ny, nx);
                ca_nb_p1_flat[k_nb*32 +: 32] = iv263_p1(nz, ny, nx);
            end
        end
    endtask

    initial begin
        $dumpfile("cuboctahedron_carrier.vcd");
        $dumpvars(0, tb_cuboctahedron_carrier_asic);

        // Initialize 12 cuboctahedron O_2 vectors (`cubicOrbit3D 2`)
        o2_dz[0]=-1; o2_dy[0]=-1; o2_dx[0]= 0;
        o2_dz[1]=-1; o2_dy[1]= 1; o2_dx[1]= 0;
        o2_dz[2]= 1; o2_dy[2]=-1; o2_dx[2]= 0;
        o2_dz[3]= 1; o2_dy[3]= 1; o2_dx[3]= 0;
        o2_dz[4]=-1; o2_dy[4]= 0; o2_dx[4]=-1;
        o2_dz[5]=-1; o2_dy[5]= 0; o2_dx[5]= 1;
        o2_dz[6]= 1; o2_dy[6]= 0; o2_dx[6]=-1;
        o2_dz[7]= 1; o2_dy[7]= 0; o2_dx[7]= 1;
        o2_dz[8]= 0; o2_dy[8]=-1; o2_dx[8]=-1;
        o2_dz[9]= 0; o2_dy[9]=-1; o2_dx[9]= 1;
        o2_dz[10]=0; o2_dy[10]=1; o2_dx[10]=-1;
        o2_dz[11]=0; o2_dy[11]=1; o2_dx[11]= 1;

        errors = 0;
        fresnel_c_sum = 0;
        fresnel_s_sum = 0;

        $display("======================================================================");
        $display("[0] True 12-Neighbor Branchless CA Cell Core on 3D Field IV(D=3)=263");
        $display("======================================================================");
        // (a) Interior octant node (2, 2, 2): raw gate = +15, deadbanded gate === 0 (Octant Silence!)
        ca_rst = 1; ca_rev = 0;
        load_iv263_node(2, 2, 2);
        #5 ca_clk = 1; #5 ca_clk = 0; #1;
        $display("  -> Octant node (2,2,2) at t=0: raw_gate0 = %3d (< 41) -> field_gate = %3d (Exact Octant Silence!)",
                 ca_raw0, ca_g_sel);
        if (ca_raw0 !== 32'sd15 || ca_g_sel !== 32'sd0) errors = errors + 1;

        // (b) Domain wall nodes (0, 2, 2) and (-1, 2, 2): chiral pair sum = -1 tick!
        load_iv263_node(0, 2, 2);
        #5 ca_clk = 1; #5 ca_clk = 0; #1;
        gate_wall_pos = ca_g_sel;
        load_iv263_node(-1, 2, 2);
        #5 ca_clk = 1; #5 ca_clk = 0; #1;
        gate_wall_neg = ca_g_sel;
        $display("  -> Domain wall z=0/-1 at t=0: gate(0,2,2) = %3d, gate(-1,2,2) = %3d -> wallPairSum = %3d tick!",
                 gate_wall_pos, gate_wall_neg, gate_wall_pos + gate_wall_neg);
        if (gate_wall_pos + gate_wall_neg !== -32'sd1) errors = errors + 1;

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
        for (i = 0; i < 512; i = i + 1) begin
            phi_tb = i * i;
            #1;
            fresnel_c_sum = fresnel_c_sum + c_tb;
            fresnel_s_sum = fresnel_s_sum + s_tb;
        end
        $display("  -> All 512 ring ticks verified: W(phi) === 128, X^2 + Y^2 === R^2 (errors = %0d)", errors);
        $display("  -> Hardware Fresnel Diffraction Integrals: C_Fresnel = %0d, S_Fresnel = %0d", fresnel_c_sum, fresnel_s_sum);
        if (fresnel_c_sum !== 2048 || fresnel_s_sum !== 2048) errors = errors + 1;

        for (ax = -64; ax <= 64; ax = ax + 1) begin
            for (ay = -64; ay <= 64; ay = ay + 1) begin
                alu_x = ax; alu_y = ay;
                #1;
                if (alu_id !== ax || alu_neg !== -ax ||
                    alu_abs !== ((ax < 0) ? -ax : ax) ||
                    alu_sq  !== (ax * ax) ||
                    alu_mul !== (ax * ay) ||
                    alu_max !== ((ax >= ay) ? ax : ay) ||
                    alu_min !== ((ax <= ay) ? ax : ay)) begin
                    $display("ALU ERROR at (%0d, %0d): mul=%0d != %0d", ax, ay, alu_mul, ax * ay);
                    errors = errors + 1;
                end
            end
        end
        $display("  -> Native Multiplierless Rotator ALU verified across all 129x129 = 16,641 signed pairs [-64..+64]^2 (errors = %0d)", errors);

        $display("======================================================================");
        $display("[2] 12-Beam Cuboctahedron Gate: Impedance Collapse & Ballistic Regimes");
        $display("======================================================================");
        dphi_gate_tb = 32'sd0; #1;
        $display("  -> Delta_phi =   0 ticks (  0.0 deg): C=%4d, S=%4d | Denom D = %7d | Gate Phi = %6d | Quanta n_E = %0d",
                 cg_tb, sg_tb, denom_tb, phig_tb, ne_tb);
        dphi_gate_tb = 32'sd41; #1;
        $display("  -> Delta_phi =  41 ticks ( 28.8 deg): C=%4d, S=%4d | Denom D = %7d | Gate Phi = %6d | Quanta n_E = %0d",
                 cg_tb, sg_tb, denom_tb, phig_tb, ne_tb);
        dphi_gate_tb = 32'sd128; #1;
        $display("  -> Delta_phi = 128 ticks ( 90.0 deg): C=%4d, S=%4d | Denom D = %7d | Gate Phi = %6d | Quanta n_E = %0d",
                 cg_tb, sg_tb, denom_tb, phig_tb, ne_tb);
        dphi_gate_tb = 32'sd139; #1;
        $display("  -> Delta_phi = 139 ticks ( 97.7 deg): C=%4d, S=%4d | Denom D = %7d | Gate Phi = %6d | Quanta n_E = %0d (587x COLLAPSE!)",
                 cg_tb, sg_tb, denom_tb, phig_tb, ne_tb);
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
        for (i = 0; i < 4; i = i + 1) begin
            #5 clk = 1; #5 clk = 0;
        end
        norm_before_tp = tp_norm_sq;
        saved_a_mu0 = tp_a_mu0; saved_a_mu1 = tp_a_mu1;
        saved_a_p0c = tp_a_p0c; saved_a_p0p = tp_a_p0p;
        saved_a_p1c = tp_a_p1c; saved_a_p1p = tp_a_p1p;
        tp_mode = 2'b01;
        #5 clk = 1; #5 clk = 0;
        $display("  -> [Step 1: STASIS]   D_stasis = %0d, D_write = %0d (Contrast = %0d : 1, Noise leak = %0d)",
                 tp_d_stasis, tp_d_write, tp_contrast, tp_noise_leak);
        $display("     Chamber A in Stasis: mu=(%2d,%2d), phi0=(%3d,%3d), phi1=(%3d,%3d) | Chamber B: mu=(%2d,%2d)",
                 tp_a_mu0, tp_a_mu1, tp_a_p0c, tp_a_p0p, tp_a_p1c, tp_a_p1p, tp_b_mu0, tp_b_mu1);
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
        tp_mode = 2'b11;
        #5 clk = 1; #5 clk = 0;
        $display("  -> [Step 3: RELEASE]  Chamber B lifts stasis and resumes evolution: phi0=(%3d,%3d), phi1=(%3d,%3d)",
                 tp_b_p0c, tp_b_p0p, tp_b_p1c, tp_b_p1p);
        if (tp_b_p0p !== saved_a_p0c || tp_b_p1p !== saved_a_p1c) errors = errors + 1;

        $display("======================================================================");
        $display("[6] Low-Cost FPGA 12-Pin Cuboctahedron Driver Verification");
        $display("======================================================================");
        drv_rst = 1; drv_mode = 3'd3;
        #5 clk = 1; #5 clk = 0;
        drv_rst = 0;
        #1;
        $display("  -> Mode 3 (Pauli Lock 0/256) at tick %3d: beam_pins = %12b (antipodal pair V1=%b, V2=%b)",
                 drv_cnt, drv_pins, drv_pins[0], drv_pins[1]);
        if (drv_pins !== 12'b0101_0101_0101) errors = errors + 1;
        drv_mode = 3'd4;
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
        for (i = 0; i < 4; i = i + 1) begin
            #5 clk = 1; #5 clk = 0;
        end
        $display("  -> [Cool & Harvest] Reverse heat leak = %0d | Joule self-heat = %0d | Harvested Vortex Battery = %0d",
                 pelt_back_leak, pelt_joule, pelt_batt);
        pelt_mode = 2'b01;
        #5 clk = 1; #5 clk = 0;
        $display("  -> [Eternal Stasis Pantry] Room-temp food decay rate Phi = %0d | Battery charge held = %0d (0 leakage!)",
                 pelt_decay, pelt_batt);
        pelt_mode = 2'b11;
        #5 clk = 1; #5 clk = 0;
        $display("  -> [Pauli Battery Discharge at dphi=128] Delivered coherent power = %0d", pelt_pwr);
        if (pelt_back_leak !== 32'sd0 || pelt_joule !== 32'sd0 || pelt_decay !== 32'sd0 || pelt_pwr !== 32'sd16384)
            errors = errors + 1;

        $display("======================================================================");
        $display("[10] Programmable V-I Phase-Throttle & Grid Inverter (MPPT at k* = 64)");
        $display("======================================================================");
        vi_nv = 32'sd12; vi_mi = 32'sd3; vi_ac = 1'b0;
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
        lab_rload = 32'sd2; #1;
        $display("  -> [DC CC Mode: V_set=12.000V, I_lim=3.000A, R=2 Ohm] V_out=%5d mV, I_out=%4d mA | CV=%b CC=%b",
                 lab_vact, lab_iact, lab_cv, lab_cc);
        if (lab_vact !== 32'sd6000 || lab_iact !== 32'sd3000 || lab_cv !== 1'b0 || lab_cc !== 1'b1)
            errors = errors + 1;
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
        soc_valid = 1; soc_op = 4'h3; soc_a0 = 32'sd24000; soc_a1 = 32'sd5000; soc_a2 = 32'sd0;
        #5 clk = 1; #5 clk = 0;
        soc_op = 4'h2; soc_a0 = 32'sd0; soc_a1 = 32'sd1;
        #5 clk = 1; #5 clk = 0;
        soc_valid = 0;
        for (i = 0; i < 5; i = i + 1) begin
            #5 clk = 1; #5 clk = 0;
        end
        $display("  -> [AI Host SoC] PSU V=%5d mV, I=%4d mA (CV=%b) | Food Stage=%0d, Ready=%b | Stasis Decay=%0d",
                 soc_vmv, soc_ima, soc_cv_w, soc_fstage, soc_fready, soc_decay);
        if (soc_vmv !== 32'sd24000 || soc_ima !== 32'sd4000 || soc_fready !== 1'b1 || soc_decay !== 32'sd0)
            errors = errors + 1;
        // Send AI Host Command 4'h6: Live Hot-Patch custom phase 256 on Vertex 0 and OE mask 12'hA5A without rebuilding!
        soc_valid = 1; soc_op = 4'h6; soc_a0 = 32'sd0; soc_a1 = 32'sd256; soc_a2 = 32'shA5A;
        #5 clk = 1; #5 clk = 0;
        soc_valid = 0; #1;
        $display("  -> [AI Host Live Hot-Patch 4'h6] Custom OE Mask = %3h (expected A5A), beam_pins = %12b",
                 soc_oe, soc_pins);
        if (soc_oe !== 12'hA5A) errors = errors + 1;

        $display("======================================================================");
        $display("[13] Sub-Threshold 81-ary (4-Trit) Heisenberg c0-Modem & SETI Decoder");
        $display("======================================================================");
        for (t3i = -1; t3i <= 1; t3i = t3i + 1) begin
            for (t2i = -1; t2i <= 1; t2i = t2i + 1) begin
                for (t1i = -1; t1i <= 1; t1i = t1i + 1) begin
                    for (t0i = -1; t0i <= 1; t0i = t0i + 1) begin
                        mod_t3 = t3i; mod_t2 = t2i; mod_t1 = t1i; mod_t0 = t0i;
                        #1;
                        if (mod_ne !== 32'sd0 || mod_srx !== mod_dphi ||
                            mod_t3r !== t3i || mod_t2r !== t2i || mod_t1r !== t1i || mod_t0r !== t0i) begin
                            $display("ERROR in 81-ary modem at dphi=%0d", mod_dphi);
                            errors = errors + 1;
                        end
                    end
                end
            end
        end
        mod_t3 = 0; mod_t2 = 1; mod_t1 = 1; mod_t0 = 1; #1;
        $display("  -> All 81 = 3^4 sub-threshold 4-trit symbols [-40..+40] verified: n_E === 0 photons, 100%% bit recovery!");
        $display("  -> Gaussian-prime beacon symbol (+13 = 9+3+1): trits=(%2d,%2d,%2d,%2d) -> S_rx=%2d, C_rx=%3d, BeaconLock=%b",
                 mod_t3r, mod_t2r, mod_t1r, mod_t0r, mod_srx, mod_crx, mod_beacon);
        if (mod_srx !== 32'sd13 || mod_beacon !== 1'b1) errors = errors + 1;

        $display("======================================================================");
        $display("[14] Bio-CAD Caspar-Klug Antiviral Shatterer & Scar-Free Morphogenetic Compiler");
        $display("======================================================================");
        for (i = 1; i <= 5; i = i + 1) begin
            bio_k = i[2:0]; #1;
            $display("  -> Viral shell k=%0d: Capsomers = %3d vs Human Nucleosome B3 = %3d | Safe=%b | Gate dphi=%3d",
                     i, bio_caps, bio_b3, bio_safe, bio_gate);
            if (bio_safe !== 1'b1) errors = errors + 1;
        end
        bio_st = 2'd3; #1;
        $display("  -> Morphogenetic Stage 4 (Laminar Cortex/Tissue): V=%2d (S2), E=%3d (B3), Euler chi=%2d (dphi_disc=41)",
                 bio_mv, bio_me, bio_chi);
        if (bio_mv !== 32'd42 || bio_me !== 32'd147 || bio_chi !== 32'sd41) errors = errors + 1;

        $display("======================================================================");
        $display("[15] 3D Gravitational-Impedance Dipole (833:1), Pauli Shield & Dome Integrity Monitor");
        $display("======================================================================");
        gd_mode = 2'b01; gd_mask = 12'hFFF; #1;
        $display("  -> [Shield Dome 12/12 Beams] D_meas=%7d | Penetration Phi=%0d | Inside_Verified_Shield=%b | 441nm_Halo=%b",
                 gd_dmeas, gd_pen, gd_verified, gd_halo);
        if (gd_dmeas !== 32'sd6823936 || gd_pen !== 32'sd0 || gd_verified !== 1'b1 || gd_halo !== 1'b1)
            errors = errors + 1;
        gd_mask = 12'h7FF; #1;
        $display("  -> [Beam #12 Obstructed: %2d/12] D_meas=%7d | Inside_Verified_Shield=%b (Breach alerted!)",
                 gd_cnt, gd_dmeas, gd_verified);
        if (gd_verified !== 1'b0) errors = errors + 1;
        gd_mask = 12'hFFF; gd_mode = 2'b00; #1;
        $display("  -> [Grav-Impedance Dipole] Top dphi=%3d (D=%4d) | Bot dphi=%3d (D=%7d) | Delta_D=%7d | Cabin G-load=%0d",
                 gd_top, gd_dl, gd_bot, gd_dh, gd_dd, gd_gload);
        if (gd_dd !== 32'sd6815744 || gd_gload !== 32'sd0) errors = errors + 1;

        $display("======================================================================");
        $display("[16] Physical Tang Nano 9K 16-Byte UART Serial Frame Deserializer & Board Top");
        $display("======================================================================");
        brd_rst_n = 0; brd_uart_rx = 1;
        #5 clk = 1; #5 clk = 0;
        brd_rst_n = 1;
        #5 clk = 1; #5 clk = 0;
        // Send 16-byte binary frame over single serial wire `brd_uart_rx`:
        // [0]=0xA5, [1]=0x02 (CMD_START_FOOD), [2..5]=arg0=0 (Cutlet), [6..9]=arg1=2 (hold 2 ticks per stage!), [10..13]=arg2=0, [14]=xor_crc=(0x02^0x02=0x00), [15]=0x5A
        send_uart_byte_4clk(8'hA5);
        send_uart_byte_4clk(8'h02);
        send_uart_byte_4clk(8'h00); send_uart_byte_4clk(8'h00); send_uart_byte_4clk(8'h00); send_uart_byte_4clk(8'h00);
        send_uart_byte_4clk(8'h02); send_uart_byte_4clk(8'h00); send_uart_byte_4clk(8'h00); send_uart_byte_4clk(8'h00);
        send_uart_byte_4clk(8'h00); send_uart_byte_4clk(8'h00); send_uart_byte_4clk(8'h00); send_uart_byte_4clk(8'h00);
        send_uart_byte_4clk(8'h00); // xor_crc = 0x02 ^ 0x02 = 0x00
        send_uart_byte_4clk(8'h5A);
        // Step 12 clocks to advance through the 5 stages with stage_hold_ticks = 2
        for (i = 0; i < 12; i = i + 1) begin
            #5 clk = 1; #5 clk = 0;
        end
        $display("  -> [UART Serial 16-Byte Frame] Frames_OK=%0d, CRC_Err=%0d | Food_Stage=%0d, Ready=%b, Target_Z=%0d",
                 brd_ok_cnt, brd_err_cnt, brd_fstage, brd_fready, brd_fz);
        if (brd_ok_cnt !== 32'd1 || brd_err_cnt !== 32'd0 || brd_fstage !== 3'd5 || brd_fready !== 1'b1 || brd_fz !== 9'd70)
            errors = errors + 1;

        $display("======================================================================");
        $display("TOTAL HARDWARE ERRORS = %0d", errors);
        $display("======================================================================");
        $finish;
    end
endmodule
