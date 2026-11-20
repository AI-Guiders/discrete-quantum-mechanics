# Hardware & SPICE Realization of the M/T Cuboctahedral Rotator (`hardware/`)

This directory contains the gate-level digital RTL implementation (**Verilog IEEE 1364-2005**, verified with **Icarus Verilog 12.0**) and the 3D 13-node / 36-branch analog LC/RF circuit simulation (**SPICE**, verified with **Analog Devices LTspice 26.1.1**) of the cuboctahedral rotator and phase bridge.

---

## 1. Digital Gate-Level ASIC / FPGA Core (`cuboctahedron_carrier_asic.v`)

Compiled and verified with **Icarus Verilog** (`C:\iverilog\bin\iverilog.exe` + `vvp.exe`), generating the waveform dump `cuboctahedron_carrier.vcd` (viewable in **GTKWave**):

```powershell
C:\iverilog\bin\iverilog.exe -o cuboctahedron_carrier_asic.vvp cuboctahedron_carrier_asic.v
C:\iverilog\bin\vvp.exe cuboctahedron_carrier_asic.vvp
```

### Verified Hardware Modules & Results (`TOTAL HARDWARE ERRORS = 0`)

1. **`rotator_512_unit` (9-Bit Branchless Rotator, Wronskian, and Weierstrass Lift):**
   - Uses 9-bit two's-complement bitmask `& 511` (`emod 512`) and XOR/abs without lookup tables or floating-point operations.
   - Across all `512` ring ticks: one-step difference Wronskian `W(φ) = C(φ)S(φ+1) - S(φ)C(φ+1) ≡ 128` (`0` errors) and Pythagorean lift `X(φ)² + Y(φ)² ≡ R(φ)²` (`0` errors).
   - Hardware Fresnel diffraction sums over `φ² mod 512`: `C_Fresnel = 2048`, `S_Fresnel = 2048`.

2. **`cuboctahedron_12beam_gate` (12-Beam Cuboctahedron Impedance Collapse & Ballistic Bridge):**
   - Evaluates the 12 cuboctahedron edges at amplitude ceiling `μ_c = μ_nb = 64`:
     - `Δφ = 0` (`0°`, in-phase barrier): `C = +128, S = 0`, impedance denominator `D = 13,631,488`, `Phi_gate = 0`;
     - `Δφ = 41` (`28.8°`, Heisenberg threshold): `C = +87, S = +41`, `D = 9,601,024`, `Phi_gate = 13,218` (`322` quanta);
     - `Δφ = 128` (`90.0°`, lossless ballistic bridge): `C = 0, S = +128`, `D = 1,048,576`, `Phi_gate = 377,856` (`9,216` quanta);
     - `Δφ = 139` (`97.7°`, second-quadrant coherent collapse): `C = -11, S = +117`, impedance collapses to the quantum vacuum floor `D = 8,192 = ε`, boosting gate acceleration to `Phi_gate = 44,209,152` (`1,078,272` quanta);
     - `Δφ = 256` (`180.0°`, Pauli singlet lock): `C = -128, S = 0`, `D = 8,192`, net transport current `Phi_gate = 0`.

3. **`quotient_remainder_512_unit` (Hardware Born-Rule Detector `P(μ) = μ² / 512`):**
   - Uses arithmetic right shift `>>> 9` for exact floor division by `512 = 2^9` (`q = branchQuotient`, `r = edgeConnection`).
   - Across all `512` background detector phases `φ_bg ∈ 0..511`, an incoming wave of amplitude `μ` (`Φ_wave = μ²`) produces `q = 1` corpuscle clicks in exact equality with `μ²`:
     - `μ = 0` (`μ² = 0`): `0 / 512` clicks;
     - `μ = 4` (`μ² = 16`): `16 / 512` clicks;
     - `μ = 8` (`μ² = 64`): `64 / 512` clicks;
     - `μ = 12` (`μ² = 144`): `144 / 512` clicks;
     - `μ = 16` (`μ² = 256`): `256 / 512` clicks.

4. **`verlet_reversible_cell` (Two-Tick Symplectic Reversible Register, Zero Landauer Heat):**
   - Starts at `(phi_curr, phi_prev) = (41, 0)` with constant acceleration `Phi_accel = 13`.
   - Advances `64` clock cycles forward (`reverse_dir = 0`) to `(9, 160)`.
   - Reverses direction (`reverse_dir = 1`) for `64` clock cycles on the same clock without a history stack, recovering `(41, 0)` bit-for-bit.

---

## 2. 3D 13-Node Cuboctahedron Analog LC/RF SPICE Circuit (`cuboctahedron_12beam_spice.cir`)

Simulated with **Analog Devices LTspice 26.1.1** (`4,061` Newton–Raphson Kirchhoff iterations across `13` 3D nodes, `12` radial spokes, and `24` surface edges of the `6` square and `8` triangular faces):

```powershell
Start-Process -FilePath "C:\Program Files\ADI\LTspice\LTspice.exe" -ArgumentList "-b `"$PWD\cuboctahedron_12beam_spice.cir`"" -Wait
Get-Content cuboctahedron_12beam_spice.log
```

### Measured SPICE Results (`cuboctahedron_12beam_spice.log`)

1. **12-Beam Coherent Cuboctahedron Focusing vs. Single-Beam Reference:**
   - Single-beam central peak-to-peak voltage: `V_single_pp = 0.181576 V`
   - Coherent 12-beam central peak-to-peak voltage: `V_coh_pp = 2.178910 V`
   - Measured amplitude gain: `Gain_amp = 12.000000` (`|N(3)| = 12`)
   - Measured power / energy density gain: `Gain_power = 143.999992` (`|N(3)|² = 144`)

2. **Pauli Singlet Vortex Lock (Stationary Particle with Internal Edge Circulation):**
   - With `6` beams at `0°` and `6` beams at `180°`, the central node voltage cancels to machine zero:
     `V_vortex_center_pp = 1.096e-14 V` (`0 V` to 14 decimal places — stationary center!)
   - Simultaneously, a steady circulating vortex current flows around the surface edges of the cuboctahedron:
     `I_vortex_loop_pp = 13.489 mA`.

3. **Euler-Angle Tilt Transfer Across the 8 Triangular Faces (`xy → xz, yz`):**
   - Driving only the `4` vertices of the horizontal `xy` square in quadrature (`0°, 90°, 180°, 270°`, `V_euler_xy_drive_pp = 1.43488 V`) with zero active generators in the `xz` and `yz` planes transfers rotating wave energy through the `24` surface edges of the `8` triangular faces equally into both tilted Euler planes:
     `V_euler_xz_tilt_pp = 0.505653 V`, `V_euler_yz_tilt_pp = 0.505653 V`.
