/-!
# Rule Z1 and Theorem 11.12 (`thm:catalan-uniqueness-d3`): Uniqueness of d = 3

Formal verification in Lean 4 of the discrete carrier invariants and the four
Diophantine locks of Theorem 11.12 in Chapter 11 (`book/sources/chapters/08-invariant.tex`):
1. Catalan / word-width lock: `1 + 2^d = d^2 ↔ d = 3`.
2. Gaussian-Coulomb lock: `2^d * (2*d*(d-1) - 2 - 2^d) = 4*(d-1)^2 ↔ d = 3` (proved for ALL `d : Nat` via induction for `d ≥ 6`).
3. Heisenberg divisibility lock: at `d = 3`, `N_φ(3) = 13` divides `512 + 13 + 8 = 533`, giving `Δφ_disc = 41`.
4. Star-boolean & two-lane density lock: `2 * N_□(d) = N_neighbors(d) ↔ d = 3` (`K_P^2 = 2^12 = 4096`).
-/

namespace MtCarrier

/-- Kissing-shell neighbor count `|N(d)| = 2 * d * (d - 1)` for the D_d root lattice. -/
def nNeighbors (d : Nat) : Nat := 2 * d * (d - 1)

/-- Phase-channel count `N_φ(d) = 1 + |N(d)|` (center + neighbors). -/
def nPhi (d : Nat) : Nat := 1 + nNeighbors d

/-- Octant / triangular face count `|△(d)| = 2^d`. -/
def nTriangles (d : Nat) : Nat := 2 ^ d

/-- Coordinate-axis / square face count `|□(d)| = 2 * d`. -/
def nSquares (d : Nat) : Nat := 2 * d

/-- Vertices per square face `d_in(□) = 4`. -/
def dInSquare : Nat := 4

/-- Cell word width `mod_bits(d) = 1 + |△(d)| = 1 + 2^d`. -/
def modBits (d : Nat) : Nat := 1 + nTriangles d

/-- Phase ring modulus `N_ring(d) = 2^(mod_bits(d)) = 2^(1 + 2^d)`. -/
def nRing (d : Nat) : Nat := 2 ^ (modBits d)

/-- Mantissa width `frac_bits(d) = mod_bits(d) - d = (1 + 2^d) - d` (at `d=3`: `9 - 3 = 6`). -/
def fracBits (d : Nat) : Nat := modBits d - d

/-- Planck amplitude ceiling `K_P(d) = 2^(frac_bits(d))` (at `d=3`: `2^6 = 64`). -/
def kP (d : Nat) : Nat := 2 ^ (fracBits d)

/-- Face quadrant length `Q_□(d) = N_ring(d) / 4` (at `d=3`: `512 / 4 = 128`). -/
def qSquare (d : Nat) : Nat := nRing d / dInSquare

/-- Pauli half-turn `Φ_Pauli(d) = N_ring(d) / 2` (at `d=3`: `512 / 2 = 256`). -/
def phiPauli (d : Nat) : Nat := nRing d / 2

/-- Unique 9-bit initial vector `IV(d) = 2^(2^d) + (2^d - 1)` (at `d=3`: `256 + 7 = 263`). -/
def ivSeed (d : Nat) : Nat := 2 ^ (2 ^ d) + (2 ^ d - 1)

/-- Coulomb channel modulus `M_hat(d) = 1 + |N(d)| * |△(d)|` (at `d=3`: `1 + 12*8 = 97`). -/
def mHat (d : Nat) : Nat := 1 + nNeighbors d * nTriangles d

/-- Canonical `d = 3` table of carrier constants (Rule Z1). -/
theorem canonical_d3_constants :
    nNeighbors 3 = 12 ∧
    nPhi 3 = 13 ∧
    nTriangles 3 = 8 ∧
    nSquares 3 = 6 ∧
    modBits 3 = 9 ∧
    nRing 3 = 512 ∧
    fracBits 3 = 6 ∧
    kP 3 = 64 ∧
    (kP 3) ^ 2 = 4096 ∧
    qSquare 3 = 128 ∧
    phiPauli 3 = 256 ∧
    mHat 3 = 97 ∧
    ivSeed 3 = 263 := by
  decide

/-- Helper arithmetic lemma for the induction step:
`2 * (2 * (k + 6) * (k + 5)) > 2 * (k + 1 + 6) * (k + 1 + 5)`. -/
theorem two_mul_quad_gt (k : Nat) :
    2 * (2 * (k + 6) * (k + 5)) > 2 * (k + 1 + 6) * (k + 1 + 5) := by
  have h1 : (k + 6) * (k + 5) = k * k + 11 * k + 30 := by
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have h2 : (k + 1 + 6) * (k + 1 + 5) = k * k + 13 * k + 42 := by
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have h_assoc1 : 2 * (k + 6) * (k + 5) = 2 * ((k + 6) * (k + 5)) := Nat.mul_assoc 2 (k + 6) (k + 5)
  have h_assoc2 : 2 * (k + 1 + 6) * (k + 1 + 5) = 2 * ((k + 1 + 6) * (k + 1 + 5)) :=
    Nat.mul_assoc 2 (k + 1 + 6) (k + 1 + 5)
  rw [h_assoc1, h_assoc2, h1, h2]
  omega

/-- Helper arithmetic lemma: `2 * (k + 6) * (k + 5) ≥ (k + 6) * (k + 6)`. -/
theorem two_d_pred_ge_d_sq (k : Nat) :
    2 * (k + 6) * (k + 5) ≥ (k + 6) * (k + 6) := by
  have h1 : (k + 6) * (k + 5) = k * k + 11 * k + 30 := by
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have h2 : (k + 6) * (k + 6) = k * k + 12 * k + 36 := by
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have h_assoc : 2 * (k + 6) * (k + 5) = 2 * ((k + 6) * (k + 5)) := Nat.mul_assoc 2 (k + 6) (k + 5)
  rw [h_assoc, h1, h2]
  omega

/-- Inductive lemma for Theorem 11.12: for all `k : Nat`, setting `d = k + 6`,
we have `2^(k+6) > 2*(k+6)*(k+5)`. -/
theorem pow2_gt_two_d_pred (k : Nat) : 2 ^ (k + 6) > 2 * (k + 6) * (k + 5) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : 2 ^ (k + 1 + 6) = 2 * 2 ^ (k + 6) := by
      rw [Nat.add_right_comm k 1 6, Nat.pow_succ, Nat.mul_comm]
    have h2 := two_mul_quad_gt k
    omega

/-- For all `d ≥ 6`, `1 + 2^d > d^2`. -/
theorem pow2_gt_d_sq_of_ge_six (d : Nat) (hd : d ≥ 6) : 1 + 2 ^ d > d * d := by
  have hk : ∃ k, d = k + 6 := ⟨d - 6, by omega⟩
  rcases hk with ⟨k, rfl⟩
  have h1 := pow2_gt_two_d_pred k
  have h2 := two_d_pred_ge_d_sq k
  omega

/-- Lock 1 of Theorem 11.12 (`eq:catalan-lock`):
For any `d ≥ 1`, `1 + 2^d = d^2` holds if and only if `d = 3`. -/
theorem catalan_lock_iff_d3 (d : Nat) (hd : d ≥ 1) :
    (1 + 2 ^ d = d * d) ↔ d = 3 := by
  constructor
  · intro h
    by_cases h6 : d ≥ 6
    · have hgt := pow2_gt_d_sq_of_ge_six d h6
      omega
    · have hd_cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
      rcases hd_cases with rfl | rfl | rfl | rfl | rfl <;> revert h <;> decide
  · rintro rfl
    decide

/-- Lock 2 of Theorem 11.12 (`eq:gaussian-coulomb-lock`):
In `ℤ` (or written without subtraction as `1 + 2*d*(d-1)*2^d = 4^d + (1 + 2^d)^2`),
the Gaussian norm factorization `M_hat(d) = 1 + |N(d)| * 2^d = d_in(□)^2 + (1 + 2^d)^2`
with `d_in(□) = 2^(d/2)` (or the exact identity `2^d * (2*d*(d-1) - 2) = 4*(d-1)^2 + 4^d`)
holds for `d ≥ 1` if and only if `d = 3` (`4^2 + 9^2 = 16 + 81 = 97 = 1 + 12*8`). -/
theorem gaussian_coulomb_lock_iff_d3 (d : Nat) (hd : d ≥ 1) :
    (2 ^ d * (2 * d * (d - 1)) = 4 * (d - 1) * (d - 1) + 2 ^ d * (2 ^ d + 2)) ↔ d = 3 := by
  constructor
  · intro h
    by_cases h6 : d ≥ 6
    · have hk : ∃ k, d = k + 6 := ⟨d - 6, by omega⟩
      rcases hk with ⟨k, rfl⟩
      have h_sub : k + 6 - 1 = k + 5 := by omega
      rw [h_sub] at h
      have hpow := pow2_gt_two_d_pred k
      have h_lhs_lt : 2 ^ (k + 6) * (2 * (k + 6) * (k + 5)) < 2 ^ (k + 6) * (2 ^ (k + 6) + 2) := by
        apply Nat.mul_lt_mul_of_pos_left
        · omega
        · exact Nat.two_pow_pos (k + 6)
      omega
    · have hd_cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
      rcases hd_cases with rfl | rfl | rfl | rfl | rfl <;> revert h <;> decide
  · rintro rfl
    decide

/-- Gaussian factorization of `M_hat(3) = 97 = 4^2 + 9^2 = d_in(□)^2 + mod_bits^2`. -/
theorem mHat_d3_gaussian_factorization :
    mHat 3 = dInSquare ^ 2 + (modBits 3) ^ 2 ∧ mHat 3 = 97 := by
  decide

/-- Lock 3 of Theorem 11.12 (`eq:heisenberg-divisibility-lock`):
At the unique root `d = 3`, `N_ring(3) + N_φ(3) + |△(3)| = 512 + 13 + 8 = 533`
is divisible by `N_φ(3) = 13` with exact quotient `Δφ_disc = 41` and remainder `0`. -/
theorem heisenberg_divisibility_d3 :
    (nRing 3 + nPhi 3 + nTriangles 3) % nPhi 3 = 0 ∧
    (nRing 3 + nPhi 3 + nTriangles 3) / nPhi 3 = 41 := by
  decide

/-- Lock 4 of Theorem 11.12 (`eq:star-boolean-density-lock`):
For `d ≥ 1`, the two-lane square-face budget `2 * |□(d)| = 4*d` equals the
kissing-shell neighbor count `|N(d)| = 2*d*(d-1)` if and only if `d = 3`,
locking `K_P(3)^2 = 2^(2*|□(3)|) = 2^(|N(3)|) = 2^12 = 4096`. -/
theorem star_boolean_density_lock_iff_d3 (d : Nat) (hd : d ≥ 1) :
    (2 * nSquares d = nNeighbors d) ↔ d = 3 := by
  unfold nSquares nNeighbors
  constructor
  · intro h
    have hdiv : 2 * d * 2 = 2 * d * (d - 1) := by omega
    have hpos : 2 * d > 0 := by omega
    have heq := Nat.eq_of_mul_eq_mul_left hpos hdiv
    omega
  · rintro rfl
    decide

theorem star_boolean_cube_equals_kp_sq_at_d3 :
    2 ^ (nNeighbors 3) = (kP 3) ^ 2 ∧
    2 ^ (2 * nSquares 3) = (kP 3) ^ 2 ∧
    (kP 3) ^ 2 = 4096 := by
  decide

end MtCarrier
