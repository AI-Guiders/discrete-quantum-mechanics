import MtCarrier.TrajectoryIV263

/-!
# Axiom Audit (`#print axioms`) for Every Theorem in `MtCarrier`

Per our epistemic contract:
1. State types are raw `Int` / `Nat` (`PolarCell` has `mu0 phi0 mu1 phi1 : Int`, NEVER `Fin 65`),
   so no invariant is smuggled into a subtype definition.
2. Every theorem in `MtCarrier` is audited below via `#print axioms` to guarantee
   zero `sorryAx` and zero custom axioms.
-/

namespace MtCarrier.Audit

-- 1. Spec.lean (Rule Z1 & Theorem 11.12)
#print axioms MtCarrier.canonical_d3_constants
#print axioms MtCarrier.catalan_lock_iff_d3
#print axioms MtCarrier.gaussian_coulomb_lock_iff_d3
#print axioms MtCarrier.mHat_d3_gaussian_factorization
#print axioms MtCarrier.heisenberg_divisibility_d3
#print axioms MtCarrier.star_boolean_density_lock_iff_d3
#print axioms MtCarrier.star_boolean_cube_equals_kp_sq_at_d3
#print axioms MtCarrier.cubic_orbits_partition_26
#print axioms MtCarrier.cuboctahedron_unique_isotropic_shell_d3
#print axioms MtCarrier.fcc_cuboctahedron_centrosymmetric_and_planar_incidence

-- 2. FaceAlgebra.lean (Rule Z2 & Theorem 11.11)
#print axioms MtCarrier.wrap512_spec
#print axioms MtCarrier.step0_face_projection_table
#print axioms MtCarrier.l1_face_identity_all_512
#print axioms MtCarrier.l1_face_identity_int
#print axioms MtCarrier.pythagorean_rotator_identity_all_512
#print axioms MtCarrier.heisenberg_pythagorean_triple
#print axioms MtCarrier.projC_even_projS_odd_interior

-- 3. HolonomyMaxwell.lean (Rule Z3, Theorem 11.8 & Corollary 11.9)
#print axioms MtCarrier.quotient_remainder_512_spec
#print axioms MtCarrier.quotient_remainder_three_regimes
#print axioms MtCarrier.d1_d0_zero
#print axioms MtCarrier.plaquette_flux_eq_512_mul_winding
#print axioms MtCarrier.plaquette_winding_zero_of_principal
#print axioms MtCarrier.shared_edge_charge_conservation
#print axioms MtCarrier.discrete_gauss_cube_divergence_zero

-- 4. TrajectoryIV263.lean (Rule Z4, Uniqueness of Polar Verlet Step, A7/A16 Theorems & IV(3)=263 3D Census)
#print axioms MtCarrier.int_eq_of_sq_eq_of_pos
#print axioms MtCarrier.polar_step_uniqueness_from_a3_a4_a5
#print axioms MtCarrier.verlet_coefficients_uniqueness_from_a13
#print axioms MtCarrier.polar_step_reverse_exact
#print axioms MtCarrier.polar_relative_phase_invariant
#print axioms MtCarrier.a7_quarter_disk_step_invariant
#print axioms MtCarrier.pauli_predicate_time_invariant
#print axioms MtCarrier.stationary_rec_eq_parabola
#print axioms MtCarrier.stationary_parabola_first_return_1023_state_period_1024
#print axioms MtCarrier.iv263_interior_octant_silence_t0
#print axioms MtCarrier.iv263_flat_domain_wall_asymmetry_t0
#print axioms MtCarrier.iv263_central_k3_plaquette_birth_t0_t1_t2
#print axioms MtCarrier.iv263_full_3d_lattice_t0_t1_t2_census
#print axioms MtCarrier.t2_vortex_loop_census_and_eta_b_rational
#print axioms MtCarrier.ablation_heisenberg_threshold_15_breaks_octant_silence
#print axioms MtCarrier.ablation_tdiv_destroys_domain_wall_chiral_asymmetry
#print axioms MtCarrier.ablation_no_denom_guard_corrupts_t2_vortex_pair

end MtCarrier.Audit
