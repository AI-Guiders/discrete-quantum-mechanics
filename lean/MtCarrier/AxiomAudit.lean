import MtCarrier.UnifiedOperators

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
#print axioms MtCarrier.catalan_lock_iff_d3
#print axioms MtCarrier.catalan_law_of_d3
#print axioms MtCarrier.canonical_d3_constants
#print axioms MtCarrier.gaussian_coulomb_lock_iff_d3
#print axioms MtCarrier.mHat_d3_gaussian_factorization
#print axioms MtCarrier.heisenberg_divisibility_d3
#print axioms MtCarrier.heisenberg_divisibility_lock_unique_d3_up_to_8
#print axioms MtCarrier.a15_iv263_unique_9bit_catalan_seed_decomposition
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
#print axioms MtCarrier.instrument_convolution_plaquette_flux_exact
#print axioms MtCarrier.instrument_convolution_gauss_monopole_free_exact
#print axioms MtCarrier.instrument_convolution_faraday_law_exact

-- 4. TrajectoryIV263.lean (Rule Z4, Uniqueness of Polar Verlet Step, A3/A4/A5/A7/A13/A16 Theorems & IV(3)=263 3D Census)
#print axioms MtCarrier.int_eq_of_sq_eq_of_pos
#print axioms MtCarrier.polar_step_uniqueness_from_a3_a4_a5
#print axioms MtCarrier.verlet_coefficients_uniqueness_from_a13
#print axioms MtCarrier.a5_vacuum_floor_from_ring_visibility_and_iv263
#print axioms MtCarrier.a13_verlet_from_clock_shift_and_unit_symplectic_det
#print axioms MtCarrier.a3_a4_from_single_9bit_catalan_word_action
#print axioms MtCarrier.polar_step_reverse_exact
#print axioms MtCarrier.polar_relative_phase_invariant
#print axioms MtCarrier.a7_quarter_disk_step_invariant
#print axioms MtCarrier.pauli_predicate_time_invariant
#print axioms MtCarrier.stationary_rec_eq_parabola
#print axioms MtCarrier.stationary_parabola_first_return_1023_state_period_1024
#print axioms MtCarrier.a6_a8_gate_pauli_ceiling_256_and_heisenberg_deadband_41
#print axioms MtCarrier.a14_u1_global_phase_shift_invariance
#print axioms MtCarrier.iv263_interior_octant_silence_t0
#print axioms MtCarrier.iv263_flat_domain_wall_asymmetry_t0
#print axioms MtCarrier.iv263_central_k3_plaquette_birth_t0_t1_t2
#print axioms MtCarrier.iv263_full_3d_lattice_t0_t1_t2_census
#print axioms MtCarrier.t2_vortex_loop_census_and_eta_b_rational
#print axioms MtCarrier.ablation_heisenberg_threshold_15_breaks_octant_silence
#print axioms MtCarrier.ablation_tdiv_destroys_domain_wall_chiral_asymmetry
#print axioms MtCarrier.ablation_no_denom_guard_corrupts_t2_vortex_pair
#print axioms MtCarrier.gravity_denominator_strictly_positive_floor_8192
#print axioms MtCarrier.closed_form_unified_4channel_measurement_iv263_t2

-- 5. UnifiedOperators.lean (Laplacian Δ_{O₂}, Strain-Tensor d=3 Lock, Bohm Deficit, Pauli Algebra, Landau Operators, α_fs ∈ ℤ[√2] & SM/Cosmology)
#print axioms MtCarrier.cuboctahedron_second_moment_isotropy_tensor
#print axioms MtCarrier.laplacian_O2_exact_on_quadratic_polynomial
#print axioms MtCarrier.gravitational_strain_tensor_lock_iff_d3
#print axioms MtCarrier.projC_even_projS_odd_all_512
#print axioms MtCarrier.even_holonomy_bohm_deficit_eq_abs_connection
#print axioms MtCarrier.odd_holonomy_current_pairwise_conservation_all_512
#print axioms MtCarrier.pauli_clifford_algebra_on_polar_cell
#print axioms MtCarrier.internal_phase_fibration_bijection_512
#print axioms MtCarrier.energy_operator_spectrum_0_to_6_squares
#print axioms MtCarrier.alpha_fs_exact_z_sqrt2_canonical_form_and_floor_137
#print axioms MtCarrier.sm_and_cosmology_closed_rational_operators
#print axioms MtCarrier.coherent_cuboctahedron_barrier_collapse_587x
#print axioms MtCarrier.zero_dark_residual_identity
#print axioms MtCarrier.no_dark_matter_and_vacuum_holonomy_halo
#print axioms MtCarrier.chemical_bond_holonomy_conservation_and_saddle_128
#print axioms MtCarrier.hess_law_and_catalytic_cycle_zero_enthalpy
#print axioms MtCarrier.woodward_hoffmann_and_valence_123_stability_from_d3
#print axioms MtCarrier.catalytic_reaction_gate_opening_on_cuboctahedron
#print axioms MtCarrier.quantum_entanglement_c0_causal_holonomy_and_tsirelson_bound
#print axioms MtCarrier.multi_component_environment_homomorphism_and_markov_blanket
#print axioms MtCarrier.universal_environment_coupling_across_quantum_chemistry_cosmology
#print axioms MtCarrier.closed_form_organism_genesis_in_environment_operator
#print axioms MtCarrier.predictive_mutagenesis_and_epigenetic_saturation_operator
#print axioms MtCarrier.inverse_phenotype_to_genome_compiler_operator

end MtCarrier.Audit
