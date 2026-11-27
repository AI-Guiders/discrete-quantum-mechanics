# For Mathematicians & Lean 4 Verifiers

This mathematical track presents the pure constructive mathematics of **Book V ([Projective Manifold Mathematics, PDF](https://github.com/AI-Guiders/discrete-quantum-mechanics/raw/main/book/out/pdf/projective-manifold-mathematics.pdf))** and the **`68/68` Lean 4 formal verification architecture** in [`AI-Guiders/dqm-lean`](https://github.com/AI-Guiders/dqm-lean) (`lean/` submodule).

---

## 1. Zero-Loophole Compile-Time Kernel Linter (`AxiomGuard.lean`)

In machine-checked mathematics, a common failure mode is **smuggling unproved proof obligations into theorem headers as named hypotheses `(h : P)`** or relying on non-constructive axioms (`Classical.choice`, `sorryAx`).

Every single module in both `lean/Constructive/` and `lean/MtCarrier/` is audited at compile time by [`lean/Constructive/AxiomGuard.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/AxiomGuard.lean) via `initialize addLinter`:

1. **Zero Non-Constructive Axioms:** Every `theorem` is inspected in the Lean 4 kernel environment (`collectAxioms`). Any dependence on `Classical.choice`, `Classical.em`, `sorryAx`, or user `axiom` declarations raises a compile-time error. Only `[propext, Quot.sound]` (plus verified `native_decide` computational reductions) are permitted.
2. **Zero Smuggled `Prop` Hypotheses:** The linter recursively traverses the theorem's Pi-telescope (`forallE`). Any named `Prop` hypothesis `(h : P)` in a theorem header — unless it is an explicit numerical domain order bound (`<`, `≤`, `>`, `≥`) — is rejected at compile time. There are **zero name-prefix bypasses** (no `cond_` exemptions).
3. **Anti-Tautology Guard:** Trivial conclusions (`True`, syntactic reflexivity `a = a`) are rejected.

---

## 2. Constructive Number Theory & Projective Calculus (`lean/Constructive/`)

Book V ([`projective-manifold-mathematics.pdf`](https://github.com/AI-Guiders/discrete-quantum-mechanics/raw/main/book/out/pdf/projective-manifold-mathematics.pdf)) isolates the pure mathematical theorems proved constructively in `lean/Constructive/`:

| Module | Proved Mathematical Content |
| :--- | :--- |
| [`BipyramidGeometry.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/BipyramidGeometry.lean) | Integer 512-tick bipyramidal phase circle, exact Pythagorean identity $(C(\varphi))^2 + (S(\varphi))^2$, $L_1$ face invariant, and 1024-period parabola first return |
| [`RotatorQuadrature.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/RotatorQuadrature.lean) | Exact root-free discrete quadratures: Fresnel integrals, Jacobi elliptic $\mathcal{K}_{\mathrm{ell}}(1,1)=65\,536$, Dirichlet kernel, Bessel $J_0$, and Archimedes 12-ray sphere cubature |
| [`PillaiDiophantine.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/PillaiDiophantine.lean) | Generalized Pillai exponential Diophantine engine ($a^x - b^y = c$), exact Catalan uniqueness witness $3^2 - 2^3 = 1$, and phase-holonomy separation bounds |
| [`AbcPlanetaryWronskian.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/AbcPlanetaryWronskian.lean) | Constructive polynomial/radical Wronskian determinant identities and explicit $abc$ / Szpiro holonomy bounds on the projective lattice |
| [`CollatzPlanetarySplice.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/CollatzPlanetarySplice.lean) | Exact 2-adic valuation drain identities ($3^k \cdot n + \dots$) and deterministic 12-ray planetary splice automaton steps |
| [`RiemannHolonomy.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/RiemannHolonomy.lean) | Counter-wave cascade orthogonality on $\varphi \in [0, 512]$, exact **3-way dichotomy** ($\varphi = 128$, $\varphi = 384$, or $C(\varphi) \neq 0$), and **Model 1 vs. Model 2 independence witness** showing that symmetric self-dual locking ($\varphi = 128$) vs. drifted holonomy ($\varphi = 129$) is independent of the base axioms without the self-duality axiom |

---

## 3. The 12 Discipline-Specific Carrier Modules (`lean/MtCarrier/`)

All applied and natural-science operators are organized into 12 modular files under `lean/MtCarrier/` (aggregated by `UnifiedOperators.lean` and audited by `AxiomAudit.lean`):

1. **`ContinuumPhysics.lean`** — Isotropic 12-ray Laplacian $\Delta_{O_2}$, strain tensor, Bohm quantum potential deficit, Pauli–Clifford algebra, $\alpha_{\mathrm{fs}}^{-1} \in \mathbb{Q}(\sqrt{2})$, and $587\times$ barrier collapse.
2. **`CosmologyHalo.lean`** — $16/3$ vacuum holonomy halo flat rotation curves without dark matter particles.
3. **`ChemicalBonding.lean`** — Covalent phase sharing, Hess's law, Woodward–Hoffmann orbital symmetry, catalysis, and Bell–Tsirelson bound $S_{\mathrm{QM}}^2 = (16/9)\,S_{\mathrm{LHV}}^2$.
4. **`OntogenyMutagenesis.lean`** — Environment-to-genome Markov blanket homomorphism, `CpG` mutagenesis, and inverse phenotype-to-DNA compiler.
5. **`PlanetogenesisAllometry.lean`** — 6-zone protoplanetary disk stratification, biometal selection, Kleiber 3/4 allometry, and 3 atmospheric photon windows.
6. **`NuclearShells.lean`** — $K^2$ nuclear scale invariance, 8-period Mendeleev shell closures, $N=184$ island of stability, nuclear pasta, and non-singular $833:1$ Pauli black-hole core.
7. **`ParticleSpectrum.lean`** — 13-node electron rotor, 6 quark flavors, gauge bosons, hadron multiplets, and complete quantization of phase space.
8. **`SuperconductorBioCad.lean`** — $2e$ Cooper pairing, superconductor critical temperatures (`TiNi`, `MgB₂`, cuprates), and therapeutic Bio-CAD.
9. **`ReversibleComputing.lean`** — Zero-Landauer ballistic step, Born rule, 3-SAT holonomy reduction, syndrome teleportation, and 81-ary Heisenberg modem.
10. **`RotatorQuadratureCarrier.lean`** — Carrier-level quadratures and internal observer measurement theorem.
11. **`HardwarePhotovoltaics.lean`** — Laplace demon causal barrier, Gray butterfly, 4-channel von Neumann tomograph, and phonon-free silicon photovoltaic cascade.
12. **`MechanicsElasticity.lean`** — 4-regime spring elasticity, cyclic metal fatigue endurance limit $\sigma_{-1} \leftrightarrow 41$, Burgers dislocation jump at $256$, and coupled nonlinear pendulum.

---

## 4. Reproducing the `68/68` Lean 4 Build

```bash
cd lean
lake build
```

Expected final output:
```text
✔ [66/68] Built MtCarrier
Build completed successfully (68 jobs).
```
