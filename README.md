# Discrete Quantum Mechanics (DQM / ДКМ): Unified Natural Science & Formal Lean 4 Verification

**From One Self-Closure Equation ($1 + 2^d = d^2 \implies d = 3$, Cuboctahedron $O_2(3)$, Phase Ring $\mathbb{Z}_{512}$) to Pure Mathematics (`mathematics/`) and Unified Natural Science (`theory/`, `laboratory/`, `engineering/`)**

**Author:** Dmitrii A. Karataev (Д. А. Каратаев)  
**Formal Verification Partner:** Luch (Луч, AI-Guiders)  
**License:** Strong Reciprocal Copyleft — CC-BY-SA-4.0 (books, papers, documentation) / GPL-3.0-or-later (Lean 4, Python, Verilog, C# code)  
**Documentation Portal (Bilingual Wiki / MkDocs):** **[English Portal](https://ai-guiders.github.io/discrete-quantum-mechanics/)** · **[Русский портал (инженерам, корабелам, математикам, физикам)](https://ai-guiders.github.io/discrete-quantum-mechanics/ru/)**

---

## Open Science Invitation, Community Verification & Honest Disclaimer

**Science does not belong to isolated individuals, corporations, or nations — it belongs to humanity and to all thinking actors on this planet.**

1. **The Core Model and Code Are Open and Working:**
   The discrete cellular automaton ($O_2(3) \times \mathbb{Z}_{512}$, 72-bit reversible `VerletCell72`), the projective rational calculus ($\mathbb{Z}_{2^m} \to \mathbb{P}^1(\mathbb{Q})$), and the deductive theorem chain are openly available and machine-checked in **Lean 4** (`68/68` targets under `AxiomGuard.lean`, `0 sorryAx`, `0 Classical.choice`), with reference implementations in **Python** (`mt_ca/`), **.NET 11** (`AI-Guiders/guiders-physics`), **Wolfram Language** (`AI-Guiders/guiders-mathematics/wolfram/`), and **Mathics3** (`AI-Guiders/mathics-core`).
2. **Honest Disclaimer on Prose Texts, Proofs & Multi-Solver Verification:**
   Even for a human working full-time alongside frontier AI agents, the scope of this work is too large to polish alone. The prose monographs, papers, translations, and exposition **may contain typos, inaccuracies, or roughness that require correction**. Independent verification of the theorems — not only in Lean 4, but also across independent proof assistants (Coq/Rocq, Isabelle/HOL, Agda), SMT solvers, and computer algebra systems — as well as thorough human peer review and proofreading of every chapter, are essential.
3. **Honest Disclaimer on Hardware, Schematics & Laboratory Protocols (`hardware/`, Books II–III):**
   The digital RTL (`cuboctahedron_carrier_asic.v`), analog SPICE models (`cuboctahedron_12beam_spice.cir`), PCB Gerbers, BOM checklists, and cleanroom protocols have been verified in digital and circuit simulation (**Icarus Verilog**, **LTspice**), **but real-world hardware and experimental benches are unforgiving: schematics, tolerances, and protocols may contain errors, may not work out-of-the-box on the first build, and will likely require bench debugging, supplementation, and independent replication by hardware engineers and experimentalists**.
4. **Open Like Wikipedia — Join Us:**
   All repositories are open under free reciprocal licenses (`CC-BY-SA-4.0` / `GPL-3.0-or-later`). We invite mathematicians, physicists, chemists, biologists, hardware engineers, CAS developers (Wolfram, Mathics3, SymPy, Lean), and AI researchers worldwide to join, audit, break, fix, open Issues and Pull Requests, and build this together.

### Verification Status Legend & Current Audit Matrix

To prevent conflating internal model theorems with independent external peer review or physical bench replication, every domain in this repository is explicitly tagged with four verification markers:
- **✅ Lean 4 Kernel-Verified (Constructive Contour 1):** Proved in `lean/` with `0 sorryAx`, `0 Classical.choice`, and `0 smuggled Prop premises` enforced automatically at compile time by [`AxiomGuard.lean`](lean/Constructive/AxiomGuard.lean).
- **🧪 Digital / Circuit / Numerical Simulation:** Verified in Python (`verify_principles.py`), `.NET 11` (`xUnit`), Icarus Verilog (`iverilog`), or LTspice (`cuboctahedron_12beam_spice.cir`).
- **⬜ Pending External Experimental / Bench Confirmation:** Physical/engineering predictions (cleanroom silicon photovoltaics `M1`–`M4`, 12-beam barrier collapse, cyclic metal fatigue limit $\sigma_{-1} \leftrightarrow \Delta\varphi_{\mathrm{disc}}=41$) that have not yet been independently tested on physical laboratory benches.
- **★ Independent Outside Confirmation:** Reserved exclusively for theorems or experimental protocols that have received documented independent review or laboratory replication by external researchers.

| Domain / Module | Lean 4 Kernel (`AxiomGuard`) | Simulation (`Python / Verilog / SPICE`) | External Review / Lab Bench |
| :--- | :---: | :---: | :---: |
| **1. Carrier Geometry ($1+2^d=d^2 \implies d=3$, $O_2(3)$, $\mathbb{Z}_{512}$)** (`MtCarrier/Spec.lean`, `FaceAlgebra.lean`) | ✅ | 🧪 | ⬜ |
| **2. Projective Manifold Calculus, Padé–$\mathrm{SL}_2(\mathbb{Z})$ Towers, Planetary Differentials & Multi-Screw Cascades** (`Constructive/*.lean`, Book V) | ✅ | 🧪 | ⬜ |
| **3. Discrete Holonomy, Maxwell Electrodynamics, Fine-Structure $\alpha_{\mathrm{fs}}^{-1}$ & Particle/Nuclear Shells** (`HolonomyMaxwell.lean`, `ContinuumPhysics.lean`, `NuclearShells.lean`) | ✅ | 🧪 | ⬜ |
| **4. 4-Regime Spring Elasticity, Infinite Fatigue Endurance Limit ($\Delta\varphi_{\mathrm{disc}}=41$), Burgers Dislocation ($256$) & Coupled Elastic Pendulum** (`MtCarrier/MechanicsElasticity.lean`) | ✅ | 🧪 | ⬜ |
| **5. 4-Layer Phonon-Free Singlet-Fission Silicon Heterojunction (`M1`–`M4`) & 3-Stage + $833:1$ Radiation Shielding** (`HardwarePhotovoltaics.lean`, Books II–III) | ✅ | 🧪 | ⬜ |
| **6. Reversible 72-Bit Silicon Stack (`Ring9 / Bus36 / VerletCell72`) & 12-Beam $O_2(3)$ LC Lattice** (`hardware/*.v`, `hardware/*.cir`, `physics/`) | ✅ | 🧪 | ⬜ |

---

## 1. The Five Core Books: Unified Natural Science (Books I–IV) & Projective Manifold Mathematics (Book V) (`book/out/pdf/`)

In Discrete Quantum Mechanics (DQM) on the two-sorted algebraic carrier structure $\langle\mathcal{M},\mathcal{T}\rangle$ (in the model-theoretic sense of A. I. Mal'cev), physics, chemistry, molecular biology, cosmology, and the physical realization of computation unify into a **single Natural Science (*Естествознание*, Books I–IV)**, while the pure constructive mathematics of the projective manifold $\mathbb{P}^1$ over $\mathbb{Z}_{4Q}$ and $\mathbb{Q}(i, \sqrt{d-1})$ is separated into a dedicated **Mathematical Monograph (Book V)**:

| Book | Role & Scope | Compiled PDF (`book/out/pdf/`) | LaTeX Source (`book/sources/`) |
| :--- | :--- | :--- | :--- |
| **Book I — Theory** | **Formal Foundations of DQM:** $1 + 2^d = d^2 \implies d = 3$, cuboctahedral rotator calculus on $\mathbb{Z}_{512}$, Post completeness, de Rham cohomology, Born's rule, Maxwell electrodynamics, $\alpha_{\mathrm{fs}}^{-1}(3) = 137.035999187\dots$, atomic/nuclear shells of $O_2(3)$, molecular biophysics, 3-stage passive & $833:1$ active radiation shielding, and the model-theoretic limit $\lim M_n = \mathcal{M}$. | [`formal-foundations-monograph.pdf`](book/out/pdf/formal-foundations-monograph.pdf) | [`vol-formal-foundations-monograph.tex`](book/sources/volumes/vol-formal-foundations-monograph.tex) |
| **Book II — Laboratory** | **Laboratory Manual & Cleanroom Protocols:** 4-layer phonon-free singlet-fission silicon heterojunction ($Z(\mathrm{C_{18}H_{12}})+Z(\mathrm{O}) = 120+8 = 128 = Q_\square(3)$, Pauli passivation barrier $45^2 < 2048 < 46^2$), Pauli gate A/B falsification ($Z=45$ vs. $Z=46$), signatures `M1`–`M4`, pre-emptive troubleshooting matrix `F1`–`F6`, and critical experiment registry (`CE-M`, `CE-F`, `CE-A`, `CE-RD`). | [`dqm-laboratory-manual.pdf`](book/out/pdf/dqm-laboratory-manual.pdf) | [`vol-laboratory-manual.tex`](book/sources/volumes/vol-laboratory-manual.tex) |
| **Book III — Engineering** | **Engineering Handbook:** Phase-relay electrical engineering on FCC cuboctahedra ($V = \mathcal{C}_3(\Delta\varphi),\ I = \mathcal{S}_3(\Delta\varphi)$), DC MPPT ($P \le 64^2 = 4096$), $0\%$-ripple capacitor-free quadrature rectifiers ($|\mathcal{C}_3|+|\mathcal{S}_3|\equiv 128$), Landauer-free reversible computing ($|\Delta\varphi|\le 40 < 41$), branchless silicon stack (`Ring9 / Bus36 / VerletCell72`), 12-coil $O_2(3)$ reactors, and 3-stage graded + $833:1$ active radiation shielding. | [`dqm-engineering-handbook.pdf`](book/out/pdf/dqm-engineering-handbook.pdf) | [`vol-engineering-handbook.tex`](book/sources/volumes/vol-engineering-handbook.tex) |
| **Book IV — Popular Science Guide (*Powered by Dr. STONE*)** | **The Complete Popular Course of Unified Natural Science (*Powered by Dr. STONE — 10,000,000,000%*):** Conversational 7-stage roadmap crafting the entire scientific tree from $1 + 2^3 = 3^2$ to living cells and silicon hardware. | [`natural-sciences-course.pdf`](book/out/pdf/natural-sciences-course.pdf) | [`vol-natural-sciences-course.tex`](book/sources/volumes/vol-natural-sciences-course.tex) |
| **Book V — Mathematics** | **Mathematics of the Projective Manifold:** Pure constructive mathematics over $\mathbb{Z}_{4Q}$ and $\mathbb{Q}(i, \sqrt{d-1})$ (`lean/Constructive/`, `0 sorryAx`, `0 Classical.choice`, `0 Prop premises` under `AxiomGuard.lean`): pole-free quotient derivative towers $D^n(f/g)=N_n/G_n$, $\mathrm{SL}_2(\mathbb{Z})$ isotropic cones and Padé approximant towers, root-free cubic Padé compression, three-shaft planetary differentials $\mathcal{A}+\mathcal{B}=\mathcal{C}$ with Mason–Stothers Wronskians, multi-screw cascade monoids with $S_A$ extremal drift envelopes, and 2D counter-wave Gram-matrix cancellation with Model 1 / Model 2 independence theorems. | [`projective-manifold-mathematics.pdf`](book/out/pdf/projective-manifold-mathematics.pdf) | [`vol-projective-manifold-mathematics.tex`](book/sources/volumes/vol-projective-manifold-mathematics.tex) |

---

## 2. "Making Of" — The 8-Volume Discovery Chronicle (`book/out/pdf/making-of/`)

The historical 8-volume expedition chronicle showing how the eight traditional separate disciplines step-by-step collapsed into a single Natural Science (*"How It Was Created / Фильм о фильме"*):

1. [`making-of/construction.pdf`](book/out/pdf/making-of/construction.pdf) — **Vol. I: Construction** (Carrier geometry, evolution law $g$, $M \to T$ projection, $\alpha_{\mathrm{fs}}^{-1}$, SI bridge)
2. [`making-of/floors.pdf`](book/out/pdf/making-of/floors.pdf) — **Vol. II: Floors** (Coordination shells, simplicial clique atlas $\mathcal{C}_{13}$, Standard Model gauge algebra)
3. [`making-of/cosmology.pdf`](book/out/pdf/making-of/cosmology.pdf) — **Vol. III: Cosmology** (9-bit seed $\mathrm{IV} = 263$, baryon asymmetry, $16/3$ vacuum holonomy halo without dark matter)
4. [`making-of/chemistry.pdf`](book/out/pdf/making-of/chemistry.pdf) — **Vol. IV: Chemistry** (Periodic table from $S_k = 10k^2 + 2$, covalent/hydrogen bonds, water & Watson–Crick lock)
5. [`making-of/biology.pdf`](book/out/pdf/making-of/biology.pdf) — **Vol. V: Biology** (Genetic code $64 \to 20+1$, $O(L)$ co-translational protein folding, 3D morphogenesis)
6. [`making-of/observer.pdf`](book/out/pdf/making-of/observer.pdf) — **Vol. VI: Observer** (Coherent macro-node $(M, R_{\mathrm{eff}})$, internal observer epistemology, Born's rule)
7. [`making-of/compute.pdf`](book/out/pdf/making-of/compute.pdf) — **Vol. VII: Compute** (72-bit cell register, reversible leapfrog Verlet architecture, GPU/FPGA/ASIC mapping)
8. [`making-of/applied.pdf`](book/out/pdf/making-of/applied.pdf) — **Vol. VIII: Applied R&D** (12-beam barrier collapse $587\times$, phase ratchet, 4-channel Neumann tomography)

---

## 3. Modular Workspace Architecture: Four Specialized Submodules (`.gitmodules`)

To allow mathematicians, Lean 4 formalists, CAS developers, and `.NET` / GPU systems engineers to clone and develop each engine independently, this workspace connects four specialized Git submodules alongside the core books (`book/`), hardware blueprints (`hardware/`), and Python reference lab (`mt_ca/`):

| Submodule Path | Upstream Repository | Role & Architecture |
| :--- | :--- | :--- |
| **[`lean/`](lean)** | [`AI-Guiders/dqm-lean`](https://github.com/AI-Guiders/dqm-lean) | **Two-Contour Lean 4 Formalization (with Global `AxiomGuard.lean` Compile-Time Linter):**<br>• **Contour 1 (`Constructive/` & `MtCarrier/`):** Pure constructive mathematics and DQM core (`56/56` build jobs, `0 external dependencies`, `0 sorryAx`, `0 Classical.choice`, `0 smuggled Prop premises` enforced automatically at compile time by `AxiomGuard.constructiveKernelLinter` with zero name-prefix exemptions).<br>• **Contour 2 (`MathlibBridge/`):** Separate Lake package with standard `mathlib4` dependency for bridging constructive theorems to classical `Mathlib` definitions. |
| **[`papers/`](papers)** | [`AI-Guiders/scientific-papers`](https://github.com/AI-Guiders/scientific-papers) | Standalone bilingual preprints (`mathematics/`, `theory/`, `laboratory/`, `engineering/`) and paper-by-paper Lean 4 modules (`RotatorQuadrature.lean`, `LogicCohomology.lean`, `PillaiDiophantine.lean`, `AbcPlanetaryWronskian.lean`, `ModelTheoreticLimit.lean`, `CollatzPlanetarySplice.lean`, `RiemannHolonomy.lean`). |
| **[`mathematics/`](mathematics)** | [`AI-Guiders/guiders-mathematics`](https://github.com/AI-Guiders/guiders-mathematics) | Exact Projective Computer Algebra System over $\mathbb{Q}(i, \sqrt{d-1})$ and $\mathbb{P}^1(\mathbb{C})$ (`guiders_math/`) + pure Wolfram Language suite (`wolfram/Core/ProjectiveCalculus.wl`, `CarrierAutomaton3D.wl`, and `wolfram/Lab/`). |
| **[`physics/`](physics)** | [`AI-Guiders/guiders-physics`](https://github.com/AI-Guiders/guiders-physics) | Native `.NET 11` + `AVX2/AVX-512` + `CUDA PTX` cellular automaton kernel (`Guiders.Physics.Core`: `Ring9`, `Bus36`, `VerletCell72`, `CuboctahedronCarrier`, `CuboctahedronAutomatonKernel`), lossless archiver, 4D media codec, and 3D world engine. |

---

## 4. Standalone Scientific Papers (`papers/` Submodule → `AI-Guiders/scientific-papers`) & Dedicated Lean 4 Modules

Linked via the [`papers/`](papers) Git submodule ([`AI-Guiders/scientific-papers`](https://github.com/AI-Guiders/scientific-papers)), organized into **Pure Mathematics (`papers/mathematics/`)** and **Unified Natural Science (`papers/theory/`, `papers/laboratory/`, `papers/engineering/`)**, each backed by its own standalone Lean 4 module (`0 sorryAx`, `0 Classical.choice`):

### I. Pure Mathematics, Abstract Computer Science & Number-Theory Research Sandbox (`papers/mathematics/`, `exercise / research`)
- **1. Core Rotator Calculus** · [`RotatorQuadrature.lean`](papers/RotatorQuadrature.lean) (`thm1`–`thm3`, `thm34`–`thm35`, `thm38`–`thm39`): [`rotator-quadrature-en.pdf`](papers/mathematics/rotator-quadrature-en.pdf) · [`-ru.pdf`](papers/mathematics/rotator-quadrature-ru.pdf)
- **2. Logic, Cohomology & Complexity Barriers** · [`LogicCohomology.lean`](papers/LogicCohomology.lean) (`thm4`–`thm5`): [`logic-cohomology-barriers-en.pdf`](papers/mathematics/logic-cohomology-barriers-en.pdf) · [`-ru.pdf`](papers/mathematics/logic-cohomology-barriers-ru.pdf)
- **3. Exploratory Research / Exercise — Pillai–Catalan Exponential Equations ($A x^m - B y^n = C$)** · [`PillaiDiophantine.lean`](papers/PillaiDiophantine.lean) (`thm6`, `thm7`, `thm10`–`thm11`, root-free cubic Padé compression & adjacent-floor escape): [`pillai-exponential-diophantine-en.pdf`](papers/mathematics/pillai-exponential-diophantine-en.pdf) · [`-ru.pdf`](papers/mathematics/pillai-exponential-diophantine-ru.pdf)
- **4. Exploratory Research / Exercise — Three-Shaft Planetary Differential & `abc` Triples ($A + B = C$)** · [`AbcPlanetaryWronskian.lean`](papers/AbcPlanetaryWronskian.lean) (`thm8`, `thm9`, `thm12`–`thm16`, Mason–Stothers Wronskian & Lagrange–Vandermonde floor-defect projectors): [`abc-planetary-differential-wronskian-en.pdf`](papers/mathematics/abc-planetary-differential-wronskian-en.pdf) · [`-ru.pdf`](papers/mathematics/abc-planetary-differential-wronskian-ru.pdf)
- **5. Exploratory Research / Exercise — Collatz Two-Screw Planetary Gear Cascade ($\mathbb{Z}_{2^a} \times \mathbb{Z}_{3^b}^\times$)** · [`CollatzPlanetarySplice.lean`](papers/CollatzPlanetarySplice.lean) (`thm18`–`thm29`, `thm31`–`thm33`, `thm37`, extremal drift envelope $3^B - 2^B \le R_w \le 2^{A-B}(3^B - 2^B)$ & 2-adic boundary reflection $n_\infty^{(-)} = -1 \notin \mathbb{N}$): [`collatz-natural-ring-wronskian-en.pdf`](papers/mathematics/collatz-natural-ring-wronskian-en.pdf) · [`-ru.pdf`](papers/mathematics/collatz-natural-ring-wronskian-ru.pdf)
- **6. Exploratory Research / Exercise — Counter-Wave Riemann Holonomy, Three-Way Orthogonality Dichotomy & Model-Theoretic Independence Witness** · [`RiemannHolonomy.lean`](papers/RiemannHolonomy.lean) (`counterwave_cascade_orthogonality_dichotomy_and_independence_models`: exact 2D vector ocean $\mathrm{MainAmount}_{\mathrm{vec}}$ cancellation, three-way dichotomy $\Pi_-(R)=0 \lor \mathbf{C}\cdot\mathbf{A}=0 \lor \delta=0$, and explicit Model 1 `[(1,0,1,0)]` vs. orthogonal Model 2 `[(1,1,-1,1)]` at $\delta=1\ne 0$ proving that $\delta=0$ is independent of the counter-wave functional-equation and $\mathrm{SL}_2(\mathbb{Z})$ cascade axioms alone).

### II. Unified Natural Science (`papers/{theory,laboratory,engineering}/`)
- **`papers/theory/` — 1. Foundations of DQM, Maxwell & $\alpha_{\mathrm{fs}}^{-1}$** · [`UnifiedOperators.lean`](lean/MtCarrier/UnifiedOperators.lean): [`dqm-foundations-maxwell-fine-structure-en.pdf`](papers/theory/dqm-foundations-maxwell-fine-structure-en.pdf) · [`-ru.pdf`](papers/theory/dqm-foundations-maxwell-fine-structure-ru.pdf)
- **`papers/theory/` — 2. Gravity, $16/3$ Halo & $587\times$ Nuclear Collapse** · [`UnifiedOperators.lean`](lean/MtCarrier/UnifiedOperators.lean): [`gravity-halo-nuclear-collapse-en.pdf`](papers/theory/gravity-halo-nuclear-collapse-en.pdf) · [`-ru.pdf`](papers/theory/gravity-halo-nuclear-collapse-ru.pdf)
- **`papers/theory/` — 3. Model-Theoretic Limit $\lim M_n = \mathcal{M}$ & Gödel–Tarski Arbitration** · [`ModelTheoreticLimit.lean`](papers/ModelTheoreticLimit.lean) (`thm17`): [`model-theoretic-limit-godel-arbitration-en.pdf`](papers/theory/model-theoretic-limit-godel-arbitration-en.pdf) · [`-ru.pdf`](papers/theory/model-theoretic-limit-godel-arbitration-ru.pdf)
- **`papers/laboratory/` — 4. Cleanroom Silicon Photovoltaics Protocol (`M1`–`M4`, `F1`–`F6`)**: [`phonon-free-silicon-photovoltaics-en.pdf`](papers/laboratory/phonon-free-silicon-photovoltaics-en.pdf) · [`-ru.pdf`](papers/laboratory/phonon-free-silicon-photovoltaics-ru.pdf)
- **`papers/engineering/` — 5. Phase-Relay Electrical Engineering & Silicon Architecture (`Ring9 / Bus36 / VerletCell72`)** · [`LogicCohomology.lean`](papers/LogicCohomology.lean) (`thm5`): [`dqm-electrical-engineering-and-silicon-hardware-en.pdf`](papers/engineering/dqm-electrical-engineering-and-silicon-hardware-en.pdf) · [`-ru.pdf`](papers/engineering/dqm-electrical-engineering-and-silicon-hardware-ru.pdf)

---

## 4. Environment Setup & Verification Commands

```bash
# 0. On a fresh clone: pull Git LFS assets and set up Python virtual environment
git submodule update --init --recursive
git lfs pull
python3 -m venv .venv
source .venv/bin/activate          # Linux / macOS
# .\.venv\Scripts\Activate.ps1     # Windows PowerShell
pip install -r requirements.txt

# 1. Formal Lean 4 proof verification (38/38 build jobs, 0 sorryAx, 0 Classical.choice):
cd lean
lake build

# 2. Full Python verification suite (list suites, run gate, or run all suites):
cd ..
python3 verify_principles.py --list
python3 verify_principles.py --suite gate
python3 verify_principles.py --ship

# 3. Build the 5 core books (Books I-IV Natural Science + Book V Projective Manifold Mathematics):
pwsh -NoProfile -File book/build.ps1 -Volume monograph
pwsh -NoProfile -File book/build.ps1 -Volume laboratory
pwsh -NoProfile -File book/build.ps1 -Volume engineering
pwsh -NoProfile -File book/build.ps1 -Volume course
pwsh -NoProfile -File book/build.ps1 -Volume mathematics
```
