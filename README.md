# Discrete Quantum Mechanics (DQM / ДКМ): Unified Natural Science & Formal Lean 4 Verification

**From One Self-Closure Equation ($1 + 2^d = d^2 \implies d = 3$, Cuboctahedron $O_2(3)$, Phase Ring $\mathbb{Z}_{512}$) to Pure Mathematics (`mathematics/`) and Unified Natural Science (`theory/`, `laboratory/`, `engineering/`)**

**Author:** Dmitrii A. Karataev (Д. А. Каратаев)  
**Formal Verification Partner:** Luch (Луч, AI-Guiders)  
**License:** Strong Reciprocal Copyleft — CC-BY-SA-4.0 (books, papers, documentation) / GPL-3.0-or-later (Lean 4, Python, Verilog, C# code)

---

## 1. The Four Core Books of Unified Natural Science (`book/out/pdf/`)

In Discrete Quantum Mechanics (DQM) on the two-sorted algebraic carrier structure $\langle\mathcal{M},\mathcal{T}\rangle$ (in the model-theoretic sense of A. I. Mal'cev), physics, chemistry, molecular biology, cosmology, and the physical realization of computation unify into a **single Natural Science (*Естествознание*)** presented in four non-duplicated, cross-referenced books:

| Book | Role & Scope | Compiled PDF (`book/out/pdf/`) | LaTeX Source (`book/sources/`) |
| :--- | :--- | :--- | :--- |
| **Book I — Theory** | **Formal Foundations of DQM:** $1 + 2^d = d^2 \implies d = 3$, cuboctahedral rotator calculus on $\mathbb{Z}_{512}$, Post completeness, de Rham cohomology, Born's rule, Maxwell electrodynamics, $\alpha_{\mathrm{fs}}^{-1}(3) = 137.035999187\dots$, atomic/nuclear shells of $O_2(3)$, molecular biophysics, and the model-theoretic limit $\lim M_n = \mathcal{M}$. | [`formal-foundations-monograph.pdf`](book/out/pdf/formal-foundations-monograph.pdf) | [`vol-formal-foundations-monograph.tex`](book/sources/volumes/vol-formal-foundations-monograph.tex) |
| **Book II — Laboratory** | **Laboratory Manual & Cleanroom Protocols:** 4-layer phonon-free singlet-fission silicon photovoltaic cascade ($441\text{ nm} \to 2\times 882\text{ nm} < 1107\text{ nm}$), Pauli gate A/B falsification ($Z=45$ vs. $Z=46$), signatures `M1`–`M4`, pre-emptive troubleshooting matrix `F1`–`F6`, and critical experiment registry (`CE-M`, `CE-F`, `CE-A`, `CE-RD`). | [`dqm-laboratory-manual.pdf`](book/out/pdf/dqm-laboratory-manual.pdf) | [`vol-laboratory-manual.tex`](book/sources/volumes/vol-laboratory-manual.tex) |
| **Book III — Engineering** | **Engineering Handbook:** Phase-relay electrical engineering on FCC cuboctahedra ($V = \mathcal{C}_3(\Delta\varphi),\ I = \mathcal{S}_3(\Delta\varphi)$), DC MPPT ($P \le 64^2 = 4096$), $0\%$-ripple capacitor-free quadrature rectifiers ($|\mathcal{C}_3|+|\mathcal{S}_3|\equiv 128$), Landauer-free reversible computing ($|\Delta\varphi|\le 40 < 41$), branchless silicon stack (`Ring9 / Bus36 / VerletCell72`), and 12-coil $O_2(3)$ reactors. | [`dqm-engineering-handbook.pdf`](book/out/pdf/dqm-engineering-handbook.pdf) | [`vol-engineering-handbook.tex`](book/sources/volumes/vol-engineering-handbook.tex) |
| **Book IV — Popular Science Guide (*Powered by Dr. STONE*)** | **The Complete Popular Course of Unified Natural Science (*Powered by Dr. STONE — 10,000,000,000%*):** Conversational 7-stage roadmap crafting the entire scientific tree from $1 + 2^3 = 3^2$ to living cells and silicon hardware. | [`natural-sciences-course.pdf`](book/out/pdf/natural-sciences-course.pdf) | [`vol-natural-sciences-course.tex`](book/sources/volumes/vol-natural-sciences-course.tex) |

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

## 3. Standalone Scientific Papers (`papers/` Submodule → `AI-Guiders/scientific-papers`) & Dedicated Lean 4 Modules

Linked via the [`papers/`](papers) Git submodule ([`AI-Guiders/scientific-papers`](https://github.com/AI-Guiders/scientific-papers)), organized into **Pure Mathematics (`papers/mathematics/`)** and **Unified Natural Science (`papers/theory/`, `papers/laboratory/`, `papers/engineering/`)**, each backed by its own standalone Lean 4 module (`0 sorryAx`, `0 Classical.choice`):

### I. Pure Mathematics & Abstract Computer Science (`papers/mathematics/`)
- **1. Core Rotator Calculus** · [`RotatorQuadrature.lean`](papers/RotatorQuadrature.lean) (`thm1`–`thm3`): [`rotator-quadrature-en.pdf`](papers/mathematics/rotator-quadrature-en.pdf) · [`-ru.pdf`](papers/mathematics/rotator-quadrature-ru.pdf)
- **2. Logic, Cohomology & Complexity Barriers** · [`LogicCohomology.lean`](papers/LogicCohomology.lean) (`thm4`–`thm5`): [`logic-cohomology-barriers-en.pdf`](papers/mathematics/logic-cohomology-barriers-en.pdf) · [`-ru.pdf`](papers/mathematics/logic-cohomology-barriers-ru.pdf)
- **3. Pillai's Problem ($A x^m - B y^n = C$)** · [`PillaiDiophantine.lean`](papers/PillaiDiophantine.lean) (`thm6`, `thm7`, `thm10`, `thm11`): [`pillai-exponential-diophantine-en.pdf`](papers/mathematics/pillai-exponential-diophantine-en.pdf) · [`-ru.pdf`](papers/mathematics/pillai-exponential-diophantine-ru.pdf)
- **4. `abc` Triples ($A + B = C$)** · [`AbcPlanetaryWronskian.lean`](papers/AbcPlanetaryWronskian.lean) (`thm8`, `thm9`, `thm12`–`thm16`): [`abc-planetary-differential-wronskian-en.pdf`](papers/mathematics/abc-planetary-differential-wronskian-en.pdf) · [`-ru.pdf`](papers/mathematics/abc-planetary-differential-wronskian-ru.pdf)
- **5. Collatz Planetary Gear Splice ($\mathbb{Z}_{2^a} \times \mathbb{Z}_{3^b}^\times$)** · [`CollatzPlanetarySplice.lean`](papers/CollatzPlanetarySplice.lean) (`thm18`–`thm29`, `collatz_global_convergence_from_local_descent`): [`collatz-natural-ring-wronskian-en.pdf`](papers/mathematics/collatz-natural-ring-wronskian-en.pdf) · [`-ru.pdf`](papers/mathematics/collatz-natural-ring-wronskian-ru.pdf)

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

# 3. Build the 4 core books of Unified Natural Science:
pwsh -NoProfile -File book/build.ps1 -Volume monograph
pwsh -NoProfile -File book/build.ps1 -Volume laboratory
pwsh -NoProfile -File book/build.ps1 -Volume engineering
pwsh -NoProfile -File book/build.ps1 -Volume course
```
