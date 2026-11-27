# For Physicists & Natural Scientists

This track covers the Unified Natural Science framework across **Books I–IV** ([Book I: Monograph](https://github.com/AI-Guiders/discrete-quantum-mechanics/raw/main/book/out/pdf/formal-foundations-monograph.pdf), [Book II: Lab Manual](https://github.com/AI-Guiders/discrete-quantum-mechanics/raw/main/book/out/pdf/dqm-laboratory-manual.pdf), [Book III: Engineering Handbook](https://github.com/AI-Guiders/discrete-quantum-mechanics/raw/main/book/out/pdf/dqm-engineering-handbook.pdf), [Book IV: Course](https://github.com/AI-Guiders/discrete-quantum-mechanics/raw/main/book/out/pdf/natural-sciences-course.pdf)).

---

## 1. Derivation of Spatial Dimension $d=3$ & the 72-Bit Cell

Rather than postulating $d=3$ or continuous real coordinates $\mathbb{R}^3$, the discrete carrier derives spatial dimensionality from the exact Diophantine closure of the local causal square (`Core.lean`):

$$1 + 2^d = d^2 \iff d = 3.$$

From $d=3$, all structural invariants of the vacuum lattice follow without adjustable parameters:

- **Elementary cell size:** $|S_{\mathrm{cell}}| = d^2 = 9$ nodes, with $2^d = 8$ boundary nodes around 1 central node, yielding the **72-bit cell state** ($9 \times 8 = 72$ bits).
- **Isotropic coordination shell:** The 12-ray cuboctahedral stencil $O_2$ ($N_{O_2}(3) = 2d(d-1) = 12$ unit face-diagonal rays of squared length 2).
- **Projective phase period:** $2^{d^2} = 2^9 = 512$ phase ticks per full cycle, with Pauli exclusion half-period $\Phi_{\mathrm{Pauli}}(3) = 256$, quadrant peak $Q_\square(3) = 128$, and Heisenberg discreteness floor $\Delta\varphi_{\mathrm{disc}}(3) = 41$ ($|E_{\mathrm{Heis}}| = 2\cdot 41 - 1 = 81 = 3^4$).
- **Ballistic-to-light speed ratio:** $(c_0 / c)^2 = 16 / 9$ ($c_0 / c = 4 / 3$), directly yielding the Tsirelson quantum correlation bound $S_{\mathrm{QM}}^2 = (16/9)\,S_{\mathrm{LHV}}^2 = (2\sqrt{2})^2 = 8$ and the cosmological vacuum holonomy halo factor $16/3$.

---

## 2. Fine-Structure Constant & Particle/Nuclear Spectrum

- **Algebraic Fine-Structure Constant (`ContinuumPhysics.lean`, `alpha.py`):**
  On the 12-ray cuboctahedral rotor, the integer bulk topological budget $12^2 - (d^2 - 2) = 144 - 7 = 137$ combines with the quadratic irrational boundary holonomy correction in $\mathbb{Q}(\sqrt{2})$:

  $$\alpha_{\mathrm{fs}}^{-1} = 137 + \frac{1}{28 - 2\sqrt{2}} = \frac{103\,851 + 2\sqrt{2}}{758} \approx 137.036797 \quad (6.3\text{ ppm from CODATA } 137.035999).$$

- **Nuclear Shell Closures & Pauli Black-Hole Core (`NuclearShells.lean`):**
  Reproduces magic numbers across 8 periods of the Mendeleev table, predicts the superheavy island of stability at neutron closure $N = 184$, models nuclear pasta transitions, and replaces gravitational point singularities with an incompressible Pauli core at density ratio $833 : 1$.

- **Markov-Blanket Ontogeny & Inverse DNA Compiler (`OntogenyMutagenesis.lean`):**
  Formalizes the homomorphism from 12-ray environmental stress tensors across a Markov blanket to the 64-codon genetic code ($K_P(3) = 64$), `CpG` methylation mutagenesis, and deterministic compilation of target tissue topologies into codon sequences.

---

## 3. Running the Verification Gate Suite

All physical constants, conservation laws, and lattice invariants are verified by deterministic Python suites:

```bash
# Fast core gate suite (3/3 checks)
python verify_principles.py --suite gate

# Full multi-discipline verification suite
python verify_principles.py --suite all
```
