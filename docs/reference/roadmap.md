# Roadmap

Theorem targets for the Project Navi formalization program.

| Status | Meaning |
|---|---|
| Shipped | proved on `main` |
| Next | next target |
| Research | meaningful, not on the critical path |
| Conjecture | conjectural in the reference program |
| Empirical | instrumentation claim, not a theorem |

---

## Shipped

- **F1: log-ratio limit** (`FlowerDimension.lean`). \(\lim_{g \to \infty} \log N_g / \log L_g = \log(u+v)/\log u\) for the recurrence-defined counts, by a squeeze.
- **F2: hub distance** (`FlowerConstruction.lean`). The explicit flower graph on `FlowerVert` / `Fin` has hub distance \(u^g\): walk upper bound, rank lower bound.
- **SimpleGraph.ball** (`GraphBall.lean`). Open metric ball via `edist` with 7 core lemmas; upstreamed to Mathlib.

---

## Next

**F3: `HasLogRatioDimension` for `flowerGraph`**, i.e. F1 for the constructed graphs. It follows from F1, F2 and \(\lvert\mathrm{Fin}\,n\rvert = n\) when the distinguished vertices are F2's hubs; stating it with the `Fin`-indexed `hub0`/`hub1` first needs an equivalence that sends the hubs to 0 and 1.

---

## Research

| ID | Target | Repo |
|---|---|---|
| F4 | Creative Determinant class \(\mathrm{CD}(\alpha, \varepsilon, \delta)\): compact \(X\), \(C^1\) map \(F\), fixed observable, invariant ergodic measure | `cd-formalization` |
| F5 | Lyapunov-determinant theorem: \(\sum \lambda_i = \int \log \lvert\det \nabla F\rvert\, d\mu\) | `cd-formalization` |
| F6 | CD implies fractal structure, under hyperbolicity / SRB assumptions | `cd-formalization` |
| F7 | Equal-contraction IFS: \(k \cdot d^{D/n} = 1\) implies \(D = -n \log k / \log d\) | benchmark repo |
| F8 | Monofractal benchmark: \(D(q)\) constant in \(q\), so \(\Delta D = 0\) | benchmark repo |

F4--F6 need measure theory, ergodic averages and Jacobian integration. F7--F8 are low-risk calibration targets.

---

## Conjectures

| ID | Direction |
|---|---|
| C1 | Robust internal fractal scaling implies a natural observable and coupling satisfying CD |
| C2 | CD systems with fractal dimension \(D\) admit observation sets of size \(\sim D\) for navigation |
| C3 | Operational closure (autopoiesis) iff CD for a natural observable |

Not ready for Lean.

---

## Empirical claims (`navi-fractal`)

| ID | Claim |
|---|---|
| E1 | Sandbox \(R^2 > 0.85\) predicts graceful degradation; below, catastrophic |
| E2 | The CD finite-data estimator is a practical check, not a certification of ergodicity or invariance |
| E3 | The sandbox estimator emits a dimension only when the scaling window passes span, slope and evidence checks |

Software and calibration claims, not theorems.

---

## Sequencing

1. **A:** F3.
2. **B:** F4--F6.
3. **C:** F7--F8.
4. Conjectures and empirical claims stay labeled as such.
