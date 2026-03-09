# Roadmap

Formal theorem targets for the Project Navi formalization program. Each target has a status, a mathematical statement, and a repo assignment.

---

## Status legend

- **Shipped** --- proved and merged on main
- **Next** --- high-leverage next target
- **Research** --- mathematically meaningful, not yet on the critical path
- **Conjecture** --- explicitly conjectural in the reference program
- **Empirical** --- instrumentation claim, not a formal theorem

---

## Shipped

### F1: Flower log-ratio theorem

\[
\lim_{g \to \infty} \frac{\log N_g}{\log L_g} = \frac{\log(u+v)}{\log u}
\]

Vertex-count / hub-distance log-ratio convergence for the arithmetic \((u,v)\)-flower model via Route B (squeeze). Zero sorry, zero custom axioms.

**Repo:** `fd-formalization` | **File:** `FlowerDimension.lean`

### F2: Hub distance bridge

\[
\operatorname{dist}_G(\text{hub}_0, \text{hub}_1) = u^g
\]

Explicit `SimpleGraph` construction on `FlowerVert` / `Fin` with graph-theoretic hub distance equal to \(u^g\). Structured-gadget approach with projection lower bound and walk upper bound.

**Repo:** `fd-formalization` | **File:** `FlowerConstruction.lean`

### Upstream: SimpleGraph.ball

Open metric ball via `edist` (strict `<`, not `\leq`). 1 definition + 7 core lemmas. `ball_top` gives connected-component support. PR ready to open for Mathlib.

**Repo:** `fd-formalization` | **File:** `GraphBall.lean`

---

## Next

### F3: HasLogRatioDimension for the flower family

\[
\texttt{HasLogRatioDimension}\ (\texttt{flowerGraph}\ u\ v)\ (\text{hub}_0)\ (\text{hub}_1)\ \bigl(\log(u+v)/\log u\bigr)
\]

Combines F1 + F2 by rewriting `Fintype.card (Fin n) = n` and the distance bridge. The definition `HasLogRatioDimension` already exists in `FlowerLogRatio.lean`.

**Repo:** `fd-formalization`

---

## Research

| ID | Target | Statement shape | Repo |
|---|---|---|---|
| F4 | Creative Determinant class definition | Formal \(\mathrm{CD}(\alpha, \varepsilon, \delta)\) on compact \(X\), \(C^1\) map \(F\), fixed observable, invariant ergodic measure | `cd-formalization` |
| F5 | Lyapunov-determinant theorem | \(\sum \lambda_i = \int \log |\det \nabla F|\, d\mu\) | `cd-formalization` |
| F6 | CD implies fractal structure | Under hyperbolicity / SRB assumptions, CD implies nontrivial Lyapunov spectrum and fractal attractor structure | `cd-formalization` |
| F7 | Equal-contraction IFS dimension formula | \(k \cdot d^{D/n} = 1\) implies \(D = -n \log k / \log d\) | benchmark repo |
| F8 | Monofractal benchmark theorem | For a self-similar family, \(D(q)\) is constant in \(q\), hence \(\Delta D = 0\) | benchmark repo |

**F4--F6** are the rigorous core of the Creative Determinant theory program. They require measure/integration framework, ergodic averages, and Jacobian determinant integration.

**F7--F8** are clean benchmark theorems --- mathematically low-risk and good calibration targets for the dimension machinery.

---

## Conjectures

| ID | Target | Direction |
|---|---|---|
| C1 | Fractal implies CD | Robust internal fractal scaling implies existence of natural observable and coupling satisfying CD |
| C2 | CD implies navigable | CD systems with fractal dimension \(D\) admit effective observation sets of size \(\sim D\) for navigation |
| C3 | Autopoietic iff CD | Operational closure implies CD for a natural observable, and conversely |

These are explicitly conjectural. Not ready for Lean-first treatment.

---

## Empirical claims

| ID | Claim | Repo |
|---|---|---|
| E1 | Sandbox \(R^2 > 0.85\) predicts graceful degradation; \(R^2 < 0.85\) predicts catastrophic | `navi-fractal` |
| E2 | CD finite-data estimator is a practical check, not a certification of ergodicity/invariance | `navi-fractal` |
| E3 | Sandbox estimator only emits a dimension when scaling window passes span/slope/evidence checks | `navi-fractal` |

These are software-spec and calibration claims, not theorems. They belong in the experimental repos with benchmark suites and statistical validation.

---

## Recommended sequencing

### Phase A: Finish the flower story

1. F1 shipped --- log-ratio convergence
2. F2 shipped --- `SimpleGraph.dist` bridge
3. **F3 next** --- combines F1 + F2 to earn `HasLogRatioDimension`

### Phase B: Build the CD hard core

4. F4 --- formalize the CD class definition
5. F5 --- formalize the Lyapunov-determinant bridge
6. F6 --- CD implies fractal structure under stated assumptions

### Phase C: Benchmark the dimension machinery

7. F7 --- equal-contraction IFS theorem
8. F8 --- monofractal benchmark for multifractal machinery

### Phase D: Keep boundaries clean

9. Conjectures (C1--C3) stay labeled as conjectural frontier
10. Empirical claims (E1--E3) stay in experimental repos with calibration data
