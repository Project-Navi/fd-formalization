# Formal Roadmap

## Status legend

- **Shipped** — proved / implemented in current repo
- **Next** — high-leverage next theorem target
- **Research** — mathematically meaningful, not yet on the critical path
- **Conjecture** — explicitly conjectural in the reference program
- **Empirical** — instrumentation / calibration claim, not a formal theorem

## Theorem targets

### Shipped

| ID | Target | Statement | Repo |
|----|--------|-----------|------|
| F1 | Flower log-ratio theorem | `Tendsto (fun g => log N_g / log L_g) atTop (nhds (log(u+v) / log u))` | `fd-formalization` |
| F2 | Hub distance bridge | `(flowerGraph u v g).dist hub0 hub1 = u^g` | `fd-formalization` |

**F1** proves vertex-count / hub-distance log-ratio convergence for the
**arithmetic** (u,v)-flower model via Route B (squeeze).

**F2** constructs the (u,v)-flower as an explicit `SimpleGraph` on
`FlowerVert` / `Fin` and proves the graph-theoretic hub distance equals `u^g`.
The proof uses a structured-gadget approach with five layers: local gadget
(`GadgetPos`, `LocalEdge`), recursive types (`FlowerEdge`, `FlowerVert`),
endpoint resolution (`edgeEndpoints`), `SimpleGraph` construction
(`flowerGraph'`), rank-based lower bound + walk upper bound, and transport
to `Fin` via `Fintype.equivFinOfCardEq`.

Supporting infrastructure (monotonicity, cast identities, log helpers) is
in `FlowerCounts`, `FlowerDiameter`, and `FlowerLog`. Leaf lemmas are proved
via a combination of human authoring and Aristotle automated proof search.

**Upstream contribution:** `GraphBall.lean` defines `SimpleGraph.ball` as an
open ball via `edist` (strict `<`, not `≤`). Reshaped per Zulip discussion and
auditor feedback: 1 def + 7 core lemmas (`mem_ball`, `ball_zero`, `ball_one`,
`ball_top`, `ball_mono`, `center_mem_ball`, `mem_ball_comm`) form the upstream
PR; convenience lemmas kept in-repo.
Import simplified to `Mathlib.Combinatorics.SimpleGraph.Metric`.
`ball_top` now gives connected-component support. PR ready to open.

### Next

| ID | Target | Prerequisites | Repo |
|----|--------|---------------|------|
| F3 | `HasLogRatioDimension` for the flower family | F1 + F2 | `fd-formalization` |

**F3** is the target theorem: `HasLogRatioDimension (flowerGraph u v) (hub0 u v) (hub1 u v) (log(u+v)/log u)`.
The definition `HasLogRatioDimension` is in `FlowerLogRatio.lean` (adapted from
Aristotle-generated `HasBoxCountingDimension`, renamed for honesty — it defines a
growth exponent, not general box-covering dimension). F3 follows from F1 + F2 by
rewriting `Fintype.card (Fin n) = n` and the distance bridge.

### Research

| ID | Target | Statement shape | Repo |
|----|--------|----------------|------|
| F4 | Creative Determinant class definition | Formal `CD(alpha, eps, delta)` on compact `X`, `C^1` map `F`, fixed observable, invariant ergodic measure | `cd-formalization` |
| F5 | Lyapunov-determinant theorem | `sum lambda_i = integral log |det nabla F| d mu` | `cd-formalization` |
| F6 | CD implies fractal structure | Under hyperbolicity / SRB assumptions, `CD` implies nontrivial Lyapunov spectrum and fractal attractor structure | `cd-formalization` |
| F7 | Equal-contraction IFS dimension formula | `k * d^(D/n) = 1` implies `D = -n log k / log d` | benchmark repo |
| F8 | Monofractal benchmark theorem | For a self-similar family, `D(q)` is constant in `q`, hence `Delta D = 0` | benchmark repo |

**F4-F6** are the rigorous core of the Creative Determinant theory program.
They belong in a sister repo and require measure/integration framework,
ergodic averages, and Jacobian determinant integration.

**F7-F8** are clean benchmark theorems: mathematically low-risk and good
calibration targets for the dimension machinery.

### Conjectures

| ID | Target | Direction |
|----|--------|-----------|
| C1 | Fractal implies CD | Robust internal fractal scaling implies existence of natural observable and coupling satisfying CD |
| C2 | CD implies navigable | CD systems with fractal dimension `D` admit effective observation sets of size `~D` for navigation |
| C3 | Autopoietic iff CD | Operational closure implies CD for a natural observable, and conversely |

These are explicitly conjectural in both the reference program and here.
Not ready for Lean-first treatment.

### Empirical

| ID | Claim | Repo |
|----|-------|------|
| E1 | Sandbox `R^2 > 0.85` predicts graceful degradation; `R^2 < 0.85` predicts catastrophic | `navi-fractal` |
| E2 | CD finite-data estimator is a practical check, not a certification of ergodicity/invariance | `navi-fractal` |
| E3 | Sandbox estimator only emits a dimension when scaling window passes span/slope/evidence checks | `navi-fractal` |

These are software-spec and calibration claims, not theorems. They belong
in the experimental repos with benchmark suites and statistical validation.

## Recommended sequencing

### Phase A: Finish the flower story honestly

1. **F1** shipped — log-ratio convergence.
2. **F2** shipped — `SimpleGraph.dist` bridge.
3. Do **F3** next — combines F1 + F2 to earn `HasLogRatioDimension`.

### Phase B: Build the CD hard core (separate lane)

4. **F4** — formalize the CD class definition.
5. **F5** — formalize the Lyapunov-determinant bridge.
6. **F6** — the real flagship: CD implies fractal structure under stated assumptions.

### Phase C: Benchmark the dimension machinery

7. **F7** — equal-contraction IFS theorem (clean, low-risk).
8. **F8** — monofractal benchmark for the multifractal machinery.

### Phase D: Keep boundaries clean

9. Conjectures (**C1-C3**) stay labeled as conjectural frontier.
10. Empirical claims (**E1-E3**) stay in experimental repos with calibration data.
