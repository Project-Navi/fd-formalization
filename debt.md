# Technical Debt Tracker

## Open

### Deferred graph realization

- [ ] **SimpleGraph model of the (u,v)-flower** — The headline dimension theorem
  uses pure arithmetic recurrences for vertex count and hub distance. A future
  bridge theorem should connect `flowerHubDist` to `SimpleGraph.edist` on an
  explicit graph model. This is a separate milestone, not a blocker.
  *(FlowerGraph.lean)*

### Upstream candidates

- [ ] **SimpleGraph.ball PR** — Clean up GraphBall.lean for Mathlib PR.
  Watch PR #33077 (Yael Dillies, SetRel.ball) for potential overlap.
  Key reviewer: Rida Hamadani. *(GraphBall.lean)*

- [ ] **GraphBall finite cardinality lemmas** — `card_ball_mono` etc. require
  `[Fintype V]`. Separated from base definition by design. *(GraphBall.lean)*

### Deferred (future milestones)

- [ ] **Transfractal case u = 1** — Infinite d_B. Separate theorem with
  different proof structure. *(new file)*

- [ ] **Multifractal spectrum tau(q)** — Furuya & Yakubo 2011 analytical
  formula for (u,v)-flowers. *(new file)*

- [ ] **Scaling relations** — Fronczak et al. 2024 seven-exponent framework.
  *(new file)*

- [ ] **OLS optimality** — Prove the OLS estimator minimizes SSE. Connects
  back to navi-fractal's regression core. *(new file)*

- [ ] **lean4checker integration** — Add `lean4checker --fresh` to CI for
  independent proof validation. *(lean_action_ci.yml)*

## Resolved

- [x] **Counting formulas** — `flowerEdgeCount_eq_pow`, `flowerVertCount_eq`,
  positivity, and two-sided bounds all proved. Real-valued wrappers included.
  *(FlowerCounts.lean)*

- [x] **Hub distance exact formula** — `flowerHubDist_eq_pow` proved as pure
  arithmetic recurrence (Option 3). No axiom fallback needed.
  *(FlowerDiameter.lean)*

- [x] **Headline dimension theorem** — `flowerDimension` proved via Route B
  (squeeze). Zero sorry, zero custom axioms.
  *(FlowerDimension.lean)*
