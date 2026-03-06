# Technical Debt Tracker

## Open

### Deferred graph realization

- [ ] **SimpleGraph realization + edist bridge** — The log-ratio theorem uses
  pure arithmetic recurrences. A bridge theorem should connect `flowerHubDist`
  to `SimpleGraph.edist` on an explicit graph model. This is the narrower of
  the two paths to connecting the log-ratio result to actual graph distance.
  *(FlowerGraph.lean)*

- [ ] **Log-ratio dimension bridge** — Prove `HasLogRatioDimension` for the
  (u,v)-flower family. Definition exists in `FlowerLogRatio.lean`. Requires
  the SimpleGraph realization above; then F3 follows from F1 + distance bridge.
  *(FlowerLogRatio.lean)*

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

- [x] **Monotonicity + cast identities** — `flowerEdgeCount_strict_mono`,
  `flowerVertCount_strict_mono`, `flowerHubDist_strict_mono`,
  `flowerVertCount_cast_eq`, `flowerHubDist_cast_eq_pow`. Leaf infrastructure
  for downstream proofs. *(FlowerCounts.lean, FlowerDiameter.lean)*

- [x] **Log identities + squeeze bounds** — `log_flowerHubDist_eq`,
  `log_flowerEdgeCount_eq`, `log_flowerVertCount_residual_lower/upper`.
  Extracted from FlowerDimension inline proofs into standalone lemmas.
  *(FlowerLog.lean)*

- [x] **HasLogRatioDimension definition** — Bridge target for F3. Uses
  `SimpleGraph.dist`, not `edist`. Compiles clean.
  *(FlowerLogRatio.lean)*

- [x] **Log-ratio convergence theorem** — `flowerDimension` proved via Route B
  (squeeze). Zero sorry, zero custom axioms. Proves the limit, not yet
  formally connected to box-counting dimension.
  *(FlowerDimension.lean)*
