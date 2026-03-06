# Technical Debt Tracker

## Open

### Deferred graph realization

- [ ] **SimpleGraph realization + edist bridge** — The log-ratio theorem uses
  pure arithmetic recurrences. A bridge theorem should connect `flowerHubDist`
  to `SimpleGraph.edist` on an explicit graph model. **Design progress:**
  `FlowerConstruction.lean` implements a structured-gadget approach with
  `GadgetPos`, `LocalEdge`, recursive `FlowerEdge` edge indices,
  `edgeEndpoints` resolution, `FlowerVert` with hub embedding, `flowerGraph'`
  as `SimpleGraph`, projection map for lower bound, and `flowerGraph_dist_hubs`
  as the F2 bridge target. Several sorry stubs remain (irreflexivity,
  connectivity, walk/distance bounds, vertex card, final transport).
  *(FlowerConstruction.lean, FlowerGraph.lean)*

- [ ] **Log-ratio dimension bridge** — Prove `HasLogRatioDimension` for the
  (u,v)-flower family. Definition exists in `FlowerLogRatio.lean`. Requires
  the SimpleGraph realization above; then F3 follows from F1 + distance bridge.
  *(FlowerLogRatio.lean)*

### Upstream candidates

- [ ] **SimpleGraph.ball PR** — Clean up GraphBall.lean for Mathlib PR.
  Now has 12 lemmas (expanded API): `mem_ball`, `edist_le_of_mem_ball`,
  `ball_zero`, `ball_top`, `ball_mono`, `ball_anti`, `center_mem_ball`,
  `nonempty_ball`, `ball_comm`, `ball_one_eq`, `adj_of_mem_ball_one`,
  `mem_ball_of_mem_ball_of_mem_ball`. Watch PR #33077 (Yael Dillies,
  SetRel.ball) for potential overlap. Key reviewer: Rida Hamadani.
  *(GraphBall.lean)*

- [ ] **GraphBall finite cardinality lemmas** — `card_ball_mono` etc. require
  `[Fintype V]`. Separated from base definition by design. *(GraphBall.lean)*

- [ ] **pathGraph distance lemmas** — `pathGraph_dist`, `pathGraph_dist_zero_last`,
  `pathGraph_edist_zero_last`, `pathGraph_exists_walk_zero_last`. These fill a
  Mathlib gap: distance in `pathGraph (n+1)` equals `|i - j|`. Currently sorry
  stubs. Needed as building blocks for recursive graph distance proofs.
  *(PathGraphDist.lean)*

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
