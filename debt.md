# Technical Debt Tracker

## Open

### Deferred bridges

- [ ] **Log-ratio dimension bridge (F3)** — Prove `HasLogRatioDimension` for
  the (u,v)-flower family. Definition exists in `FlowerLogRatio.lean`.
  `flowerGraph_dist_hubs` (F2) now provides the distance bridge; F3 follows
  from combining F1 (log-ratio limit) + F2 (graph distance = u^g).
  *(FlowerLogRatio.lean)*

### Upstream candidates

- [ ] **SimpleGraph.ball PR** — Reshaped per Zulip discussion and auditor
  feedback: open ball (`<` not `≤`), 1 def + 7 core lemmas (`mem_ball`,
  `ball_zero`, `ball_one`, `ball_top`, `ball_mono`, `center_mem_ball`,
  `mem_ball_comm`). `ball_top` gives connected-component
  support. Import simplified to `Mathlib.Combinatorics.SimpleGraph.Metric`.
  Convenience lemmas kept in-repo for project use. **Ready to open PR.**
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

- [x] **SimpleGraph realization + distance bridge (F2)** —
  `FlowerConstruction.lean` fully proved. Structured-gadget approach with
  recursive `FlowerEdge` edge indices, `edgeEndpoints` resolution, connectivity
  (`flowerGraph'_connected`), rank-based lower bound (`rank_edge_bounds` →
  `walk_length_ge_rank` → `flowerGraph'_dist_ge`), walk upper bound
  (`lift_walk` → `flowerGraph'_walk_hubs`), and comap transport to `Fin`
  (`flowerGraph_dist_hubs`). Zero sorry.
  *(FlowerConstruction.lean)*

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

- [x] **pathGraph distance lemmas** — `pathGraph_dist`, `pathGraph_dist_zero_last`,
  `pathGraph_edist_zero_last`, `pathGraph_exists_walk_zero_last`. Distance in
  `pathGraph (n+1)` equals `|i - j|`. Zero sorry.
  *(PathGraphDist.lean)*
