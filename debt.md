# Technical Debt Tracker

## Open

### Core proof work

- [ ] **FlowerGraph vertex representation** — Choose between Fin-indexed,
  inductive vertex type, or sigma type. This is the key implementation risk;
  the vertex type must support Fintype instances and graph metric reasoning.
  *(FlowerGraph.lean)*

- [ ] **FlowerDiameter exact formula** — The diameter `L_g = u^g` requires
  reasoning about shortest paths in the recursive construction. This is
  where proof complexity concentrates: the vertex type must interact with
  `SimpleGraph.edist`, and the shortest-path argument recurses through the
  construction. Parity of u and v may affect the exact formula. Expect this
  file to be the longest by a factor of ~3x. If friction blocks progress,
  consider axiomatizing diameter as a fallback (but this weakens the zero-axiom
  story). *(FlowerDiameter.lean)*

- [ ] **Real-valued wrappers** — Define `V_count_real` and `L_diam_real` with
  explicit ℕ → ℝ casts and prove positivity lemmas. Cast early to avoid
  coercion fights in FlowerDimension. *(FlowerCounts.lean, FlowerDiameter.lean)*

### Upstream candidates

- [ ] **SimpleGraph.ball PR** — Clean up GraphBall.lean for Mathlib PR.
  Watch PR #33077 (Yael Dillies, SetRel.ball) for potential overlap.
  Key reviewer: Rida Hamadani. *(GraphBall.lean)*

- [ ] **GraphBall finite cardinality lemmas** — `card_ball_mono` etc. require
  `[Fintype V]`. Separated from base definition by design. *(GraphBall.lean)*

### Deferred (future milestones)

- [ ] **Transfractal case u = 1** — Infinite d_B. Separate theorem with
  different proof structure. *(new file)*

- [ ] **Multifractal spectrum τ(q)** — Furuya & Yakubo 2011 analytical
  formula for (u,v)-flowers. *(new file)*

- [ ] **Scaling relations** — Fronczak et al. 2024 seven-exponent framework.
  *(new file)*

- [ ] **OLS optimality** — Prove the OLS estimator minimizes SSE. Connects
  back to navi-fractal's regression core. *(new file)*

- [ ] **lean4checker integration** — Add `lean4checker --fresh` to CI for
  independent proof validation. *(lean_action_ci.yml)*

## Resolved

(None yet — project just scaffolded.)
