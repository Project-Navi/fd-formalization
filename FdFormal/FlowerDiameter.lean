/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.FlowerGraph
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Flower Graph Diameter Scaling

The diameter of the (u,v)-flower at generation `g` scales as `u^g`
for `u > 1`. The shortest path between the two hub vertices traverses
the shorter parallel path (of length `u`) at each generation, giving
`L_g = u^g`.

## Main statements

- `flower_diam_eq` — `L_g = u^g` (or asymptotic bound if exact
  formula requires parity analysis)

## Implementation notes

The exact diameter formula `L_g = u^g` holds because:
1. The two original hubs are at distance `u^g` (the short path
   recurses through `g` generations).
2. No pair of vertices can be farther apart (the long path of
   length `v^g` between hubs provides an alternative route, but
   `u ≤ v` means internal vertices on the long path are closer
   to a hub than the hub-to-hub distance).

For the headline theorem, we need `Real.log L_g / g → Real.log u`,
which follows from `L_g = u^g` and `Real.log (u^g) = g * Real.log u`.

## References

- [Rozenfeld2007] §2, diameter analysis.
-/

-- TODO: State and prove diameter formula once FlowerGraph is defined.
--
-- Real-valued wrapper:
--   def L_diam_real (u v g : ℕ) : ℝ := (L_g : ℝ)
-- Cast early, prove positivity (L_g > 0 for g ≥ 1, u > 1).
