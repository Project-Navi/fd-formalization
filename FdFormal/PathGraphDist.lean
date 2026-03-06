/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Distance in path graphs

**Status: Stub.** Statements are frozen; proofs are pending (submitted to
Aristotle automated prover).

The graph distance between vertices `i` and `j` in `pathGraph (n + 1)`
equals `|i - j|`. These lemmas are building blocks for distance proofs
in recursive graph constructions.

## Main statements

- `SimpleGraph.pathGraph_dist` — `dist i j = |i.val - j.val|`
- `SimpleGraph.pathGraph_dist_zero_last` — `dist 0 (Fin.last n) = n`
- `SimpleGraph.pathGraph_edist_zero_last` — `edist 0 (Fin.last n) = n`

## Tags

path graph, graph distance, Hasse diagram
-/

namespace SimpleGraph

/-! ### Walk construction -/

/-- There is a walk of length `n` from `0` to `Fin.last n` in `pathGraph (n + 1)`. -/
theorem pathGraph_exists_walk_zero_last (n : ℕ) :
    ∃ w : (pathGraph (n + 1)).Walk 0 (Fin.last n), w.length = n := by
  sorry

/-! ### Distance formula -/

/-- Distance in a path graph equals the absolute difference of indices. -/
theorem pathGraph_dist {n : ℕ} (i j : Fin (n + 1)) :
    (pathGraph (n + 1)).dist i j = if i.val ≤ j.val then j.val - i.val else i.val - j.val := by
  sorry

/-- Distance from `0` to `Fin.last n` in `pathGraph (n + 1)` is `n`. -/
theorem pathGraph_dist_zero_last (n : ℕ) :
    (pathGraph (n + 1)).dist (0 : Fin (n + 1)) (Fin.last n) = n := by
  sorry

/-- The extended distance from `0` to `Fin.last n` in `pathGraph (n + 1)` is `n`. -/
theorem pathGraph_edist_zero_last (n : ℕ) :
    (pathGraph (n + 1)).edist (0 : Fin (n + 1)) (Fin.last n) = n := by
  sorry

end SimpleGraph
