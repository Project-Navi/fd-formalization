/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Graph Balls via Extended Distance

Defines the metric ball on a `SimpleGraph` using `edist` (not `dist`),
so that disconnected vertices are correctly excluded (they have
`edist = ⊤`, not `dist = 0`).

## Main definitions

- `SimpleGraph.ball` — the set of vertices within extended distance `r`
  of a center vertex `c`

## Main statements

- `SimpleGraph.mem_ball` — membership characterization
- `SimpleGraph.ball_mono` — monotonicity in radius

## Implementation notes

This file is designed as an upstream Mathlib candidate. It has no
project-specific imports. The definition and basic API work on
arbitrary vertex types; finiteness lemmas requiring `[Fintype V]`
are separated into their own section.

## References

- Mathlib `SimpleGraph.Metric` for `edist`

## Tags

simple graph, metric ball, edist, graph distance
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The ball of radius `r` around vertex `c` in the graph metric.
Uses `edist` so that unreachable vertices (at distance `⊤`) are
correctly excluded. -/
def ball (c : V) (r : ℕ∞) : Set V :=
  {v | G.edist c v ≤ r}

@[simp]
theorem mem_ball {c : V} {v : V} {r : ℕ∞} :
    v ∈ G.ball c r ↔ G.edist c v ≤ r :=
  Iff.rfl

/-- Balls are monotone in the radius. -/
theorem ball_mono {c : V} {r₁ r₂ : ℕ∞} (h : r₁ ≤ r₂) :
    G.ball c r₁ ⊆ G.ball c r₂ :=
  fun _ hv ↦ le_trans hv h

/-- The center vertex belongs to any ball around it. -/
theorem center_mem_ball {c : V} {r : ℕ∞} :
    c ∈ G.ball c r := by
  simp [ball, SimpleGraph.edist_self]

end SimpleGraph
