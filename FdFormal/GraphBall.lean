/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Metric balls for simple graphs

This file defines the metric ball `SimpleGraph.ball` using the extended
distance `SimpleGraph.edist`. Using `edist` (rather than `dist`) ensures
that disconnected vertices, which are at distance `⊤`, are correctly
excluded from finite-radius balls.

## Main definitions

- `SimpleGraph.ball` — the set of vertices within extended distance `r`
  of a center vertex

## Main statements

- `SimpleGraph.mem_ball` — membership characterization
- `SimpleGraph.ball_mono` — monotonicity in radius
- `SimpleGraph.ball_zero` — the zero-radius ball is `{c}`
- `SimpleGraph.ball_top` — the `⊤`-radius ball is `Set.univ`
- `SimpleGraph.ball_comm` — `v ∈ G.ball c r ↔ c ∈ G.ball v r`
- `SimpleGraph.ball_anti` — supergraphs have larger balls

## Tags

simple graph, metric ball, edist, graph distance
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-! ### Definition and membership -/

/-- The closed ball of radius `r` around vertex `c` in the graph extended metric. -/
def ball (c : V) (r : ℕ∞) : Set V :=
  {v | G.edist c v ≤ r}

variable {G}

@[simp]
theorem mem_ball {c v : V} {r : ℕ∞} :
    v ∈ G.ball c r ↔ G.edist c v ≤ r :=
  Iff.rfl

theorem edist_le_of_mem_ball {c v : V} {r : ℕ∞} (h : v ∈ G.ball c r) :
    G.edist c v ≤ r :=
  h

/-! ### Radius extremes -/

@[simp]
theorem ball_zero {c : V} : G.ball c 0 = {c} := by
  ext v
  simp [ball, nonpos_iff_eq_zero]

@[simp]
theorem ball_top {c : V} : G.ball c ⊤ = Set.univ := by
  ext v
  simp [ball]

/-! ### Monotonicity -/

/-- Balls are monotone in the radius. -/
theorem ball_mono {c : V} {r₁ r₂ : ℕ∞} (h : r₁ ≤ r₂) :
    G.ball c r₁ ⊆ G.ball c r₂ :=
  fun _ hv ↦ le_trans hv h

/-- Supergraphs have larger or equal balls. -/
@[gcongr]
theorem ball_anti {G' : SimpleGraph V} {c : V} {r : ℕ∞} (h : G ≤ G') :
    G.ball c r ⊆ G'.ball c r :=
  fun _ hv ↦ le_trans (edist_anti h) hv

/-! ### Center and symmetry -/

/-- The center vertex belongs to any ball around it. -/
@[simp]
theorem center_mem_ball {c : V} {r : ℕ∞} :
    c ∈ G.ball c r := by
  simp [ball]

theorem nonempty_ball {c : V} {r : ℕ∞} : (G.ball c r).Nonempty :=
  ⟨c, center_mem_ball⟩

/-- Ball membership is symmetric in center and point. -/
theorem ball_comm {c v : V} {r : ℕ∞} :
    v ∈ G.ball c r ↔ c ∈ G.ball v r := by
  simp [ball, edist_comm]

/-! ### Adjacency -/

theorem ball_one_eq {c : V} :
    G.ball c 1 = {v | G.edist c v ≤ 1} :=
  rfl

theorem adj_of_mem_ball_one {c v : V} (h : v ∈ G.ball c 1) (hne : c ≠ v) :
    G.Adj c v := by
  rw [mem_ball] at h
  exact (edist_le_one_iff_adj_or_eq.mp h).resolve_right hne

/-! ### Triangle inequality -/

/-- If `v ∈ ball c r₁` and `w ∈ ball v r₂`, then `w ∈ ball c (r₁ + r₂)`. -/
theorem mem_ball_of_mem_ball_of_mem_ball {c v w : V} {r₁ r₂ : ℕ∞}
    (hv : v ∈ G.ball c r₁) (hw : w ∈ G.ball v r₂) :
    w ∈ G.ball c (r₁ + r₂) :=
  le_trans G.edist_triangle (add_le_add hv hw)

end SimpleGraph
