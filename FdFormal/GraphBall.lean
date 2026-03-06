/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Metric balls for simple graphs

This file defines the open metric ball `SimpleGraph.ball` using the extended
distance `SimpleGraph.edist`, following the convention of `Metric.ball`.

Using strict inequality (`<`) gives the natural property that `ball c ⊤`
equals the support of the connected component containing `c`.

## Main definitions

- `SimpleGraph.ball` — the set of vertices within extended distance strictly
  less than `r` of a center vertex

## Main statements

- `SimpleGraph.mem_ball` — membership characterization
- `SimpleGraph.ball_zero` — the zero-radius ball is empty
- `SimpleGraph.ball_one` — the unit ball is `{c}`
- `SimpleGraph.ball_top` — the `⊤`-radius ball is the connected component
- `SimpleGraph.ball_mono` — monotonicity in radius
- `SimpleGraph.center_mem_ball` — center belongs to any positive-radius ball
- `SimpleGraph.mem_ball_comm` — membership is symmetric in center and point

## Implementation notes

The definition uses `ℕ∞` radius to match `SimpleGraph.edist`. For finite
`n : ℕ`, `G.ball c (n + 1)` is the closed ball of radius `n` in the usual
sense (vertices at distance `≤ n`), since `edist c v < n + 1 ↔ edist c v ≤ n`
for natural numbers.

## References

* `Mathlib.Combinatorics.SimpleGraph.Metric`

## Tags

simple graph, metric ball, edist, graph distance
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The open ball of radius `r` around vertex `c` in the graph extended metric. -/
def ball (c : V) (r : ℕ∞) : Set V :=
  {v | G.edist c v < r}

variable {G}

@[simp]
theorem mem_ball {c v : V} {r : ℕ∞} :
    v ∈ G.ball c r ↔ G.edist c v < r :=
  Iff.rfl

@[simp]
theorem ball_zero {c : V} : G.ball c 0 = ∅ := by
  ext v; simp [ball]

@[simp]
theorem ball_one {c : V} : G.ball c 1 = {c} := by
  ext v
  simp only [mem_ball, Set.mem_singleton_iff]
  constructor
  · intro h
    have h0 : G.edist c v = 0 := by
      have hne : G.edist c v ≠ ⊤ := ne_top_of_lt h
      lift G.edist c v to ℕ using hne with d
      have : d < 1 := by exact_mod_cast h
      exact_mod_cast (show d = 0 from by omega)
    exact (edist_eq_zero_iff.mp h0).symm
  · rintro rfl; simp

@[simp]
theorem ball_top {c : V} :
    G.ball c ⊤ = (G.connectedComponentMk c).supp := by
  ext v
  simp only [mem_ball, ConnectedComponent.mem_supp_iff]
  constructor
  · intro h
    exact (ConnectedComponent.eq.mpr
      (reachable_of_edist_ne_top (ne_top_of_lt h))).symm
  · intro h
    exact lt_top_iff_ne_top.mpr
      (edist_ne_top_iff_reachable.mpr (ConnectedComponent.eq.mp h.symm))

/-- Balls are monotone in the radius. -/
theorem ball_mono {c : V} {r₁ r₂ : ℕ∞} (h : r₁ ≤ r₂) :
    G.ball c r₁ ⊆ G.ball c r₂ :=
  fun _ hv ↦ lt_of_lt_of_le hv h

/-- The center vertex belongs to any ball of positive radius. -/
theorem center_mem_ball {c : V} {r : ℕ∞} (hr : 0 < r) :
    c ∈ G.ball c r := by
  simp [ball, hr]

/-- Ball membership is symmetric in center and point. -/
theorem mem_ball_comm {c v : V} {r : ℕ∞} :
    v ∈ G.ball c r ↔ c ∈ G.ball v r := by
  simp [ball, edist_comm]

/-! ### Convenience lemmas (not in first upstream PR) -/

theorem edist_lt_of_mem_ball {c v : V} {r : ℕ∞} (h : v ∈ G.ball c r) :
    G.edist c v < r :=
  h

theorem ball_nonempty {c : V} {r : ℕ∞} (hr : 0 < r) : (G.ball c r).Nonempty :=
  ⟨c, center_mem_ball hr⟩

/-- Supergraphs have larger or equal balls. -/
@[gcongr]
theorem ball_anti {G' : SimpleGraph V} {c : V} {r : ℕ∞} (h : G ≤ G') :
    G.ball c r ⊆ G'.ball c r :=
  fun _ hv ↦ lt_of_le_of_lt (edist_anti h) hv

/-- Vertices adjacent to `c` are in the ball of radius 2. -/
theorem mem_ball_of_adj {c v : V} (h : G.Adj c v) :
    v ∈ G.ball c 2 := by
  simp only [mem_ball]
  have h1 : (1 : ℕ∞) < 2 := by exact_mod_cast (show (1 : ℕ) < 2 from by omega)
  exact lt_of_le_of_lt (edist_le_one_iff_adj_or_eq.mpr (Or.inl h)) h1

theorem adj_of_mem_ball_two {c v : V} (h : v ∈ G.ball c 2) (hne : c ≠ v) :
    G.Adj c v := by
  simp only [mem_ball] at h
  have hle : G.edist c v ≤ 1 := by
    have hne_top : G.edist c v ≠ ⊤ := ne_top_of_lt h
    lift G.edist c v to ℕ using hne_top with d
    have : d < 2 := by exact_mod_cast h
    exact_mod_cast (show d ≤ 1 from by omega)
  exact (edist_le_one_iff_adj_or_eq.mp hle).resolve_right hne

/-- If `v ∈ ball c r₁` and `w ∈ ball v r₂`, then `w ∈ ball c (r₁ + r₂)`. -/
theorem mem_ball_of_mem_ball_of_mem_ball {c v w : V} {r₁ r₂ : ℕ∞}
    (hv : v ∈ G.ball c r₁) (hw : w ∈ G.ball v r₂) :
    w ∈ G.ball c (r₁ + r₂) := by
  simp only [mem_ball] at *
  have hw_ne : G.edist v w ≠ ⊤ := ne_top_of_lt hw
  calc G.edist c w
    ≤ G.edist c v + G.edist v w := G.edist_triangle
    _ < r₁ + G.edist v w := (ENat.add_lt_add_iff_right hw_ne).mpr hv
    _ ≤ r₁ + r₂ := by gcongr

end SimpleGraph
