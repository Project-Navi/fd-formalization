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

The graph distance between vertices `i` and `j` in `pathGraph (n + 1)`
equals the absolute difference `|i - j|`. These lemmas fill a gap in
Mathlib's `pathGraph` API (which has adjacency and connectivity but no
distance results) and serve as building blocks for distance proofs in
recursive graph constructions.

Proof strategies discovered by Aristotle (Harmonic) automated proof search,
rewritten into human-owned form.

## Main definitions

None — this file provides only lemmas about existing Mathlib definitions.

## Main statements

- `SimpleGraph.pathGraph_edist` — `edist i j = |i.val - j.val|`
- `SimpleGraph.pathGraph_dist` — `dist i j = |i.val - j.val|`
- `SimpleGraph.pathGraph_dist_zero_last` — `dist 0 (Fin.last n) = n`
- `SimpleGraph.pathGraph_edist_zero_last` — `edist 0 (Fin.last n) = n`

## Implementation notes

The key step is constructing a walk of length `|i - j|` by induction on the
target vertex, then showing no shorter walk exists via a triangle-inequality
argument on `Fin.val`. The `edist` result follows by `le_antisymm` on `iInf`.

## References

None — fills a gap in Mathlib's `SimpleGraph.Hasse` / `SimpleGraph.Metric` API.

## Tags

path graph, graph distance, Hasse diagram
-/

namespace SimpleGraph

/-! ### Walk construction -/

/-- Walk from `0` to any vertex `i` in `pathGraph (n + 1)`, of length `i.val`. -/
private theorem pathGraph_walk_from_zero {n : ℕ} (i : Fin (n + 1)) :
    ∃ w : (pathGraph (n + 1)).Walk 0 i, w.length = i.val := by
  induction i using Fin.inductionOn with
  | zero => exact ⟨.nil, rfl⟩
  | succ i ih =>
    obtain ⟨w, hw⟩ := ih
    have hadj : (pathGraph (n + 1)).Adj i.castSucc i.succ := by
      rw [pathGraph_adj]; left; simp [Fin.val_succ, Fin.val_castSucc]
    exact ⟨w.append (.cons hadj .nil), by simp [hw]⟩

/-- There is a walk of length `n` from `0` to `Fin.last n` in `pathGraph (n + 1)`. -/
theorem pathGraph_exists_walk_zero_last (n : ℕ) :
    ∃ w : (pathGraph (n + 1)).Walk 0 (Fin.last n), w.length = n :=
  (pathGraph_walk_from_zero (Fin.last n)).imp fun _ h ↦ by simpa [Fin.val_last] using h

/-! ### Walk bounds -/

/-- Walk from `i` to `j` of length `j.val - i.val` when `i.val ≤ j.val`. -/
private theorem pathGraph_walk_le {n : ℕ} {i j : Fin (n + 1)} (hij : i.val ≤ j.val) :
    ∃ w : (pathGraph (n + 1)).Walk i j, w.length = j.val - i.val := by
  induction j using Fin.inductionOn with
  | zero =>
    have hi : i = 0 := by ext; exact Nat.le_zero.mp hij
    exact hi ▸ ⟨.nil, by simp⟩
  | succ j ih =>
    by_cases h : i.val ≤ j.val
    · obtain ⟨w, hw⟩ := ih h
      have hadj : (pathGraph (n + 1)).Adj j.castSucc j.succ := by
        rw [pathGraph_adj]; left; simp [Fin.val_succ, Fin.val_castSucc]
      exact ⟨w.append (.cons hadj .nil), by simp [hw]; omega⟩
    · have hval : j.succ.val = j.val + 1 := Fin.val_succ j
      have hi : i = j.succ := Fin.ext (by omega)
      subst hi; exact ⟨.nil, by simp⟩

/-- Any walk in `pathGraph` has length ≥ the index difference between endpoints.
Each step changes the index by exactly 1, so `|i - j|` steps are needed. -/
private theorem pathGraph_walk_length_ge {n : ℕ} {i j : Fin (n + 1)}
    (p : (pathGraph (n + 1)).Walk i j) :
    (if i.val ≤ j.val then j.val - i.val else i.val - j.val) ≤ p.length := by
  induction p with
  | nil => simp
  | @cons u v w hadj p ih =>
    have : u.val + 1 = v.val ∨ v.val + 1 = u.val := by
      rw [pathGraph_adj] at hadj; exact hadj
    simp only [Walk.length_cons]
    split_ifs at ih ⊢ <;> omega

/-! ### Extended distance formula -/

/-- Extended distance in a path graph equals the absolute difference of indices. -/
theorem pathGraph_edist {n : ℕ} (i j : Fin (n + 1)) :
    (pathGraph (n + 1)).edist i j =
      ↑(if i.val ≤ j.val then j.val - i.val else i.val - j.val) := by
  -- Exhibit an optimal walk
  obtain ⟨w, hw⟩ : ∃ w : (pathGraph (n + 1)).Walk i j,
      w.length = if i.val ≤ j.val then j.val - i.val else i.val - j.val := by
    split_ifs with hij
    · exact pathGraph_walk_le hij
    · obtain ⟨w', hw'⟩ := pathGraph_walk_le (show j.val ≤ i.val by omega)
      exact ⟨w'.reverse, by rw [Walk.length_reverse, hw']⟩
  apply le_antisymm
  · -- Upper: edist ≤ walk length = target
    calc (pathGraph (n + 1)).edist i j
        ≤ ↑w.length := edist_le w
      _ = _ := by exact_mod_cast hw
  · -- Lower: target ≤ every walk length → target ≤ iInf
    simp only [edist]
    exact le_iInf fun w' ↦ by exact_mod_cast pathGraph_walk_length_ge w'

/-! ### Distance formula -/

/-- Distance in a path graph equals the absolute difference of indices. -/
theorem pathGraph_dist {n : ℕ} (i j : Fin (n + 1)) :
    (pathGraph (n + 1)).dist i j =
      if i.val ≤ j.val then j.val - i.val else i.val - j.val := by
  simp only [SimpleGraph.dist, pathGraph_edist, ENat.toNat_coe]

/-- Distance from `0` to `Fin.last n` in `pathGraph (n + 1)` is `n`. -/
theorem pathGraph_dist_zero_last (n : ℕ) :
    (pathGraph (n + 1)).dist (0 : Fin (n + 1)) (Fin.last n) = n := by
  rw [pathGraph_dist]; simp [Fin.val_last]

/-- The extended distance from `0` to `Fin.last n` in `pathGraph (n + 1)` is `n`. -/
theorem pathGraph_edist_zero_last (n : ℕ) :
    (pathGraph (n + 1)).edist (0 : Fin (n + 1)) (Fin.last n) = n := by
  rw [pathGraph_edist]; simp [Fin.val_last]

end SimpleGraph
