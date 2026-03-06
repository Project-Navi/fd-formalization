/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Flower Graph Exact Counts

Exact formulas for the edge and vertex counts of (u,v)-flower graphs
at generation `g`. With `w = u + v`:

- **Edges:** `E_g = w^g`
- **Vertices:** `(w - 1) * N_g = (w - 2) * w^g + w`

These are proved by induction on `g` from the construction rule:
each edge is replaced by two parallel paths of lengths `u` and `v`,
contributing `(u - 1) + (v - 1) = w - 2` new internal vertices per
edge and multiplying the edge count by `w`.

The counting formulas are pure arithmetic recurrences and do not
depend on the graph representation.

## Main definitions

- `flowerEdgeCount` — number of edges at generation `g`
- `flowerVertCount` — number of vertices at generation `g`
- `flowerVertCountReal` — vertex count cast to `ℝ`

## Main statements

- `flowerEdgeCount_eq_pow` — `E_g = w^g`
- `flowerVertCount_eq` — `(w - 1) * N_g = (w - 2) * w^g + w`
- `flowerVertCount_lower` — `(w - 2) * w^g ≤ (w - 1) * N_g`
- `flowerVertCount_upper` — `(w - 1) * N_g ≤ 2 * (w - 1) * w^g`
- `flowerVertCount_pos` — `0 < N_g`

## References

- [Rozenfeld2007] §2, construction and counting formulas.

## Tags

flower graph, fractal, edge count, vertex count
-/

/-- Number of edges in the (u,v)-flower at generation `g`. -/
def flowerEdgeCount (u v : ℕ) : ℕ → ℕ
  | 0 => 1
  | g + 1 => (u + v) * flowerEdgeCount u v g

@[simp]
theorem flowerEdgeCount_zero (u v : ℕ) : flowerEdgeCount u v 0 = 1 := rfl

@[simp]
theorem flowerEdgeCount_succ (u v g : ℕ) :
    flowerEdgeCount u v (g + 1) = (u + v) * flowerEdgeCount u v g := rfl

/-- Number of vertices in the (u,v)-flower at generation `g`. -/
def flowerVertCount (u v : ℕ) : ℕ → ℕ
  | 0 => 2
  | g + 1 => flowerVertCount u v g + (u + v - 2) * flowerEdgeCount u v g

@[simp]
theorem flowerVertCount_zero (u v : ℕ) : flowerVertCount u v 0 = 2 := rfl

@[simp]
theorem flowerVertCount_succ (u v g : ℕ) :
    flowerVertCount u v (g + 1) =
    flowerVertCount u v g + (u + v - 2) * flowerEdgeCount u v g := rfl

/-! ### Edge count -/

/-- The edge count of the (u,v)-flower at generation `g` is `(u + v) ^ g`. -/
theorem flowerEdgeCount_eq_pow (u v g : ℕ) :
    flowerEdgeCount u v g = (u + v) ^ g := by
  induction g with
  | zero => simp
  | succ g ih => rw [flowerEdgeCount_succ, ih, pow_succ, mul_comm]

/-! ### Vertex count -/

/-- The vertex count satisfies `(w - 1) * N_g = (w - 2) * w^g + w`
where `w = u + v`. Multiplicative form avoids ℕ division. -/
theorem flowerVertCount_eq (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 1) * flowerVertCount u v g =
    (u + v - 2) * (u + v) ^ g + (u + v) := by
  induction g with
  | zero =>
    simp
    omega
  | succ g ih =>
    simp only [flowerVertCount_succ, flowerEdgeCount_eq_pow, pow_succ]
    have h1 : 1 ≤ u + v := by omega
    have h2 : 2 ≤ u + v := by omega
    zify [h1, h2] at ih ⊢
    nlinarith [ih]

/-- The vertex count is always positive (holds for all `u`, `v`). -/
theorem flowerVertCount_pos (u v g : ℕ) :
    0 < flowerVertCount u v g := by
  induction g with
  | zero => simp
  | succ g ih =>
    simp only [flowerVertCount_succ]
    omega

/-! ### Two-sided bounds for squeeze -/

/-- Lower bound: `(w - 2) * w^g ≤ (w - 1) * N_g`. -/
theorem flowerVertCount_lower (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 2) * (u + v) ^ g ≤
    (u + v - 1) * flowerVertCount u v g := by
  rw [flowerVertCount_eq u v g hu huv]
  exact le_add_of_nonneg_right (Nat.zero_le _)

/-- Upper bound: `(w - 1) * N_g ≤ 2 * (w - 1) * w^g`. -/
theorem flowerVertCount_upper (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 1) * flowerVertCount u v g ≤
    2 * (u + v - 1) * (u + v) ^ g := by
  rw [flowerVertCount_eq u v g hu huv]
  have h1 : 1 ≤ u + v := by omega
  have h2 : 2 ≤ u + v := by omega
  have h_pow : 1 ≤ (u + v) ^ g := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2] at h_pow ⊢
  nlinarith [h_pow]

/-! ### Real-valued wrappers -/

/-- Vertex count cast to `ℝ`. -/
noncomputable def flowerVertCountReal (u v : ℕ) (g : ℕ) : ℝ :=
  (flowerVertCount u v g : ℝ)

/-- The real-valued vertex count is positive. -/
theorem flowerVertCountReal_pos (u v g : ℕ) :
    0 < flowerVertCountReal u v g := by
  simp only [flowerVertCountReal]
  exact Nat.cast_pos.mpr (flowerVertCount_pos u v g)
