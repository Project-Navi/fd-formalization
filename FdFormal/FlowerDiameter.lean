/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.FlowerCounts

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Flower Graph Hub-Distance Scaling

The hub-to-hub distance in the (u,v)-flower at generation `g` scales
as `u^g`. This is defined as a pure arithmetic recurrence encoding the
recursive construction rule: at each generation, the shortest path
between hubs follows the short side (`u` sub-edges), each of which is
itself a copy of the previous generation.

This file does not reference `SimpleGraph.dist` or `SimpleGraph.edist`.
The connection between `flowerHubDist` and a concrete graph metric is
a deferred bridge theorem (see `FlowerGraph.lean`).

## Main definitions

- `flowerHubDist` — hub-to-hub distance at generation `g`
- `flowerHubDistReal` — hub distance cast to `ℝ`

## Main statements

- `flowerHubDist_eq_pow` — `flowerHubDist u v g = u ^ g`
- `flowerHubDist_pos` — `0 < flowerHubDist u v g` when `1 < u`
- `flowerHubDistReal_pos` — positivity in `ℝ`

## References

- [Rozenfeld2007] §2, diameter analysis.

## Tags

flower graph, hub distance, diameter scaling, fractal
-/

/-- Hub-to-hub distance in the (u,v)-flower at generation `g`.
Defined by the recurrence: `D_0 = 1`, `D_{g+1} = u * D_g`.
Encodes the fact that the shortest hub-to-hub path follows `u`
copies of the previous generation's shortest path.
The `v` parameter is unused but kept for API uniformity with
`flowerEdgeCount u v g` and `flowerVertCount u v g`. -/
@[nolint unusedArguments]
def flowerHubDist (u v : ℕ) : ℕ → ℕ
  | 0 => 1
  | g + 1 => u * flowerHubDist u v g

@[simp]
theorem flowerHubDist_zero (u v : ℕ) : flowerHubDist u v 0 = 1 := rfl

@[simp]
theorem flowerHubDist_succ (u v g : ℕ) :
    flowerHubDist u v (g + 1) = u * flowerHubDist u v g := rfl

/-- The hub distance equals `u ^ g`. -/
theorem flowerHubDist_eq_pow (u v g : ℕ) :
    flowerHubDist u v g = u ^ g := by
  induction g with
  | zero => simp
  | succ g ih => rw [flowerHubDist_succ, ih, pow_succ, mul_comm]

/-- The hub distance is positive when `1 < u`. -/
theorem flowerHubDist_pos (u v g : ℕ) (hu : 1 < u) :
    0 < flowerHubDist u v g := by
  rw [flowerHubDist_eq_pow]
  positivity

/-! ### Real-valued wrapper -/

/-- Hub distance cast to `ℝ`. -/
noncomputable def flowerHubDistReal (u v g : ℕ) : ℝ :=
  (flowerHubDist u v g : ℝ)

/-- The real-valued hub distance is positive when `1 < u`. -/
theorem flowerHubDistReal_pos (u v g : ℕ) (hu : 1 < u) :
    0 < flowerHubDistReal u v g := by
  simp only [flowerHubDistReal]
  exact Nat.cast_pos.mpr (flowerHubDist_pos u v g hu)
