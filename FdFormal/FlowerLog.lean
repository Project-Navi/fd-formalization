/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.FlowerCounts
import FdFormal.FlowerDiameter
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Flower Log Lemmas

Reusable log identities and squeeze-sandwich bounds for the (u,v)-flower
model. These extract calculations that were previously inlined in
`FlowerDimension.lean` into standalone lemmas.

## Main statements

- `log_flowerHubDist_eq` — `log L_g = g * log u`
- `log_flowerEdgeCount_eq` — `log E_g = g * log(u + v)`
- `log_flowerVertCount_residual_lower` — residual lower bound for squeeze
- `log_flowerVertCount_residual_upper` — residual upper bound for squeeze

## References

- [Rozenfeld2007] §2, vertex count and hub-distance formulas used in bounds.

## Tags

flower graph, logarithm, squeeze bounds
-/

open Real

section FlowerLog

variable (u v g : ℕ)

/-! ### Log identities -/

/-- `log(L_g) = g * log(u)`: hub distance log scales linearly in `g`. -/
theorem log_flowerHubDist_eq :
    log (↑(flowerHubDist u v g) : ℝ) = ↑g * log (↑u : ℝ) := by
  rw [← log_pow, ← Nat.cast_pow, flowerHubDist_eq_pow]

/-- `log(E_g) = g * log(u + v)`: edge count log scales linearly in `g`. -/
theorem log_flowerEdgeCount_eq :
    log (↑(flowerEdgeCount u v g) : ℝ) = ↑g * log (↑(u + v) : ℝ) := by
  rw [← log_pow, ← Nat.cast_pow, flowerEdgeCount_eq_pow]

/-! ### Squeeze-sandwich bounds

The residual `log N_g - g * log(u + v)` is bounded between `log((w-2)/(w-1))`
and `log 2`. Dividing by `g * log u` and squeezing to zero gives the
log-ratio limit in `FlowerDimension`. -/

variable (hu : 1 < u) (huv : u ≤ v)
include hu huv

/-- Lower bound on the squeeze residual:
`log((w-2)/(w-1)) ≤ log N_g - g * log(u + v)`. -/
theorem log_flowerVertCount_residual_lower :
    log ((↑(u + v) - 2 : ℝ) / (↑(u + v) - 1)) ≤
    log ↑(flowerVertCount u v g) - ↑g * log (↑(u + v) : ℝ) := by
  have hw_pos : (0 : ℝ) < ↑(u + v) := Nat.cast_pos.mpr (by omega)
  have hw1 : (0 : ℝ) < ↑(u + v) - 1 :=
    sub_pos.mpr (by exact_mod_cast (show 1 < u + v by omega))
  have hc : (0 : ℝ) < (↑(u + v) - 2) / (↑(u + v) - 1) :=
    div_pos (sub_pos.mpr (by exact_mod_cast (show 2 < u + v by omega))) hw1
  -- From ℕ bound: (w-2)·w^g ≤ (w-1)·N_g → (w-2)/(w-1)·w^g ≤ N_g
  have h_ge : (↑(u + v) - 2) / (↑(u + v) - 1) * (↑(u + v) : ℝ) ^ g ≤
      ↑(flowerVertCount u v g) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hw1]
    have h_cast := Nat.cast_le (α := ℝ) |>.mpr (flowerVertCount_lower u v g hu huv)
    simp only [Nat.cast_mul, Nat.cast_pow] at h_cast
    rw [Nat.cast_sub (by omega : 2 ≤ u + v),
        Nat.cast_sub (by omega : 1 ≤ u + v)] at h_cast
    simp only [Nat.cast_ofNat, Nat.cast_one] at h_cast
    linarith [mul_comm (↑(u + v) - 1 : ℝ) (↑(flowerVertCount u v g) : ℝ)]
  have h_log := log_le_log (mul_pos hc (pow_pos hw_pos g)) h_ge
  rw [log_mul (ne_of_gt hc) (ne_of_gt (pow_pos hw_pos g)), log_pow] at h_log
  linarith

/-- Upper bound on the squeeze residual:
`log N_g - g * log(u + v) ≤ log 2`. -/
theorem log_flowerVertCount_residual_upper :
    log (↑(flowerVertCount u v g) : ℝ) - ↑g * log (↑(u + v) : ℝ) ≤
    log 2 := by
  have hw_pos : (0 : ℝ) < ↑(u + v) := Nat.cast_pos.mpr (by omega)
  have hN_pos : (0 : ℝ) < ↑(flowerVertCount u v g) :=
    Nat.cast_pos.mpr (flowerVertCount_pos u v g)
  -- From ℕ bound: (w-1)·N_g ≤ 2·(w-1)·w^g → N_g ≤ 2·w^g
  have h_le : (↑(flowerVertCount u v g) : ℝ) ≤ 2 * (↑(u + v) : ℝ) ^ g := by
    have : flowerVertCount u v g ≤ 2 * (u + v) ^ g :=
      Nat.le_of_mul_le_mul_left
        (by nlinarith [flowerVertCount_upper u v g hu huv])
        (by omega : 0 < u + v - 1)
    exact_mod_cast this
  have h_log := log_le_log hN_pos h_le
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt (pow_pos hw_pos g)), log_pow] at h_log
  linarith

end FlowerLog
