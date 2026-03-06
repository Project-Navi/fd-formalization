/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.FlowerCounts
import FdFormal.FlowerDiameter
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fractal Dimension of (u,v)-Flower Graphs

The fractal dimension of the (u,v)-flower family (for `1 < u`, `u ≤ v`)
is `d_B = Real.log (u + v) / Real.log u`.

The proof uses Route B (squeeze): two-sided bounds on `N_g` in terms
of `(u+v)^g`, combined with `L_g = u^g`, yield the log-ratio limit.

## Main statements

- `flowerDimension` — `Filter.Tendsto (fun g ↦ log N_g / log L_g)
    atTop (nhds (log w / log u))`

## References

- [Rozenfeld2007] Theorem 1, fractal dimension formula.

## Tags

fractal dimension, flower graph, box-counting dimension, squeeze theorem
-/

open Real Filter Topology

/-! ### ℝ bounds (multiplicative form, cast from ℕ) -/

/-- Lower bound in `ℝ`: `(w-2) * w^g ≤ (w-1) * N_g`. -/
theorem flowerVertCount_lower_real (u v g : ℕ) (hu : 1 < u)
    (huv : u ≤ v) :
    (↑(u + v) - 2 : ℝ) * (↑(u + v) : ℝ) ^ g ≤
    (↑(u + v) - 1 : ℝ) * (↑(flowerVertCount u v g) : ℝ) := by
  have h := flowerVertCount_lower u v g hu huv
  have h_cast := Nat.cast_le (α := ℝ) |>.mpr h
  simp only [Nat.cast_mul, Nat.cast_pow] at h_cast
  rw [Nat.cast_sub (by omega : 2 ≤ u + v),
      Nat.cast_sub (by omega : 1 ≤ u + v)] at h_cast
  exact_mod_cast h_cast

/-- Upper bound in `ℝ`: `(w-1) * N_g ≤ 2 * (w-1) * w^g`. -/
theorem flowerVertCount_upper_real (u v g : ℕ) (hu : 1 < u)
    (huv : u ≤ v) :
    (↑(u + v) - 1 : ℝ) * (↑(flowerVertCount u v g) : ℝ) ≤
    2 * (↑(u + v) - 1 : ℝ) * (↑(u + v) : ℝ) ^ g := by
  have h := flowerVertCount_upper u v g hu huv
  have h_cast := Nat.cast_le (α := ℝ) |>.mpr h
  simp only [Nat.cast_mul, Nat.cast_pow] at h_cast
  rw [Nat.cast_sub (by omega : 1 ≤ u + v)] at h_cast
  exact_mod_cast h_cast

/-! ### Divided-form ℝ bounds -/

/-- `(w-2)/(w-1) * w^g ≤ N_g` in `ℝ`. -/
theorem flowerVertCount_ge_real (u v g : ℕ) (hu : 1 < u)
    (huv : u ≤ v) :
    (↑(u + v) - 2) / (↑(u + v) - 1) * (↑(u + v) : ℝ) ^ g ≤
    ↑(flowerVertCount u v g) := by
  have hw1 : (0 : ℝ) < ↑(u + v) - 1 := by
    have : (1 : ℝ) < ↑(u + v) := by
      exact_mod_cast (show 1 < u + v from by omega)
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hw1]
  have h := flowerVertCount_lower_real u v g hu huv
  linarith [mul_comm (↑(u + v) - 1 : ℝ) (↑(flowerVertCount u v g) : ℝ)]

/-- `N_g ≤ 2 * w^g` in `ℝ`. -/
theorem flowerVertCount_le_real (u v g : ℕ) (hu : 1 < u)
    (huv : u ≤ v) :
    (↑(flowerVertCount u v g) : ℝ) ≤ 2 * (↑(u + v) : ℝ) ^ g := by
  have hw1 : (0 : ℝ) < ↑(u + v) - 1 := by
    have : (1 : ℝ) < ↑(u + v) := by
      exact_mod_cast (show 1 < u + v from by omega)
    linarith
  have h := flowerVertCount_upper_real u v g hu huv
  rw [show (2 : ℝ) * (↑(u + v) - 1) * (↑(u + v) : ℝ) ^ g =
      (↑(u + v) - 1) * (2 * (↑(u + v) : ℝ) ^ g) from by ring] at h
  exact (mul_le_mul_iff_right₀ hw1).mp h

/-! ### The headline theorem -/

/-- **Fractal dimension of the (u,v)-flower.**
The ratio `log |V_g| / log (hub distance)` tends to
`log(u + v) / log(u)` as generation `g → ∞`. -/
theorem flowerDimension (u v : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    Tendsto
      (fun g : ℕ ↦
        log ↑(flowerVertCount u v g) /
        log ↑(flowerHubDist u v g))
      atTop
      (nhds (log ↑(u + v) / log ↑u)) := by
  -- Positivity
  have hlogu : 0 < log (↑u : ℝ) :=
    log_pos (by exact_mod_cast hu)
  have hlogw : 0 < log (↑(u + v) : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < u + v from by omega))
  have hw_pos : (0 : ℝ) < ↑(u + v) :=
    Nat.cast_pos.mpr (by omega)
  have hN_pos : ∀ g, (0 : ℝ) < ↑(flowerVertCount u v g) :=
    fun g ↦ Nat.cast_pos.mpr (flowerVertCount_pos u v g)
  -- Step 1: log(L_g) = g * log(u) via log_pow
  have h_log_hub : ∀ g : ℕ,
      log (↑(flowerHubDist u v g) : ℝ) = ↑g * log (↑u : ℝ) := by
    intro g
    rw [show (↑(flowerHubDist u v g) : ℝ) = (↑u : ℝ) ^ g from by
      simp [flowerHubDist_eq_pow, Nat.cast_pow]]
    exact log_pow (↑u) g
  -- Step 2: Suffices with g * log(u) in denominator
  suffices h : Tendsto
      (fun g : ℕ ↦ log ↑(flowerVertCount u v g) / (↑g * log (↑u : ℝ)))
      atTop (nhds (log ↑(u + v) / log ↑u)) by
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with g hg
    rw [h_log_hub]
  -- Step 3: Decompose ratio = residual + constant
  -- log(N_g)/(g*log u) = [log(N_g) - g*log w]/(g*log u) + log w/log u
  have h_decomp : ∀ g : ℕ, 0 < (↑g : ℝ) →
      log ↑(flowerVertCount u v g) / (↑g * log (↑u : ℝ)) =
      (log ↑(flowerVertCount u v g) - ↑g * log ↑(u + v)) /
        (↑g * log (↑u : ℝ)) +
      log ↑(u + v) / log (↑u : ℝ) := by
    intro g hg
    have hg_ne : (↑g : ℝ) ≠ 0 := ne_of_gt hg
    have hlogu_ne : log (↑u : ℝ) ≠ 0 := ne_of_gt hlogu
    field_simp
    ring
  -- Step 4: Show residual → 0
  -- The residual is bounded between log(c₁)/(g*log u) and log(2)/(g*log u)
  -- where c₁ = (w-2)/(w-1) > 0
  set c₁ := (↑(u + v) - 2 : ℝ) / (↑(u + v) - 1) with hc₁_def
  have hc₁_pos : 0 < c₁ := by
    apply div_pos
    · have : (2 : ℝ) < ↑(u + v) := by
        exact_mod_cast (show 2 < u + v from by omega)
      linarith
    · have : (1 : ℝ) < ↑(u + v) := by
        exact_mod_cast (show 1 < u + v from by omega)
      linarith
  -- g * log(u) → ∞
  have h_denom : Tendsto (fun g : ℕ ↦ (↑g : ℝ) * log (↑u : ℝ))
      atTop atTop :=
    Tendsto.atTop_mul_const hlogu (tendsto_natCast_atTop_atTop (R := ℝ))
  -- Lower bound: log(c₁) ≤ log(N_g) - g * log(w)
  have h_res_lower : ∀ᶠ g in atTop,
      log c₁ / (↑g * log (↑u : ℝ)) ≤
      (log ↑(flowerVertCount u v g) - ↑g * log ↑(u + v)) /
        (↑g * log (↑u : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with g hg
    have hg_pos : (0 : ℝ) < ↑g := Nat.cast_pos.mpr hg
    rw [div_le_div_iff_of_pos_right (mul_pos hg_pos hlogu)]
    have h_bound := flowerVertCount_ge_real u v g hu huv
    have h_cw_pos : 0 < c₁ * (↑(u + v) : ℝ) ^ g :=
      mul_pos hc₁_pos (pow_pos hw_pos g)
    have h_log := log_le_log h_cw_pos h_bound
    rw [log_mul (ne_of_gt hc₁_pos) (ne_of_gt (pow_pos hw_pos g)),
        log_pow] at h_log
    linarith
  -- Upper bound: log(N_g) - g * log(w) ≤ log(2)
  have h_res_upper : ∀ᶠ g in atTop,
      (log ↑(flowerVertCount u v g) - ↑g * log ↑(u + v)) /
        (↑g * log (↑u : ℝ)) ≤
      log 2 / (↑g * log (↑u : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with g hg
    have hg_pos : (0 : ℝ) < ↑g := Nat.cast_pos.mpr hg
    rw [div_le_div_iff_of_pos_right (mul_pos hg_pos hlogu)]
    have h_bound := flowerVertCount_le_real u v g hu huv
    have h_log := log_le_log (hN_pos g) h_bound
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (ne_of_gt (pow_pos hw_pos g)),
        log_pow] at h_log
    linarith
  -- Both bounds → 0
  have h_lo : Tendsto (fun g : ℕ ↦ log c₁ / (↑g * log (↑u : ℝ)))
      atTop (nhds 0) :=
    h_denom.const_div_atTop _
  have h_hi : Tendsto (fun g : ℕ ↦ log 2 / (↑g * log (↑u : ℝ)))
      atTop (nhds 0) :=
    h_denom.const_div_atTop _
  -- Squeeze: residual → 0
  have h_res : Tendsto
      (fun g : ℕ ↦
        (log ↑(flowerVertCount u v g) - ↑g * log ↑(u + v)) /
          (↑g * log (↑u : ℝ)))
      atTop (nhds 0) :=
    h_lo.squeeze' h_hi h_res_lower h_res_upper
  -- Step 5: residual + constant → 0 + constant = constant
  have h_sum := h_res.add
    (tendsto_const_nhds (x := log (↑(u + v) : ℝ) / log (↑u : ℝ)))
  rw [zero_add] at h_sum
  exact h_sum.congr' (by
    filter_upwards [eventually_gt_atTop 0] with g hg
    exact (h_decomp g (Nat.cast_pos.mpr hg)).symm)
