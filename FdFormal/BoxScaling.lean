/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Basic

/-!
# Scaling lemma for box counts

Pure analysis, with no graphs: if a two-parameter count `N g ℓ` is antitone in the scale `ℓ`
and is within a constant factor of `b ^ (g - m)` at the scales `ℓ = u ^ m`, then along any
scales `ℓ_g` with `L_g / ℓ_g → ∞` (where `L_g` is comparable to `u ^ g`),
`log N g ℓ_g / log (L_g / ℓ_g) → log b / log u`.

## Main statements

- `exists_pow_le_lt` — every positive `ℓ` lies between consecutive powers of `u`
- `tendsto_log_count_div_log_scale` — the scaling limit

## Tags

box-counting, scaling, logarithm
-/

open Filter Real Topology

/-- Every positive `ℓ` lies between two consecutive powers of `u`. -/
theorem exists_pow_le_lt {u ℓ : ℕ} (hu : 1 < u) (hℓ : 0 < ℓ) :
    ∃ m, u ^ m ≤ ℓ ∧ ℓ < u ^ (m + 1) :=
  ⟨Nat.log u ℓ, Nat.pow_log_le_self u hℓ.ne', Nat.lt_pow_succ_log_self hu ℓ⟩

/-- An affine-over-affine function of `x` tends to the ratio of leading coefficients. -/
private lemma tendsto_affine_div_affine (A B C D : ℝ) (hC : C ≠ 0) :
    Tendsto (fun x : ℝ ↦ (x * A + B) / (x * C + D)) atTop (𝓝 (A / C)) := by
  have h0 := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have hnum : Tendsto (fun x : ℝ ↦ A + B * x⁻¹) atTop (𝓝 A) := by
    simpa using (h0.const_mul B).const_add A
  have hden : Tendsto (fun x : ℝ ↦ C + D * x⁻¹) atTop (𝓝 C) := by
    simpa using (h0.const_mul D).const_add C
  refine (hnum.div hden hC).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Pi.div_apply]
  field_simp

/-- **Scaling lemma.** A count `N g ℓ` that is antitone in `ℓ` and within the constant
factor `c` of `b ^ (g - m)` at `ℓ = u ^ m` has exponent `log b / log u` along every scale
sequence `ℓ_g` with `L_g / ℓ_g → ∞`, where `u ^ g ≤ L_g ≤ c * u ^ g`. -/
theorem tendsto_log_count_div_log_scale
    (u b c : ℕ) (hu : 1 < u) (hb : 1 < b) (hc : 0 < c)
    (N : ℕ → ℕ → ℕ)
    (hanti : ∀ g ℓ ℓ', 0 < ℓ → ℓ ≤ ℓ' → N g ℓ' ≤ N g ℓ)
    (hlow : ∀ g m, m ≤ g → b ^ (g - m) ≤ c * N g (u ^ m))
    (hup : ∀ g m, m ≤ g → N g (u ^ m) ≤ c * b ^ (g - m))
    (L : ℕ → ℕ) (hL : ∀ g, u ^ g ≤ L g ∧ L g ≤ c * u ^ g)
    (ℓ : ℕ → ℕ) (hℓ : ∀ g, 0 < ℓ g)
    (hscale : Tendsto (fun g ↦ (L g : ℝ) / ℓ g) atTop atTop) :
    Tendsto (fun g ↦ log (N g (ℓ g) : ℝ) / log ((L g : ℝ) / ℓ g)) atTop
      (𝓝 (log b / log u)) := by
  choose m hm1 hm2 using fun g ↦ exists_pow_le_lt hu (hℓ g)
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hu1 : (1 : ℝ) < u := by exact_mod_cast hu
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hlu : 0 < log (u : ℝ) := log_pos hu1
  have hlb : 0 < log (b : ℝ) := log_pos (by exact_mod_cast hb)
  set A := log (b : ℝ)
  set C := log (u : ℝ)
  set K := log (c : ℝ)
  -- eventually `m g + 2 ≤ g`
  have hev : ∀ᶠ g in atTop, m g + 2 ≤ g := by
    filter_upwards [hscale.eventually_gt_atTop ((c : ℝ) * u)] with g hg
    have hℓg : (0 : ℝ) < ℓ g := by exact_mod_cast hℓ g
    rw [lt_div_iff₀ hℓg] at hg
    have h1 : c * u * ℓ g < L g := by exact_mod_cast hg
    have h2 : c * u ^ (m g + 1) < c * u ^ g := by
      calc c * u ^ (m g + 1) = c * u * u ^ m g := by ring
        _ ≤ c * u * ℓ g := Nat.mul_le_mul_left _ (hm1 g)
        _ < L g := h1
        _ ≤ c * u ^ g := (hL g).2
    have h3 : u ^ (m g + 1) < u ^ g := Nat.lt_of_mul_lt_mul_left h2
    have := (Nat.pow_lt_pow_iff_right hu).1 h3
    omega
  -- key bounds, with `j = g - m g`
  have hbounds : ∀ᶠ g in atTop, 2 ≤ ((g - m g : ℕ) : ℝ) ∧
      ((g - m g : ℕ) - 1) * A - K ≤ log (N g (ℓ g) : ℝ) ∧
      log (N g (ℓ g) : ℝ) ≤ (g - m g : ℕ) * A + K ∧
      ((g - m g : ℕ) - 1) * C ≤ log ((L g : ℝ) / ℓ g) ∧
      log ((L g : ℝ) / ℓ g) ≤ (g - m g : ℕ) * C + K ∧
      0 ≤ log (N g (ℓ g) : ℝ) := by
    filter_upwards [hev] with g hg
    set j := g - m g with hj
    have hj2 : 2 ≤ j := by omega
    have hgj : g = j + m g := by omega
    have hℓg : (0 : ℝ) < ℓ g := by exact_mod_cast hℓ g
    -- counts
    have hNup : N g (ℓ g) ≤ c * b ^ j :=
      (hanti g _ _ (pow_pos (by omega) _) (hm1 g)).trans (hup g (m g) (by omega))
    have hNlow : b ^ (j - 1) ≤ c * N g (ℓ g) := by
      have := hlow g (m g + 1) (by omega)
      rw [show g - (m g + 1) = j - 1 by omega] at this
      exact this.trans (Nat.mul_le_mul_left _
        (hanti g _ _ (hℓ g) (hm2 g).le))
    have hNpos : 0 < N g (ℓ g) := by
      have : 0 < c * N g (ℓ g) := lt_of_lt_of_le (by positivity) hNlow
      exact Nat.pos_of_mul_pos_left this
    have hNpos' : (0 : ℝ) < N g (ℓ g) := by exact_mod_cast hNpos
    have hNupR : (N g (ℓ g) : ℝ) ≤ c * b ^ j := by exact_mod_cast hNup
    have hNlowR : (b : ℝ) ^ (j - 1) ≤ c * N g (ℓ g) := by exact_mod_cast hNlow
    have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    -- scales
    have hLup : L g ≤ c * u ^ j * ℓ g := by
      calc L g ≤ c * u ^ g := (hL g).2
        _ = c * u ^ j * u ^ m g := by
          rw [show u ^ g = u ^ j * u ^ m g by rw [← pow_add, ← hgj]]; ring
        _ ≤ c * u ^ j * ℓ g := Nat.mul_le_mul_left _ (hm1 g)
    have hLlow : u ^ (j - 1) * ℓ g ≤ L g := by
      calc u ^ (j - 1) * ℓ g ≤ u ^ (j - 1) * u ^ (m g + 1) :=
            Nat.mul_le_mul_left _ (hm2 g).le
        _ = u ^ g := by rw [← pow_add]; congr 1; omega
        _ ≤ L g := (hL g).1
    have hLupR : (L g : ℝ) / ℓ g ≤ c * u ^ j := by
      rw [div_le_iff₀ hℓg]; exact_mod_cast hLup
    have hLlowR : (u : ℝ) ^ (j - 1) ≤ (L g : ℝ) / ℓ g := by
      rw [le_div_iff₀ hℓg]; exact_mod_cast hLlow
    have hpow_pos : (0 : ℝ) < (u : ℝ) ^ (j - 1) := by positivity
    refine ⟨by exact_mod_cast hj2, ?_, ?_, ?_, ?_, ?_⟩
    · have := log_le_log (by positivity) hNlowR
      rw [log_pow, log_mul hc0.ne' hNpos'.ne', hcast] at this
      linarith
    · have := log_le_log hNpos' hNupR
      rw [log_mul hc0.ne' (by positivity), log_pow] at this
      linarith
    · have := log_le_log hpow_pos hLlowR
      rwa [log_pow, hcast] at this
    · have := log_le_log (lt_of_lt_of_le hpow_pos hLlowR) hLupR
      rw [log_mul hc0.ne' (by positivity), log_pow] at this
      linarith
    · exact log_nonneg (by exact_mod_cast hNpos)
  -- `j → ∞`
  have hj : Tendsto (fun g ↦ ((g - m g : ℕ) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun g ↦ (log ((L g : ℝ) / ℓ g) - K) / C) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-K) (tendsto_log_atTop.comp hscale)).atTop_div_const
        hlu
    refine tendsto_atTop_mono' _ ?_ h1
    filter_upwards [hbounds] with g hg
    rw [div_le_iff₀ hlu]
    linarith [hg.2.2.2.2.1]
  have hlo := (tendsto_affine_div_affine A (-A - K) C K hlu.ne').comp hj
  have hhi := (tendsto_affine_div_affine A K C (-C) hlu.ne').comp hj
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hbounds] with g ⟨h2, hN1, hN2, hS1, hS2, hN0⟩
    have hSpos : 0 < log ((L g : ℝ) / ℓ g) := by nlinarith
    simp only [Function.comp]
    exact div_le_div₀ hN0 (by linarith) hSpos (by linarith)
  · filter_upwards [hbounds] with g ⟨h2, hN1, hN2, hS1, hS2, hN0⟩
    have hSpos : 0 < ((g - m g : ℕ) - 1 : ℝ) * C := by nlinarith
    simp only [Function.comp]
    exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
