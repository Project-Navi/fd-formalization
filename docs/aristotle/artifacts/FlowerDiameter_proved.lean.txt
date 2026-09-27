/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3c3104ec-6801-40fa-b6f0-ee54416f39b6

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem flowerHubDist_eq_pow (u v g : ℕ) :
    flowerHubDist u v g = u ^ g

- theorem flowerHubDist_pos (u v g : ℕ) (hu : 1 < u) :
    0 < flowerHubDist u v g

- theorem flowerHubDistReal_pos (u v g : ℕ) (hu : 1 < u) :
    0 < flowerHubDistReal u v g
-/

/-
Sorry-stubbed version for Aristotle independent verification.
Original: FdFormal/FlowerDiameter.lean
-/
import Mathlib.Tactic


set_option relaxedAutoImplicit false

set_option autoImplicit false

def flowerHubDist (u v : ℕ) : ℕ → ℕ
  | 0 => 1
  | g + 1 => u * flowerHubDist u v g

@[simp]
theorem flowerHubDist_zero (u v : ℕ) : flowerHubDist u v 0 = 1 := rfl

@[simp]
theorem flowerHubDist_succ (u v g : ℕ) :
    flowerHubDist u v (g + 1) = u * flowerHubDist u v g := rfl

theorem flowerHubDist_eq_pow (u v g : ℕ) :
    flowerHubDist u v g = u ^ g := by
  -- We proceed by induction on $g$.
  induction' g with g ih;
  · -- By definition of flowerHubDist, we know that flowerHubDist u v 0 = 1.
    simp [flowerHubDist];
  · -- By definition of flowerHubDist, we have flowerHubDist u v (g + 1) = u * flowerHubDist u v g.
    rw [flowerHubDist_succ, ih]
    -- Using the properties of exponents, we can simplify this to u^(g + 1).
    ring

theorem flowerHubDist_pos (u v g : ℕ) (hu : 1 < u) :
    0 < flowerHubDist u v g := by
  -- Since $u > 1$, we have $u^g > 0$ for all $g \geq 0$.
  have h_pos : ∀ g, 0 < u^g := by
    -- Since $u > 1$, we have $u^g > 0$ for all $g \geq 0$ by the properties of exponents.
    intros g
    apply pow_pos
    exact Nat.zero_lt_of_lt hu
  exact h_pos g |> fun h => by simpa only [ flowerHubDist_eq_pow ] using h;

noncomputable def flowerHubDistReal (u v g : ℕ) : ℝ :=
  (flowerHubDist u v g : ℝ)

theorem flowerHubDistReal_pos (u v g : ℕ) (hu : 1 < u) :
    0 < flowerHubDistReal u v g := by
  -- Since $u > 1$, $u^g$ is positive for any $g$, hence $flowerHubDistReal u v g = u^g$ is also positive.
  have h_pos : 0 < flowerHubDist u v g := by
    -- Since $u > 1$, $u^g$ is positive for any $g$, hence $flowerHubDist u v g = u^g$ is also positive. Therefore, the inequality holds.
    apply flowerHubDist_pos u v g hu;
  -- Since $flowerHubDist u v g$ is positive, it must be non-zero.
  apply Nat.cast_pos.mpr h_pos
