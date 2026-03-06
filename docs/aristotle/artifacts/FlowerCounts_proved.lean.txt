/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8ef69c4c-785d-45f2-a71e-c731ca8cf011

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem flowerEdgeCount_eq_pow (u v g : ℕ) :
    flowerEdgeCount u v g = (u + v) ^ g

- theorem flowerVertCount_eq (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 1) * flowerVertCount u v g =
    (u + v - 2) * (u + v) ^ g + (u + v)

- theorem flowerVertCount_pos (u v g : ℕ) :
    0 < flowerVertCount u v g

- theorem flowerVertCount_lower (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 2) * (u + v) ^ g ≤
    (u + v - 1) * flowerVertCount u v g

- theorem flowerVertCount_upper (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 1) * flowerVertCount u v g ≤
    2 * (u + v - 1) * (u + v) ^ g

- theorem flowerVertCountReal_pos (u v g : ℕ) :
    0 < flowerVertCountReal u v g
-/

/-
Sorry-stubbed version for Aristotle independent verification.
Original: FdFormal/FlowerCounts.lean
-/
import Mathlib.Tactic


set_option relaxedAutoImplicit false

set_option autoImplicit false

def flowerEdgeCount (u v : ℕ) : ℕ → ℕ
  | 0 => 1
  | g + 1 => (u + v) * flowerEdgeCount u v g

@[simp]
theorem flowerEdgeCount_zero (u v : ℕ) : flowerEdgeCount u v 0 = 1 := rfl

@[simp]
theorem flowerEdgeCount_succ (u v g : ℕ) :
    flowerEdgeCount u v (g + 1) = (u + v) * flowerEdgeCount u v g := rfl

def flowerVertCount (u v : ℕ) : ℕ → ℕ
  | 0 => 2
  | g + 1 => flowerVertCount u v g + (u + v - 2) * flowerEdgeCount u v g

@[simp]
theorem flowerVertCount_zero (u v : ℕ) : flowerVertCount u v 0 = 2 := rfl

@[simp]
theorem flowerVertCount_succ (u v g : ℕ) :
    flowerVertCount u v (g + 1) =
    flowerVertCount u v g + (u + v - 2) * flowerEdgeCount u v g := rfl

theorem flowerEdgeCount_eq_pow (u v g : ℕ) :
    flowerEdgeCount u v g = (u + v) ^ g := by
  -- We proceed by induction on $g$.
  induction' g with g ih;
  · -- By definition of flowerEdgeCount, we have flowerEdgeCount u v 0 = 1.
    simp [flowerEdgeCount];
  · -- By definition of flowerEdgeCount, we have flowerEdgeCount u v (g + 1) = (u + v) * flowerEdgeCount u v g.
    rw [flowerEdgeCount_succ, ih]
    ring

theorem flowerVertCount_eq (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 1) * flowerVertCount u v g =
    (u + v - 2) * (u + v) ^ g + (u + v) := by
  -- We proceed by induction on $g$.
  induction' g with g ih;
  · rcases u with ( _ | _ | u ) <;> rcases v with ( _ | _ | v ) <;> simp_all +arith +decide [ Nat.mul_succ ];
  · -- Substitute the induction hypothesis into the equation.
    have h_sub : (u + v - 1) * (flowerVertCount u v g + (u + v - 2) * (u + v)^g) = (u + v - 2) * (u + v)^(g + 1) + (u + v) := by
      cases k : u + v <;> simp_all +decide [ pow_succ' ] ; nlinarith;
    -- Substitute the definition of `flowerVertCount` into the goal.
    rw [flowerVertCount_succ];
    rwa [ flowerEdgeCount_eq_pow ]

theorem flowerVertCount_pos (u v g : ℕ) :
    0 < flowerVertCount u v g := by
  -- By definition of flowerVertCount, it is always positive since it is a sum of positive terms.
  induction' g with g ih generalizing u v;
  · -- The base case is when $g = 0$. We have $flowerVertCount u v 0 = 2$, which is clearly positive.
    simp [flowerVertCount];
  · -- Since both terms in the sum are positive, their sum is also positive.
    apply add_pos_of_pos_of_nonneg; exact ih u v; exact Nat.zero_le _

theorem flowerVertCount_lower (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 2) * (u + v) ^ g ≤
    (u + v - 1) * flowerVertCount u v g := by
  -- Substitute the expression for `flowerVertCount u v g` from `flowerVertCount_eq`.
  have h_subst : (u + v - 1) * flowerVertCount u v g = (u + v - 2) * (u + v)^g + (u + v) := by
    -- Apply the theorem flowerVertCount_eq with the given conditions.
    apply flowerVertCount_eq u v g hu huv;
  -- Since $(u + v)$ is positive, adding it to $(u + v - 2) * (u + v)^g$ will make the right side larger.
  rw [h_subst]
  apply le_add_of_nonneg_right
  apply Nat.zero_le

theorem flowerVertCount_upper (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 1) * flowerVertCount u v g ≤
    2 * (u + v - 1) * (u + v) ^ g := by
  -- Substitute the expression for `flowerVertCount u v g` from `flowerVertCount_eq`.
  have h_subst : flowerVertCount u v g = ((u + v - 2) * (u + v)^g + (u + v)) / (u + v - 1) := by
    exact Eq.symm ( Nat.div_eq_of_eq_mul_left ( Nat.sub_pos_of_lt ( by linarith ) ) ( by linarith [ flowerVertCount_eq u v g hu huv ] ) );
  -- Substitute h_subst into the inequality and simplify.
  rw [h_subst]
  have h_simp : ((u + v - 2) * (u + v)^g + (u + v)) ≤ 2 * (u + v - 1) * (u + v)^g := by
    -- Since $u + v \geq 4$, we have $(u + v)^g \geq 1$ for any $g \geq 0$.
    have h_ge_one : (u + v)^g ≥ 1 := by
      exact Nat.one_le_pow _ _ ( by linarith );
    nlinarith [ Nat.sub_add_cancel ( by linarith : 2 ≤ u + v ), Nat.sub_add_cancel ( by linarith : 1 ≤ u + v ) ];
  exact le_trans ( Nat.mul_div_le _ _ ) h_simp

noncomputable def flowerVertCountReal (u v : ℕ) (g : ℕ) : ℝ :=
  (flowerVertCount u v g : ℝ)

theorem flowerVertCountReal_pos (u v g : ℕ) :
    0 < flowerVertCountReal u v g := by
  -- Since flowerVertCount is a positive integer, converting it to a real number preserves positivity.
  apply Nat.cast_pos.mpr; exact flowerVertCount_pos u v g
