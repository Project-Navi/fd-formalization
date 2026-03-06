/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
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
  sorry

theorem flowerVertCount_eq (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 1) * flowerVertCount u v g =
    (u + v - 2) * (u + v) ^ g + (u + v) := by
  sorry

theorem flowerVertCount_pos (u v g : ℕ) :
    0 < flowerVertCount u v g := by
  sorry

theorem flowerVertCount_lower (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 2) * (u + v) ^ g ≤
    (u + v - 1) * flowerVertCount u v g := by
  sorry

theorem flowerVertCount_upper (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 1) * flowerVertCount u v g ≤
    2 * (u + v - 1) * (u + v) ^ g := by
  sorry

noncomputable def flowerVertCountReal (u v : ℕ) (g : ℕ) : ℝ :=
  (flowerVertCount u v g : ℝ)

theorem flowerVertCountReal_pos (u v g : ℕ) :
    0 < flowerVertCountReal u v g := by
  sorry
