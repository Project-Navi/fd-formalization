/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b8544192-9594-4568-b272-99d847cddff9

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem flowerVertCount_pos (u v g : ℕ) :
    0 < flowerVertCount u v g

- theorem flowerVertCount_two_le (u v g : ℕ) :
    2 ≤ flowerVertCount u v g

- theorem hub0_ne_hub1 (u v g : ℕ) : hub0 u v g ≠ hub1 u v g
-/

/-
Sorry-stubbed version for Aristotle independent verification.
Original: FdFormal/FlowerGraph.lean
-/
import Mathlib.Tactic


set_option relaxedAutoImplicit false

set_option autoImplicit false

-- Inline the dependencies from FlowerCounts
def flowerEdgeCount (u v : ℕ) : ℕ → ℕ
  | 0 => 1
  | g + 1 => (u + v) * flowerEdgeCount u v g

def flowerVertCount (u v : ℕ) : ℕ → ℕ
  | 0 => 2
  | g + 1 => flowerVertCount u v g + (u + v - 2) * flowerEdgeCount u v g

theorem flowerVertCount_pos (u v g : ℕ) :
    0 < flowerVertCount u v g := by
  -- We proceed by induction on $g$.
  induction' g with g ih;
  · exact Nat.zero_lt_succ _;
  · -- By definition of flowerVertCount, we have flowerVertCount u v (g + 1) = flowerVertCount u v g + (u + v - 2) * flowerEdgeCount u v g.
    have h_def : flowerVertCount u v (g + 1) = flowerVertCount u v g + (u + v - 2) * flowerEdgeCount u v g := by
      rfl;
    -- Since both terms in the sum are positive, their sum must also be positive.
    simp [h_def, ih]

theorem flowerVertCount_two_le (u v g : ℕ) :
    2 ≤ flowerVertCount u v g := by
  -- We proceed by induction on $g$.
  induction' g with g ih;
  · exact Nat.le_refl _;
  · -- By definition of flowerVertCount, we have flowerVertCount u v (g + 1) = flowerVertCount u v g + (u + v - 2) * flowerEdgeCount u v g.
    have h_def : flowerVertCount u v (g + 1) = flowerVertCount u v g + (u + v - 2) * flowerEdgeCount u v g := by
      rfl;
    grind

def hub0 (u v g : ℕ) : Fin (flowerVertCount u v g) :=
  ⟨0, flowerVertCount_pos u v g⟩

def hub1 (u v g : ℕ) : Fin (flowerVertCount u v g) :=
  ⟨1, flowerVertCount_two_le u v g⟩

theorem hub0_ne_hub1 (u v g : ℕ) : hub0 u v g ≠ hub1 u v g := by
  -- Since 0 and 1 are distinct natural numbers, their corresponding Fin elements are also distinct.
  simp [hub0, hub1]
