/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
/-
Aristotle Batch 1 — Leaf: flowerEdge_card
Target: Fintype.card (FlowerEdge u v g) = (u + v) ^ g
Strategy: induction on g, card Unit = 1, card (A × B) = card A * card B
-/
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- Edge index at generation `g`. -/
def FlowerEdge (u v : ℕ) : ℕ → Type
  | 0     => Unit
  | g + 1 => FlowerEdge u v g × (Fin u ⊕ Fin v)

instance instFintypeFlowerEdge (u v g : ℕ) : Fintype (FlowerEdge u v g) := by
  induction g with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ g ih => exact inferInstanceAs (Fintype (_ × _))

/-- Edge count matches the arithmetic formula. -/
theorem flowerEdge_card (u v g : ℕ) :
    Fintype.card (FlowerEdge u v g) = (u + v) ^ g := by
  sorry
