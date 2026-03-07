/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
/-
Aristotle Batch 2A — Leaf: flowerVert_card
Target: Fintype.card (FlowerVert u v g) = flowerVertCount u v g
Strategy: induction on g, decompose card of Sum/Sigma/Prod types,
          use flowerEdge_card and flowerEdgeCount_eq_pow as bridges.

Helper lemmas provided to guide decomposition:
  - gadgetInternalCount: card (Fin (u-1) ⊕ Fin (v-1)) = u + v - 2
  - flowerVert_card_zero: base case
  - flowerVert_card_succ: inductive step
-/
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! ## Upstream definitions (from FlowerCounts.lean) -/

def flowerEdgeCount (u v : ℕ) : ℕ → ℕ
  | 0 => 1
  | g + 1 => (u + v) * flowerEdgeCount u v g

@[simp]
theorem flowerEdgeCount_zero (u v : ℕ) : flowerEdgeCount u v 0 = 1 := rfl

@[simp]
theorem flowerEdgeCount_succ (u v g : ℕ) :
    flowerEdgeCount u v (g + 1) = (u + v) * flowerEdgeCount u v g := rfl

theorem flowerEdgeCount_eq_pow (u v g : ℕ) :
    flowerEdgeCount u v g = (u + v) ^ g := by
  induction g with
  | zero => simp
  | succ g ih => rw [flowerEdgeCount_succ, ih, pow_succ, mul_comm]

def flowerVertCount (u v : ℕ) : ℕ → ℕ
  | 0 => 2
  | g + 1 => flowerVertCount u v g + (u + v - 2) * flowerEdgeCount u v g

@[simp]
theorem flowerVertCount_zero (u v : ℕ) : flowerVertCount u v 0 = 2 := rfl

@[simp]
theorem flowerVertCount_succ (u v g : ℕ) :
    flowerVertCount u v (g + 1) =
    flowerVertCount u v g + (u + v - 2) * flowerEdgeCount u v g := rfl

/-! ## Construction types (from FlowerConstruction.lean) -/

def FlowerEdge (u v : ℕ) : ℕ → Type
  | 0     => Unit
  | g + 1 => FlowerEdge u v g × (Fin u ⊕ Fin v)

instance instFintypeFlowerEdge (u v g : ℕ) : Fintype (FlowerEdge u v g) := by
  induction g with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ g ih => exact inferInstanceAs (Fintype (_ × _))

theorem flowerEdge_card (u v g : ℕ) :
    Fintype.card (FlowerEdge u v g) = (u + v) ^ g := by
  induction g with
  | zero => simp [FlowerEdge]
  | succ g ih =>
    simp only [FlowerEdge, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, ih, pow_succ,
      mul_comm]

def FlowerVert (u v : ℕ) (g : ℕ) : Type :=
  Fin 2 ⊕ Σ (k : Fin g), FlowerEdge u v k.val × (Fin (u - 1) ⊕ Fin (v - 1))

instance instFintypeFlowerVert (u v g : ℕ) : Fintype (FlowerVert u v g) := by
  unfold FlowerVert; infer_instance

/-! ## Helper lemmas -/

/-- Internal vertex count per gadget: (u-1) + (v-1) = u + v - 2. -/
theorem gadgetInternalCount (u v : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    Fintype.card (Fin (u - 1) ⊕ Fin (v - 1)) = u + v - 2 := by
  sorry

/-- Base case: FlowerVert at gen 0 has 2 vertices (just the hubs). -/
theorem flowerVert_card_zero (u v : ℕ) :
    Fintype.card (FlowerVert u v 0) = 2 := by
  sorry

/-- Inductive step: each generation adds (u+v-2) internal vertices per edge. -/
theorem flowerVert_card_succ (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v)
    (ih : Fintype.card (FlowerVert u v g) = flowerVertCount u v g) :
    Fintype.card (FlowerVert u v (g + 1)) = flowerVertCount u v (g + 1) := by
  sorry

/-! ## Target theorem -/

/-- Vertex count matches the arithmetic recurrence. -/
theorem flowerVert_card (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    Fintype.card (FlowerVert u v g) = flowerVertCount u v g := by
  sorry
