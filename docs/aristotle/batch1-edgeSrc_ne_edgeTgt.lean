/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
/-
Aristotle Batch 1 — Leaf: edgeSrc_ne_edgeTgt
Target: Source ≠ target for every edge in the flower construction.
Strategy: induction on g, case analysis on local edge positions.
Base case: hub0 ≠ hub1. Step: gadget resolution preserves distinctness.
-/
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! ## Layer 0: Local replacement gadget -/

inductive GadgetPos (u v : ℕ)
  | src
  | tgt
  | short (i : Fin (u - 1))
  | long  (j : Fin (v - 1))

abbrev LocalEdge (u v : ℕ) := Fin u ⊕ Fin v

def localSrc (u v : ℕ) : LocalEdge u v → GadgetPos u v
  | .inl ⟨0, _⟩     => .src
  | .inl ⟨i + 1, h⟩ => .short ⟨i, by omega⟩
  | .inr ⟨0, _⟩     => .src
  | .inr ⟨j + 1, h⟩ => .long ⟨j, by omega⟩

def localTgt (u v : ℕ) : LocalEdge u v → GadgetPos u v
  | .inl i => if h : i.val + 1 = u then .tgt else .short ⟨i.val, by omega⟩
  | .inr j => if h : j.val + 1 = v then .tgt else .long ⟨j.val, by omega⟩

/-! ## Layer 1: Types -/

def FlowerEdge (u v : ℕ) : ℕ → Type
  | 0     => Unit
  | g + 1 => FlowerEdge u v g × LocalEdge u v

instance instFintypeFlowerEdge (u v g : ℕ) : Fintype (FlowerEdge u v g) := by
  induction g with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ g ih => exact inferInstanceAs (Fintype (_ × _))

def FlowerVert (u v : ℕ) (g : ℕ) : Type :=
  Fin 2 ⊕ Σ (k : Fin g), FlowerEdge u v k.val × (Fin (u - 1) ⊕ Fin (v - 1))

def FlowerVert.hub0 (u v g : ℕ) : FlowerVert u v g := .inl 0
def FlowerVert.hub1 (u v g : ℕ) : FlowerVert u v g := .inl 1

def FlowerVert.embed (u v g : ℕ) : FlowerVert u v g → FlowerVert u v (g + 1)
  | .inl h => .inl h
  | .inr ⟨k, e, pos⟩ => .inr ⟨k.castSucc, e, pos⟩

/-! ## Layer 2: Edge endpoints -/

def edgeEndpoints (u v : ℕ) :
    (g : ℕ) → FlowerEdge u v g → FlowerVert u v g × FlowerVert u v g
  | 0, () => (.hub0 u v 0, .hub1 u v 0)
  | g + 1, (parent, localE) =>
    let (pSrc, pTgt) := edgeEndpoints u v g parent
    let resolve : GadgetPos u v → FlowerVert u v (g + 1) := fun
      | .src     => FlowerVert.embed u v g pSrc
      | .tgt     => FlowerVert.embed u v g pTgt
      | .short i => .inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inl i⟩
      | .long j  => .inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inr j⟩
    (resolve (localSrc u v localE), resolve (localTgt u v localE))

def edgeSrc (u v g : ℕ) (e : FlowerEdge u v g) : FlowerVert u v g :=
  (edgeEndpoints u v g e).1

def edgeTgt (u v g : ℕ) (e : FlowerEdge u v g) : FlowerVert u v g :=
  (edgeEndpoints u v g e).2

/-! ## Helper: local source ≠ local target -/

/-- Within a single gadget, source and target positions are always distinct
when `1 < u`. This is the key inductive step helper. -/
theorem localSrc_ne_localTgt (u v : ℕ) (hu : 1 < u) (e : LocalEdge u v) :
    localSrc u v e ≠ localTgt u v e := by
  sorry

/-- Source ≠ target for every edge. -/
theorem edgeSrc_ne_edgeTgt (u v g : ℕ) (hu : 1 < u) (e : FlowerEdge u v g) :
    edgeSrc u v g e ≠ edgeTgt u v g e := by
  sorry
