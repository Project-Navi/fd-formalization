/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
/-
Aristotle Batch 3C — Gadget adjacency chain

Target: constructive adjacency chain through the short path of a
replacement gadget. This is the key building block for
`flowerGraph'_walk_hubs` (upper bound: walk of length u^g between hubs).

The witness is `edgeSrc(g+1, (parent, .inl ⟨i, _⟩))` for each i < u,
plus `embed(edgeTgt g parent)` at position u. Adjacency follows from
`short_path_consecutive_adj` and endpoint matching from
`short_tgt_eq_succ_src`, `short_first_eq_embed_src`,
`short_last_eq_embed_tgt`.

Safe target:
  - gadget_adj_chain: existence of u+1 vertex sequence with adjacency
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Metric

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

/-! ## Proved helpers (from FlowerConstruction.lean) -/

def flowerAdj' (u v g : ℕ) (a b : FlowerVert u v g) : Prop :=
  ∃ e : FlowerEdge u v g,
    (a = edgeSrc u v g e ∧ b = edgeTgt u v g e) ∨
    (b = edgeSrc u v g e ∧ a = edgeTgt u v g e)

theorem resolve_localEdge_adj (u v g : ℕ) (parent : FlowerEdge u v g)
    (localE : LocalEdge u v) :
    flowerAdj' u v (g + 1)
      (edgeSrc u v (g + 1) (parent, localE))
      (edgeTgt u v (g + 1) (parent, localE)) :=
  ⟨(parent, localE), Or.inl ⟨rfl, rfl⟩⟩

theorem short_path_consecutive_adj (u v g : ℕ) (parent : FlowerEdge u v g)
    (i : Fin u) :
    flowerAdj' u v (g + 1)
      (edgeSrc u v (g + 1) (parent, .inl i))
      (edgeTgt u v (g + 1) (parent, .inl i)) :=
  resolve_localEdge_adj u v g parent (.inl i)

theorem short_tgt_eq_succ_src (u v g : ℕ) (parent : FlowerEdge u v g)
    (i : Fin u) (hi : i.val + 1 < u) :
    edgeTgt u v (g + 1) (parent, .inl i) =
    edgeSrc u v (g + 1) (parent, .inl ⟨i.val + 1, hi⟩) := by
  simp only [edgeTgt, edgeSrc, edgeEndpoints, localTgt, localSrc,
    dif_neg (show ¬(i.val + 1 = u) by omega)]

theorem short_first_eq_embed_src (u v g : ℕ) (hu : 1 < u)
    (parent : FlowerEdge u v g) :
    edgeSrc u v (g + 1) (parent, .inl ⟨0, by omega⟩) =
    FlowerVert.embed u v g (edgeSrc u v g parent) := by
  simp only [edgeSrc, edgeEndpoints, localSrc]

theorem short_last_eq_embed_tgt (u v g : ℕ) (hu : 1 < u)
    (parent : FlowerEdge u v g) :
    edgeTgt u v (g + 1) (parent, .inl ⟨u - 1, by omega⟩) =
    FlowerVert.embed u v g (edgeTgt u v g parent) := by
  simp only [edgeTgt, edgeEndpoints, localTgt,
    dif_pos (show (u - 1) + 1 = u by omega)]

/-! ## Target lemma -/

/-- There exists a chain of `u + 1` vertices through the short path of a
replacement gadget, where consecutive vertices are adjacent. The chain
starts at the embedded source and ends at the embedded target of the
parent edge.

The witness is:
- `vertices i = edgeSrc(g+1, (parent, .inl ⟨i, _⟩))` for `i < u`
- `vertices u = embed(edgeTgt g parent)`

Adjacency between `vertices i` and `vertices (i+1)`:
- For `i + 1 < u`: `edgeTgt(parent, .inl i) = edgeSrc(parent, .inl (i+1))`
  by `short_tgt_eq_succ_src`, and `short_path_consecutive_adj` gives adjacency.
- For `i + 1 = u` (last step): `edgeTgt(parent, .inl (u-1)) = embed(edgeTgt)`
  by `short_last_eq_embed_tgt`, and `short_path_consecutive_adj` gives adjacency. -/
theorem gadget_adj_chain (u v g : ℕ) (hu : 1 < u)
    (parent : FlowerEdge u v g) :
    ∃ (vertices : Fin (u + 1) → FlowerVert u v (g + 1)),
      vertices 0 = FlowerVert.embed u v g (edgeSrc u v g parent) ∧
      vertices ⟨u, Nat.lt_succ_of_le le_rfl⟩ =
        FlowerVert.embed u v g (edgeTgt u v g parent) ∧
      ∀ (i : Fin u), flowerAdj' u v (g + 1)
        (vertices i.castSucc) (vertices i.succ) := by
  sorry
