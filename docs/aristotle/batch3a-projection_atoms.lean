/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
/-
Aristotle Batch 3A — Projection micro-lemmas

Target: projection atoms for the lower bound (distance ≥ u^g) proof.
These show how edgeSrc/edgeTgt at gen g+1 project back to gen g,
feeding into `project_adj_or_eq` (adjacency preserved under projection).

Safe targets (case splits on localSrc/localTgt):
  - project_edgeSrc_succ: source endpoint always projects to parent source
  - project_edgeTgt_succ: target endpoint projects to parent source or target

Stretch target (combines the above with adjacency witness):
  - project_adj_or_eq: adjacent vertices project to equal or adjacent vertices
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

theorem resolve_src_eq_embed_edgeSrc (u v g : ℕ) (parent : FlowerEdge u v g)
    (localE : LocalEdge u v) (hs : localSrc u v localE = .src) :
    edgeSrc u v (g + 1) (parent, localE) =
      FlowerVert.embed u v g (edgeSrc u v g parent) := by
  simp only [edgeSrc, edgeEndpoints, hs]

theorem resolve_tgt_eq_embed_edgeTgt (u v g : ℕ) (parent : FlowerEdge u v g)
    (localE : LocalEdge u v) (ht : localTgt u v localE = .tgt) :
    edgeTgt u v (g + 1) (parent, localE) =
      FlowerVert.embed u v g (edgeTgt u v g parent) := by
  simp only [edgeTgt, edgeEndpoints, ht]

/-! ## Adjacency -/

def flowerAdj' (u v g : ℕ) (a b : FlowerVert u v g) : Prop :=
  ∃ e : FlowerEdge u v g,
    (a = edgeSrc u v g e ∧ b = edgeTgt u v g e) ∨
    (b = edgeSrc u v g e ∧ a = edgeTgt u v g e)

/-! ## Projection map -/

def FlowerVert.project (u v g : ℕ) : FlowerVert u v (g + 1) → FlowerVert u v g
  | .inl h => .inl h
  | .inr ⟨k, e, pos⟩ =>
    if h : k.val < g then
      .inr ⟨⟨k.val, h⟩, e, pos⟩
    else
      have hk : k.val = g := by omega
      edgeSrc u v g (hk ▸ e)

theorem FlowerVert.project_embed (u v g : ℕ) (x : FlowerVert u v g) :
    FlowerVert.project u v g (FlowerVert.embed u v g x) = x := by
  cases x with
  | inl _ => rfl
  | inr val =>
    obtain ⟨k, e, pos⟩ := val
    simp only [FlowerVert.embed, FlowerVert.project, Fin.val_castSucc, dif_pos k.isLt,
      Fin.eta]

theorem FlowerVert.project_hub0 (u v g : ℕ) :
    FlowerVert.project u v g (.hub0 u v (g + 1)) = .hub0 u v g := rfl

theorem FlowerVert.project_hub1 (u v g : ℕ) :
    FlowerVert.project u v g (.hub1 u v (g + 1)) = .hub1 u v g := rfl

theorem FlowerVert.project_new (u v g : ℕ) (parent : FlowerEdge u v g)
    (pos : Fin (u - 1) ⊕ Fin (v - 1)) :
    FlowerVert.project u v g
      (.inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, pos⟩) =
    edgeSrc u v g parent := by
  simp [FlowerVert.project, show ¬(g < g) from lt_irrefl g]

/-! ## Target lemmas -/

/-- Source endpoint of `(parent, localE)` at gen `g+1` always projects to the
source endpoint of `parent` at gen `g`. This holds because `localSrc` never
returns `.tgt` — it only returns `.src`, `.short`, or `.long`. In all cases,
projection recovers `edgeSrc g parent` (via `project_embed` for `.src`,
via `project_new` for `.short`/`.long`). -/
theorem project_edgeSrc_succ (u v g : ℕ) (parent : FlowerEdge u v g)
    (localE : LocalEdge u v) :
    FlowerVert.project u v g (edgeSrc u v (g + 1) (parent, localE)) =
      edgeSrc u v g parent := by
  sorry

/-- Target endpoint of `(parent, localE)` at gen `g+1` projects to either the
source or target endpoint of `parent` at gen `g`. When `localTgt = .tgt`
(the last edge in the path), it projects to `edgeTgt g parent`. When
`localTgt = .short` or `.long` (intermediate edge), it projects to
`edgeSrc g parent`. -/
theorem project_edgeTgt_succ (u v g : ℕ) (parent : FlowerEdge u v g)
    (localE : LocalEdge u v) :
    FlowerVert.project u v g (edgeTgt u v (g + 1) (parent, localE)) =
      edgeSrc u v g parent ∨
    FlowerVert.project u v g (edgeTgt u v (g + 1) (parent, localE)) =
      edgeTgt u v g parent := by
  sorry

/-- **Stretch target.** Adjacent vertices at gen `g+1` project to either equal
or adjacent vertices at gen `g`. This is the key lemma for the lower bound
proof: each step of a walk either survives projection (contributing an edge
to the projected walk) or is absorbed (both endpoints collapse to the same
vertex).

Proof idea: adjacency means `∃ e = (parent, localE)` with matching endpoints.
By `project_edgeSrc_succ`, the source always projects to `edgeSrc g parent`.
By `project_edgeTgt_succ`, the target projects to `edgeSrc` or `edgeTgt` of
parent. If both project to `edgeSrc`, they're equal (`Or.inl`). If they
project to `edgeSrc` and `edgeTgt`, they're adjacent via parent (`Or.inr`). -/
theorem project_adj_or_eq (u v g : ℕ)
    (a b : FlowerVert u v (g + 1))
    (hab : flowerAdj' u v (g + 1) a b) :
    FlowerVert.project u v g a = FlowerVert.project u v g b ∨
    flowerAdj' u v g
      (FlowerVert.project u v g a)
      (FlowerVert.project u v g b) := by
  sorry
