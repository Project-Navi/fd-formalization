/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.FlowerCounts
import FdFormal.FlowerDiameter
import FdFormal.FlowerGraph
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# (u,v)-Flower Graph Construction — SKETCH v2

**Status: Exploratory.** Design sketch for the F2 bridge, following
the structured-gadget approach. Proofs are stubbed with `sorry`.

## Main definitions

- `GadgetPos` — position within a replacement gadget (src, tgt, or internal)
- `LocalEdge` — edge within a replacement gadget (`Fin u ⊕ Fin v`)
- `FlowerEdge` — recursive edge index type
- `FlowerVert` — vertex type (hubs + sigma of internal vertices)
- `edgeEndpoints` — endpoint resolution via recursive gadget expansion
- `flowerGraph'` — the (u,v)-flower as a `SimpleGraph` on `FlowerVert`
- `FlowerVert.project` — projection map for lower bound proof

## Main statements

- `flowerGraph'_dist_hubs` — hub distance equals `u^g` (sorry stubs)
- `flowerGraph_dist_hubs` — F2 bridge on `Fin` (sorry stub)

## Implementation notes

Each edge is replaced by two parallel paths of lengths `u` and `v`.
Internal vertices are `Fin (u-1) ⊕ Fin (v-1)`. Edges at generation `g`
are `FlowerEdge u v g`, defined recursively (parent × local edge),
avoiding division/modular arithmetic on `Fin`. The projection map
collapses each gadget traversal to a single edge for the lower bound.

## Tags

flower graph, construction, sketch
-/

/-! ## Layer 0: Local replacement gadget -/

/-- Position within a replacement gadget: either a boundary point (source/target
of the replaced edge) or an internal vertex on one of the two paths. -/
inductive GadgetPos (u v : ℕ)
  | src   -- source endpoint of the replaced edge
  | tgt   -- target endpoint of the replaced edge
  | short (i : Fin (u - 1))  -- internal vertex on the short (length u) path
  | long  (j : Fin (v - 1))  -- internal vertex on the long (length v) path

/-- A local edge within a replacement gadget: either an edge on the short path
(`Sum.inl i` for `i : Fin u`) or on the long path (`Sum.inr j` for `j : Fin v`). -/
abbrev LocalEdge (u v : ℕ) := Fin u ⊕ Fin v

/-- Source of local edge `e` within the gadget.

Short path: `src → s₀ → s₁ → ... → s_{u-2} → tgt`
- Edge 0 starts at `src`
- Edge i+1 starts at `short ⟨i, _⟩`

Long path: analogous with `long`. -/
def localSrc (u v : ℕ) : LocalEdge u v → GadgetPos u v
  | .inl ⟨0, _⟩     => .src
  | .inl ⟨i + 1, h⟩ => .short ⟨i, by omega⟩
  | .inr ⟨0, _⟩     => .src
  | .inr ⟨j + 1, h⟩ => .long ⟨j, by omega⟩

/-- Target of local edge `e` within the gadget.

Short path: `src → s₀ → s₁ → ... → s_{u-2} → tgt`
- Edge u-1 ends at `tgt`
- Edge i (i < u-1) ends at `short ⟨i, _⟩`

Long path: analogous with `long`. -/
def localTgt (u v : ℕ) : LocalEdge u v → GadgetPos u v
  | .inl i => if h : i.val + 1 = u then .tgt else .short ⟨i.val, by omega⟩
  | .inr j => if h : j.val + 1 = v then .tgt else .long ⟨j.val, by omega⟩

/-! ## Layer 1: Structured types -/

/-- Edge index at generation `g`. Recursive: a gen g+1 edge is a gen g edge
(the parent being replaced) paired with a position in the replacement gadget. -/
def FlowerEdge (u v : ℕ) : ℕ → Type
  | 0     => Unit
  | g + 1 => FlowerEdge u v g × LocalEdge u v

instance instFintypeFlowerEdge (u v g : ℕ) : Fintype (FlowerEdge u v g) := by
  induction g with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ g ih => exact inferInstanceAs (Fintype (_ × _))

/-- Edge count matches the arithmetic formula. -/
theorem flowerEdge_card (u v g : ℕ) :
    Fintype.card (FlowerEdge u v g) = (u + v) ^ g := by
  induction g with
  | zero => simp [FlowerEdge]
  | succ g ih =>
    simp only [FlowerEdge, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, ih, pow_succ,
      mul_comm]

/-- Vertex type for the (u,v)-flower at generation `g`.

- `Sum.inl h` for `h : Fin 2`: hub vertices (present at all generations)
- `Sum.inr ⟨k, e, pos⟩`: internal vertex created when replacing edge `e`
  at generation `k`, at position `pos` within the replacement gadget.
  Here `pos : Fin (u-1) ⊕ Fin (v-1)` tells us which path and where. -/
def FlowerVert (u v : ℕ) (g : ℕ) : Type :=
  Fin 2 ⊕ Σ (k : Fin g), FlowerEdge u v k.val × (Fin (u - 1) ⊕ Fin (v - 1))

instance instFintypeFlowerVert (u v g : ℕ) : Fintype (FlowerVert u v g) := by
  unfold FlowerVert; infer_instance

/-- Hub 0. -/
def FlowerVert.hub0 (u v g : ℕ) : FlowerVert u v g := .inl 0

/-- Hub 1. -/
def FlowerVert.hub1 (u v g : ℕ) : FlowerVert u v g := .inl 1

theorem FlowerVert.hub0_ne_hub1 (u v g : ℕ) :
    FlowerVert.hub0 u v g ≠ FlowerVert.hub1 u v g := by
  unfold hub0 hub1; exact Sum.inl_injective.ne (by decide)

/-- Embed a vertex from generation `g` into generation `g+1`.
Hubs stay hubs. Internal vertices keep their identity (the generation
index `k : Fin g` lifts to `Fin (g+1)` via `castSucc`). -/
def FlowerVert.embed (u v g : ℕ) : FlowerVert u v g → FlowerVert u v (g + 1)
  | .inl h => .inl h
  | .inr ⟨k, e, pos⟩ => .inr ⟨k.castSucc, e, pos⟩

/-- `embed` is injective: distinct vertices at gen g remain distinct at gen g+1. -/
theorem FlowerVert.embed_injective {u v g : ℕ} :
    Function.Injective (FlowerVert.embed u v g) := by
  intro x y hxy
  cases x with
  | inl a =>
    cases y with
    | inl _ =>
      have := Sum.inl_injective hxy
      exact congrArg Sum.inl this
    | inr _ => simp [embed] at hxy
  | inr a =>
    cases y with
    | inl _ => simp [embed] at hxy
    | inr b =>
      congr 1
      have h := Sum.inr_injective hxy
      have hfst : a.1.castSucc = b.1.castSucc := congr_arg Sigma.fst h
      have hk : a.1 = b.1 := Fin.castSucc_injective _ hfst
      cases a; cases b; simp only at hk; subst hk
      simpa using h

/-- An embedded (old) vertex is never equal to a newly created vertex at gen g. -/
theorem FlowerVert.embed_ne_new {u v g : ℕ} (x : FlowerVert u v g)
    (e : FlowerEdge u v g) (pos : Fin (u - 1) ⊕ Fin (v - 1)) :
    FlowerVert.embed u v g x ≠
      .inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, e, pos⟩ := by
  cases x with
  | inl _ => simp [embed]
  | inr val =>
    intro h
    have h := Sum.inr_injective h
    have hk := congr_arg (fun s => (Sigma.fst s).val) h
    simp only [Fin.val_castSucc] at hk
    omega

/-- Within a single gadget, source and target positions are always distinct
when `1 < u`. -/
theorem localSrc_ne_localTgt (u v : ℕ) (hu : 1 < u) (e : LocalEdge u v) :
    localSrc u v e ≠ localTgt u v e := by
  rcases e with (⟨⟨_ | i, hi⟩⟩ | ⟨⟨_ | j, hj⟩⟩) <;>
    simp [localSrc, localTgt] <;> split_ifs <;> simp_all

/-! ## Layer 2: Edge endpoints via gadget resolution -/

/-- Endpoints of edge `e` at generation `g`: `(source, target)`.

- Gen 0: the single edge goes from hub0 to hub1.
- Gen g+1: edge `(parent, localEdge)`. Look up parent's endpoints,
  then resolve the local edge's gadget positions.

`GadgetPos.src` → parent's source (embedded into gen g+1)
`GadgetPos.tgt` → parent's target (embedded into gen g+1)
`GadgetPos.short i` → new internal vertex `(g, parent, .inl i)`
`GadgetPos.long j` → new internal vertex `(g, parent, .inr j)` -/
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

/-- Source endpoint of an edge. -/
def edgeSrc (u v g : ℕ) (e : FlowerEdge u v g) : FlowerVert u v g :=
  (edgeEndpoints u v g e).1

/-- Target endpoint of an edge. -/
def edgeTgt (u v g : ℕ) (e : FlowerEdge u v g) : FlowerVert u v g :=
  (edgeEndpoints u v g e).2

/-- Source ≠ target for every edge. (Needed for `SimpleGraph.loopless`.) -/
theorem edgeSrc_ne_edgeTgt (u v g : ℕ) (hu : 1 < u) (e : FlowerEdge u v g) :
    edgeSrc u v g e ≠ edgeTgt u v g e := by
  induction g with
  | zero => exact FlowerVert.hub0_ne_hub1 u v 0
  | succ g ih =>
    obtain ⟨parent, localE⟩ := e
    have hpar := ih parent
    have hloc := localSrc_ne_localTgt u v hu localE
    simp only [edgeEndpoints, edgeSrc, edgeTgt] at hpar ⊢
    -- Case-split on localSrc/localTgt values
    rcases hs : localSrc u v localE with src | tgt | ⟨i⟩ | ⟨j⟩ <;>
      rcases ht : localTgt u v localE with src | tgt | ⟨i'⟩ | ⟨j'⟩ <;>
      simp only [hs, ht] at hloc ⊢
    -- same-position contradictions
    all_goals first
      | exact absurd rfl hloc
      | exact FlowerVert.embed_injective.ne hpar
      | exact Ne.symm (FlowerVert.embed_injective.ne hpar)
      | exact FlowerVert.embed_ne_new _ parent _
      | exact Ne.symm (FlowerVert.embed_ne_new _ parent _)
      | (intro h; have := Sum.inr_injective h; simp_all)

/-! ## Layer 3: SimpleGraph -/

/-- Adjacency: vertices `a` and `b` are adjacent iff there exists an edge
whose endpoints are `{a, b}`. -/
def flowerAdj' (u v g : ℕ) (a b : FlowerVert u v g) : Prop :=
  ∃ e : FlowerEdge u v g,
    (a = edgeSrc u v g e ∧ b = edgeTgt u v g e) ∨
    (b = edgeSrc u v g e ∧ a = edgeTgt u v g e)

/-- The (u,v)-flower as a `SimpleGraph` on `FlowerVert`.
Construction requires `edgeSrc_ne_edgeTgt` for irreflexivity. -/
noncomputable def flowerGraph' (u v g : ℕ) (hu : 1 < u) :
    SimpleGraph (FlowerVert u v g) := by
  refine SimpleGraph.mk (flowerAdj' u v g) ?_ ?_
  · -- symmetry
    intro a b ⟨e, h⟩; exact ⟨e, h.symm⟩
  · -- irreflexivity
    exact ⟨fun a ⟨e, h⟩ => by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact edgeSrc_ne_edgeTgt u v g hu e (h1 ▸ h2)⟩

/-! ## Layer 4: Distance proof outline -/

/-- The flower graph is connected. -/
theorem flowerGraph'_connected (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (flowerGraph' u v g hu).Connected := by
  sorry

/-- **Upper bound**: there exists a walk of length `u^g` between hubs.

Proof idea (inductive): At gen 0, the single edge is a walk of length 1 = u^0.
At gen g+1, replace each edge of the gen g walk with the short path
(length u) through the gadget. Total length: u * u^g = u^(g+1). -/
theorem flowerGraph'_walk_hubs (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    ∃ w : (flowerGraph' u v g hu).Walk (.hub0 u v g) (.hub1 u v g),
      w.length = u ^ g := by
  sorry

/-- **Lower bound**: every walk between hubs has length ≥ u^g.

Proof idea (inductive via projection): Define a projection map that
collapses each gadget to a single edge, turning a gen g+1 walk into
a gen g walk. Key observation: any walk segment that enters a gadget
at one endpoint and exits at the other must traverse ≥ u edges (the
short path is the minimum). Therefore:

  walk length at gen g+1 ≥ u × (projected walk length at gen g)

By induction, walk length ≥ u × u^g = u^(g+1). -/
theorem flowerGraph'_dist_ge (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    u ^ g ≤ (flowerGraph' u v g hu).dist (.hub0 u v g) (.hub1 u v g) := by
  sorry

/-- **F2 bridge on FlowerVert**: hub distance = u^g. -/
theorem flowerGraph'_dist_hubs (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (flowerGraph' u v g hu).dist (.hub0 u v g) (.hub1 u v g) = u ^ g := by
  apply le_antisymm
  · -- Upper: from the exhibited walk
    obtain ⟨w, hw⟩ := flowerGraph'_walk_hubs u v g hu huv
    exact hw ▸ (flowerGraph' u v g hu).dist_le w
  · -- Lower: from projection
    exact flowerGraph'_dist_ge u v g hu huv

/-! ## Layer 5: Transport to Fin and final bridge -/

/-- Vertex count matches. -/
theorem flowerVert_card (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    Fintype.card (FlowerVert u v g) = flowerVertCount u v g := by
  sorry

/-- Equivalence to `Fin (flowerVertCount u v g)`. -/
noncomputable def flowerVertEquiv (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    FlowerVert u v g ≃ Fin (flowerVertCount u v g) :=
  (Fintype.equivFinOfCardEq (flowerVert_card u v g hu huv))

/-- The (u,v)-flower on `Fin`. -/
noncomputable def flowerGraph (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    SimpleGraph (Fin (flowerVertCount u v g)) :=
  (flowerGraph' u v g hu).comap (flowerVertEquiv u v g hu huv).symm

/-- **The F2 bridge theorem.** -/
theorem flowerGraph_dist_hubs (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (flowerGraph u v g hu huv).dist
      ((flowerVertEquiv u v g hu huv) (.hub0 u v g))
      ((flowerVertEquiv u v g hu huv) (.hub1 u v g))
    = flowerHubDist u v g := by
  -- Rewrite flowerHubDist as u^g, then use flowerGraph'_dist_hubs + comap
  sorry

/-! ## Projection map (for lower bound proof)

The projection collapses each replacement gadget to a single edge,
mapping a gen g+1 walk to a gen g walk.

On vertices:
- Hubs and older internal vertices (gen < g) map to themselves via embed⁻¹
- Internal vertices at gen g (inside a gadget) map to the source endpoint
  of their parent edge

On walk segments:
- A sub-walk within one gadget from src to tgt contributes 1 edge to
  the projected walk (length ≥ u maps to 1)
- A sub-walk that enters and returns to the same gadget endpoint
  contributes 0 edges (but consumes ≥ 0 steps)

This gives: projected walk length × u ≤ original walk length.
Combined with inductive hypothesis `projected walk length ≥ u^g`,
we get `original walk length ≥ u^(g+1)`. -/

/-- Project a FlowerVert at gen g+1 back to gen g.
Internal vertices at generation g collapse to the source endpoint
of their parent edge. All older vertices map to themselves. -/
def FlowerVert.project (u v g : ℕ) : FlowerVert u v (g + 1) → FlowerVert u v g
  | .inl h => .inl h
  | .inr ⟨k, e, pos⟩ =>
    if h : k.val < g then
      -- Older internal vertex: embed back
      .inr ⟨⟨k.val, h⟩, e, pos⟩
    else
      -- Gen g internal vertex: collapse to parent edge's source
      -- k.val = g (since k : Fin (g+1) and k.val ≥ g means k.val = g)
      have hk : k.val = g := by omega
      edgeSrc u v g (hk ▸ e)
