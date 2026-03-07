/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.FlowerCounts
import FdFormal.FlowerDiameter
import FdFormal.FlowerGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# (u,v)-Flower Graph Construction

Structured-gadget approach for the F2 bridge theorem: the (u,v)-flower
graph on `Fin` has hub distance `u^g`. All definitions and theorems are
fully proved with zero sorry.

## Main definitions

- `GadgetPos` — position within a replacement gadget (src, tgt, or internal)
- `LocalEdge` — edge within a replacement gadget (`Fin u ⊕ Fin v`)
- `FlowerEdge` — recursive edge index type
- `FlowerVert` — vertex type (hubs + sigma of internal vertices)
- `edgeEndpoints` — endpoint resolution via recursive gadget expansion
- `flowerGraph'` — the (u,v)-flower as a `SimpleGraph` on `FlowerVert`
- `FlowerVert.project` — projection map for lower bound proof

## Main statements

- `flowerVert_card` — vertex count matches arithmetic recurrence
- `gadgetInternal_card` — internal vertex count per gadget
- `edgeSrc_zero`, `edgeTgt_zero` — base case endpoints
- `short_tgt_eq_succ_src` — consecutive short-path endpoints match
- `short_first_eq_embed_src`, `short_last_eq_embed_tgt` — short-path boundary
- `long_tgt_eq_succ_src` — consecutive long-path endpoints match
- `long_first_eq_embed_src`, `long_last_eq_embed_tgt` — long-path boundary
- `flowerGraph'_adj_iff` — adjacency iff `flowerAdj'`
- `project_edgeSrc_succ` — source projects to parent source
- `project_edgeTgt_succ` — target projects to parent source or target
- `gadget_adj_chain` — u+1 vertex chain through short path of gadget
- `project_adj_or_eq` — adjacency preserved or collapsed under projection
- `flowerGraph'_connected` — connectivity of the flower graph
- `flowerGraph'_dist_hubs` — hub distance equals `u^g`
- `flowerGraph_dist_hubs` — F2 bridge on `Fin`

## Implementation notes

Each edge is replaced by two parallel paths of lengths `u` and `v`.
Internal vertices are `Fin (u-1) ⊕ Fin (v-1)`. Edges at generation `g`
are `FlowerEdge u v g`, defined recursively (parent × local edge),
avoiding division/modular arithmetic on `Fin`. The projection map
collapses each gadget traversal to a single edge for the lower bound.

## Tags

flower graph, construction
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
theorem localSrc_ne_localTgt (u v : ℕ) (_hu : 1 < u) (e : LocalEdge u v) :
    localSrc u v e ≠ localTgt u v e := by
  rcases e with (⟨⟨_ | i, hi⟩⟩ | ⟨⟨_ | j, hj⟩⟩) <;>
    simp only [localSrc, localTgt] <;> (split_ifs <;> simp_all)

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

/-- Fold `(edgeEndpoints ...).1` to `edgeSrc`. -/
@[simp] theorem edgeEndpoints_fst (u v g : ℕ) (e : FlowerEdge u v g) :
    (edgeEndpoints u v g e).1 = edgeSrc u v g e := rfl

/-- Fold `(edgeEndpoints ...).2` to `edgeTgt`. -/
@[simp] theorem edgeEndpoints_snd (u v g : ℕ) (e : FlowerEdge u v g) :
    (edgeEndpoints u v g e).2 = edgeTgt u v g e := rfl

/-- Base case: source of the unique gen-0 edge is hub0. -/
theorem edgeSrc_zero (u v : ℕ) :
    edgeSrc u v 0 () = FlowerVert.hub0 u v 0 := rfl

/-- Base case: target of the unique gen-0 edge is hub1. -/
theorem edgeTgt_zero (u v : ℕ) :
    edgeTgt u v 0 () = FlowerVert.hub1 u v 0 := rfl

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
    -- 16 cases from (localSrc × localTgt). Four closure patterns:
    -- 1. absurd rfl hloc: same position (src=src, tgt=tgt) contradicts hloc
    -- 2. embed_injective.ne: both endpoints are embedded, use inductive hypothesis
    -- 3. embed_ne_new: one endpoint is embedded, the other is a new vertex
    -- 4. Sum.inr_injective + simp_all: both are new vertices, extract index equality
    all_goals first
      | exact absurd rfl hloc
      | exact FlowerVert.embed_injective.ne hpar
      | exact Ne.symm (FlowerVert.embed_injective.ne hpar)
      | exact FlowerVert.embed_ne_new _ parent _
      | exact Ne.symm (FlowerVert.embed_ne_new _ parent _)
      | (intro h; have := Sum.inr_injective h; simp_all)

/-- The resolved source of a gadget edge matches the embedded source
of its parent edge. -/
theorem resolve_src_eq_embed_edgeSrc (u v g : ℕ) (parent : FlowerEdge u v g)
    (localE : LocalEdge u v) (hs : localSrc u v localE = .src) :
    edgeSrc u v (g + 1) (parent, localE) =
      FlowerVert.embed u v g (edgeSrc u v g parent) := by
  simp only [edgeSrc, edgeEndpoints, hs]

/-- The resolved target of a gadget edge matches the embedded target
of its parent edge. -/
theorem resolve_tgt_eq_embed_edgeTgt (u v g : ℕ) (parent : FlowerEdge u v g)
    (localE : LocalEdge u v) (ht : localTgt u v localE = .tgt) :
    edgeTgt u v (g + 1) (parent, localE) =
      FlowerVert.embed u v g (edgeTgt u v g parent) := by
  simp only [edgeTgt, edgeEndpoints, ht]

/-- Consecutive short-path edges share an endpoint: the target of edge `i`
equals the source of edge `i+1`. -/
theorem short_tgt_eq_succ_src (u v g : ℕ) (parent : FlowerEdge u v g)
    (i : Fin u) (hi : i.val + 1 < u) :
    edgeTgt u v (g + 1) (parent, .inl i) =
    edgeSrc u v (g + 1) (parent, .inl ⟨i.val + 1, hi⟩) := by
  simp only [edgeTgt, edgeSrc, edgeEndpoints, localTgt, localSrc,
    dif_neg (show ¬(i.val + 1 = u) by omega)]

/-- First short-path source is the embedded parent source. -/
theorem short_first_eq_embed_src (u v g : ℕ) (hu : 1 < u)
    (parent : FlowerEdge u v g) :
    edgeSrc u v (g + 1) (parent, .inl ⟨0, by omega⟩) =
    FlowerVert.embed u v g (edgeSrc u v g parent) := by
  simp only [edgeSrc, edgeEndpoints, localSrc]

/-- Last short-path target is the embedded parent target. -/
theorem short_last_eq_embed_tgt (u v g : ℕ) (hu : 1 < u)
    (parent : FlowerEdge u v g) :
    edgeTgt u v (g + 1) (parent, .inl ⟨u - 1, by omega⟩) =
    FlowerVert.embed u v g (edgeTgt u v g parent) := by
  simp only [edgeTgt, edgeEndpoints, localTgt,
    dif_pos (show (u - 1) + 1 = u by omega)]

/-- Consecutive long-path edges share an endpoint. -/
theorem long_tgt_eq_succ_src (u v g : ℕ) (parent : FlowerEdge u v g)
    (j : Fin v) (hj : j.val + 1 < v) :
    edgeTgt u v (g + 1) (parent, .inr j) =
    edgeSrc u v (g + 1) (parent, .inr ⟨j.val + 1, hj⟩) := by
  simp only [edgeTgt, edgeSrc, edgeEndpoints, localTgt, localSrc,
    dif_neg (show ¬(j.val + 1 = v) by omega)]

/-- First long-path source is the embedded parent source. -/
theorem long_first_eq_embed_src (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v)
    (parent : FlowerEdge u v g) :
    edgeSrc u v (g + 1) (parent, .inr ⟨0, by omega⟩) =
    FlowerVert.embed u v g (edgeSrc u v g parent) := by
  simp only [edgeSrc, edgeEndpoints, localSrc]

/-- Last long-path target is the embedded parent target. -/
theorem long_last_eq_embed_tgt (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v)
    (parent : FlowerEdge u v g) :
    edgeTgt u v (g + 1) (parent, .inr ⟨v - 1, by omega⟩) =
    FlowerVert.embed u v g (edgeTgt u v g parent) := by
  simp only [edgeTgt, edgeEndpoints, localTgt,
    dif_pos (show (v - 1) + 1 = v by omega)]

/-! ## Layer 3: SimpleGraph -/

/-- Adjacency: vertices `a` and `b` are adjacent iff there exists an edge
whose endpoints are `{a, b}`. -/
def flowerAdj' (u v g : ℕ) (a b : FlowerVert u v g) : Prop :=
  ∃ e : FlowerEdge u v g,
    (a = edgeSrc u v g e ∧ b = edgeTgt u v g e) ∨
    (b = edgeSrc u v g e ∧ a = edgeTgt u v g e)

/-- A local edge in a gadget creates an adjacency in `flowerAdj'`. -/
theorem resolve_localEdge_adj (u v g : ℕ) (parent : FlowerEdge u v g)
    (localE : LocalEdge u v) :
    flowerAdj' u v (g + 1)
      (edgeSrc u v (g + 1) (parent, localE))
      (edgeTgt u v (g + 1) (parent, localE)) :=
  ⟨(parent, localE), Or.inl ⟨rfl, rfl⟩⟩

/-- Consecutive short-path positions are adjacent. -/
theorem short_path_consecutive_adj (u v g : ℕ) (parent : FlowerEdge u v g)
    (i : Fin u) :
    flowerAdj' u v (g + 1)
      (edgeSrc u v (g + 1) (parent, .inl i))
      (edgeTgt u v (g + 1) (parent, .inl i)) :=
  resolve_localEdge_adj u v g parent (.inl i)

/-- Consecutive long-path positions are adjacent. -/
theorem long_path_consecutive_adj (u v g : ℕ) (parent : FlowerEdge u v g)
    (j : Fin v) :
    flowerAdj' u v (g + 1)
      (edgeSrc u v (g + 1) (parent, .inr j))
      (edgeTgt u v (g + 1) (parent, .inr j)) :=
  resolve_localEdge_adj u v g parent (.inr j)

/-- There exists a chain of `u + 1` vertices through the short path of a
replacement gadget, where consecutive vertices are adjacent. The chain
starts at the embedded source and ends at the embedded target of the
parent edge. Key building block for `flowerGraph'_walk_hubs`. -/
theorem gadget_adj_chain (u v g : ℕ) (hu : 1 < u)
    (parent : FlowerEdge u v g) :
    ∃ (vertices : Fin (u + 1) → FlowerVert u v (g + 1)),
      vertices 0 = FlowerVert.embed u v g (edgeSrc u v g parent) ∧
      vertices ⟨u, Nat.lt_succ_of_le le_rfl⟩ =
        FlowerVert.embed u v g (edgeTgt u v g parent) ∧
      ∀ (i : Fin u), flowerAdj' u v (g + 1)
        (vertices i.castSucc) (vertices i.succ) := by
  refine ⟨fun i => if h : i.val < u
    then edgeSrc u v (g + 1) (parent, .inl ⟨i.val, h⟩)
    else FlowerVert.embed u v g (edgeTgt u v g parent), ?_, ?_, ?_⟩
  · -- vertices 0 = embed(edgeSrc)
    simp only [Fin.val_zero, dif_pos (by omega : (0 : ℕ) < u)]
    exact short_first_eq_embed_src u v g hu parent
  · -- vertices u = embed(edgeTgt)
    exact dif_neg (lt_irrefl u)
  · intro i
    by_cases hi : i.val + 1 < u
    · -- internal step: both in edgeSrc branch
      simp only [Fin.val_castSucc, dif_pos i.isLt, Fin.val_succ, dif_pos hi]
      rw [← short_tgt_eq_succ_src u v g parent i hi]
      exact short_path_consecutive_adj u v g parent i
    · -- last step: i.castSucc in edgeSrc, i.succ in embed branch
      simp only [Fin.val_castSucc, dif_pos i.isLt, Fin.val_succ, dif_neg hi]
      have hival : i.val = u - 1 := by omega
      have : i = ⟨u - 1, by omega⟩ := Fin.ext hival
      rw [this, ← short_last_eq_embed_tgt u v g hu parent]
      exact short_path_consecutive_adj u v g parent ⟨u - 1, by omega⟩

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

/-- The adjacency relation of `flowerGraph'` is `flowerAdj'`. -/
theorem flowerGraph'_adj_iff (u v g : ℕ) (hu : 1 < u)
    (a b : FlowerVert u v g) :
    (flowerGraph' u v g hu).Adj a b ↔ flowerAdj' u v g a b := by
  constructor
  · exact id
  · exact id

/-! ## Layer 4: Walk construction and distance -/

/-- Walk of length `u` through the short path of a replacement gadget.
Converts the vertex chain from `gadget_adj_chain` into a `SimpleGraph.Walk`. -/
theorem gadget_short_walk (u v g : ℕ) (hu : 1 < u)
    (parent : FlowerEdge u v g) :
    ∃ w : (flowerGraph' u v (g + 1) hu).Walk
        (FlowerVert.embed u v g (edgeSrc u v g parent))
        (FlowerVert.embed u v g (edgeTgt u v g parent)),
      w.length = u := by
  obtain ⟨vertices, h0, hlast, hadj⟩ := gadget_adj_chain u v g hu parent
  rw [← h0, ← hlast]
  suffices ∀ k (hk : k ≤ u),
      ∃ w : (flowerGraph' u v (g + 1) hu).Walk
          (vertices 0) (vertices ⟨k, by omega⟩),
        w.length = k from this u le_rfl
  intro k hk
  induction k with
  | zero => exact ⟨.nil, rfl⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih (by omega)
    exact ⟨w.append (.cons (hadj ⟨k, by omega⟩) .nil), by
      simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_nil, hw]⟩

/-- Adjacent vertices in gen `g` are connected by a walk of length `u`
in gen `g+1` (through the replacement gadget's short path). -/
theorem adj_lift (u v g : ℕ) (hu : 1 < u) (a b : FlowerVert u v g)
    (hab : (flowerGraph' u v g hu).Adj a b) :
    ∃ w : (flowerGraph' u v (g + 1) hu).Walk
        (FlowerVert.embed u v g a) (FlowerVert.embed u v g b),
      w.length = u := by
  obtain ⟨e, he⟩ := hab
  rcases he with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · subst ha; subst hb
    exact gadget_short_walk u v g hu e
  · subst ha; subst hb
    obtain ⟨w, hw⟩ := gadget_short_walk u v g hu e
    exact ⟨w.reverse, by rw [SimpleGraph.Walk.length_reverse, hw]⟩

/-- Lift a gen-`g` walk to gen `g+1` by replacing each edge with a gadget
short path. The resulting walk has length `u * w.length`. -/
theorem lift_walk (u v g : ℕ) (hu : 1 < u) {a b : FlowerVert u v g}
    (w : (flowerGraph' u v g hu).Walk a b) :
    ∃ w' : (flowerGraph' u v (g + 1) hu).Walk
        (FlowerVert.embed u v g a) (FlowerVert.embed u v g b),
      w'.length = u * w.length := by
  induction w with
  | nil => exact ⟨.nil, by simp⟩
  | cons hab tail ih =>
    obtain ⟨w_step, hw_step⟩ := adj_lift u v g hu _ _ hab
    obtain ⟨w_tail, hw_tail⟩ := ih
    exact ⟨w_step.append w_tail, by
      rw [SimpleGraph.Walk.length_append, hw_step, hw_tail,
        SimpleGraph.Walk.length_cons, Nat.mul_succ]
      omega⟩

/-- **Upper bound**: there exists a walk of length `u^g` between hubs.

At gen 0, the single edge gives a walk of length 1 = u^0.
At gen g+1, `lift_walk` replaces each edge with a gadget short path
(length u), giving total length u * u^g = u^(g+1). -/
theorem flowerGraph'_walk_hubs (u v g : ℕ) (hu : 1 < u) :
    ∃ w : (flowerGraph' u v g hu).Walk (.hub0 u v g) (.hub1 u v g),
      w.length = u ^ g := by
  induction g with
  | zero =>
    exact ⟨.cons (⟨(), Or.inl ⟨rfl, rfl⟩⟩ : (flowerGraph' u v 0 hu).Adj _ _) .nil,
      by simp [SimpleGraph.Walk.length]⟩
  | succ g ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨w', hw'⟩ := lift_walk u v g hu w
    exact ⟨w', by rw [hw', hw, pow_succ, Nat.mul_comm]⟩

/-- Every new short-path vertex is reachable from the embedded source of its
parent edge, by chaining through the short-path adjacencies. -/
theorem new_short_reachable (u v g : ℕ) (hu : 1 < u)
    (parent : FlowerEdge u v g) (i : Fin (u - 1)) :
    (flowerGraph' u v (g + 1) hu).Reachable
      (FlowerVert.embed u v g (edgeSrc u v g parent))
      (.inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inl i⟩) := by
  suffices h : ∀ n (hn : n < u - 1),
      (flowerGraph' u v (g + 1) hu).Reachable
        (FlowerVert.embed u v g (edgeSrc u v g parent))
        (.inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inl ⟨n, hn⟩⟩) from
    h i.val i.isLt
  intro n
  induction n with
  | zero =>
    intro _
    have hadj : (flowerGraph' u v (g + 1) hu).Adj
        (edgeSrc u v (g + 1) (parent, .inl ⟨0, by omega⟩))
        (edgeTgt u v (g + 1) (parent, .inl ⟨0, by omega⟩)) :=
      short_path_consecutive_adj u v g parent ⟨0, by omega⟩
    rw [short_first_eq_embed_src u v g hu parent] at hadj
    convert hadj.reachable using 1
    simp only [edgeTgt, edgeEndpoints, localTgt, dif_neg (by omega : ¬(0 + 1 = u))]
  | succ m ih =>
    intro hm
    have hadj : (flowerGraph' u v (g + 1) hu).Adj
        (edgeSrc u v (g + 1) (parent, .inl ⟨m + 1, by omega⟩))
        (edgeTgt u v (g + 1) (parent, .inl ⟨m + 1, by omega⟩)) :=
      short_path_consecutive_adj u v g parent ⟨m + 1, by omega⟩
    have hsrc : edgeSrc u v (g + 1) (parent, .inl ⟨m + 1, by omega⟩) =
        .inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inl ⟨m, by omega⟩⟩ := by
      simp only [edgeSrc, edgeEndpoints, localSrc]
    have htgt : edgeTgt u v (g + 1) (parent, .inl ⟨m + 1, by omega⟩) =
        .inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inl ⟨m + 1, by omega⟩⟩ := by
      simp only [edgeTgt, edgeEndpoints, localTgt,
        dif_neg (show ¬(m + 1 + 1 = u) by omega)]
    rw [hsrc, htgt] at hadj
    exact (ih (by omega)).trans hadj.reachable

/-- Every new long-path vertex is reachable from the embedded source of its
parent edge, by chaining through the long-path adjacencies. -/
theorem new_long_reachable (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v)
    (parent : FlowerEdge u v g) (j : Fin (v - 1)) :
    (flowerGraph' u v (g + 1) hu).Reachable
      (FlowerVert.embed u v g (edgeSrc u v g parent))
      (.inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inr j⟩) := by
  suffices h : ∀ n (hn : n < v - 1),
      (flowerGraph' u v (g + 1) hu).Reachable
        (FlowerVert.embed u v g (edgeSrc u v g parent))
        (.inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inr ⟨n, hn⟩⟩) from
    h j.val j.isLt
  intro n
  induction n with
  | zero =>
    intro _
    have hadj : (flowerGraph' u v (g + 1) hu).Adj
        (edgeSrc u v (g + 1) (parent, .inr ⟨0, by omega⟩))
        (edgeTgt u v (g + 1) (parent, .inr ⟨0, by omega⟩)) :=
      long_path_consecutive_adj u v g parent ⟨0, by omega⟩
    rw [long_first_eq_embed_src u v g hu huv parent] at hadj
    convert hadj.reachable using 1
    simp only [edgeTgt, edgeEndpoints, localTgt, dif_neg (by omega : ¬(0 + 1 = v))]
  | succ m ih =>
    intro hm
    have hadj : (flowerGraph' u v (g + 1) hu).Adj
        (edgeSrc u v (g + 1) (parent, .inr ⟨m + 1, by omega⟩))
        (edgeTgt u v (g + 1) (parent, .inr ⟨m + 1, by omega⟩)) :=
      long_path_consecutive_adj u v g parent ⟨m + 1, by omega⟩
    have hsrc : edgeSrc u v (g + 1) (parent, .inr ⟨m + 1, by omega⟩) =
        .inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inr ⟨m, by omega⟩⟩ := by
      simp only [edgeSrc, edgeEndpoints, localSrc]
    have htgt : edgeTgt u v (g + 1) (parent, .inr ⟨m + 1, by omega⟩) =
        .inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inr ⟨m + 1, by omega⟩⟩ := by
      simp only [edgeTgt, edgeEndpoints, localTgt,
        dif_neg (show ¬(m + 1 + 1 = v) by omega)]
    rw [hsrc, htgt] at hadj
    exact (ih (by omega)).trans hadj.reachable

/-- The flower graph is connected. -/
theorem flowerGraph'_connected (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (flowerGraph' u v g hu).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  use .hub0 u v g
  induction g with
  | zero =>
    intro z
    cases z with
    | inl h =>
      fin_cases h
      · exact .rfl
      · exact SimpleGraph.Adj.reachable (show (flowerGraph' u v 0 hu).Adj _ _ from
          ⟨(), Or.inl ⟨rfl, rfl⟩⟩)
    | inr s => exact s.1.elim0
  | succ g ih =>
    have embed_reach : ∀ x : FlowerVert u v g,
        (flowerGraph' u v (g + 1) hu).Reachable
          (.hub0 u v (g + 1)) (FlowerVert.embed u v g x) := by
      intro x
      obtain ⟨w⟩ := ih x
      exact (lift_walk u v g hu w).choose.reachable
    intro z
    cases z with
    | inl h => fin_cases h <;> [exact .rfl; exact embed_reach (.hub1 u v g)]
    | inr s =>
      obtain ⟨k, parent, pos⟩ := s
      by_cases hk : k.val < g
      · -- Old vertex = embed of gen-g vertex
        have : (.inr (⟨k, parent, pos⟩ : Σ (k : Fin (g + 1)),
            FlowerEdge u v k.val × _) : FlowerVert u v (g + 1)) =
            FlowerVert.embed u v g (.inr ⟨⟨k.val, hk⟩, parent, pos⟩) := by
          simp [FlowerVert.embed]
        rw [this]; exact embed_reach _
      · -- New vertex at gen g
        have hkv : k.val = g := by omega
        have hkg : k = ⟨g, Nat.lt_succ_of_le le_rfl⟩ := Fin.ext hkv
        subst hkg
        exact (embed_reach (edgeSrc u v g parent)).trans (by
          cases pos with
          | inl i => exact new_short_reachable u v g hu parent i
          | inr j => exact new_long_reachable u v g hu huv parent j)

/-! ## Rank function (1-Lipschitz potential for lower bound)

The rank function assigns each vertex a "coarse position" from hub0 to hub1.
It satisfies `rank(hub0) = 0`, `rank(hub1) = u^g`, and adjacent vertices
differ by at most 1. This gives the lower bound on hub distance immediately.

For embedded vertices: `rank(embed x) = u * rank_g(x)`.
For new short-path vertices: `rank = u * srcR + (i+1)` if the parent edge
has distinct endpoint ranks, else `u * srcR` (flat gadget).
For new long-path vertices: floor-division interpolation `u * srcR + ((j+1)*u)/v`
if interpolating, else `u * srcR`. -/

/-- Floor-division adjacency: consecutive multiples divided by `v` differ
by at most 1 when `u ≤ v`. -/
theorem div_succ_le (k u v : ℕ) (huv : u ≤ v) (hv : 0 < v) :
    ((k + 1) * u) / v ≤ (k * u) / v + 1 := by
  rw [Nat.add_one_mul]
  calc (k * u + u) / v ≤ (k * u + v) / v :=
        Nat.div_le_div_right (Nat.add_le_add_left huv _)
    _ = k * u / v + 1 := Nat.add_div_right _ hv

/-- Rank: coarse position from hub0 (rank 0) to hub1 (rank u^g). -/
def FlowerVert.rank (u v : ℕ) : (g : ℕ) → FlowerVert u v g → ℕ
  | 0, .inl ⟨0, _⟩ => 0
  | 0, .inl ⟨1, _⟩ => 1
  | 0, .inl ⟨n + 2, h⟩ => absurd h (by omega)
  | 0, .inr ⟨k, _, _⟩ => absurd k.isLt (by omega)
  | g + 1, .inl h => u * rank u v g (.inl h)
  | g + 1, .inr ⟨k, parent, pos⟩ =>
    if hk : k.val < g then
      u * rank u v g (.inr ⟨⟨k.val, hk⟩, parent, pos⟩)
    else
      have hkg : k.val = g := by omega
      let parent' : FlowerEdge u v g := hkg ▸ parent
      let srcR := rank u v g (edgeSrc u v g parent')
      let tgtR := rank u v g (edgeTgt u v g parent')
      if srcR = tgtR then u * srcR
      else match pos with
        | .inl i => u * srcR + (i.val + 1)
        | .inr j => u * srcR + ((j.val + 1) * u) / v

/-- Hub 0 has rank 0. -/
theorem rank_hub0 (u v g : ℕ) :
    FlowerVert.rank u v g (.hub0 u v g) = 0 := by
  induction g with
  | zero => rfl
  | succ g ih =>
    change u * FlowerVert.rank u v g (.hub0 u v g) = 0
    rw [ih, Nat.mul_zero]

/-- Hub 1 has rank u^g. -/
theorem rank_hub1 (u v g : ℕ) :
    FlowerVert.rank u v g (.hub1 u v g) = u ^ g := by
  induction g with
  | zero => rfl
  | succ g ih =>
    change u * FlowerVert.rank u v g (.hub1 u v g) = u ^ (g + 1)
    rw [ih, pow_succ, Nat.mul_comm]

/-- Rank of an embedded vertex scales by `u`. -/
theorem rank_embed (u v g : ℕ) (x : FlowerVert u v g) :
    FlowerVert.rank u v (g + 1) (FlowerVert.embed u v g x) =
      u * FlowerVert.rank u v g x := by
  cases x with
  | inl h => rfl
  | inr val =>
    obtain ⟨k, parent, pos⟩ := val
    simp only [FlowerVert.embed, FlowerVert.rank, Fin.val_castSucc, dif_pos k.isLt, Fin.eta]

/-- Rank of a new short-path vertex at generation g. -/
theorem rank_new_short (u v g : ℕ) (parent : FlowerEdge u v g) (i : Fin (u - 1)) :
    FlowerVert.rank u v (g + 1)
      (.inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inl i⟩) =
    if FlowerVert.rank u v g (edgeSrc u v g parent) =
        FlowerVert.rank u v g (edgeTgt u v g parent)
    then u * FlowerVert.rank u v g (edgeSrc u v g parent)
    else u * FlowerVert.rank u v g (edgeSrc u v g parent) + (i.val + 1) := by
  simp only [FlowerVert.rank, dif_neg (by omega : ¬(g < g))]

/-- Rank of a new long-path vertex at generation g. -/
theorem rank_new_long (u v g : ℕ) (parent : FlowerEdge u v g) (j : Fin (v - 1)) :
    FlowerVert.rank u v (g + 1)
      (.inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inr j⟩) =
    if FlowerVert.rank u v g (edgeSrc u v g parent) =
        FlowerVert.rank u v g (edgeTgt u v g parent)
    then u * FlowerVert.rank u v g (edgeSrc u v g parent)
    else u * FlowerVert.rank u v g (edgeSrc u v g parent) +
      ((j.val + 1) * u) / v := by
  simp only [FlowerVert.rank, dif_neg (by omega : ¬(g < g))]

/-- Rank bounds along edges: non-decreasing and 1-Lipschitz.
Both bounds are proved simultaneously by induction, since the monotonicity
proof for the last short/long edge uses the Lipschitz bound at gen g. -/
theorem rank_edge_bounds (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v)
    (e : FlowerEdge u v g) :
    FlowerVert.rank u v g (edgeSrc u v g e) ≤
      FlowerVert.rank u v g (edgeTgt u v g e) ∧
    FlowerVert.rank u v g (edgeTgt u v g e) ≤
      FlowerVert.rank u v g (edgeSrc u v g e) + 1 := by
  induction g with
  | zero =>
    obtain ⟨⟩ := e
    simp [edgeSrc, edgeTgt, edgeEndpoints, FlowerVert.rank, FlowerVert.hub0, FlowerVert.hub1]
  | succ g ih =>
    obtain ⟨parent, localE⟩ := e
    obtain ⟨ihle, ihub⟩ := ih parent
    -- Helper: in the non-flat case, tgtR = srcR + 1
    have htgt_eq : ¬(FlowerVert.rank u v g (edgeSrc u v g parent) =
        FlowerVert.rank u v g (edgeTgt u v g parent)) →
        FlowerVert.rank u v g (edgeTgt u v g parent) =
        FlowerVert.rank u v g (edgeSrc u v g parent) + 1 :=
      fun h => Nat.le_antisymm ihub (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne ihle h))
    -- Unfold everything, split all ifs
    -- Case split on local edge, unfold endpoints and rank.
    -- rank_embed handles stuck `rank(embed x)` for abstract x.
    -- ← edgeSrc/edgeTgt normalizes (edgeEndpoints...).1/.2 so htgt_eq matches.
    rcases localE with ⟨⟨_ | n, hi⟩⟩ | ⟨⟨_ | n, hj⟩⟩ <;>
      simp only [edgeSrc, edgeTgt, edgeEndpoints, localSrc, localTgt,
        FlowerVert.rank, dif_neg (lt_irrefl g)] <;>
      split_ifs <;>
      simp only [FlowerVert.rank, rank_embed,
        edgeEndpoints_fst, edgeEndpoints_snd,
        dif_neg (lt_irrefl g)] <;>
      (try split_ifs) <;>
      simp only [edgeEndpoints_fst, edgeEndpoints_snd, Nat.zero_add] at * <;>
      first
      | exact ⟨le_rfl, Nat.le_succ _⟩
      | exact ⟨Nat.le_add_right _ _, le_rfl⟩
      | (constructor <;> omega)
      | (constructor
         · exact Nat.le_add_right _ _
         · have : (1 * u) / v ≤ 1 := Nat.div_le_of_le_mul (by omega); omega)
      | (constructor
         · exact Nat.add_le_add_left
             (Nat.div_le_div_right (Nat.mul_le_mul_right u (by omega))) _
         · exact Nat.add_le_add_left (div_succ_le (n + 1) u v huv (by omega)) _)
      | contradiction
      | (have h_eq : FlowerVert.rank u v g (edgeSrc u v g parent) =
            FlowerVert.rank u v g (edgeTgt u v g parent) := ‹_›
         rw [h_eq]; exact ⟨le_rfl, Nat.le_succ _⟩)
      | (have h := htgt_eq ‹_›; rw [h, mul_add, mul_one]
         constructor <;> linarith)
      | (have h := htgt_eq ‹_›; rw [h, mul_add, mul_one]
         constructor
         · exact Nat.add_le_add_left (Nat.div_le_of_le_mul (by
             nlinarith [Nat.mul_le_mul_left u (show n + 1 ≤ v from by omega),
               mul_comm (n + 1) u])) _
         · suffices u - 1 ≤ (n + 1) * u / v by omega
           calc u - 1 = (u - 1) * v / v :=
                 (Nat.mul_div_cancel (u - 1) (show 0 < v from by omega)).symm
             _ ≤ (n + 1) * u / v := Nat.div_le_div_right (by
                 zify [show 1 ≤ u from by omega, show 1 ≤ v from by omega] at *
                 nlinarith))

/-- Rank is non-decreasing along edges: rank(edgeSrc) ≤ rank(edgeTgt). -/
theorem rank_edgeSrc_le_edgeTgt (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v)
    (e : FlowerEdge u v g) :
    FlowerVert.rank u v g (edgeSrc u v g e) ≤
      FlowerVert.rank u v g (edgeTgt u v g e) :=
  (rank_edge_bounds u v g hu huv e).1

/-- Rank increases by at most 1 along edges. -/
theorem rank_edgeTgt_le_edgeSrc_succ (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v)
    (e : FlowerEdge u v g) :
    FlowerVert.rank u v g (edgeTgt u v g e) ≤
      FlowerVert.rank u v g (edgeSrc u v g e) + 1 :=
  (rank_edge_bounds u v g hu huv e).2

/-- Adjacent vertices satisfy `rank b ≤ rank a + 1`. -/
theorem rank_adj_le (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v)
    (a b : FlowerVert u v g) (hab : flowerAdj' u v g a b) :
    FlowerVert.rank u v g b ≤ FlowerVert.rank u v g a + 1 := by
  obtain ⟨e, he⟩ := hab
  rcases he with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;> subst ha <;> subst hb
  · exact rank_edgeTgt_le_edgeSrc_succ u v g hu huv e
  · exact Nat.le_succ_of_le (rank_edgeSrc_le_edgeTgt u v g hu huv e)

/-- Walk length bounds rank difference (one-sided). -/
theorem walk_length_ge_rank (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v)
    {a b : FlowerVert u v g}
    (w : (flowerGraph' u v g hu).Walk a b) :
    FlowerVert.rank u v g b ≤ FlowerVert.rank u v g a + w.length := by
  induction w with
  | nil => omega
  | cons hab tail ih =>
    have hadj := rank_adj_le u v g hu huv _ _ hab
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- **Lower bound**: hub distance ≥ u^g.

Uses the rank function as a 1-Lipschitz potential: any walk from hub0
(rank 0) to hub1 (rank u^g) has length ≥ u^g. -/
theorem flowerGraph'_dist_ge (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    u ^ g ≤ (flowerGraph' u v g hu).dist (.hub0 u v g) (.hub1 u v g) := by
  obtain ⟨w, hw⟩ := flowerGraph'_walk_hubs u v g hu
  have hreach : (flowerGraph' u v g hu).Reachable (.hub0 u v g) (.hub1 u v g) :=
    ⟨w⟩
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  have := walk_length_ge_rank u v g hu huv p
  rw [rank_hub0, rank_hub1] at this
  omega

/-- **F2 bridge on FlowerVert**: hub distance = u^g. -/
theorem flowerGraph'_dist_hubs (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (flowerGraph' u v g hu).dist (.hub0 u v g) (.hub1 u v g) = u ^ g := by
  apply le_antisymm
  · -- Upper: from the exhibited walk
    obtain ⟨w, hw⟩ := flowerGraph'_walk_hubs u v g hu
    exact hw ▸ (flowerGraph' u v g hu).dist_le w
  · -- Lower: from projection
    exact flowerGraph'_dist_ge u v g hu huv

/-! ## Layer 5: Transport to Fin and final bridge -/

/-- Internal vertex count per gadget: `(u-1) + (v-1) = u + v - 2`. -/
theorem gadgetInternal_card (u v : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    Fintype.card (Fin (u - 1) ⊕ Fin (v - 1)) = u + v - 2 := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- Vertex count matches the arithmetic recurrence. -/
theorem flowerVert_card (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    Fintype.card (FlowerVert u v g) = flowerVertCount u v g := by
  induction g with
  | zero =>
    simp [FlowerVert, Fintype.card_sum, Fintype.card_fin]
  | succ g ih =>
    simp only [FlowerVert, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod,
      Fintype.card_fin] at ih ⊢
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [flowerVertCount_succ, flowerEdgeCount_eq_pow, ← flowerEdge_card u v g]
    have h1 : u - 1 + (v - 1) = u + v - 2 := by omega
    simp only [h1] at ih ⊢
    linarith [Nat.mul_comm (Fintype.card (FlowerEdge u v g)) (u + v - 2)]

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
  set e := flowerVertEquiv u v g hu huv
  rw [flowerHubDist_eq_pow, ← flowerGraph'_dist_hubs u v g hu huv]
  -- Goal: flowerGraph.dist (e hub0) (e hub1) = flowerGraph'.dist hub0 hub1
  -- flowerGraph = flowerGraph'.comap e.symm, so e.symm is the comap hom
  set G := flowerGraph' u v g hu
  set G' := flowerGraph u v g hu huv
  -- e.symm is a hom G' →g G (by comap definition)
  have hom_back : ∀ {a b : Fin _}, G'.Adj a b → G.Adj (e.symm a) (e.symm b) :=
    fun h => h
  -- e is a hom G →g G' (comap + cancel)
  have hom_fwd : ∀ {a b}, G.Adj a b → G'.Adj (e a) (e b) := by
    intro a b h
    change G.Adj (e.symm (e a)) (e.symm (e b))
    simp only [Equiv.symm_apply_apply]; exact h
  apply le_antisymm
  · -- ≤: walk in G maps to walk in G'
    obtain ⟨w, hw⟩ := (flowerGraph'_connected u v g hu huv).exists_walk_length_eq_dist
      (.hub0 u v g) (.hub1 u v g)
    calc G'.dist (e (.hub0 u v g)) (e (.hub1 u v g))
        ≤ (w.map ⟨e, @hom_fwd⟩).length := SimpleGraph.dist_le _
      _ = w.length := SimpleGraph.Walk.length_map _ _
      _ = _ := hw
  · -- ≥: walk in G' maps to walk in G (e.symm preserves adjacency)
    have hreach : G'.Reachable (e (.hub0 u v g)) (e (.hub1 u v g)) := by
      obtain ⟨w, _⟩ := flowerGraph'_walk_hubs u v g hu
      exact (w.map ⟨e, @hom_fwd⟩).reachable
    obtain ⟨w', hw'⟩ := hreach.exists_walk_length_eq_dist
    calc G.dist _ _ ≤ ((w'.map ⟨e.symm, @hom_back⟩).copy
          (e.symm_apply_apply _) (e.symm_apply_apply _)).length := SimpleGraph.dist_le _
      _ = w'.length := by
          rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
      _ = G'.dist _ _ := hw'

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

/-- Project is a left inverse of embed: projecting an embedded vertex
recovers the original. -/
theorem FlowerVert.project_embed (u v g : ℕ) (x : FlowerVert u v g) :
    FlowerVert.project u v g (FlowerVert.embed u v g x) = x := by
  cases x with
  | inl _ => rfl
  | inr val =>
    obtain ⟨k, e, pos⟩ := val
    simp only [FlowerVert.embed, FlowerVert.project, Fin.val_castSucc, dif_pos k.isLt,
      Fin.eta]

/-- Hub 0 projects to hub 0. -/
theorem FlowerVert.project_hub0 (u v g : ℕ) :
    FlowerVert.project u v g (.hub0 u v (g + 1)) = .hub0 u v g := rfl

/-- Hub 1 projects to hub 1. -/
theorem FlowerVert.project_hub1 (u v g : ℕ) :
    FlowerVert.project u v g (.hub1 u v (g + 1)) = .hub1 u v g := rfl

/-- A new vertex at generation g projects to the source endpoint of its
parent edge. -/
theorem FlowerVert.project_new (u v g : ℕ) (parent : FlowerEdge u v g)
    (pos : Fin (u - 1) ⊕ Fin (v - 1)) :
    FlowerVert.project u v g
      (.inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, pos⟩) =
    edgeSrc u v g parent := by
  simp [FlowerVert.project]

/-- Source endpoint of `(parent, localE)` at gen `g+1` always projects to the
source endpoint of `parent` at gen `g`. -/
theorem project_edgeSrc_succ (u v g : ℕ) (parent : FlowerEdge u v g)
    (localE : LocalEdge u v) :
    FlowerVert.project u v g (edgeSrc u v (g + 1) (parent, localE)) =
      edgeSrc u v g parent := by
  rcases localE with ⟨⟨_ | i, hi⟩⟩ | ⟨⟨_ | j, hj⟩⟩ <;>
    simp only [edgeSrc, edgeEndpoints, localSrc] <;>
    first
    | exact FlowerVert.project_embed u v g _
    | exact FlowerVert.project_new u v g parent _

/-- Target endpoint of `(parent, localE)` at gen `g+1` projects to either the
source or target endpoint of `parent` at gen `g`. -/
theorem project_edgeTgt_succ (u v g : ℕ) (parent : FlowerEdge u v g)
    (localE : LocalEdge u v) :
    FlowerVert.project u v g (edgeTgt u v (g + 1) (parent, localE)) =
      edgeSrc u v g parent ∨
    FlowerVert.project u v g (edgeTgt u v (g + 1) (parent, localE)) =
      edgeTgt u v g parent := by
  rcases localE with ⟨i⟩ | ⟨j⟩ <;>
    simp only [edgeTgt, edgeEndpoints, localTgt] <;>
    split_ifs <;>
    first
    | exact Or.inr (FlowerVert.project_embed u v g _)
    | exact Or.inl (FlowerVert.project_new u v g parent _)

/-- Adjacent vertices at gen `g+1` project to either equal or adjacent
vertices at gen `g`. Key lemma for the lower bound proof. -/
theorem project_adj_or_eq (u v g : ℕ)
    (a b : FlowerVert u v (g + 1))
    (hab : flowerAdj' u v (g + 1) a b) :
    FlowerVert.project u v g a = FlowerVert.project u v g b ∨
    flowerAdj' u v g
      (FlowerVert.project u v g a)
      (FlowerVert.project u v g b) := by
  obtain ⟨⟨parent, localE⟩, he⟩ := hab
  rcases he with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;> subst ha <;> subst hb <;>
    simp only [project_edgeSrc_succ]
  · rcases project_edgeTgt_succ u v g parent localE with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr ⟨parent, Or.inl ⟨rfl, rfl⟩⟩
  · rcases project_edgeTgt_succ u v g parent localE with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr ⟨parent, Or.inr ⟨rfl, rfl⟩⟩
