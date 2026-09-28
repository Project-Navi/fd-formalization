/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.FlowerConstruction

/-!
# Cells of the (u,v)-flower

A generation-`k` edge `e` is replaced, `j` generations later, by a copy of the
generation-`j` flower hanging between the (embedded) endpoints of `e`: its *cell*.
`cellEmbed k e j` maps the generation-`j` flower onto the cell of `e` inside the
generation-`(k + j)` flower. The `(u + v) ^ k` cells cover the graph and meet only at
their hubs.

## Main definitions

- `FlowerEdge.graft` — a gen-`k` edge followed by the local indices of a gen-`j` edge
- `FlowerEdge.trunc`, `FlowerEdge.suffix` — split a gen-`(k + j)` edge back apart
- `FlowerVert.embedN` — `embed` iterated `j` times
- `cellEmbed` — the gen-`j` flower mapped onto the cell of `e`

## Main statements

- `trunc_graft`, `suffix_graft`, `graft_trunc_suffix` — `graft` is a bijection
- `edgeSrc_graft`, `edgeTgt_graft` — edges of the cell are images of gen-`j` edges
- `cellEmbed_injective` — each cell is an injective copy of the gen-`j` flower
- `cellEmbed_adj` — `cellEmbed` is a graph homomorphism
- `exists_cellEmbed_eq` — the cells cover every vertex
- `cellEmbed_eq_of_ne` — distinct cells meet only at hubs

## Implementation notes

Generations are indexed as `k + j` throughout, so `k + (j + 1)` reduces to
`(k + j) + 1` definitionally and no casts between `FlowerEdge` types are needed.

## References

- [Rozenfeld2007] the recursive construction of the (u,v)-flowers.

## Tags

flower graph, self-similarity, cell decomposition
-/

variable {u v : ℕ}

/-- A generation-`k` edge `e` followed by the local indices of a generation-`j` edge `f`:
the edge of generation `k + j` that `f` names inside the cell of `e`. -/
def FlowerEdge.graft (k : ℕ) (e : FlowerEdge u v k) :
    (j : ℕ) → FlowerEdge u v j → FlowerEdge u v (k + j)
  | 0, () => e
  | j + 1, (f, l) => (FlowerEdge.graft k e j f, l)

/-- The generation-`k` ancestor of a generation-`(k + j)` edge. -/
def FlowerEdge.trunc (k : ℕ) : (j : ℕ) → FlowerEdge u v (k + j) → FlowerEdge u v k
  | 0, e => e
  | j + 1, (f, _) => FlowerEdge.trunc k j f

/-- The last `j` local indices of a generation-`(k + j)` edge, as a generation-`j` edge. -/
def FlowerEdge.suffix (k : ℕ) : (j : ℕ) → FlowerEdge u v (k + j) → FlowerEdge u v j
  | 0, _ => ()
  | j + 1, (f, l) => (FlowerEdge.suffix k j f, l)

/-- `FlowerVert.embed` iterated `j` times. -/
def FlowerVert.embedN (k : ℕ) : (j : ℕ) → FlowerVert u v k → FlowerVert u v (k + j)
  | 0, x => x
  | j + 1, x => FlowerVert.embed u v (k + j) (FlowerVert.embedN k j x)

/-- The generation-`j` flower mapped onto the cell of the generation-`k` edge `e` inside
the generation-`(k + j)` flower: the hubs go to the embedded endpoints of `e`, and the
vertex created at generation `i` on edge `f` goes to the vertex created at generation
`k + i` on `graft k e i f`. -/
def cellEmbed (k : ℕ) (e : FlowerEdge u v k) (j : ℕ) :
    FlowerVert u v j → FlowerVert u v (k + j)
  | .inl ⟨0, _⟩ => FlowerVert.embedN k j (edgeSrc u v k e)
  | .inl ⟨_ + 1, _⟩ => FlowerVert.embedN k j (edgeTgt u v k e)
  | .inr ⟨i, f, pos⟩ => .inr ⟨⟨k + i.val, by omega⟩, FlowerEdge.graft k e i.val f, pos⟩

/-! ## `graft` is a bijection -/

theorem FlowerEdge.trunc_graft (k : ℕ) (e : FlowerEdge u v k) (j : ℕ)
    (f : FlowerEdge u v j) : FlowerEdge.trunc k j (FlowerEdge.graft k e j f) = e := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih f.1

theorem FlowerEdge.suffix_graft (k : ℕ) (e : FlowerEdge u v k) (j : ℕ)
    (f : FlowerEdge u v j) : FlowerEdge.suffix k j (FlowerEdge.graft k e j f) = f := by
  induction j with
  | zero => rfl
  | succ j ih =>
    obtain ⟨f, l⟩ := f
    exact congrArg (·, l) (ih f)

theorem FlowerEdge.graft_trunc_suffix (k j : ℕ) (f : FlowerEdge u v (k + j)) :
    FlowerEdge.graft k (FlowerEdge.trunc k j f) j (FlowerEdge.suffix k j f) = f := by
  induction j with
  | zero => rfl
  | succ j ih =>
    obtain ⟨f, l⟩ := f
    exact congrArg (·, l) (ih f)

/-! ## Cell edges are images of generation-`j` edges -/

theorem cellEmbed_embed (k : ℕ) (e : FlowerEdge u v k) (j : ℕ) (x : FlowerVert u v j) :
    cellEmbed k e (j + 1) (FlowerVert.embed u v j x) =
      FlowerVert.embed u v (k + j) (cellEmbed k e j x) := by
  rcases x with ⟨⟨_ | _ | n, hn⟩⟩ | ⟨⟨i, hi⟩, f, pos⟩
  · rfl
  · rfl
  · omega
  · rfl

private theorem edgeEndpoints_graft (k : ℕ) (e : FlowerEdge u v k) (j : ℕ)
    (f : FlowerEdge u v j) :
    edgeSrc u v (k + j) (FlowerEdge.graft k e j f) = cellEmbed k e j (edgeSrc u v j f) ∧
    edgeTgt u v (k + j) (FlowerEdge.graft k e j f) = cellEmbed k e j (edgeTgt u v j f) := by
  induction j with
  | zero => exact ⟨rfl, rfl⟩
  | succ j ih =>
    obtain ⟨f, l⟩ := f
    obtain ⟨ihs, iht⟩ := ih f
    have key : ∀ p : GadgetPos u v,
        (match p with
          | .src => FlowerVert.embed u v (k + j) (edgeSrc u v (k + j) (FlowerEdge.graft k e j f))
          | .tgt => FlowerVert.embed u v (k + j) (edgeTgt u v (k + j) (FlowerEdge.graft k e j f))
          | .short i => .inr ⟨⟨k + j, Nat.lt_succ_of_le le_rfl⟩, FlowerEdge.graft k e j f, .inl i⟩
          | .long i => .inr ⟨⟨k + j, Nat.lt_succ_of_le le_rfl⟩, FlowerEdge.graft k e j f, .inr i⟩ :
          FlowerVert u v (k + j + 1)) =
        cellEmbed k e (j + 1) (match p with
          | .src => FlowerVert.embed u v j (edgeSrc u v j f)
          | .tgt => FlowerVert.embed u v j (edgeTgt u v j f)
          | .short i => .inr ⟨⟨j, Nat.lt_succ_of_le le_rfl⟩, f, .inl i⟩
          | .long i => .inr ⟨⟨j, Nat.lt_succ_of_le le_rfl⟩, f, .inr i⟩) := by
      intro p
      rcases p with _ | _ | i | i
      · rw [ihs, cellEmbed_embed]
      · rw [iht, cellEmbed_embed]
      · rfl
      · rfl
    exact ⟨key (localSrc u v l), key (localTgt u v l)⟩

theorem edgeSrc_graft (k : ℕ) (e : FlowerEdge u v k) (j : ℕ) (f : FlowerEdge u v j) :
    edgeSrc u v (k + j) (FlowerEdge.graft k e j f) = cellEmbed k e j (edgeSrc u v j f) := by
  exact (edgeEndpoints_graft k e j f).1

theorem edgeTgt_graft (k : ℕ) (e : FlowerEdge u v k) (j : ℕ) (f : FlowerEdge u v j) :
    edgeTgt u v (k + j) (FlowerEdge.graft k e j f) = cellEmbed k e j (edgeTgt u v j f) := by
  exact (edgeEndpoints_graft k e j f).2

/-! ## Each cell is a copy of the generation-`j` flower -/

private theorem embedN_inl (k j : ℕ) (h : Fin 2) :
    FlowerVert.embedN k j (.inl h : FlowerVert u v k) = .inl h := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [FlowerVert.embedN, ih]; rfl

private theorem embedN_inr (k j i : ℕ) (hi : i < k) (f : FlowerEdge u v i)
    (pos : Fin (u - 1) ⊕ Fin (v - 1)) :
    FlowerVert.embedN k j (.inr ⟨⟨i, hi⟩, f, pos⟩ : FlowerVert u v k) =
      .inr ⟨⟨i, by omega⟩, f, pos⟩ := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [FlowerVert.embedN, ih]; rfl

private theorem embedN_injective (k j : ℕ) :
    Function.Injective (FlowerVert.embedN (u := u) (v := v) k j) := by
  induction j with
  | zero => exact fun _ _ h => h
  | succ j ih => exact fun _ _ h => ih (FlowerVert.embed_injective h)

private theorem embedN_ne_inr (k j : ℕ) (w : FlowerVert u v k) (i : ℕ) (hi : k + i < k + j)
    (f : FlowerEdge u v (k + i)) (pos : Fin (u - 1) ⊕ Fin (v - 1)) :
    FlowerVert.embedN k j w ≠ .inr ⟨⟨k + i, hi⟩, f, pos⟩ := by
  rcases w with h | ⟨⟨i', hi'⟩, f', pos'⟩
  · rw [embedN_inl]; exact Sum.inl_ne_inr
  · rw [embedN_inr]
    intro h
    have := congrArg (fun s => (Sigma.fst s).val) (Sum.inr_injective h)
    simp only at this
    omega

private theorem cellEmbed_inr_eq {k : ℕ} {e e' : FlowerEdge u v k} {j i i' : ℕ} {hi : i < j}
    {hi' : i' < j} {f : FlowerEdge u v i} {f' : FlowerEdge u v i'}
    {pos pos' : Fin (u - 1) ⊕ Fin (v - 1)}
    (h : cellEmbed k e j (.inr ⟨⟨i, hi⟩, f, pos⟩) =
      cellEmbed k e' j (.inr ⟨⟨i', hi'⟩, f', pos'⟩)) :
    ∃ hii : i = i', FlowerEdge.graft k e i f = FlowerEdge.graft k e' i (hii ▸ f') ∧
      pos = pos' := by
  have h1 := Sum.inr_injective h
  have h2 := congrArg (fun s => s.1.val) h1
  simp only [add_right_inj] at h2
  subst h2
  have h3 := Prod.mk.inj (eq_of_heq (Sigma.mk.inj h1).2)
  exact ⟨rfl, h3⟩

theorem cellEmbed_injective (k : ℕ) (e : FlowerEdge u v k) (j : ℕ) :
    Function.Injective (cellEmbed k e j) := by
  intro x y h
  rcases x with ⟨⟨_ | _ | n, hn⟩⟩ | ⟨⟨i, hi⟩, f, pos⟩ <;>
    rcases y with ⟨⟨_ | _ | n', hn'⟩⟩ | ⟨⟨i', hi'⟩, f', pos'⟩ <;>
    try first | omega | rfl
  · exact absurd (embedN_injective k j h) (edgeSrc_ne_edgeTgt u v k e)
  · exact absurd h (embedN_ne_inr _ _ _ _ _ _ _)
  · exact absurd (embedN_injective k j h).symm (edgeSrc_ne_edgeTgt u v k e)
  · exact absurd h (embedN_ne_inr _ _ _ _ _ _ _)
  · exact absurd h.symm (embedN_ne_inr _ _ _ _ _ _ _)
  · exact absurd h.symm (embedN_ne_inr _ _ _ _ _ _ _)
  · obtain ⟨rfl, hg, rfl⟩ := cellEmbed_inr_eq h
    have := congrArg (FlowerEdge.suffix k i) hg
    rw [FlowerEdge.suffix_graft, FlowerEdge.suffix_graft] at this
    subst this
    rfl

theorem cellEmbed_adj (k : ℕ) (e : FlowerEdge u v k) (j : ℕ) {x y : FlowerVert u v j}
    (h : (flowerGraph' u v j).Adj x y) :
    (flowerGraph' u v (k + j)).Adj (cellEmbed k e j x) (cellEmbed k e j y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨FlowerEdge.graft k e j f, ?_⟩
  rw [edgeSrc_graft, edgeTgt_graft]
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- `cellEmbed` as a graph homomorphism. -/
def cellHom (k : ℕ) (e : FlowerEdge u v k) (j : ℕ) :
    flowerGraph' u v j →g flowerGraph' u v (k + j) where
  toFun := cellEmbed k e j
  map_rel' := cellEmbed_adj k e j

/-! ## The cells cover the graph and meet only at hubs -/

private theorem embed_endpoint (hu : 1 < u) (g : ℕ) (y : FlowerVert u v g)
    (hy : ∃ e, y = edgeSrc u v g e ∨ y = edgeTgt u v g e) :
    ∃ e, FlowerVert.embed u v g y = edgeSrc u v (g + 1) e ∨
      FlowerVert.embed u v g y = edgeTgt u v (g + 1) e := by
  obtain ⟨e, rfl | rfl⟩ := hy
  · exact ⟨(e, .inl ⟨0, by omega⟩), Or.inl (short_first_eq_embed_src u v g hu e).symm⟩
  · exact ⟨(e, .inl ⟨u - 1, by omega⟩), Or.inr (short_last_eq_embed_tgt u v g hu e).symm⟩

private theorem vert_endpoint (hu : 1 < u) (g : ℕ) (w : FlowerVert u v g) :
    ∃ e, w = edgeSrc u v g e ∨ w = edgeTgt u v g e := by
  induction g with
  | zero =>
    rcases w with ⟨⟨_ | _ | n, hn⟩⟩ | ⟨⟨i, hi⟩, f, pos⟩
    · exact ⟨(), Or.inl rfl⟩
    · exact ⟨(), Or.inr rfl⟩
    · omega
    · omega
  | succ g ih =>
    rcases w with h | ⟨⟨i, hi⟩, f, pos⟩
    · exact embed_endpoint hu g (.inl h) (ih _)
    · by_cases hig : i < g
      · exact embed_endpoint hu g (.inr ⟨⟨i, hig⟩, f, pos⟩) (ih _)
      · obtain rfl : i = g := by omega
        rcases pos with p | p
        · refine ⟨(f, .inl ⟨p.val, by omega⟩), Or.inr ?_⟩
          have hp : ¬ (p.val + 1 = u) := by omega
          simp only [edgeTgt, edgeEndpoints, localTgt, hp, dite_false]
          rfl
        · refine ⟨(f, .inr ⟨p.val, by omega⟩), Or.inr ?_⟩
          have hp : ¬ (p.val + 1 = v) := by omega
          simp only [edgeTgt, edgeEndpoints, localTgt, hp, dite_false]
          rfl

private theorem exists_cellEmbed_eq_embedN (hu : 1 < u) (k j : ℕ) (w : FlowerVert u v k) :
    ∃ (e : FlowerEdge u v k) (y : FlowerVert u v j),
      cellEmbed k e j y = FlowerVert.embedN k j w := by
  obtain ⟨e, rfl | rfl⟩ := vert_endpoint hu k w
  · exact ⟨e, .hub0 u v j, rfl⟩
  · exact ⟨e, .hub1 u v j, rfl⟩

/-- Every vertex of generation `k + j` lies in the cell of some generation-`k` edge. -/
theorem exists_cellEmbed_eq (hu : 1 < u) (k j : ℕ) (x : FlowerVert u v (k + j)) :
    ∃ (e : FlowerEdge u v k) (y : FlowerVert u v j), cellEmbed k e j y = x := by
  rcases x with h | ⟨⟨i, hi⟩, f, pos⟩
  · rw [← embedN_inl k j h]
    exact exists_cellEmbed_eq_embedN hu k j _
  · by_cases hik : i < k
    · rw [← embedN_inr k j i hik f pos]
      exact exists_cellEmbed_eq_embedN hu k j _
    · obtain ⟨m, rfl⟩ : ∃ m, i = k + m := ⟨i - k, by omega⟩
      refine ⟨FlowerEdge.trunc k m f, .inr ⟨⟨m, by omega⟩, FlowerEdge.suffix k m f, pos⟩, ?_⟩
      simp only [cellEmbed, FlowerEdge.graft_trunc_suffix]
      rfl

/-- Distinct cells meet only at hubs: a common vertex is a hub of each cell. -/
theorem cellEmbed_eq_of_ne (k : ℕ) {e e' : FlowerEdge u v k} (hee' : e ≠ e') (j : ℕ)
    {y y' : FlowerVert u v j} (h : cellEmbed k e j y = cellEmbed k e' j y') :
    (y = .hub0 u v j ∨ y = .hub1 u v j) := by
  rcases y with ⟨⟨_ | _ | n, hn⟩⟩ | ⟨⟨i, hi⟩, f, pos⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega
  · exfalso
    rcases y' with ⟨⟨_ | _ | n', hn'⟩⟩ | ⟨⟨i', hi'⟩, f', pos'⟩
    · exact embedN_ne_inr _ _ _ _ _ _ _ h.symm
    · exact embedN_ne_inr _ _ _ _ _ _ _ h.symm
    · omega
    · obtain ⟨rfl, hg, -⟩ := cellEmbed_inr_eq h
      have := congrArg (FlowerEdge.trunc k i) hg
      rw [FlowerEdge.trunc_graft, FlowerEdge.trunc_graft] at this
      exact hee' this

/-- Every edge of generation `k + j` is the image of a generation-`j` edge under the
`cellEmbed` of its ancestor. -/
theorem adj_cellEmbed (k j : ℕ) {a b : FlowerVert u v (k + j)}
    (h : (flowerGraph' u v (k + j)).Adj a b) :
    ∃ (e : FlowerEdge u v k) (x y : FlowerVert u v j), (flowerGraph' u v j).Adj x y ∧
      cellEmbed k e j x = a ∧ cellEmbed k e j y = b := by
  obtain ⟨F, hF⟩ := h
  have hs : cellEmbed k (FlowerEdge.trunc k j F) j (edgeSrc u v j (FlowerEdge.suffix k j F)) =
      edgeSrc u v (k + j) F := by
    rw [← edgeSrc_graft, FlowerEdge.graft_trunc_suffix]
  have ht : cellEmbed k (FlowerEdge.trunc k j F) j (edgeTgt u v j (FlowerEdge.suffix k j F)) =
      edgeTgt u v (k + j) F := by
    rw [← edgeTgt_graft, FlowerEdge.graft_trunc_suffix]
  rcases hF with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, _, _, ⟨FlowerEdge.suffix k j F, Or.inl ⟨rfl, rfl⟩⟩, hs, ht⟩
  · exact ⟨_, _, _, ⟨FlowerEdge.suffix k j F, Or.inr ⟨rfl, rfl⟩⟩, ht, hs⟩

/-! ## A potential supported on one cell -/

open Classical in
/-- Transport a potential on the generation-`j` flower to the cell of `e`, extended by
zero outside the cell. -/
noncomputable def cellPotential (k : ℕ) (e : FlowerEdge u v k) (j : ℕ)
    (φ : FlowerVert u v j → ℕ) (x : FlowerVert u v (k + j)) : ℕ :=
  if h : ∃ y, cellEmbed k e j y = x then φ h.choose else 0

theorem cellPotential_cellEmbed (k : ℕ) (e : FlowerEdge u v k) (j : ℕ)
    (φ : FlowerVert u v j → ℕ) (y : FlowerVert u v j) :
    cellPotential k e j φ (cellEmbed k e j y) = φ y := by
  have h : ∃ z, cellEmbed k e j z = cellEmbed k e j y := ⟨y, rfl⟩
  unfold cellPotential
  rw [dite_eq_left h, cellEmbed_injective k e j h.choose_spec]

/-- A potential that vanishes at the hubs, transported to the cell of `e`, is zero on every
other cell. -/
theorem cellPotential_eq_zero_of_ne (k : ℕ) {e e' : FlowerEdge u v k} (hee' : e ≠ e')
    (j : ℕ) (φ : FlowerVert u v j → ℕ)
    (h0 : φ (.hub0 u v j) = 0) (h1 : φ (.hub1 u v j) = 0) (x : FlowerVert u v j) :
    cellPotential k e j φ (cellEmbed k e' j x) = 0 := by
  unfold cellPotential
  split_ifs with h
  · rcases cellEmbed_eq_of_ne k hee' j h.choose_spec with h' | h' <;> rw [h'] <;> assumption
  · rfl

/-- A 1-Lipschitz potential on the generation-`j` flower that vanishes at both hubs stays
1-Lipschitz when transported to a cell and extended by zero, because the cell meets the
rest of the graph only at its hubs. -/
theorem cellPotential_lipschitz (k : ℕ) (e : FlowerEdge u v k) (j : ℕ)
    (φ : FlowerVert u v j → ℕ)
    (hφ : ∀ a b, (flowerGraph' u v j).Adj a b → φ a ≤ φ b + 1)
    (h0 : φ (.hub0 u v j) = 0) (h1 : φ (.hub1 u v j) = 0)
    (a b : FlowerVert u v (k + j)) (hab : (flowerGraph' u v (k + j)).Adj a b) :
    cellPotential k e j φ a ≤ cellPotential k e j φ b + 1 := by
  obtain ⟨e', x, y, hxy, rfl, rfl⟩ := adj_cellEmbed k j hab
  by_cases hee' : e = e'
  · subst hee'
    rw [cellPotential_cellEmbed, cellPotential_cellEmbed]
    exact hφ x y hxy
  · rw [cellPotential_eq_zero_of_ne k hee' j φ h0 h1 x]
    omega
