/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Box covering of graphs

The box-covering number of Song, Havlin and Makse: the fewest vertex sets of extended
diameter `< ℓ` needed to cover every vertex.

## Main definitions

- `SimpleGraph.IsBox` — a vertex set whose points are pairwise at extended distance `< ℓ`
- `SimpleGraph.boxCount` — the box-covering number `N_B(G, ℓ)`

## Main statements

- `SimpleGraph.boxCount_le_of_cover` — any cover bounds `boxCount` from above
- `SimpleGraph.le_boxCount_of_separated` — `ℓ`-separated points bound it from below
- `SimpleGraph.boxCount_anti` — `boxCount` is antitone in `ℓ`
- `SimpleGraph.Iso.boxCount_eq` — `boxCount` is invariant under isomorphism
- `SimpleGraph.le_add_dist_of_lipschitz` — a 1-Lipschitz potential bounds distance

## References

- [SongHavlinMakse2005] box covering of complex networks.

## Tags

box covering, box-counting, graph metric
-/

namespace SimpleGraph

variable {V W : Type*} (G : SimpleGraph V)

/-- A box of size `ℓ`: a vertex set whose points are pairwise at extended distance `< ℓ`. -/
def IsBox (ℓ : ℕ) (B : Set V) : Prop :=
  ∀ ⦃x⦄, x ∈ B → ∀ ⦃y⦄, y ∈ B → G.edist x y < ℓ

/-- The box-covering number `N_B(G, ℓ)`: the fewest boxes of size `ℓ` covering every vertex. -/
noncomputable def boxCount (ℓ : ℕ) : ℕ :=
  sInf {n | ∃ B : Fin n → Set V, (∀ i, G.IsBox ℓ (B i)) ∧ ∀ x, ∃ i, x ∈ B i}

variable {G}

theorem isBox_singleton {ℓ : ℕ} (hℓ : 0 < ℓ) (x : V) : G.IsBox ℓ {x} := by
  intro a ha b hb
  simp only [Set.mem_singleton_iff] at ha hb
  subst ha hb
  simp [edist_self, hℓ]

theorem IsBox.subset {ℓ : ℕ} {B B' : Set V} (h : G.IsBox ℓ B) (hB : B' ⊆ B) :
    G.IsBox ℓ B' := by
  intro x hx y hy
  exact h (hB hx) (hB hy)

theorem IsBox.mono {ℓ ℓ' : ℕ} {B : Set V} (h : G.IsBox ℓ B) (hℓ : ℓ ≤ ℓ') :
    G.IsBox ℓ' B := by
  intro x hx y hy
  exact (h hx hy).trans_le (by exact_mod_cast hℓ)

theorem boxCount_le_of_cover {ℓ n : ℕ} (B : Fin n → Set V) (hB : ∀ i, G.IsBox ℓ (B i))
    (hcov : ∀ x, ∃ i, x ∈ B i) : G.boxCount ℓ ≤ n := by
  exact Nat.sInf_le ⟨B, hB, hcov⟩

theorem exists_cover_boxCount [Finite V] {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∃ B : Fin (G.boxCount ℓ) → Set V, (∀ i, G.IsBox ℓ (B i)) ∧ ∀ x, ∃ i, x ∈ B i := by
  have : Fintype V := Fintype.ofFinite V
  have hne : {n | ∃ B : Fin n → Set V, (∀ i, G.IsBox ℓ (B i)) ∧ ∀ x, ∃ i, x ∈ B i}.Nonempty :=
    ⟨Fintype.card V, fun i => {(Fintype.equivFin V).symm i}, fun i => isBox_singleton hℓ _,
      fun x => ⟨Fintype.equivFin V x, by simp⟩⟩
  exact Nat.sInf_mem hne

theorem boxCount_le_card [Fintype V] {ℓ : ℕ} (hℓ : 0 < ℓ) :
    G.boxCount ℓ ≤ Fintype.card V := by
  exact boxCount_le_of_cover (fun i => {(Fintype.equivFin V).symm i})
    (fun i => isBox_singleton hℓ _) (fun x => ⟨Fintype.equivFin V x, by simp⟩)

theorem boxCount_pos [Finite V] [Nonempty V] {ℓ : ℕ} (hℓ : 0 < ℓ) : 0 < G.boxCount ℓ := by
  obtain ⟨B, -, hcov⟩ := G.exists_cover_boxCount hℓ
  obtain ⟨i, -⟩ := hcov (Classical.arbitrary V)
  exact Nat.pos_of_ne_zero fun h => (Fin.cast h i).elim0

theorem boxCount_anti [Finite V] {ℓ ℓ' : ℕ} (hℓ : 0 < ℓ) (h : ℓ ≤ ℓ') :
    G.boxCount ℓ' ≤ G.boxCount ℓ := by
  obtain ⟨B, hB, hcov⟩ := G.exists_cover_boxCount hℓ
  exact boxCount_le_of_cover B (fun i => (hB i).mono h) hcov

/-- Points that are pairwise at extended distance `≥ ℓ` lie in distinct boxes of size `ℓ`,
so they force at least that many boxes. -/
theorem le_boxCount_of_separated [Finite V] {ℓ n : ℕ} (hℓ : 0 < ℓ) (c : Fin n → V)
    (hc : ∀ i j, i ≠ j → (ℓ : ℕ∞) ≤ G.edist (c i) (c j)) : n ≤ G.boxCount ℓ := by
  obtain ⟨B, hB, hcov⟩ := G.exists_cover_boxCount hℓ
  choose g hg using fun i => hcov (c i)
  have hinj : Function.Injective g := by
    intro i j hij
    by_contra hne
    have h1 := hB (g i) (hg i) (hij ▸ hg j)
    exact absurd (hc i j hne) (not_le.mpr h1)
  simpa using Fintype.card_le_of_injective g hinj

/-- `boxCount` is invariant under graph isomorphism. -/
theorem Iso.boxCount_eq {G' : SimpleGraph W} (φ : G ≃g G') (ℓ : ℕ) :
    G'.boxCount ℓ = G.boxCount ℓ := by
  have e1 : ∀ x y : V, G.edist x y ≤ G'.edist (φ x) (φ y) := by
    intro x y
    by_cases h : G'.edist (φ x) (φ y) = ⊤
    · simp [h]
    · obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top h
      rw [← hp]
      have h2 := edist_le (p.map φ.symm.toHom)
      simpa using h2
  have e2 : ∀ x y : W, G'.edist x y ≤ G.edist (φ.symm x) (φ.symm y) := by
    intro x y
    by_cases h : G.edist (φ.symm x) (φ.symm y) = ⊤
    · simp [h]
    · obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top h
      rw [← hp]
      have h2 := edist_le (p.map φ.toHom)
      simpa using h2
  unfold boxCount
  congr 1
  ext n
  constructor
  · rintro ⟨B, hB, hcov⟩
    refine ⟨fun i => φ ⁻¹' B i, fun i x hx y hy => (e1 x y).trans_lt (hB i hx hy), fun x => ?_⟩
    obtain ⟨i, hi⟩ := hcov (φ x)
    exact ⟨i, hi⟩
  · rintro ⟨B, hB, hcov⟩
    refine ⟨fun i => φ.symm ⁻¹' B i, fun i x hx y hy => (e2 x y).trans_lt (hB i hx hy),
      fun x => ?_⟩
    obtain ⟨i, hi⟩ := hcov (φ.symm x)
    exact ⟨i, hi⟩

/-- A potential that changes by at most one along each edge bounds distance. -/
theorem le_add_dist_of_lipschitz {f : V → ℕ} (hf : ∀ a b, G.Adj a b → f a ≤ f b + 1)
    {x y : V} (hxy : G.Reachable x y) : f x ≤ f y + G.dist x y := by
  have key : ∀ {u v : V} (p : G.Walk u v), f u ≤ f v + p.length := by
    intro u v p
    induction p with
    | nil => simp
    | cons h p ih =>
      have := hf _ _ h
      simp only [Walk.length_cons]
      omega
  obtain ⟨p, hp⟩ := hxy.exists_walk_length_eq_dist
  have := key p
  omega

/-- Folding a 1-Lipschitz potential into a tent `min f (M - f)` keeps it 1-Lipschitz. -/
theorem tent_lipschitz {f : V → ℕ} (M : ℕ) (hf : ∀ a b, G.Adj a b → f a ≤ f b + 1)
    (a b : V) (hab : G.Adj a b) : min (f a) (M - f a) ≤ min (f b) (M - f b) + 1 := by
  have h1 := hf a b hab
  have h2 := hf b a hab.symm
  omega

/-- Graph homomorphisms do not increase distance between reachable vertices. -/
theorem Hom.dist_le {G' : SimpleGraph W} (φ : G →g G') {x y : V} (hxy : G.Reachable x y) :
    G'.dist (φ x) (φ y) ≤ G.dist x y := by
  obtain ⟨p, hp⟩ := hxy.exists_walk_length_eq_dist
  exact (SimpleGraph.dist_le (p.map φ)).trans (by simp [hp])

end SimpleGraph
