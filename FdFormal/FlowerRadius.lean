/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.FlowerConstruction

/-!
# Radius and rank of the (u,v)-flower

Every vertex of the generation-`g` flower is within `v * u ^ g` of a hub, so the diameter
is at most `(2 * v + 1) * u ^ g`. The rank potential takes every value in `[0, u ^ g]`.

## Main statements

- `rank_le_pow` — ranks lie in `[0, u ^ g]`
- `rank_adj_le'` — rank changes by at most one along an edge, in both directions
- `exists_rank_eq` — every value in `[0, u ^ g]` is a rank
- `dist_hub_le` — every vertex is within `v * u ^ g` of a hub
- `flowerGraph'_dist_le` — the diameter is at most `(2 * v + 1) * u ^ g`

## Implementation notes

`dist_hub_le` is an induction on `g`. An old vertex `embed x` is within `u` times its
generation-`g` distance of a hub, by `lift_walk`. A new vertex sits on the short or long
path of a gadget, within `v / 2` steps of an embedded endpoint of its parent edge. That
gives `R (g + 1) ≤ u * R g + v / 2`, and `R g ≤ v * u ^ g` follows since `2 ≤ u`.

## Tags

flower graph, radius, diameter, rank
-/

variable {u v : ℕ}

/-- Every vertex of generation `g + 1` is either embedded from generation `g` or is a new
internal vertex of a gadget created at generation `g`. -/
private theorem flowerVert_succ_cases (g : ℕ) (x : FlowerVert u v (g + 1)) :
    (∃ y : FlowerVert u v g, x = FlowerVert.embed u v g y) ∨
      ∃ (parent : FlowerEdge u v g) (pos : Fin (u - 1) ⊕ Fin (v - 1)),
        x = .inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, pos⟩ := by
  rcases x with h | ⟨⟨k, hk⟩, parent, pos⟩
  · exact Or.inl ⟨.inl h, rfl⟩
  · by_cases hkg : k < g
    · exact Or.inl ⟨.inr ⟨⟨k, hkg⟩, parent, pos⟩, rfl⟩
    · obtain rfl : k = g := by omega
      exact Or.inr ⟨parent, pos, rfl⟩

/-- A chain of consecutive adjacencies gives walks between any two of its vertices. -/
private theorem chain_walk {V : Type*} (G : SimpleGraph V) (f : ℕ → V) (m : ℕ)
    (hf : ∀ n < m, G.Adj (f n) (f (n + 1))) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ m) :
    ∃ w : G.Walk (f a) (f b), w.length = b - a := by
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    exact ⟨.nil, rfl⟩
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · exact ⟨.nil, by simp⟩
    · obtain ⟨w, hw⟩ := ih (by omega) (by omega)
      exact ⟨w.append (.cons (hf b (by omega)) .nil), by simp [hw]; omega⟩

theorem rank_le_pow (hu : 1 < u) (huv : u ≤ v) (g : ℕ) (x : FlowerVert u v g) :
    FlowerVert.rank u v g x ≤ u ^ g := by
  induction g with
  | zero =>
    rcases x with ⟨_ | _ | n, h⟩ | ⟨⟨k, hk⟩, _⟩
    · simp [FlowerVert.rank]
    · simp [FlowerVert.rank]
    · omega
    · omega
  | succ g ih =>
    rcases flowerVert_succ_cases g x with ⟨y, rfl⟩ | ⟨parent, pos, rfl⟩
    · rw [rank_embed, pow_succ, Nat.mul_comm (u ^ g)]
      exact Nat.mul_le_mul_left _ (ih y)
    · have h1 := rank_edgeSrc_le_edgeTgt u v g hu huv parent
      have h2 := ih (edgeTgt u v g parent)
      have key : ∀ s t : ℕ, s ≤ t → t ≤ u ^ g → u * s ≤ u ^ (g + 1) := by
        intro s t hst ht
        rw [pow_succ, Nat.mul_comm (u ^ g)]; exact Nat.mul_le_mul_left _ (by omega)
      have key2 : ∀ s t : ℕ, s ≤ t → t ≤ u ^ g → s ≠ t → u * s + u ≤ u ^ (g + 1) := by
        intro s t hst ht hne
        rw [pow_succ, Nat.mul_comm (u ^ g), ← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ (by omega)
      have k1 := key _ _ h1 h2
      have k2 := key2 _ _ h1 h2
      rcases pos with i | j
      · rw [rank_new_short]
        split_ifs with hst
        · exact k1
        · have := k2 hst; have := i.isLt; omega
      · rw [rank_new_long]
        split_ifs with hst
        · exact k1
        · have := k2 hst
          have hj : (j.val + 1) * u / v ≤ u := by
            apply Nat.div_le_of_le_mul
            have hj' : j.val + 1 ≤ v := by have := j.isLt; omega
            exact Nat.mul_le_mul_right u hj'
          omega

/-- The rank changes by at most one along an edge, in either direction. -/
theorem rank_adj_le' (hu : 1 < u) (huv : u ≤ v) (g : ℕ) (a b : FlowerVert u v g)
    (hab : (flowerGraph' u v g).Adj a b) :
    FlowerVert.rank u v g a ≤ FlowerVert.rank u v g b + 1 := by
  exact rank_adj_le u v g hu huv b a hab.symm

/-- Discrete intermediate values: every `r ≤ u ^ g` is the rank of some vertex. -/
theorem exists_rank_eq (hu : 1 < u) (huv : u ≤ v) (g r : ℕ) (hr : r ≤ u ^ g) :
    ∃ x : FlowerVert u v g, FlowerVert.rank u v g x = r := by
  have key : ∀ {a b : FlowerVert u v g} (w : (flowerGraph' u v g).Walk a b),
      FlowerVert.rank u v g a ≤ r → r ≤ FlowerVert.rank u v g b →
        ∃ x : FlowerVert u v g, FlowerVert.rank u v g x = r := by
    intro a b w
    induction w with
    | @nil a => intro h1 h2; exact ⟨a, by omega⟩
    | @cons a c b hac tail ih =>
      intro h1 h2
      by_cases hra : FlowerVert.rank u v g a = r
      · exact ⟨a, hra⟩
      · have := rank_adj_le u v g hu huv a c hac
        exact ih (by omega) h2
  obtain ⟨w, -⟩ := flowerGraph'_walk_hubs u v g hu
  exact key w (by rw [rank_hub0]; omega) (by rw [rank_hub1]; exact hr)

/-- Radius invariant: every vertex has a walk to some hub of length `L` with
`2 * L + v ≤ v * u ^ g`. -/
private theorem hub_walk_invariant (hu : 1 < u) (huv : u ≤ v) (g : ℕ)
    (x : FlowerVert u v g) :
    ∃ (h : Fin 2) (w : (flowerGraph' u v g).Walk x (.inl h)),
      2 * w.length + v ≤ v * u ^ g := by
  induction g with
  | zero =>
    rcases x with h | ⟨⟨k, hk⟩, _⟩
    · exact ⟨h, .nil, by change 2 * 0 + v ≤ v * u ^ 0; simp⟩
    · omega
  | succ g ih =>
    -- embedded vertices
    have hemb : ∀ y : FlowerVert u v g, ∃ (h : Fin 2)
        (w : (flowerGraph' u v (g + 1)).Walk (FlowerVert.embed u v g y) (.inl h)),
        2 * w.length + u * v ≤ v * u ^ (g + 1) := by
      intro y
      obtain ⟨h, w, hw⟩ := ih y
      obtain ⟨w', hw'⟩ := lift_walk u v g hu w
      refine ⟨h, w', ?_⟩
      -- Tactics cannot rewrite inside `w'` (its endpoint is `embed (.inl h)`), so prove the
      -- bound for an arbitrary length and apply it.
      have key (L : ℕ) (hL : L = u * w.length) : 2 * L + u * v ≤ v * u ^ (g + 1) := by
        subst hL
        rw [pow_succ]
        nlinarith [Nat.mul_le_mul_left u hw]
      exact key _ hw'
    rcases flowerVert_succ_cases g x with ⟨y, rfl⟩ | ⟨parent, pos, rfl⟩
    · obtain ⟨h, w, hw⟩ := hemb y
      exact ⟨h, w, by nlinarith⟩
    · -- a new vertex is close to an embedded endpoint of its parent edge
      suffices hnear : ∃ (z : FlowerVert u v g)
          (w : (flowerGraph' u v (g + 1)).Walk
            (.inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, pos⟩) (FlowerVert.embed u v g z)),
          2 * w.length ≤ v by
        obtain ⟨z, w, hw⟩ := hnear
        obtain ⟨h, w', hw'⟩ := hemb z
        refine ⟨h, w.append w', ?_⟩
        nlinarith [SimpleGraph.Walk.length_append w w']
      rcases pos with i | j
      · let f : ℕ → FlowerVert u v (g + 1) := fun n =>
          if hn : n < u then edgeSrc u v (g + 1) (parent, .inl ⟨n, hn⟩)
          else FlowerVert.embed u v g (edgeTgt u v g parent)
        have hf : ∀ n < u, (flowerGraph' u v (g + 1)).Adj (f n) (f (n + 1)) := by
          intro n hn
          by_cases hn1 : n + 1 < u
          · simp only [f, dite_eq_left hn, dite_eq_left hn1]
            rw [← short_tgt_eq_succ_src u v g parent ⟨n, hn⟩ hn1]
            exact short_path_consecutive_adj u v g parent ⟨n, hn⟩
          · simp only [f, dite_eq_left hn, dite_eq_right hn1]
            have : (⟨n, hn⟩ : Fin u) = ⟨u - 1, by omega⟩ := Fin.ext (by simp; omega)
            rw [this, ← short_last_eq_embed_tgt u v g hu parent]
            exact short_path_consecutive_adj u v g parent ⟨u - 1, by omega⟩
        have hf0 : f 0 = FlowerVert.embed u v g (edgeSrc u v g parent) := by
          simp only [f, dite_eq_left (by omega : 0 < u)]
          exact short_first_eq_embed_src u v g hu parent
        have hfu : f u = FlowerVert.embed u v g (edgeTgt u v g parent) := by
          simp only [f, dite_eq_right (lt_irrefl u)]
        have hfi : f (i.val + 1) = .inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inl i⟩ := by
          simp only [f, dite_eq_left (by omega : i.val + 1 < u)]
          simp only [edgeSrc, edgeEndpoints, localSrc]
          rfl
        have hi := i.isLt
        by_cases hle : 2 * (i.val + 1) ≤ v
        · obtain ⟨w, hw⟩ := chain_walk _ f u hf 0 (i.val + 1) (by omega) (by omega)
          exact ⟨edgeSrc u v g parent, (w.copy hf0 hfi).reverse, by
            have := (w.copy hf0 hfi).length_reverse
            have := w.length_copy hf0 hfi
            omega⟩
        · obtain ⟨w, hw⟩ := chain_walk _ f u hf (i.val + 1) u (by omega) le_rfl
          exact ⟨edgeTgt u v g parent, w.copy hfi hfu, by
            have := w.length_copy hfi hfu
            omega⟩
      · let f : ℕ → FlowerVert u v (g + 1) := fun n =>
          if hn : n < v then edgeSrc u v (g + 1) (parent, .inr ⟨n, hn⟩)
          else FlowerVert.embed u v g (edgeTgt u v g parent)
        have hf : ∀ n < v, (flowerGraph' u v (g + 1)).Adj (f n) (f (n + 1)) := by
          intro n hn
          by_cases hn1 : n + 1 < v
          · simp only [f, dite_eq_left hn, dite_eq_left hn1]
            rw [← long_tgt_eq_succ_src u v g parent ⟨n, hn⟩ hn1]
            exact long_path_consecutive_adj u v g parent ⟨n, hn⟩
          · simp only [f, dite_eq_left hn, dite_eq_right hn1]
            have : (⟨n, hn⟩ : Fin v) = ⟨v - 1, by omega⟩ := Fin.ext (by simp; omega)
            rw [this, ← long_last_eq_embed_tgt u v g hu huv parent]
            exact long_path_consecutive_adj u v g parent ⟨v - 1, by omega⟩
        have hf0 : f 0 = FlowerVert.embed u v g (edgeSrc u v g parent) := by
          simp only [f, dite_eq_left (by omega : 0 < v)]
          exact long_first_eq_embed_src u v g hu huv parent
        have hfv : f v = FlowerVert.embed u v g (edgeTgt u v g parent) := by
          simp only [f, dite_eq_right (lt_irrefl v)]
        have hfj : f (j.val + 1) = .inr ⟨⟨g, Nat.lt_succ_of_le le_rfl⟩, parent, .inr j⟩ := by
          simp only [f, dite_eq_left (by omega : j.val + 1 < v)]
          simp only [edgeSrc, edgeEndpoints, localSrc]
          rfl
        have hj := j.isLt
        by_cases hle : 2 * (j.val + 1) ≤ v
        · obtain ⟨w, hw⟩ := chain_walk _ f v hf 0 (j.val + 1) (by omega) (by omega)
          exact ⟨edgeSrc u v g parent, (w.copy hf0 hfj).reverse, by
            have := (w.copy hf0 hfj).length_reverse
            have := w.length_copy hf0 hfj
            omega⟩
        · obtain ⟨w, hw⟩ := chain_walk _ f v hf (j.val + 1) v (by omega) le_rfl
          exact ⟨edgeTgt u v g parent, w.copy hfj hfv, by
            have := w.length_copy hfj hfv
            omega⟩

/-- Every vertex is within `v * u ^ g` of a hub. -/
theorem dist_hub_le (hu : 1 < u) (huv : u ≤ v) (g : ℕ) (x : FlowerVert u v g) :
    (flowerGraph' u v g).dist x (.hub0 u v g) ≤ v * u ^ g ∨
      (flowerGraph' u v g).dist x (.hub1 u v g) ≤ v * u ^ g := by
  obtain ⟨h, w, hw⟩ := hub_walk_invariant hu huv g x
  have hd := (flowerGraph' u v g).dist_le w
  have hle : (flowerGraph' u v g).dist x (.inl h) ≤ v * u ^ g := by omega
  rcases Fin.exists_fin_two.mp ⟨h, rfl⟩ with rfl | rfl
  · exact Or.inl hle
  · exact Or.inr hle

/-- The diameter of the generation-`g` flower is at most `(2 * v + 1) * u ^ g`. -/
theorem flowerGraph'_dist_le (hu : 1 < u) (huv : u ≤ v) (g : ℕ) (x y : FlowerVert u v g) :
    (flowerGraph' u v g).dist x y ≤ (2 * v + 1) * u ^ g := by
  have hconn := flowerGraph'_connected u v g hu huv
  have hhub := flowerGraph'_dist_hubs u v g hu huv
  have hhub' : (flowerGraph' u v g).dist (.hub1 u v g) (.hub0 u v g) = u ^ g := by
    rw [SimpleGraph.dist_comm]; exact hhub
  have hself : ∀ z : FlowerVert u v g, (flowerGraph' u v g).dist z z = 0 := fun z =>
    SimpleGraph.dist_self
  have tri : ∀ a b c : FlowerVert u v g, (flowerGraph' u v g).dist a c ≤
      (flowerGraph' u v g).dist a b + (flowerGraph' u v g).dist b c :=
    fun a b c => hconn.dist_triangle
  have hy := dist_hub_le hu huv g y
  rw [SimpleGraph.dist_comm (u := y), SimpleGraph.dist_comm (u := y)] at hy
  have hsum : (2 * v + 1) * u ^ g = v * u ^ g + u ^ g + v * u ^ g := by
    rw [Nat.add_mul, Nat.two_mul, Nat.add_mul, Nat.one_mul]; omega
  rw [hsum]
  rcases dist_hub_le hu huv g x with hx | hx <;> rcases hy with hy | hy
  · have := tri x (.hub0 u v g) y; have := hself (.hub0 u v g); omega
  · have := tri x (.hub0 u v g) y; have := tri (.hub0 u v g) (.hub1 u v g) y; omega
  · have := tri x (.hub1 u v g) y; have := tri (.hub1 u v g) (.hub0 u v g) y; omega
  · have := tri x (.hub1 u v g) y; omega
