/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.BoxCounting
import FdFormal.BoxScaling
import FdFormal.FlowerCells
import FdFormal.FlowerRadius
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
# Box-counting dimension of the (u,v)-flowers

The (u,v)-flower graphs have box-counting dimension `log (u + v) / log u`, measured
against their diameter along every scale sequence `ℓ_g` with `diam G_g / ℓ_g → ∞`.

## Main definitions

- `HasBoxDimension` — box-counting dimension of a graph family

## Main statements

- `flower_boxCount_ge` — for `0 < j`, the `(u + v) ^ k` cell centers are `u ^ j / 2`-separated
- `flower_boxCount_le` — the `(u + v) ^ k` cells are boxes of size `(2v + 1) u ^ j + 1`
- `HasBoxDimension.unique` — a family has at most one box-counting dimension
- `HasBoxDimension.tendsto_log_card_div_log_diam` — it contains the mass-scaling law
- `flowerGraph_hasBoxDimension` — the flowers have box-counting dimension
  `log (u + v) / log u`

## Implementation notes

Lower bound: in each cell pick `cellEmbed k e j m`, where `rank m = u ^ j / 2`
(`exists_rank_eq`). The tent `min rank (u ^ j - rank)` is 1-Lipschitz (`tent_lipschitz`)
and vanishes at the hubs, so `cellPotential` of it is 1-Lipschitz on the whole graph
(`cellPotential_lipschitz`). It is `u ^ j / 2` at the center of `e` and `0` at the center
of any other cell (`cellEmbed_eq_of_ne`; `m` is not a hub), so centers are at distance
`≥ u ^ j / 2` (`le_add_dist_of_lipschitz`), and `le_boxCount_of_separated` applies.

Upper bound: each cell is the image of the generation-`j` flower under the homomorphism
`cellHom`, so its diameter is at most `(2v + 1) u ^ j` (`Hom.dist_le`,
`flowerGraph'_dist_le`); the cells cover the graph (`exists_cellEmbed_eq`), so
`boxCount_le_of_cover` applies.

Assembly: `Real.tendsto_log_count_div_log_scale` with `b = u + v`, `L = diam`
(`u ^ g ≤ diam ≤ (2v + 1) u ^ g`), transported to `Fin` by `Iso.boxCount_eq`.

## References

- [Rozenfeld2007] the flowers' box-counting dimension `log (u + v) / log u`.
- [SongHavlinMakse2005] box covering of complex networks.

## Tags

flower graph, box-counting dimension, fractal dimension
-/

open Filter Real Topology

/-- A graph family `G g` has box-counting dimension `d` if its diameters diverge and, along
every scale sequence `ℓ_g ≥ 1` with `diam (G g) / ℓ_g → ∞`,
`log N_B(G g, ℓ_g) / log (diam (G g) / ℓ_g) → d`. Divergence makes `ℓ_g = 1` admissible,
so `d` is unique (`HasBoxDimension.unique`). The graphs must be finite, so `boxCount` never
takes its junk value. -/
def HasBoxDimension {V : ℕ → Type*} (G : (g : ℕ) → SimpleGraph (V g)) (d : ℝ) : Prop :=
  (∀ g, Finite (V g)) ∧ Tendsto (fun g ↦ ((G g).diam : ℝ)) atTop atTop ∧
  ∀ ℓ : ℕ → ℕ, (∀ g, 0 < ℓ g) →
    Tendsto (fun g ↦ ((G g).diam : ℝ) / ℓ g) atTop atTop →
    Tendsto (fun g ↦ log ((G g).boxCount (ℓ g) : ℝ) / log (((G g).diam : ℝ) / ℓ g))
      atTop (𝓝 d)

/-- The box-counting dimension of a family is unique: the scales `ℓ_g = 1` are admissible
because the diameters diverge. -/
theorem HasBoxDimension.unique {V : ℕ → Type*} {G : (g : ℕ) → SimpleGraph (V g)} {d d' : ℝ}
    (h : HasBoxDimension G d) (h' : HasBoxDimension G d') : d = d' := by
  have hs : Tendsto (fun g ↦ ((G g).diam : ℝ) / (((fun _ ↦ 1) : ℕ → ℕ) g : ℝ)) atTop atTop := by
    simpa using h.2.1
  exact tendsto_nhds_unique (h.2.2 _ (fun _ ↦ Nat.one_pos) hs) (h'.2.2 _ (fun _ ↦ Nat.one_pos) hs)

/-- Box-counting dimension contains the mass-scaling law: at scale `ℓ_g = 1` every box is a
single vertex, so `log |V_g| / log (diam G_g) → d`. -/
theorem HasBoxDimension.tendsto_log_card_div_log_diam {V : ℕ → Type*} [∀ g, Fintype (V g)]
    {G : (g : ℕ) → SimpleGraph (V g)} {d : ℝ} (h : HasBoxDimension G d) :
    Tendsto (fun g ↦ log (Fintype.card (V g) : ℝ) / log ((G g).diam : ℝ)) atTop (𝓝 d) := by
  have hs : Tendsto (fun g ↦ ((G g).diam : ℝ) / (((fun _ ↦ 1) : ℕ → ℕ) g : ℝ)) atTop atTop := by
    simpa using h.2.1
  simpa [SimpleGraph.boxCount_one] using h.2.2 _ (fun _ ↦ Nat.one_pos) hs

variable {u v : ℕ}

/-- **Lower bound.** The generation-`(k + j)` flower needs at least `(u + v) ^ k` boxes of
size `u ^ j / 2`. -/
theorem flower_boxCount_ge (hu : 1 < u) (huv : u ≤ v) (k j : ℕ) (hj : 0 < j) :
    (u + v) ^ k ≤ (flowerGraph' u v (k + j)).boxCount (u ^ j / 2) := by
  have hconn := flowerGraph'_connected u v (k + j) hu huv
  have hu2 : 2 ≤ u ^ j := le_trans hu (Nat.le_self_pow hj.ne' u)
  obtain ⟨m, hm⟩ := exists_rank_eq hu huv j (u ^ j / 2) (Nat.div_le_self _ _)
  let φ : FlowerVert u v j → ℕ := fun x ↦
    min (FlowerVert.rank u v j x) (u ^ j - FlowerVert.rank u v j x)
  have hφ : ∀ a b, (flowerGraph' u v j).Adj a b → φ a ≤ φ b + 1 :=
    fun a b hab ↦ SimpleGraph.tent_lipschitz (u ^ j) (rank_adj_le' hu huv j) a b hab
  have h0 : φ (.hub0 u v j) = 0 := by simp [φ, rank_hub0]
  have h1 : φ (.hub1 u v j) = 0 := by simp [φ, rank_hub1]
  have hφm : φ m = u ^ j / 2 := by simp only [φ, hm]; omega
  let E := (Fintype.equivFin (FlowerEdge u v k)).trans (finCongr (flowerEdge_card u v k))
  refine SimpleGraph.le_boxCount_of_separated (by omega)
    (fun i ↦ cellEmbed k (E.symm i) j m) fun a b hab ↦ ?_
  have hne : E.symm a ≠ E.symm b := E.symm.injective.ne hab
  have hlip := SimpleGraph.le_add_dist_of_lipschitz
    (cellPotential_lipschitz k (E.symm a) j φ hφ h0 h1)
    (hconn.preconnected (cellEmbed k (E.symm a) j m) (cellEmbed k (E.symm b) j m))
  rw [cellPotential_cellEmbed, hφm, cellPotential_eq_zero_of_ne k hne j φ h0 h1 m,
    zero_add] at hlip
  rw [← (hconn.preconnected _ _).coe_dist_eq_edist]
  exact_mod_cast hlip

/-- **Upper bound.** The generation-`(k + j)` flower is covered by `(u + v) ^ k` boxes of
size `(2 * v + 1) * u ^ j + 1`. -/
theorem flower_boxCount_le (hu : 1 < u) (huv : u ≤ v) (k j : ℕ) :
    (flowerGraph' u v (k + j)).boxCount ((2 * v + 1) * u ^ j + 1) ≤ (u + v) ^ k := by
  have hconn := flowerGraph'_connected u v j hu huv
  have hconn' := flowerGraph'_connected u v (k + j) hu huv
  let E := (Fintype.equivFin (FlowerEdge u v k)).trans (finCongr (flowerEdge_card u v k))
  refine SimpleGraph.boxCount_le_of_cover (fun i ↦ Set.range (cellEmbed k (E.symm i) j))
    ?_ fun x ↦ ?_
  · rintro i _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have h1 : (flowerGraph' u v (k + j)).dist (cellEmbed k (E.symm i) j x)
        (cellEmbed k (E.symm i) j y) ≤ (flowerGraph' u v j).dist x y :=
      SimpleGraph.Hom.dist_le (cellHom k (E.symm i) j) (hconn.preconnected x y)
    have h2 := flowerGraph'_dist_le hu huv j x y
    rw [← (hconn'.preconnected _ _).coe_dist_eq_edist]
    exact_mod_cast (show _ < (2 * v + 1) * u ^ j + 1 by omega)
  · obtain ⟨e, y, rfl⟩ := exists_cellEmbed_eq hu k j x
    exact ⟨E e, y, by simp⟩

/-- The diameter of the generation-`g` flower is between `u ^ g` and `(2v + 1) u ^ g`. -/
theorem flowerGraph'_diam_bounds (hu : 1 < u) (huv : u ≤ v) (g : ℕ) :
    u ^ g ≤ (flowerGraph' u v g).diam ∧ (flowerGraph' u v g).diam ≤ (2 * v + 1) * u ^ g := by
  have hconn := flowerGraph'_connected u v g hu huv
  have : Nonempty (FlowerVert u v g) := ⟨.hub0 u v g⟩
  refine ⟨?_, ?_⟩
  · rw [← flowerGraph'_dist_hubs u v g hu huv]
    exact SimpleGraph.dist_le_diam (SimpleGraph.connected_iff_ediam_ne_top.mp hconn)
  · obtain ⟨a, b, hab⟩ := (flowerGraph' u v g).exists_dist_eq_diam
    rw [← hab]
    exact flowerGraph'_dist_le hu huv g a b

/-- The `Fin`-indexed flower is isomorphic to the structured one. -/
theorem nonempty_flowerGraph_iso (hu : 1 < u) (huv : u ≤ v) (g : ℕ) :
    Nonempty (flowerGraph' u v g ≃g flowerGraph u v g hu huv) :=
  ⟨{ toEquiv := flowerVertEquiv u v g hu huv
     map_rel_iff' := by intro a b; simp [flowerGraph] }⟩

/-- An isomorphism from a finite connected graph does not increase the diameter. -/
private lemma iso_diam_le {V W : Type*} [Finite V] [Nonempty W] {G : SimpleGraph V}
    {G' : SimpleGraph W} (φ : G ≃g G') (hG : G.Connected) : G'.diam ≤ G.diam := by
  have : Nonempty V := ⟨φ.symm (Classical.arbitrary W)⟩
  obtain ⟨a, b, hab⟩ := G'.exists_dist_eq_diam
  rw [← hab]
  have h : G'.dist (φ (φ.symm a)) (φ (φ.symm b)) ≤ G.dist (φ.symm a) (φ.symm b) :=
    SimpleGraph.Hom.dist_le φ.toHom (hG.preconnected (φ.symm a) (φ.symm b))
  rw [φ.apply_symm_apply, φ.apply_symm_apply] at h
  exact h.trans (SimpleGraph.dist_le_diam (SimpleGraph.connected_iff_ediam_ne_top.mp hG))

/-- Lower bound at the scales `u ^ m`, up to the factor `u + v`. -/
private lemma flower_count_lower (hu : 1 < u) (huv : u ≤ v) (g m : ℕ) (hm : m ≤ g) :
    (u + v) ^ (g - m) ≤ (u + v) * (flowerGraph' u v g).boxCount (u ^ m) := by
  rcases hm.lt_or_eq with hlt | rfl
  · obtain ⟨k, rfl⟩ : ∃ k, g = k + (m + 1) := ⟨g - (m + 1), by omega⟩
    have h1 := flower_boxCount_ge hu huv k (m + 1) (by omega)
    have hpos : 0 < u ^ m := by positivity
    have h2 : u ^ m ≤ u ^ (m + 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num), pow_succ]
      exact Nat.mul_le_mul_left _ hu
    have h3 := (flowerGraph' u v (k + (m + 1))).boxCount_anti hpos h2
    rw [show k + (m + 1) - m = k + 1 by omega, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ (h1.trans h3)
  · have : Nonempty (FlowerVert u v m) := ⟨.hub0 u v m⟩
    have := (flowerGraph' u v m).boxCount_pos (ℓ := u ^ m) (by positivity)
    simp only [Nat.sub_self, pow_zero]
    nlinarith

/-- Upper bound at the scales `u ^ m`, up to the factor `2 (u + v) ^ s`. -/
private lemma flower_count_upper (hu : 1 < u) (huv : u ≤ v) {s : ℕ} (hs : 2 * v + 2 ≤ u ^ s)
    (g m : ℕ) (hm : m ≤ g) :
    (flowerGraph' u v g).boxCount (u ^ m) ≤ 2 * (u + v) ^ s * (u + v) ^ (g - m) := by
  rcases le_or_gt s m with hsm | hsm
  · obtain ⟨k, rfl⟩ : ∃ k, g = k + (m - s) := ⟨g - (m - s), by omega⟩
    have h1 := flower_boxCount_le hu huv k (m - s)
    have hp : 0 < u ^ (m - s) := by positivity
    have hum : u ^ m = u ^ s * u ^ (m - s) := by rw [← pow_add]; congr 1; omega
    have h2 : (2 * v + 1) * u ^ (m - s) + 1 ≤ u ^ m := by rw [hum]; nlinarith
    have h3 := (flowerGraph' u v (k + (m - s))).boxCount_anti (by omega) h2
    have hk : (u + v) ^ k = (u + v) ^ s * (u + v) ^ (k + (m - s) - m) := by
      rw [← pow_add]; congr 1; omega
    rw [mul_assoc, ← hk]
    omega
  · have h1 := (flowerGraph' u v g).boxCount_le_card (ℓ := u ^ m) (by positivity)
    rw [flowerVert_card u v g hu huv] at h1
    have h2 := flowerVertCount_upper u v g hu huv
    rw [show 2 * (u + v - 1) * (u + v) ^ g = (u + v - 1) * (2 * (u + v) ^ g) by ring] at h2
    have h3 := Nat.le_of_mul_le_mul_left h2 (by omega)
    have h4 : (u + v) ^ g = (u + v) ^ m * (u + v) ^ (g - m) := by
      rw [← pow_add]; congr 1; omega
    have h5 : (u + v) ^ m ≤ (u + v) ^ s := Nat.pow_le_pow_right (by omega) hsm.le
    have h6 := Nat.mul_le_mul_right ((u + v) ^ (g - m)) h5
    rw [← h4] at h6
    rw [mul_assoc]
    omega

/-- **The flowers have box-counting dimension `log (u + v) / log u`.** -/
theorem flowerGraph_hasBoxDimension (hu : 1 < u) (huv : u ≤ v) :
    HasBoxDimension (fun g ↦ flowerGraph u v g hu huv) (log ↑(u + v) / log ↑u) := by
  have hdiam : ∀ g, (flowerGraph u v g hu huv).diam = (flowerGraph' u v g).diam := by
    intro g
    obtain ⟨φ⟩ := nonempty_flowerGraph_iso hu huv g
    have hc := flowerGraph'_connected u v g hu huv
    have : Nonempty (FlowerVert u v g) := ⟨.hub0 u v g⟩
    have : Nonempty (Fin (flowerVertCount u v g)) := ⟨φ (.hub0 u v g)⟩
    exact le_antisymm (iso_diam_le φ hc) (iso_diam_le φ.symm (φ.connected_iff.mp hc))
  refine ⟨fun g ↦ inferInstance, ?_, fun ℓ hℓ hscale ↦ ?_⟩
  · -- the diameters diverge, since `u ^ g ≤ diam`
    simp only [hdiam]
    refine tendsto_atTop_mono (fun g ↦ ?_) (tendsto_pow_atTop_atTop_of_one_lt
      (by exact_mod_cast hu : (1 : ℝ) < u))
    exact_mod_cast (flowerGraph'_diam_bounds hu huv g).1
  have hbox : ∀ g n, (flowerGraph u v g hu huv).boxCount n =
      (flowerGraph' u v g).boxCount n :=
    fun g n ↦ (nonempty_flowerGraph_iso hu huv g).some.boxCount_eq n
  simp only [hdiam, hbox] at hscale ⊢
  obtain ⟨s, hs⟩ : ∃ s, 2 * v + 2 ≤ u ^ s := ⟨2 * v + 2, (Nat.lt_pow_self hu).le⟩
  have hX : 1 ≤ (u + v) ^ s := Nat.one_le_pow _ _ (by omega)
  set X := (u + v) ^ s
  have hK : 2 * X * (u + v) ≤ (2 * v + 1) * (2 * X * (u + v)) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hC1 : u + v ≤ (2 * v + 1) * (2 * X * (u + v)) :=
    (Nat.le_mul_of_pos_left _ (by omega)).trans hK
  have hC2 : 2 * X ≤ (2 * v + 1) * (2 * X * (u + v)) :=
    (Nat.le_mul_of_pos_right _ (by omega)).trans hK
  have hC3 : 2 * v + 1 ≤ (2 * v + 1) * (2 * X * (u + v)) :=
    Nat.le_mul_of_pos_right _ (by positivity)
  refine Real.tendsto_log_count_div_log_scale u (u + v) ((2 * v + 1) * (2 * X * (u + v))) hu
    (by omega) (by positivity) (fun g n ↦ (flowerGraph' u v g).boxCount n)
    (fun g _ _ h h' ↦ SimpleGraph.boxCount_anti h h') (fun g m hm ↦ ?_) (fun g m hm ↦ ?_)
    (fun g ↦ (flowerGraph' u v g).diam) (fun g ↦ ?_) ℓ hℓ hscale
  · exact (flower_count_lower hu huv g m hm).trans (Nat.mul_le_mul_right _ hC1)
  · exact (flower_count_upper hu huv hs g m hm).trans (Nat.mul_le_mul_right _ hC2)
  · obtain ⟨h1, h2⟩ := flowerGraph'_diam_bounds hu huv g
    exact ⟨h1, h2.trans (Nat.mul_le_mul_right _ hC3)⟩
