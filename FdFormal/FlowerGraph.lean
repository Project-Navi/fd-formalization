/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.FlowerCounts

/-!
# (u,v)-Flower Graph — Structural Definitions

Hub vertices and vertex-type helpers for the (u,v)-flower network
family from Rozenfeld, Havlin & ben-Avraham (NJP 2007).

The log-ratio convergence theorem (in `FlowerDimension`) needs only the
counting formulas (`FlowerCounts`) and the hub-distance recurrence
(`FlowerDiameter`). The explicit `SimpleGraph` is built in
`FlowerConstruction`, whose `flowerGraph_dist_hub0_hub1` connects
`flowerHubDist` to `SimpleGraph.dist`; its hubs are the indices defined here.

## Main definitions

- `hub0`, `hub1` — the two distinguished hub vertices as `Fin` indices

## Main statements

- `two_le_flowerVertCount` — vertex count is at least 2
- `hub0_ne_hub1` — the two hubs are distinct

## Implementation notes

The hubs are the indices `0` and `1` of `Fin (flowerVertCount u v g)`, which exist because
`2 ≤ flowerVertCount u v g`. `flowerVertEquiv` in `FlowerConstruction` sends the
construction's hubs to exactly these indices.

## References

- [Rozenfeld2007] §2, construction and hub structure.

## Tags

flower graph, hub vertices, fractal network
-/

/-! ### Vertex count helpers -/

/-- The vertex count is at least 2 for all generations. -/
theorem two_le_flowerVertCount (u v g : ℕ) :
    2 ≤ flowerVertCount u v g := by
  induction g with
  | zero => simp
  | succ g ih =>
    simp only [flowerVertCount_succ]
    omega

/-! ### Hub vertices -/

/-- Hub vertex 0 at generation `g`. -/
def hub0 (u v g : ℕ) : Fin (flowerVertCount u v g) :=
  ⟨0, flowerVertCount_pos u v g⟩

/-- Hub vertex 1 at generation `g`. -/
def hub1 (u v g : ℕ) : Fin (flowerVertCount u v g) :=
  ⟨1, two_le_flowerVertCount u v g⟩

/-- The two hub vertices are distinct. -/
@[simp]
theorem hub0_ne_hub1 (u v g : ℕ) : hub0 u v g ≠ hub1 u v g := by
  simp [hub0, hub1, Fin.ext_iff]
