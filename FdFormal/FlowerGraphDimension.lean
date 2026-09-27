/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.FlowerConstruction
import FdFormal.FlowerDimension
import FdFormal.FlowerLogRatio

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Log-Ratio Dimension of the Flower Graphs

The explicit (u,v)-flower graphs `flowerGraph u v g` have log-ratio dimension
`log (u + v) / log u`, measured between the hubs `hub0` and `hub1`. This combines the
arithmetic limit `flowerDimension` with the hub distance `flowerGraph_dist_hub0_hub1` and
`Fintype.card (Fin n) = n`.

The limit is the box-counting dimension of the flowers in the physics literature; that
identification is not formalized.

## Main statements

- `flowerGraph_hasLogRatioDimension` — `HasLogRatioDimension` for the flower graphs

## References

- [Rozenfeld2007] §2, dimension as log-ratio limit for flower graphs.

## Tags

flower graph, log-ratio dimension
-/

open Real

/-- **The flower graphs have log-ratio dimension `log (u + v) / log u`**, measured between
the hubs `hub0` and `hub1`. -/
theorem flowerGraph_hasLogRatioDimension (u v : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    HasLogRatioDimension (fun g ↦ flowerGraph u v g hu huv) (hub0 u v) (hub1 u v)
      (log ↑(u + v) / log ↑u) := by
  simpa [HasLogRatioDimension, flowerGraph_dist_hub0_hub1, flowerHubDist_eq_pow] using
    flowerDimension u v hu huv
