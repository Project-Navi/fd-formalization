/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.FlowerGraph
import FdFormal.FlowerLog
import FdFormal.FlowerLogRatio
import FdFormal.FlowerDimension
import FdFormal.FlowerConstruction
import FdFormal.FlowerGraphDimension
import FdFormal.PathGraphDist
import FdFormal.FlowerBoxDimension

/-!
# Axiom Dashboard

Displays the axiom dependencies of all verified declarations.
Run `lake env lean FdFormal/Verify.lean` to see the output.

All declarations should depend only on `[propext, Classical.choice, Quot.sound]`.

## Main definitions

None.

## Main statements

None: every line is a `#print axioms` record, one per headline result or cited supporting
declaration. CI counts the records and checks each against the allowlist.

## Implementation notes

This file is imported by the root, so `lake build` compiles it; CI also runs it with
warnings as errors.

## References

None.

## Tags

verification, axioms, soundness
-/

-- Counting formulas (FlowerCounts)
#print axioms flowerEdgeCount_eq_pow
#print axioms flowerVertCount_eq
#print axioms flowerVertCount_pos
#print axioms flowerVertCount_lower
#print axioms flowerVertCount_upper

-- Hub distance (FlowerHubDist)
#print axioms flowerHubDist_eq_pow
#print axioms flowerHubDist_pos

-- Monotonicity (FlowerCounts / FlowerHubDist)
#print axioms flowerEdgeCount_pos
#print axioms flowerEdgeCount_strict_mono
#print axioms flowerVertCount_strict_mono
#print axioms flowerVertCount_cast_eq
#print axioms flowerHubDist_strict_mono
#print axioms flowerHubDist_cast_eq_pow

-- Hub vertices (FlowerGraph)
#print axioms hub0
#print axioms hub1
#print axioms two_le_flowerVertCount
#print axioms hub0_ne_hub1

-- Log identities and squeeze bounds (FlowerLog)
#print axioms log_flowerHubDist_eq
#print axioms log_flowerEdgeCount_eq
#print axioms log_flowerVertCount_residual_lower
#print axioms log_flowerVertCount_residual_upper

-- Bridge target definition (FlowerLogRatio)
#print axioms HasLogRatioDimension

-- F2 bridge: SimpleGraph construction + distance (FlowerConstruction)
#print axioms GadgetPos
#print axioms LocalEdge
#print axioms FlowerEdge
#print axioms FlowerVert
#print axioms flowerAdj'
#print axioms flowerGraph'
#print axioms flowerGraph'_adj_iff
#print axioms gadgetInternal_card
#print axioms flowerVert_card
#print axioms flowerVertEquiv
#print axioms flowerGraph
#print axioms flowerGraph'_connected
#print axioms flowerGraph'_dist_hubs
#print axioms flowerGraph_dist_hubs

-- Log-ratio convergence (FlowerDimension)
#print axioms flowerDimension

-- Hubs on `Fin` (FlowerConstruction)
#print axioms flowerVertEquiv_hub0
#print axioms flowerVertEquiv_hub1
#print axioms flowerGraph_dist_hub0_hub1

-- Log-ratio dimension of the flower graphs (FlowerGraphDimension)
#print axioms flowerGraph_hasLogRatioDimension

-- Path graph distances (PathGraphDist)
#print axioms SimpleGraph.pathGraph_edist
#print axioms SimpleGraph.pathGraph_dist
#print axioms SimpleGraph.pathGraph_edist_zero_last
#print axioms SimpleGraph.pathGraph_dist_zero_last

-- Box covering (BoxCounting)
#print axioms SimpleGraph.IsBox
#print axioms SimpleGraph.boxCount
#print axioms SimpleGraph.boxCount_le_of_cover
#print axioms SimpleGraph.le_boxCount_of_separated
#print axioms SimpleGraph.boxCount_anti
#print axioms SimpleGraph.boxCount_pos
#print axioms SimpleGraph.boxCount_le_card
#print axioms SimpleGraph.Iso.boxCount_eq
#print axioms SimpleGraph.Hom.dist_le
#print axioms SimpleGraph.le_add_dist_of_lipschitz
#print axioms SimpleGraph.tent_lipschitz

-- Scaling lemma (BoxScaling)
#print axioms Real.tendsto_log_count_div_log_scale

-- Cell decomposition (FlowerCells)
#print axioms FlowerEdge.graft
#print axioms FlowerEdge.trunc
#print axioms FlowerEdge.suffix
#print axioms cellEmbed
#print axioms cellHom
#print axioms cellEmbed_injective
#print axioms exists_cellEmbed_eq
#print axioms cellEmbed_eq_of_ne
#print axioms cellPotential_lipschitz

-- Rank and radius (FlowerRadius)
#print axioms rank_le_pow
#print axioms exists_rank_eq
#print axioms dist_hub_le
#print axioms flowerGraph'_dist_le

-- Box-counting dimension of the flower graphs (FlowerBoxDimension)
#print axioms HasBoxDimension
#print axioms HasBoxDimension.unique
#print axioms flower_boxCount_ge
#print axioms flower_boxCount_le
#print axioms flowerGraph'_diam_bounds
#print axioms flowerGraph_hasBoxDimension
