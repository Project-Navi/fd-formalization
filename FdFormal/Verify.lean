/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.GraphBall
import FdFormal.FlowerGraph
import FdFormal.FlowerLog
import FdFormal.FlowerLogRatio
import FdFormal.FlowerDimension
import FdFormal.FlowerConstruction

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Axiom Dashboard

Displays the axiom dependencies of all verified declarations.
Run `lake env lean FdFormal/Verify.lean` to see the output.

All declarations should depend only on `[propext, Classical.choice, Quot.sound]`
with no `sorryAx`.

## Tags

verification, axioms, soundness
-/

-- Upstream candidate (GraphBall)
#print axioms SimpleGraph.ball
#print axioms SimpleGraph.mem_ball
#print axioms SimpleGraph.ball_mono
#print axioms SimpleGraph.center_mem_ball

-- Counting formulas (FlowerCounts)
#print axioms flowerEdgeCount_eq_pow
#print axioms flowerVertCount_eq
#print axioms flowerVertCount_pos
#print axioms flowerVertCount_lower
#print axioms flowerVertCount_upper

-- Hub distance (FlowerDiameter)
#print axioms flowerHubDist_eq_pow
#print axioms flowerHubDist_pos

-- Monotonicity (FlowerCounts / FlowerDiameter)
#print axioms flowerEdgeCount_pos
#print axioms flowerEdgeCount_strict_mono
#print axioms flowerVertCount_strict_mono
#print axioms flowerVertCount_cast_eq
#print axioms flowerHubDist_strict_mono
#print axioms flowerHubDist_cast_eq_pow

-- Hub vertices (FlowerGraph)
#print axioms hub0_ne_hub1

-- Log identities and squeeze bounds (FlowerLog)
#print axioms log_flowerHubDist_eq
#print axioms log_flowerEdgeCount_eq
#print axioms log_flowerVertCount_residual_lower
#print axioms log_flowerVertCount_residual_upper

-- Bridge target definition (FlowerLogRatio)
#print axioms HasLogRatioDimension

-- F2 bridge: SimpleGraph construction + distance (FlowerConstruction)
#print axioms flowerGraph'_connected
#print axioms flowerGraph'_dist_hubs
#print axioms flowerGraph_dist_hubs

-- Log-ratio convergence (FlowerDimension)
#print axioms flowerDimension
