/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.GraphBall
import FdFormal.FlowerDimension

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Axiom Dashboard

Displays the axiom dependencies of all verified declarations.
Run `lake env lean FdFormal/Verify.lean` to see the output.

All declarations should depend only on `[propext, Classical.choice, Quot.sound]`
with no `sorryAx`.
-/

-- Upstream candidate (GraphBall)
#print axioms SimpleGraph.ball
#print axioms SimpleGraph.mem_ball
#print axioms SimpleGraph.ball_mono
#print axioms SimpleGraph.center_mem_ball

-- Flower dimension theorems will be added here as they are proved:
-- #print axioms flower_edge_count
-- #print axioms flower_vertex_count
-- #print axioms flower_diam_eq
-- #print axioms flower_dimension
