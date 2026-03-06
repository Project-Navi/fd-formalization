/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.FlowerGraph
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Flower Graph Exact Counts

Exact formulas for the edge and vertex counts of (u,v)-flower graphs
at generation `g`. With `w = u + v`:

- **Edges:** `E_g = w^g`
- **Vertices:** `(w - 1) * N_g = (w - 2) * w^g + w`

These are proved by induction on `g` from the construction rule:
each edge is replaced by two parallel paths of lengths `u` and `v`,
contributing `(u - 1) + (v - 1) = w - 2` new internal vertices per
edge and multiplying the edge count by `w`.

## Main statements

- `flower_edge_count` — `E_g = w^g`
- `flower_vertex_count` — `(w - 1) * N_g = (w - 2) * w^g + w`

## References

- [Rozenfeld2007] §2, construction and counting formulas.
-/

-- TODO: State and prove edge_count and vertex_count once FlowerGraph
-- construction is defined.
--
-- The edge count E_g = w^g follows directly: each edge produces w
-- new edges (u edges on the short path + v edges on the long path).
--
-- The vertex count uses the recurrence:
--   N_{g+1} = N_g + (w - 2) * E_g
--            = N_g + (w - 2) * w^g
-- with N_0 = 2 (two hub vertices connected by a single edge).
-- Solving: (w-1) * N_g = (w-2) * w^g + w.
--
-- Real-valued wrappers for the headline theorem:
--   def V_count_real (u v g : ℕ) : ℝ := (N_g : ℝ)
-- Cast early, prove positivity lemmas here.
