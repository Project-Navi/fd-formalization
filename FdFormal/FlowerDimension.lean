/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import FdFormal.FlowerCounts
import FdFormal.FlowerDiameter
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fractal Dimension of (u,v)-Flower Graphs

The fractal dimension of the (u,v)-flower family (for `1 < u`, `u ≤ v`)
is `d_B = Real.log (u + v) / Real.log u`.

This is derived from the exact growth laws:
- `|V_g|` grows like `(u+v)^g` (from `FlowerCounts`)
- `L_g = u^g` (from `FlowerDiameter`)

So `Real.log |V_g| / Real.log L_g` → `Real.log (u+v) / Real.log u`
as `g → ∞`.

## Main statements

- `flower_dimension` — the headline theorem:
  `Filter.Tendsto (fun g ↦ Real.log (V_count_real u v g) /
    Real.log (L_diam_real u v g))
    Filter.atTop (nhds (Real.log (u + v) / Real.log u))`

## Implementation notes

Counts and diameters are cast to `ℝ` via explicit wrapper definitions
(`V_count_real`, `L_diam_real`) defined in `FlowerCounts` and
`FlowerDiameter`. This avoids implicit coercion fights.

The proof uses:
- `Real.log_pow` — `Real.log (x ^ n) = n * Real.log x`
- `Real.log_pos` — `1 < x → 0 < Real.log x`
- `Filter.Tendsto` for the limit statement

The u = 1 case is excluded by hypothesis (`1 < u`). The source
treatment identifies u = 1 as transfractal with infinite d_B.

## References

- [Rozenfeld2007] Theorem 1, fractal dimension formula.
- [Spence2026] navi-fractal calibration against this formula.
-/

-- TODO: State and prove flower_dimension once FlowerCounts and
-- FlowerDiameter provide the exact formulas.
--
-- Proof sketch:
--   Real.log (V_count_real u v g) / Real.log (L_diam_real u v g)
--   = Real.log (C * (u+v)^g) / Real.log (u^g)      [by FlowerCounts]
--   = Real.log (C * (u+v)^g) / (g * Real.log u)     [by log_pow]
--   = (Real.log C + g * Real.log (u+v)) / (g * Real.log u)  [by log_mul]
--   → Real.log (u+v) / Real.log u  as g → ∞         [C term vanishes]
