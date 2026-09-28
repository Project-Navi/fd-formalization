# (u,v)-flower dimensions in Lean 4

A Lean 4 and Mathlib (v4.34.1) formalization about the (u,v)-flowers of Rozenfeld, Havlin and ben-Avraham. The main results take `1 < u` and `u ≤ v` as hypotheses. Documentation: [project-navi.github.io/fd-formalization](https://project-navi.github.io/fd-formalization/).

- `flowerDimension` (`FdFormal/FlowerDimension.lean`): for the vertex count `N_g` and hub distance `L_g`, both defined by recurrences, `log N_g / log L_g` tends to `log (u + v) / log u`.
- `flowerGraph_dist_hub0_hub1` (`FdFormal/FlowerConstruction.lean`): in the constructed graph `flowerGraph u v g hu huv` on `Fin N_g`, the distance between `hub0` and `hub1` (indices 0 and 1) is `u ^ g`.
- `flowerGraph_hasLogRatioDimension` (`FdFormal/FlowerGraphDimension.lean`): so these graphs have log-ratio dimension `log (u + v) / log u` (`HasLogRatioDimension`).
- `flowerGraph_hasBoxDimension` (`FdFormal/FlowerBoxDimension.lean`): these graphs also have box-counting dimension `log (u + v) / log u` (`HasBoxDimension`). Boxes are vertex sets of diameter `< ℓ` (Song, Havlin and Makse), the diameters diverge, and the limit of `log N_B(G_g, ℓ_g) / log (diam G_g / ℓ_g)` is taken along every scale sequence `ℓ_g` with `diam G_g / ℓ_g → ∞`, so it does not depend on a choice of scales and is unique. This is the dimension the paper identifies with the log-ratio limit.

Not covered: `u = 1`, the transfractal case. There the hub distance is `1 ^ g = 1` and the diameter grows only linearly in `g`, so there is no length scale factor `u > 1` whose logarithm could serve as the denominator.

## Verify

```bash
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true FdFormal/Verify.lean
```

`FdFormal/Verify.lean` prints the axioms of 52 declarations, including all four results; CI requires each to use only `propext`, `Classical.choice` and `Quot.sound`.

## Credit and license

Formalization by Nelson Spence. Aristotle (Harmonic) proved leaf lemmas and simplified proofs, and proved the box-counting modules against hand-written definitions and statements; Claude assisted with Lean. For the mathematics, cite H. D. Rozenfeld, S. Havlin and D. ben-Avraham, "Fractal and transfractal recursive scale-free nets", *New J. Phys.* 9, 175 (2007), and for box covering C. Song, S. Havlin and H. A. Makse, "Self-similarity of complex networks", *Nature* 433, 392 (2005). Apache 2.0; see [LICENSE](LICENSE).
