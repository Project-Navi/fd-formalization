# (u,v)-flower log-ratio limit in Lean 4

A Lean 4 and Mathlib (v4.28.0) formalization about the (u,v)-flowers of Rozenfeld, Havlin and ben-Avraham. The main results take `1 < u` and `u ≤ v` as hypotheses; `u = 1` is not covered. Documentation: [project-navi.github.io/fd-formalization](https://project-navi.github.io/fd-formalization/).

- `flowerDimension` (`FdFormal/FlowerDimension.lean`): for the vertex count `N_g` and hub distance `L_g`, both defined by recurrences, `log N_g / log L_g` tends to `log (u + v) / log u`.
- `flowerGraph_dist_hub0_hub1` (`FdFormal/FlowerConstruction.lean`): in the constructed graph `flowerGraph u v g hu huv` on `Fin N_g`, the distance between `hub0` and `hub1` (indices 0 and 1) is `u ^ g`.
- `flowerGraph_hasLogRatioDimension` (`FdFormal/FlowerGraphDimension.lean`): so these graphs have log-ratio dimension `log (u + v) / log u` (`HasLogRatioDimension`).

Not formalized: box-counting dimension, with which the paper identifies this limit.

## Verify

```bash
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true FdFormal/Verify.lean
```

`FdFormal/Verify.lean` prints the axioms of 33 declarations, including all three results; CI requires each to use only `propext`, `Classical.choice` and `Quot.sound`.

## Credit and license

Formalization by Nelson Spence; Aristotle (Harmonic) proved several leaf lemmas and simplified proofs, and Claude assisted with Lean. For the mathematics, cite H. D. Rozenfeld, S. Havlin and D. ben-Avraham, "Fractal and transfractal recursive scale-free nets", *New J. Phys.* 9, 175 (2007). Apache 2.0; see [LICENSE](LICENSE).
