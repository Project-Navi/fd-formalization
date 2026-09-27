# (u,v)-flower log-ratio limit in Lean 4

A Lean 4 and Mathlib (v4.28.0) formalization about the (u,v)-flowers of Rozenfeld, Havlin and ben-Avraham. Both main results take `1 < u` and `u ≤ v` as hypotheses; `u = 1` is not covered.

- `flowerDimension` (`FdFormal/FlowerDimension.lean`): for the vertex count `N_g` and hub distance `L_g`, both defined by recurrences, `log N_g / log L_g` tends to `log (u + v) / log u`.
- `flowerGraph_dist_hubs` (`FdFormal/FlowerConstruction.lean`): the constructed graph `flowerGraph u v g` on `Fin N_g` has `SimpleGraph.dist` `L_g = u ^ g` between its two hubs, the images of `FlowerVert.hub0` and `FlowerVert.hub1` under `flowerVertEquiv`.

Not formalized: box-counting dimension, with which the paper identifies the limit, and the log-ratio limit for `flowerGraph` itself (`HasLogRatioDimension` is only defined).

## Verify

```bash
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true FdFormal/Verify.lean
```

`FdFormal/Verify.lean` prints the axioms of 27 declarations, including both results; CI requires each to use only `propext`, `Classical.choice` and `Quot.sound`. `docs/aristotle/` holds unbuilt prover files; the inputs contain `sorry`.

## Credit and license

Formalization by Nelson Spence; Aristotle (Harmonic) proved several leaf lemmas and Claude assisted with Lean. For the mathematics, cite H. D. Rozenfeld, S. Havlin and D. ben-Avraham, "Fractal and transfractal recursive scale-free nets", *New J. Phys.* 9, 175 (2007). Apache 2.0; see [LICENSE](LICENSE).
