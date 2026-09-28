# (u,v)-flower dimensions in Lean 4

**The flowers' box-counting exponent `log (u + v) / log u` holds for minimum box covers of the finite graphs themselves, uniformly across every resolving scale: from single vertices, where it is the mass-scaling law `log |V_g| / log diam G_g → d` (`HasBoxDimension.tendsto_log_card_div_log_diam`), up to any scale that grows more slowly than the diameter.**

A complete Lean 4 and Mathlib (v4.34.1) proof that the (u,v)-flowers of Rozenfeld, Havlin and ben-Avraham have fractal dimension `log (u + v) / log u` for `1 < u ≤ v`: as the limit of their counting recurrences, as the log-ratio dimension of the explicit graphs, and as their box-counting dimension. There is no `sorry` and no custom axiom. Documentation: [project-navi.github.io/fd-formalization](https://project-navi.github.io/fd-formalization/).

- `flowerDimension` (`FdFormal/FlowerDimension.lean`): for the vertex count `N_g` and hub distance `L_g`, both defined by recurrences, `log N_g / log L_g` tends to `log (u + v) / log u`.
- `flowerGraph_dist_hub0_hub1` (`FdFormal/FlowerConstruction.lean`): in the constructed graph `flowerGraph u v g hu huv` on `Fin N_g`, the distance between `hub0` and `hub1` (indices 0 and 1) is `u ^ g`.
- `flowerGraph_hasLogRatioDimension` (`FdFormal/FlowerGraphDimension.lean`): so these graphs have log-ratio dimension `log (u + v) / log u` (`HasLogRatioDimension`).
- `flowerGraph_hasBoxDimension` (`FdFormal/FlowerBoxDimension.lean`): these graphs also have box-counting dimension `log (u + v) / log u` (`HasBoxDimension`). Boxes are vertex sets of diameter `< ℓ` (Song, Havlin and Makse), the diameters diverge, and the limit of `log N_B(G_g, ℓ_g) / log (diam G_g / ℓ_g)` is taken along every scale sequence `ℓ_g` with `diam G_g / ℓ_g → ∞`, so it does not depend on a choice of scales and is unique. This is the dimension the paper identifies with the log-ratio limit.

Not covered: `u = 1`, the transfractal case. There the hub distance is `1 ^ g = 1` and the diameter grows only linearly in `g`, so there is no length scale factor `u > 1` whose logarithm could serve as the denominator.

## Prior work

To our knowledge, this is the first machine-checked computation, in any proof assistant, of the intrinsic box-covering dimension (network box dimension) of a recursively growing family of finite combinatorial graphs. We prove in Lean 4 that, for `1 < u ≤ v`, the Rozenfeld–Havlin–ben-Avraham (u,v)-flowers have box-counting dimension `log (u + v) / log u`, using minimum covers by vertex sets of intrinsic diameter less than `ℓ` in the Song–Havlin–Makse sense. The limit holds along every positive integer scale sequence `ℓ_g` with `diam G_g / ℓ_g → ∞`, so it does not depend on a preferred sequence of recursive scales. This is a large-generation dimension for a sequence of finite graphs, taken as the generation tends to infinity; it is not the classical box dimension of a single bounded space as the scale tends to zero. Rozenfeld, Havlin and ben-Avraham obtained the same exponent from the flowers' self-similar scaling in 2007; it is also consistent with the general dimension theorem for deterministic iterated graph systems of Neroli (2024), which is stated for a Gromov–Hausdorff scaling limit rather than for minimum covers of the finite graphs. The search behind this claim, and what it found, is recorded in [Prior art](docs/reference/prior-art.md); corrections are welcome.

## Verify

```bash
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true FdFormal/Verify.lean
```

`FdFormal/Verify.lean` prints the axioms of 78 declarations, including all four results; CI requires each to use only `propext`, `Classical.choice` and `Quot.sound`.

## Credit and license

Formalization by Nelson Spence. Aristotle (Harmonic) proved leaf lemmas and simplified proofs, and proved the box-counting modules against hand-written definitions and statements; Claude assisted with Lean. For the mathematics, cite H. D. Rozenfeld, S. Havlin and D. ben-Avraham, "Fractal and transfractal recursive scale-free nets", *New J. Phys.* 9, 175 (2007), for box covering C. Song, S. Havlin and H. A. Makse, "Self-similarity of complex networks", *Nature* 433, 392 (2005), and for the dimension theory of iterated graph systems Z. Neroli, "Fractal dimensions for iterated graph systems", *Proc. R. Soc. A* 480, 20240406 (2024), [doi:10.1098/rspa.2024.0406](https://doi.org/10.1098/rspa.2024.0406). Apache 2.0; see [LICENSE](LICENSE).
