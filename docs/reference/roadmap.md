# Roadmap

## Done

- **F1: log-ratio limit** (`FlowerDimension.lean`). \(\lim_{g \to \infty} \log N_g / \log L_g = \log(u+v)/\log u\) for the recurrence-defined counts, by a squeeze.
- **F2: hub distance** (`FlowerConstruction.lean`). The explicit flower graph on `Fin` has distance \(u^g\) between its hubs, the indices 0 and 1: walk upper bound, rank lower bound.
- **F3: log-ratio dimension of the graphs** (`FlowerGraphDimension.lean`). `HasLogRatioDimension` for `flowerGraph` between `hub0` and `hub1`, from F1, F2 and \(\lvert\mathrm{Fin}\,n\rvert = n\).
- **SimpleGraph.ball** (`GraphBall.lean`). Open metric ball via `edist`; since upstreamed to Mathlib.

## Next

Define box-counting dimension for graph families and prove that the flowers have dimension \(\log(u+v)/\log u\) under it. Rozenfeld et al. (2007) identify the two; the log-ratio exponent alone depends on the chosen vertex pair, so this needs its own theorem.
