# Roadmap

## Done

- **F1: log-ratio limit** (`FlowerDimension.lean`). \(\lim_{g \to \infty} \log N_g / \log L_g = \log(u+v)/\log u\) for the recurrence-defined counts, by a squeeze.
- **F2: hub distance** (`FlowerConstruction.lean`). The explicit flower graph on `Fin` has distance \(u^g\) between its hubs, the indices 0 and 1: walk upper bound, rank lower bound.
- **F3: log-ratio dimension of the graphs** (`FlowerGraphDimension.lean`). `HasLogRatioDimension` for `flowerGraph` between `hub0` and `hub1`, from F1, F2 and \(\lvert\mathrm{Fin}\,n\rvert = n\).
- **F4: box-counting dimension of the graphs** (`FlowerBoxDimension.lean`). `HasBoxDimension` for `flowerGraph`: along every scale sequence with \(\operatorname{diam} G_g / \ell_g \to \infty\), \(\log N_B(G_g, \ell_g) / \log(\operatorname{diam} G_g / \ell_g) \to \log(u+v)/\log u\). This is the identification Rozenfeld et al. (2007) make; see [Proof Strategy](../explanation/proof-strategy.md#f4-box-counting).
- **SimpleGraph.ball**. Open metric ball via `edist`, first written here and since upstreamed to Mathlib; the local copy was removed with the move to Mathlib v4.34.1.

## Scope

The roadmap is complete. The case \(u = 1\) is out of scope by design, not open. The flowers are then transfractal: the hub distance is \(1^g = 1\), the diameter grows only linearly in \(g\), and with no length scale factor \(u > 1\) there is no \(\log u\) to divide by.
