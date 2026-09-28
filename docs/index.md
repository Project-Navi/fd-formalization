---
hide:
  - navigation
  - toc
---

# fd-formalization

**Lean 4 + Mathlib formalization of the \((u,v)\)-flower log-ratio limit, hub distance and box-counting dimension.**

[Get Started](getting-started/quickstart.md){ .md-button .md-button--primary }
[Theorems](reference/theorems.md){ .md-button }

---

## What it proves

For \(1 < u \leq v\):

| Theorem | Statement | File |
|---|---|---|
| **F1** --- log-ratio limit | \(\displaystyle\lim_{g \to \infty} \frac{\log N_g}{\log L_g} = \frac{\log(u+v)}{\log u}\), for the vertex count \(N_g\) and hub distance \(L_g\) defined by recurrences | `FlowerDimension.lean` |
| **F2** --- hub distance | the explicit flower graph on \(\mathrm{Fin}\,N_g\) has distance \(L_g = u^g\) between its hubs, the indices 0 and 1 | `FlowerConstruction.lean` |
| **F3** --- graph dimension | so the flower graphs themselves have log-ratio dimension \(\log(u+v)/\log u\) | `FlowerGraphDimension.lean` |
| **F4** --- box counting | the flower graphs have box-counting dimension \(\log(u+v)/\log u\), along every scale sequence \(\ell_g\) with \(\operatorname{diam} G_g / \ell_g \to \infty\) | `FlowerBoxDimension.lean` |

Rozenfeld et al. (2007) identify this limit with the box-counting dimension \(d_B\); F4 proves that identification for the explicit graphs. [navi-fractal](https://github.com/Project-Navi/navi-fractal) uses the formula as calibration ground truth.

The library builds with no `sorry`, and the 46 declarations checked in `Verify.lean` use only `propext`, `Classical.choice` and `Quot.sound`.

## Documentation

| Section | Contents |
|---|---|
| [Quickstart](getting-started/quickstart.md) | Build and verify |
| [Proof Strategy](explanation/proof-strategy.md) | Squeeze argument for F1; cells and box counting for F4 |
| [Graph Construction](explanation/graph-construction.md) | F2 and F3: gadgets, the distance proof |
| [Theorems](reference/theorems.md) | Catalog by file |
| [Roadmap](reference/roadmap.md) | What is done, and the scope |
