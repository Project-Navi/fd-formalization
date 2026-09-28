# Proof Strategy

For \(1 < u \leq v\) and \(w = u + v\), with the vertex count \(N_g\) and hub distance \(L_g\) defined by recurrences:

\[
\lim_{g \to \infty} \frac{\log N_g}{\log L_g} = \frac{\log w}{\log u}
\]

Rozenfeld, Havlin & ben-Avraham (2007) identify this limit with the box-counting dimension \(d_B\); F4 proves that identification for the explicit graphs.

---

## Route B: squeeze

1. **Exact counts.** \(E_g = w^g\), \(L_g = u^g\), and \((w - 1)\,N_g = (w - 2)\,w^g + w\): each replaced edge adds \(w - 2\) internal vertices.
2. **Bounds.** \(\frac{w-2}{w-1}\,w^g \leq N_g \leq 2\,w^g\).
3. **Decomposition.** For \(g \geq 1\), \(\log L_g = g \log u > 0\), so
   \[
   \frac{\log N_g}{\log L_g} = \underbrace{\frac{\log N_g - g \log w}{g \log u}}_{\text{residual}} + \frac{\log w}{\log u}.
   \]
4. **Squeeze.** The residual lies between \(\log\frac{w-2}{w-1} / (g \log u)\) and \(\log 2 / (g \log u)\), so it tends to 0 (`Filter.Tendsto.squeeze'`, applied eventually in \(g\)).

This avoids taking the log of the exact sum \((w-2)\,w^g + w\).

---

## F2: the graph

F1 is about the recurrences. F2 builds the flower as an explicit `SimpleGraph` on \(\mathrm{Fin}\,N_g\) and proves that the distance between its hubs, the indices 0 and 1, is \(L_g = u^g\): an explicit walk gives the upper bound and a rank potential the lower bound. Since the graph has \(N_g\) vertices, F1 and F2 give F3: the graphs themselves have log-ratio dimension \(\log w / \log u\). See [Graph Construction](graph-construction.md). F3 measures between one chosen pair of vertices; F4 below removes that choice.

---

## F4: box counting

A box of size \(\ell\) is a vertex set whose points are pairwise at distance \(< \ell\), and \(N_B(G, \ell)\) is the fewest boxes that cover \(G\) (Song, Havlin & Makse 2005). `HasBoxDimension` asks that the diameters diverge and that \(\log N_B(G_g, \ell_g) / \log(\operatorname{diam} G_g / \ell_g) \to d\) along **every** scale sequence with \(\operatorname{diam} G_g / \ell_g \to \infty\), so the value cannot depend on a choice of scales and is unique.

The proof is the renormalization picture made exact. Each generation-\(k\) edge is replaced, \(j\) generations later, by a copy of the generation-\(j\) flower: its *cell* (`cellEmbed`). The generation-\((k + j)\) flower is \(w^k\) cells of scale \(u^j\), and cells meet only at their hubs.

1. **Lower bound.** In each cell take a centre whose rank is \(u^j / 2\). The tent \(\min(\mathrm{rank}, u^j - \mathrm{rank})\) is 1-Lipschitz and zero at the hubs, so moved onto one cell and extended by zero it stays 1-Lipschitz on the whole graph. It is \(u^j / 2\) at that cell's centre and 0 at every other centre, so centres are \(u^j / 2\) apart and no box of that size holds two: \(N_B \geq w^k\).
2. **Upper bound.** Every vertex lies within \(v\,u^j\) of a hub, so each cell has diameter at most \((2v + 1)\,u^j\) and is a box: \(N_B \leq w^k\).
3. **Scaling.** Both bounds hold at scales a constant factor apart, and \(N_B\) is antitone in \(\ell\), so an abstract squeeze gives the exponent \(\log w / \log u\): the number of blocks multiplies by \(w\) each time lengths multiply by \(u\).

A volume argument would fail here: hubs have degree \(2^g\), so a ball around a hub holds far more than a constant times \(w^j\) vertices. The separated centres avoid degrees altogether.

---

## Axioms

The 75 declarations in `Verify.lean` use only `propext`, `Classical.choice` and `Quot.sound`.

---

## References

- H. D. Rozenfeld, S. Havlin & D. ben-Avraham, "Fractal and transfractal recursive scale-free nets," *New Journal of Physics* **9**, 175 (2007)
- C. Song, S. Havlin & H. A. Makse, "Self-similarity of complex networks," *Nature* **433**, 392 (2005)
