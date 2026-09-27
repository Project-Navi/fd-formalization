# Proof Strategy

For \(1 < u \leq v\) and \(w = u + v\), with the vertex count \(N_g\) and hub distance \(L_g\) defined by recurrences:

\[
\lim_{g \to \infty} \frac{\log N_g}{\log L_g} = \frac{\log w}{\log u}
\]

Rozenfeld, Havlin & ben-Avraham (2007) identify this limit with the box-counting dimension \(d_B\); that identification is not formalized.

---

## Route B: squeeze

1. **Exact counts.** \(E_g = w^g\), \(L_g = u^g\), and \((w - 1)\,N_g = (w - 2)\,w^g + w\): each replaced edge adds \(w - 2\) internal vertices.
2. **Bounds.** \(\frac{w-2}{w-1}\,w^g \leq N_g \leq 2\,w^g\).
3. **Decomposition.** Since \(\log L_g = g \log u\),
   \[
   \frac{\log N_g}{\log L_g} = \underbrace{\frac{\log N_g - g \log w}{g \log u}}_{\text{residual}} + \frac{\log w}{\log u}.
   \]
4. **Squeeze.** The residual lies between \(\log\frac{w-2}{w-1} / (g \log u)\) and \(\log 2 / (g \log u)\), so it tends to 0 (`Filter.Tendsto.squeeze'`).

This avoids taking the log of the exact sum \((w-2)\,w^g + w\).

---

## F2: the graph

F1 is about the recurrences. F2 builds the flower as an explicit `SimpleGraph` on \(\mathrm{Fin}\,N_g\) and proves that the distance between its hubs, the indices 0 and 1, is \(L_g = u^g\): an explicit walk gives the upper bound and a rank potential the lower bound. Since the graph has \(N_g\) vertices, F1 and F2 give F3: the graphs themselves have log-ratio dimension \(\log w / \log u\). See [Graph Construction](graph-construction.md).

---

## Axioms

The 33 declarations in `Verify.lean` use only `propext`, `Classical.choice` and `Quot.sound`.

---

## References

- H. D. Rozenfeld, S. Havlin & D. ben-Avraham, "Fractal and transfractal recursive scale-free nets," *New Journal of Physics* **9**, 175 (2007)
- C. Song, S. Havlin & H. A. Makse, "Self-similarity of complex networks," *Nature* **433**, 392 (2005)
