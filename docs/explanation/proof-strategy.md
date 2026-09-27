# Proof Strategy

This page explains the mathematical approach behind the formalization --- how the log-ratio convergence theorem is proved, and why this particular strategy was chosen.

---

## The target theorem

For the arithmetic \((u,v)\)-flower model with \(1 < u \leq v\), the ratio of log vertex count to log hub distance converges:

\[
\lim_{g \to \infty} \frac{\log |V_g|}{\log L_g} = \frac{\log(u+v)}{\log u}
\]

In the physics literature (Rozenfeld, Havlin & ben-Avraham 2007), this quantity equals the box-counting fractal dimension \(d_B\). This formalization proves the log-ratio convergence; a formal bridge to a box-counting definition is future work.

---

## Route B: squeeze

The proof uses a squeeze (sandwich) argument. The key insight is that the vertex count \(N_g\) grows like \((u+v)^g\) up to bounded multiplicative constants, while the hub distance grows exactly as \(u^g\).

### Step 1: exact counting formulas

The edge count and hub distance have clean closed forms:

\[
E_g = (u+v)^g, \qquad L_g = u^g
\]

The vertex count satisfies an exact recurrence:

\[
(w - 1) \cdot N_g = (w - 2) \cdot w^g + w
\]

where \(w = u + v\). This follows from the construction rule: each generation replaces every edge with two parallel paths of lengths \(u\) and \(v\), contributing \(u + v - 2\) new internal vertices per edge.

### Step 2: two-sided bounds

From the exact recurrence, we derive bounds that squeeze \(N_g\) between multiples of \(w^g\):

\[
\frac{w - 2}{w - 1} \cdot w^g \leq N_g \leq 2 \cdot w^g
\]

The lower bound follows from dropping the additive \(+w\) term. The upper bound follows from \((w-2) \cdot w^g + w \leq 2(w-1) \cdot w^g\) for \(w \geq 3\).

### Step 3: log decomposition

Taking logs and dividing by \(g \cdot \log u\), the ratio decomposes as:

\[
\frac{\log N_g}{\log L_g} = \frac{\log N_g}{g \cdot \log u} = \underbrace{\frac{\log N_g - g \cdot \log w}{g \cdot \log u}}_{\text{residual}} + \frac{\log w}{\log u}
\]

### Step 4: squeeze the residual

The bounds from Step 2 give:

\[
\frac{\log\!\left(\frac{w-2}{w-1}\right)}{g \cdot \log u} \leq \text{residual} \leq \frac{\log 2}{g \cdot \log u}
\]

Both bounds tend to 0 as \(g \to \infty\) (they are constants divided by \(g\)), so by the squeeze theorem:

\[
\lim_{g \to \infty} \frac{\log N_g}{\log L_g} = \frac{\log(u+v)}{\log u}
\]

---

## Why Route B

Route A (direct division of exact formulas) would require proving that \(\log\!\bigl((w-2) \cdot w^g + w\bigr) - \log(w-1)\) simplifies cleanly, which involves awkward log-of-sum manipulations. Route B avoids this entirely --- the two-sided bounds are simple arithmetic, and the squeeze argument is a standard Lean/Mathlib pattern (`Filter.Tendsto.squeeze'`).

---

## The F2 bridge

The log-ratio theorem (F1) works with arithmetic recurrences for \(N_g\) and \(L_g\). A separate theorem (F2) connects these to a concrete graph:

> **F2 bridge**: The \((u,v)\)-flower constructed as an explicit `SimpleGraph` on `Fin` has `SimpleGraph.dist hub0 hub1 = u^g`.

This is proved via a structured-gadget approach in five layers:

1. **Local gadgets** --- each edge replacement creates a gadget with \(u+v-2\) internal vertices arranged as two parallel paths
2. **Recursive types** --- `FlowerEdge` (edge indices) and `FlowerVert` (vertex type) grow recursively through generations
3. **Endpoint resolution** --- `edgeEndpoints` maps each recursive edge to its source and target vertices
4. **Distance bounds** --- a projection-based rank lower bound and an explicit walk upper bound together yield `dist = u^g`
5. **Transport to Fin** --- `Fintype.equivFinOfCardEq` transports the result to the standard `Fin`-indexed graph

---

## Hypotheses

All theorems require two hypotheses:

- \(1 < u\) --- excludes the transfractal case (\(u = 1\) gives infinite \(d_B\))
- \(u \leq v\) --- without-loss-of-generality normalization from the source paper

---

## Axiom boundary

**Zero custom axioms.** Every theorem is proved from Mathlib primitives. The `#print axioms` dashboard in `Verify.lean` confirms all declarations depend only on `propext`, `Classical.choice`, and `Quot.sound` --- the standard Lean 4 axioms.

---

## References

- H. D. Rozenfeld, S. Havlin & D. ben-Avraham, "Fractal and transfractal recursive scale-free nets," *New Journal of Physics* **9**, 175 (2007)
- C. Song, S. Havlin & H. A. Makse, "Self-similarity of complex networks," *Nature* **433**, 392 (2005)
