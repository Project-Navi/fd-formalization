# Theorems

Definitions and theorems by file. The tables omit hypotheses (mostly \(1 < u\) and \(u \leq v\)); see the source. The library builds with no `sorry`, and the 52 declarations in `Verify.lean` use only `propext`, `Classical.choice` and `Quot.sound`.

---

## Headline theorems

### F1: log-ratio limit (`FlowerDimension.lean`)

```lean
theorem flowerDimension (u v : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    Tendsto (fun g : ℕ ↦ log ↑(flowerVertCount u v g) / log ↑(flowerHubDist u v g))
      atTop (nhds (log ↑(u + v) / log ↑u))
```

### F2: hub distance (`FlowerConstruction.lean`)

```lean
theorem flowerGraph_dist_hub0_hub1 (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (flowerGraph u v g hu huv).dist (hub0 u v g) (hub1 u v g) = u ^ g
```

`hub0` and `hub1` are the indices 0 and 1, where `flowerVertEquiv` sends the construction's hubs; see [Graph Construction](../explanation/graph-construction.md).

### F3: log-ratio dimension of the graphs (`FlowerGraphDimension.lean`)

```lean
theorem flowerGraph_hasLogRatioDimension (u v : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    HasLogRatioDimension (fun g ↦ flowerGraph u v g hu huv) (hub0 u v) (hub1 u v)
      (log ↑(u + v) / log ↑u)
```

### HasLogRatioDimension (`FlowerLogRatio.lean`)

```lean
def HasLogRatioDimension
    {V : ℕ → Type*} [∀ g, Fintype (V g)]
    (G : (g : ℕ) → SimpleGraph (V g))
    (s t : (g : ℕ) → V g)
    (d : ℝ) : Prop :=
  Tendsto (fun g ↦ log (Fintype.card (V g) : ℝ) / log ((G g).dist (s g) (t g) : ℝ))
    atTop (nhds d)
```

For a family of finite graphs with distinguished vertices, the log-ratio of vertex count to their distance tends to \(d\). F3 proves it for the flower graphs.

### F4: box-counting dimension of the graphs (`FlowerBoxDimension.lean`)

```lean
theorem flowerGraph_hasBoxDimension (hu : 1 < u) (huv : u ≤ v) :
    HasBoxDimension (fun g ↦ flowerGraph u v g hu huv) (log ↑(u + v) / log ↑u)
```

### HasBoxDimension (`FlowerBoxDimension.lean`)

```lean
def HasBoxDimension {V : ℕ → Type*} (G : (g : ℕ) → SimpleGraph (V g)) (d : ℝ) : Prop :=
  Tendsto (fun g ↦ ((G g).diam : ℝ)) atTop atTop ∧
  ∀ ℓ : ℕ → ℕ, (∀ g, 0 < ℓ g) →
    Tendsto (fun g ↦ ((G g).diam : ℝ) / ℓ g) atTop atTop →
    Tendsto (fun g ↦ log ((G g).boxCount (ℓ g) : ℝ) / log (((G g).diam : ℝ) / ℓ g))
      atTop (𝓝 d)
```

`boxCount ℓ` is the fewest vertex sets of extended diameter \(< \ell\) that cover the graph (Song, Havlin & Makse 2005). The diameters must diverge, and the limit is required along every scale sequence with \(\operatorname{diam} G_g / \ell_g \to \infty\), so it does not depend on a choice of scales and \(d\) is unique. F4 proves it for the flower graphs; see [Proof Strategy](../explanation/proof-strategy.md#f4-box-counting).

---

## Counts (`FlowerCounts.lean`)

\(E_0 = 1\), \(E_{g+1} = (u+v)\,E_g\); \(N_0 = 2\), \(N_{g+1} = N_g + (u+v-2)\,E_g\); \(w = u + v\).

| Theorem | Statement |
|---|---|
| `flowerEdgeCount_eq_pow` | \(E_g = w^g\) |
| `flowerVertCount_eq` | \((w-1)\,N_g = (w-2)\,w^g + w\) |
| `flowerVertCount_lower` | \((w-2)\,w^g \leq (w-1)\,N_g\) |
| `flowerVertCount_upper` | \((w-1)\,N_g \leq 2(w-1)\,w^g\) |
| `flowerEdgeCount_pos`, `flowerVertCount_pos` | \(0 < E_g\), \(0 < N_g\) |
| `flowerEdgeCount_strict_mono`, `flowerVertCount_strict_mono` | \(E_g < E_{g+1}\), \(N_g < N_{g+1}\) |
| `flowerVertCount_cast_eq` | the exact recurrence in \(\mathbb{R}\) |

---

## Hub distance (`FlowerDiameter.lean`)

\(L_0 = 1\), \(L_{g+1} = u\,L_g\).

| Theorem | Statement |
|---|---|
| `flowerHubDist_eq_pow` | \(L_g = u^g\) |
| `flowerHubDist_pos`, `flowerHubDist_strict_mono` | \(0 < L_g\), \(L_g < L_{g+1}\) |
| `flowerHubDist_cast_eq_pow` | \(\uparrow\!L_g = (\uparrow\!u)^g\) in \(\mathbb{R}\) |

---

## Logs (`FlowerLog.lean`)

| Theorem | Statement |
|---|---|
| `log_flowerHubDist_eq` | \(\log L_g = g \log u\) |
| `log_flowerEdgeCount_eq` | \(\log E_g = g \log w\) |
| `log_flowerVertCount_residual_lower` | \(\log\frac{w-2}{w-1} \leq \log N_g - g \log w\) |
| `log_flowerVertCount_residual_upper` | \(\log N_g - g \log w \leq \log 2\) |

---

## Hubs on `Fin` (`FlowerGraph.lean`)

`hub0`, `hub1 : Fin (flowerVertCount u v g)` are the indices 0 and 1, with `two_le_flowerVertCount` (\(2 \leq N_g\)) and `hub0_ne_hub1`.

---

## Graph construction (`FlowerConstruction.lean`)

| Declaration | Content |
|---|---|
| `GadgetPos`, `LocalEdge`, `FlowerEdge`, `FlowerVert` | gadget positions, edge and vertex types |
| `flowerGraph'` | the flower graph on `FlowerVert` |
| `flowerGraph'_adj_iff` | adjacency iff `flowerAdj'` |
| `gadgetInternal_card` | \(u + v - 2\) internal vertices per gadget |
| `flowerVert_card` | `Fintype.card (FlowerVert u v g) = flowerVertCount u v g` |
| `flowerGraph'_connected` | the flower graph is connected |
| `flowerGraph'_dist_hubs` | hub distance \(u^g\) on `FlowerVert` |
| `flowerVertEquiv_hub0`, `flowerVertEquiv_hub1` | `flowerVertEquiv` sends the hubs to `hub0`, `hub1` |
| `flowerGraph_dist_hubs` | hub distance on `Fin`, via `flowerVertEquiv` |
| `flowerGraph_dist_hub0_hub1` | F2 (see [above](#f2-hub-distance-flowerconstructionlean)) |

---

## Path graphs (`PathGraphDist.lean`)

In `pathGraph (n + 1)`, `pathGraph_edist` and `pathGraph_dist` give \(|i - j|\), and `pathGraph_edist_zero_last` and `pathGraph_dist_zero_last` give \(n\) between the endpoints.

---

## Box covering (`BoxCounting.lean`)

For any simple graph \(G\):

| Declaration | Content |
|---|---|
| `IsBox ℓ B` | the points of \(B\) are pairwise at extended distance \(< \ell\) |
| `boxCount ℓ` | \(N_B(G, \ell)\), the fewest boxes of size \(\ell\) covering every vertex |
| `boxCount_le_of_cover` | any cover by \(n\) boxes gives \(N_B \leq n\) |
| `le_boxCount_of_separated` | \(n\) points pairwise at distance \(\geq \ell\) give \(n \leq N_B\) |
| `boxCount_anti`, `boxCount_pos`, `boxCount_le_card` | antitone in \(\ell\); \(0 < N_B \leq \lvert V \rvert\) |
| `Iso.boxCount_eq` | isomorphic graphs have equal box counts |
| `Hom.dist_le` | graph homomorphisms do not increase distance |
| `le_add_dist_of_lipschitz`, `tent_lipschitz` | a 1-Lipschitz potential bounds distance; folding it into a tent keeps it 1-Lipschitz |

---

## Scaling (`BoxScaling.lean`)

`Real.tendsto_log_count_div_log_scale`: if \(N(g, \ell)\) is antitone in \(\ell\) and within a constant factor of \(b^{g-m}\) at \(\ell = u^m\), then along any scales with \(L_g / \ell_g \to \infty\) (where \(L_g\) is comparable to \(u^g\)), \(\log N(g, \ell_g) / \log(L_g / \ell_g) \to \log b / \log u\).

---

## Cells (`FlowerCells.lean`)

A generation-\(k\) edge \(e\) is replaced, \(j\) generations later, by a copy of the generation-\(j\) flower.

| Declaration | Content |
|---|---|
| `FlowerEdge.graft`, `trunc`, `suffix` | split a generation-\((k + j)\) edge into its generation-\(k\) ancestor and the rest |
| `cellEmbed k e j` | the generation-\(j\) flower mapped onto the cell of \(e\) |
| `cellEmbed_injective`, `cellHom` | each cell is an injective graph homomorphism image |
| `exists_cellEmbed_eq` | the \((u+v)^k\) cells cover every vertex |
| `cellEmbed_eq_of_ne` | distinct cells meet only at hubs |
| `cellPotential_lipschitz` | a hub-vanishing 1-Lipschitz potential moved onto one cell stays 1-Lipschitz |

---

## Rank and radius (`FlowerRadius.lean`)

| Theorem | Statement |
|---|---|
| `rank_le_pow`, `exists_rank_eq` | ranks lie in \([0, u^g]\), and each value is taken |
| `dist_hub_le` | every vertex is within \(v\,u^g\) of a hub |
| `flowerGraph'_dist_le` | the diameter is at most \((2v + 1)\,u^g\) |

---

## Box counts of the flowers (`FlowerBoxDimension.lean`)

| Theorem | Statement |
|---|---|
| `flower_boxCount_ge` | for \(0 < j\), \((u+v)^k \leq N_B(G_{k+j}, u^j / 2)\): cell centres are \(u^j / 2\)-separated |
| `flower_boxCount_le` | \(N_B(G_{k+j}, (2v + 1)\,u^j + 1) \leq (u+v)^k\): cells are boxes |
| `flowerGraph'_diam_bounds` | \(u^g \leq \operatorname{diam} G_g \leq (2v + 1)\,u^g\) |
| `flowerGraph_hasBoxDimension` | F4 (see [above](#f4-box-counting-dimension-of-the-graphs-flowerboxdimensionlean)) |

---

## Metric balls

`SimpleGraph.ball` was first written here and has been in Mathlib since v4.30.0. Mathlib's version is `{v | G.edist v c < r}` (the varying point first), and its centre lemma is `mem_ball_self`.
