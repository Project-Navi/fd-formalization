# Theorems

Definitions and theorems by file. The tables omit hypotheses (mostly \(1 < u\) and \(u \leq v\)); see the source. The library builds with no `sorry`, and the 27 declarations in `Verify.lean` use only `propext`, `Classical.choice` and `Quot.sound`.

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
theorem flowerGraph_dist_hubs (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (flowerGraph u v g hu huv).dist
      ((flowerVertEquiv u v g hu huv) (.hub0 u v g))
      ((flowerVertEquiv u v g hu huv) (.hub1 u v g))
    = flowerHubDist u v g
```

The hubs are the images of `FlowerVert.hub0` and `FlowerVert.hub1`; see [Graph Construction](../explanation/graph-construction.md).

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

Defined only; not yet proved for the flower graphs (F3 on the [Roadmap](roadmap.md)).

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

`hub0`, `hub1 : Fin (flowerVertCount u v g)` are the indices 0 and 1, with `two_le_flowerVertCount` (\(2 \leq N_g\)) and `hub0_ne_hub1`. F2 does not use them yet.

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
| `flowerGraph_dist_hubs` | F2 on `Fin` (see [above](#f2-hub-distance-flowerconstructionlean)) |

---

## Path graphs (`PathGraphDist.lean`)

In `pathGraph (n + 1)`, `pathGraph_edist` and `pathGraph_dist` give \(|i - j|\), and `pathGraph_edist_zero_last` and `pathGraph_dist_zero_last` give \(n\) between the endpoints.

---

## Metric balls (`GraphBall.lean`)

```lean
def SimpleGraph.ball (c : V) (r : ℕ∞) : Set V := {v | G.edist c v < r}
```

An open ball (strict `<`, like `Metric.ball`). It has since been upstreamed to Mathlib, and is kept here for the pinned version. Core lemmas: `mem_ball`, `ball_zero` (empty), `ball_one` (\(\{c\}\)), `ball_top` (the connected component of \(c\)), `ball_mono`, `center_mem_ball`, `mem_ball_comm`. Convenience lemmas: `edist_lt_of_mem_ball`, `ball_nonempty`, `ball_anti`, `mem_ball_of_adj`, `adj_of_mem_ball_two`, `mem_ball_of_mem_ball_of_mem_ball`.
