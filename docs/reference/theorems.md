# Theorems

Complete catalog of definitions and theorems in the formalization, organized by source file. All declarations are fully proved with zero `sorry` and zero custom axioms.

---

## Headline theorems

### F1: Log-ratio convergence

```lean
theorem flowerDimension (u v : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    Tendsto (fun g : ℕ ↦ log ↑(flowerVertCount u v g) / log ↑(flowerHubDist u v g))
      atTop (nhds (log ↑(u + v) / log ↑u))
```

The ratio \(\log |V_g| / \log L_g\) converges to \(\log(u+v) / \log u\) as \(g \to \infty\). Proved via Route B (squeeze). See [Proof Strategy](../explanation/proof-strategy.md).

**File:** `FlowerDimension.lean`

### F2: Hub distance bridge

```lean
theorem flowerGraph_dist_hubs (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (flowerGraph u v g hu huv).dist
      ((flowerVertEquiv u v g hu huv) (.hub0 u v g))
      ((flowerVertEquiv u v g hu huv) (.hub1 u v g))
    = flowerHubDist u v g
```

The `SimpleGraph.dist` between hub vertices in the concrete \((u,v)\)-flower graph on `Fin` equals \(u^g\). See [Graph Construction](../explanation/graph-construction.md).

**File:** `FlowerConstruction.lean`

### HasLogRatioDimension

```lean
def HasLogRatioDimension
    {V : ℕ → Type*} [∀ g, Fintype (V g)]
    (G : (g : ℕ) → SimpleGraph (V g))
    (s t : (g : ℕ) → V g)
    (d : ℝ) : Prop :=
  Tendsto (fun g ↦ log (Fintype.card (V g) : ℝ) / log ((G g).dist (s g) (t g) : ℝ))
    atTop (nhds d)
```

Predicate asserting that the log-ratio limit equals \(d\) for a graph family with distinguished vertex pairs. Bridge target for F3 (combining F1 + F2).

**File:** `FlowerLogRatio.lean`

---

## Counting formulas (FlowerCounts.lean)

### Definitions

```lean
def flowerEdgeCount (u v : ℕ) : ℕ → ℕ
  | 0     => 1
  | g + 1 => (u + v) * flowerEdgeCount u v g

def flowerVertCount (u v : ℕ) : ℕ → ℕ
  | 0     => 2
  | g + 1 => flowerVertCount u v g + (u + v - 2) * flowerEdgeCount u v g
```

### Exact formulas

| Theorem | Statement |
|---|---|
| `flowerEdgeCount_eq_pow` | \(E_g = (u+v)^g\) |
| `flowerVertCount_eq` | \((w-1) \cdot N_g = (w-2) \cdot w^g + w\) where \(w = u+v\) |

### Bounds

| Theorem | Statement |
|---|---|
| `flowerVertCount_lower` | \((w-2) \cdot w^g \leq (w-1) \cdot N_g\) |
| `flowerVertCount_upper` | \((w-1) \cdot N_g \leq 2(w-1) \cdot w^g\) |

### Positivity and monotonicity

| Theorem | Statement |
|---|---|
| `flowerEdgeCount_pos` | \(0 < E_g\) |
| `flowerVertCount_pos` | \(0 < N_g\) |
| `flowerEdgeCount_strict_mono` | \(E_g < E_{g+1}\) |
| `flowerVertCount_strict_mono` | \(N_g < N_{g+1}\) |

### Cast identity

| Theorem | Statement |
|---|---|
| `flowerVertCount_cast_eq` | The exact recurrence holds in \(\mathbb{R}\): \((w-1) \cdot N_g = (w-2) \cdot w^g + w\) |

---

## Hub distance (FlowerDiameter.lean)

### Definition

```lean
def flowerHubDist (u v : ℕ) : ℕ → ℕ
  | 0     => 1
  | g + 1 => u * flowerHubDist u v g
```

### Theorems

| Theorem | Statement |
|---|---|
| `flowerHubDist_eq_pow` | \(L_g = u^g\) |
| `flowerHubDist_pos` | \(0 < L_g\) |
| `flowerHubDist_strict_mono` | \(L_g < L_{g+1}\) |
| `flowerHubDist_cast_eq_pow` | \(\uparrow\!L_g = (\uparrow\!u)^g\) in \(\mathbb{R}\) |

---

## Log identities (FlowerLog.lean)

| Theorem | Statement |
|---|---|
| `log_flowerHubDist_eq` | \(\log L_g = g \cdot \log u\) |
| `log_flowerEdgeCount_eq` | \(\log E_g = g \cdot \log(u+v)\) |
| `log_flowerVertCount_residual_lower` | \(\log\!\bigl(\tfrac{w-2}{w-1}\bigr) \leq \log N_g - g \cdot \log w\) |
| `log_flowerVertCount_residual_upper` | \(\log N_g - g \cdot \log w \leq \log 2\) |

---

## Hub vertices (FlowerGraph.lean)

```lean
def hub0 (u v g : ℕ) : Fin (flowerVertCount u v g)
def hub1 (u v g : ℕ) : Fin (flowerVertCount u v g)
```

| Theorem | Statement |
|---|---|
| `two_le_flowerVertCount` | \(2 \leq N_g\) |
| `hub0_ne_hub1` | The two hubs are distinct |

---

## Graph construction (FlowerConstruction.lean)

### Types

| Definition | Purpose |
|---|---|
| `GadgetPos u v` | Position within a replacement gadget (src, tgt, short, long) |
| `LocalEdge u v` | Edge index within a gadget: `Fin u ⊕ Fin v` |
| `FlowerEdge u v g` | Recursive edge index type |
| `FlowerVert u v g` | Vertex type: `Fin 2 ⊕ Σ (k : Fin g), FlowerEdge u v k.val × (Fin (u-1) ⊕ Fin (v-1))` |
| `flowerGraph' u v g` | `SimpleGraph` on `FlowerVert` |

### Structural theorems

| Theorem | Statement |
|---|---|
| `flowerGraph'_adj_iff` | Adjacency iff `flowerAdj'` |
| `gadgetInternal_card` | Internal vertex count per gadget = \(u+v-2\) |
| `flowerVert_card` | `Fintype.card (FlowerVert u v g) = flowerVertCount u v g` |
| `flowerGraph'_connected` | The flower graph is connected |
| `flowerGraph'_dist_hubs` | `dist hub0 hub1 = u^g` on `FlowerVert` |
| `flowerGraph_dist_hubs` | F2 bridge on `Fin` (see [headline](#f2-hub-distance-bridge)) |

---

## Path graph distance (PathGraphDist.lean)

Distance in `pathGraph (n+1)` equals the absolute difference of vertex indices.

| Theorem | Statement |
|---|---|
| `pathGraph_edist` | \(\operatorname{edist}(i, j) = |i - j|\) |
| `pathGraph_dist` | \(\operatorname{dist}(i, j) = |i - j|\) |
| `pathGraph_dist_zero_last` | \(\operatorname{dist}(0, n) = n\) |
| `pathGraph_edist_zero_last` | \(\operatorname{edist}(0, n) = n\) |

---

## Metric balls (GraphBall.lean)

### Definition

```lean
def SimpleGraph.ball (c : V) (r : ℕ∞) : Set V := {v | G.edist c v < r}
```

Open ball using strict inequality (`<`), matching `Metric.ball` convention. This is an upstream candidate for Mathlib.

### Core lemmas

| Lemma | Statement |
|---|---|
| `mem_ball` | \(v \in B(c, r) \iff \operatorname{edist}(c, v) < r\) |
| `ball_zero` | \(B(c, 0) = \varnothing\) |
| `ball_one` | \(B(c, 1) = \{c\}\) |
| `ball_top` | \(B(c, \top)\) = connected component of \(c\) |
| `ball_mono` | \(r_1 \leq r_2 \implies B(c, r_1) \subseteq B(c, r_2)\) |
| `center_mem_ball` | \(0 < r \implies c \in B(c, r)\) |
| `mem_ball_comm` | \(v \in B(c, r) \iff c \in B(v, r)\) |

### Convenience lemmas

| Lemma | Statement |
|---|---|
| `ball_nonempty` | \(0 < r \implies B(c, r) \neq \varnothing\) |
| `ball_anti` | Subgraph balls are subsets of supergraph balls |
| `mem_ball_of_adj` | Adjacent vertices are in each other's radius-2 ball |
| `adj_of_mem_ball_two` | Distinct vertices in \(B(c, 2)\) are adjacent |
| `mem_ball_of_mem_ball_of_mem_ball` | Triangle inequality: \(B(c, r_1) \ni v\) and \(B(v, r_2) \ni w\) implies \(w \in B(c, r_1 + r_2)\) |
