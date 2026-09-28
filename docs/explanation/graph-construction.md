# Graph Construction

F2 builds the \((u,v)\)-flower as an explicit `SimpleGraph` and proves that its hub distance is \(u^g\) (`FlowerConstruction.lean`); F3 turns this into the log-ratio dimension of the graphs (`FlowerGraphDimension.lean`). F4 reuses the same construction: its cells are the copies of an earlier generation's flower that each edge grows into (`FlowerCells.lean`); see [Proof Strategy](proof-strategy.md#f4-box-counting).

---

## Types

```lean
def FlowerVert (u v : ℕ) (g : ℕ) : Type :=
  Fin 2 ⊕ Σ (k : Fin g), FlowerEdge u v k.val × (Fin (u - 1) ⊕ Fin (v - 1))

def FlowerEdge (u v : ℕ) : ℕ → Type
  | 0     => Unit
  | g + 1 => FlowerEdge u v g × LocalEdge u v   -- LocalEdge u v := Fin u ⊕ Fin v
```

`Fin 2` holds the hubs `FlowerVert.hub0` and `FlowerVert.hub1`. Every other vertex records the generation `k` that created it, the edge it replaced, and its position on the short (length \(u\)) or long (length \(v\)) path: \(u + v - 2\) internal vertices per gadget. `GadgetPos` (`src`, `tgt`, `short i`, `long j`) names positions in a gadget, `localSrc`/`localTgt` give the endpoints of each local edge, and `edgeEndpoints` resolves them recursively.

---

## Adjacency

`flowerAdj' a b` holds when some edge has endpoints \(\{a, b\}\) (`edgeSrc`, `edgeTgt`); `flowerGraph'` is the resulting graph on `FlowerVert`. Lemmas such as `short_tgt_eq_succ_src`, `short_first_eq_embed_src` and `short_last_eq_embed_tgt` show that consecutive gadget edges share endpoints.

---

## Distance

- **Upper bound.** `flowerGraph'_walk_hubs`: by induction on \(g\), `lift_walk` replaces each edge of a hub-to-hub walk with a short path of length \(u\), giving a walk of length \(u^g\).
- **Lower bound.** `FlowerVert.rank` is 0 at `hub0`, \(u^g\) at `hub1`, and grows by at most 1 along an edge (`rank_adj_le`), so every hub-to-hub walk has length at least \(u^g\) (`walk_length_ge_rank`, `flowerGraph'_dist_ge`).

Together they give `flowerGraph'_dist_hubs`.

---

## Connectivity

`flowerGraph'_connected` goes by induction: lifted walks reach every embedded vertex from `hub0`, and each new vertex is reachable from its gadget's source (`new_short_reachable`, `new_long_reachable`).

---

## Transport to `Fin`

```lean
theorem flowerVert_card (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    Fintype.card (FlowerVert u v g) = flowerVertCount u v g
```

`flowerVertEquiv : FlowerVert u v g ≃ Fin (flowerVertCount u v g)` lists the hubs first, then the internal vertices, so it sends `FlowerVert.hub0` and `FlowerVert.hub1` to `hub0` and `hub1`, the indices 0 and 1 (`flowerVertEquiv_hub0`, `flowerVertEquiv_hub1`). `flowerGraph` is `flowerGraph'` transported along it, and F2 reads:

```lean
theorem flowerGraph_dist_hub0_hub1 (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (flowerGraph u v g hu huv).dist (hub0 u v g) (hub1 u v g) = u ^ g
```

(`flowerGraph_dist_hubs` states the same for the images of the hubs, with `flowerHubDist u v g`.)

---

## F3: log-ratio dimension of the graphs

`FlowerGraphDimension.lean` combines F1, F2 and \(\lvert\mathrm{Fin}\,n\rvert = n\):

```lean
theorem flowerGraph_hasLogRatioDimension (u v : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    HasLogRatioDimension (fun g ↦ flowerGraph u v g hu huv) (hub0 u v) (hub1 u v)
      (log ↑(u + v) / log ↑u)
```
