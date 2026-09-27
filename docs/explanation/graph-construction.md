# Graph Construction

F2 builds the \((u,v)\)-flower as an explicit `SimpleGraph` and proves that its hub distance is \(u^g\). Everything here is in `FlowerConstruction.lean`.

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

Together they give `flowerGraph'_dist_hubs`. The projection lemmas `FlowerVert.project` and `project_adj_or_eq`, from an earlier approach, remain in the file but are not used.

---

## Connectivity

`flowerGraph'_connected` goes by induction: lifted walks reach every embedded vertex from `hub0`, and each new vertex is reachable from its gadget's source (`new_short_reachable`, `new_long_reachable`).

---

## Transport to `Fin`

```lean
theorem flowerVert_card (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    Fintype.card (FlowerVert u v g) = flowerVertCount u v g
```

`flowerVertEquiv` is `Fintype.equivFinOfCardEq` applied to this, and `flowerGraph` is `flowerGraph'` transported along it:

```lean
theorem flowerGraph_dist_hubs (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (flowerGraph u v g hu huv).dist
      ((flowerVertEquiv u v g hu huv) (.hub0 u v g))
      ((flowerVertEquiv u v g hu huv) (.hub1 u v g))
    = flowerHubDist u v g
```

`Fintype.equivFinOfCardEq` is not canonical, so the hubs' images need not be `0` and `1`; the `Fin`-indexed `hub0`/`hub1` in `FlowerGraph.lean` are not yet tied to this construction.
