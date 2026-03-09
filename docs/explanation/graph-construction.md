# Graph Construction

The F2 bridge theorem proves that the \((u,v)\)-flower, constructed as an explicit `SimpleGraph`, has hub distance exactly \(u^g\). This page explains the construction strategy and the distance proof.

---

## The construction problem

The log-ratio convergence theorem (F1) works with pure arithmetic --- recurrences for vertex count \(N_g\) and hub distance \(L_g\). But to connect this to graph theory, we need an actual `SimpleGraph` whose `SimpleGraph.dist` matches the arithmetic formula. This is the F2 bridge.

The challenge is that `SimpleGraph.dist` is defined as the minimum walk length, which requires constructing a concrete graph, proving it is connected, and bounding the distance from both above and below.

---

## Structured gadgets

### Vertex type

At generation \(g\), the flower has two hub vertices plus internal vertices contributed by each edge replacement. The vertex type is:

```lean
def FlowerVert (u v : ℕ) (g : ℕ) : Type :=
  Sum (Fin 2) (Σ (e : FlowerEdge u v g), GadgetPos u v)
```

The left summand `Fin 2` gives the two hubs. The right summand pairs each edge index with a position within its replacement gadget.

### Gadget positions

Each edge is replaced by two parallel paths of lengths \(u\) and \(v\). The internal vertices of this replacement are:

```lean
inductive GadgetPos (u v : ℕ)
  | src                    -- source endpoint
  | tgt                    -- target endpoint
  | short (i : Fin (u-1))  -- internal vertices on the short path
  | long  (j : Fin (v-1))  -- internal vertices on the long path
```

This gives \((u-1) + (v-1) = u+v-2\) internal vertices per gadget, matching the counting formula.

### Edge indices

Edge indices grow recursively --- each generation-\((g+1)\) edge lives inside a gadget of a generation-\(g\) edge:

```lean
def FlowerEdge (u v : ℕ) : ℕ → Type
  | 0     => Unit
  | g + 1 => FlowerEdge u v g × LocalEdge u v
```

where `LocalEdge u v = Fin u ⊕ Fin v` indexes the \(u + v\) sub-edges within a gadget.

---

## Adjacency

The `SimpleGraph` is defined by a symmetric, irreflexive adjacency relation `flowerAdj'` that is built recursively:

- **Base case** (\(g = 0\)): the two hubs are adjacent
- **Recursive case** (\(g + 1\)): two vertices are adjacent if they are consecutive positions within the same gadget's short path or long path

The key structural lemmas prove that endpoints of consecutive gadget positions match up correctly:

- `short_tgt_eq_succ_src` --- consecutive short-path edges share a vertex
- `long_tgt_eq_succ_src` --- consecutive long-path edges share a vertex
- `short_first_eq_embed_src` --- the first short-path edge starts at the gadget source
- `short_last_eq_embed_tgt` --- the last short-path edge ends at the gadget target

---

## Distance proof

The hub distance proof has two directions:

### Lower bound (projection)

A projection map `FlowerVert.project` collapses generation-\((g+1)\) vertices onto generation-\(g\) vertices by mapping each gadget's short-path internals to its source. The key property:

> If two vertices are adjacent, their projections are either adjacent or equal.

This means any walk of length \(\ell\) in generation \(g+1\) projects to a walk of length \(\leq \ell\) in generation \(g\). By induction, `dist hub0 hub1 ≥ u^g`.

### Upper bound (explicit walk)

An explicit walk of length exactly \(u^g\) is constructed between the hubs by recursively following the short path through each gadget. The walk `flowerGraph'_walk_hubs` is built by induction on \(g\), lifting generation-\(g\) walks into generation-\((g+1)\) walks via the gadget structure.

### Combined

Since `dist hub0 hub1 ≥ u^g` and there exists a walk of length `u^g`, we get `dist hub0 hub1 = u^g`.

---

## Transport to Fin

The `SimpleGraph` is initially defined on `FlowerVert u v g` (a sum type). To match the arithmetic counting formulas, we transport to `Fin (flowerVertCount u v g)` via `Fintype.equivFinOfCardEq`, using the cardinality theorem:

```lean
flowerVert_card : Fintype.card (FlowerVert u v g) = flowerVertCount u v g
```

The final F2 bridge theorem states:

```lean
flowerGraph_dist_hubs (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (flowerGraph u v g hu huv).dist
      ((flowerVertEquiv u v g hu huv) (.hub0 u v g))
      ((flowerVertEquiv u v g hu huv) (.hub1 u v g))
    = flowerHubDist u v g
```

---

## Connectivity

The connectivity proof (`flowerGraph'_connected`) uses the gadget chain lemma: within each gadget, the \(u+1\) vertices along the short path form a connected chain. Since the short path connects gadget source to gadget target, and the hub vertices are the source and target of the generation-0 edge, the full graph is connected by induction.
