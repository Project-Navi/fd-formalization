# Fractal Dimension — Lean 4 Formalization

Formal verification of the (u,v)-flower analytical dimension formula from:

> H. D. Rozenfeld, S. Havlin & D. ben-Avraham, "Fractal and transfractal recursive scale-free nets," *New Journal of Physics* **9**, 175 (2007).

## What is verified

The fractal (box-counting) dimension of the (u,v)-flower network family:

```
d_B = ln(u + v) / ln(u)    for 1 < u ≤ v
```

This is the ground truth formula that [navi-fractal](https://github.com/Project-Navi/navi-fractal) calibrates its sandbox dimension estimates against (see the calibration table in that project's README).

### Proof spine

| Step | Declaration | File | Topic |
|------|-------------|------|-------|
| Construction | `FlowerGraph` | `FlowerGraph` | Recursive (u,v)-flower |
| Edge count | `flower_edge_count` | `FlowerCounts` | `E_g = (u+v)^g` |
| Vertex count | `flower_vertex_count` | `FlowerCounts` | `(w-1) N_g = (w-2) w^g + w` |
| Diameter | `flower_diam_eq` | `FlowerDiameter` | `L_g = u^g` |
| Dimension | `flower_dimension` | `FlowerDimension` | `d_B = log(u+v) / log(u)` |

### Upstream candidate

| Declaration | File | Topic | Mathlib status |
|-------------|------|-------|----------------|
| `SimpleGraph.ball` | `GraphBall` | Metric ball via `edist` | No `SimpleGraph.ball` in Mathlib |

## Axiom boundary

**None.** All results proved from Mathlib primitives — no custom axioms or typeclasses. The formalization uses `SimpleGraph.edist` for graph distance, `Fintype.card` for counting, `Real.log` for logarithms, and `Nat.rec` induction for generation-recursive proofs.

Run `#print axioms` in `FdFormal/Verify.lean` to confirm no `sorryAx` — all theorems should depend only on `[propext, Classical.choice, Quot.sound]`.

## Hypotheses

- `1 < u` — excludes the transfractal case (`u = 1` gives infinite d_B)
- `u ≤ v` — WLOG normalization from the source paper

## Building

Requires Lean 4 (v4.28.0) and Mathlib.

```bash
lake build
lake build --wfail   # fail on any sorry or warning
```

## Project structure

```
FdFormal/
  GraphBall.lean         — SimpleGraph.ball via edist (upstream candidate)
  FlowerGraph.lean       — Recursive (u,v)-flower construction
  FlowerCounts.lean      — Exact edge/vertex count formulas
  FlowerDiameter.lean    — Diameter scaling L_g = u^g
  FlowerDimension.lean   — Headline theorem: d_B = log(u+v) / log(u)
  Verify.lean            — #print axioms dashboard
```

## Mathematical background

The (u,v)-flower is a deterministic recursive network: start with two vertices connected by an edge (generation 0), then at each generation replace every edge with two parallel paths of lengths `u` and `v`. For `u > 1`, this produces a fractal network with finite box-counting dimension. For `u = 1`, the network is transfractal (small-world) with infinite dimension.

The dimension formula follows from three facts:
1. The edge count grows as `(u+v)^g` (each edge produces `u+v` new edges)
2. The vertex count grows proportionally to the edge count
3. The diameter scales as `u^g` (shortest hub-to-hub path recurses through the short side)

The ratio `log |V_g| / log L_g` therefore tends to `log(u+v) / log(u)`.

### Key references

- Rozenfeld, Havlin & ben-Avraham, NJP 9:175 (2007) — construction and dimension formula
- Song, Havlin & Makse, Nature 433:392 (2005) — fractal self-similarity of complex networks
- Furuya & Yakubo, Phys. Rev. E 84:036118 (2011) — multifractal spectrum (future work)

## Development Process

**What the author did**: The formalization architecture — choosing the proof spine
(counts → diameter → log-ratio), the vertex representation strategy, the decision
to target zero axioms, and the `edist`-based ball definition — is the core
contribution. The underlying mathematics is from Rozenfeld et al. 2007.

**What AI tools did**: Claude Opus assisted with Lean 4 syntax, Mathlib API
navigation, and proof term synthesis. These roles are analogous to `omega`,
`aesop`, and other proof automation — the strategy is human, the term-level
search is machine-assisted.

**Verification**: The final arbiter is the Lean compiler:
```bash
lake build --wfail   # type-checks or it doesn't
```

## License

Copyright 2026 Nelson Spence. Licensed under [Apache 2.0](LICENSE).
