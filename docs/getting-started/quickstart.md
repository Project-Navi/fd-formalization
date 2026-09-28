# Quickstart

Requires [elan](https://github.com/leanprover/elan), which installs the pinned Lean (v4.34.1); Lake fetches Mathlib.

```bash
git clone https://github.com/Project-Navi/fd-formalization.git
cd fd-formalization
lake exe cache get   # prebuilt Mathlib
lake build --wfail   # warnings, including sorry, are errors
```

## Verify

```bash
lake env lean -DwarningAsError=true FdFormal/Verify.lean   # axiom dashboard
lake lint                                                 # Mathlib linters
```

`Verify.lean` prints the axioms of 75 key declarations; each should use only `propext`, `Classical.choice` and `Quot.sound`. CI checks this.

## Files

| Module | Contents |
|---|---|
| `FlowerCounts` | edge and vertex counts, bounds, monotonicity |
| `FlowerDiameter` | hub distance \(L_g = u^g\) |
| `FlowerGraph` | `Fin`-indexed hub vertices |
| `FlowerLog` | log identities, squeeze bounds |
| `FlowerDimension` | F1: log-ratio limit |
| `FlowerLogRatio` | `HasLogRatioDimension` (definition) |
| `FlowerConstruction` | F2: explicit graph and hub distance |
| `FlowerGraphDimension` | F3: log-ratio dimension of the graphs |
| `BoxCounting` | box covering of graphs: `IsBox`, `boxCount`, cover and separation bounds |
| `BoxScaling` | the scaling limit behind box-counting exponents |
| `FlowerCells` | cells: copies of the generation-\(j\) flower inside generation \(k + j\) |
| `FlowerRadius` | rank values and the diameter bound \((2v + 1)\,u^g\) |
| `FlowerBoxDimension` | F4: box-counting dimension of the graphs |
| `PathGraphDist` | distances in `pathGraph` |
| `Verify` | axiom dashboard |

The main theorems assume \(1 < u\) (\(u = 1\) is the transfractal case) and \(u \leq v\). See [Proof Strategy](../explanation/proof-strategy.md).
