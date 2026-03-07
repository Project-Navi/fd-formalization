[![CI](https://github.com/Project-Navi/fd-formalization/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Project-Navi/fd-formalization/actions/workflows/lean_action_ci.yml)
![Lean v4.28.0](https://img.shields.io/badge/Lean-v4.28.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-dep-blue)
![sorry-free](https://img.shields.io/badge/sorry--free-%E2%9C%93-brightgreen)
![no custom axioms](https://img.shields.io/badge/custom%20axioms-0-brightgreen)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-orange)](LICENSE)

# (u,v)-Flower Log-Ratio Convergence — Lean 4 Formalization

Formal verification of the vertex-count / hub-distance log-ratio limit for the (u,v)-flower network family, from:

> H. D. Rozenfeld, S. Havlin & D. ben-Avraham, "Fractal and transfractal recursive scale-free nets," *New Journal of Physics* **9**, 175 (2007).

## What is verified

For the arithmetic (u,v)-flower model, the log-ratio of vertex count to hub distance converges to `log(u+v) / log(u)`:

```
lim   log |V_g| / log L_g  =  ln(u + v) / ln(u)    for 1 < u ≤ v
g→∞
```

In the physics literature (Rozenfeld et al. 2007), this quantity equals the box-counting fractal dimension `d_B`. **This formalization proves the log-ratio convergence; a formal bridge to a box-counting definition is not yet built** (see `debt.md`).

This is the ground truth formula that [navi-fractal](https://github.com/Project-Navi/navi-fractal) calibrates its sandbox dimension estimates against (see the calibration table in that project's README).

### Proof spine

| Step | Declaration | File | Topic |
|------|-------------|------|-------|
| Edge count | `flowerEdgeCount_eq_pow` | `FlowerCounts` | `E_g = (u+v)^g` |
| Vertex count | `flowerVertCount_eq` | `FlowerCounts` | `(w-1) N_g = (w-2) w^g + w` |
| Two-sided bounds | `flowerVertCount_lower/upper` | `FlowerCounts` | Squeeze inputs |
| Monotonicity | `flowerVertCount_strict_mono` etc. | `FlowerCounts`/`FlowerDiameter` | `N_g`, `E_g`, `L_g` strictly increasing |
| Hub distance | `flowerHubDist_eq_pow` | `FlowerDiameter` | `L_g = u^g` |
| Hub vertices | `hub0`, `hub1` | `FlowerGraph` | Distinguished vertices |
| Log identities | `log_flowerHubDist_eq` etc. | `FlowerLog` | `log L_g = g · log u` |
| **Log-ratio limit** | **`flowerDimension`** | **`FlowerDimension`** | **`lim log N_g / log L_g = log(u+v) / log(u)`** |

### Upstream candidate

| Declaration | File | Topic | Mathlib status |
|-------------|------|-------|----------------|
| `SimpleGraph.ball` + 7 core lemmas | `GraphBall` | Open metric ball via `edist` (8 core + convenience lemmas) | No `SimpleGraph.ball` in Mathlib; PR ready to open |

## Axiom boundary

**Zero custom axioms.** All results proved from Mathlib primitives. The `#print axioms` dashboard in `Verify.lean` confirms every declaration depends only on `[propext, Classical.choice, Quot.sound]` with no `sorryAx`.

The log-ratio theorem uses pure arithmetic recurrences for vertex count and hub distance — no `SimpleGraph` construction is in the critical path. A bridge theorem connecting `flowerHubDist` to `SimpleGraph.edist` on an explicit graph model, and further to a formal box-counting dimension definition, is deferred (see `debt.md`).

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
  GraphBall.lean         — SimpleGraph.ball (open ball via edist), 8 core + convenience lemmas (upstream candidate)
  FlowerGraph.lean       — Hub vertices and structural helpers
  FlowerCounts.lean      — Exact edge/vertex count formulas, bounds, monotonicity
  FlowerDiameter.lean    — Hub-distance scaling L_g = u^g, cast identities
  FlowerLog.lean         — Log identities and squeeze-sandwich bounds (all proofs complete)
  FlowerLogRatio.lean    — HasLogRatioDimension definition (bridge target)
  FlowerDimension.lean   — Headline theorem: log-ratio limit = log(u+v) / log(u)
  PathGraphDist.lean     — pathGraph distance lemmas (all proofs complete)
  FlowerConstruction.lean — F2 bridge construction (4 sorry stubs remaining)
  Verify.lean            — #print axioms dashboard (17 declarations)
```

## Mathematical background

The (u,v)-flower is a deterministic recursive network: start with two vertices connected by an edge (generation 0), then at each generation replace every edge with two parallel paths of lengths `u` and `v`. For `u > 1`, the physics literature identifies this as a fractal network with finite box-counting dimension `d_B = log(u+v)/log(u)`. For `u = 1`, the network is transfractal (small-world).

The log-ratio convergence proof (Route B — squeeze) works as follows:
1. Two-sided bounds: `c₁ · w^g ≤ N_g ≤ c₂ · w^g` where `w = u + v`
2. Hub distance: `L_g = u^g`
3. Decompose `log(N_g) / (g · log u) = residual + log(w) / log(u)`
4. Squeeze the residual to 0 between `log(c₁) / (g · log u)` and `log(2) / (g · log u)`
5. The limit is `log(u + v) / log(u)`

### Key references

- Rozenfeld, Havlin & ben-Avraham, NJP 9:175 (2007) — construction and dimension formula
- Song, Havlin & Makse, Nature 433:392 (2005) — fractal self-similarity of complex networks
- Furuya & Yakubo, Phys. Rev. E 84:036118 (2011) — multifractal spectrum (future work)

## Development Process

**What the author did**: The formalization architecture — choosing the proof spine
(counts + bounds → hub distance → squeeze limit), the decision to use pure arithmetic
recurrences (Option 3) instead of a full SimpleGraph construction, and the zero-axiom
target — is the core contribution. The underlying mathematics is from Rozenfeld et al. 2007.

**What AI tools did**: Claude Opus assisted with Lean 4 syntax, Mathlib API
navigation, and proof term synthesis. Aristotle (Harmonic) independently proved
leaf lemmas (positivity, monotonicity, cast identities) via automated proof search.
These roles are analogous to `omega`, `aesop`, and other proof automation — the
strategy is human, the term-level search is machine-assisted.

**Verification**: The final arbiter is the Lean compiler:
```bash
lake build --wfail   # type-checks or it doesn't
```

## License

Copyright 2026 Nelson Spence. Licensed under [Apache 2.0](LICENSE).
