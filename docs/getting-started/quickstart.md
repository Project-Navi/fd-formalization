# Quickstart

Build and verify the \((u,v)\)-flower fractal dimension formalization.

---

## Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) (v4.28.0)
- [elan](https://github.com/leanprover/elan) (Lean version manager)

Mathlib is pulled automatically by Lake.

---

## Clone and build

```bash
git clone https://github.com/Project-Navi/fd-formalization.git
cd fd-formalization

# Download Mathlib cache (saves ~30 min of compilation)
lake exe cache get

# Build all files
lake build
```

The first build after `cache get` takes a few minutes to compile the project files against cached Mathlib oleans.

---

## Verify

### Check for sorry-freedom

```bash
lake build --wfail
```

This fails on any `sorry` or warning. A clean exit means every theorem is fully proved.

### Axiom dashboard

```bash
lake build FdFormal.Verify
```

This builds `Verify.lean`, which runs `#print axioms` on all 27 key declarations. Every declaration should depend only on `propext`, `Classical.choice`, and `Quot.sound` --- the standard Lean 4 axioms.

### Mathlib linter

```bash
lake lint
```

Checks all declarations against Mathlib's linter suite (naming conventions, `@[simp]` hygiene, documentation).

---

## Project structure

```
FdFormal/
  FlowerCounts.lean       -- Edge/vertex count formulas, bounds, monotonicity
  FlowerDiameter.lean     -- Hub distance: L_g = u^g
  FlowerGraph.lean        -- Hub vertices, structural helpers
  FlowerLog.lean          -- Log identities, squeeze bounds
  FlowerDimension.lean    -- Headline theorem: log-ratio limit (F1)
  FlowerLogRatio.lean     -- HasLogRatioDimension definition (F3 target)
  FlowerConstruction.lean -- SimpleGraph construction + dist = u^g (F2)
  GraphBall.lean          -- SimpleGraph.ball (upstream candidate)
  PathGraphDist.lean      -- pathGraph distance lemmas (upstream candidate)
  Verify.lean             -- #print axioms dashboard
```

### Proof spine

The formalization builds from bottom to top:

1. **FlowerCounts** --- exact edge count \(E_g = (u+v)^g\) and vertex recurrence \((w-1) N_g = (w-2) w^g + w\), with two-sided bounds and monotonicity
2. **FlowerDiameter** --- hub distance \(L_g = u^g\) as pure arithmetic recurrence
3. **FlowerLog** --- log identities: \(\log L_g = g \cdot \log u\), residual bounds for the squeeze
4. **FlowerDimension** --- the headline theorem via squeeze: \(\lim \log N_g / \log L_g = \log(u+v) / \log u\)
5. **FlowerConstruction** --- explicit `SimpleGraph` on `Fin`, hub distance bridge

See [Proof Strategy](../explanation/proof-strategy.md) for the full mathematical explanation.

---

## Hypotheses

All theorems require:

- \(1 < u\) --- excludes the transfractal case (\(u = 1\) gives infinite \(d_B\))
- \(u \leq v\) --- WLOG normalization from the source paper

---

## Connection to navi-fractal

This formalization proves the exact dimension formula that [navi-fractal](https://github.com/Project-Navi/navi-fractal) uses as calibration ground truth. The calibration instrument in navi-fractal generates \((u,v)\)-flower graphs and checks that its sandbox dimension estimates converge to \(\log(u+v) / \log u\) within tolerance.
