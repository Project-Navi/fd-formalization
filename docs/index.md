---
hide:
  - navigation
  - toc
---

<div class="hero-glow" markdown>

# fd-formalization

**Lean 4 + Mathlib formalization of \((u,v)\)-flower fractal dimension.**

Hub distance \(= u^g\) and log-ratio convergence to \(\frac{\log(u+v)}{\log u}\). Zero sorry, zero custom axioms.

[Get Started](getting-started/quickstart.md){ .md-button .md-button--primary }
[Theorems](reference/theorems.md){ .md-button }

</div>

---

## What it proves

For the arithmetic \((u,v)\)-flower model with \(1 < u \leq v\), this formalization proves:

| Theorem | Statement | File |
|---|---|---|
| **F1** --- Log-ratio convergence | \(\displaystyle\lim_{g \to \infty} \frac{\log \lvert V_g \rvert}{\log L_g} = \frac{\log(u+v)}{\log u}\) | `FlowerDimension.lean` |
| **F2** --- Hub distance bridge | \(\operatorname{dist}_G(\text{hub}_0, \text{hub}_1) = u^g\) | `FlowerConstruction.lean` |

In the physics literature (Rozenfeld et al. 2007), this log-ratio equals the box-counting fractal dimension \(d_B\). This is the ground truth formula that [navi-fractal](https://github.com/Project-Navi/navi-fractal) calibrates its sandbox dimension estimates against.

**Axiom boundary:** All results proved from Mathlib primitives --- `propext`, `Classical.choice`, `Quot.sound` only.

---

## Documentation

| Section | What you'll find |
|---|---|
| [Quickstart](getting-started/quickstart.md) | Build and verify the proofs |
| [Proof Strategy](explanation/proof-strategy.md) | Route B squeeze, mathematical background |
| [Graph Construction](explanation/graph-construction.md) | F2 bridge, structured gadgets, distance proof |
| [Theorems](reference/theorems.md) | Complete theorem catalog by file |
| [Roadmap](reference/roadmap.md) | Future theorem targets and sequencing |
