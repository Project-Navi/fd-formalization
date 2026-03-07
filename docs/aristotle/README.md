# Aristotle Independent Verification — Reference Only

**These artifacts are not reproducible on the current toolchain.**
They are retained as a historical record of the verification experiment,
not as drop-in replacements for the proofs in `FdFormal/`.

The `artifacts/` directory contains sorry-stubbed versions of the project's
Lean files, submitted to [Aristotle](https://aristotle.harmonic.fun) for
independent proof synthesis.

## Results

### Original campaign (FlowerCounts, FlowerDiameter, FlowerGraph, FlowerDimension)

| File | Sorries | Proved | Status |
|------|---------|--------|--------|
| FlowerCounts | 7 | 7 | Full independent proof |
| FlowerDiameter | 3 | 3 | Full independent proof |
| FlowerGraph | 3 | 3 | Full independent proof |
| FlowerDimension | 5 | 0 | Environment load failure (axiom conflict) |

The log-ratio convergence theorem (`flowerDimension`) could not be loaded into
Aristotle's environment due to axiom declarations shadowing function
definitions. The real-valued bounds and squeeze limit proof remain human-authored.

### Batch 1 (FlowerConstruction — irreflexivity + edge card)

| Lemma | Proved | Status |
|-------|--------|--------|
| `flowerEdge_card` | Yes | Integrated |
| `edgeSrc_ne_edgeTgt` | Yes | Integrated (with bonus helpers `embed_injective`, `embed_ne_new`) |
| `localSrc_ne_localTgt` | Yes | Integrated |

All proofs required significant rewrite for Lean 4.28.0 (`grind`, `exact?`,
`simp +decide` removed). Artifacts: `artifacts/batch1-*.lean.txt`.

### Batch 2 (FlowerConstruction — vertex card, gadget walks, projection)

| Lemma | Proved | Status |
|-------|--------|--------|
| `gadgetInternal_card` | Yes | Integrated |
| `flowerVert_card` | Yes | Integrated |
| `resolve_localEdge_adj` | Yes | Integrated |
| `short_path_consecutive_adj` | Yes | Integrated |
| `long_path_consecutive_adj` | Yes | Integrated |
| `resolve_src_eq_embed_edgeSrc` | Yes | Integrated |
| `resolve_tgt_eq_embed_edgeTgt` | Yes | Integrated |
| `project_embed` | Yes | Integrated |
| `project_hub0` | Yes | Integrated |
| `project_hub1` | Yes | Integrated |
| `project_new` | Yes | Integrated |
| `project_adj_or_eq` | No | Aristotle error (reason code 9) |

12 of 13 lemmas proved. All proofs rewritten for Lean 4.28.0
(`exact?` → term-mode, `aesop` → targeted simp, `simp +decide` → omega).
New import: `Mathlib.Algebra.BigOperators.Fin`.
Artifacts: `artifacts/batch2{a,b,c}-*.lean.txt`.

### Batch 3A (FlowerConstruction — projection atoms)

| Lemma | Proved | Status |
|-------|--------|--------|
| `project_edgeSrc_succ` | Yes | Integrated |
| `project_edgeTgt_succ` | Yes | Integrated |
| `project_adj_or_eq` | Yes | Integrated |

3 of 3 lemmas proved, including the stretch target `project_adj_or_eq`
(which failed as `project_adj_or_eq` in Batch 2 — decomposing into
micro-lemmas enabled success). All proofs rewritten for Lean 4.28.0.
Artifacts: `artifacts/batch3a-projection_atoms.lean.txt`.

### Batch 3B (FlowerConstruction — walk support)

| Lemma | Proved | Status |
|-------|--------|--------|
| `edgeSrc_zero` | No | Environment load failure |
| `edgeTgt_zero` | No | Environment load failure |
| `short_tgt_eq_succ_src` | No | Environment load failure |
| `short_first_eq_embed_src` | No | Environment load failure |
| `short_last_eq_embed_tgt` | No | Environment load failure |
| `long_tgt_eq_succ_src` | No | Environment load failure |
| `long_first_eq_embed_src` | No | Environment load failure |
| `long_last_eq_embed_tgt` | No | Environment load failure |
| `flowerGraph'_adj_iff` | No | Environment load failure |
| `gadget_short_walk` | No | Environment load failure |

0 of 10 — complete environment load failure. The `flowerGraph'` definition
using `⟨...⟩` for `Std.Irrefl` is valid on Lean 4.28.0 but not on
Aristotle's 4.24.0, cascading to block all targets. All 10 lemmas
proved by hand instead. Artifacts: `artifacts/batch3b-walk_support.lean.txt`.

### Batch 3C (FlowerConstruction — gadget adjacency chain)

| Lemma | Proved | Status |
|-------|--------|--------|
| `gadget_adj_chain` | Yes | Integrated |

1 of 1 — `gadget_adj_chain` proved, providing the step-replacement
engine for `flowerGraph'_walk_hubs`. Proof rewritten for Lean 4.28.0
(`aesop` → targeted simp, `simp +decide` → `dif_pos`/`dif_neg`,
`exact?` → explicit terms).
Artifacts: `artifacts/batch3c-gadget_chain.lean.txt`.

## Files

- `*_proved.lean` — Aristotle's output with proofs filled in (original campaign)
- `*.lean` — sorry-stubbed inputs as submitted (original campaign)
- `batch1-*.lean` — Batch 1 submission files
- `batch1-*.lean.txt` — Batch 1 Aristotle output (artifacts)
- `batch2{a,b,c}-*.lean` — Batch 2 submission files (3 sub-batches)
- `batch2{a,b,c}-*.lean.txt` — Batch 2 Aristotle output (artifacts)
- `batch3{a,b,c}-*.lean` — Batch 3 submission files
- `batch3{a,b,c}-*.lean.txt` — Batch 3 Aristotle output (artifacts)

These files are outside the `FdFormal/` build tree and are **not compiled
by `lake build`**. Do not rely on them for correctness claims.
