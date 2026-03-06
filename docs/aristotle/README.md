# Aristotle Independent Verification

The `artifacts/` directory contains sorry-stubbed versions of the project's
Lean files, submitted to [Aristotle](https://aristotle.harmonic.fun) for
independent proof synthesis.

## Results

| File | Sorries | Proved | Status |
|------|---------|--------|--------|
| FlowerCounts | 7 | 7 | Full independent proof |
| FlowerDiameter | 3 | 3 | Full independent proof |
| FlowerGraph | 3 | 3 | Full independent proof |
| FlowerDimension | 5 | 0 | Environment load failure (axiom conflict) |

The headline theorem (`flowerDimension`) could not be loaded into
Aristotle's environment due to axiom declarations shadowing function
definitions. The ℝ bounds and squeeze limit proof remain human-authored.

## Files

- `*_proved.lean` — Aristotle's output with proofs filled in
- `*.lean` — sorry-stubbed inputs as submitted

These files are outside the `FdFormal/` build tree and are not compiled
by `lake build`.
