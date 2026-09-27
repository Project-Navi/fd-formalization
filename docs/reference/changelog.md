# Changelog

See [Releases](https://github.com/Project-Navi/fd-formalization/releases) on GitHub.

---

## 2026-03-28

### [#12](https://github.com/Project-Navi/fd-formalization/pull/12) --- Aristotle proof golf

Proof golf pass using Aristotle-discovered simplifications. Eliminates intermediate bindings and restores named squeeze waypoints in the headline theorem.

**Changed files:** `FlowerConstruction.lean`, `FlowerCounts.lean`, `FlowerDiameter.lean`, `FlowerDimension.lean`, `FlowerLog.lean`, `GraphBall.lean`, `PathGraphDist.lean`

Highlights:

- `flowerVertCountReal_pos` and `flowerHubDistReal_pos` are now term-mode proofs (`Nat.cast_pos.mpr ...`)
- `FlowerVert.hub0_ne_hub1` is now term-mode (`Sum.inl_injective.ne (by decide)`)
- `hc₁_pos` in the headline theorem uses `sub_pos.mpr` pattern directly
- Named squeeze waypoints (`h_lo`, `h_hi`, `h_res`) restored in `flowerDimension` for readability
- Net reduction: 49 insertions, 104 deletions across 7 files

### [#11](https://github.com/Project-Navi/fd-formalization/pull/11) --- Mathlib style cleanup

Proof style tightening from Mathlib PR review feedback. Aligns proof idioms with upstream conventions.

**Changed files:** `FlowerConstruction.lean`, `FlowerCounts.lean`, `FlowerDimension.lean`, `FlowerLog.lean`, `GraphBall.lean`, `PathGraphDist.lean`

Highlights:

- `flowerGraph'_adj_iff` now uses `.rfl` instead of tactic proof
- `ball_one` and `ball_top` use `simp` proofs (leveraging `ENat.lt_one_iff_eq_zero` and `lt_top_iff_ne_top`)
- Various `show ... from by` patterns replaced with `show ... by` (dropped deprecated `from`)
- Net reduction: 50 insertions, 67 deletions across 7 files
