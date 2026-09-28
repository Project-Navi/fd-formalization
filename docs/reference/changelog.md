# Changelog

Notable merged pull requests.

---

## 2026-09-27

- [#21](https://github.com/Project-Navi/fd-formalization/pull/21) --- F4: the flower graphs have box-counting dimension \(\log(u+v)/\log u\) (`flowerGraph_hasBoxDimension`), completing the roadmap. New modules `BoxCounting`, `BoxScaling`, `FlowerCells`, `FlowerRadius` and `FlowerBoxDimension`. Lean and Mathlib move to v4.34.1; `GraphBall.lean` is removed in favour of Mathlib's `SimpleGraph.ball`. 52 declarations on the axiom dashboard.

## 2026-03-28

- [#12](https://github.com/Project-Navi/fd-formalization/pull/12) --- proof golf from Aristotle-found simplifications: term-mode proofs for `flowerVertCountReal_pos`, `flowerHubDistReal_pos` and `FlowerVert.hub0_ne_hub1`; named squeeze waypoints restored in `flowerDimension`. 7 files, net −55 lines.
- [#11](https://github.com/Project-Navi/fd-formalization/pull/11) --- Mathlib style cleanup from PR review: `.rfl` for `flowerGraph'_adj_iff`, `simp` proofs for `ball_one` and `ball_top`, `show … from by` replaced. 7 files, net −17 lines.
