# AGENTS.md — Lean 4 + Mathlib conventions

Shared conventions for Lean 4 formalization repos. Task-specific proof obligations take
precedence over these generic conventions. Toolchain and Mathlib are pinned to
the same release across repos (currently `v4.28.0`), so lemmas can be ported between them
without a bump. API notes below were checked against that pin; re-check them after a bump.

## Invariants

- **No `sorry` on the default branch.** Every declaration is fully proved before merge.
- **No `axiom` declarations.** Classical results that are not proved are assumed through a
  typeclass or structure field (see *Assumed results*, which needs approval), never
  through `axiom`.
- **Axiom allowlist**: every public result depends only on `propext`, `Classical.choice`
  and `Quot.sound`. Anything else, including `sorryAx`, is a failure.
- **Every module compiles.** `lake build` builds only what the root imports, so a file
  nobody imports is never checked and can rot silently. CI builds every tracked module.
- **Assumption changes require approval.** Never complete an assigned proof by adding an
  unproved hypothesis, infrastructure field, or equivalent assumption unless the task
  explicitly authorizes a conditional result. A clean axiom report does not discharge
  theorem hypotheses. Report the complete theorem signature and any remaining assumed
  mathematical results.

## Build & verify

```bash
lake exe cache get                                   # Mathlib oleans; never build Mathlib
lake build --wfail                                   # warnings are errors (includes sorry)
lake lint                                            # Mathlib environment linters
lake env lean -DwarningAsError=true <Pkg>/Verify.lean   # axiom dashboard
```

- `Verify.lean` holds one `#print axioms` per selected declaration: every headline result
  and the supporting declarations the docs cite, not every public theorem. Add a line when
  you add one of those. CI checks each record present against the allowlist; it does not
  check that the selection is complete.
- If the sandbox cannot install Lean or fetch the Mathlib cache, push to a draft PR and
  let CI build and verify. Report which checks ran where; never claim a local build that
  did not happen.
- Audit for placeholders: `rg -n '\bsorry\b|sorryAx' <Pkg>` must return nothing, even in
  comments; CI runs the same check.
- If a repo has a docs site, `uv run zensical build` must succeed; CI also checks the
  built site's local links.
- If a repo has a `Makefile`, use its targets (`build`, `verify`, `audit`, `lint`) as
  the canonical commands.

## Project configuration

- Lean options live in `lakefile.toml` `[leanOptions]`, the single source of truth. Do
  not add per-file `set_option` for them.
  ```toml
  [leanOptions]
  pp.unicode.fun = true
  relaxedAutoImplicit = false
  autoImplicit = false
  weak.linter.mathlibStandardSet = true
  linter.style.longLine = true
  linter.style.lambdaSyntax = true
  linter.style.dollarSyntax = true
  linter.style.cdot = true
  linter.style.missingEnd = true
  ```
  Existing per-file `set_option autoImplicit false` lines are redundant. Don't add new ones.
- `lintDriver = "batteries/runLinter"`.
- Mathlib is required at a release tag (`rev = "v4.28.0"`), with no local fork and no
  `require` overrides. Bump only when a needed API landed or changed.

## File layout

Every `.lean` file, in order:

1. Copyright header, matching the repository's `LICENSE` and actual contributors (the
   example below is this repo's; list every author of the file and keep existing credit):
   ```lean
   /-
   Copyright (c) 2026 Nelson Spence. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Nelson Spence
   -/
   ```
2. Granular imports. **Never `import Mathlib`.**
3. Module docstring `/-! ... -/`: title, summary, `## Main definitions`,
   `## Main statements`, `## Implementation notes`, `## References`, `## Tags`.

- Keep files under ~1000 lines and split along natural boundaries.
- Respect the import hierarchy: Algebra → Order → Topology → Analysis.
- Every `def` has a `/-- ... -/` docstring (the `docBlame` linter checks this).
- Cite references as `[AuthorYear]`.

## Naming (Mathlib)

- Theorems (Prop terms): `snake_case`, e.g. `flowerVertCount_pos`.
- Types, structures, classes, Props-as-types: `UpperCamelCase`.
- Other terms (defs, functions, instances): `lowerCamelCase`.
- An UpperCamelCase name inside snake_case becomes lowerCamelCase: `neZero_iff`, not
  `NeZero_iff`.
- Conclusion first, hypotheses joined by `_of_` in order: `C_of_A_of_B` for `A → B → C`.
- American English (`factorization`).
- Name instances explicitly: `instance instFintypeFoo : Fintype Foo`.
- Never shadow prelude names with variables (`le`, `lt`, `eq`, `ne`).
- Fix one set of standard parameter names per repo and declare them in `variable` blocks.

## Formatting

- 100-character lines.
- `by` at the end of the preceding line, never on its own line.
- 2-space indent for proof bodies; 4-space for continuation lines of a statement.
- No blank lines inside a declaration.
- Focusing dots `·` flush with the current indent, with the tactics beneath them.
- `:`, `:=` and infix operators end a line; they don't start the next one.
- `fun x ↦`, not `λ`. No `$`; use `<|`.
- One tactic per line. Semicolons are only for a short sequence that expresses one idea.

## Definitions and statements

- `Type*`, not `Type _`.
- `where` syntax for instances, not braces.
- Hypotheses go left of the colon: `(h : 1 < n) : 0 < n`, not `: 1 < n → 0 < n`.
- `abbrev` and `@[irreducible]` each need a stated justification.
- Classical by default. Don't thread `Decidable` instances unless the type demands them.
- Order definition arguments to match the API lemmas you'll use, e.g.
  `{v | G.edist v c < r}` if the lemmas put the varying argument first, so downstream
  proofs don't need `symm`/`comm`.
- If a construction has distinguished points, make them definitionally where the API
  expects them, e.g. build an equivalence to `Fin n` by hand so the hubs land at `0` and
  `1`. `Fintype.equivFinOfCardEq` scatters them to unknown indices.

## Attributes

- `@[simp]` on equations or iffs whose LHS is more complex than the RHS. It must not loop.
- `@[ext]` on extensionality lemmas; `@[simps]` for structure projections.
- `@[gcongr]` on congruence lemmas of the form `f x₁ ∼ f x₂` given `x₁ ∼ x₂`.

## Tactics

| Goal | Reach for |
|------|-----------|
| Linear ℕ/ℤ arithmetic | `omega` |
| Numerals | `norm_num` |
| Decidable props | `decide` |
| `0 ≤ x`, `0 < x` | `positivity` |
| Monotonicity / congruence | `gcongr` |
| Nonlinear arithmetic | `nlinarith [hints]` |
| ℕ subtraction | `zify [h₁, h₂]` first |
| Field algebra | `field_simp`, then `ring` or `linarith` |
| General rewriting | `simp` (last resort) |

- A terminal `simp` stays unsqueezed, since squeezed lists break on lemma renames.
- A non-terminal `simp` must be `simp only [...]`.
- For set equality, `ext v; simp [...]` is canonical. Skip `ext` when `simp` alone closes
  it. Don't hand-build `constructor`/`rcases`/`absurd` chains.
- `simp` with commutativity lemmas (`adj_comm`, `or_comm`) often closes goals that look
  like they need `tauto`.
- Write `.rfl`, not `Iff.rfl`. Prefer a named lemma to `show _ from rfl`, e.g.
  `one_add_one_eq_two.symm`.
- When a `simp` call leaves an unexpected residual goal, an explicit
  `rw [defn, lemma₁, lemma₂]` chain is often more robust.
- `exact?`, `apply?` and `simp?` are for exploration only. Never commit them.

## API notes (Mathlib v4.28.0)

**Casts**
- After `Nat.cast_sub`, normalize with `simp only [Nat.cast_ofNat, Nat.cast_one]` before
  `linarith` can close the goal.
- `exact_mod_cast` settles `↑n` vs `n` mismatches.
- `Nat.cast_pos : 0 < (↑n : R) ↔ 0 < n`.
- `tendsto_natCast_atTop_atTop` needs an explicit `(R := ℝ)`.

**ℕ and `Fin`**
- `ring` does not close `a * a ^ n = a ^ (n + 1)` on ℕ. Use `rw [pow_succ, mul_comm]`.
- `omega` does not see `Fin` value facts. State them first, e.g.
  `have : (j.succ : ℕ) = j + 1 := Fin.val_succ j`.
- `i ≤ 0` on `Fin` to `i = 0`: `Fin.le_zero_iff.mp`, not `ext; omega`.
- `Function.iterate_succ_apply'` unfolds `f^[n+1] x = f (f^[n] x)` from the right.

**Real analysis**
- `Real.log 0 = 0`, so positivity side conditions are load-bearing.
- `Real.log_pow : log (x ^ n) = n * log x`; `Real.log_pos : 1 < x → 0 < log x`.
- `Real.rpow_sub_one (hv : v ≠ 0) : v ^ (p - 1) = v ^ p / v`.
- `Real.rpow_le_rpow` needs `0 ≤ base` and `0 ≤ exponent`; `Real.rpow_mul` needs `0 ≤ x`.
- `one_div_nonneg.mpr` gives `0 ≤ 1 / (p - 1)` from `0 < p - 1`.
- `ContDiff` at `n = ⊤` reduces to an existential, so dot notation (`.comp`) fails. Call
  `ContDiff.comp hg hf` as a function.
- `ContDiff.continuous_fderiv` takes `(hn : n ≠ 0)`, not `1 ≤ n`. Discharge it with
  `(by decide)`.
- `LinearMap.isUnit_iff_ker_eq_bot` needs the `LinearMap.` prefix.
- There is no standalone `continuous_det`; `grind +suggestions` can derive it.

**Filters**
- `Tendsto.squeeze'` argument order: lower tendsto, upper tendsto, lower eventually,
  upper eventually.
- `Tendsto.atTop_mul_const` takes the positivity proof first, then the tendsto.
- Standard pattern: `filter_upwards [eventually_gt_atTop 0] with g hg`.

**Graphs, order, dynamics**
- `SimpleGraph.mk` needs the `Std.Symmetric` / `Std.Irrefl` wrappers, not a raw `∀`.
- `pathGraph` exists, but Mathlib has no distance lemmas for it.
- `OrderHom.nextFixed` (Knaster–Tarski) needs `CompleteLattice α`.
- Periodic points live in `Dynamics.PeriodicPts.Defs` (`Function.minimalPeriod`,
  `Function.IsPeriodicPt`), not `GroupTheory.OrderOfElement`.

**Measure and dimension**
- Area formula: `MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv` in
  `Mathlib.MeasureTheory.Function.Jacobian`.
- `dimH`, `ContDiffOn.dimH_image_le` and `hausdorffMeasure_of_dimH_lt` are in
  `Mathlib.Topology.MetricSpace.HausdorffDimension`.
- `absolutelyContinuous_isAddHaarMeasure` is in `Mathlib.MeasureTheory.Measure.Haar.Unique`.
- Bounded sets: `Bornology.IsVonNBounded ℝ S`.

## Assumed results

Only when the task explicitly authorizes a conditional result (see *Invariants*). When a
classical result is too large to prove in the repo, assume it explicitly and keep the
boundary visible:

- Bundle the assumptions as fields of a typeclass or structure (an `…Infra` class),
  one field per classical result, each with a docstring naming its source.
- Theorems take the class as a hypothesis, so every dependency is visible in the
  signature and `#print axioms` stays clean.
- Put the consequences you prove from the fields in separate lemma files. Only add a
  field when it provably cannot be derived from the existing ones.
- Keep proof trees that don't need the assumptions free of any import of the class.

## Documentation must match the code

- Every Lean name that appears in the README or docs must resolve. Check this
  mechanically by generating a file of `#check @Name` lines and running
  `lake env lean` on it.
- State hypotheses exactly as in the theorem (e.g. `1 < u`, `u ≤ v`), and state what is
  **not** formalized. Never let a theorem name or summary claim more than the
  statement proves.
- Keep a short list of public names (the headline results) and make sure `Verify.lean`
  covers all of them.

## Aristotle (automated prover)

Aristotle grinds leaf lemmas and detects dependencies. It is not the theorem architect.

- **Good targets**: cast control (ℕ → ℝ), positivity and nonzeroness, algebraic
  reshaping, `Fin` arithmetic, rpow/log/pow simplification, squeeze bounds,
  recurrence-to-closed-form algebra.
- **Bad targets**: headline theorems, design decisions, anything whose definitions are
  still moving. If you can't say in one sentence why a lemma is true, don't submit it.
- **Protocol**:
  1. Freeze the statement: hand-write the definition and statement, and compile with `sorry`.
  2. One `sorry` per leaf: one concept, an obvious target, a short dependency cone.
  3. Proof-shaped files: short helpers first, named intermediates, minimal imports.
  4. Batch by kind: positivity → algebra → analysis → cleanup.
  5. Submit with `wait=False`. Runs take minutes to hours, so don't poll in a tight loop.
- **Output is a draft.** Keep the statement and any dependencies it discovered, then
  rewrite the proof into clean, human-owned form:
  - Rewrite `import Mathlib` to granular imports.
  - Replace `exact?` with the actual term or tactic.
  - Reject any `axiom` it introduces, since axioms can shadow real definitions.
- Before trusting output, check Aristotle's Lean version against `lean-toolchain`.
- Keep raw prover artifacts and run logs out of the public repository. Commit only the
  rewritten proofs, and credit Aristotle in the README.
