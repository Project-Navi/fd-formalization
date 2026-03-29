# CLAUDE.md — fd-formalization

## Project

Lean 4 (v4.28.0) + Mathlib formalization of log-ratio convergence for (u,v)-flower
graphs. Headline theorem: `flowerDimension` in `FlowerDimension.lean`. Zero sorry,
zero custom axioms on main branch.

## Build & verify

```bash
lake build --wfail      # primary check — warnings are errors
lake lint                # Mathlib linter suite
lake build FdFormal.Verify  # axiom dashboard (#print axioms)
```

Pre-commit hooks enforce: trailing whitespace, EOF newline, merge conflicts,
copyright headers on all `.lean` files.

## Lean style (Mathlib conventions)

### Naming

- **Prop terms** (theorems): `snake_case` — `mul_comm`, `flowerVertCount_pos`
- **Types/Props/Sorts** (structures): `UpperCamelCase` — `FlowerVert`, `HasLogRatioDimension`
- **Other Type terms**: `lowerCamelCase` — `hub0`, `edgeSrc`, `instFintypeFlowerEdge`
- **UpperCamelCase inside snake_case**: becomes `lowerCamelCase` — `neZero_iff` not `NeZero_iff`
- **Conclusion-first**: `lt_of_le_of_ne` (conclusion `lt`, hypotheses `le` and `ne`)
- **`_of_` pattern**: hypotheses joined by `_of_` in order: `C_of_A_of_B` for `A → B → C`
- **American English**: `factorization` not `factorisation`

### Formatting

- **100-char line limit** (linter-enforced)
- **`by` at end of preceding line**, never on its own line
- **2-space indent** for proof bodies; **4-space** for multi-line statements
- **No empty lines** inside declarations (linter-enforced)
- **Focusing dots** `·` flush with current indent, tactics indented beneath
- **`:`, `:=`, infix ops** at end of line, not start of next
- **`fun x ↦`** not `λ x ↦`; **no `$`** (use `<|` if needed)

### Tactics

| Goal type | Preferred tactic |
|-----------|-----------------|
| Linear ℕ/ℤ arithmetic | `omega` |
| Numerical evaluation | `norm_num` |
| Decidable props | `decide` |
| Positivity (0 ≤ x, 0 < x) | `positivity` |
| Monotonicity/congruence | `gcongr` |
| General simplification | `simp` (last resort) |
| Nonlinear arithmetic | `nlinarith [hint]` |
| ℕ subtraction → ℤ | `zify [h1, h2]` |

- **Terminal `simp`**: do NOT squeeze (maintenance burden from lemma renames)
- **Non-terminal `simp`**: MUST be `simp only [...]`
- **One tactic per line** (semicolons only for short single-idea sequences)
- **Set equality**: `ext v; simp [...]` is canonical — don't build manual
  `constructor`/`rcases`/`absurd` chains when `simp` with the right lemma set closes it
- **Skip `ext`** when `simp` alone closes a set equality (e.g., `ball_zero`)
- **`simp` before `tauto`**: `simp` + commutativity lemmas (`adj_comm`, `or_comm`)
  often closes goals that look like they need `tauto`
- **`.rfl`** not `Iff.rfl` — dot notation for constructor terms
- **Named lemmas over `show ... from rfl`**: e.g., `one_add_one_eq_two.symm`
  not `show (2 : ℕ∞) = 1 + 1 from rfl`

### Attributes

- `@[simp]`: equations/iff where LHS is more complex than RHS; must not loop
- `@[ext]`: extensionality lemmas
- `@[simps]`: auto-generate projection simp lemmas for structures
- `@[gcongr]`: congruence lemmas of form `f x₁ ∼ f x₂` given `x₁ ∼ x₂`

### Types and definitions

- **`Type*`** not `Type _` (performance requirement)
- **`where` syntax** for instances, not braces
- **Named instances**: `instance instFintypeFlowerEdge : Fintype (FlowerEdge u v g)`
- **`variable` blocks** for shared parameters — don't repeat `(u v g : ℕ) (hu : 1 < u)`
- **Hypotheses left of colon** — `(h : 1 < n) : 0 < n` not `: 1 < n → 0 < n`
- **`abbrev`** (reducible) requires justification; `@[irreducible]` requires justification
- **Classical by default** — don't thread `Decidable` instances unless the type requires them
- **Definition argument order**: choose to minimize downstream `symm`/`comm` calls —
  e.g., `{v | G.edist v c < r}` not `{v | G.edist c v < r}` when most API lemmas
  state the varying argument first

### Documentation

- **Module docstring** (`/-! ... -/`) required after imports: title, summary,
  Main definitions, Main statements, Implementation notes, References, Tags
- **Definition docstrings** (`/-- ... -/`) required on every `def` (linter: `docBlame`)
- **References**: cite as `[AuthorYear]`, anchor in `docs/references.bib`

### Imports

- **Granular imports only** — never `import Mathlib`
- Import hierarchy: Algebra → Order → Topology → Analysis (no cross-category violations)
- Files under ~1000 lines; split along natural boundaries

## Aristotle prover

**Role: leaf-lemma grinder and dependency detector, not theorem architect.**

### When to use

- Cast-control lemmas (ℕ → ℝ), positivity/nonzeroness, algebraic reshaping
- Squeeze bounds, pow/log simplification, recurrence-to-closed-form algebra
- High success on algebraic/order-theoretic leaves

### When NOT to use

- Headline theorems, design decisions, anything where definitions are still moving
- If you can't explain in one sentence why the lemma is true, don't submit it

### Submission protocol

1. **Freeze the statement** — hand-design def + statement, compile to sorry, then submit
2. **Each sorry = one leaf** — one concept, one obvious target, short dependency cone
3. **Proof-shaped files** — short helpers first, named intermediates, minimal imports
4. **Batch by type**: positivity → algebra → squeeze → limits → cleanup
5. **`prove_file` with `wait=False`** — runs take minutes to hours; don't poll in tight loops

### Output handling

- Keep the statement, keep discovered dependencies
- **Rewrite proof into clean human-owned form** — Aristotle output is draft, not scripture
- Artifacts go to `docs/aristotle/artifacts/*.lean.txt` (outside build tree)

### Known limitations

- Aristotle runs Lean 4.24.0 — outputs may not compile on our 4.28.0
- Sometimes generates `exact?` (interactive-only tactic) — rewrite manually
- Do NOT use `axiom` to provide upstream lemmas — shadows function definitions

## Hard-won API gotchas

### Nat.cast

- After `Nat.cast_sub`, need `simp only [Nat.cast_ofNat, Nat.cast_one]` to normalize
  `↑2 → 2` and `↑1 → 1` before `linarith` can close
- `exact_mod_cast` resolves `↑n` vs `n` mismatches
- `Nat.cast_pos` for `0 < ↑n ↔ 0 < n`

### Real.log

- `Real.log 0 = 0` — positivity lemmas are load-bearing
- `log_pow (x : ℝ) (n : ℕ) : log (x ^ n) = n * log x`
- `log_pos (h : 1 < x) : 0 < log x`

### Filter.Tendsto

- `Tendsto.squeeze'` args: lower_tendsto, upper_tendsto, lower_eventually, upper_eventually
- `Tendsto.atTop_mul_const`: positivity proof FIRST, then tendsto proof
- `tendsto_natCast_atTop_atTop` needs explicit `(R := ℝ)`
- `filter_upwards [eventually_gt_atTop 0] with g hg` — standard pattern

### ℕ arithmetic

- `ring` does NOT close `a * a^n = a^(n+1)` on ℕ — use `rw [pow_succ, mul_comm]`
- `zify [h1, h2] at ih ⊢` converts ℕ subtraction to ℤ

### SimpleGraph

- `SimpleGraph.mk` needs `Std.Symmetric` and `Std.Irrefl` wrappers (not raw ∀)
- `pathGraph` exists in Mathlib (Hasse on Fin n) but has zero distance lemmas
- `SimpleGraph.ball` does not exist in Mathlib — our `GraphBall.lean` fills this gap

## Variable naming

- **Never shadow prelude names**: don't use `le`, `lt`, `eq`, `ne` as variable names
- Standard parameters in this repo: `u v g : ℕ`, `hu : 1 < u`, `huv : u ≤ v`
- `w` is shorthand for `u + v` (edge branching factor)

## File structure

| File | Role | Status |
|------|------|--------|
| `FlowerCounts.lean` | Edge/vertex recurrences + bounds | Proved |
| `FlowerDiameter.lean` | Hub distance L_g = u^g | Proved |
| `FlowerGraph.lean` | Hub vertices, structural helpers | Proved |
| `FlowerLog.lean` | Log identities + squeeze bounds | Proved |
| `FlowerDimension.lean` | Headline theorem (squeeze limit) | Proved |
| `FlowerLogRatio.lean` | HasLogRatioDimension definition | Definition only |
| `GraphBall.lean` | SimpleGraph.ball open metric balls (upstream candidate) | Proved |
| `PathGraphDist.lean` | pathGraph distance (upstream candidate) | Proved |
| `FlowerConstruction.lean` | F2 bridge (structured gadgets) | Proved |
| `Verify.lean` | Axiom dashboard | Proved |

## Workflow rules

- **No sorries on main** — every theorem fully proved before shipping
- **Internal docs** (`docs/internal/`) are NOT committed to git
- **Commit messages**: substantive, not ceremonial
- Feature branches merge to main via fast-forward; delete after merge
- **Mathlib PR process**: post to Zulip first, small PRs preferred, AI disclosure required
- **PR description format**: one-line summary → blank line → AI disclosure (1-2 sentences)
  → Zulip link → `---` → template buttons. No design-decision sections, no tables.
- **Review responses**: one sentence per comment, inline on the diff where possible.
  No tables, headers, diff summaries, or structured documents. Let the code speak.
- **AI disclosure**: in PR body only, not in commit `Co-Authored-By` tags
- **Reviewer disagreements**: defer to the later or more authoritative reviewer
- **File-author naming preferences**: defer (e.g., `ball_mono` over `ball_subset_ball`)
