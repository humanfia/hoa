# Verification — `icho_2026_t9_a7`

## Deliverables

- `answer.md` — natural-language answer + source-grounding explanation.
- `IChO2026Problems/problem_icho_2026_t9_a7.lean` — Lean 4 formalization with substantive
  theorems for both requested outputs and supporting component-accounting/mass lemmas.

## Final answer (requested outputs)

| Target output       | Value | Kind          |
|---------------------|-------|---------------|
| `first_fragment_mz` | **455** | exact integer (m/z, [M+Na]⁺ of the C₂₇H₂₈O₅ fragment) |
| `second_fragment_mz` | **376** | exact integer (m/z, [M+Na]⁺ of the C₂₂H₂₅O₄ fragment) |

## Lean verification commands and results

All commands run from `/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t9_a7/campaign/workspace`.

Toolchain: `leanprover/lean4:v4.31.0` (`lean-toolchain`), deps from `lake-manifest.json`
(mathlib v4.31.0 already present under `.lake/packages`).

### 1. Compile the standalone problem file

```
lake env lean IChO2026Problems/problem_icho_2026_t9_a7.lean
```

Result: **exit code 0** (no errors, no warnings).  Stdout was the output of the live
`#print axioms` diagnostics (see §2).  No `sorry`, `admit`, `native_decide`, or `axiom`
declarations appear anywhere in the file (grep confirmed; the only textual hit is a
word inside a `/-! … -/` doc comment, not code).

### 2. Inspect axioms of the final theorems

`#print axioms` commands are embedded at the end of the file; their output on a clean run:

```
'icho_2026_t9_a7_first_fragment_mz' does not depend on any axioms
'icho_2026_t9_a7_second_fragment_mz' does not depend on any axioms
'IChO2026.Problems.T9A7.firstFragment_neutral_mass_explicit' depends on axioms: [propext]
'IChO2026.Problems.T9A7.secondFragment_neutral_mass_explicit' depends on axioms: [propext]
```

Interpretation:

- The two headline theorems (`..._first_fragment_mz`, `..._second_fragment_mz`, proved by
  `decide`) are **fully kernel-checked and use no axioms whatsoever** — not even
  `propext`/`Classical.choice`/`Quot.sound`.
- The two auxiliary `..._explicit` lemmas (proved by `norm_num`) use only the standard
  logical axiom `propext`, which is an allowed standard Lean axiom.
- **No custom/unchecked/unsafe axiom is introduced.**  In particular `native_decide` was
  deliberately avoided because it emits an unverifiable native axiom
  (`<name>._native.native_decide.ax_1_1`).

### 3. Exact reproduction one-liner

```
lake env lean IChO2026Problems/problem_icho_2026_t9_a7.lean ; echo "exit=$?"
```

Expected: prints the axiom-classification lines above and `exit=0`.

## Semantic-faithfulness self-audit (a green build is not enough)

- *Requested objects*: two integer `m/z` values.  Theorem statements return exactly those
  integers (`= 455` and `= 376`) in `ℕ`, with no rounding/widening — matching the problem's
  "Use integer values of atomic mass" and "exact integer" reporting policy.
- *Chemistry*: each theorem is about `Composition.sodiumAdductMz` of the composition that
  the problem prints under that product (C₂₇H₂₈O₅ / C₂₂H₂₅O₄), i.e. nominal neutral mass +
  one Na nominal mass at unit charge — precisely the [M+Na]⁺ convention.
- *Independence*: the only problem inputs consumed are the two printed molecular formulas and
  the integer-mass instruction; scientific premises are limited to the standard nominal
  masses (C=12, H=1, O=16, Na=23).  No prior-part result is assumed.

## Source grounding

- `icho_2026_source/raw/theory_problem.pdf`, page Q9-4 (printed page "Q9-4", source page 87).
- Image assets `T9_page-4.png` (degradation scheme + 9.7 task line) and `T9_page-3.png`
  (structure of **L**), sha256 as recorded in `TASK.json` / `isolation_manifest.json`.

No source inputs or generic infrastructure files were modified.
