# Verification — IChO 2026 T3-A2 (icho_2026_t3_a2)

## Toolchain

- Lean 4 toolchain: `leanprover/lean4:v4.31.0` (from `lean-toolchain`).
- Dependencies (pinned in `lakefile.toml` / `lake-manifest.json`): Mathlib
  v4.31.0, Physlib, crnt-lean.

## Commands and results

All commands run in the workspace root
(`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t3_a2/campaign/workspace`).

### 1. Build shared reporting infrastructure

```
lake build IChO2026Chem
```

Result: `Build completed successfully (8561 jobs).`

### 2. Compile the target problem file (primary verification command)

```
lake env lean IChO2026Problems/problem_icho_2026_t3_a2.lean
```

Result: exit code 0, no errors, no warnings on the problem file. The file ends
with `#print axioms` for every final theorem; the complete output was:

```
'IChO2026T3A2.cof2HexagonSide_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T3A2.cof2InternalDiameter_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T3A2.cof2InternalDiameter_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T3A2.cof2InternalDiameter_rounding_uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T3A2.cof2InternalDiameter_three_sf' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T3A2.cof2InternalDiameter_reported' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T3A2.cof2Submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(`cof2InternalDiameter_lower` and `cof2InternalDiameter_upper` are packages of
the bounds theorem; `cof2InternalDiameter_nonneg` is a definition-level lemma
used inside the above.)

Every final theorem depends only on the standard Lean logical axioms
`propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`, no custom `axiom`
declarations, and no `unsafe` code are present (checked by the axiom dump
above and by `grep` for `sorry|admit|^axiom|unsafe` over `IChO2026Problems/`).

### 3. Build the whole problem library including the umbrella import

```
lake build IChO2026Problems
```

Result: `Build completed successfully (8564 jobs).` The only diagnostic is a
pre-existing style warning about a >100-character comment line in the
infrastructure file `IChO2026Problems.lean` (present before this task; not
introduced or modified here).

## Semantic-faithfulness audit (independent of the green build)

- The theorem `cof2HexagonSide_eq` computes the side length from the three
  stipulated inputs as `2·bO + 2·cB + 2·cC = 8.66`, matching the honeycomb
  side shown on page Q3-1 (boroxine-ring vertices, benzene para-linker edges,
  collinear C–B bonds) and the bond values from page Q3-2.
- `cof2InternalDiameter` is defined exactly as the problem's stipulated
  formula `d = √3 · a`, with `a` the hexagon side; no stronger or weaker
  statement is proved.
- `cof2InternalDiameter_sq` pins the exact raw square 3·8.66² = 224.9868,
  which forces the unique rounding: 14.95² = 223.5025 < 224.9868 < 226.5025 =
  15.05², hence 14.95 < d < 15.05 (`cof2InternalDiameter_bounds`), proved
  via `Real.sqrt_lt_sqrt` (square-root monotonicity), not by floating-point
  approximation.
- `cof2InternalDiameter_reported` and `cof2Submission_valid` use the shared
  answer-blind `ReportsAtQuantum`/`ValidNumericSubmission` contract with
  quantum 0.1 (three significant figures, the uniform evaluation default);
  `cof2InternalDiameter_rounding_uniqueness`rules out any other multiple of
  0.1, i.e. 15.0 Å is not a chosen but the forced reported value.
- The final chemist's statement is `d = 15.0 Å` (3 s.f.); the raw exact value
  `√3 · 8.66 Å ≈ 14.9996 Å` is preserved unrounded in
  `cof2Submission.rawValue = cof2InternalDiameter`.

## Inputs used

- `icho_2026_source/raw/theory_problem.pdf` pages Q3-1 (printed 25, COF-2
  structure figure from monomer A2), Q3-2 (printed 26, question and assumed
  bond lengths/formula), A3-1 (answer sheet blank `d = ____ Å`).
- `icho_2026_source/image/T3_page-1.png`, `T3_page-2.png` (same content,
  raster).
- No solutions, marking schemes, or answer keys exist in the workspace and
  none were consulted (`official_answer_seen: false` in TASK.json).
