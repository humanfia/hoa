# Verification record — icho_2026_t4_a1

Date: 2026-09-14. All commands run in the workspace root
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t4_a1/campaign/workspace`,
toolchain `leanprover/lean4:v4.31.0` (see `lean-toolchain`).

## Files created by this target

- `IChO2026Problems/problem_icho_2026_t4_a1.lean` — formalization + proofs.
- `IChO2026Problems/All.lean` — umbrella required by the fixed
  `IChO2026Problems.lean` (`import IChO2026Problems.All`); contains only the
  import of this target's file.
- `answer.md` — natural-language answer and source grounding.
- `verification.md` (this file), `result.json`.

No source inputs (`icho_2026_source/**`), and none of the pinned skeleton
files (`lakefile.toml`, `IChO2026Chem/**`, `IChO2026Run/**`,
`IChO2026Problems.lean`, `lean-toolchain`, `archon-protected.yaml`) were
modified.

## Command 1: build shared chemistry library (prerequisite oleans)

    lake build IChO2026Chem

Result: `✔ [8560/8561] Built IChO2026Chem (9.1s)` — success.

## Command 2: compile the target file directly

    lake env lean IChO2026Problems/problem_icho_2026_t4_a1.lean

Result: exit code 0, output consists only of the four `#print axioms` messages:

    'IChO2026Problems.T4A1.uranium235_abundance_reports_three_sig_figs' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]
    'IChO2026Problems.T4A1.submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026Problems.T4A1.abundance_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026Problems.T4A1.abundance_percent' depends on axioms: [propext, Classical.choice, Quot.sound]

Only the standard Lean logical axioms appear. `sorryAx` is absent: no `sorry`,
no `admit`, no `unsafe` constructs, and no custom unchecked axioms anywhere in
the file.

## Command 3: whole-library build (fixed umbrella includes the target)

    lake build IChO2026Problems

Result: `⚠ [8563/8564] Built IChO2026Problems (39s)`, "Build completed
successfully (8564 jobs)". The single warning is a pre-existing style warning
in the pinned, protected skeleton file `IChO2026Problems.lean` (line length),
unrelated to this target.

## Semantic faithfulness check (independent of compilation)

- The model `abundance x := m235·x + m238·(1−x) = mAvg` is exactly the
  abundance-weighted average atomic weight of a two-isotope mixture, with the
  printed constants 235.04 / 238.05 (problem text, PDF page 37) and 238.03
  (official periodic table, PDF page header G1-5).
- `abundance_unique` proves the only consistent atomic fraction is 2/301;
  `abundance_percent` proves the requested percentage is 200/301 % ≈
  0.6644518… %; `uranium235_abundance_reports_three_sig_figs` proves 0.664 %
  is the correct 3-significant-figure report at quantum 0.001 % with ties
  half away from zero. The upper inequality there is strict (200·2000 = 400000
  < 400029 = 1329·301), confirming no tie ever occurs.
- The requested output id from TASK.json (`uranium235_abundance`, unit "%")
  matches the reported quantity.
