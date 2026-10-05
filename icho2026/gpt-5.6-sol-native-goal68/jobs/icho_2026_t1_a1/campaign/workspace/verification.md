# Verification: IChO 2026 T1-A1

All commands were run from:

`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t1_a1/campaign/workspace`

## Source integrity

Command:

```text
sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T1_page-1.png icho_2026_source/image/T1_page-2.png
```

Result (exit code 0):

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
c03ceb7b203d63570c24c999ca3894c33b346a86ea54879d30c3c2650e992f52  icho_2026_source/image/T1_page-1.png
06f9276f8440fd17bd18f6778d1cc5950d47ffebaa60395b7078b96fcbf4f0cb  icho_2026_source/image/T1_page-2.png
```

The hashes match `TASK.json` and `isolation_manifest.json`. The PDF page tree
was inspected directly: it contains 93 `/Type /Page` objects. Page 7 is Q1-2;
page 10 is the blank A1-1 student sheet with choices 1–10 for each of X and Y.

## Lean compilation and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t1_a1.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T1A1.identity_x' depends on axioms: [propext]
'IChO2026Problems.T1A1.identity_y' depends on axioms: [propext]
'IChO2026Problems.T1A1.identify_X_and_Y' depends on axioms: [propext]
'IChO2026Problems.T1A1.candidate3_has_plane_of_symmetry' depends on axioms: [propext]
'IChO2026Problems.T1A1.candidate3_formula_from_graph' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T1A1.problem_observation_is_consistent' depends on axioms: [propext]
'IChO2026Problems.T1A1.candidate6_to_candidate3_acid_cyclization' depends on axioms: [propext]
```

These are standard Lean logical axioms only. There are no custom axioms. The
two requested identity theorems and combined theorem use only `propext`.

## Shortcut and file checks

Commands:

```text
grep -nE '^[[:space:]]*(axiom|unsafe)[[:space:]]|\b(sorry|admit)\b' IChO2026Problems/problem_icho_2026_t1_a1.lean
python3 -m json.tool result.json >/dev/null
test -s answer.md -a -s verification.md -a -s result.json -a -s IChO2026Problems/problem_icho_2026_t1_a1.lean
```

Results:

- `grep`: exit code 1 with no output (no forbidden proof shortcut or custom
  axiom occurs).
- JSON validation: exit code 0.
- Nonempty-deliverable check: exit code 0.
