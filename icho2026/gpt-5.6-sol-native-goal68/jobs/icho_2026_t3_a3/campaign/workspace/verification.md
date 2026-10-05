# Verification — IChO 2026 T3-A3

## Source audit

I read `GOAL.txt` and `TASK.json` first. I then inspected the supplied
`T3_page-3.png` (monomers and topology schematics), `T3_page-4.png` (question
and partially prefilled table), and the original 93-page
`theory_problem.pdf`. Within the PDF I inspected Q3-3 (physical page 27), Q3-4
(physical page 28), and the blank student answer page A3-2 (physical page 33).
The answer sheet has two blank rows in each of seven columns, matching the
fourteen `Cell` values formalized in Lean.

Source-integrity command:

```text
$ sha256sum /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T3_page-3.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T3_page-4.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
da855bddec848e5e6615fefd29529eb40a68a3927e21f4db1faaa8f871579b71  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T3_page-3.png
4f3df55e436f779a83a2561f744c8e5dcbbbf17fc707d97e230d2c0dfe164a19  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T3_page-4.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
```

All three hashes match `TASK.json`.

## Semantic audit

The formalization does not make `XXX` an unchecked input. `Combination` has
exactly the three source-allowed reaction families (`AB`, `CD`, `ED`), giving
28 finite candidates. The theorem `fits_iff_mem_allSolutions` exhausts these
candidates against the source-transcribed monomer roles and topology
schematics. `ValidSubmission` additionally checks:

1. exactly two answer cells per topology;
2. every entered combination fits and is not one of the three supplied
   examples;
3. no supplied or entered combination is duplicated;
4. whenever `XXX` occurs, every fitting candidate is already supplied or
   entered in that column.

Thus `topology_table_valid` covers all requested entries and proves the
negative `XXX` claims by finite exclusion. `topology_table_entries` exposes the
exact table value. No earlier subquestion, numerical tolerance, or
supplementary model assumption is used.

## Lean verification

Final command (run from the workspace root):

```text
$ lake env lean IChO2026Problems/problem_icho_2026_t3_a3.lean
'IChO2026Problems.T3A3.fits_iff_mem_allSolutions' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T3A3.topology_table_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T3A3.topology_table_entries' does not depend on any axioms
```

Exit status: `0`.

The `#print axioms` lines are part of the target file, so the compile command
also performs the requested axiom inspection. The reported dependencies are
standard Lean logical axioms; there are no custom axioms.

Shortcut scan:

```text
$ grep -nE '(^|[^[:alpha:]])(sorry|admit|unsafe|axiom)[[:space:]]' IChO2026Problems/problem_icho_2026_t3_a3.lean
```

Result: no matches (exit status `1`), so the file contains no `sorry`, `admit`,
`unsafe`, or custom `axiom` declaration.
