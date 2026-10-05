# Verification for `icho_2026_t2_a3`

All commands below were run from
`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t2_a3/campaign/workspace`.

## Source integrity and inspection

Command:

```text
sha256sum /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T2_page-2.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T2_page-3.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
```

Result: exit code 0.

```text
77bd97168be820a9643a8acac845ca1ef8c4c1a4a99f678c78227e6e5e48ef8b  .../T2_page-2.png
c3149da1c24d984ae95dea8947243aba8fe833b79e4447761bb04ec17b831260  .../T2_page-3.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  .../theory_problem.pdf
```

These hashes exactly match `TASK.json` and `isolation_manifest.json`.  Both PNG
pages were inspected at original resolution.  Because Poppler/Ghostscript PDF
utilities are not installed, the original PDF was additionally inspected with
a read-only Python-standard-library parser that traversed its page tree,
decompressed Flate streams, and applied embedded ToUnicode maps.  It found 93
pages and identified:

```text
17 obj=185: Theory Q2-3 English (Official) ... [Br−]critical ...
21 obj=236: Theory A2-3 English (Official) 2.3 (4.0 pt) [Br−]critical = M ...
```

The A2-3 page is the blank student answer sheet; it confirms the requested
quantity and molar unit but supplies no answer.

## Lean toolchain and dependency

Command:

```text
lake env lean --version
```

Result: exit code 0.

```text
Lean (version 4.31.0, x86_64-unknown-linux-gnu, commit 68218e876d2a38b1985b8590fff244a83c321783, Release)
```

The first direct target check correctly reported that the pre-existing local
module `IChO2026Chem.Reporting` had not yet been compiled.  It was built with:

```text
lake build IChO2026Chem.Reporting
```

Result: exit code 0 (`Build completed successfully (8558 jobs)`).  The only
diagnostic was the pre-existing style warning `Copyright too short!` in
`IChO2026Chem/Reporting.lean`; no generic infrastructure was modified.

## Final Lean verification

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t2_a3.lean
```

Result: exit code 0.  The file's explicit `#print axioms` commands reported:

```text
'IChO2026Problems.T2A3.switchBoundary_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A3.printedRates_equal_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A3.step4_exceeds_step1_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A3.step1_exceeds_step4_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A3.fallbackHBrO2_levels_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A3.bromide_critical' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A3.bromide_critical_reported' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms permitted by the task.  In particular,
`sorryAx` is absent.

Command:

```text
if grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t2_a3.lean; then exit 1; else echo 'No prohibited proof shortcuts or custom axioms found.'; fi
```

Expected and final result: exit code 0 with
`No prohibited proof shortcuts or custom axioms found.`

## Semantic coverage

The formalization proves all of the following rather than merely checking the
final arithmetic:

1. cancellation of the common nonzero `[HBrO2]` and `[H+]` rate factors;
2. equality of the two printed rate laws exactly at the critical value;
3. step (4) faster above the threshold and step (1) faster below it;
4. positivity of both problem-stated fallback `[HBrO2]` levels;
5. the exact raw result `3 / 10^7`; and
6. validity of the three-significant-figure report `3.00 × 10^-7`, represented
   with reporting quantum `10^-9`.
