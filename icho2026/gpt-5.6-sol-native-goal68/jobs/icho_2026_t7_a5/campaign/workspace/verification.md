# Verification for `icho_2026_t7_a5`

## Source audit

The supplied assets were checked against `TASK.json`:

```text
$ sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T7_page-2.png icho_2026_source/image/T7_page-3.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
010bf0d38d5f34a4edd184c97a2a3f0f9375e0e6f1326e7d0fbd336d319b97ba  icho_2026_source/image/T7_page-2.png
9bc386ab33010a7f8e999035212268ecbeb2ff73ca3a8a108dca96b364e5d47c  icho_2026_source/image/T7_page-3.png
```

The original PDF has 93 pages. PDF pages 64–65 contain the reaction scheme and
T7-A5 text; PDF page 70 is the blank A7-4 student sheet containing the empty
answer box for 7.5. These pages and both task images were visually inspected.

## Lean verification

The shared reporting module was built once so that direct `lean` invocation
could resolve its compiled import:

```text
$ lake build IChO2026Chem
Build completed successfully (8561 jobs).
```

Final verification command:

```text
$ lake env lean IChO2026Problems/problem_icho_2026_t7_a5.lean
exit code: 0
```

The file's three `#print axioms` commands reported:

```text
'IChO2026Problems.T7A5.five_n2_for_two_precursors_matches_gas_datum' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T7A5.binding_topology_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T7A5.structure_5_is_dinitrogen_bridged_dimolybdenum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms permitted by the goal. There are no
custom axioms. The command emitted only two style-linter warnings in the proof
of bond symmetry; neither is a proof or build error.

Shortcut scan command:

```text
$ if grep -nE '\b(sorry|admit|unsafe|axiom)[[:space:]]' IChO2026Problems/problem_icho_2026_t7_a5.lean; then exit 1; else echo 'no prohibited declarations'; fi
no prohibited declarations
```

The pattern deliberately excludes the required plural command `#print axioms`.
