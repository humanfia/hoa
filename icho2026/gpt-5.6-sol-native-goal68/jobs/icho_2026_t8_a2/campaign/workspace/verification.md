# Verification — `icho_2026_t8_a2`

## Source checks

Command:

```bash
sha256sum TASK.json icho_2026_source/image/T8_page-1.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
0bbd8505fb429521d87fe4b4da98e9c6b9dbe781e6a3d0be1ab98246aa5a42be  TASK.json
3490231dd64238ab3db32a48d86f92c857f9fef386b510c45ba1b80f483cc843  icho_2026_source/image/T8_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

The PDF was inspected at page 72 (`Q8-1`, the mechanism) and page 77 (`A8-1`,
the blank student answer sheet). The latter contains the 8.2 score line and
five otherwise blank answer areas labelled 3, 4, 5, 6, and 7.

## Lean compile and axiom audit

Command:

```bash
lake env lean IChO2026Problems/problem_icho_2026_t8_a2.lean
```

Result (exit code 0):

```text
'IChO2026T8A2.structure_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T8A2.structure_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T8A2.structure_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T8A2.structure_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T8A2.structure_7' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms permitted by the task. In particular,
none of the final theorems depends on `sorryAx` or a custom axiom.

Command:

```bash
grep -nE '\b(sorry|admit|unsafe)\b' IChO2026Problems/problem_icho_2026_t8_a2.lean
```

Result: exit code 1 and no output, meaning none of the forbidden proof
shortcuts occurs in the target file.

## Semantic coverage

The final theorems `structure_3` through `structure_7` each assert all of the
following for their requested species: equality of the mechanism-derived graph
to a separately declared answer graph, local Lewis-valence validity, exact
molecular formula, net charge, radical count, and absence of unrequested
stereochemical annotations. `structure_6` additionally proves the absence of
an aldehyde subgraph; `structure_7` proves its presence. The supporting
theorems `intermediate_arrow_accounting` and `hydrolysis_arrow_accounting`
verify the atom/charge/radical changes printed over the mechanism arrows.
