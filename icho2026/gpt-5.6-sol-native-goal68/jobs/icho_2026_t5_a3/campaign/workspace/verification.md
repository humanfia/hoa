# Verification record for `icho_2026_t5_a3`

All commands below were run from:

`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t5_a3/campaign/workspace`

## Source identity

Command:

```text
sha256sum GOAL.txt TASK.json icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T5_page-1.png icho_2026_source/image/T5_page-2.png icho_2026_source/image/T5_page-3.png icho_2026_source/image/T5_page-4.png
```

Result (exit code 0):

```text
1025a8b9dd262e247175b8d6dc8a13188c2811ee66a72ea52baf3580577052bb  GOAL.txt
f4b07fd7668d1ac1b24159966f2d22a133ad5cd4052d4d08d128d0d22ece9f10  TASK.json
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
4f1688b010a3470a1dec9e211f1577b2eab98b2cd1b9b990ccba4126875b6347  icho_2026_source/image/T5_page-1.png
7f0f35d726d79f8d1ff9b15ee00574efeb89d8b179ab05469b5c297cb147bb96  icho_2026_source/image/T5_page-2.png
9824f187e7baa6e5929ec0c7cda6c740aee46a1404afdcad974c734b083b86b7  icho_2026_source/image/T5_page-3.png
bd87230867a821630559f26fb8c6ec968579a3d7cc2c130460fb91b8aa0463f3  icho_2026_source/image/T5_page-4.png
```

The PDF and image hashes equal those in `TASK.json`. The four T5 page images
were visually inspected at original resolution against the corresponding T5
material in the PDF bundle. In particular, page 2 is the blank Q5.2 student
answer sheet, page 3 contains Q5.3, and page 4 contains the printed PL1
hydrolysis equation used as an atom-balance cross-check.

## Lean compilation and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t5_a3.lean
```

Result (exit code 0, no warnings or errors):

```text
'IChO2026Problems.T5A3.determine_fatty_acid_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T5A3.fatty_acid_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T5A3.fatty_acid_answer_satisfies_data' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The `#print axioms` commands are part of the final Lean file. The reported
axioms are standard Lean/Mathlib logical axioms; there are no custom unchecked
axioms.

## Proof-shortcut scan

Command:

```text
if grep -nE '(^|[[:space:]])(sorry|admit|unsafe|axiom)[[:space:]]' IChO2026Problems/problem_icho_2026_t5_a3.lean; then exit 1; else echo 'PASS: no sorry/admit/unsafe/custom axiom declarations'; fi
```

Result (exit code 0):

```text
PASS: no sorry/admit/unsafe/custom axiom declarations
```

## Semantic audit

The formal theorem does not assume the requested formula. It quantifies over
candidate carbon, C=C, and C≡C counts, defines the acid hydrogen count from
acyclic valence bookkeeping, derives PL1's atom formula from the four fatty
acids/three glycerols/two phosphates balance, counts sigma and pi bonds
separately, and uses only the printed observations 3 and 255. The theorem
`determine_fatty_acid_counts` proves `c = 18`, `d = 2`, `t = 0`, and `h = 32`;
`fatty_acid_formula` returns `C18H32O2`; and
`fatty_acid_answer_satisfies_data` verifies the answer in the same model.
