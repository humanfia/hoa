# Verification for `icho_2026_t6_a2`

All commands below were run from:

```text
/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t6_a2/campaign/workspace
```

## Source identity

Command:

```bash
sha256sum icho_2026_source/image/T6_page-1.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit 0):

```text
29fff91c704c94f9e4e9fddba3ab61896375763880aff114baef9318cbdbe6ba  icho_2026_source/image/T6_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These hashes exactly match `TASK.json`. The PDF was inspected directly with
PyMuPDF: it has 93 pages; the question is PDF page 52 and the original blank
student sheet containing the drawn A template is PDF page 57.

## Lean build and axiom audit

Command:

```bash
lake env lean IChO2026Problems/problem_icho_2026_t6_a2.lean
```

Result (exit 0):

```text
'IChO2026Problems.T6A2.structure_d_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A2.structure_b_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A2.structure_c_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A2.every_transformation_is_applicable' depends on axioms: [propext]
'IChO2026Problems.T6A2.c_to_cyclo14_consistency' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The output comes from the five `#print axioms` commands at the end of the Lean
file. Only the standard Lean logical axioms allowed by the task appear. In
particular, neither `sorryAx` nor a custom chemistry axiom appears.

The proof also checks the closed theorem
`every_transformation_is_applicable`: every listed loss acts on a present chlorine,
both retro-Bergman preconditions hold, both adjacent-radical pairings are
legal, and the final opposite-radical closure has the required cumulenic arc.

## Shortcut scan

Command:

```bash
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe|axiom)([^[:alnum:]_]|$)' IChO2026Problems/problem_icho_2026_t6_a2.lean; then exit 1; else exit 0; fi
```

Result: exit 0 with no output. The target contains none of the forbidden proof
shortcuts or a custom `axiom` declaration.

## Result metadata

Command:

```bash
python3 -m json.tool result.json >/dev/null
```

Result: exit 0.

## Semantic completion audit

- B, C, and D are each represented as an explicit 14-carbon graph, not as a
  string label.
- Every perimeter C–C bond order and both possible anthracene fusion bonds are
  encoded.
- Chlorine atoms and their single C–Cl bonds, carbon radical flags, carbon and
  chlorine formal charges, and stereocentre flags are explicit.
- The derived structures are proved equal to independently declared output
  structures.
- Carbon valence four, neutral charge, macrocyclic connectivity, no overlap of
  chlorine and radical flags, chlorine counts 3/1/5, and one radical in each
  output are proved.
- The final C→C₁₄ step is proved to give the alternating single/triple neutral
  cyclo[14]carbon, providing an endpoint check on C rather than relying only on
  the labeled chlorine count.
