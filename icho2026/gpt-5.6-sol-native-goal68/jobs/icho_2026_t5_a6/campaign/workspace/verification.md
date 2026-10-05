# Verification record

Target: `icho_2026_t5_a6`  
Date: 2026-09-13 (UTC)

## Source audit

I inspected all four supplied T5 page images.  I also opened the original
93-page `icho_2026_source/raw/theory_problem.pdf`, rendered PDF pages 44-51,
and visually checked both the Q5 pages and blank student sheets A5-1 through
A5-4.  The target prompt and hydrolysis drawings are on PDF page 47; the blank
PL2/PL3 answer boxes are on PDF page 51.

The SHA-256 values of the relevant mounted inputs matched the values recorded
in `TASK.json`/`isolation_manifest.json`:

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
4f1688b010a3470a1dec9e211f1577b2eab98b2cd1b9b990ccba4126875b6347  icho_2026_source/image/T5_page-1.png
7f0f35d726d79f8d1ff9b15ee00574efeb89d8b179ab05469b5c297cb147bb96  icho_2026_source/image/T5_page-2.png
9824f187e7baa6e5929ec0c7cda6c740aee46a1404afdcad974c734b083b86b7  icho_2026_source/image/T5_page-3.png
bd87230867a821630559f26fb8c6ec968579a3d7cc2c130460fb91b8aa0463f3  icho_2026_source/image/T5_page-4.png
```

No answer, marking, grading, or solution source was consulted.

## Lean verification

Command (run from the workspace root):

```bash
lake env lean IChO2026Problems/problem_icho_2026_t5_a6.lean
```

Result: exit code `0`.

```text
'IChO2026Problems.ProblemIcho2026T5A6.structure_pl2' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.ProblemIcho2026T5A6.structure_pl3' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.ProblemIcho2026T5A6.requested_structures' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Thus the final theorems use only standard Lean logical axioms.  There is no
`sorryAx`, custom axiom, native evaluator axiom, `admit`, or `unsafe` proof
shortcut in their dependency graphs.

Command:

```bash
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)' IChO2026Problems/problem_icho_2026_t5_a6.lean; then exit 1; else echo 'No forbidden proof shortcuts found.'; fi
```

Result: exit code `0`.

```text
No forbidden proof shortcuts found.
```

Command:

```bash
python3 -m json.tool result.json >/dev/null
```

Result: exit code `0` (valid JSON).

## Semantic coverage

The Lean model separately verifies:

- all explicitly drawn scaffold atoms and every `R` placeholder;
- exact single/double bond connectivity for PL2 and PL3;
- four PL2 and two PL3 fatty-acid residues;
- two same-handed PL2 stereocentres and the all-mirrored enantiomer;
- one PL3 stereocentre and its mirror;
- neutral PL2 phosphate groups and the localized `-1` PL3 phosphate charge;
- zero radical electrons;
- `Z = C3H8O2` with an all-single-bond O-C-C-C-O path;
- PL2 total bond order 254 and its eight-water hydrolysis balance;
- PL3 four-water neutral-parent hydrolysis balance and one physiological
  deprotonation; and
- PL2's nontrivial involutive side exchange, with the bond set constructed as
  one half plus its swapped orbit.
