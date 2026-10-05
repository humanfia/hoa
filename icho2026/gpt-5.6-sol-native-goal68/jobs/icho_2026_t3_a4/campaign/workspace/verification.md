# Verification record — `icho_2026_t3_a4`

All commands below were run from
`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t3_a4/campaign/workspace`
unless another directory is shown.

## Source integrity and inspection

Command (run from the immutable seed source directory):

```text
sha256sum image/T3_page-3.png image/T3_page-4.png raw/theory_problem.pdf
```

Result (exit 0):

```text
da855bddec848e5e6615fefd29529eb40a68a3927e21f4db1faaa8f871579b71  image/T3_page-3.png
4f3df55e436f779a83a2561f744c8e5dcbbbf17fc707d97e230d2c0dfe164a19  image/T3_page-4.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  raw/theory_problem.pdf
```

These exactly match `TASK.json` and `isolation_manifest.json`.  I visually
inspected both PNGs.  I parsed the original 93-page PDF directly: zero-based
page 27 / PDF page 28 contains the T3-A4 problem and COF-1 dashed-cell example;
zero-based page 33 / PDF page 34 is the blank student answer sheet with four
panels labelled COF-3 through COF-6.  Both original-PDF pages were rendered and
visually inspected.

## Lean build and kernel verification

The shared local library first had to be built because this fresh workspace did
not yet contain its `.olean` files:

```text
lake build IChO2026Chem
```

Result (exit 0):

```text
Build completed successfully (8561 jobs).
```

Final target command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t3_a4.lean
```

Result (exit 0):

```text
'IChO2026Problems.T3A4.cof3_repeat_unit' depends on axioms: [propext]
'IChO2026Problems.T3A4.cof4_repeat_unit' depends on axioms: [propext]
'IChO2026Problems.T3A4.cof5_repeat_unit' depends on axioms: [propext]
'IChO2026Problems.T3A4.cof6_repeat_unit' depends on axioms: [propext]
'IChO2026Problems.T3A4.products_match_problem_observations' depends on axioms: [propext]
```

`propext` is a permitted standard Lean logical axiom.  There are no custom or
native-evaluation axioms: the final computational proofs use kernel-reduced
`decide`, not `native_decide`.

## Artifact and shortcut checks

Commands:

```text
python3 -c "import xml.etree.ElementTree as E; E.parse('cof_repeat_units.svg'); print('SVG XML parses successfully')"
grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t3_a4.lean
python3 -m json.tool result.json >/dev/null
```

Results: SVG parsing succeeded; the prohibited-token scan returned no matches
(grep exit 1, as expected); and `result.json` parsed successfully (exit 0).
The SVG was additionally rasterized at 1600 × 1120 and visually checked: all
four structures, three dashed geometric edges per structure, labels, and
continuation marks are visible without clipping.

## Semantic coverage audit

The four final theorems prove more than structural names.  Their finite graphs
record every in-cell heavy atom, exact attached-H count, bond order, formal
charge, radical count, and stereochemical tag.  They prove graph
well-formedness, complete doubled-valence checks (including bonds crossed by
the dashed boundaries), exact formulas, exact six-cut boundary lists, and the
diagnostic functional-group counts.  `products_match_problem_observations`
separately checks the printed IR and six-hydrogen-loss evidence.  The graph
transformations are explicit: oxidative cyclization removes the two required H
atoms and adds O–C closure bonds; ketoenamine tautomerization transfers H and
changes all affected bond orders while preserving composition.

