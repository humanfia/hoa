# Verification for `icho_2026_t9_a3`

## Source inspection

`GOAL.txt` and `TASK.json` were read before any target work.  The relevant
rendered question pages `T9_page-1.png` and `T9_page-2.png` were inspected at
original resolution.  The original PDF was independently opened with PyMuPDF:
it has 93 pages; physical PDF page 85 is official question sheet Q9-2, physical
page 89 is blank student sheet A9-1, and physical page 90 is blank student sheet
A9-2.  The latter contains only the empty fields
`rs: __________________` and `sc: __________________` for 9.3, so it supplies
the requested answer format but no answer value.

Source-integrity command:

```text
sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T9_page-1.png icho_2026_source/image/T9_page-2.png
```

Result:

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
c7f5114e9bb5d3e821a3df76d40c4ab86006fdb550992aa8013bc50b68a90608  icho_2026_source/image/T9_page-1.png
a65b4bf067ff9b1aa03ad40758319abec68f959fce4bf64380bd0e8227bee48f  icho_2026_source/image/T9_page-2.png
```

## Lean kernel check and axiom audit

Exact command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t9_a3.lean
```

Exit status: `0`.

Exact output from the three `#print axioms` commands in the file:

```text
'IChO2026Problems.T9A3.macrocycle_X_ring_size' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T9A3.macrocycle_X_stereocentres' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T9A3.macrocycle_X_requested_outputs' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms permitted by the goal.  No custom or
unchecked chemistry axiom occurs.

Proof-shortcut scan command:

```text
grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe|axiom)([^[:alnum:]_]|$)' IChO2026Problems/problem_icho_2026_t9_a3.lean
```

Result: no output; exit status `1`, meaning no match.

## Semantic coverage check

- Direct problem input: the starting β-CD scheme is marked with seven repeats.
- Ring inventory formalized: every repeat contributes exactly
  `C1, O5, C5, C4, O(glycosidic)` to the surviving loop; the five-site list is
  proved duplicate-free and exhaustive, and its sevenfold product has card 35.
- Stereocentre inventory formalized: the five original carbon positions C1–C5
  are represented; C2 and C3 are exactly the two periodate-cleaved positions
  made methylene by reduction; the retained subtype is proved to have card 3,
  and its sevenfold product has card 21.
- Both exact integer outputs requested in `TASK.json` are separately proved and
  also packaged in `macrocycle_X_requested_outputs`.
- T9-A2 concerns the independent right-hand branch leading to K and is not used
  as an unproved prerequisite for the left-hand branch leading to X.
- No source gap remains.
