# Verification for `icho_2026_t9_a2`

## Source integrity and inspection

The task-named source paths resolve inside the read-only `icho_2026_source`
bundle as `image/T9_page-1.png`, `image/T9_page-2.png`, and
`raw/theory_problem.pdf`. Both PNGs were visually inspected at original
resolution. PDF pages 84–85 (problem pages Q9-1/Q9-2) and page 89 (blank
student answer sheet A9-1) were rendered with PyMuPDF and visually inspected.
The answer sheet is blank and supplies the two chair/CD templates only.

Command:

```bash
sha256sum icho_2026_source/image/T9_page-1.png icho_2026_source/image/T9_page-2.png icho_2026_source/raw/theory_problem.pdf
```

Result:

```text
c7f5114e9bb5d3e821a3df76d40c4ab86006fdb550992aa8013bc50b68a90608  icho_2026_source/image/T9_page-1.png
a65b4bf067ff9b1aa03ad40758319abec68f959fce4bf64380bd0e8227bee48f  icho_2026_source/image/T9_page-2.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These equal the hashes recorded in `TASK.json`.

## Lean build and axiom audit

The shared local import was built once because the initial workspace did not
contain its `.olean` file.

Command:

```bash
lake build IChO2026Chem
```

Result: exit code 0; `Build completed successfully (8561 jobs).`

Final target command:

```bash
lake env lean IChO2026Problems/problem_icho_2026_t9_a2.lean
```

Result: exit code 0. The `#print axioms` commands embedded at the end of the
file printed:

```text
'IChO2026Problems.Icho2026T9A2.chair_conformation' does not depend on any axioms
'IChO2026Problems.Icho2026T9A2.structure_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.Icho2026T9A2.k_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.Icho2026T9A2.k_bondOrder_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.Icho2026T9A2.k_connectivity_is_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`propext`, `Classical.choice`, and `Quot.sound` are standard Lean logical
axioms; no target-specific or unchecked chemistry axiom occurs.

## Shortcut and artifact checks

Command:

```bash
! grep -nE '\b(sorry|admit|unsafe)\b' IChO2026Problems/problem_icho_2026_t9_a2.lean
```

Result: exit code 0 (the negated search found no prohibited proof shortcut).

Command:

```bash
python3 -m json.tool result.json >/dev/null
```

Result: exit code 0.

Command:

```bash
! grep -nE '[[:blank:]]+$|^(<<<<<<<|=======|>>>>>>>)' answer.md verification.md result.json IChO2026Problems/problem_icho_2026_t9_a2.lean
```

Result: exit code 0 (no trailing whitespace or merge-conflict marker). The
workspace has no Git metadata, so a repository-based `git diff --check` is not
applicable here.

## Semantic audit

- `chair_conformation` derives the right-hand `¹C₄` choice from the two
  reaction operations, rather than postulating the selected box.
- `structure_K` proves that the computed reaction state is the per-3,6-anhydro
  state and binds it to `kGraph`.
- `KAtom = Fin 7 × ProductSite` provides exactly 70 heavy-atom vertices.
  `k_formula` computes `C42H56O28` from the vertex labels and per-vertex
  implicit-hydrogen counts.
- `ProductAdjacent` lists every pyranose, C5–C6, C2–OH, C3–O36–C6, and cyclic
  C1(i)–O(i)–C4(i+1) edge. `k_connectivity_is_exact` is an iff, so it excludes
  unlisted bonds as well as requiring the listed ones. `k_has_only_single_bonds`
  proves that every bond order is zero or one.
- All formal charges and radical-electron counts are zero. The only oxygen
  carrying a hydrogen is O2 on every repeat.
- `ProductStereo` is exact (not merely a list of required positive examples):
  it records down C1–glycosidic O, down C2–OH, up C3–O36, down incoming
  C4–glycosidic O, and up C5–C6 on all seven retained α-D-gluco repeats.

This covers both requested outputs and the structure/stereochemistry fields in
`TASK.json`; no source gap remains.
