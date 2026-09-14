# Verification for `icho_2026_t1_a2`

## Lean build and axiom audit

Command run from the workspace root:

```bash
lake env lean IChO2026Problems/problem_icho_2026_t1_a2.lean
```

Result: **exit code 0**.

The source file contains `#print axioms` commands for every main final theorem.
The exact compiler output was:

```text
'IChO2026T1A2.identify_Z_from_mass_spectrum' depends on axioms: [propext]
'IChO2026T1A2.chamazulene_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A2.azulene_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A2.naphthalene_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A2.azulene_two_perpendicular_planes' depends on axioms: [propext, Quot.sound]
'IChO2026T1A2.naphthalene_three_mutually_perpendicular_planes' depends on axioms: [propext, Quot.sound]
'IChO2026T1A2.azulene_isomerizes_structurally_to_naphthalene' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A2.icho_2026_t1_a2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only Lean’s permitted standard logical axioms occur.  In particular, the final
run contains neither `sorryAx` nor native-evaluation certificate axioms.

## Shortcut scan

Command:

```bash
grep -En '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t1_a2.lean
```

Result: **exit code 1 with no output**, the expected result when none of those
tokens occurs.  (`#print axioms` is plural and is intentionally not flagged.)

## Source-integrity check

Command:

```bash
sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T1_page-2.png icho_2026_source/image/T1_page-3.png
```

Result:

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
06f9276f8440fd17bd18f6778d1cc5950d47ffebaa60395b7078b96fcbf4f0cb  icho_2026_source/image/T1_page-2.png
fbdc901fd87b13a184497f3cb922f1cceb63ec8d01f0ff7fc6985d4131e70a17  icho_2026_source/image/T1_page-3.png
```

These hashes exactly match `TASK.json`.

## PDF inspection

Because Poppler tools were not installed, PyMuPDF 1.26.4 was unpacked under
`/tmp` solely as a renderer.  The original 93-page PDF was opened directly.
Extracted text located T1-A2 on PDF page 8 and its blank student response sheets
on PDF pages 10–11.  The sheets show a ten-checkbox field for Z and separate
blank drawing boxes for A and B.  They contain no solution data.  The supplied
page images for T1 pages 2 and 3 were also inspected at original resolution.

## Semantic coverage audit

The successful build checks all requested outputs, not only theorem syntax:

| Requirement | Evidence in the Lean file |
|---|---|
| Identity of Z | `candidate7_is_unique_mass_match` checks all ten printed formulae; `identify_Z_from_mass_spectrum` and the bundled theorem select candidate 7. |
| Complete Z graph | `chamazulene`, `chamazulene_complete`, `chamazulene_substitution_bonds`, and `chamazulene_has_azulene_core`. |
| Structure of A | `azulene`, `azulene_complete`, and `azulene_two_perpendicular_planes`. |
| Structure of B | `naphthalene`, `naphthalene_complete`, and `naphthalene_three_mutually_perpendicular_planes`. |
| A → B isomer relationship | `azulene_isomerizes_structurally_to_naphthalene` checks the common C₁₀H₈ formula, every unchanged atom/bond, and the exact fusion-bond/hydrogen rewrite. |
| No hidden charge/radical/stereo | `CompleteStructure` checks every explicit atom and bond, including neutral closed shells, no radicals, and no atom/bond stereochemical annotations. |
| Bond orders and valence | Each aromatic graph has an explicit Kekulé double-edge set; `ValidKekuleForm` checks every selected double bond and every atom’s ordinary valence. |

There are no unresolved source gaps.
