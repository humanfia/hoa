# Verification — `icho_2026_t6_a5`

Verification was performed in
`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t6_a5/campaign/workspace`
on 2026-09-13 UTC.

## Source integrity and inspection

Command:

```bash
sha256sum icho_2026_source/image/T6_page-3.png icho_2026_source/image/T6_page-2.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit 0):

```text
7ae1859c62e61f1da4136e4651d0b7f3f15930b9672a36cb31684f02291c34e5  icho_2026_source/image/T6_page-3.png
d9fd1e2d82d0e8a94ab6bcee210a2aee319715da722bbeb8d1df38e35d7d3362  icho_2026_source/image/T6_page-2.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These are exactly the hashes in `TASK.json`. The PDF has 93 pages. PyMuPDF
text extraction located Q6-3 at PDF page 54 and blank answer sheets A6-3 and
A6-4 at PDF pages 59 and 60. Those three pages were rendered at 2x resolution
and visually inspected. Pages 59–60 contain only blank boxes labelled F–L; no
partial bonds or stereochemical marks are present.

## Direct Lean verification and axiom audit

Command:

```bash
lake env lean IChO2026Problems/problem_icho_2026_t6_a5.lean
```

Result (exit 0):

```text
'IChO2026Problems.T6A5.structure_f' depends on axioms: [propext]
'IChO2026Problems.T6A5.structure_g' depends on axioms: [propext]
'IChO2026Problems.T6A5.structure_h' depends on axioms: [propext]
'IChO2026Problems.T6A5.structure_i' depends on axioms: [propext]
'IChO2026Problems.T6A5.structure_j' depends on axioms: [propext]
'IChO2026Problems.T6A5.structure_k' depends on axioms: [propext]
'IChO2026Problems.T6A5.structure_l' depends on axioms: [propext]
'IChO2026Problems.T6A5.structure_l_gives_five_cpp' depends on axioms: [propext]
```

The lines are produced by the explicit `#print axioms` commands in the final
file. `propext` is a standard Lean logical axiom. There are no custom axioms,
and the proofs use kernel-reduced `decide`, not `native_decide`.

## Full project build

Command:

```bash
lake build IChO2026Run
```

Result (exit 0):

```text
ℹ [8577/8581] Built IChO2026Problems.problem_icho_2026_t6_a5 (109s)
info: ...structure_f depends on axioms: [propext]
info: ...structure_g depends on axioms: [propext]
info: ...structure_h depends on axioms: [propext]
info: ...structure_i depends on axioms: [propext]
info: ...structure_j depends on axioms: [propext]
info: ...structure_k depends on axioms: [propext]
info: ...structure_l depends on axioms: [propext]
info: ...structure_l_gives_five_cpp depends on axioms: [propext]
✔ [8580/8581] Built IChO2026Run (35s)
Build completed successfully (8581 jobs).
```

Lake also printed only pre-existing/generic style warnings in
`IChO2026Run/Dependencies.lean`, `IChO2026Run/Basic.lean`,
`IChO2026Chem/Core.lean`, `IChO2026Chem/Reporting.lean`,
`IChO2026Problems/All.lean`, and `IChO2026Problems.lean`; there were no target
errors or target warnings.

Before that build, the diagnostic command
`lake env lean IChO2026Run.lean` exited 1 with `unknown module prefix
'IChO2026Run'` because its imported project modules had not yet been built into
Lake's module search path. The proper project command above built those modules
in dependency order and passed; the failed diagnostic is not listed as a final
verification command in `result.json`.

## Static checks

Command:

```bash
! grep -RInE '\b(sorry|admit|unsafe)\b' IChO2026Problems/problem_icho_2026_t6_a5.lean
```

Result: exit 0, no output. The target contains none of the forbidden proof
shortcuts.

Command:

```bash
! grep -nE '[[:blank:]]+$' answer.md IChO2026Problems/problem_icho_2026_t6_a5.lean IChO2026Problems/All.lean result.json verification.md
```

Result: exit 0, no output.

Command:

```bash
python3 -m json.tool result.json
```

Result: exit 0; the JSON parsed successfully.

## Semantic coverage

For each of F–L, the final theorem proves all three of the following:

1. evaluating the corresponding prefix of the source reaction scheme produces
   the stated constitution;
2. expanding that constitution produces a graph with an exact checked formula;
3. the expanded graph has unique atom IDs and bonds, existing endpoints,
   ordinary C/O/Si/Br valences, zero formal charges and radicals, and no
   invented stereochemical designation.

The explicitly checked formulas are F C30H33BrO3Si, G C42H61BrO3Si3,
H C36H47BrO3Si2, I C36H47BrO4Si2, J C42H52Br2O4Si2,
K C54H80Br2O4Si4, and L C54H80O4Si4. H and L match the formulas printed on
Q6-3. The additional theorem `structure_l_gives_five_cpp` checks that the
printed fourfold fluoride deprotection and SnCl2 aromatization convert L into a
well-formed cyclic C30H20 graph of five para-phenylenes, independently tying L
to the downstream [5]CPP product.
