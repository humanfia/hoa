# Verification record — `icho_2026_t6_a6`

## Source integrity and page audit

Command:

```bash
sha256sum icho_2026_source/image/T6_page-4.png icho_2026_source/image/T6_page-3.png icho_2026_source/image/T6_page-2.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit 0), matching `TASK.json` exactly:

```text
fd4ea1325d4a9b1980cce5824fc9878e7607a8cab8572c2e5699ea0d7eab7631  icho_2026_source/image/T6_page-4.png
7ae1859c62e61f1da4136e4651d0b7f3f15930b9672a36cb31684f02291c34e5  icho_2026_source/image/T6_page-3.png
d9fd1e2d82d0e8a94ab6bcee210a2aee319715da722bbeb8d1df38e35d7d3362  icho_2026_source/image/T6_page-2.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

The original PDF and relevant blank student sheets were inspected directly (the environment has no `pdftotext` executable):

```bash
python3 - <<'PY'
import pymupdf
pdf = pymupdf.open('icho_2026_source/raw/theory_problem.pdf')
print('page_count', len(pdf))
for n in (55, 61, 62):
    text = ' '.join(pdf[n - 1].get_text('text').split())
    print(n, text[:160])
PY
```

Result (exit 0):

```text
page_count 93
55 Theory Q6-4 English (Official) Next generation nanobelts were constructed from porphyrin rings and triple bonds using the template synthesis method. Hint: M is
61 Theory A6-5 English (Official) 6.6 (20.0 pt) M N O Q
62 Theory A6-6 English (Official) 6.6 (cont.) R 6.7 (4.0 pt) n(e) n(t)
```

The rendered pages were also visually inspected at original resolution. PDF page 55 is Q6-4. The relevant blank student sheets are PDF pages 61 (A6-5: boxes M, N, O, Q) and 62 (A6-6: box R). This is independent evidence that there is no standalone P response box; P6 is already drawn on Q6-4.

## Lean compilation and axiom audit

Command, run from the workspace root:

```bash
lake env lean IChO2026Problems/problem_icho_2026_t6_a6.lean
```

Result: exit code 0. The `#print axioms` commands embedded at the end of the file printed:

```text
'IChO2026Problems.ProblemIChO2026T6A6.leastCrowded_sites_unique' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.ProblemIChO2026T6A6.m_has_four_proton_environments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.ProblemIChO2026T6A6.structure_M' depends on axioms: [propext]
'IChO2026Problems.ProblemIChO2026T6A6.structure_N' depends on axioms: [propext]
'IChO2026Problems.ProblemIChO2026T6A6.structure_O' depends on axioms: [propext]
'IChO2026Problems.ProblemIChO2026T6A6.structure_Q' depends on axioms: [propext]
'IChO2026Problems.ProblemIChO2026T6A6.structure_R' depends on axioms: [propext]
'IChO2026Problems.ProblemIChO2026T6A6.structure_P' depends on axioms: [propext]
'IChO2026Problems.ProblemIChO2026T6A6.structure_P_source_gap' depends on axioms: [propext]
'IChO2026Problems.ProblemIChO2026T6A6.structure_P6' depends on axioms: [propext]
```

These are permitted standard logical axioms. There is no `sorryAx`, custom axiom, or unsafe declaration.

Shortcut scan command:

```bash
grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t6_a6.lean || true
```

Result: no output.

## What the proof checks

- M is the unique least-crowded 1,3,5-substitution pattern and has exactly four proton environments; its complete graph has formula C15H24.
- N is reached by the encoded benzylic-bromination/Sommelet sequence and its graph contains Ar–C(H)=O; formula C15H22O.
- O is the trans-5,15-diaryl Zn porphyrin with two opposite meso-H atoms, all four Zn–N coordination bonds, zero net formal charge, and formula C48H52N4Zn.
- Q replaces exactly those two meso-H atoms by Br; formula C48H50Br2N4Zn.
- R replaces them by terminal C≡CH groups through the protected-ethynyl/deprotection sequence; formula C52H52N4Zn.
- P6 contains six complete R-derived porphyrins with all twelve terminal hydrogens removed, six explicit closing C(sp)–C(sp) bonds, 342 heavy atoms, 402 bonds, and formula C312H300N24Zn6.
- Every requested graph is certified in range, neutral, closed-shell, and without stereocentres. M–R additionally have pairwise-distinct bond lists.
