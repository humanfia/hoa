# Verification record

## Source inspection and integrity

I inspected the original `theory_problem.pdf`, including:

- raw PDF page 55, which displays the P6 repeat unit and complete six-membered
  nanoring;
- raw PDF page 56, which contains question 6.7; and
- raw PDF page 62 (A6-6), the blank student answer sheet with the `n(e)` and
  `n(t)` boxes.

The provided problem-page images T6 pages 2--5 were also inspected.  The
source-integrity command was:

```text
sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T6_page-2.png icho_2026_source/image/T6_page-3.png icho_2026_source/image/T6_page-4.png icho_2026_source/image/T6_page-5.png
```

It exited with status 0 and printed:

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
d9fd1e2d82d0e8a94ab6bcee210a2aee319715da722bbeb8d1df38e35d7d3362  icho_2026_source/image/T6_page-2.png
7ae1859c62e61f1da4136e4651d0b7f3f15930b9672a36cb31684f02291c34e5  icho_2026_source/image/T6_page-3.png
fd4ea1325d4a9b1980cce5824fc9878e7607a8cab8572c2e5699ea0d7eab7631  icho_2026_source/image/T6_page-4.png
33d7bc00e7f1805f32c3afaa22bda1ef7c548c51da80244e2fe0d27004deb748  icho_2026_source/image/T6_page-5.png
```

All five digests match `TASK.json` / `isolation_manifest.json`.

## Lean verification and axiom audit

The final target was compiled with the required command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t6_a7.lean
```

It exited with status 0.  The file's four `#print axioms` commands printed:

```text
'IChO2026Problems.ProblemIcho2026T6A7.minimum_electrons_removed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.ProblemIcho2026T6A7.global_pi_electron_count' depends on axioms: [propext]
'IChO2026Problems.ProblemIcho2026T6A7.requested_outputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.ProblemIcho2026T6A7.requested_outputs_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

These are standard Lean logical axioms permitted by the goal.  In particular,
`sorryAx` is absent, and the file declares no custom axiom.

## Shortcut/declaration scans

The exact proof-shortcut scan command is:

```text
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)' IChO2026Problems/problem_icho_2026_t6_a7.lean; then echo 'prohibited proof shortcut found'; exit 1; else echo 'no sorry/admit/unsafe tokens found'; fi
```

It exited with status 0 and printed:

```text
no sorry/admit/unsafe tokens found
```

The exact unchecked-declaration scan command is:

```text
if grep -nE '^[[:space:]]*(axiom|constant)[[:space:]]' IChO2026Problems/problem_icho_2026_t6_a7.lean; then echo 'custom unchecked declaration found'; exit 1; else echo 'no custom axiom/constant declarations found'; fi
```

It exited with status 0 and printed:

```text
no custom axiom/constant declarations found
```

Finally,

```text
python3 -m json.tool result.json >/dev/null && echo 'result.json is valid JSON'
```

exited with status 0 and printed:

```text
result.json is valid JSON
```

## Semantic coverage

The compile checks the full requested specification, not merely the arithmetic
of a chosen candidate:

- `minimum_electrons_removed` proves that removal of 2 is valid and aromatic
  and is no greater than every valid positive aromatic removal;
- `global_pi_electron_count` proves that this removal leaves 82 electrons;
- `requested_outputs_unique` proves that every `(removed, total)` satisfying
  the formal problem specification equals `(2, 82)`.
