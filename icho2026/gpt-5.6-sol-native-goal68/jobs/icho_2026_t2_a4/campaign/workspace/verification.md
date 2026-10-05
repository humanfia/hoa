# Verification: IChO 2026 T2-A4

## Source audit

The following problem-only materials were inspected:

- `GOAL.txt` and `TASK.json`;
- `icho_2026_source/image/T2_page-2.png` and
  `icho_2026_source/image/T2_page-3.png`;
- the original 93-page `icho_2026_source/raw/theory_problem.pdf`, especially
  PDF page 17 (Q2-3, containing T2-A4 and its phase portrait) and PDF page 21
  (A2-3, the blank student answer sheet containing the four selectable arrow
  diagrams).

The relevant SHA-256 check was run as:

```text
$ sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T2_page-2.png icho_2026_source/image/T2_page-3.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
77bd97168be820a9643a8acac845ca1ef8c4c1a4a99f678c78227e6e5e48ef8b  icho_2026_source/image/T2_page-2.png
c3149da1c24d984ae95dea8947243aba8fe833b79e4447761bb04ec17b831260  icho_2026_source/image/T2_page-3.png
```

Semantic cross-check:

1. The lower horizontal segment has ordinate
   \([\mathrm{HBrO_2}]_B\), so it is the Process-B branch.
2. The question text explicitly says that \([\mathrm{Br^-}]\) slowly
   decreases from \([\mathrm{Br^-}]_{\max}\) to
   \([\mathrm{Br^-}]_{\mathrm{critical}}\). Therefore the lower segment is
   traversed right-to-left.
3. Of the two answer-sheet choices whose arrows form a directed closed cycle,
   only the upper-right choice has that right-to-left lower arrow. Its complete
   traversal is clockwise. The other two printed choices are not directed
   cycles.

This checks the theorem's meaning against the actual chemistry prompt and the
blank answer sheet, independently of whether Lean accepts the file.

## Lean verification

Exact command:

```text
$ lake env lean IChO2026Problems/problem_icho_2026_t2_a4.lean
```

Result: exit code `0`. The two `#print axioms` commands at the end of the file
reported:

```text
'IChO2026Problems.T2A4.icho_2026_t2_a4_phase_direction' depends on axioms: [propext]
'IChO2026Problems.T2A4.icho_2026_t2_a4_unique_phase_direction' depends on axioms: [propext]
```

`propext` is a standard Lean logical axiom and is allowed by the task. There
are no custom axioms. The target contains no `sorry`, `admit`, or `unsafe`
declarations.

The formalization represents all sixteen arrows appearing across the four
printed choices, defines clockwise and counterclockwise directed cycles, and
proves that the upper-right choice is both valid and uniquely compatible with
the source-stated bromide decrease.
