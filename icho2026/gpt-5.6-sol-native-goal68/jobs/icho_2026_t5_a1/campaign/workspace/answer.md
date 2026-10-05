# IChO 2026 T5-A1

**Tick (b): `n` is an odd number.**

The wavy bonds in the fragment diagram are the open attachment ends that must
be paired when the fragments are assembled.  The four fragment types have the
following numbers of open ends per copy:

| fragment | copies | open ends per copy | contribution |
|---|---:|---:|---:|
| `a` | `n` | 1 | `n` |
| `b` | 2 | 2 | 4 |
| `c` | 3 | 3 | 9 |
| `d` | 4 | 1 | 4 |

Hence the inventory has

\[
n+4+9+4=n+17
\]

open attachment ends.  Each bond made between fragments consumes exactly two
such ends.  A completed molecule therefore requires `n + 17` to be even.  Since
17 is odd, `n` must be odd.

As a stronger consistency check, the page calls PL1 a single acyclic molecule.
There are `n + 2 + 3 + 4 = n + 9` initially separate fragments, so a connected
acyclic assembly has `n + 8` joining bonds.  Counting their ends gives
`n + 17 = 2(n + 8)`, hence in fact `n = 1`; this again selects (b).  The
no-peroxide condition restricts *which* ends may be joined but is not needed
for this parity count.

## Source grounding

- `TASK.json` identifies the sole requested output as the exact classification
  `fragment_parity_statement` for T5-A1.
- `icho_2026_source/image/T5_page-1.png` and source page 44 of
  `icho_2026_source/raw/theory_problem.pdf` show the fragment multiplicities
  `n, 2, 3, 4`, their wavy attachment bonds, the statements that PL1 can be
  assembled from them and is acyclic, and choices (a)--(c).
- The PDF has SHA-256
  `af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60`;
  the supplied render of the question page has SHA-256
  `4f1688b010a3470a1dec9e211f1577b2eab98b2cd1b9b990ccba4126875b6347`.
- The following blank student response page (the supplied `T5_page-2.png`, PDF
  source page 45) was also inspected.  It supplies answer space for T5.2 and no
  additional premise for T5-A1.

No official solution, marking scheme, grading report, answer repository, or
historical answer was used.  There is no source gap for the requested parity:
the proof needs only the depicted attachment counts and the ordinary two-ended
nature of a bond.

