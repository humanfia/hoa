# IChO 2026 T8-A7

Tick **a) increases**.

The problem defines TOF as the number of product molecules formed per catalyst
molecule per hour.  For one gram of C₃N₄, the number of loaded catalyst
molecules is proportional to the catalyst mass fraction
\(\omega_{\mathrm{cat}}\); all conversion factors (including molar mass and
the percent-to-fraction factor) are fixed and positive.  Hence the overall CO
formation rate has the same trend as

\[
  \omega_{\mathrm{cat}}\,\mathrm{TOF}.
\]

Using all labelled points in the supplied graph gives:

| \(\omega_{\mathrm{cat}}\) (%) | CO TOF (h\(^{-1}\)) | proportional rate \(\omega_{\mathrm{cat}}\mathrm{TOF}\) |
|---:|---:|---:|
| 0.1 | 62 | 6.2 |
| 0.3 | 56 | 16.8 |
| 0.6 | 37 | 22.2 |
| 1.0 | 29 | 29.0 |
| 2.0 | 15 | 30.0 |
| 2.9 | 11 | 31.9 |
| 3.8 | 8 | 30.4 |

Thus the rate rises from 6.2 at the lowest loading to 30.4 at the highest
loading (a factor of \(30.4/6.2=152/31\approx4.90\)).  It levels off at the
larger loadings, and the final two plotted values show a small fluctuation, so
the data should not be described as strictly increasing at every adjacent
point.  Nevertheless, the overall low-to-high change asked for by the three
boxes is unambiguously an **increase**.  The decreasing plotted TOF alone is
not the overall rate because more catalyst molecules are present at higher
loading.

The conclusion is robust to the task's half-last-displayed-quantum convention.
At the low endpoint the largest possible index is
\(0.15\times62.5=9.375\); at the high endpoint the smallest possible index is
\(3.75\times7.5=28.125\).  Therefore even these conservative intervals force
the high-loading rate to exceed the low-loading rate.

## Source grounding

- `TASK.json` identifies Q8-3 / PDF page 74 as the source for T8-A7 and asks
  for the classification of the rate trend.
- `T8_page-3.png` and page 74 of `theory_problem.pdf` contain the seven graph
  points transcribed above and the choices `a`, `b`, and `c`.
- `T8_page-2.png` supplies the definition of TOF used in the multiplication.
- The blank student answer sheet on page 82 of `theory_problem.pdf` confirms
  that the requested output is one tick among `a`, `b`, and `c`; it supplies
  no answer.
- The SHA-256 hashes of both images and the PDF were checked against
  `TASK.json` / `isolation_manifest.json`.  No solution, marking scheme,
  answer repository, or historical answer was consulted.

The Lean development separates the graph readings (`displayedGraphPoints`)
from all derived rate calculations and proves both the exact displayed-value
classification and the interval-robust classification.
