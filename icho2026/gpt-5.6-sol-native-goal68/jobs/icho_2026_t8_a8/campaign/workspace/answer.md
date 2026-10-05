# IChO 2026 T8-A8

## Answer

| diagram label | condition to tick |
|---|---|
| **a** | **N** (no irradiation) |
| **b** | **B** (blue light) |
| **c** | **G** (green light) |
| **d** | **R** (red light) |

Thus the requested classification is

\[
\boxed{a=N,\qquad b=B,\qquad c=G,\qquad d=R.}
\]

## Reasoning and source grounding

The supplied product-composition diagram on `T8_page-4.png` (PDF page 75,
headed Q8-4) shows no H₂ or CO bar at **a**, while **b**, **c**, and **d** are
the three illuminated, nonzero-output cases. Because the system is described
as photocatalytic, the zero-output case is the dark control, so **a = N**.

For the illuminated cases, the blue-striped H₂ portions have the strict
order

\[
\chi(\mathrm{H_2})_b > \chi(\mathrm{H_2})_c >
\chi(\mathrm{H_2})_d.
\]

The Gibbs-energy diagram on `T8_page-3.png` (PDF page 74, headed Q8-3) shows
that the proton-reduction/H₂ branch is the more energetically demanding
branch relative to the CO-forming branch. The standard photon relation
\(E=hc/\lambda\), together with
\(\lambda_{\mathrm{blue}}<\lambda_{\mathrm{green}}<
\lambda_{\mathrm{red}}\), gives

\[
E_{\mathrm{blue}}>E_{\mathrm{green}}>E_{\mathrm{red}}.
\]

Consequently, the largest H₂ share is assigned to blue light, the
intermediate share to green, and the smallest share to red: **b = B**,
**c = G**, and **d = R**.

The original `theory_problem.pdf` was also inspected directly. Its PDF page 82
(headed A8-6) is the blank student answer sheet and confirms that part 8.8 is a
four-by-four tick table with rows `a,b,c,d` and columns `N,R,G,B`. It contains
no filled answers and was used only to verify the requested output format.

## Formalization correspondence

The Lean file defines the four conditions and four bars as finite types. It
records only source/physics-derived constraints: a bijection, the dark-control
assignment for the sole zero-output bar, and preservation of the strict order
between H₂ share and photon energy for illuminated bars. It then proves that
the only valid correspondence is `a↦N, b↦B, c↦G, d↦R`. The four
requested-output theorems are derived from this uniqueness theorem.

