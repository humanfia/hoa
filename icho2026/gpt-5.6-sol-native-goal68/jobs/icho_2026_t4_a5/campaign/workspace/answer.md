# IChO 2026 T4-A5

The logarithmic decrement is additive over successive collisions. If the
average decrement per collision is the constant \(\xi\), then after an average
of \(n_c\) collisions,

\[
n_c\xi=\ln\!\left(\frac{E_\text{initial}}{E_\text{final}}\right).
\]

First put both energies in electronvolts:

\[
E_\text{initial}=2\ \mathrm{MeV}=2.000000\times10^6\ \mathrm{eV},
\qquad E_\text{final}=0.012\ \mathrm{eV}.
\]

Therefore

\[
\begin{aligned}
n_c
&=\frac{\ln\!\left((2.000000\times10^6)/0.012\right)}{0.948}\\
&=\frac{\ln(166666666.666\ldots)}{0.948}\\
&=19.969943425863\ldots\ \text{collisions}.
\end{aligned}
\]

To three significant figures, the requested average is

\[
\boxed{n_c=20.0\ \text{collisions}}.
\]

This is an average count, so the unrounded value need not be an integer.

## Source grounding

- `TASK.json` identifies T4-A5 and records the requested output and the
  answer-blind three-significant-figure reporting policy.
- `icho_2026_source/image/T4_page-2.png` prints the definition
  \(\xi=\ln(E_\text{initial}/E_\text{final})\), says that \(\xi\) is constant
  for a material, and gives \(2\ \mathrm{MeV}\), \(0.012\ \mathrm{eV}\), and
  \(\xi(\text{water})=0.948\). `T4_page-1.png` supplies the preceding T4
  context and contains no additional dependency for part 4.5.
- The original `icho_2026_source/raw/theory_problem.pdf` was independently
  inspected. PDF page 38 is the official Q4-2 page containing part 4.5. Its
  blank student sheets are PDF pages 40--41 (A4-1 and A4-2); A4-2 contains a
  single answer field labelled \(n_c\) for part 4.5 and supplies no extra data.
- The conversion \(1\ \mathrm{MeV}=10^6\ \mathrm{eV}\) is the standard SI
  prefix conversion. The equation \(n_c\xi=\ln(E_i/E_f)\) follows by adding
  the stated constant per-collision logarithmic decrements. No earlier problem
  result, supplementary model premise, or competition solution is used.

The Lean development keeps the printed inputs separate from the derived raw
count, proves uniqueness under the stated constant-decrement equation, derives
rational bounds for the logarithm from proved mathlib logarithm bounds, and
certifies that the raw value lies strictly between 19.95 and 20.05. Thus `20.0`
is proved to satisfy the fixed reporting contract rather than being assumed.
There are no source gaps for this subquestion.
