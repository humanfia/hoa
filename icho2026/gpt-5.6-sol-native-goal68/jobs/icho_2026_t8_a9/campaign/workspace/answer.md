# IChO 2026 T8-A9

The quenching percentages are

\[
\boxed{\eta_q(S_1)=43.9\%},\qquad
\boxed{\eta_q(T_1)=99.9\%}.
\]

## Calculation

At fixed reductant concentration, a bimolecular quenching constant (k_q)
gives a pseudo-first-order quenching rate

\[
k'_q=k_q[\mathrm{Red}].
\]

For an excited state whose lifetime without quencher is \(\tau_0\), the sum of
the competing intrinsic first-order decay rates is \(k_0=1/\tau_0\). The
fraction of excited molecules that use the added quenching channel is therefore

\[
f_q=\frac{k'_q}{k_0+k'_q}
   =\frac{k_q[\mathrm{Red}]\tau_0}
          {1+k_q[\mathrm{Red}]\tau_0},
\qquad \eta_q=100f_q.
\]

For \(S_1\), using the printed values without intermediate rounding,

\[
x_S=k_S[\mathrm{Red}]\tau_0(S_1)
=(2.7\times10^9)(0.1)(2.9\times10^{-9})=0.783,
\]

so

\[
\eta_q(S_1)=100\frac{0.783}{1+0.783}
=\frac{78300}{1783}\%=43.9147504\ldots\%=\boxed{43.9\%}.
\]

For \(T_1\),

\[
x_T=k_T[\mathrm{Red}]\tau_0(T_1)
=(1.5\times10^8)(0.1)(84\times10^{-6})=1260,
\]

so

\[
\eta_q(T_1)=100\frac{1260}{1+1260}
=\frac{126000}{1261}\%=99.9206979\ldots\%=\boxed{99.9\%}.
\]

Both boxed values are reported to three significant figures, as required by
`TASK.json`; the raw exact values are retained in the Lean formalization.

## Source grounding and model boundary

The numerical inputs come directly from the supplied problem materials:

- `T8_page-5.png` and PDF page 76 (printed page Q8-5) state
  \(k_S=2.7\times10^9\ \mathrm{M^{-1}s^{-1}}\),
  \(k_T=1.5\times10^8\ \mathrm{M^{-1}s^{-1}}\),
  \(\tau_0(S_1)=2.9\ \mathrm{ns}\),
  \(\tau_0(T_1)=84\ \mathrm{\mu s}\), and
  \([\mathrm{Red}]=0.1\ \mathrm M\).
- PDF page 83 (printed page A8-7), the blank student answer sheet, asks for
  exactly the two entries \(\eta_q(S_1)\) and \(\eta_q(T_1)\), both in percent.
- `T8_page-4.png` supplies the immediately preceding context but adds no
  numerical input needed for part 8.9.

The only general kinetic law used is mass action plus the branching ratio for
competing first-order processes. The supplied unquenched lifetime represents
the total intrinsic departure rate through \(1/\tau_0\), so the individual
values of \(k_F\), \(k_{ISC}\), and other intrinsic channels are not needed.
The printed note \(k_F\gg k_{ISC}\) is consistent with fluorescence dominating
the singlet's intrinsic loss, but no numerical approximation based on that
inequality is inserted into the calculation. There is no source gap affecting
either requested result.
