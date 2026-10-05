# IChO 2026 T8-A6

The quantum yield for CO formation is

\[
\boxed{\varphi=1.86\%}
\]

(three significant figures). The unrounded result is
\(1.8594101613683624924\ldots\%\).

## Calculation

The catalyst mass in the stated 10 mg loaded sample is

\[
m_{\mathrm{cat}}=(10\times10^{-3}\ \mathrm{g})(0.038)
                 =3.8\times10^{-4}\ \mathrm{g}.
\]

Consequently, the amount and number of catalyst molecules are

\[
n_{\mathrm{cat}}=
\frac{3.8\times10^{-4}\ \mathrm{g}}
     {557.21\ \mathrm{g\ mol^{-1}}}
\approx6.8196909603201665\times10^{-7}\ \mathrm{mol},
\]

\[
N_{\mathrm{cat}}=n_{\mathrm{cat}}N_A
\approx4.1069138902747618\times10^{17}\ \text{molecules}.
\]

By the problem's definition of TOF, the hourly number of CO molecules is

\[
N_{\mathrm{CO}}=(8\ \mathrm{h^{-1}})N_{\mathrm{cat}}
\approx3.2855311122198094\times10^{18}\ \mathrm{h^{-1}}.
\]

The balanced acidic reduction half-reaction is

\[
\mathrm{CO_2+2H^++2e^-\longrightarrow CO+H_2O}.
\]

Thus two reacted electrons correspond to each CO molecule, giving

\[
N_{e^-}=2N_{\mathrm{CO}}
\approx6.5710622244396188\times10^{18}\ \mathrm{h^{-1}}.
\]

For 390 nm light, using \(E_\gamma=hc/\lambda\),

\[
E_\gamma
=\frac{(6.62607015\times10^{-34}\ \mathrm{J\,s})
        (299792458\ \mathrm{m\,s^{-1}})}
       {390\times10^{-9}\ \mathrm m}
\approx5.0934509157664838\times10^{-19}\ \mathrm J.
\]

The number of incident photons in one hour at 50 mW is therefore

\[
N_\gamma=
\frac{(0.050\ \mathrm{J\,s^{-1}})(3600\ \mathrm s)}{E_\gamma}
\approx3.5339498304149819\times10^{20}.
\]

Applying the formula printed in the problem,

\[
\begin{aligned}
\varphi
&=\frac{N_{e^-}}{N_\gamma}\,100\%\\
&=\frac{18940872892793693114789369}
        {10186495312500000000000000}\%\\
&=1.8594101613683624924\ldots\%\\
&\longrightarrow \boxed{1.86\%}.
\end{aligned}
\]

No intermediate value was rounded.

## Source grounding

- `TASK.json` identifies the sole requested output as the CO quantum yield in
  percent and prescribes a three-significant-figure final display while
  retaining the raw result.
- Problem page Q8-2 (PDF page 73; `T8_page-2.png`) supplies 390 nm, 50 mW,
  8 h\(^{-1}\), 10 mg, 3.8%, the catalyst molar mass 557.21 g mol\(^{-1}\),
  the definition of TOF, and the electron/photon quantum-yield formula.
- The two-electron factor is derived from the atom- and charge-balanced acidic
  half-reaction requested in the shared T8 context; it is not an assumed final
  answer.
- The original PDF's blank student answer sheet A8-5 (PDF page 81) was also
  inspected. It contains only work space and the blank field
  \(\varphi=\underline{\hspace{1cm}}\%\); it supplies no hidden values or
  alternative convention.
- The calculation uses the problem's stated mass fraction directly for the
  stated loaded 10 mg batch and applies its TOF to the resulting catalyst
  molecule count. No additional activity fraction is introduced by the
  source. The exact 2019-SI values of \(N_A\), \(h\), and \(c\), together with
  \(E=hc/\lambda\), are standard physical constants and laws.

The Lean development separates the printed inputs, exact SI constants,
stoichiometric derivation, molecule/electron/photon calculations, exact raw
percentage, and final reporting proof.
