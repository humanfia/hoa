# IChO 2026 T4-A8

## Answer

For complete combustion with all species gaseous,

\[
\mathrm{CH_4(g)+2O_2(g)\longrightarrow CO_2(g)+2H_2O(g)}.
\]

First derive the preceding thermochemical results rather than using the
problem's fallback value.  At 298 K,

\[
\begin{aligned}
\Delta_rH_{298}
 &=\left[-393.5+2(-241.8)\right]-[-74.8]\\
 &=-802.3\ \mathrm{kJ\,mol^{-1}}.
\end{aligned}
\]

The reaction heat-capacity change is

\[
\Delta_rC_p=(37+2\cdot34)-(35+2\cdot29)
           =12\ \mathrm{J\,mol^{-1}\,K^{-1}}.
\]

Using the temperature-dependence equation printed on the general equations
sheet,

\[
\begin{aligned}
\Delta_rH_{2000}
 &=\Delta_rH_{298}+\frac{\Delta_rC_p(2000-298)}{1000}\\
 &=-802.3+\frac{12(1702)}{1000}\\
 &=-781.876\ \mathrm{kJ\,mol^{-1}}.
\end{aligned}
\]

At the pre-ignition conditions, the printed ideal-gas law and gas constant give

\[
\begin{aligned}
n&=\frac{PV}{RT}\\
 &=\frac{(101325\ \mathrm{Pa})(2.2\times10^5\ \mathrm{m^3})}
          {(8.314\ \mathrm{J\,mol^{-1}\,K^{-1}})(298\ \mathrm K)}\\
 &=8.9973167278\times10^6\ \mathrm{mol}.
\end{aligned}
\]

Therefore, if the printed volume is the methane volume delivered in one day,
the positive magnitude of the released energy is

\[
\begin{aligned}
E
 &=n\left|\Delta_rH_{2000}\right|(1000\ \mathrm{J\,kJ^{-1}})\\
 &=\frac{4357297213500000000}{619393}\ \mathrm{J\,day^{-1}}\\
 &=7.03478601388779\times10^{12}\ \mathrm{J\,day^{-1}}.
\end{aligned}
\]

The requested three-significant-figure report is thus

\[
\boxed{E=7.03\times10^{12}\ \mathrm{J\,day^{-1}}}.
\]

The Lean proof keeps the raw rational value exact and proves that it lies in
the rounding interval
\([7.025\times10^{12},7.035\times10^{12})\), whose reported midpoint is
\(7.03\times10^{12}\) with last-place quantum \(10^{10}\).

## Source grounding and dimensional qualification

- `T4_page-2.png` and PDF page 38 give the three formation enthalpies and four
  heat capacities used above.  The zero formation enthalpy of
  \(\mathrm{O_2}\) is the defining standard-state convention for an element.
- `T4_page-3.png` and PDF page 39 give 2000 K, 101.325 kPa, 298 K, and
  \(Q=2.2\times10^5\ \mathrm{m^3}\).  The fallback
  \(-700\ \mathrm{kJ\,mol^{-1}}\) was not used.
- PDF page 3 fixes \(R=8.314\ \mathrm{J\,K^{-1}\,mol^{-1}}\).  PDF page 4
  gives \(PV=nRT\), the constant-\(\Delta_rC_p\) enthalpy relation, and the
  instruction to treat all gases as ideal.
- The blank student sheet on PDF page 42 (A4-3) has only the fields
  `ΔrH2000 = ___ kJ mol−1` and `E = ___ J day−1`; it supplies no additional
  time unit for the flow.

There is a source-level dimensional omission: the flow datum is printed with
unit \(\mathrm{m^3}\), not \(\mathrm{m^3\,day^{-1}}\) (or any other time
denominator).  The boxed numerical answer is consequently conditional on the
apparently intended one-day basis.  If the printed volume instead corresponds
to an interval of \(\tau\) days, the result is

\[
E(\tau)=\frac{7.03478601388779\times10^{12}}{\tau}
\ \mathrm{J\,day^{-1}},
\]

so the literal printed data do not determine an unconditional daily value.
The Lean theorem `missing_time_basis_changes_daily_energy` formalizes this
dependence by proving that one-day and two-day interpretations give unequal
daily energies.
