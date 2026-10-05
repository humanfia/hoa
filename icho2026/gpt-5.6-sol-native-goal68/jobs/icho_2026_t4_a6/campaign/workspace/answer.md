# IChO 2026 T4-A6

For complete combustion of one mole of methane with every species gaseous,

\[
\mathrm{CH_4(g) + 2\,O_2(g) \longrightarrow CO_2(g) + 2\,H_2O(g)}.
\]

At 298 K, Hess's law gives

\[
\begin{aligned}
\Delta_{\mathrm r}H^\circ_{298}
&= \sum \nu\Delta_{\mathrm f}H^\circ_{298}(\text{products})
 - \sum \nu\Delta_{\mathrm f}H^\circ_{298}(\text{reactants}) \\
&= \left[-393.5 + 2(-241.8)\right]
 - \left[-74.8 + 2(0)\right] \\
&= -802.3\ \mathrm{kJ\,mol^{-1}}.
\end{aligned}
\]

Here \(\Delta_{\mathrm f}H^\circ_{298}(\mathrm{O_2(g)})=0\) because gaseous
O₂ is elemental oxygen's standard reference state. The heat capacities in
the table are not needed: this subquestion asks for the reaction enthalpy at
the same temperature as the tabulated formation enthalpies. They become
relevant only to the temperature change in part 4.7.

Thus the requested three-significant-figure answer is

\[
\boxed{\Delta_{\mathrm r}H^\circ_{298}=-802\ \mathrm{kJ\,mol^{-1}}}
\]

with unrounded/raw value \(-802.3\ \mathrm{kJ\,mol^{-1}}\).

## Source grounding

- `TASK.json` identifies T4-A6 as a one-mole methane-combustion enthalpy at
  298 K, requires gaseous species, and specifies three significant figures for
  the final display.
- `icho_2026_source/image/T4_page-2.png` and page 38 (one-based) of
  `icho_2026_source/raw/theory_problem.pdf` print
  \(\Delta_{\mathrm f}H^\circ_{298}(\mathrm{CH_4})=-74.8\),
  \(\Delta_{\mathrm f}H^\circ_{298}(\mathrm{H_2O,g})=-241.8\), and
  \(\Delta_{\mathrm f}H^\circ_{298}(\mathrm{CO_2})=-393.5\), all in
  kJ mol⁻¹. `T4_page-1.png` supplies the immediately preceding T4 context.
- The blank student answer sheet A4-2 on page 41 (one-based) of the same PDF
  provides a single field labelled
  \(\Delta_{\mathrm r}H_{298}=\underline{\hspace{1cm}}\ \mathrm{kJ\,mol^{-1}}\),
  consistent with the single requested numerical output.
- The red value \(-750\ \mathrm{kJ\,mol^{-1}}\) below the table is explicitly
  a fallback for later calculations when part 4.6 was not obtained. It is not
  an answer to part 4.6 and was not used.
- The reaction equation, Hess's law, and the zero standard formation enthalpy
  of O₂(g) are standard thermochemical laws/conventions. No previous-part
  result or external competition answer is used, and there is no source gap.

