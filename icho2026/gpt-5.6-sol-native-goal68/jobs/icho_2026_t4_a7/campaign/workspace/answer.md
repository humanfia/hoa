# IChO 2026 T4-A7

For gaseous methane combustion,

\[
\mathrm{CH_4(g)+2\,O_2(g)\longrightarrow CO_2(g)+2\,H_2O(g)}.
\]

First derive the 298 K reaction enthalpy from the data in T4-A6.  The standard
formation enthalpy of \(\mathrm{O_2(g)}\) is zero because oxygen gas is the
element in its standard state:

\[
\begin{aligned}
\Delta_r H^\circ_{298}
 &= \left[\Delta_fH^\circ(\mathrm{CO_2})
        +2\Delta_fH^\circ(\mathrm{H_2O(g)})\right] \\
 &\quad-\left[\Delta_fH^\circ(\mathrm{CH_4})
        +2\Delta_fH^\circ(\mathrm{O_2})\right] \\
 &= [-393.5+2(-241.8)]-[-74.8+2(0)] \\
 &= -802.3\ \mathrm{kJ\,mol^{-1}}.
\end{aligned}
\]

The reaction heat-capacity change is

\[
\begin{aligned}
\Delta_r C_p
 &= [C_p(\mathrm{CO_2})+2C_p(\mathrm{H_2O})]
    -[C_p(\mathrm{CH_4})+2C_p(\mathrm{O_2})] \\
 &= (37+2\cdot34)-(35+2\cdot29) \\
 &= 12\ \mathrm{J\,mol^{-1}\,K^{-1}}.
\end{aligned}
\]

Using Kirchhoff's law with the tabulated heat capacities treated as constant,

\[
\begin{aligned}
\Delta_r H_{2000}
 &= \Delta_rH^\circ_{298}
    +\frac{\Delta_rC_p(2000-298)}{1000} \\
 &= -802.3+\frac{12\cdot1702}{1000} \\
 &= -802.3+20.424 \\
 &= -781.876\ \mathrm{kJ\,mol^{-1}}.
\end{aligned}
\]

Thus the requested answer, to three significant figures, is

\[
\boxed{\Delta_rH_{2000}=-782\ \mathrm{kJ\,mol^{-1}}}.
\]

## Source grounding and model boundary

- `TASK.json` identifies T4-A7 as the requested methane-combustion enthalpy at
  2000 K and supplies the three-significant-figure reporting policy.
- `T4_page-2.png`, matching PDF page 38, supplies the T4-A6 formation
  enthalpies and heat capacities used above, and states that all species are
  gaseous.
- `T4_page-3.png`, matching PDF page 39 (`Q4-3`), contains the T4-A7 question.
- The blank student sheets in the original PDF were also checked: PDF page 41
  (`A4-2`) has the blank T4-A6 line, and page 42 (`A4-3`) asks for one value of
  \(\Delta_rH_{2000}\) in \(\mathrm{kJ\,mol^{-1}}\).  They provide no extra
  numerical premise or precision instruction.
- Products-minus-reactants for formation enthalpies and Kirchhoff's law are
  standard thermodynamic laws.  The zero formation enthalpy of
  \(\mathrm{O_2(g)}\) is the standard-state convention, not an extra measured
  datum.
- The paper lists one \(C_p\) number for each gas but does not explicitly say
  that these values are temperature-independent from 298 K to 2000 K.  The
  calculation above is therefore the constant-\(C_p\) approximation clearly
  indicated by the data supplied for this exercise.  Without that intended
  approximation (or temperature-dependent \(C_p(T)\) data), an exact physical
  high-temperature enthalpy would be underdetermined by the problem statement.

The Lean formalization keeps the printed inputs, the balanced-reaction change,
the constant-\(C_p\) Kirchhoff transformation, the exact raw result, and the
final rounding relation separate.
