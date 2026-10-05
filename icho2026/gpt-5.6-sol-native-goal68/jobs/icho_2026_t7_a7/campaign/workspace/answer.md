# IChO 2026 T7.7

## Answer

| requested item | result |
|---|---|
| 7 | **LaN** |
| 8 | **Ca₃N₂** |
| 9 | **Si₃N₄** |
| 10 | **La₅Ca₉O₂[SiO₃N][Si₁₂N₂₄]**, equivalently the flat empirical formula **La₅Ca₉Si₁₃N₂₅O₅** |
| S | **O²⁻** |
| T | **[SiO₃N]⁵⁻**, a tetrahedral Si-centred anion |

Thus, in the notation of the question, one may take

\[
Q=\mathrm{La},\quad \alpha=5,\qquad
R=\mathrm{Ca},\quad \beta=9,
\]

and

\[
\boxed{\mathrm{La_5Ca_9O_2[SiO_3N][Si_{12}N_{24}]}}.
\]

(`Q` and `R` are dummy labels, so interchanging the two labels while also
interchanging their coefficients does not change the chemical formula.)

## Derivation

The supplied periodic table gives

\[
A_r(\mathrm{La})=138.9,\ A_r(\mathrm{Ca})=40.08,\
A_r(\mathrm{Si})=28.09,\ A_r(\mathrm N)=14.01,\ A_r(\mathrm O)=16.00.
\]

The three binary nitrides whose calculated nitrogen percentages reproduce the
three printed values are:

\[
\begin{aligned}
w_N(\mathrm{LaN})
  &=100\frac{14.01}{138.9+14.01}
    =9.162252\ldots\%,\\
w_N(\mathrm{Ca_3N_2})
  &=100\frac{2(14.01)}{3(40.08)+2(14.01)}
    =18.899231\ldots\%,\\
w_N(\mathrm{Si_3N_4})
  &=100\frac{4(14.01)}{3(28.09)+4(14.01)}
    =39.940133\ldots\%.
\end{aligned}
\]

These lie respectively in the half-last-displayed-place intervals
\([9.155,9.165]\), \([18.895,18.905]\), and \([39.935,39.945]\), so they
give the printed 9.16%, 18.90%, and 39.94%. Their charge-neutral empirical
ratios are also exactly those required by La(III), Ca(II), Si(IV), and
N(−III).

The corresponding formula masses are 152.91, 148.26, 140.31, and 60.09 for
LaN, Ca₃N₂, Si₃N₄, and SiO₂. The mole ratio recovered from the printed mass
ratio is

\[
\mathrm{LaN:Ca_3N_2:Si_3N_4:SiO_2}=10:6:7:5.
\]

Indeed, the raw mass ratios for that integer batch, normalized by the mass of
5 mol SiO₂, are

\[
\frac{10(152.91)}{5(60.09)}=5.089365951\ldots,
\quad
\frac{6(148.26)}{5(60.09)}=2.960758862\ldots,
\quad
\frac{7(140.31)}{5(60.09)}=3.268996505\ldots.
\]

They lie in the source intervals \([5.085,5.095]\), \([2.955,2.965]\), and
\([3.265,3.275]\), hence reproduce 5.09 : 2.96 : 3.27 : 1.00 without
intermediate rounding.

Conserving every atom gives

\[
10\,\mathrm{LaN}+6\,\mathrm{Ca_3N_2}+7\,\mathrm{Si_3N_4}
+5\,\mathrm{SiO_2}
\longrightarrow 2\,\mathrm{La_5Ca_9Si_{13}N_{25}O_5}.
\]

The left side contains La₁₀Ca₁₈Si₂₆N₅₀O₁₀, so division by two gives the
primitive empirical composition La₅Ca₉Si₁₃N₂₅O₅. Removing the explicitly
given framework [Si₁₂N₂₄] leaves La₅Ca₉SiNO₅. After the metal cations are
separated, the atoms to be divided between S₂ and T are SiNO₅.

Because S is monoatomic and occurs twice, S cannot be nitride: there is only
one residual N atom. Hence S is O²⁻. The two copies of S consume O₂, leaving
SiO₃N for T. A Si atom with its four O/N ligands is the required tetrahedral
unit, so T = [SiO₃N]⁵⁻.

Finally, the formal-charge check is

\[
5(+3)+9(+2)=+33,
\]

while

\[
2(-2)+[4+3(-2)+(-3)]+[12(4)+24(-3)]
=-4-5-24=-33.
\]

Thus both atom balance and charge balance support the stated decomposition.

## Source grounding and boundary

- The problem statement and all five numbered constraints were read from
  `icho_2026_source/image/T7_page-4.png` and original PDF page 66 (Q7-4) of
  `icho_2026_source/raw/theory_problem.pdf`.
- The atomic masses were read from original PDF page 5 (G1-5), the supplied
  periodic table.
- Original PDF page 71 (A7-5), the blank student answer sheet for 7.7, was
  inspected. It supplies four formula blanks (7–10) and no additional
  chemical premise or answer content.
- Actual source inputs in the Lean model are the printed atomic masses,
  percentage/mass-ratio display intervals, N(−III), the quantitative
  single-product atom balance, the cation oxidation states, and the stated
  monoatomic/tetrahedral constraints. The candidate formulae, integer reaction
  coefficients, product atom counts, anion compositions, and charge checks
  are derived results.
- The only general chemical interpretation used beyond literal atom counting
  is the standard one that a tetrahedral Si/O/N unit has one central Si and
  four O/N ligands. No official solution, marking scheme, answer repository,
  or historical answer was consulted.

There is no source gap affecting the requested formulas.
