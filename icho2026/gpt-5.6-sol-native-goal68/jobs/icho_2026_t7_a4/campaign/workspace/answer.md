# IChO 2026 T7-A4

## Answer

Compound **3** is N-methyldiethanolamine (MDEA),
`CH₃N(CH₂CH₂OH)₂`.  Its aqueous carbon-dioxide-scrubbing reaction is

\[
\boxed{
\mathrm{CH_3N(CH_2CH_2OH)_2 + CO_2 + H_2O
\rightleftharpoons
[CH_3NH(CH_2CH_2OH)_2]^+ + HCO_3^-}
}
\]

Thus every stoichiometric coefficient is 1.  Equivalently, with
\(R_3N=\mathrm{CH_3N(CH_2CH_2OH)_2}\), the equation is
\(R_3N+CO_2+H_2O\rightleftharpoons R_3NH^+ + HCO_3^-\).

## Why these products follow

The structure printed for 3 has nitrogen bonded to one methyl group and two
2-hydroxyethyl groups.  Nitrogen therefore has three carbon substituents and no
N–H bond: 3 is the tertiary alkanolamine MDEA.  In aqueous solution, a tertiary
amine cannot give the ordinary N-bound carbamate pathway of primary and
secondary amines.  Instead, it acts as a base in CO₂ hydration; proton transfer
gives protonated MDEA while the captured inorganic-carbon species is
bicarbonate.  Camacho *et al.* experimentally study this aqueous MDEA/CO₂
system, identify the depicted formula `CH₃N(CH₂CH₂OH)₂`, and give the net
stoichiometry `CO₂ + H₂O + R₃N ⇌ R₃NH⁺ + HCO₃⁻` (their reaction 16):
[doi:10.1002/kin.20375](https://doi.org/10.1002/kin.20375).

The balance check is

| quantity | reactants | products |
|---|---:|---:|
| C atoms | 6 | 6 |
| H atoms | 15 | 15 |
| N atoms | 1 | 1 |
| O atoms | 5 | 5 |
| net charge | 0 | 0 |

## Source grounding and scope

- The actual problem input [`T7_page-2.png`](icho_2026_source/image/T7_page-2.png)
  states that an **aqueous** solution of structurally drawn compound 3 removes
  CO₂ and asks for the reaction equation.  The drawing, rather than the lossy
  text extraction in `TASK.json`, supplies the identity of 3.
- [`T7_page-1.png`](icho_2026_source/image/T7_page-1.png) places the aqueous
  scrubber `Z` after the water-gas-shift stage and labels its incoming stream
  `N₂, CO₂, H₂`, confirming that CO₂ is the species removed.
- The corresponding original [`theory_problem.pdf`](icho_2026_source/raw/theory_problem.pdf)
  was inspected at PDF page 64.  Its blank student sheet was also inspected at
  PDF page 69 (`A7-3`): the 7.4 area is an empty response box and supplies no
  fallback equation or extra condition.
- The choice of bicarbonate/protonated-MDEA products uses the cited general
  aqueous-tertiary-amine chemistry.  It is not inferred from atom balance
  alone.  No official solution, marking scheme, grading report, historical
  answer, or answer repository was used.

There is no source gap affecting the requested equation.  The equilibrium
arrow records that chemical absorption is reversible; the forward direction
is the CO₂-removal operation described by the question.

## Lean formalization

[`problem_icho_2026_t7_a4.lean`](IChO2026Problems/problem_icho_2026_t7_a4.lean)
defines the exact equation as `reactionEquation`.  It represents every element
present (C, H, N, O), atom counts, stoichiometric coefficients, and integer net
charge.  The proof `reaction_conserved_totals` establishes the explicit common
total `C₆H₁₅NO₅` and charge zero; `t7_a4_reaction_equation` proves elementwise
and charge balance.  Product selection is the empirical chemistry premise
explained above, not a custom Lean axiom.
