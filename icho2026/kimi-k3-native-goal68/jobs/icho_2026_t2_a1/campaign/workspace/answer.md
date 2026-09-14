# IChO 2026 - Problem T2, Subquestion 2.1 (target `icho_2026_t2_a1`)

## Requested output

One exact symbolic output (`balanced_bz_equation`): the overall balanced
equation of the Belousov-Zhabotinsky reaction, with atoms and charge
conserved.

## Answer

$$3\,\mathrm{CH_2(COOH)_2} + 4\,\mathrm{BrO_3^-} \;\longrightarrow\; 9\,\mathrm{CO_2} + 4\,\mathrm{Br^-} + 6\,\mathrm{H_2O}$$

(equivalently: 3 C3H4O4 + 4 BrO3- -> 9 CO2 + 4 Br- + 6 H2O).

Verification of balance:

| Element / charge | Left side | Right side |
|---|---|---|
| C | 3 * 3 = 9 | 9 * 1 = 9 |
| H | 3 * 4 = 12 | 6 * 2 = 12 |
| O | 3 * 4 + 4 * 3 = 24 | 9 * 2 + 6 * 1 = 24 |
| Br | 4 * 1 = 4 | 4 * 1 = 4 |
| charge | 4 * (-1) = -4 | 4 * (-1) = -4 |

## Derivation (oxidation-number / half-reaction method)

The note in the problem fixes the redox bookkeeping completely:

- **Oxidation:** malonic acid MA = CH2(COOH)2 = C3H4O4 is fully oxidised to
  CO2. With H at +1 and O at -2, the average carbon oxidation state in
  C3H4O4 satisfies 3x + 4(+1) + 4(-2) = 0, i.e. x = +4/3. In CO2 carbon is
  +4. The three carbons therefore release 3 * (4 - 4/3) = 8 electrons:

  C3H4O4 + 2 H2O -> 3 CO2 + 8 H+ + 8 e-

- **Reduction:** in BrO3- bromine is +5; in Br- it is -1, so each bromate
  consumes 6 electrons (acidic medium, balanced with H+/H2O):

  BrO3- + 6 H+ + 6 e- -> Br- + 3 H2O

- **Combination:** lcm(8, 6) = 24, so take 3 copies of the oxidation
  half-reaction and 4 copies of the reduction half-reaction. Adding them
  gives

  3 C3H4O4 + 6 H2O + 4 BrO3- + 24 H+ -> 9 CO2 + 24 H+ + 4 Br- + 12 H2O

  and cancelling 24 H+ and 6 H2O from both sides yields the overall equation
  above.

- **Cerium:** the note states Ce(IV) is a catalyst, so Ce4+/Ce3+ cancel
  between the processes and cerium does not appear in the overall equation.
  (The mechanism printed in question 2.2 confirms this: Ce4+ is consumed in
  Process C (7) and regenerated via step (2) of Process A; sulfate and K+ are
  spectator ions from the H2SO4/KBrO3 medium and likewise never enter the net
  equation.)

## Source grounding

- Problem sheet page Q2-1 (`T2_page-1.png`, `theory_problem.pdf` page 15):
  the reactants are KBrO3, CH2(COOH)2 (malonic acid, - MA), Ce(SO4)2, and
  H2SO4; the question asks for the overall balanced equation and stipulates
  "MA is oxidised to CO2, BrO3- is reduced to Br-, and Ce(IV) is a
  catalyst".
- Answer sheet page A2-1 (`theory_problem.pdf` page 19) provides a blank
  field for 2.1 only - a single equation is the expected output.
- Mechanism context on page Q2-2 (question 2.2, used only as corroborating
  context within the same problem): Process C step (7) consumes Ce4+ and
  releases Br-, Process A step (2) regenerates Ce4+, consistent with Ce(IV)
  being a catalyst as stated in the note of 2.1.
- Standard oxidation-number conventions (H = +1, O = -2, average oxidation
  states may be fractional) were used; this is ordinary chemistry, not
  competition material.

## Formalization

`IChO2026Problems/problem_icho_2026_t2_a1.lean` encodes the species CO2,
Br-, BrO3-, H2O and MA as element-count vectors with charges over
`{C, H, O, Br}`, defines `overallBZ` as the equation
`3*MA + 4*BrO3 -> 9*CO2 + 4*BrIon + 6*H2O`, and proves:

- `overallBZ_isBalanced` - conservation of every element and of charge, with
  nonzero coefficients (no spurious zero-coefficient terms);
- `overallBZ_atom_balance`, `overallBZ_charge_balance` - the explicit
  integer identities per element and for charge;
- `oxidation_half_reaction_balance`, `reduction_half_reaction_balance` -
  balance of the two half-reactions used in the derivation;
- `electron_lcm` - the electron ledger lcm(8, 6) = 24 with multiplicities
  3 and 4;
- `cerium_is_catalyst_balance` - the Ce row of the balance (0 = 0).

All theorems were checked with `#print axioms`: none depends on any axiom
(no `sorryAx`, not even `propext`/`Classical.choice`/`Quot.sound`). The
chemistry encoded was checked independently of the build: `overallBZ` uses
exactly the species the problem involves and the coefficients derived above,
and the balance identities match the hand verification table.
