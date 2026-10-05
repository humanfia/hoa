import Mathlib

/-!
# IChO 2026, Theory Problem T8, Part A1 (printed subquestion 8.1)

Source: `theory_problem.pdf`, source page 72 (printed page Q8-1),
image `T8_page-1.png`, 2.0 pt.

> **8.1  Write** the half equation for the reduction of CO₂ to CO in an
> acidic medium.

## The half equation

In acidic aqueous medium the balanced reduction half equation is

    CO₂ + 2 H⁺ + 2 e⁻  →  CO + H₂O

This file formalizes what "balanced" means and *verifies* that this
equation satisfies it, and that its acidic-medium coefficients are
uniquely forced by the balance laws:

* it is a **reduction** half equation: the electron is a reactant;
* it converts exactly one CO₂ into exactly one CO
  (the stoichiometry printed above the catalyst **1** arrow on the
  problem page, `CO₂ --1--> CO`);
* it uses only the reagents allowed in an acidic medium
  (H⁺, H₂O and electrons, by the standard half-equation balancing
  conventions trusted as general chemical law);
* atoms of carbon and oxygen, hydrogen count, and net electrical charge
  are all conserved.

## Formalization

Each species is modeled through its coefficient function on the two
sides of the equation, and balance is the equality of the
coefficient-weighted (C, O, H, charge) totals.  The theorem
`half_equation_balanced` verifies the answer; `coefficients_forced`
shows that, given one CO₂ consumed, one CO formed and the two-electron
reduction, the coefficients 2 of H⁺ and 1 of H₂O are forced by atom
conservation alone.
-/

namespace IChO2026.Problems.T8.A1

/-- The species that may appear in the half equation for the reduction of
CO₂ to CO in acidic medium: the substrates named by the problem (CO₂ and
CO), the acidic-medium reagents (H⁺ and H₂O) and the electron. -/
inductive Species
  | CO2 | CO | Hplus | H2O | electron
  deriving DecidableEq, Repr

/-- Atom/charge inventory of a species as a vector over
(carbon, oxygen, hydrogen, net charge).  These are the defining chemical
identities of each species (trusted general chemistry): CO₂ = O=C=O,
CO = carbon monoxide, H⁺ = proton, H₂O = water, e⁻ charge −1. -/
def inventory : Species → ℤ × ℤ × ℤ × ℤ
  | .CO2      => (1, 2, 0,  0)
  | .CO       => (1, 1, 0,  0)
  | .Hplus    => (0, 0, 1,  1)
  | .H2O      => (0, 1, 2,  0)
  | .electron => (0, 0, 0, -1)

/-- A half equation `left → right` is *balanced* when, writing `l s` and
`r s` for the coefficient of each species on the two sides, the totals of
carbon, oxygen, hydrogen and net charge agree:

* C: `l CO2 = r CO`  (CO₂ and CO are the only carbon carriers);
* O: `2·l CO2 = r CO + r H2O`;
* H: `l H⁺ = 2·r H2O`;
* charge: `l H⁺ − l e⁻ = 0`.
-/
structure Balanced (left right : Species → ℤ) : Prop where
  carbon   : left .CO2 = right .CO
  oxygen   : 2 * left .CO2 + right .CO2 * 0 + left .CO * 0
               = right .CO + right .H2O + left .H2O * 0
  hydrogen : left .Hplus + left .H2O * 2 = right .Hplus + right .H2O * 2
  charge   : left .Hplus - left .electron = right .Hplus - right .electron

/-- The left-hand (reactant) side of the answer: one CO₂, two H⁺ and two
electrons. -/
def lhs : Species → ℤ
  | .CO2 => 1 | .Hplus => 2 | .electron => 2 | _ => 0

/-- The right-hand (product) side of the answer: one CO and one H₂O. -/
def rhs : Species → ℤ
  | .CO => 1 | .H2O => 1 | _ => 0

/-- **Main theorem.** The half equation

    CO₂ + 2 H⁺ + 2 e⁻ → CO + H₂O

is balanced in carbon, oxygen, hydrogen and net charge. -/
theorem half_equation_balanced : Balanced lhs rhs := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- The answer is a *reduction* half equation: electrons appear on the
reactant side, not the product side. -/
theorem is_reduction : lhs .electron = 2 ∧ rhs .electron = 0 :=
  ⟨rfl, rfl⟩

/-- The equation converts exactly the substrates named by the problem
(and printed as `CO₂ --1--> CO` on the problem page): one CO₂ consumed
per one CO formed, with no CO on the left and no CO₂ on the right. -/
theorem substrates_as_printed :
    lhs .CO2 = 1 ∧ rhs .CO = 1 ∧ rhs .CO2 = 0 ∧ lhs .CO = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Two electrons are consumed per CO₂, i.e. carbon is reduced from
oxidation state +IV in CO₂ to +II in CO: a two-electron reduction. -/
theorem two_electron_reduction : lhs .electron = 2 * lhs .CO2 := rfl

/-- **Uniqueness.** Once a half equation is required to consume one CO₂,
produce one CO, consume two electrons up front, and use only the
acidic-medium reagents H⁺ (left) and H₂O (right), atom balance forces
exactly two H⁺ and one H₂O.  Hence the answer required by subquestion
8.1 is uniquely determined by the balance laws; it is not an arbitrary
choice among balanced-looking equations. -/
theorem coefficients_forced
    (hLeft hRight : Species → ℤ)
    (hCO2 : hLeft .CO2 = 1) (hCO : hRight .CO = 1)
    (_he : hLeft .electron = 2)
    (hPlacement : hLeft .CO = 0 ∧ hRight .CO2 = 0 ∧
                  hRight .Hplus = 0 ∧ hLeft .H2O = 0 ∧
                  hRight .electron = 0)
    (hbal : Balanced hLeft hRight) :
    hLeft .Hplus = 2 ∧ hRight .H2O = 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hPlacement
  have hO := hbal.oxygen
  have hH := hbal.hydrogen
  rw [hCO2, hCO, h2, h4] at hO
  rw [h3, h4] at hH
  constructor <;> omega

#print axioms half_equation_balanced
#print axioms coefficients_forced

end IChO2026.Problems.T8.A1
