import Mathlib.Tactic

/-!
# IChO 2026 T7-A4: aqueous MDEA carbon-dioxide scrubbing

The problem page depicts compound 3 as N-methyldiethanolamine (MDEA),
`CH₃N(CH₂CH₂OH)₂`.  Because MDEA is a tertiary amine, aqueous carbon-dioxide
capture gives protonated MDEA and bicarbonate:

`MDEA + CO₂ + H₂O ⇌ MDEAH⁺ + HCO₃⁻`.

The empirical choice of products is chemistry input, documented in `answer.md`.
This file formalizes the exact equation and proves that its unit coefficients
conserve every represented element and total electric charge.
-/

namespace IChO2026Problems.T7A4

/-- The complete set of elements occurring in the T7-A4 equation. -/
inductive Element where
  | carbon
  | hydrogen
  | nitrogen
  | oxygen
  deriving DecidableEq, Repr

/-- Molecular composition together with net charge in elementary-charge units. -/
structure Species where
  atomCount : Element → ℕ
  charge : ℤ

/-- A species supplied with its stoichiometric coefficient. -/
structure StoichTerm where
  coefficient : ℕ
  species : Species

/-- A chemical equation has a reactant side and a product side. -/
structure ChemicalEquation where
  reactants : List StoichTerm
  products : List StoichTerm

/-- Number of atoms of `element` on one side of an equation. -/
def atomTotal (element : Element) : List StoichTerm → ℕ
  | [] => 0
  | term :: rest =>
      term.coefficient * term.species.atomCount element + atomTotal element rest

/-- Net charge on one side of an equation. -/
def chargeTotal : List StoichTerm → ℤ
  | [] => 0
  | term :: rest =>
      (term.coefficient : ℤ) * term.species.charge + chargeTotal rest

/-- Atom balance for every element, together with charge balance. -/
def IsBalanced (equation : ChemicalEquation) : Prop :=
  (∀ element, atomTotal element equation.reactants = atomTotal element equation.products) ∧
    chargeTotal equation.reactants = chargeTotal equation.products

private def atoms (c h n o : ℕ) : Element → ℕ
  | .carbon => c
  | .hydrogen => h
  | .nitrogen => n
  | .oxygen => o

/-- `CH₃N(CH₂CH₂OH)₂ = C₅H₁₃NO₂`, the neutral tertiary amine drawn as 3. -/
def mdea : Species := ⟨atoms 5 13 1 2, 0⟩

/-- Carbon dioxide, `CO₂`. -/
def carbonDioxide : Species := ⟨atoms 1 0 0 2, 0⟩

/-- Water, `H₂O`. -/
def water : Species := ⟨atoms 0 2 0 1, 0⟩

/-- Protonated MDEA, `CH₃NH⁺(CH₂CH₂OH)₂ = C₅H₁₄NO₂⁺`. -/
def protonatedMdea : Species := ⟨atoms 5 14 1 2, 1⟩

/-- Bicarbonate, `HCO₃⁻`. -/
def bicarbonate : Species := ⟨atoms 1 1 0 3, -1⟩

private def unitTerm (species : Species) : StoichTerm := ⟨1, species⟩

/--
The requested equation, with every stoichiometric coefficient equal to one:

`CH₃N(CH₂CH₂OH)₂ + CO₂ + H₂O ⇌ CH₃NH⁺(CH₂CH₂OH)₂ + HCO₃⁻`.
-/
def reactionEquation : ChemicalEquation :=
  { reactants := [unitTerm mdea, unitTerm carbonDioxide, unitTerm water]
    products := [unitTerm protonatedMdea, unitTerm bicarbonate] }

/-- The displayed structure of compound 3 gives the molecular formula `C₅H₁₃NO₂`. -/
theorem mdea_atom_counts :
    mdea.atomCount .carbon = 5 ∧
    mdea.atomCount .hydrogen = 13 ∧
    mdea.atomCount .nitrogen = 1 ∧
    mdea.atomCount .oxygen = 2 ∧
    mdea.charge = 0 := by
  norm_num [mdea, atoms]

/-- Both sides contain C₆H₁₅NO₅ and have zero net charge. -/
theorem reaction_conserved_totals :
    atomTotal .carbon reactionEquation.reactants = 6 ∧
    atomTotal .hydrogen reactionEquation.reactants = 15 ∧
    atomTotal .nitrogen reactionEquation.reactants = 1 ∧
    atomTotal .oxygen reactionEquation.reactants = 5 ∧
    chargeTotal reactionEquation.reactants = 0 ∧
    atomTotal .carbon reactionEquation.products = 6 ∧
    atomTotal .hydrogen reactionEquation.products = 15 ∧
    atomTotal .nitrogen reactionEquation.products = 1 ∧
    atomTotal .oxygen reactionEquation.products = 5 ∧
    chargeTotal reactionEquation.products = 0 := by
  norm_num [reactionEquation, unitTerm, atomTotal, chargeTotal, mdea, carbonDioxide,
    water, protonatedMdea, bicarbonate, atoms]

/-- Formal verification of the requested T7-A4 reaction equation. -/
theorem t7_a4_reaction_equation : IsBalanced reactionEquation := by
  constructor
  · intro element
    cases element <;>
      norm_num [reactionEquation, unitTerm, atomTotal, mdea, carbonDioxide, water,
        protonatedMdea, bicarbonate, atoms]
  · norm_num [reactionEquation, unitTerm, chargeTotal, mdea, carbonDioxide, water,
      protonatedMdea, bicarbonate]

#print axioms mdea_atom_counts
#print axioms reaction_conserved_totals
#print axioms t7_a4_reaction_equation

end IChO2026Problems.T7A4
