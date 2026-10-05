import Mathlib

/-!
# IChO 2026, theory problem 5.3

This file formalizes the determination of the molecular formula of the fatty
acid in PL1.  The two numerical observations printed in the problem are kept
separate from the transparent chemistry model used to interpret them.

The model uses the fragment drawing on Q5-1:

* four identical fatty-acyl residues;
* three glycerol residues;
* two phosphoric-acid residues;
* a connected, acyclic PL1 molecule.

For an acyclic monocarboxylic acid with `c` carbon atoms, `d` carbon-carbon
double bonds, and `t` carbon-carbon triple bonds, the hydrogen count is
`2*c - (2*d + 4*t)`.  Keeping `t` in the model avoids silently assuming the
absence of alkynes: the observations themselves will force `t = 0`.  Complete
ozonolysis cuts its acyclic carbon skeleton into `d + t + 1` chain fragments.
In the stated case the three products are different and equimolar, so every
fragment occurs once and the observed number of product species is also the
fragment count.
-/

namespace IChO2026Problems.T5A3

/-- Atom counts used for the formulas relevant to this subquestion. -/
@[ext] structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  phosphorus : ℕ
deriving DecidableEq, Repr

namespace MolecularFormula

/-- Componentwise addition of molecular formulas. -/
def add (x y : MolecularFormula) : MolecularFormula where
  carbon := x.carbon + y.carbon
  hydrogen := x.hydrogen + y.hydrogen
  oxygen := x.oxygen + y.oxygen
  phosphorus := x.phosphorus + y.phosphorus

/-- `n` copies of a molecular formula. -/
def scale (n : ℕ) (x : MolecularFormula) : MolecularFormula where
  carbon := n * x.carbon
  hydrogen := n * x.hydrogen
  oxygen := n * x.oxygen
  phosphorus := n * x.phosphorus

/-- Total number of atoms in a molecular formula. -/
def atomCount (x : MolecularFormula) : ℕ :=
  x.carbon + x.hydrogen + x.oxygen + x.phosphorus

end MolecularFormula

/-- Formula of a monocarboxylic acid when its carbon and hydrogen counts are
left symbolic. -/
def fattyAcidFormula (c h : ℕ) : MolecularFormula where
  carbon := c
  hydrogen := h
  oxygen := 2
  phosphorus := 0

def glycerolFormula : MolecularFormula := ⟨3, 8, 3, 0⟩

def phosphoricAcidFormula : MolecularFormula := ⟨0, 3, 4, 1⟩

def waterFormula : MolecularFormula := ⟨0, 2, 1, 0⟩

/-- Atom counts of neutral PL1 obtained from four acids, two phosphoric acids,
and three glycerols after eight condensations. -/
def pl1Formula (c h : ℕ) : MolecularFormula where
  carbon := 4 * c + 9
  hydrogen := 4 * h + 14
  oxygen := 17
  phosphorus := 2

/-- The formula above really balances the fragment assembly (equivalently,
the hydrolysis equation `PL1 + 8 H₂O -> 4 acid + 2 H₃PO₄ + 3 glycerol`). -/
theorem pl1_fragment_atom_balance (c h : ℕ) :
    MolecularFormula.add (pl1Formula c h)
        (MolecularFormula.scale 8 waterFormula) =
      MolecularFormula.add
        (MolecularFormula.scale 4 (fattyAcidFormula c h))
        (MolecularFormula.add
          (MolecularFormula.scale 2 phosphoricAcidFormula)
          (MolecularFormula.scale 3 glycerolFormula)) := by
  ext <;>
    simp [MolecularFormula.add, MolecularFormula.scale, pl1Formula,
      waterFormula, fattyAcidFormula, phosphoricAcidFormula, glycerolFormula]

/-- A connected acyclic molecule has one fewer sigma bond than atoms.  Applied
to the atom counts of PL1, this is its sigma-bond count. -/
def pl1SigmaBondCount (c h : ℕ) : ℕ :=
  MolecularFormula.atomCount (pl1Formula c h) - 1

theorem pl1_sigma_bond_count (c h : ℕ) :
    pl1SigmaBondCount c h = 4 * c + 4 * h + 41 := by
  simp [pl1SigmaBondCount, MolecularFormula.atomCount, pl1Formula]
  omega

/-- PL1 has four copies of every chain C=C bond, two pi bonds for every chain
C≡C bond, four carbonyl pi bonds, and two P=O pi bonds, as displayed by
fragments `b` and `d`. -/
def pl1PiBondCount (d t : ℕ) : ℕ :=
  4 * d + 8 * t + 4 + 2

theorem pl1_pi_bond_count (d t : ℕ) :
    pl1PiBondCount d t = 4 * d + 8 * t + 6 := by
  simp [pl1PiBondCount]

def pl1SigmaPiBondCount (c h d t : ℕ) : ℕ :=
  pl1SigmaBondCount c h + pl1PiBondCount d t

theorem pl1_sigma_pi_bond_count (c h d t : ℕ) :
    pl1SigmaPiBondCount c h d t =
      4 * c + 4 * h + 4 * d + 8 * t + 47 := by
  rw [pl1SigmaPiBondCount, pl1_sigma_bond_count, pl1_pi_bond_count]
  omega

/-- Hydrogen count `C_c H_(2c-2d-4t) O_2` for an acyclic monocarboxylic acid
with `d` C=C and `t` C≡C bonds. -/
def acyclicFattyAcidHydrogenCount (c d t : ℕ) : ℕ :=
  2 * c - (2 * d + 4 * t)

theorem acyclic_fatty_acid_hydrogen_balance {c d t : ℕ}
    (h : 2 * d + 4 * t ≤ 2 * c) :
    acyclicFattyAcidHydrogenCount c d t + (2 * d + 4 * t) = 2 * c := by
  simp [acyclicFattyAcidHydrogenCount]
  omega

/-- Number of connected chain fragments after every carbon-carbon multiple
bond in an acyclic fatty acid is cleaved by ozonolysis. -/
def ozonolysisFragmentCount (d t : ℕ) : ℕ := d + t + 1

/-! ## Printed observations -/

/-- Q5.3 states that three different products are formed in equimolar amounts. -/
def observedOzonolysisProductCount : ℕ := 3

/-- Q5.3 states that neutral PL1 contains 255 sigma and pi bonds in total. -/
def observedPL1SigmaPiBondCount : ℕ := 255

/-- The source observations applied to a chemically admissible candidate.
The first conjunct is the natural-domain condition needed by the hydrogen
count. -/
def SatisfiesProblemData (c d t : ℕ) : Prop :=
  2 * d + 4 * t ≤ 2 * c ∧
  ozonolysisFragmentCount d t = observedOzonolysisProductCount ∧
  pl1SigmaPiBondCount c (acyclicFattyAcidHydrogenCount c d t) d t =
    observedPL1SigmaPiBondCount

/-- Ozonolysis shows that there are two cleaved carbon-carbon multiple bonds
in total. -/
theorem ozonolysis_forces_two_cleavages {d t : ℕ}
    (h : ozonolysisFragmentCount d t = observedOzonolysisProductCount) :
    d + t = 2 := by
  simp [ozonolysisFragmentCount, observedOzonolysisProductCount] at h
  omega

/-- The observations uniquely determine 18 carbon atoms, two C=C bonds, no
C≡C bonds, and 32 hydrogen atoms in the fatty acid. -/
theorem determine_fatty_acid_counts {c d t : ℕ}
    (h : SatisfiesProblemData c d t) :
    c = 18 ∧ d = 2 ∧ t = 0 ∧ acyclicFattyAcidHydrogenCount c d t = 32 := by
  rcases h with ⟨hdomain, hozonolysis, hbonds⟩
  have hcleavages : d + t = 2 := ozonolysis_forces_two_cleavages hozonolysis
  rw [pl1_sigma_pi_bond_count] at hbonds
  simp [observedPL1SigmaPiBondCount, acyclicFattyAcidHydrogenCount] at hbonds ⊢
  omega

/-- The requested exact molecular formula, C18H32O2. -/
def fattyAcidAnswer : MolecularFormula := ⟨18, 32, 2, 0⟩

/-- Final requested output: every fatty acid satisfying the problem data has
molecular formula C18H32O2. -/
theorem fatty_acid_formula {c d t : ℕ} (h : SatisfiesProblemData c d t) :
    fattyAcidFormula c (acyclicFattyAcidHydrogenCount c d t) = fattyAcidAnswer := by
  obtain ⟨hc, hd, ht, hh⟩ := determine_fatty_acid_counts h
  subst c
  subst d
  subst t
  rfl

/-- A concrete witness, showing that the derived answer actually satisfies
both observations rather than merely being forced by them. -/
theorem fatty_acid_answer_satisfies_data : SatisfiesProblemData 18 2 0 := by
  norm_num [SatisfiesProblemData, ozonolysisFragmentCount,
    observedOzonolysisProductCount, pl1SigmaPiBondCount,
    pl1SigmaBondCount, MolecularFormula.atomCount, pl1Formula,
    pl1PiBondCount, acyclicFattyAcidHydrogenCount,
    observedPL1SigmaPiBondCount]

end IChO2026Problems.T5A3

#print axioms IChO2026Problems.T5A3.determine_fatty_acid_counts
#print axioms IChO2026Problems.T5A3.fatty_acid_formula
#print axioms IChO2026Problems.T5A3.fatty_acid_answer_satisfies_data
