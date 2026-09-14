import IChO2026Chem.Reporting

/-!
# IChO 2026, problem 7, part 7

This file formalizes the identification requested in part 7.7.  The proposed
formulae occur only as witnesses in the conclusions below.  They are checked
against the printed nitrogen mass fractions, nitride charge balance, the
structured formula `Q_α R_β S₂ T[Si₁₂N₂₄]`, and a complete atom ledger for the
quantitative single-product synthesis.

The finite element type is the outcome-decisive atom ledger of the proposed
synthesis, not an exhaustive domain used to choose a candidate.
-/

namespace IChO2026Problems
namespace T7A7

open scoped BigOperators
open IChO2026Chem.Reporting

noncomputable section

/-- Elements occurring in the outcome-decisive atom ledger for the proposed
quantitative formation of compound 10. -/
inductive LedgerElement
  | lanthanum
  | calcium
  | silicon
  | nitrogen
  | oxygen
  deriving DecidableEq, Fintype, Repr

/-- Expands a sum over the outcome-decisive ledger. -/
private theorem sum_ledgerElement
    {M : Type*} [AddCommMonoid M] (f : LedgerElement → M) :
    ∑ e, f e =
      f .lanthanum + f .calcium + f .silicon + f .nitrogen + f .oxygen := by
  classical
  rw [show (Finset.univ : Finset LedgerElement) =
      {.lanthanum, .calcium, .silicon, .nitrogen, .oxygen} by decide]
  simp [add_left_comm, add_comm]

/-- A molecular or empirical formula, represented by its atom counts in the
outcome-decisive ledger. -/
abbrev Formula := LedgerElement → ℕ

namespace Formula

/-- Constructor whose arguments are ordered La, Ca, Si, N, O. -/
def ofCounts (la ca si n o : ℕ) : Formula
  | .lanthanum => la
  | .calcium => ca
  | .silicon => si
  | .nitrogen => n
  | .oxygen => o

/-- Formula of one atom. -/
def singleton (a : LedgerElement) : Formula :=
  fun e => if e = a then 1 else 0

/-- Pointwise sum of formulae. -/
def add (f g : Formula) : Formula :=
  fun e => f e + g e

/-- `k` copies of a formula. -/
def scale (k : ℕ) (f : Formula) : Formula :=
  fun e => k * f e

/-- Total number of atoms in one formula unit. -/
def totalAtoms (f : Formula) : ℕ :=
  ∑ e, f e

/-- GCD of all five displayed atom counts. -/
def contentGCD (f : Formula) : ℕ :=
  Nat.gcd (f .lanthanum)
    (Nat.gcd (f .calcium)
      (Nat.gcd (f .silicon) (Nat.gcd (f .nitrogen) (f .oxygen))))

/-- Arithmetic meaning of an empirical (minimal integral) formula. -/
def IsEmpirical (f : Formula) : Prop :=
  0 < totalAtoms f ∧ contentGCD f = 1

/-- Molar mass computed from an atomic-weight table. -/
def molarMass (weights : LedgerElement → ℝ) (f : Formula) : ℝ :=
  ∑ e, (f e : ℝ) * weights e

/-- Nitrogen mass divided by total formula mass. -/
def nitrogenMassFraction (weights : LedgerElement → ℝ) (f : Formula) : ℝ :=
  (f .nitrogen : ℝ) * weights .nitrogen / molarMass weights f

end Formula

/-! ## Pinned conventional atomic weights

These are the nominal values returned by Archon's version-pinned offline CIAAW
2024 table.  Only these five entries are used in this target.
-/

def atomicWeight : LedgerElement → ℝ
  | .nitrogen => 14007 / 1000
  | .lanthanum => 13891 / 100
  | .calcium => 40078 / 1000
  | .silicon => 28085 / 1000
  | .oxygen => 15999 / 1000

/-- A binary nitride candidate, including the positive constituent's formal
oxidation number used in the charge ledger. -/
structure BinaryNitrideCandidate where
  positiveElement : LedgerElement
  positiveOxidationNumber : ℤ
  formula : Formula

/-- Source-driven check for a proposed binary nitride.  The last conjunct uses
the printed percentage as a measurement cell: `0.01 %` corresponds to the
fraction quantum `0.0001`. -/
def BinaryNitrideSpec
    (shownFraction quantum : ℝ) (c : BinaryNitrideCandidate) : Prop :=
  c.positiveElement ≠ .nitrogen ∧
  0 < c.positiveOxidationNumber ∧
  0 < c.formula c.positiveElement ∧
  0 < c.formula .nitrogen ∧
  (∀ e, 0 < c.formula e ↔
    e = c.positiveElement ∨ e = .nitrogen) ∧
  c.positiveOxidationNumber * Int.ofNat (c.formula c.positiveElement) +
      (-3 : ℤ) * Int.ofNat (c.formula .nitrogen) = 0 ∧
  Formula.IsEmpirical c.formula ∧
  ConsistentMeasurement
    (Formula.nitrogenMassFraction atomicWeight c.formula)
    shownFraction quantum

/-- Candidate for nitride 7: LaN. -/
def nitride7Candidate : BinaryNitrideCandidate where
  positiveElement := .lanthanum
  positiveOxidationNumber := 3
  formula := Formula.ofCounts 1 0 0 1 0

/-- Candidate for nitride 8: Ca₃N₂. -/
def nitride8Candidate : BinaryNitrideCandidate where
  positiveElement := .calcium
  positiveOxidationNumber := 2
  formula := Formula.ofCounts 0 3 0 2 0

/-- Candidate for nitride 9: Si₃N₄. -/
def nitride9Candidate : BinaryNitrideCandidate where
  positiveElement := .silicon
  positiveOxidationNumber := 4
  formula := Formula.ofCounts 0 0 3 4 0

/-- The common source-derived mass-fraction quantum: `0.01 % = 0.0001`. -/
def nitrogenFractionQuantum : ℝ := 1 / 10000

def shownNitrogenFraction7 : ℝ := 916 / 10000
def shownNitrogenFraction8 : ℝ := 1890 / 10000
def shownNitrogenFraction9 : ℝ := 3994 / 10000

/-! ## Structured anions and compound 10 -/

structure CationComponent where
  element : LedgerElement
  charge : ℤ

structure MonoatomicAnion where
  atom : LedgerElement
  charge : ℤ

namespace MonoatomicAnion

def formula (s : MonoatomicAnion) : Formula :=
  Formula.singleton s.atom

end MonoatomicAnion

/-- A tetrahedral anion has one central atom and exactly four ligand vertices.
This retains the structural information that an unstructured formula would
erase. -/
structure TetrahedralAnion where
  central : LedgerElement
  ligand : Fin 4 → LedgerElement
  charge : ℤ

namespace TetrahedralAnion

def formula (t : TetrahedralAnion) : Formula :=
  fun e => (if e = t.central then 1 else 0) +
    ∑ i : Fin 4, if e = t.ligand i then 1 else 0

end TetrahedralAnion

structure ChargedFormula where
  formula : Formula
  charge : ℤ

/-- Highest oxidation states needed for the two proposed metal cations.  This
is a candidate audit table, not an exhaustive periodic-table search domain. -/
def ledgerHighestMetalOxidationState : LedgerElement → Option ℤ
  | .lanthanum => some 3
  | .calcium => some 2
  | _ => none

/-- Ordinary oxidation-number bookkeeping for the five atoms in the claimed
product ledger. -/
def oxidationContribution : LedgerElement → ℤ
  | .lanthanum => 3
  | .calcium => 2
  | .silicon => 4
  | .nitrogen => -3
  | .oxygen => -2

namespace Formula

def formalCharge (f : Formula) : ℤ :=
  ∑ e, Int.ofNat (f e) * oxidationContribution e

end Formula

/-- A value of the source template `Q_α R_β S₂ T[Si₁₂N₂₄]`. -/
structure StructuredCompound where
  q : CationComponent
  alpha : ℕ
  r : CationComponent
  beta : ℕ
  s : MonoatomicAnion
  t : TetrahedralAnion
  framework : ChargedFormula

namespace StructuredCompound

/-- Full ungrouped empirical formula represented by a structured unit. -/
def assembledFormula (u : StructuredCompound) : Formula :=
  Formula.add (Formula.scale u.alpha (Formula.singleton u.q.element))
    (Formula.add (Formula.scale u.beta (Formula.singleton u.r.element))
      (Formula.add (Formula.scale 2 u.s.formula)
        (Formula.add u.t.formula u.framework.formula)))

/-- Full formal charge, including the stipulated multiplicity two of `S`. -/
def netCharge (u : StructuredCompound) : ℤ :=
  Int.ofNat u.alpha * u.q.charge +
    Int.ofNat u.beta * u.r.charge +
    2 * u.s.charge + u.t.charge + u.framework.charge

end StructuredCompound

/-- Candidate `S = O²⁻`. -/
def sCandidate : MonoatomicAnion where
  atom := .oxygen
  charge := -2

/-- Candidate `T = [SiO₃N]⁵⁻`; the index type enforces four ligand vertices. -/
def tCandidate : TetrahedralAnion where
  central := .silicon
  ligand := fun i => if i.val < 3 then .oxygen else .nitrogen
  charge := -5

/-- The stipulated `[Si₁₂N₂₄]` framework with its oxidation-number charge. -/
def frameworkCandidate : ChargedFormula where
  formula := Formula.ofCounts 0 0 12 24 0
  charge := -24

/-- Candidate structured formula
`La₅Ca₉O₂[SiO₃N][Si₁₂N₂₄]`. -/
def compound10Candidate : StructuredCompound where
  q := ⟨.lanthanum, 3⟩
  alpha := 5
  r := ⟨.calcium, 2⟩
  beta := 9
  s := sCandidate
  t := tCandidate
  framework := frameworkCandidate

/-- Source-facing specification of the structured unit. -/
def StructuredCompoundSpec (u : StructuredCompound) : Prop :=
  0 < u.alpha ∧
  0 < u.beta ∧
  u.q.element ≠ u.r.element ∧
  ledgerHighestMetalOxidationState u.q.element = some u.q.charge ∧
  ledgerHighestMetalOxidationState u.r.element = some u.r.charge ∧
  u.s.charge < 0 ∧
  u.s.charge = Formula.formalCharge u.s.formula ∧
  u.t.charge < 0 ∧
  u.t.charge = Formula.formalCharge u.t.formula ∧
  u.framework.formula = Formula.ofCounts 0 0 12 24 0 ∧
  u.framework.charge = Formula.formalCharge u.framework.formula ∧
  u.netCharge = 0 ∧
  Formula.IsEmpirical u.assembledFormula

/-! ## Quantitative single-product material stage -/

/-- The only input and output species admitted to the atom ledger for the
problem-stipulated quantitative single-product stage. -/
structure FormationCandidate where
  reagent7 : Formula
  reagent8 : Formula
  reagent9 : Formula
  silica : Formula
  product10 : Formula
  coeff7 : ℕ
  coeff8 : ℕ
  coeff9 : ℕ
  coeffSilica : ℕ
  coeffProduct : ℕ

namespace FormationCandidate

def inputAtomLedger (r : FormationCandidate) : Formula :=
  Formula.add (Formula.scale r.coeff7 r.reagent7)
    (Formula.add (Formula.scale r.coeff8 r.reagent8)
      (Formula.add (Formula.scale r.coeff9 r.reagent9)
        (Formula.scale r.coeffSilica r.silica)))

def outputAtomLedger (r : FormationCandidate) : Formula :=
  Formula.scale r.coeffProduct r.product10

def batchMass (coefficient : ℕ) (f : Formula) : ℝ :=
  (coefficient : ℝ) * Formula.molarMass atomicWeight f

/-- Reagent mass divided by the total mass of the silica reagent portion, as
specified by the printed ratio `7 : 8 : 9 : SiO₂`. -/
def relativeToSilica
    (coefficient : ℕ) (f : Formula) (r : FormationCandidate) : ℝ :=
  batchMass coefficient f / batchMass r.coeffSilica r.silica

end FormationCandidate

def silicaFormula : Formula := Formula.ofCounts 0 0 1 0 2
def ungroupedCompound10Formula : Formula := Formula.ofCounts 5 9 13 25 5

/-- Candidate whole-stage equation
`10 LaN + 6 Ca₃N₂ + 7 Si₃N₄ + 5 SiO₂ → 2 compound10`. -/
def formationCandidate : FormationCandidate where
  reagent7 := nitride7Candidate.formula
  reagent8 := nitride8Candidate.formula
  reagent9 := nitride9Candidate.formula
  silica := silicaFormula
  product10 := ungroupedCompound10Formula
  coeff7 := 10
  coeff8 := 6
  coeff9 := 7
  coeffSilica := 5
  coeffProduct := 2

/-- Complete specification of the quantitative material stage.  There is one
named product field and no anonymous or catch-all stream.  All displayed mass
ratios have quantum `0.01` and use the silica batch mass as denominator. -/
def QuantitativeSingleProductFormationSpec (r : FormationCandidate) : Prop :=
  0 < r.coeff7 ∧
  0 < r.coeff8 ∧
  0 < r.coeff9 ∧
  0 < r.coeffSilica ∧
  0 < r.coeffProduct ∧
  0 < FormationCandidate.batchMass r.coeffSilica r.silica ∧
  r.inputAtomLedger = r.outputAtomLedger ∧
  FormationCandidate.batchMass r.coeff7 r.reagent7 +
      FormationCandidate.batchMass r.coeff8 r.reagent8 +
      FormationCandidate.batchMass r.coeff9 r.reagent9 +
      FormationCandidate.batchMass r.coeffSilica r.silica =
    FormationCandidate.batchMass r.coeffProduct r.product10 ∧
  ConsistentMeasurement
    (FormationCandidate.relativeToSilica r.coeff7 r.reagent7 r)
    (509 / 100) (1 / 100) ∧
  ConsistentMeasurement
    (FormationCandidate.relativeToSilica r.coeff8 r.reagent8 r)
    (296 / 100) (1 / 100) ∧
  ConsistentMeasurement
    (FormationCandidate.relativeToSilica r.coeff9 r.reagent9 r)
    (327 / 100) (1 / 100) ∧
  ConsistentMeasurement
    (FormationCandidate.relativeToSilica r.coeffSilica r.silica r)
    1 (1 / 100)

/-! ## One semantic carrier for each requested output -/

/-- Requested output `formula_7`: LaN, audited against the source data. -/
def Formula7Output : Prop :=
  BinaryNitrideSpec shownNitrogenFraction7 nitrogenFractionQuantum
      nitride7Candidate ∧
  formationCandidate.reagent7 = nitride7Candidate.formula ∧
  QuantitativeSingleProductFormationSpec formationCandidate

/-- Requested output `formula_8`: Ca₃N₂, audited against the source data. -/
def Formula8Output : Prop :=
  BinaryNitrideSpec shownNitrogenFraction8 nitrogenFractionQuantum
      nitride8Candidate ∧
  formationCandidate.reagent8 = nitride8Candidate.formula ∧
  QuantitativeSingleProductFormationSpec formationCandidate

/-- Requested output `formula_9`: Si₃N₄, audited against the source data. -/
def Formula9Output : Prop :=
  BinaryNitrideSpec shownNitrogenFraction9 nitrogenFractionQuantum
      nitride9Candidate ∧
  formationCandidate.reagent9 = nitride9Candidate.formula ∧
  QuantitativeSingleProductFormationSpec formationCandidate

/-- Requested output `formula_10`: the grouped structured formula and its
ungrouped empirical composition. -/
def Formula10Output : Prop :=
  StructuredCompoundSpec compound10Candidate ∧
  compound10Candidate.assembledFormula = ungroupedCompound10Formula ∧
  formationCandidate.product10 = compound10Candidate.assembledFormula ∧
  QuantitativeSingleProductFormationSpec formationCandidate

/-- Requested output `formula_s`: `O²⁻`, integrated into compound 10. -/
def FormulaSOutput : Prop :=
  sCandidate.formula = Formula.ofCounts 0 0 0 0 1 ∧
  sCandidate.charge = -2 ∧
  compound10Candidate.s = sCandidate ∧
  StructuredCompoundSpec compound10Candidate ∧
  QuantitativeSingleProductFormationSpec formationCandidate

/-- Requested output `formula_t`: tetrahedral `[SiO₃N]⁵⁻`, integrated into
compound 10. -/
def FormulaTOutput : Prop :=
  tCandidate.formula = Formula.ofCounts 0 0 1 1 3 ∧
  tCandidate.charge = -5 ∧
  compound10Candidate.t = tCandidate ∧
  StructuredCompoundSpec compound10Candidate ∧
  QuantitativeSingleProductFormationSpec formationCandidate

theorem formula7_output : Formula7Output := by
  norm_num [Formula7Output, BinaryNitrideSpec, nitride7Candidate,
    nitrogenFractionQuantum, shownNitrogenFraction7,
    Formula.nitrogenMassFraction, Formula.molarMass, atomicWeight,
    Formula.IsEmpirical, Formula.totalAtoms, Formula.contentGCD,
    Formula.ofCounts, QuantitativeSingleProductFormationSpec,
    formationCandidate, FormationCandidate.inputAtomLedger,
    FormationCandidate.outputAtomLedger, FormationCandidate.batchMass,
    FormationCandidate.relativeToSilica, Formula.add, Formula.scale,
    nitride8Candidate, nitride9Candidate, silicaFormula,
    ungroupedCompound10Formula, ConsistentMeasurement, sum_ledgerElement]
  constructor
  · constructor
    · decide
    · intro e
      cases e <;> simp
  · funext e
    cases e <;> decide

theorem formula8_output : Formula8Output := by
  refine ⟨?_, rfl, formula7_output.2.2⟩
  norm_num [BinaryNitrideSpec, nitride8Candidate, nitrogenFractionQuantum,
    shownNitrogenFraction8, Formula.nitrogenMassFraction,
    Formula.molarMass, atomicWeight, Formula.IsEmpirical,
    Formula.totalAtoms, Formula.contentGCD, Formula.ofCounts,
    ConsistentMeasurement, sum_ledgerElement]
  constructor
  · decide
  · intro e
    cases e <;> simp

theorem formula9_output : Formula9Output := by
  refine ⟨?_, rfl, formula7_output.2.2⟩
  norm_num [BinaryNitrideSpec, nitride9Candidate, nitrogenFractionQuantum,
    shownNitrogenFraction9, Formula.nitrogenMassFraction,
    Formula.molarMass, atomicWeight, Formula.IsEmpirical,
    Formula.totalAtoms, Formula.contentGCD, Formula.ofCounts,
    ConsistentMeasurement, sum_ledgerElement]
  constructor
  · decide
  · intro e
    cases e <;> simp

theorem formula10_output : Formula10Output := by
  have hassembled :
      compound10Candidate.assembledFormula = ungroupedCompound10Formula := by
    funext e
    cases e <;> decide
  refine ⟨?_, hassembled, ?_, formula7_output.2.2⟩
  · norm_num [StructuredCompoundSpec, compound10Candidate, sCandidate,
      tCandidate, frameworkCandidate, ledgerHighestMetalOxidationState,
      MonoatomicAnion.formula, TetrahedralAnion.formula,
      StructuredCompound.netCharge, StructuredCompound.assembledFormula,
      Formula.formalCharge, Formula.IsEmpirical, Formula.totalAtoms,
      Formula.contentGCD, Formula.singleton, Formula.ofCounts, Formula.add,
      Formula.scale, oxidationContribution, sum_ledgerElement,
      Fin.sum_univ_succ]
    decide
  · simpa [formationCandidate] using hassembled.symm

theorem formulaS_output : FormulaSOutput := by
  refine ⟨?_, rfl, rfl, formula10_output.1, formula7_output.2.2⟩
  funext e
  cases e <;> decide

theorem formulaT_output : FormulaTOutput := by
  refine ⟨?_, rfl, rfl, formula10_output.1, formula7_output.2.2⟩
  funext e
  cases e <;> decide

/-- The exact symbolic raw result covers all six source-requested outputs. -/
def RawResult : Prop :=
  Formula7Output ∧ Formula8Output ∧ Formula9Output ∧
    Formula10Output ∧ FormulaSOutput ∧ FormulaTOutput

/-- Exact symbolic reporting performs no numerical rounding. -/
def ReportedResult : Prop := RawResult

theorem raw_result : RawResult := by
  exact ⟨formula7_output, formula8_output, formula9_output,
    formula10_output, formulaS_output, formulaT_output⟩

theorem reported_result : ReportedResult := by
  exact raw_result

/-! ## Inline treatment of the listed previous-part prerequisites

Neither previous part is used as a premise of the 7.7 result.  These separate
targets record the problem-side derivations requested by the controller and
prevent an unbound sibling answer from entering the assumptions above.
-/

structure DinitrogenComplexTopology where
  molybdenumCentres : ℕ
  terminalN2Ligands : ℕ
  bridgingN2Ligands : ℕ

def previousPart5Topology : DinitrogenComplexTopology where
  molybdenumCentres := 2
  terminalN2Ligands := 4
  bridgingN2Ligands := 1

/-- Ideal-gas uptake divided by moles of precursor 4, using only values printed
in part 7.5 and the conventional gas constant `8.314 J mol⁻¹ K⁻¹`. -/
def previousPart5N2PerPrecursor : ℝ :=
  ((100000 : ℝ) * (9497 / 100000000 : ℝ) /
      ((8314 / 1000 : ℝ) * (27315 / 100 : ℝ))) /
    ((1 : ℝ) / (597824 / 1000 : ℝ))

def PreviousPart5Derived : Prop :=
  |previousPart5N2PerPrecursor - 5 / 2| < 1 / 1000 ∧
  previousPart5Topology.molybdenumCentres = 2 ∧
  previousPart5Topology.terminalN2Ligands =
    2 * previousPart5Topology.molybdenumCentres ∧
  previousPart5Topology.bridgingN2Ligands = 1 ∧
  2 * (previousPart5Topology.terminalN2Ligands +
      previousPart5Topology.bridgingN2Ligands) =
    5 * previousPart5Topology.molybdenumCentres

theorem previousPart5_derived : PreviousPart5Derived := by
  norm_num [PreviousPart5Derived, previousPart5N2PerPrecursor,
    previousPart5Topology, abs_lt]

inductive RedAdCombination
  | A | B | C | D
  deriving DecidableEq, Repr

def reductantPotential : RedAdCombination → ℝ
  | .A => -9 / 100
  | .B => -110 / 100
  | .C => -110 / 100
  | .D => -110 / 100

def additivePka : RedAdCombination → ℝ
  | .A => 137 / 10
  | .B => 150 / 10
  | .C => 137 / 10
  | .D => 106 / 10

/-- Bounded ordering model extracted from the calibration panel: a reductant
more negative than the zero-yield `-0.88 V` reference is electron-capable;
within that class, the triflate examples are ordered by additive pKa. -/
def calibrationPredictsHigherYield
    (x y : RedAdCombination) : Prop :=
  (reductantPotential x < -88 / 100 ∧ ¬ reductantPotential y < -88 / 100) ∨
  (reductantPotential x < -88 / 100 ∧ reductantPotential y < -88 / 100 ∧
    additivePka y < additivePka x)

def PreviousPart6Derived : Prop :=
  calibrationPredictsHigherYield .B .C ∧
  calibrationPredictsHigherYield .C .D ∧
  calibrationPredictsHigherYield .D .A

theorem previousPart6_derived : PreviousPart6Derived := by
  norm_num [PreviousPart6Derived, calibrationPredictsHigherYield,
    reductantPotential, additivePka]

end
end T7A7
end IChO2026Problems
