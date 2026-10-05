import IChO2026Chem.Reporting

/-!
# IChO 2026, theory problem 3.1

This file formalizes both requested outputs for COF-1.

## Source boundary

The problem diagram depicts COF-1 as a honeycomb network made from

* para-phenylene linkers, each with composition `C6H4` and two ends, and
* boroxine rings, each with composition `B3O3` and three phenyl attachment
  sites.

Those facts are encoded in `ProblemData` below.  The first is the ordinary
line-angle interpretation of the doubly substituted benzene rings drawn in
the figure; the second is both stated in the prose ("boroxine rings") and
visible as the alternating six-membered B/O rings.  The four atomic weights
are copied exactly from the periodic table supplied on PDF page 5.

Everything after `ProblemData` is derived.  In particular, the empirical
formula is not inserted as a premise: it follows from attachment balance and
normalization of the resulting atom counts.
-/

namespace IChO2026Problems.T3A1

open IChO2026Chem.Reporting

/-- Atom counts, restricted to the four elements present in COF-1. -/
@[ext] structure Formula where
  carbon : ℕ
  hydrogen : ℕ
  boron : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

namespace Formula

/-- Componentwise addition of atom counts. -/
def add (a b : Formula) : Formula where
  carbon := a.carbon + b.carbon
  hydrogen := a.hydrogen + b.hydrogen
  boron := a.boron + b.boron
  oxygen := a.oxygen + b.oxygen

/-- Componentwise multiplication of atom counts by a natural number. -/
def scale (n : ℕ) (a : Formula) : Formula where
  carbon := n * a.carbon
  hydrogen := n * a.hydrogen
  boron := n * a.boron
  oxygen := n * a.oxygen

/-- Greatest common divisor of all four subscripts. -/
def content (a : Formula) : ℕ :=
  Nat.gcd a.carbon (Nat.gcd a.hydrogen (Nat.gcd a.boron a.oxygen))

/-- Divide every subscript by their common content. -/
def normalize (a : Formula) : Formula where
  carbon := a.carbon / a.content
  hydrogen := a.hydrogen / a.content
  boron := a.boron / a.content
  oxygen := a.oxygen / a.content

end Formula

/-- Atomic weights needed for this question, in g mol⁻¹. -/
structure AtomicWeights where
  carbon : ℝ
  hydrogen : ℝ
  boron : ℝ
  oxygen : ℝ

namespace ProblemData

/-- A doubly substituted benzene unit read from the COF-1 diagram. -/
def phenylene : Formula := ⟨6, 4, 0, 0⟩

/-- An alternating B/O boroxine ring read from the COF-1 diagram. -/
def boroxineRing : Formula := ⟨0, 0, 3, 3⟩

/-- Atomic weights printed in the problem's periodic table:
`C = 12.01`, `H = 1.008`, `B = 10.81`, and `O = 16.00`. -/
noncomputable def atomicWeights : AtomicWeights where
  carbon := 1201 / 100
  hydrogen := 126 / 125
  boron := 1081 / 100
  oxygen := 16

end ProblemData

/-- Formula obtained from a cell containing `linkers` phenylene linkers and
`rings` boroxine rings. -/
def formulaFromPieces (linkers rings : ℕ) : Formula :=
  Formula.add (Formula.scale linkers ProblemData.phenylene)
    (Formula.scale rings ProblemData.boroxineRing)

/-- Closing every bond end in a periodic COF-1 cell forces three phenylene
linkers for every two boroxine rings.  This is the number-theoretic content of
`2 * linkers = 3 * rings`: two ends per linker and three sites per ring. -/
theorem balanced_cell_multiplicities {linkers rings : ℕ}
    (attachmentBalance : 2 * linkers = 3 * rings) :
    ∃ k : ℕ, linkers = 3 * k ∧ rings = 2 * k := by
  have three_dvd_twice_linkers : 3 ∣ 2 * linkers :=
    ⟨rings, attachmentBalance⟩
  have three_dvd_linkers : 3 ∣ linkers :=
    (show Nat.Coprime 3 2 by norm_num).dvd_of_dvd_mul_left
      three_dvd_twice_linkers
  obtain ⟨k, linkers_eq⟩ := three_dvd_linkers
  refine ⟨k, linkers_eq, ?_⟩
  omega

/-- The primitive positive topology cell: three linkers and two rings. -/
def cof1TopologyCell : Formula := formulaFromPieces 3 2

/-- Direct atom count in that topology cell. -/
theorem cof1_topology_cell_atom_count :
    cof1TopologyCell = ⟨18, 12, 6, 6⟩ := by
  rfl

/-- Candidate primitive atom counts corresponding to the chemical formula
`C3H2BO`. -/
def cof1EmpiricalFormula : Formula := ⟨3, 2, 1, 1⟩

/-- Every attachment-balanced cell has atom counts equal to a multiple of six
copies of `C3H2BO`; hence the ratio does not depend on the chosen cell. -/
theorem balanced_cell_formula {linkers rings : ℕ}
    (attachmentBalance : 2 * linkers = 3 * rings) :
    ∃ k : ℕ,
      formulaFromPieces linkers rings =
        Formula.scale (6 * k) cof1EmpiricalFormula := by
  obtain ⟨k, rfl, rfl⟩ := balanced_cell_multiplicities attachmentBalance
  refine ⟨k, ?_⟩
  ext <;> simp [formulaFromPieces, Formula.add, Formula.scale,
    ProblemData.phenylene, ProblemData.boroxineRing, cof1EmpiricalFormula] <;>
    omega

/-- The cell contains exactly six copies of the proposed empirical unit. -/
theorem cof1_topology_cell_is_six_empirical_units :
    cof1TopologyCell = Formula.scale 6 cof1EmpiricalFormula := by
  rfl

/-- The proposed empirical formula is primitive: its four subscripts have
greatest common divisor one. -/
theorem cof1_empirical_formula_is_primitive :
    Formula.content cof1EmpiricalFormula = 1 := by
  norm_num [Formula.content, cof1EmpiricalFormula]

/-- **Requested formula output.** Normalizing the atom count obtained from the
COF-1 topology gives `C3H2BO`. -/
theorem cof1_empirical_formula :
    Formula.normalize cof1TopologyCell = cof1EmpiricalFormula := by
  norm_num [Formula.normalize, Formula.content, cof1TopologyCell,
    formulaFromPieces, Formula.add, Formula.scale, ProblemData.phenylene,
    ProblemData.boroxineRing, cof1EmpiricalFormula]

/-- Formula mass computed from exact printed atomic weights. -/
def formulaMass (weights : AtomicWeights) (formula : Formula) : ℝ :=
  formula.carbon * weights.carbon +
  formula.hydrogen * weights.hydrogen +
  formula.boron * weights.boron +
  formula.oxygen * weights.oxygen

/-- Carbon's mass contribution to a formula. -/
def carbonMass (weights : AtomicWeights) (formula : Formula) : ℝ :=
  formula.carbon * weights.carbon

/-- Unrounded carbon mass percentage. -/
noncomputable def carbonMassPercent (weights : AtomicWeights) (formula : Formula) : ℝ :=
  100 * carbonMass weights formula / formulaMass weights formula

/-- `C3H2BO` has formula mass 64.856 g mol⁻¹ with the supplied weights. -/
theorem cof1_formula_mass :
    formulaMass ProblemData.atomicWeights cof1EmpiricalFormula = 8107 / 125 := by
  norm_num [formulaMass, ProblemData.atomicWeights, cof1EmpiricalFormula]

/-- The carbon contribution is 36.03 g mol⁻¹. -/
theorem cof1_carbon_mass :
    carbonMass ProblemData.atomicWeights cof1EmpiricalFormula = 3603 / 100 := by
  norm_num [carbonMass, ProblemData.atomicWeights, cof1EmpiricalFormula]

/-- Exact, unrounded carbon percentage, kept separate from the display value. -/
theorem cof1_carbon_mass_percent_exact :
    carbonMassPercent ProblemData.atomicWeights cof1EmpiricalFormula =
      450375 / 8107 := by
  norm_num [carbonMassPercent, carbonMass, formulaMass,
    ProblemData.atomicWeights, cof1EmpiricalFormula]

/-- The submitted numerical answer: raw exact value, displayed value `55.55`,
and the `0.01` quantum required by "to two decimal places". -/
noncomputable def cof1CarbonSubmission : NumericSubmission where
  rawValue := carbonMassPercent ProblemData.atomicWeights cof1EmpiricalFormula
  reportedValue := 5555 / 100
  reportingQuantum := 1 / 100

/-- **Requested numerical output.** The exact percentage lies in the unique
rounding interval for `55.55%` at quantum `0.01`; thus the stated value obeys
the problem's two-decimal-place instruction. -/
theorem cof1_carbon_mass_percent_reported :
    ValidNumericSubmission
      (carbonMassPercent ProblemData.atomicWeights cof1EmpiricalFormula)
      cof1CarbonSubmission := by
  constructor
  · rfl
  · rw [show cof1CarbonSubmission.rawValue =
        carbonMassPercent ProblemData.atomicWeights cof1EmpiricalFormula by rfl]
    rw [cof1_carbon_mass_percent_exact]
    refine ⟨by norm_num [cof1CarbonSubmission], ?_, ?_⟩
    · refine ⟨5555, ?_⟩
      norm_num [cof1CarbonSubmission]
    · norm_num [cof1CarbonSubmission]

/-- The requested display value appears explicitly here: the raw percentage
rounds to `5555 / 100 = 55.55` at a two-decimal quantum. -/
theorem cof1_carbon_mass_percent_two_decimal_places :
    ReportsAtQuantum
      (carbonMassPercent ProblemData.atomicWeights cof1EmpiricalFormula)
      (5555 / 100) (1 / 100) := by
  have valid := cof1_carbon_mass_percent_reported
  unfold ValidNumericSubmission at valid
  simpa [cof1CarbonSubmission] using valid.2

/-- Both requested outputs, with all atom subscripts and numerical values
shown explicitly in the theorem statement. -/
theorem icho_2026_t3_a1 :
    Formula.normalize cof1TopologyCell = ⟨3, 2, 1, 1⟩ ∧
    carbonMassPercent ProblemData.atomicWeights cof1EmpiricalFormula =
      450375 / 8107 ∧
    ReportsAtQuantum
      (carbonMassPercent ProblemData.atomicWeights cof1EmpiricalFormula)
      (5555 / 100) (1 / 100) := by
  refine ⟨?_, cof1_carbon_mass_percent_exact,
    cof1_carbon_mass_percent_two_decimal_places⟩
  simpa [cof1EmpiricalFormula] using cof1_empirical_formula

#print axioms cof1_empirical_formula
#print axioms cof1_carbon_mass_percent_reported
#print axioms cof1_carbon_mass_percent_two_decimal_places
#print axioms icho_2026_t3_a1

end IChO2026Problems.T3A1
