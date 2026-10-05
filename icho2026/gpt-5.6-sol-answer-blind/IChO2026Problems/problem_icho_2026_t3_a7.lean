import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, problem T3-A7

This file formalizes the two requested numerical outputs without using an
answer as a hypothesis.  The displayed experimental values are kept as exact
central values, while `sourceMeasurementBounds` separately records the
half-last-place measurement cells fixed by the source report.

The molecular formula needed for the pore count is reconstructed from the two
depicted building blocks, the three condensations forming COF-8, and the three
hydroxylamine additions forming COF-9.  The six vertices of one displayed
honeycomb face consist of three E1 and three D2 vertices; each trivalent vertex
is shared by three pores, hence one effective E1 and one effective D2 unit per
pore.
-/

namespace IChO2026Problems.T3A7

noncomputable section

/-! ## Chemical inventories and source-first image accounting -/

/-- Element counts used by this target.  Integer counts make subtraction of
condensation leaving groups explicit; nonnegativity is asserted after the
assembly has been recombined. -/
structure ElementInventory where
  carbon : ℤ
  hydrogen : ℤ
  nitrogen : ℤ
  oxygen : ℤ
  uranium : ℤ
deriving DecidableEq, Repr

namespace ElementInventory

def zero : ElementInventory := ⟨0, 0, 0, 0, 0⟩

def add (a b : ElementInventory) : ElementInventory :=
  ⟨a.carbon + b.carbon,
   a.hydrogen + b.hydrogen,
   a.nitrogen + b.nitrogen,
   a.oxygen + b.oxygen,
   a.uranium + b.uranium⟩

def sub (a b : ElementInventory) : ElementInventory :=
  ⟨a.carbon - b.carbon,
   a.hydrogen - b.hydrogen,
   a.nitrogen - b.nitrogen,
   a.oxygen - b.oxygen,
   a.uranium - b.uranium⟩

def scale (k : ℤ) (a : ElementInventory) : ElementInventory :=
  ⟨k * a.carbon, k * a.hydrogen, k * a.nitrogen,
   k * a.oxygen, k * a.uranium⟩

def Nonnegative (a : ElementInventory) : Prop :=
  0 ≤ a.carbon ∧ 0 ≤ a.hydrogen ∧ 0 ≤ a.nitrogen ∧
  0 ≤ a.oxygen ∧ 0 ≤ a.uranium

end ElementInventory

inductive Phase where
  | solid
  | aqueous
  | unspecified
deriving DecidableEq, Repr

structure ChemicalSpecies where
  name : String
  atoms : ElementInventory
  charge : ℤ
  phase : Phase
deriving DecidableEq, Repr

inductive ComponentRole where
  | core
  | repeatUnit
  | linker
  | substituent
  | terminalGroup
  | guest
  | adduct
  | leavingGroup
  | productFragment
deriving DecidableEq, Repr

/-- A positive-multiplicity entry in the image-derived assembly ledger. -/
structure ComponentLedgerEntry where
  sourceLabel : String
  atoms : ElementInventory
  multiplicity : ℕ
  role : ComponentRole
deriving DecidableEq, Repr

/-- The E1 arene core after its three hydrogens have been replaced by arms. -/
def e1AreneCore : ElementInventory := ⟨6, 3, 0, 0, 0⟩

/-- One cyanomethyl arm, `-CH₂-CN`, on the depicted E1 monomer. -/
def cyanomethylArm : ElementInventory := ⟨2, 2, 1, 0, 0⟩

/-- E1 is `C₆H₃ + 3(C₂H₂N) = C₁₂H₉N₃`. -/
def e1Monomer : ElementInventory :=
  ElementInventory.add e1AreneCore (ElementInventory.scale 3 cyanomethylArm)

/-- The central 1,3,5-triazine ring of D2. -/
def d2TriazineCore : ElementInventory := ⟨3, 0, 3, 0, 0⟩

/-- One para-formylphenyl arm of D2. -/
def paraFormylphenylArm : ElementInventory := ⟨7, 5, 0, 1, 0⟩

/-- D2 is `C₃N₃ + 3(C₇H₅O) = C₂₄H₁₅N₃O₃`. -/
def d2Monomer : ElementInventory :=
  ElementInventory.add d2TriazineCore
    (ElementInventory.scale 3 paraFormylphenylArm)

def water : ElementInventory := ⟨0, 2, 0, 1, 0⟩

/-- Hydroxylamine, the reagent printed above the COF-8 → COF-9 arrow. -/
def hydroxylamine : ElementInventory := ⟨0, 3, 1, 1, 0⟩

/-- One effective pore formula of COF-8: E1 + D2 minus three waters. -/
def cof8PoreAssembly : ElementInventory :=
  ElementInventory.sub (ElementInventory.add e1Monomer d2Monomer)
    (ElementInventory.scale 3 water)

/-- One effective pore formula of COF-9 after addition of three NH₂OH units. -/
def cof9PoreAssembly : ElementInventory :=
  ElementInventory.add cof8PoreAssembly
    (ElementInventory.scale 3 hydroxylamine)

/-- Component ledger for the complete effective pore assembly.  Every listed
multiplicity is positive; `leavingGroup` entries are subtracted in the full
assembly expression, while `adduct` entries are added. -/
def cof9PoreComponentLedger : List ComponentLedgerEntry :=
  [ ⟨"effective E1 pore share", e1Monomer, 1, .repeatUnit⟩,
    ⟨"effective D2 pore share", d2Monomer, 1, .repeatUnit⟩,
    ⟨"water from three C=C-forming condensations", water, 3, .leavingGroup⟩,
    ⟨"hydroxylamine added at three nitriles", hydroxylamine, 3, .adduct⟩ ]

/-- Source-first topology recount for one complete honeycomb face in the two
bound images.  The six third arms are continuation bonds into adjacent pores,
not terminal caps. -/
structure HoneycombFaceLedger where
  buildingBlockTypes : ℕ
  e1Vertices : ℕ
  d2Vertices : ℕ
  degreeOfEachVertex : ℕ
  poresSharingEachVertex : ℕ
  outgoingNetworkBonds : ℕ
deriving DecidableEq, Repr

def cof9HoneycombFaceLedger : HoneycombFaceLedger :=
  ⟨2, 3, 3, 3, 3, 6⟩

def effectiveE1UnitsPerPore : ℝ :=
  cof9HoneycombFaceLedger.e1Vertices /
    cof9HoneycombFaceLedger.poresSharingEachVertex

def effectiveD2UnitsPerPore : ℝ :=
  cof9HoneycombFaceLedger.d2Vertices /
    cof9HoneycombFaceLedger.poresSharingEachVertex

/-- The complete image-to-formula bridge used by the pore calculation. -/
def Cof9PoreAssemblySpec : Prop :=
  cof9HoneycombFaceLedger.buildingBlockTypes = 2 ∧
  cof9HoneycombFaceLedger.degreeOfEachVertex = 3 ∧
  cof9HoneycombFaceLedger.outgoingNetworkBonds = 6 ∧
  effectiveE1UnitsPerPore = 1 ∧
  effectiveD2UnitsPerPore = 1 ∧
  cof9PoreAssembly = ⟨36, 27, 9, 3, 0⟩ ∧
  ElementInventory.Nonnegative cof9PoreAssembly

theorem cof9PoreAssembly_spec : Cof9PoreAssemblySpec := by
  norm_num [Cof9PoreAssemblySpec, effectiveE1UnitsPerPore,
    effectiveD2UnitsPerPore, cof9HoneycombFaceLedger, cof9PoreAssembly,
    cof8PoreAssembly, e1Monomer, e1AreneCore, cyanomethylArm, d2Monomer,
    d2TriazineCore, paraFormylphenylArm, water, hydroxylamine,
    ElementInventory.add, ElementInventory.sub, ElementInventory.scale,
    ElementInventory.Nonnegative]

theorem cof9PoreComponentLedger_positive :
    ∀ entry ∈ cof9PoreComponentLedger, 0 < entry.multiplicity := by
  intro entry hentry
  simp [cof9PoreComponentLedger] at hentry
  rcases hentry with rfl | rfl | rfl | rfl <;> norm_num

/-! ## Quantitative material-stage ledgers -/

inductive TransformationUse where
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
deriving DecidableEq, Repr

structure MaterialTerm where
  sourceLabel : String
  atoms : ElementInventory
  charge : ℤ
  coefficient : ℕ
  phase : Phase
deriving DecidableEq, Repr

structure MaterialStageLedger where
  sourceArrow : String
  classification : TransformationUse
  inputs : List MaterialTerm
  outputs : List MaterialTerm
deriving DecidableEq, Repr

def totalAtoms : List MaterialTerm → ElementInventory
  | [] => ElementInventory.zero
  | term :: terms =>
      ElementInventory.add
        (ElementInventory.scale term.coefficient term.atoms)
        (totalAtoms terms)

def totalCharge : List MaterialTerm → ℤ
  | [] => 0
  | term :: terms => term.coefficient * term.charge + totalCharge terms

def MaterialStageBalanced (stage : MaterialStageLedger) : Prop :=
  totalAtoms stage.inputs = totalAtoms stage.outputs ∧
  totalCharge stage.inputs = totalCharge stage.outputs

/-- E1 + D2 → COF-8 is used quantitatively because its three condensation
losses determine the pore formula needed downstream. -/
def cof8CondensationLedger : MaterialStageLedger :=
  { sourceArrow := "page 6: E1 + D2 to COF-8"
    classification := .quantitativeMaterialStage
    inputs :=
      [ ⟨"E1", e1Monomer, 0, 1, .unspecified⟩,
        ⟨"D2", d2Monomer, 0, 1, .unspecified⟩ ]
    outputs :=
      [ ⟨"COF-8 effective pore unit", cof8PoreAssembly, 0, 1, .solid⟩,
        ⟨"condensation water", water, 0, 3, .unspecified⟩ ] }

/-- COF-8 + 3 NH₂OH → COF-9 is used quantitatively because all three depicted
nitriles become amidoxime groups and hence change the pore molar mass. -/
def cof8ToCof9Ledger : MaterialStageLedger :=
  { sourceArrow := "page 7: COF-8 plus NH2OH to COF-9"
    classification := .quantitativeMaterialStage
    inputs :=
      [ ⟨"COF-8 effective pore unit", cof8PoreAssembly, 0, 1, .solid⟩,
        ⟨"hydroxylamine", hydroxylamine, 0, 3, .unspecified⟩ ]
    outputs :=
      [ ⟨"COF-9 effective pore unit", cof9PoreAssembly, 0, 1, .solid⟩ ] }

theorem cof8CondensationLedger_balanced :
    MaterialStageBalanced cof8CondensationLedger := by
  norm_num [MaterialStageBalanced, cof8CondensationLedger, totalAtoms,
    totalCharge, cof8PoreAssembly, e1Monomer, e1AreneCore, cyanomethylArm,
    d2Monomer, d2TriazineCore, paraFormylphenylArm, water,
    ElementInventory.zero, ElementInventory.add, ElementInventory.sub,
    ElementInventory.scale]

theorem cof8ToCof9Ledger_balanced :
    MaterialStageBalanced cof8ToCof9Ledger := by
  norm_num [MaterialStageBalanced, cof8ToCof9Ledger, totalAtoms, totalCharge,
    cof9PoreAssembly, cof8PoreAssembly, e1Monomer, e1AreneCore,
    cyanomethylArm, d2Monomer, d2TriazineCore, paraFormylphenylArm, water,
    hydroxylamine, ElementInventory.add, ElementInventory.sub,
    ElementInventory.scale, ElementInventory.zero]

/-! ## Pinned molar-mass data and experiment -/

/-- Reproducible metadata for one approved offline molar-mass lookup.  The
registry nominal value is the conventional olympiad input; its metadata
uncertainty is retained but is not a source measurement interval. -/
structure MolarMassReceipt where
  formula : String
  atoms : ElementInventory
  nominalValue : ℝ
  uncertaintyBound : ℝ
  unit : String
  datasetVersion : String
  datasetSha256 : String
  recordSha256 : String
  sourceUrl : String

def cof9PoreMolarMassReceipt : MolarMassReceipt :=
  { formula := "C36H27N9O3"
    atoms := ⟨36, 27, 9, 3, 0⟩
    nominalValue := 633.672
    uncertaintyBound := 0.0894
    unit := "g mol^-1"
    datasetVersion :=
      "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1"
    datasetSha256 :=
      "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"
    recordSha256 :=
      "4c08e5cc8fc09e3bd98e6c3572685f7893544144fde54c0f913c4b9f5ffde384"
    sourceUrl := "https://ciaaw.org/abridged-atomic-weights.htm" }

def uranylMolarMassReceipt : MolarMassReceipt :=
  { formula := "UO2"
    atoms := ⟨0, 0, 0, 2, 1⟩
    nominalValue := 270.028
    uncertaintyBound := 0.012
    unit := "g mol^-1"
    datasetVersion :=
      "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1"
    datasetSha256 :=
      "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"
    recordSha256 :=
      "f28469ce635cdd4a6cf12a345ce780b39df4f6ef5ff346c55cc3bb7312b54e18"
    sourceUrl := "https://ciaaw.org/abridged-atomic-weights.htm" }

def cof9PoreMolarMass : ℝ := cof9PoreMolarMassReceipt.nominalValue

def uranylMolarMass : ℝ := uranylMolarMassReceipt.nominalValue

def cof9Solid : ChemicalSpecies :=
  ⟨"COF-9 effective pore unit", cof9PoreAssembly, 0, .solid⟩

def uranylIonAqueous : ChemicalSpecies :=
  ⟨"UO2^2+", ⟨0, 0, 0, 2, 1⟩, 2, .aqueous⟩

inductive UraniumSpeciation where
  | allUranyl
  | unspecifiedOrMixed
deriving DecidableEq, Repr

inductive ConcentrationStage where
  | initial
  | equilibrium
deriving DecidableEq, Repr

/-- All numerical fields are the central values printed on page 7. -/
structure AdsorptionExperiment where
  adsorbent : ChemicalSpecies
  dissolvedAdsorbate : ChemicalSpecies
  uraniumSpeciation : UraniumSpeciation
  finalConcentrationStage : ConcentrationStage
  initialConcentrationMgPerDm3 : ℝ
  equilibriumConcentrationMgPerDm3 : ℝ
  solutionVolumeMl : ℝ
  adsorbentMassMg : ℝ

def sourceExperiment : AdsorptionExperiment :=
  { adsorbent := cof9Solid
    dissolvedAdsorbate := uranylIonAqueous
    uraniumSpeciation := .allUranyl
    finalConcentrationStage := .equilibrium
    initialConcentrationMgPerDm3 := 19.90
    equilibriumConcentrationMgPerDm3 := 9.225
    solutionVolumeMl := 200.0
    adsorbentMassMg := 5.000 }

def sourceExperimentSideConditions : Prop :=
  sourceExperiment.uraniumSpeciation = .allUranyl ∧
  sourceExperiment.finalConcentrationStage = .equilibrium ∧
  0 < sourceExperiment.equilibriumConcentrationMgPerDm3 ∧
  sourceExperiment.equilibriumConcentrationMgPerDm3 <
    sourceExperiment.initialConcentrationMgPerDm3 ∧
  0 < sourceExperiment.solutionVolumeMl ∧
  0 < sourceExperiment.adsorbentMassMg ∧
  0 < cof9PoreMolarMass ∧
  0 < uranylMolarMass

/-- The source report's half-last-displayed-quantum interpretation of all four
measured readouts. -/
def sourceMeasurementBounds
    (initial equilibrium volumeMl adsorbentMassMg : ℝ) : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement
      initial sourceExperiment.initialConcentrationMgPerDm3 0.01 ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      equilibrium sourceExperiment.equilibriumConcentrationMgPerDm3 0.001 ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      volumeMl sourceExperiment.solutionVolumeMl 0.1 ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      adsorbentMassMg sourceExperiment.adsorbentMassMg 0.001

def solutionVolumeDm3 (volumeMl : ℝ) : ℝ := volumeMl / 1000

def massGFromMg (massMg : ℝ) : ℝ := massMg / 1000

/-- Loss of dissolved uranyl mass from the measured solution, in milligrams. -/
def adsorbedUranylMassMgFromMeasurements
    (initial equilibrium volumeMl : ℝ) : ℝ :=
  (initial - equilibrium) * solutionVolumeDm3 volumeMl

def equilibriumAbsorptionCapacityFromMeasurements
    (initial equilibrium volumeMl adsorbentMassMg : ℝ) : ℝ :=
  adsorbedUranylMassMgFromMeasurements initial equilibrium volumeMl /
    massGFromMg adsorbentMassMg

/-- Exact, unrounded central-value expression for `q_e`, in mg g⁻¹. -/
def equilibriumAbsorptionCapacityRaw : ℝ :=
  equilibriumAbsorptionCapacityFromMeasurements
    sourceExperiment.initialConcentrationMgPerDm3
    sourceExperiment.equilibriumConcentrationMgPerDm3
    sourceExperiment.solutionVolumeMl
    sourceExperiment.adsorbentMassMg

/-- Governing source-to-target relation for the absorption capacity. -/
def EquilibriumAbsorptionCapacityDerivationSpec (q : ℝ) : Prop :=
  sourceExperimentSideConditions ∧
  q = equilibriumAbsorptionCapacityFromMeasurements
    sourceExperiment.initialConcentrationMgPerDm3
    sourceExperiment.equilibriumConcentrationMgPerDm3
    sourceExperiment.solutionVolumeMl
    sourceExperiment.adsorbentMassMg

theorem adsorbedUranylMassMg_exact :
    adsorbedUranylMassMgFromMeasurements
      sourceExperiment.initialConcentrationMgPerDm3
      sourceExperiment.equilibriumConcentrationMgPerDm3
      sourceExperiment.solutionVolumeMl = 2.135 := by
  norm_num [adsorbedUranylMassMgFromMeasurements, solutionVolumeDm3,
    sourceExperiment]

/-- Raw result contract: the governing equation and the nondegenerate reporting
cell derived from the fixed quantum are both exposed. -/
theorem equilibriumAbsorptionCapacityRaw_spec :
    EquilibriumAbsorptionCapacityDerivationSpec
        equilibriumAbsorptionCapacityRaw ∧
      (853 / 2 : ℝ) < equilibriumAbsorptionCapacityRaw ∧
      equilibriumAbsorptionCapacityRaw < (855 / 2 : ℝ) := by
  norm_num [EquilibriumAbsorptionCapacityDerivationSpec,
    sourceExperimentSideConditions, equilibriumAbsorptionCapacityRaw,
    equilibriumAbsorptionCapacityFromMeasurements,
    adsorbedUranylMassMgFromMeasurements, solutionVolumeDm3, massGFromMg,
    sourceExperiment, cof9PoreMolarMass, cof9PoreMolarMassReceipt,
    uranylMolarMass, uranylMolarMassReceipt]

theorem equilibriumAbsorptionCapacityRaw_exact :
    equilibriumAbsorptionCapacityRaw = 427 := by
  norm_num [equilibriumAbsorptionCapacityRaw,
    equilibriumAbsorptionCapacityFromMeasurements,
    adsorbedUranylMassMgFromMeasurements, solutionVolumeDm3, massGFromMg,
    sourceExperiment]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"equilibrium_absorption_capacity","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"427","reporting_quantum":"1","raw_declaration":"IChO2026Problems.T3A7.equilibriumAbsorptionCapacityRaw","reporting_declaration":"IChO2026Problems.T3A7.equilibriumAbsorptionCapacity_reported"}
theorem equilibriumAbsorptionCapacity_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      equilibriumAbsorptionCapacityRaw 427 1 := by
  refine ⟨by norm_num, ⟨427, by norm_num⟩, ?_⟩
  norm_num [
    equilibriumAbsorptionCapacityRaw,
    equilibriumAbsorptionCapacityFromMeasurements,
    adsorbedUranylMassMgFromMeasurements, solutionVolumeDm3, massGFromMg,
    sourceExperiment]

/-- The requested display is stable over every source-derived measurement
cell, not only at the four central values. -/
theorem equilibriumAbsorptionCapacity_measurement_stable :
    ∀ initial equilibrium volumeMl adsorbentMassMg : ℝ,
      sourceMeasurementBounds initial equilibrium volumeMl adsorbentMassMg →
      IChO2026Chem.Reporting.ReportsAtQuantum
        (equilibriumAbsorptionCapacityFromMeasurements
          initial equilibrium volumeMl adsorbentMassMg) 427 1 := by
  intro initial equilibrium volumeMl adsorbentMassMg hbounds
  norm_num [sourceMeasurementBounds,
    IChO2026Chem.Reporting.ConsistentMeasurement, sourceExperiment] at hbounds
  rcases hbounds with ⟨hinitialAbs, hequilibriumAbs, hvolumeAbs, hmassAbs⟩
  have hinitialBounds := abs_le.mp hinitialAbs
  have hequilibriumBounds := abs_le.mp hequilibriumAbs
  have hvolumeBounds := abs_le.mp hvolumeAbs
  have hmassBounds := abs_le.mp hmassAbs
  have hinitialLower : (3979 / 200 : ℝ) ≤ initial := by linarith
  have hinitialUpper : initial ≤ (3981 / 200 : ℝ) := by linarith
  have hequilibriumLower : (18449 / 2000 : ℝ) ≤ equilibrium := by
    linarith
  have hequilibriumUpper : equilibrium ≤ (18451 / 2000 : ℝ) := by
    linarith
  have hvolumeLower : (3999 / 20 : ℝ) ≤ volumeMl := by linarith
  have hvolumeUpper : volumeMl ≤ (4001 / 20 : ℝ) := by linarith
  have hmassLower : (9999 / 2000 : ℝ) ≤ adsorbentMassMg := by linarith
  have hmassUpper : adsorbentMassMg ≤ (10001 / 2000 : ℝ) := by linarith
  have hdifferenceLower :
      (21339 / 2000 : ℝ) ≤ initial - equilibrium := by
    linarith
  have hdifferenceUpper :
      initial - equilibrium ≤ (21361 / 2000 : ℝ) := by
    linarith
  have hdifferencePositive : 0 < initial - equilibrium := by
    linarith
  have hvolumePositive : 0 < volumeMl := by linarith
  have hmassPositive : 0 < adsorbentMassMg := by linarith
  have hproductLower :
      (21339 / 2000 : ℝ) * (3999 / 20 : ℝ) ≤
        (initial - equilibrium) * volumeMl := by
    exact mul_le_mul hdifferenceLower hvolumeLower (by norm_num)
      (le_of_lt hdifferencePositive)
  have hproductUpper :
      (initial - equilibrium) * volumeMl ≤
        (21361 / 2000 : ℝ) * (4001 / 20 : ℝ) := by
    exact mul_le_mul hdifferenceUpper hvolumeUpper
      (le_of_lt hvolumePositive) (by norm_num)
  have hformula :
      equilibriumAbsorptionCapacityFromMeasurements
          initial equilibrium volumeMl adsorbentMassMg =
        (initial - equilibrium) * volumeMl / adsorbentMassMg := by
    simp only [equilibriumAbsorptionCapacityFromMeasurements,
      adsorbedUranylMassMgFromMeasurements, solutionVolumeDm3, massGFromMg]
    field_simp
  have hrawPositive :
      0 < equilibriumAbsorptionCapacityFromMeasurements
        initial equilibrium volumeMl adsorbentMassMg := by
    rw [hformula]
    exact div_pos (mul_pos hdifferencePositive hvolumePositive) hmassPositive
  refine ⟨by norm_num, ⟨427, by norm_num⟩, ?_⟩
  rw [if_pos (le_of_lt hrawPositive)]
  constructor
  · rw [hformula]
    apply (le_div_iff₀ hmassPositive).2
    exact (calc
      (427 - 1 / 2 : ℝ) * adsorbentMassMg ≤
          (427 - 1 / 2 : ℝ) * (10001 / 2000 : ℝ) :=
        mul_le_mul_of_nonneg_left hmassUpper (by norm_num)
      _ ≤ (21339 / 2000 : ℝ) * (3999 / 20 : ℝ) := by norm_num
      _ ≤ (initial - equilibrium) * volumeMl := hproductLower)
  · rw [hformula]
    apply (div_lt_iff₀ hmassPositive).2
    exact (calc
      (initial - equilibrium) * volumeMl ≤
          (21361 / 2000 : ℝ) * (4001 / 20 : ℝ) := hproductUpper
      _ < (427 + 1 / 2 : ℝ) * (9999 / 2000 : ℝ) := by norm_num
      _ ≤ (427 + 1 / 2 : ℝ) * adsorbentMassMg :=
        mul_le_mul_of_nonneg_left hmassLower (by norm_num))

/-! ## Uranyl ions per pore -/

def adsorbedUranylAmountMolFromMeasurements
    (initial equilibrium volumeMl : ℝ) : ℝ :=
  massGFromMg
      (adsorbedUranylMassMgFromMeasurements initial equilibrium volumeMl) /
    uranylMolarMass

/-- Moles of effective COF-9 pore units in the weighed solid.  The topology
ledger proves that one reconstructed formula unit corresponds to one pore. -/
def cof9PoreAmountMolFromMass (adsorbentMassMg : ℝ) : ℝ :=
  massGFromMg adsorbentMassMg / cof9PoreMolarMass

/-- The Avogadro factor cancels from the ratio of uranyl entities to pores. -/
def uranylIonsPerPoreFromMeasurements
    (initial equilibrium volumeMl adsorbentMassMg : ℝ) : ℝ :=
  adsorbedUranylAmountMolFromMeasurements initial equilibrium volumeMl /
    cof9PoreAmountMolFromMass adsorbentMassMg

/-- Exact, unrounded central-value expression for uranyl ions per pore. -/
def uranylIonsPerPoreRaw : ℝ :=
  uranylIonsPerPoreFromMeasurements
    sourceExperiment.initialConcentrationMgPerDm3
    sourceExperiment.equilibriumConcentrationMgPerDm3
    sourceExperiment.solutionVolumeMl
    sourceExperiment.adsorbentMassMg

/-- Governing source-to-target relation for the entity-to-pore count. -/
def UranylIonsPerPoreDerivationSpec (n : ℝ) : Prop :=
  Cof9PoreAssemblySpec ∧
  sourceExperimentSideConditions ∧
  cof9PoreMolarMassReceipt.atoms = cof9PoreAssembly ∧
  uranylMolarMassReceipt.atoms = uranylIonAqueous.atoms ∧
  n = uranylIonsPerPoreFromMeasurements
    sourceExperiment.initialConcentrationMgPerDm3
    sourceExperiment.equilibriumConcentrationMgPerDm3
    sourceExperiment.solutionVolumeMl
    sourceExperiment.adsorbentMassMg

/-- Raw result contract with the nondegenerate 0.01-wide reporting cell. -/
theorem uranylIonsPerPoreRaw_spec :
    UranylIonsPerPoreDerivationSpec uranylIonsPerPoreRaw ∧
      (199 / 200 : ℝ) < uranylIonsPerPoreRaw ∧
      uranylIonsPerPoreRaw < (201 / 200 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨cof9PoreAssembly_spec, ?_, ?_, ?_, rfl⟩
    · norm_num [sourceExperimentSideConditions, cof9PoreMolarMass,
        cof9PoreMolarMassReceipt, uranylMolarMass, uranylMolarMassReceipt,
        sourceExperiment]
    · simpa [cof9PoreMolarMassReceipt] using
        cof9PoreAssembly_spec.2.2.2.2.2.1.symm
    · rfl
  · norm_num [uranylIonsPerPoreRaw, uranylIonsPerPoreFromMeasurements,
      adsorbedUranylAmountMolFromMeasurements, cof9PoreAmountMolFromMass,
      adsorbedUranylMassMgFromMeasurements, solutionVolumeDm3, massGFromMg,
      uranylMolarMass, uranylMolarMassReceipt, cof9PoreMolarMass,
      cof9PoreMolarMassReceipt, sourceExperiment]
  · norm_num [uranylIonsPerPoreRaw, uranylIonsPerPoreFromMeasurements,
      adsorbedUranylAmountMolFromMeasurements, cof9PoreAmountMolFromMass,
      adsorbedUranylMassMgFromMeasurements, solutionVolumeDm3, massGFromMg,
      uranylMolarMass, uranylMolarMassReceipt, cof9PoreMolarMass,
      cof9PoreMolarMassReceipt, sourceExperiment]

theorem uranylIonsPerPoreRaw_exact :
    uranylIonsPerPoreRaw = (33822243 / 33753500 : ℝ) := by
  norm_num [uranylIonsPerPoreRaw, uranylIonsPerPoreFromMeasurements,
    adsorbedUranylAmountMolFromMeasurements, cof9PoreAmountMolFromMass,
    adsorbedUranylMassMgFromMeasurements, solutionVolumeDm3, massGFromMg,
    uranylMolarMass, uranylMolarMassReceipt, cof9PoreMolarMass,
    cof9PoreMolarMassReceipt, sourceExperiment]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"uranyl_ions_per_pore","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"1.00","reporting_quantum":"1/100","raw_declaration":"IChO2026Problems.T3A7.uranylIonsPerPoreRaw","reporting_declaration":"IChO2026Problems.T3A7.uranylIonsPerPore_reported"}
theorem uranylIonsPerPore_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      uranylIonsPerPoreRaw 1 (1 / 100 : ℝ) := by
  refine ⟨by norm_num, ⟨100, by norm_num⟩, ?_⟩
  norm_num [
    uranylIonsPerPoreRaw, uranylIonsPerPoreFromMeasurements,
    adsorbedUranylAmountMolFromMeasurements, cof9PoreAmountMolFromMass,
    adsorbedUranylMassMgFromMeasurements, solutionVolumeDm3, massGFromMg,
    uranylMolarMass, uranylMolarMassReceipt, cof9PoreMolarMass,
    cof9PoreMolarMassReceipt, sourceExperiment]

theorem uranylIonsPerPore_measurement_stable :
    ∀ initial equilibrium volumeMl adsorbentMassMg : ℝ,
      sourceMeasurementBounds initial equilibrium volumeMl adsorbentMassMg →
      IChO2026Chem.Reporting.ReportsAtQuantum
        (uranylIonsPerPoreFromMeasurements
          initial equilibrium volumeMl adsorbentMassMg) 1 0.01 := by
  intro initial equilibrium volumeMl adsorbentMassMg hbounds
  have hcapacityReport :=
    equilibriumAbsorptionCapacity_measurement_stable
      initial equilibrium volumeMl adsorbentMassMg hbounds
  have hcapacityBounds :
      (427 - 1 / 2 : ℝ) ≤
          equilibriumAbsorptionCapacityFromMeasurements
            initial equilibrium volumeMl adsorbentMassMg ∧
        equilibriumAbsorptionCapacityFromMeasurements
            initial equilibrium volumeMl adsorbentMassMg < (427 + 1 / 2 : ℝ) := by
    have hbranch := hcapacityReport.2.2
    by_cases hnonnegative :
        0 ≤ equilibriumAbsorptionCapacityFromMeasurements
          initial equilibrium volumeMl adsorbentMassMg
    · simpa [hnonnegative] using hbranch
    · have himpossible : False := by
        have hnegativeBounds :
            (427 - 1 / 2 : ℝ) <
                equilibriumAbsorptionCapacityFromMeasurements
                  initial equilibrium volumeMl adsorbentMassMg ∧
              equilibriumAbsorptionCapacityFromMeasurements
                  initial equilibrium volumeMl adsorbentMassMg ≤
                (427 + 1 / 2 : ℝ) := by
          simpa [hnonnegative] using hbranch
        linarith
      exact himpossible.elim
  have hboundsCopy := hbounds
  norm_num [sourceMeasurementBounds,
    IChO2026Chem.Reporting.ConsistentMeasurement, sourceExperiment] at hboundsCopy
  have hmassInterval := abs_le.mp hboundsCopy.2.2.2
  have hmassPositive : 0 < adsorbentMassMg := by linarith
  have hformula :
      uranylIonsPerPoreFromMeasurements
          initial equilibrium volumeMl adsorbentMassMg =
        equilibriumAbsorptionCapacityFromMeasurements
            initial equilibrium volumeMl adsorbentMassMg *
          (cof9PoreMolarMass / (1000 * uranylMolarMass)) := by
    simp only [uranylIonsPerPoreFromMeasurements,
      adsorbedUranylAmountMolFromMeasurements, cof9PoreAmountMolFromMass,
      equilibriumAbsorptionCapacityFromMeasurements,
      adsorbedUranylMassMgFromMeasurements, solutionVolumeDm3, massGFromMg]
    field_simp [cof9PoreMolarMass, cof9PoreMolarMassReceipt,
      uranylMolarMass, uranylMolarMassReceipt, ne_of_gt hmassPositive]
  have hfactorPositive :
      0 < cof9PoreMolarMass / (1000 * uranylMolarMass) := by
    norm_num [cof9PoreMolarMass, cof9PoreMolarMassReceipt,
      uranylMolarMass, uranylMolarMassReceipt]
  have hscaledLower :
      (427 - 1 / 2 : ℝ) *
          (cof9PoreMolarMass / (1000 * uranylMolarMass)) ≤
        equilibriumAbsorptionCapacityFromMeasurements
            initial equilibrium volumeMl adsorbentMassMg *
          (cof9PoreMolarMass / (1000 * uranylMolarMass)) := by
    exact mul_le_mul_of_nonneg_right hcapacityBounds.1
      (le_of_lt hfactorPositive)
  have hscaledUpper :
      equilibriumAbsorptionCapacityFromMeasurements
            initial equilibrium volumeMl adsorbentMassMg *
          (cof9PoreMolarMass / (1000 * uranylMolarMass)) <
        (427 + 1 / 2 : ℝ) *
          (cof9PoreMolarMass / (1000 * uranylMolarMass)) := by
    exact mul_lt_mul_of_pos_right hcapacityBounds.2 hfactorPositive
  have hreportedBounds :
      (1 - (0.01 : ℝ) / 2) ≤
          uranylIonsPerPoreFromMeasurements
            initial equilibrium volumeMl adsorbentMassMg ∧
        uranylIonsPerPoreFromMeasurements
            initial equilibrium volumeMl adsorbentMassMg <
          (1 + (0.01 : ℝ) / 2) := by
    constructor
    · rw [hformula]
      exact le_trans (by
          norm_num [cof9PoreMolarMass, cof9PoreMolarMassReceipt,
            uranylMolarMass, uranylMolarMassReceipt]) hscaledLower
    · rw [hformula]
      exact lt_trans hscaledUpper (by
        norm_num [cof9PoreMolarMass, cof9PoreMolarMassReceipt,
          uranylMolarMass, uranylMolarMassReceipt])
  have hrawPositive :
      0 < uranylIonsPerPoreFromMeasurements
        initial equilibrium volumeMl adsorbentMassMg := by
    norm_num at hreportedBounds
    linarith
  refine ⟨by norm_num, ⟨100, by norm_num⟩, ?_⟩
  simpa [if_pos (le_of_lt hrawPositive)] using hreportedBounds

/-! ## One mixed contract covering both requested outputs -/

structure RequestedRawOutputs where
  equilibriumAbsorptionCapacityMgPerG : ℝ
  uranylIonsPerPore : ℝ

def requestedRawOutputs : RequestedRawOutputs :=
  ⟨equilibriumAbsorptionCapacityRaw, uranylIonsPerPoreRaw⟩

def RequestedRawOutputsSpec (outputs : RequestedRawOutputs) : Prop :=
  EquilibriumAbsorptionCapacityDerivationSpec
      outputs.equilibriumAbsorptionCapacityMgPerG ∧
  UranylIonsPerPoreDerivationSpec outputs.uranylIonsPerPore

theorem requestedRawOutputs_spec :
    RequestedRawOutputsSpec requestedRawOutputs := by
  exact ⟨equilibriumAbsorptionCapacityRaw_spec.1,
    uranylIonsPerPoreRaw_spec.1⟩

theorem requestedOutputs_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
        requestedRawOutputs.equilibriumAbsorptionCapacityMgPerG 427 1 ∧
      IChO2026Chem.Reporting.ReportsAtQuantum
        requestedRawOutputs.uranylIonsPerPore 1 (1 / 100 : ℝ) := by
  exact ⟨equilibriumAbsorptionCapacity_reported,
    uranylIonsPerPore_reported⟩

end

end IChO2026Problems.T3A7

/- Exact problem-policy probes mirrored by the deterministic Review preflight. -/
example : IChO2026Chem.Reporting.ReportsAtQuantum
    (_root_.IChO2026Problems.T3A7.equilibriumAbsorptionCapacityRaw : ℝ)
    (427 : ℝ)
    (1 : ℝ) :=
  _root_.IChO2026Problems.T3A7.equilibriumAbsorptionCapacity_reported

example : IChO2026Chem.Reporting.ReportsAtQuantum
    (_root_.IChO2026Problems.T3A7.uranylIonsPerPoreRaw : ℝ)
    (1 : ℝ)
    ((1 : ℝ) / 100) :=
  _root_.IChO2026Problems.T3A7.uranylIonsPerPore_reported
