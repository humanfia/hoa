import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, theory problem 1, part 6

This file formalizes the two formula identifications requested by the problem.
The thermogravimetric transformation is treated as a
`quantitative_material_stage`: the finite material domain, phases, external
dioxygen input, volatile outputs, atom/charge ledgers, mass ledgers, and the
three displayed-mass intervals are all explicit below.

The two earlier-part facts used here are precisely the controller-certified
exports for this consumer: metal `Q` is aluminium, and acid `F` is mellitic
acid, `C₁₂H₆O₁₂ = C₆(COOH)₆`.  No generated earlier-problem Lean module is
imported.
-/

namespace IChO2026Problems.T1A6

noncomputable section

/-! ## Certified earlier-part carriers -/

/-- Element counts and net charge for the small formulae used in this target. -/
structure MolecularComposition where
  aluminum : ℕ
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  charge : ℤ
  deriving DecidableEq, Repr

/-- Certified T1-A4 export: `Q` is aluminium (atomic number 13). -/
def certifiedMetalQAtomicNumber : ℕ := 13

/-- Certified T1-A5 export: mellitic acid has formula `C₁₂H₆O₁₂`. -/
def certifiedMelliticAcidComposition : MolecularComposition where
  aluminum := 0
  carbon := 12
  hydrogen := 6
  oxygen := 12
  charge := 0

/-- Removing all six carboxylic-acid protons gives mellitate, `C₁₂O₁₂⁶⁻`. -/
def mellitateComposition : MolecularComposition where
  aluminum := 0
  carbon := 12
  hydrogen := 0
  oxygen := 12
  charge := -6

/-- Non-opaque source-to-Lean bridge supplied by the two certified exports and
ordinary deprotonation bookkeeping. -/
def CertifiedPriorBridge : Prop :=
  certifiedMetalQAtomicNumber = 13 ∧
  certifiedMelliticAcidComposition.carbon = 12 ∧
  certifiedMelliticAcidComposition.hydrogen = 6 ∧
  certifiedMelliticAcidComposition.oxygen = 12 ∧
  mellitateComposition.carbon = 12 ∧
  mellitateComposition.hydrogen = 0 ∧
  mellitateComposition.oxygen = 12 ∧
  mellitateComposition.charge = -6

theorem certified_prior_bridge : CertifiedPriorBridge := by
  norm_num [CertifiedPriorBridge, certifiedMetalQAtomicNumber,
    certifiedMelliticAcidComposition, mellitateComposition]

/-! ## Pinned conventional atomic weights -/

/-- A nominal atomic weight together with the exact offline-registry receipt
that supplied it.  Registry uncertainty is retained as metadata; as required
for this olympiad central-value calculation, the nominal value is the exact
conventional input and is not treated as a source measurement. -/
structure AtomicWeightDatum where
  symbol : String
  value : ℝ
  registryUncertainty : ℝ
  recordSHA256 : String

def chemistryDatasetVersion : String :=
  "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1"

def chemistryDatasetSHA256 : String :=
  "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"

def aluminumWeight : AtomicWeightDatum where
  symbol := "Al"
  value := 26982 / 1000
  registryUncertainty := 1 / 1000
  recordSHA256 := "bdb840d02b2eb42be07e27b58fc76501786c75d0a321d38f76dae129c84f5e7f"

def carbonWeight : AtomicWeightDatum where
  symbol := "C"
  value := 12011 / 1000
  registryUncertainty := 2 / 1000
  recordSHA256 := "0f558fc72d4299d061e9d29f394ebed43fc8246f7dbdb402bbb2a338cfbe4b8a"

def oxygenWeight : AtomicWeightDatum where
  symbol := "O"
  value := 15999 / 1000
  registryUncertainty := 1 / 1000
  recordSHA256 := "d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588"

def hydrogenWeight : AtomicWeightDatum where
  symbol := "H"
  value := 1008 / 1000
  registryUncertainty := 2 / 10000
  recordSHA256 := "8e5f2e512d11f6c3409197956a4f015f6144f43057a286107064436c64b4bce5"

def nreal (n : ℕ) : ℝ := n

def waterMolarMass : ℝ :=
  2 * hydrogenWeight.value + oxygenWeight.value

def dioxygenMolarMass : ℝ :=
  2 * oxygenWeight.value

def carbonDioxideMolarMass : ℝ :=
  carbonWeight.value + 2 * oxygenWeight.value

/-! ## Candidate-independent formula domains -/

/-- An empirical hydrated aluminium-mellitate salt formula.  Counts range over
all naturals; no finite or candidate-named singleton domain is assumed. -/
structure StoneFormula where
  aluminumAtoms : ℕ
  mellitateIons : ℕ
  waterMolecules : ℕ
  deriving DecidableEq, Repr

/-- An empirical binary aluminium/oxygen formula for the stable open-air
terminal residue.  This is the narrow closed contest-model residue domain
licensed by the stated salt core, atmosphere, named final compound, stable
plateau, and request for a formula from the TGA data. -/
structure ResidueFormula where
  aluminumAtoms : ℕ
  oxygenAtoms : ℕ
  deriving DecidableEq, Repr

def stoneCoreMolarMass (s : StoneFormula) : ℝ :=
  nreal s.aluminumAtoms * aluminumWeight.value +
    nreal (12 * s.mellitateIons) * carbonWeight.value +
    nreal (12 * s.mellitateIons) * oxygenWeight.value

def stoneMolarMass (s : StoneFormula) : ℝ :=
  stoneCoreMolarMass s + nreal s.waterMolecules * waterMolarMass

def residueMolarMass (h : ResidueFormula) : ℝ :=
  nreal h.aluminumAtoms * aluminumWeight.value +
    nreal h.oxygenAtoms * oxygenWeight.value

/-- Charge, positivity, and empirical-formula normalization for the salt core:
Al is `3+` and mellitate is `6-`. -/
def StoneChargeLedger (s : StoneFormula) : Prop :=
  0 < s.aluminumAtoms ∧
  0 < s.mellitateIons ∧
  Nat.Coprime s.aluminumAtoms s.mellitateIons ∧
  3 * s.aluminumAtoms = 6 * s.mellitateIons

/-- Charge, positivity, and empirical-formula normalization for a binary
aluminium oxide: Al is `3+` and O is `2-`. -/
def ResidueChargeLedger (h : ResidueFormula) : Prop :=
  0 < h.aluminumAtoms ∧
  0 < h.oxygenAtoms ∧
  Nat.Coprime h.aluminumAtoms h.oxygenAtoms ∧
  3 * h.aluminumAtoms = 2 * h.oxygenAtoms

/-! ## Source conditions, species, phases, and roles -/

inductive Atmosphere
  | openAir
  deriving DecidableEq, Repr

inductive TemperatureQualifier
  | approximate
  | stated
  deriving DecidableEq, Repr

structure TemperatureEvent where
  celsius : ℝ
  qualifier : TemperatureQualifier

structure TGAConditions where
  atmosphere : Atmosphere
  dehydrationOnset : TemperatureEvent
  firstPlateau : TemperatureEvent
  secondDrop : TemperatureEvent

def sourceTGAConditions : TGAConditions where
  atmosphere := .openAir
  dehydrationOnset := ⟨100, .approximate⟩
  firstPlateau := ⟨200, .stated⟩
  secondDrop := ⟨400, .stated⟩

inductive Phase
  | solid
  | gas
  deriving DecidableEq, Repr

inductive TGASpecies
  | hydratedStone
  | anhydrousStone
  | waterVapor
  | dioxygen
  | carbonDioxide
  | terminalResidueH
  deriving DecidableEq, Repr

inductive MaterialRole
  | initialSample
  | intermediate
  | externalInput
  | volatileOutput
  | terminalResidue
  deriving DecidableEq, Repr

def speciesPhase : TGASpecies → Phase
  | .hydratedStone => .solid
  | .anhydrousStone => .solid
  | .waterVapor => .gas
  | .dioxygen => .gas
  | .carbonDioxide => .gas
  | .terminalResidueH => .solid

def speciesRole : TGASpecies → MaterialRole
  | .hydratedStone => .initialSample
  | .anhydrousStone => .intermediate
  | .waterVapor => .volatileOutput
  | .dioxygen => .externalInput
  | .carbonDioxide => .volatileOutput
  | .terminalResidueH => .terminalResidue

/-- Exact finite stage-one material domain; there is no catch-all stream. -/
def dehydrationSpeciesDomain : List TGASpecies :=
  [.hydratedStone, .anhydrousStone, .waterVapor]

/-- Exact finite stage-two material domain; there is no catch-all stream. -/
def calcinationSpeciesDomain : List TGASpecies :=
  [.anhydrousStone, .dioxygen, .terminalResidueH, .carbonDioxide]

/-! ## Displayed measurements and quantitative stage ledgers -/

structure DisplayedMass where
  shownGrams : ℝ
  displayedQuantumGrams : ℝ

def initialMassReading : DisplayedMass := ⟨10, 1 / 100⟩
def firstPlateauReading : DisplayedMass := ⟨23 / 4, 1 / 100⟩
def finalPlateauReading : DisplayedMass := ⟨3 / 2, 1 / 100⟩

def FitsDisplayedMass (actual : ℝ) (reading : DisplayedMass) : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement
    actual reading.shownGrams reading.displayedQuantumGrams

/-- Complete atom and mass ledger for loss of hydration water.  Amounts are in
moles of the named species. -/
structure DehydrationLedger (s : StoneFormula) where
  hydratedAmount : ℝ
  anhydrousAmount : ℝ
  waterAmount : ℝ
  hydratedAmount_pos : 0 < hydratedAmount
  anhydrousAmount_pos : 0 < anhydrousAmount
  waterAmount_pos : 0 < waterAmount
  formulaUnitBalance : anhydrousAmount = hydratedAmount
  waterStoichiometry : waterAmount = hydratedAmount * nreal s.waterMolecules
  aluminumBalance :
    hydratedAmount * nreal s.aluminumAtoms =
      anhydrousAmount * nreal s.aluminumAtoms
  carbonBalance :
    hydratedAmount * nreal (12 * s.mellitateIons) =
      anhydrousAmount * nreal (12 * s.mellitateIons)
  hydrogenBalance :
    hydratedAmount * nreal (2 * s.waterMolecules) = waterAmount * 2
  oxygenBalance :
    hydratedAmount * nreal (12 * s.mellitateIons + s.waterMolecules) =
      anhydrousAmount * nreal (12 * s.mellitateIons) + waterAmount
  massBalance :
    hydratedAmount * stoneMolarMass s =
      anhydrousAmount * stoneCoreMolarMass s + waterAmount * waterMolarMass

/-- Complete atom and mass ledger for open-air oxidative calcination.  The
only external material is dioxygen and the only volatile product is carbon
dioxide. -/
structure CalcinationLedger (s : StoneFormula) (h : ResidueFormula) where
  coreAmount : ℝ
  dioxygenAmount : ℝ
  residueAmount : ℝ
  carbonDioxideAmount : ℝ
  coreAmount_pos : 0 < coreAmount
  dioxygenAmount_pos : 0 < dioxygenAmount
  residueAmount_pos : 0 < residueAmount
  carbonDioxideAmount_pos : 0 < carbonDioxideAmount
  aluminumBalance :
    coreAmount * nreal s.aluminumAtoms =
      residueAmount * nreal h.aluminumAtoms
  carbonBalance :
    coreAmount * nreal (12 * s.mellitateIons) = carbonDioxideAmount
  oxygenBalance :
    coreAmount * nreal (12 * s.mellitateIons) + 2 * dioxygenAmount =
      residueAmount * nreal h.oxygenAtoms + 2 * carbonDioxideAmount
  massBalance :
    coreAmount * stoneCoreMolarMass s + dioxygenAmount * dioxygenMolarMass =
      residueAmount * residueMolarMass h +
        carbonDioxideAmount * carbonDioxideMolarMass

/-- One realization of the source experiment.  The actual masses may vary
inside the half-last-place intervals fixed before candidate selection. -/
structure TGAExecution (s : StoneFormula) (h : ResidueFormula) where
  initialMass : ℝ
  firstPlateauMass : ℝ
  finalPlateauMass : ℝ
  initialMass_pos : 0 < initialMass
  firstPlateauMass_pos : 0 < firstPlateauMass
  finalPlateauMass_pos : 0 < finalPlateauMass
  initialMeasurement : FitsDisplayedMass initialMass initialMassReading
  firstPlateauMeasurement :
    FitsDisplayedMass firstPlateauMass firstPlateauReading
  finalPlateauMeasurement : FitsDisplayedMass finalPlateauMass finalPlateauReading
  dehydration : DehydrationLedger s
  calcination : CalcinationLedger s h
  stagesJoin : calcination.coreAmount = dehydration.anhydrousAmount
  firstPlateauMassFraction :
    firstPlateauMass / initialMass =
      (dehydration.anhydrousAmount * stoneCoreMolarMass s) /
        (dehydration.hydratedAmount * stoneMolarMass s)
  finalPlateauMassFraction :
    finalPlateauMass / initialMass =
      (calcination.residueAmount * residueMolarMass h) /
        (dehydration.hydratedAmount * stoneMolarMass s)

/-- Candidate-independent source model.  All formula counts range over
naturals and every outcome-decisive constraint is applied uniformly. -/
def SourceCompatible (s : StoneFormula) (h : ResidueFormula) : Prop :=
  StoneChargeLedger s ∧
  ResidueChargeLedger h ∧
  Nonempty (TGAExecution s h)

/-! ## Derived candidates and requested-output specifications -/

/-- Candidate obtained by solving the salt charge ratio and the first TGA
plateau over the unrestricted whole-number hydration count. -/
def stoneFormula : StoneFormula where
  aluminumAtoms := 2
  mellitateIons := 1
  waterMolecules := 16

/-- Candidate obtained from the normalized aluminium/oxygen charge ledger and
checked by the final TGA plateau. -/
def compoundHFormula : ResidueFormula where
  aluminumAtoms := 2
  oxygenAtoms := 3

/-- Independent molar-mass receipts for the three candidate formula blocks,
used only as an audit against the element-by-element calculation. -/
def RegistryMassCrossChecks : Prop :=
  stoneCoreMolarMass stoneFormula = 390084 / 1000 ∧
  waterMolarMass = 18015 / 1000 ∧
  residueMolarMass compoundHFormula = 101961 / 1000

theorem registry_mass_cross_checks : RegistryMassCrossChecks := by
  norm_num [RegistryMassCrossChecks, stoneCoreMolarMass, stoneFormula,
    residueMolarMass, compoundHFormula, waterMolarMass, nreal,
    aluminumWeight, carbonWeight, oxygenWeight, hydrogenWeight]

/-! ## Arithmetic consequences of the normalized charge ledgers -/

/-- A positive coprime neutral aluminium/mellitate formula has the unique
empirical ratio `Al₂ : mellitate = 2 : 1`. -/
lemma stone_charge_ledger_unique (s : StoneFormula)
    (hs : StoneChargeLedger s) :
    s.aluminumAtoms = 2 ∧ s.mellitateIons = 1 := by
  rcases hs with ⟨ha, hm, hcop, hcharge⟩
  have hratio : s.aluminumAtoms = 2 * s.mellitateIons := by omega
  have hm_one : s.mellitateIons = 1 := by
    apply Nat.eq_one_of_dvd_coprimes hcop
    · rw [hratio]
      exact ⟨2, by omega⟩
    · exact dvd_rfl
  constructor <;> omega

/-- A positive coprime neutral binary aluminium/oxygen formula is uniquely
`Al₂O₃`. -/
lemma residue_charge_ledger_unique (h : ResidueFormula)
    (hh : ResidueChargeLedger h) :
    h.aluminumAtoms = 2 ∧ h.oxygenAtoms = 3 := by
  rcases hh with ⟨ha, ho, hcop, hcharge⟩
  have ha_even : 2 ∣ h.aluminumAtoms := by omega
  rcases ha_even with ⟨k, hk⟩
  have ho_eq : h.oxygenAtoms = 3 * k := by omega
  have hk_one : k = 1 := by
    apply Nat.eq_one_of_dvd_coprimes hcop
    · exact ⟨2, by omega⟩
    · exact ⟨3, by omega⟩
  constructor <;> omega

/-! ## Explicit source-compatible realization of the proposed formulae -/

/-- The exact central `10 g` realization.  Its two calculated plateaux are
inside the independently fixed two-decimal display intervals. -/
def candidate_tga_execution :
    TGAExecution stoneFormula compoundHFormula := by
  let dehydrationLedger : DehydrationLedger stoneFormula :=
    { hydratedAmount := 1
      anhydrousAmount := 1
      waterAmount := 16
      hydratedAmount_pos := by norm_num
      anhydrousAmount_pos := by norm_num
      waterAmount_pos := by norm_num
      formulaUnitBalance := by norm_num
      waterStoichiometry := by
        norm_num [stoneFormula, nreal]
      aluminumBalance := by
        norm_num [stoneFormula, nreal]
      carbonBalance := by
        norm_num [stoneFormula, nreal]
      hydrogenBalance := by
        norm_num [stoneFormula, nreal]
      oxygenBalance := by
        norm_num [stoneFormula, nreal]
      massBalance := by
        norm_num [stoneMolarMass, stoneCoreMolarMass, waterMolarMass,
          stoneFormula, nreal, aluminumWeight, carbonWeight, oxygenWeight,
          hydrogenWeight] }
  let calcinationLedger :
      CalcinationLedger stoneFormula compoundHFormula :=
    { coreAmount := 1
      dioxygenAmount := 15 / 2
      residueAmount := 1
      carbonDioxideAmount := 12
      coreAmount_pos := by norm_num
      dioxygenAmount_pos := by norm_num
      residueAmount_pos := by norm_num
      carbonDioxideAmount_pos := by norm_num
      aluminumBalance := by
        norm_num [stoneFormula, compoundHFormula, nreal]
      carbonBalance := by
        norm_num [stoneFormula, nreal]
      oxygenBalance := by
        norm_num [stoneFormula, compoundHFormula, nreal]
      massBalance := by
        norm_num [stoneCoreMolarMass, residueMolarMass, dioxygenMolarMass,
          carbonDioxideMolarMass, stoneFormula, compoundHFormula, nreal,
          aluminumWeight, carbonWeight, oxygenWeight] }
  refine
    { initialMass := 10
      firstPlateauMass := 325070 / 56527
      finalPlateauMass := 169935 / 113054
      initialMass_pos := by norm_num
      firstPlateauMass_pos := by norm_num
      finalPlateauMass_pos := by norm_num
      initialMeasurement := by
        norm_num [FitsDisplayedMass, initialMassReading,
          IChO2026Chem.Reporting.ConsistentMeasurement]
      firstPlateauMeasurement := by
        norm_num [FitsDisplayedMass, firstPlateauReading,
          IChO2026Chem.Reporting.ConsistentMeasurement, abs_of_nonneg,
          abs_of_nonpos]
      finalPlateauMeasurement := by
        norm_num [FitsDisplayedMass, finalPlateauReading,
          IChO2026Chem.Reporting.ConsistentMeasurement, abs_of_nonneg,
          abs_of_nonpos]
      dehydration := dehydrationLedger
      calcination := calcinationLedger
      stagesJoin := by norm_num [calcinationLedger, dehydrationLedger]
      firstPlateauMassFraction := by
        norm_num [calcinationLedger, dehydrationLedger, stoneMolarMass,
          stoneCoreMolarMass, waterMolarMass, stoneFormula, nreal,
          aluminumWeight, carbonWeight, oxygenWeight, hydrogenWeight]
      finalPlateauMassFraction := by
        norm_num [calcinationLedger, dehydrationLedger, stoneMolarMass,
          stoneCoreMolarMass, residueMolarMass, waterMolarMass, stoneFormula,
          compoundHFormula, nreal, aluminumWeight, carbonWeight,
          oxygenWeight, hydrogenWeight] }

lemma candidate_source_compatible :
    SourceCompatible stoneFormula compoundHFormula := by
  refine ⟨?_, ?_, ⟨candidate_tga_execution⟩⟩
  · norm_num [StoneChargeLedger, stoneFormula]
  · norm_num [ResidueChargeLedger, compoundHFormula]

/-! ## Uniqueness from the displayed-mass intervals -/

/-- The first plateau forces the unrestricted hydration count strictly between
15 and 17, after the normalized salt core has been fixed by charge. -/
lemma source_compatible_stone_unique (s : StoneFormula) (h : ResidueFormula)
    (hcompat : SourceCompatible s h) : s = stoneFormula := by
  rcases hcompat with ⟨hs, _hh, ⟨execution⟩⟩
  obtain ⟨haluminum, hmellitate⟩ := stone_charge_ledger_unique s hs

  have hcore : stoneCoreMolarMass s = (390084 : ℝ) / 1000 := by
    norm_num [stoneCoreMolarMass, nreal, aluminumWeight, carbonWeight,
      oxygenWeight, haluminum, hmellitate]
  have htotal :
      stoneMolarMass s =
        (390084 : ℝ) / 1000 +
          (s.waterMolecules : ℝ) * ((18015 : ℝ) / 1000) := by
    norm_num [stoneMolarMass, stoneCoreMolarMass, waterMolarMass, nreal,
      aluminumWeight, carbonWeight, oxygenWeight, hydrogenWeight,
      haluminum, hmellitate]
  have htotal_pos : 0 < stoneMolarMass s := by
    rw [htotal]
    positivity
  have htotal_nonneg : 0 ≤ stoneMolarMass s := le_of_lt htotal_pos

  have hinitial := execution.initialMeasurement
  change
    0 < (1 / 100 : ℝ) ∧
      |execution.initialMass - 10| ≤ (1 / 100 : ℝ) / 2 at hinitial
  obtain ⟨hinitial_lower_abs, hinitial_upper_abs⟩ := abs_le.mp hinitial.2
  have hinitial_lower : (1999 : ℝ) / 200 ≤ execution.initialMass := by
    nlinarith
  have hinitial_upper : execution.initialMass ≤ (2001 : ℝ) / 200 := by
    nlinarith

  have hfirst := execution.firstPlateauMeasurement
  change
    0 < (1 / 100 : ℝ) ∧
      |execution.firstPlateauMass - 23 / 4| ≤ (1 / 100 : ℝ) / 2 at hfirst
  obtain ⟨hfirst_lower_abs, hfirst_upper_abs⟩ := abs_le.mp hfirst.2
  have hfirst_lower : (1149 : ℝ) / 200 ≤ execution.firstPlateauMass := by
    nlinarith
  have hfirst_upper : execution.firstPlateauMass ≤ (1151 : ℝ) / 200 := by
    nlinarith
  have hfirst_nonneg : 0 ≤ execution.firstPlateauMass :=
    le_of_lt execution.firstPlateauMass_pos

  have hstage_ratio :
      (execution.dehydration.anhydrousAmount * stoneCoreMolarMass s) /
          (execution.dehydration.hydratedAmount * stoneMolarMass s) =
        stoneCoreMolarMass s / stoneMolarMass s := by
    rw [execution.dehydration.formulaUnitBalance]
    field_simp [ne_of_gt execution.dehydration.hydratedAmount_pos,
      ne_of_gt htotal_pos]
  have hfraction := execution.firstPlateauMassFraction
  rw [hstage_ratio] at hfraction
  have hcross :
      execution.firstPlateauMass * stoneMolarMass s =
        execution.initialMass * stoneCoreMolarMass s := by
    field_simp [ne_of_gt execution.initialMass_pos, ne_of_gt htotal_pos] at hfraction
    nlinarith [hfraction]

  have hwater_gt : 15 < s.waterMolecules := by
    by_contra hnot
    have hwater_le_nat : s.waterMolecules ≤ 15 := by omega
    have hwater_le_real : (s.waterMolecules : ℝ) ≤ 15 := by
      exact_mod_cast hwater_le_nat
    have htotal_upper :
        stoneMolarMass s ≤
          (390084 : ℝ) / 1000 + 15 * ((18015 : ℝ) / 1000) := by
      rw [htotal]
      nlinarith
    have hproduct_upper :
        execution.firstPlateauMass * stoneMolarMass s ≤
          ((1151 : ℝ) / 200) *
            ((390084 : ℝ) / 1000 + 15 * ((18015 : ℝ) / 1000)) :=
      mul_le_mul hfirst_upper htotal_upper htotal_nonneg (by norm_num)
    have hproduct_lower :
        ((1999 : ℝ) / 200) * ((390084 : ℝ) / 1000) ≤
          execution.initialMass * stoneCoreMolarMass s := by
      rw [hcore]
      exact mul_le_mul_of_nonneg_right hinitial_lower (by norm_num)
    norm_num at hproduct_upper hproduct_lower
    nlinarith [hcross]

  have hwater_lt : s.waterMolecules < 17 := by
    by_contra hnot
    have hwater_ge_nat : 17 ≤ s.waterMolecules := by omega
    have hwater_ge_real : (17 : ℝ) ≤ s.waterMolecules := by
      exact_mod_cast hwater_ge_nat
    have htotal_lower :
        (390084 : ℝ) / 1000 + 17 * ((18015 : ℝ) / 1000) ≤
          stoneMolarMass s := by
      rw [htotal]
      nlinarith
    have hproduct_lower :
        ((1149 : ℝ) / 200) *
            ((390084 : ℝ) / 1000 + 17 * ((18015 : ℝ) / 1000)) ≤
          execution.firstPlateauMass * stoneMolarMass s :=
      mul_le_mul hfirst_lower htotal_lower (by norm_num) hfirst_nonneg
    have hproduct_upper :
        execution.initialMass * stoneCoreMolarMass s ≤
          ((2001 : ℝ) / 200) * ((390084 : ℝ) / 1000) := by
      rw [hcore]
      exact mul_le_mul_of_nonneg_right hinitial_upper (by norm_num)
    norm_num at hproduct_lower hproduct_upper
    nlinarith [hcross]

  have hwater : s.waterMolecules = 16 := by omega
  cases s with
  | mk aluminum mellitate water =>
      change aluminum = 2 at haluminum
      change mellitate = 1 at hmellitate
      change water = 16 at hwater
      subst aluminum
      subst mellitate
      subst water
      rfl

lemma source_compatible_residue_unique (s : StoneFormula) (h : ResidueFormula)
    (hcompat : SourceCompatible s h) : h = compoundHFormula := by
  rcases hcompat with ⟨_hs, hh, _execution⟩
  obtain ⟨haluminum, hoxygen⟩ := residue_charge_ledger_unique h hh
  cases h with
  | mk aluminum oxygen =>
      change aluminum = 2 at haluminum
      change oxygen = 3 at hoxygen
      subst aluminum
      subst oxygen
      rfl

/-- Requested output carrier 1: the displayed TGA intervals admit the proposed
stone formula, and every source-compatible formula has exactly those counts. -/
def StoneFormulaResult : Prop :=
  SourceCompatible stoneFormula compoundHFormula ∧
  ∀ (s : StoneFormula) (h : ResidueFormula),
    SourceCompatible s h → s = stoneFormula

/-- Requested output carrier 2: the same source model admits the proposed
terminal residue and every source-compatible residue has exactly those counts. -/
def CompoundHFormulaResult : Prop :=
  SourceCompatible stoneFormula compoundHFormula ∧
  ∀ (s : StoneFormula) (h : ResidueFormula),
    SourceCompatible s h → h = compoundHFormula

theorem stone_formula_identified : StoneFormulaResult := by
  exact ⟨candidate_source_compatible, source_compatible_stone_unique⟩

theorem compound_h_formula_identified : CompoundHFormulaResult := by
  exact ⟨candidate_source_compatible, source_compatible_residue_unique⟩

/-- Raw mixed symbolic result covering both requested outputs in source order. -/
def RawResult : Prop :=
  CertifiedPriorBridge ∧
  RegistryMassCrossChecks ∧
  StoneFormulaResult ∧
  CompoundHFormulaResult

/-- Exact-symbolic reporting adds no rounding; it exposes every atom and water
count of both requested formula carriers. -/
def ReportedResult : Prop :=
  RawResult ∧
  stoneFormula.aluminumAtoms = 2 ∧
  stoneFormula.mellitateIons = 1 ∧
  stoneFormula.waterMolecules = 16 ∧
  compoundHFormula.aluminumAtoms = 2 ∧
  compoundHFormula.oxygenAtoms = 3

/-- The payload-marker strings are patched from the answer-blind candidate
record after its exact fields have been frozen. -/
theorem rawResultContract :
    ("5a6b5b9e6d556138ce9222ae12408ea98a42ad9d7f6cf3b7ce9f5b168964b727" : String) =
        "5a6b5b9e6d556138ce9222ae12408ea98a42ad9d7f6cf3b7ce9f5b168964b727" ∧
      IChO2026Problems.T1A6.RawResult := by
  refine ⟨rfl, ?_⟩
  exact ⟨certified_prior_bridge, registry_mass_cross_checks,
    stone_formula_identified, compound_h_formula_identified⟩

theorem reportedResultContract :
    ("7fd5c8f986c6ca92baae72317ec0662f7e1fa4e14ad6ce780f574847037f8dc0" : String) =
        "7fd5c8f986c6ca92baae72317ec0662f7e1fa4e14ad6ce780f574847037f8dc0" ∧
      IChO2026Problems.T1A6.ReportedResult := by
  refine ⟨rfl, ?_⟩
  exact
    ⟨⟨certified_prior_bridge, registry_mass_cross_checks,
        stone_formula_identified, compound_h_formula_identified⟩,
      rfl, rfl, rfl, rfl, rfl⟩

end

end IChO2026Problems.T1A6
