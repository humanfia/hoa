import Mathlib
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem T4-A9

This file formalizes the source-side calculation of the number of fissions in
the 30-kiloton Urtabulak explosion and the corresponding mass of 90%-enriched
uranium when 33% of its uranium-235 nuclei fissioned.

The previous-part energy is derived here from the printed T4-A4 binding-energy
data.  No theorem from another generated problem file is imported.
-/

namespace IChO2026Problems.ProblemIcho2026T4A9

noncomputable section

/-! ## Source-bounded fission species and nucleon ledger -/

/-- The complete species-role domain needed by the A4/A9 nucleon and energy
calculation.  The individual fission fragments need not be identified: only
their source-forced total bound-nucleon count enters A4. -/
inductive FissionSpeciesRole where
  | uranium235Nucleus
  | absorbedNeutron
  | boundFissionProducts
  | emittedFreeNeutrons
  deriving DecidableEq, Repr

/-- Provenance tag for the finite fission domain. -/
inductive DomainProvenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- The four source-stated roles used in the fission ledger. -/
def fissionSpeciesDomain : Finset FissionSpeciesRole :=
  { .uranium235Nucleus, .absorbedNeutron, .boundFissionProducts,
    .emittedFreeNeutrons }

/-- The role domain comes directly from the printed reaction description. -/
def fissionSpeciesDomainProvenance : DomainProvenance := .problemText

/-- This reaction is used quantitatively: its bound/free nucleon balance
determines the energy released per fission. -/
inductive TransformationUse where
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

def fissionTransformationUse : TransformationUse :=
  .quantitativeMaterialStage

/-- Nucleon counts for one uranium-235 fission event. -/
structure FissionNucleonLedger where
  uranium235BoundNucleons : ℕ
  absorbedFreeNeutrons : ℕ
  productBoundNucleons : ℕ
  emittedFreeNeutrons : ℕ
  deriving Repr

/-- Conservation of nucleon number across one fission event. -/
def FissionNucleonLedger.ConservesNucleons
    (ledger : FissionNucleonLedger) : Prop :=
  ledger.uranium235BoundNucleons + ledger.absorbedFreeNeutrons =
    ledger.productBoundNucleons + ledger.emittedFreeNeutrons

/-- Source ledger: uranium-235 absorbs one neutron and emits three free
neutrons.  Thus the fission products contain `235 + 1 - 3` bound nucleons. -/
def sourceFissionNucleonLedger : FissionNucleonLedger where
  uranium235BoundNucleons := 235
  absorbedFreeNeutrons := 1
  productBoundNucleons := 235 + 1 - 3
  emittedFreeNeutrons := 3

theorem sourceFissionNucleonLedger_conserves :
    sourceFissionNucleonLedger.ConservesNucleons := by
  norm_num [FissionNucleonLedger.ConservesNucleons,
    sourceFissionNucleonLedger]

/-! ## Inline derivation of the T4-A4 energy -/

/-- Binding-energy data for the bound nuclei on the two sides of the
reaction.  Free-neutron binding energy is absent, exactly as stipulated. -/
structure BindingEnergyLedger where
  reactantBoundNucleons : ℕ
  productBoundNucleons : ℕ
  reactantBindingMeVPerNucleon : ℝ
  productBindingMeVPerNucleon : ℝ

/-- Energy released equals final total binding energy minus initial total
binding energy. -/
def BindingEnergyLedger.releasedEnergyMeV
    (ledger : BindingEnergyLedger) : ℝ :=
  (ledger.productBoundNucleons : ℝ) * ledger.productBindingMeVPerNucleon -
    (ledger.reactantBoundNucleons : ℝ) * ledger.reactantBindingMeVPerNucleon

/-- The exact binding-energy inputs printed in T4-A4. -/
def sourceBindingEnergyLedger : BindingEnergyLedger where
  reactantBoundNucleons := sourceFissionNucleonLedger.uranium235BoundNucleons
  productBoundNucleons := sourceFissionNucleonLedger.productBoundNucleons
  reactantBindingMeVPerNucleon := 7.59
  productBindingMeVPerNucleon := 8.45

/-- Primary A4 route, derived from the printed binding energies. -/
def fissionEnergyMeV : ℝ :=
  sourceBindingEnergyLedger.releasedEnergyMeV

/-- The problem-stated fallback is recorded but is not used in the primary
answer-blind derivation. -/
def statedFallbackFissionEnergyMeV : ℝ := 200

/-- Complete source-to-result specification for the locally derived A4 value. -/
def A4EnergyDerivationSpec : Prop :=
  sourceFissionNucleonLedger.ConservesNucleons ∧
  sourceFissionNucleonLedger.productBoundNucleons = 233 ∧
  fissionEnergyMeV =
    (sourceFissionNucleonLedger.productBoundNucleons : ℝ) * 8.45 -
      (sourceFissionNucleonLedger.uranium235BoundNucleons : ℝ) * 7.59 ∧
  fissionEnergyMeV = 185.20

theorem a4Energy_derived : A4EnergyDerivationSpec := by
  norm_num [A4EnergyDerivationSpec, FissionNucleonLedger.ConservesNucleons,
    sourceFissionNucleonLedger, fissionEnergyMeV, sourceBindingEnergyLedger,
    BindingEnergyLedger.releasedEnergyMeV]

/-! ## Explosion-energy and per-fission energy conversions -/

/-- Printed TNT equivalent of the explosion, in kilotons. -/
def explosionYieldKilotonsTNT : ℝ := 30

/-- Exact prefix conversion. -/
def tonsPerKiloton : ℝ := 1000

/-- Printed energy of one ton TNT equivalent, in gigajoules. -/
def gigajoulesPerTonTNT : ℝ := 4.184

/-- Exact SI prefix conversion. -/
def joulesPerGigajoule : ℝ := (10 : ℝ) ^ 9

/-- Explosion energy in joules, with no intermediate rounding. -/
def explosionEnergyJ : ℝ :=
  explosionYieldKilotonsTNT * tonsPerKiloton *
    gigajoulesPerTonTNT * joulesPerGigajoule

/-- Exact SI value of one electronvolt in joules.  This scalar interface is
the value used by the verified `DimEnergy.electronVolt` declaration in
Physlib. -/
def joulesPerElectronVolt : ℝ := 1.602176634e-19

/-- Exact prefix conversion from MeV to eV followed by the SI eV conversion. -/
def joulesPerMegaElectronVolt : ℝ :=
  (10 : ℝ) ^ 6 * joulesPerElectronVolt

/-- Energy in joules released by one fission, without rounding A4. -/
def energyPerFissionJ : ℝ :=
  fissionEnergyMeV * joulesPerMegaElectronVolt

theorem energyPerFissionJ_positive : 0 < energyPerFissionJ := by
  norm_num [energyPerFissionJ, joulesPerMegaElectronVolt,
    joulesPerElectronVolt, fissionEnergyMeV, sourceBindingEnergyLedger,
    BindingEnergyLedger.releasedEnergyMeV, sourceFissionNucleonLedger]

/-! ## Requested output 1: total number of fissions -/

/-- Exact end-to-end number of fissions obtained by dividing the total
explosion energy by the energy released per fission. -/
def totalFissionsRaw : ℝ :=
  explosionEnergyJ / energyPerFissionJ

/-- Governing specification for the first requested output. -/
def TotalFissionsDerivationSpec : Prop :=
  A4EnergyDerivationSpec ∧
  explosionEnergyJ = 30 * 1000 * 4.184 * (10 : ℝ) ^ 9 ∧
  energyPerFissionJ = fissionEnergyMeV * (10 : ℝ) ^ 6 * 1.602176634e-19 ∧
  totalFissionsRaw = explosionEnergyJ / energyPerFissionJ ∧
  totalFissionsRaw * energyPerFissionJ = explosionEnergyJ

theorem totalFissions_raw_derivation : TotalFissionsDerivationSpec := by
  refine ⟨a4Energy_derived, ?_, ?_, rfl, ?_⟩
  · rfl
  · simp only [energyPerFissionJ, joulesPerMegaElectronVolt,
      joulesPerElectronVolt, mul_assoc]
  · rw [totalFissionsRaw]
    exact div_mul_cancel₀ explosionEnergyJ (ne_of_gt energyPerFissionJ_positive)

/-! ## Requested output 2: enriched-uranium mass -/

/-- Exact source-stated fraction of uranium-235 nuclei that underwent
fission. -/
def fissionedUranium235Fraction : ℝ := 33 / 100

/-- Exact source-stated uranium-235 mass fraction in the enriched material.
The denominator of the mass fraction is the total enriched-uranium mass. -/
def uranium235EnrichedMassFraction : ℝ := 90 / 100

/-- Exact SI-defining Avogadro constant, in entities per mole.  The value is
the exact NIST/CODATA entry at `https://physics.nist.gov/cgi-bin/cuu/Value?na`
("Numerical value" and "Standard uncertainty" rows). -/
def avogadroConstantPerMol : ℝ := 6.02214076e23

/-- The problem prints the uranium-235 atomic mass as 235.04 atomic mass
units.  The numerical atomic-mass/molar-mass correspondence gives 235.04
g mol⁻¹, converted here to kg mol⁻¹. -/
def uranium235MolarMassKgPerMol : ℝ := 235.04 / 1000

/-- Outcome-decisive population and mass ledger for the enriched-uranium
sample. -/
structure UraniumMassLedger where
  fissionCount : ℝ
  uranium235NucleusCount : ℝ
  uranium235AmountMol : ℝ
  uranium235MassKg : ℝ
  totalEnrichedUraniumMassKg : ℝ

/-- The four equations connecting fissions, U-235 nuclei, amount of U-235,
U-235 mass, and total enriched-uranium mass. -/
def UraniumMassLedger.Valid (ledger : UraniumMassLedger) : Prop :=
  0 ≤ ledger.fissionCount ∧
  0 ≤ ledger.uranium235NucleusCount ∧
  0 ≤ ledger.uranium235AmountMol ∧
  0 ≤ ledger.uranium235MassKg ∧
  0 ≤ ledger.totalEnrichedUraniumMassKg ∧
  ledger.fissionCount =
    fissionedUranium235Fraction * ledger.uranium235NucleusCount ∧
  ledger.uranium235NucleusCount =
    avogadroConstantPerMol * ledger.uranium235AmountMol ∧
  ledger.uranium235MassKg =
    uranium235MolarMassKgPerMol * ledger.uranium235AmountMol ∧
  ledger.uranium235MassKg =
    uranium235EnrichedMassFraction * ledger.totalEnrichedUraniumMassKg

/-- Exact unrounded mass requested in A9.  The successive divisions expose
the 33%-fission population balance and the 90%-of-total mass basis. -/
def enrichedUraniumMassKgRaw : ℝ :=
  (((totalFissionsRaw / fissionedUranium235Fraction) /
      avogadroConstantPerMol) * uranium235MolarMassKgPerMol) /
    uranium235EnrichedMassFraction

/-- Canonical ledger induced by the exact source-side derivation. -/
def sourceUraniumMassLedger : UraniumMassLedger where
  fissionCount := totalFissionsRaw
  uranium235NucleusCount :=
    totalFissionsRaw / fissionedUranium235Fraction
  uranium235AmountMol :=
    (totalFissionsRaw / fissionedUranium235Fraction) /
      avogadroConstantPerMol
  uranium235MassKg :=
    ((totalFissionsRaw / fissionedUranium235Fraction) /
      avogadroConstantPerMol) * uranium235MolarMassKgPerMol
  totalEnrichedUraniumMassKg := enrichedUraniumMassKgRaw

/-- Governing specification for the second requested output. -/
def EnrichedUraniumMassDerivationSpec : Prop :=
  sourceUraniumMassLedger.Valid ∧
  sourceUraniumMassLedger.fissionCount = totalFissionsRaw ∧
  sourceUraniumMassLedger.totalEnrichedUraniumMassKg =
    enrichedUraniumMassKgRaw ∧
  enrichedUraniumMassKgRaw =
    (((totalFissionsRaw / (33 / 100 : ℝ)) / 6.02214076e23) *
      (235.04 / 1000)) / (90 / 100 : ℝ)

theorem enrichedUraniumMass_raw_derivation :
    EnrichedUraniumMassDerivationSpec := by
  have hTotalFissions : 0 < totalFissionsRaw := by
    rw [totalFissionsRaw]
    exact div_pos (by norm_num [explosionEnergyJ, explosionYieldKilotonsTNT,
      tonsPerKiloton, gigajoulesPerTonTNT, joulesPerGigajoule])
      energyPerFissionJ_positive
  have hFissionedFraction : 0 < fissionedUranium235Fraction := by
    norm_num [fissionedUranium235Fraction]
  have hAvogadro : 0 < avogadroConstantPerMol := by
    norm_num [avogadroConstantPerMol]
  have hMolarMass : 0 < uranium235MolarMassKgPerMol := by
    norm_num [uranium235MolarMassKgPerMol]
  have hEnrichedFraction : 0 < uranium235EnrichedMassFraction := by
    norm_num [uranium235EnrichedMassFraction]
  unfold EnrichedUraniumMassDerivationSpec
  refine ⟨?_, rfl, rfl, ?_⟩
  · unfold UraniumMassLedger.Valid
    dsimp only [sourceUraniumMassLedger]
    refine ⟨hTotalFissions.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (div_pos hTotalFissions hFissionedFraction).le
    · exact (div_pos (div_pos hTotalFissions hFissionedFraction) hAvogadro).le
    · exact (mul_pos
        (div_pos (div_pos hTotalFissions hFissionedFraction) hAvogadro)
        hMolarMass).le
    · unfold enrichedUraniumMassKgRaw
      exact (div_pos (mul_pos
        (div_pos (div_pos hTotalFissions hFissionedFraction) hAvogadro)
        hMolarMass) hEnrichedFraction).le
    · field_simp [fissionedUranium235Fraction]
    · field_simp [avogadroConstantPerMol, fissionedUranium235Fraction]
    · ring
    · unfold enrichedUraniumMassKgRaw
      field_simp [uranium235EnrichedMassFraction]
  · rfl

/-! ## Joint raw and reported solve-phase contracts -/

/-- The raw mixed-output proposition covers both requested scalar outputs. -/
def RawResultSpec : Prop :=
  TotalFissionsDerivationSpec ∧ EnrichedUraniumMassDerivationSpec

/-- Certified rational enclosure for the unrounded fission count. -/
def TotalFissionsCertifiedInterval : Prop :=
  4.23020e24 < totalFissionsRaw ∧ totalFissionsRaw < 4.23021e24

/-- Certified rational enclosure for the unrounded enriched-uranium mass. -/
def EnrichedUraniumMassCertifiedInterval : Prop :=
  5.55899 < enrichedUraniumMassKgRaw ∧ enrichedUraniumMassKgRaw < 5.55900

/-- Raw result contract: the full governing derivation and nondegenerate
enclosures for both requested outputs. -/
def RawResultContractSpec : Prop :=
  RawResultSpec ∧ TotalFissionsCertifiedInterval ∧
    EnrichedUraniumMassCertifiedInterval

/-- Hash-bound solve artifact for the joint raw result.  The string equality
is generated from the exact answer-blind payload; the semantic conjunct is the
source-derived contract above. -/
theorem raw_result :
    ("367bdfecf6e67303c03ab5e02127184cfdc8d4c78abdba8056851e55eb92e32c" : String) =
        "367bdfecf6e67303c03ab5e02127184cfdc8d4c78abdba8056851e55eb92e32c" ∧
      IChO2026Problems.ProblemIcho2026T4A9.RawResultContractSpec := by
  refine ⟨rfl, ⟨⟨totalFissions_raw_derivation,
    enrichedUraniumMass_raw_derivation⟩, ?_, ?_⟩⟩
  · norm_num [TotalFissionsCertifiedInterval, totalFissionsRaw,
      explosionEnergyJ, explosionYieldKilotonsTNT, tonsPerKiloton,
      gigajoulesPerTonTNT, joulesPerGigajoule, energyPerFissionJ,
      fissionEnergyMeV, sourceBindingEnergyLedger,
      BindingEnergyLedger.releasedEnergyMeV, sourceFissionNucleonLedger,
      joulesPerMegaElectronVolt, joulesPerElectronVolt]
  · norm_num [EnrichedUraniumMassCertifiedInterval, enrichedUraniumMassKgRaw,
      totalFissionsRaw, explosionEnergyJ, explosionYieldKilotonsTNT,
      tonsPerKiloton, gigajoulesPerTonTNT, joulesPerGigajoule,
      energyPerFissionJ, fissionEnergyMeV, sourceBindingEnergyLedger,
      BindingEnergyLedger.releasedEnergyMeV, sourceFissionNucleonLedger,
      joulesPerMegaElectronVolt, joulesPerElectronVolt,
      fissionedUranium235Fraction, avogadroConstantPerMol,
      uranium235MolarMassKgPerMol, uranium235EnrichedMassFraction]

/-- Three-significant-figure display for the fission count. -/
def totalFissionsReported : ℝ := 4.23e24

/-- At the magnitude of the fission count, three significant figures have
quantum `10^22`. -/
def totalFissionsReportingQuantum : ℝ := 1e22

/-- Three-significant-figure display for the enriched-uranium mass. -/
def enrichedUraniumMassKgReported : ℝ := 5.56

/-- At the magnitude of the mass, three significant figures have quantum
`0.01 kg`. -/
def enrichedUraniumMassReportingQuantum : ℝ := 0.01

theorem totalFissions_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      totalFissionsRaw (4230000000000000000000000 : ℝ)
        (10000000000000000000000 : ℝ) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨423, by norm_num⟩, ?_⟩
  have hBounds := raw_result.2.2.1
  unfold TotalFissionsCertifiedInterval at hBounds
  rw [if_pos (le_of_lt (lt_trans (by norm_num) hBounds.1))]
  constructor <;> linarith [hBounds.1, hBounds.2]

theorem enrichedUraniumMass_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      enrichedUraniumMassKgRaw ((139 : ℝ) / 25) ((1 : ℝ) / 100) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨556, by norm_num⟩, ?_⟩
  have hBounds := raw_result.2.2.2
  unfold EnrichedUraniumMassCertifiedInterval at hBounds
  rw [if_pos (le_of_lt (lt_trans (by norm_num) hBounds.1))]
  constructor <;> linarith [hBounds.1, hBounds.2]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"total_fissions","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"4.23e24","reporting_quantum":"1e22","raw_declaration":"IChO2026Problems.ProblemIcho2026T4A9.totalFissionsRaw","reporting_declaration":"IChO2026Problems.ProblemIcho2026T4A9.totalFissions_reported"}
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"enriched_uranium_mass","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"5.56","reporting_quantum":"0.01","raw_declaration":"IChO2026Problems.ProblemIcho2026T4A9.enrichedUraniumMassKgRaw","reporting_declaration":"IChO2026Problems.ProblemIcho2026T4A9.enrichedUraniumMass_reported"}

/-- The reported mixed-output proposition preserves both output-specific
three-significant-figure contracts. -/
def ReportedResultSpec : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum
      totalFissionsRaw (4230000000000000000000000 : ℝ)
        (10000000000000000000000 : ℝ) ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      enrichedUraniumMassKgRaw ((139 : ℝ) / 25) ((1 : ℝ) / 100)

theorem reported_result :
    ("209fe0c639a1b7e5f67f06393c5c5a8a3828b59fc530a2eb495d6995caca35c4" : String) =
        "209fe0c639a1b7e5f67f06393c5c5a8a3828b59fc530a2eb495d6995caca35c4" ∧
      IChO2026Problems.ProblemIcho2026T4A9.ReportedResultSpec := by
  exact ⟨rfl, totalFissions_reported, enrichedUraniumMass_reported⟩

end

end IChO2026Problems.ProblemIcho2026T4A9
