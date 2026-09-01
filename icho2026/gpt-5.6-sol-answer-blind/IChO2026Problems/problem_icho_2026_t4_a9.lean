import Mathlib
import Physlib.Units.WithDim.Energy
import IChO2026Chem

/-!
# IChO 2026, problem T4-A9

This file formalizes the source-side calculation of both requested outputs:
the total number of fissions in a 30 kiloton TNT-equivalent explosion and the
total mass of 90%-enriched uranium when 33% of its uranium-235 fissions.

The fission energy required from T4-A4 is derived here from the printed binding
energies.  No result from another generated problem file is imported.
-/

namespace IChO2026Problems.Icho2026T4A9

open IChO2026Chem.Reporting

noncomputable section

/-- An isotope is identified by atomic number and mass number. -/
structure Isotope where
  atomicNumber : ℕ
  massNumber : ℕ
  deriving DecidableEq

/-- The fissile isotope named in the problem. -/
def uranium235 : Isotope where
  atomicNumber := 92
  massNumber := 235

/-- Source-side nucleon bookkeeping for one uranium-235 fission event. -/
structure FissionNucleonLedger where
  fissileIsotope : Isotope
  absorbedNeutrons : ℕ
  emittedFreeNeutrons : ℕ

namespace FissionNucleonLedger

/-- Bound nucleons remaining in the two fission products. -/
def boundProductNucleons (ledger : FissionNucleonLedger) : ℕ :=
  ledger.fissileIsotope.massNumber + ledger.absorbedNeutrons -
    ledger.emittedFreeNeutrons

/-- The emitted free neutrons and bound product nucleons exhaust the input
nucleons. -/
def ConservesNucleons (ledger : FissionNucleonLedger) : Prop :=
  ledger.emittedFreeNeutrons ≤
      ledger.fissileIsotope.massNumber + ledger.absorbedNeutrons ∧
    ledger.boundProductNucleons + ledger.emittedFreeNeutrons =
      ledger.fissileIsotope.massNumber + ledger.absorbedNeutrons

end FissionNucleonLedger

/-- The problem states absorption of one neutron and emission of three free
neutrons per fission. -/
def sourceFissionLedger : FissionNucleonLedger where
  fissileIsotope := uranium235
  absorbedNeutrons := 1
  emittedFreeNeutrons := 3

/-- All numerical problem data, retained in the units printed in the source
where possible. -/
structure ProblemInputs where
  uranium235BindingMeVPerNucleon : ℝ
  fissionProductBindingMeVPerNucleon : ℝ
  freeNeutronBindingMeV : ℝ
  explosionKilotonTNT : ℝ
  tntEnergyGJPerTon : ℝ
  uranium235MolarMassKgPerMol : ℝ
  uranium235EnrichmentMassFraction : ℝ
  uranium235FissionMassFraction : ℝ

/-- Exact values printed in T4-A4/T4-A9.  `freeNeutronBindingMeV = 0`
implements the instruction to neglect the binding energy of free neutrons.
The value `0.23504 kg mol⁻¹` is the printed `235.04` atomic-mass value with the
standard numerical atomic-mass/molar-mass conversion. -/
def sourceInputs : ProblemInputs where
  uranium235BindingMeVPerNucleon := 759 / 100
  fissionProductBindingMeVPerNucleon := 169 / 20
  freeNeutronBindingMeV := 0
  explosionKilotonTNT := 30
  tntEnergyGJPerTon := 4184 / 1000
  uranium235MolarMassKgPerMol := 23504 / 100000
  uranium235EnrichmentMassFraction := 90 / 100
  uranium235FissionMassFraction := 33 / 100

/-- Exact conventional SI conversion factors used by the calculation.
`joulesPerElectronVolt` is the scalar value appearing in the verified Physlib
declaration `DimEnergy.electronVolt`.  The same electron-volt value and the
exact Avogadro constant are independently listed by the NIST 2022 CODATA
constant pages (`Value?evj` and `Value?na`, numerical-value rows). -/
structure SIExactConstants where
  tonsPerKiloton : ℝ
  joulesPerGigajoule : ℝ
  electronVoltsPerMegaElectronVolt : ℝ
  joulesPerElectronVolt : ℝ
  entitiesPerMole : ℝ

def siExactConstants : SIExactConstants where
  tonsPerKiloton := 1000
  joulesPerGigajoule := 10 ^ 9
  electronVoltsPerMegaElectronVolt := 10 ^ 6
  joulesPerElectronVolt := 1602176634 / 10 ^ 28
  entitiesPerMole := 602214076 * 10 ^ 15

/-- The explicit source assumptions: the nucleon ledger balances, all scale
factors used as divisors are positive, and both stated mass fractions lie in
the physical interval `(0,1]`. -/
def SourceAssumptions : Prop :=
  sourceFissionLedger.ConservesNucleons ∧
    0 < sourceInputs.uranium235BindingMeVPerNucleon ∧
    0 < sourceInputs.fissionProductBindingMeVPerNucleon ∧
    0 < sourceInputs.explosionKilotonTNT ∧
    0 < sourceInputs.tntEnergyGJPerTon ∧
    0 < sourceInputs.uranium235MolarMassKgPerMol ∧
    0 < sourceInputs.uranium235EnrichmentMassFraction ∧
    sourceInputs.uranium235EnrichmentMassFraction ≤ 1 ∧
    0 < sourceInputs.uranium235FissionMassFraction ∧
    sourceInputs.uranium235FissionMassFraction ≤ 1 ∧
    0 < siExactConstants.joulesPerElectronVolt ∧
    0 < siExactConstants.entitiesPerMole

/-- Energy released by one fission in MeV, computed as final total binding
energy minus initial total binding energy.  The free-neutron terms are kept
explicit even though their stipulated value is zero. -/
def fissionEnergyMeV : ℝ :=
  (sourceFissionLedger.boundProductNucleons : ℝ) *
      sourceInputs.fissionProductBindingMeVPerNucleon +
      sourceFissionLedger.emittedFreeNeutrons *
        sourceInputs.freeNeutronBindingMeV -
    ((sourceFissionLedger.fissileIsotope.massNumber : ℝ) *
        sourceInputs.uranium235BindingMeVPerNucleon +
      sourceFissionLedger.absorbedNeutrons *
        sourceInputs.freeNeutronBindingMeV)

/-- The inline derivation required from T4-A4.  The first equality derives the
233 bound product nucleons; the second is the exact unrounded energy release. -/
def FissionEnergyDerivationSpec : Prop :=
  sourceFissionLedger.boundProductNucleons = 233 ∧
    fissionEnergyMeV = 926 / 5

theorem fissionEnergyDerivation : FissionEnergyDerivationSpec := by
  norm_num [FissionEnergyDerivationSpec, fissionEnergyMeV,
    sourceFissionLedger, FissionNucleonLedger.boundProductNucleons,
    uranium235, sourceInputs]

/-- Joules released per fission. -/
def energyPerFissionJ : ℝ :=
  fissionEnergyMeV * siExactConstants.electronVoltsPerMegaElectronVolt *
    siExactConstants.joulesPerElectronVolt

/-- Total energy of the 30-kiloton TNT-equivalent explosion, in joules. -/
def explosionEnergyJ : ℝ :=
  sourceInputs.explosionKilotonTNT * siExactConstants.tonsPerKiloton *
    sourceInputs.tntEnergyGJPerTon * siExactConstants.joulesPerGigajoule

/-- First requested raw output: explosion energy divided by energy per
fission. -/
def totalFissionsRaw : ℝ := explosionEnergyJ / energyPerFissionJ

/-- Exact governing relation for the first requested output. -/
def TotalFissionsDerivationSpec : Prop :=
  SourceAssumptions ∧
    FissionEnergyDerivationSpec ∧
    0 < energyPerFissionJ ∧
    totalFissionsRaw = explosionEnergyJ / energyPerFissionJ ∧
    totalFissionsRaw * energyPerFissionJ = explosionEnergyJ

theorem totalFissionsDerivation : TotalFissionsDerivationSpec := by
  norm_num [TotalFissionsDerivationSpec, SourceAssumptions,
    FissionEnergyDerivationSpec, FissionNucleonLedger.ConservesNucleons,
    FissionNucleonLedger.boundProductNucleons, totalFissionsRaw,
    explosionEnergyJ, energyPerFissionJ, fissionEnergyMeV,
    sourceFissionLedger, uranium235, sourceInputs, siExactConstants]

/-- Mass of the uranium-235 nuclei which actually underwent fission. -/
def fissionedUranium235MassKg : ℝ :=
  totalFissionsRaw / siExactConstants.entitiesPerMole *
    sourceInputs.uranium235MolarMassKgPerMol

/-- Total uranium-235 inventory before the explosion. -/
def uranium235InventoryMassKg : ℝ :=
  fissionedUranium235MassKg / sourceInputs.uranium235FissionMassFraction

/-- Second requested raw output: total enriched-uranium mass. -/
def enrichedUraniumMassRawKg : ℝ :=
  uranium235InventoryMassKg /
    sourceInputs.uranium235EnrichmentMassFraction

/-- Atom-count/mole/mass bridge for the fissioned uranium-235. -/
def AtomCountMassLedger : Prop :=
  fissionedUranium235MassKg =
    totalFissionsRaw / siExactConstants.entitiesPerMole *
      sourceInputs.uranium235MolarMassKgPerMol

/-- The numerator is fissioned uranium-235 mass and the denominator is total
uranium-235 inventory mass. -/
def FissionFractionMassLedger : Prop :=
  fissionedUranium235MassKg =
    sourceInputs.uranium235FissionMassFraction * uranium235InventoryMassKg

/-- The numerator is uranium-235 inventory mass and the denominator is total
enriched-uranium mass. -/
def EnrichmentMassLedger : Prop :=
  uranium235InventoryMassKg =
    sourceInputs.uranium235EnrichmentMassFraction * enrichedUraniumMassRawKg

/-- Exact governing relations for the second requested output. -/
def EnrichedUraniumMassDerivationSpec : Prop :=
  SourceAssumptions ∧
    AtomCountMassLedger ∧
    FissionFractionMassLedger ∧
    EnrichmentMassLedger ∧
    enrichedUraniumMassRawKg =
      totalFissionsRaw * sourceInputs.uranium235MolarMassKgPerMol /
        (siExactConstants.entitiesPerMole *
          sourceInputs.uranium235FissionMassFraction *
          sourceInputs.uranium235EnrichmentMassFraction)

theorem enrichedUraniumMassDerivation :
    EnrichedUraniumMassDerivationSpec := by
  norm_num [EnrichedUraniumMassDerivationSpec, SourceAssumptions,
    AtomCountMassLedger, FissionFractionMassLedger, EnrichmentMassLedger,
    FissionNucleonLedger.ConservesNucleons,
    FissionNucleonLedger.boundProductNucleons, enrichedUraniumMassRawKg,
    uranium235InventoryMassKg, fissionedUranium235MassKg, totalFissionsRaw,
    explosionEnergyJ, energyPerFissionJ, fissionEnergyMeV,
    sourceFissionLedger, uranium235, sourceInputs, siExactConstants]

/-- Exact, unrounded forms of both requested scalar outputs, obtained only
after the source-derived governing relations above. -/
def ExactRawOutputValues : Prop :=
  totalFissionsRaw =
      (523000000000000000000000000000000000 : ℝ) / 123634630257 ∧
    enrichedUraniumMassRawKg =
      (30731480000000000000000 : ℝ) / 5528247710670201641751

/-- Complete raw mixed-output proposition. -/
def RawResult : Prop :=
  FissionEnergyDerivationSpec ∧
    TotalFissionsDerivationSpec ∧
    EnrichedUraniumMassDerivationSpec ∧
    ExactRawOutputValues

theorem rawResultSpec : RawResult := by
  refine ⟨fissionEnergyDerivation, totalFissionsDerivation,
    enrichedUraniumMassDerivation, ?_⟩
  norm_num [ExactRawOutputValues, enrichedUraniumMassRawKg,
    uranium235InventoryMassKg, fissionedUranium235MassKg, totalFissionsRaw,
    explosionEnergyJ, energyPerFissionJ, fissionEnergyMeV,
    FissionNucleonLedger.boundProductNucleons, sourceFissionLedger,
    uranium235, sourceInputs, siExactConstants]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"total_fissions","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"4.23e24","reporting_quantum":"1e22","raw_declaration":"IChO2026Problems.Icho2026T4A9.totalFissionsRaw","reporting_declaration":"IChO2026Problems.Icho2026T4A9.totalFissionsReportsAtQuantum"}
theorem totalFissionsReportsAtQuantum :
    ReportsAtQuantum totalFissionsRaw
      (4230000000000000000000000 : ℝ)
      (10000000000000000000000 : ℝ) := by
  refine ⟨by norm_num, ⟨423, by norm_num⟩, ?_⟩
  norm_num [totalFissionsRaw, explosionEnergyJ, energyPerFissionJ,
    fissionEnergyMeV, FissionNucleonLedger.boundProductNucleons,
    sourceFissionLedger, uranium235, sourceInputs, siExactConstants]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"enriched_uranium_mass","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"5.56","reporting_quantum":"0.01","raw_declaration":"IChO2026Problems.Icho2026T4A9.enrichedUraniumMassRawKg","reporting_declaration":"IChO2026Problems.Icho2026T4A9.enrichedUraniumMassReportsAtQuantum"}
theorem enrichedUraniumMassReportsAtQuantum :
    ReportsAtQuantum enrichedUraniumMassRawKg (139 / 25) (1 / 100) := by
  refine ⟨by norm_num, ⟨556, by norm_num⟩, ?_⟩
  norm_num [enrichedUraniumMassRawKg, uranium235InventoryMassKg,
    fissionedUranium235MassKg, totalFissionsRaw, explosionEnergyJ,
    energyPerFissionJ, fissionEnergyMeV,
    FissionNucleonLedger.boundProductNucleons, sourceFissionLedger,
    uranium235, sourceInputs, siExactConstants]

/-- Complete reported mixed-output proposition. -/
def ReportedResult : Prop :=
  RawResult ∧
    ReportsAtQuantum totalFissionsRaw
      (4230000000000000000000000 : ℝ)
      (10000000000000000000000 : ℝ) ∧
    ReportsAtQuantum enrichedUraniumMassRawKg (139 / 25) (1 / 100)

theorem reportedResultSpec : ReportedResult := by
  exact ⟨rawResultSpec, totalFissionsReportsAtQuantum,
    enrichedUraniumMassReportsAtQuantum⟩

/-- Payload-bound raw result contract for the answer-blind pipeline. -/
theorem rawResultContract :
    ("74f408870829e07dfc4efbc368f75b77e8576702a9bcb7baca2799e696e26ae5" : String) =
        "74f408870829e07dfc4efbc368f75b77e8576702a9bcb7baca2799e696e26ae5" ∧
      RawResult := by
  exact ⟨rfl, rawResultSpec⟩

/-- Payload-bound reported result contract for the answer-blind pipeline. -/
theorem reportedResultContract :
    ("84fbd4296c157debf437f501ff498f103d1fd9156fc43b626fb1504c02f13c3b" : String) =
        "84fbd4296c157debf437f501ff498f103d1fd9156fc43b626fb1504c02f13c3b" ∧
      ReportedResult := by
  exact ⟨rfl, reportedResultSpec⟩

end

end IChO2026Problems.Icho2026T4A9
