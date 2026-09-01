import Mathlib
import Physlib.Units.WithDim.Energy

/-!
# IChO 2026 T6.3: carbon-nanoring precursor halogen

The problem gives four C–X bond dissociation energies and an electron accelerated
through `2.5 V`.  This file keeps the four printed candidates as the complete
source domain, converts the single-electron energy to `kJ mol⁻¹` without
rounding, and filters the candidates by the transparent energy-threshold rule.
-/

namespace IChO2026Problems.ProblemIcho2026T6A3

/-- The complete candidate domain printed in the C–X bond-energy table. -/
inductive Halogen where
  | fluorine
  | chlorine
  | bromine
  | iodine
  deriving DecidableEq, Fintype, Repr

/-- Exact scalar values carrying volts. -/
abbrev Volts := ℚ

/-- Exact scalar values carrying electron-volts per electron. -/
abbrev ElectronVoltsPerElectron := ℚ

/-- Exact scalar values carrying kilojoules per mole. -/
abbrev KilojoulesPerMole := ℚ

/-- The source-named synthesis route.  No material balance for the route is
used in this subquestion. -/
inductive SynthesisRoute where
  | afmMediatedRetroBergmanOnSurface
  deriving DecidableEq, Repr

/-- The source conditions that identify the synthesis discussed in T6.3. -/
structure SynthesisContext where
  productCarbonAtoms : ℕ
  route : SynthesisRoute
  appliedVoltage : Volts

/-- The `C₁₈`, retro-Bergman, `2.5 V` context printed in the question. -/
def sourceContext : SynthesisContext where
  productCarbonAtoms := 18
  route := .afmMediatedRetroBergmanOnSurface
  appliedVoltage := 5 / 2

/-- All and only the four halogens for which the problem supplies C–X data.
Provenance: `problem_text` and the table in `T6_page-2.png`. -/
def candidateHalogens : Finset Halogen := Finset.univ

/-- The printed C–X bond dissociation energy table, in `kJ mol⁻¹`. -/
def bondDissociationEnergy : Halogen → KilojoulesPerMole
  | .fluorine => 467
  | .chlorine => 346
  | .bromine => 290
  | .iodine => 228

/-- A non-opaque carrier for all four entries in the source table. -/
def SourceBondEnergyTable : Prop :=
  bondDissociationEnergy .fluorine = 467 ∧
  bondDissociationEnergy .chlorine = 346 ∧
  bondDissociationEnergy .bromine = 290 ∧
  bondDissociationEnergy .iodine = 228

theorem sourceBondEnergyTable : SourceBondEnergyTable := by
  simp [SourceBondEnergyTable, bondDissociationEnergy]

/-- The magnitude of an electron's charge in units of the elementary charge. -/
def electronChargeMagnitudeInElementaryCharges : ℚ := 1

/-- Energy gained by a particle, in eV per particle, from its charge magnitude
and the potential difference through which it is accelerated. -/
def energyFromPotential
    (chargeMagnitudeInElementaryCharges : ℚ) (potential : Volts) :
    ElectronVoltsPerElectron :=
  chargeMagnitudeInElementaryCharges * potential

/-- Exact SI conversion data used to put a single-particle electron-volt on the
same molar scale as the printed bond energies. -/
structure ElectronVoltMolarConversion where
  joulesPerElectronVoltPerParticle : ℚ
  particlesPerMole : ℚ
  joulesPerKilojoule : ℚ

/-- Conventional exact SI data: `1 eV = 1.602176634·10⁻¹⁹ J` per particle
and `Nₐ = 6.02214076·10²³ mol⁻¹`.  Physlib's `DimEnergy.electronVolt`
uses the same exact joule value; Physlib has no molar-energy conversion API.
The two exact constants were independently checked against the NIST Reference
on Constants, Units and Uncertainty, 2022 CODATA value pages `Value?e` and
`Value?na` (their "Numerical value" and "Standard uncertainty" rows). -/
def siElectronVoltMolarConversion : ElectronVoltMolarConversion where
  joulesPerElectronVoltPerParticle := 1602176634 / 10 ^ 28
  particlesPerMole := 602214076 * 10 ^ 15
  joulesPerKilojoule := 1000

/-- The Physlib carrier whose documented SI value agrees with the first field
of `siElectronVoltMolarConversion`. -/
noncomputable def physlibElectronVolt : DimEnergy := DimEnergy.electronVolt

/-- Convert exact electron-volts per particle to exact kilojoules per mole. -/
def electronVoltsToKilojoulesPerMole
    (conversion : ElectronVoltMolarConversion)
    (energy : ElectronVoltsPerElectron) : KilojoulesPerMole :=
  energy * conversion.joulesPerElectronVoltPerParticle *
      conversion.particlesPerMole / conversion.joulesPerKilojoule

/-- The unrounded molar energy supplied by the `2.5 V` electron. -/
def availableElectronEnergy : KilojoulesPerMole :=
  electronVoltsToKilojoulesPerMole siElectronVoltMolarConversion
    (energyFromPotential electronChargeMagnitudeInElementaryCharges
      sourceContext.appliedVoltage)

/-- The complete, unrounded source-to-energy derivation. -/
def AvailableElectronEnergyDerivation : Prop :=
  availableElectronEnergy =
    (1 * (5 / 2)) * (1602176634 / 10 ^ 28) *
      (602214076 * 10 ^ 15) / 1000

theorem availableElectronEnergy_derivation :
    AvailableElectronEnergyDerivation := by
  rfl

/-- Bounds sufficient to compare the electron energy with the two closest
printed bond energies.  They retain the exact expression above and introduce
no reporting tolerance. -/
def AvailableElectronEnergySeparatesCandidates : Prop :=
  (228 : ℚ) ≤ availableElectronEnergy ∧ availableElectronEnergy < 290

theorem availableElectronEnergy_separatesCandidates :
    AvailableElectronEnergySeparatesCandidates := by
  norm_num [AvailableElectronEnergySeparatesCandidates,
    availableElectronEnergy, electronVoltsToKilojoulesPerMole,
    siElectronVoltMolarConversion, energyFromPotential,
    electronChargeMagnitudeInElementaryCharges, sourceContext]

/-- The transparent threshold model requested by "using the given C–X bond
energies": a supplied electron can cleave a listed bond when its molar energy
is at least that bond's dissociation energy. -/
def energeticallyCleavable (halogen : Halogen) : Prop :=
  bondDissociationEnergy halogen ≤ availableElectronEnergy

/-- The candidate is derived by applying the same threshold to every entry of
the source-provided domain. -/
def possibleHalogens : Finset Halogen :=
  candidateHalogens.filter fun halogen =>
    bondDissociationEnergy halogen ≤ availableElectronEnergy

/-- Specification of the uniform source-domain filter, independent of the
eventual selected constructor. -/
def PossibleHalogensFilterSpecification : Prop :=
  ∀ halogen : Halogen,
    halogen ∈ possibleHalogens ↔
      halogen ∈ candidateHalogens ∧
        bondDissociationEnergy halogen ≤ availableElectronEnergy

theorem possibleHalogens_filterSpecification :
    PossibleHalogensFilterSpecification := by
  intro halogen
  simp [possibleHalogens, candidateHalogens]

/-- Raw exact-symbolic result for the requested finite set.  The singleton is
the conclusion of the uniform four-candidate audit, not an input domain. -/
def PossibleHalogensRawResult : Prop :=
  possibleHalogens = ({Halogen.iodine} : Finset Halogen)

/-- Reported exact-symbolic result; exact symbolic outputs undergo no numeric
rounding. -/
def PossibleHalogensReportedResult : Prop :=
  ∀ halogen : Halogen, halogen ∈ possibleHalogens ↔ halogen = .iodine

theorem possibleHalogens_rawResult : PossibleHalogensRawResult := by
  ext halogen
  cases halogen <;>
    norm_num [PossibleHalogensRawResult, possibleHalogens, candidateHalogens,
      bondDissociationEnergy, availableElectronEnergy,
      electronVoltsToKilojoulesPerMole, siElectronVoltMolarConversion,
      energyFromPotential, electronChargeMagnitudeInElementaryCharges,
      sourceContext] <;>
    simp

theorem possibleHalogens_reportedResult : PossibleHalogensReportedResult := by
  intro halogen
  rw [show possibleHalogens = ({Halogen.iodine} : Finset Halogen) from
    possibleHalogens_rawResult]
  simp

end IChO2026Problems.ProblemIcho2026T6A3
