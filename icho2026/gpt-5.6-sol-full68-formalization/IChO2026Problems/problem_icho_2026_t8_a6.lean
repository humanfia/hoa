import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T8-A6

This file formalizes the source-side calculation of the quantum yield for CO
formation.  All displayed experimental inputs are treated as the exact
contest values stipulated in the problem.  The raw calculation is kept apart
from the final three-significant-figure reporting relation.

The mass fraction is interpreted in its usual sense: catalyst mass divided by
the total mass of catalyst plus support.  Thus the stated `10 mg of C3N4` is
the support mass, not the total composite mass.
-/

namespace IChO2026Problems.ProblemIcho2026T8A6

noncomputable section

/-! ## Source inputs and exact SI conversion factors -/

/-- Catalyst mass divided by total loaded-sample mass: `3.8 %`. -/
def catalystMassFraction : ℝ := (38 : ℝ) / 1000

/-- Mass of C3N4 support in the irradiated sample, in grams: `10 mg`. -/
def supportMassG : ℝ := (10 : ℝ) / 1000

/-- Molar mass of molecular catalyst 1, in grams per mole. -/
def catalystMolarMassGPerMol : ℝ := (55721 : ℝ) / 100

/-- Specific surface area of the C3N4 support, in square metres per gram. -/
def specificSurfaceAreaM2PerG : ℝ := (178 : ℝ) / 10

/-- Exact conversion from square metres to square nanometres. -/
def nmSquaredPerMSquared : ℝ := (10 : ℝ) ^ 18

/-- Exact SI Avogadro constant, in reciprocal moles. -/
def avogadroConstantPerMol : ℝ := (602214076 : ℝ) * (10 : ℝ) ^ 15

/-- Turnover frequency for formation of CO molecules, in reciprocal hours. -/
def coTurnoverFrequencyPerHour : ℝ := 8

/-- Common observation window used for the reaction and photon counts. -/
def observationDurationHours : ℝ := 1

/-- Exact conversion of hours to seconds. -/
def secondsPerHour : ℝ := 3600

/-- Incident LED power, in watts: `50 mW`. -/
def ledPowerW : ℝ := (50 : ℝ) / 1000

/-- Incident wavelength, in metres: `390 nm`. -/
def ledWavelengthM : ℝ := (390 : ℝ) / (10 : ℝ) ^ 9

/-- Exact SI Planck constant, in joule seconds. -/
def planckConstantJouleSecond : ℝ :=
  (662607015 : ℝ) / (10 : ℝ) ^ 42

/-- Exact speed of light in vacuum, in metres per second. -/
def speedOfLightMPerSecond : ℝ := 299792458

/-! ## Catalyst-loading mass balance -/

/-- The three explicitly tracked masses for the loaded photocatalyst sample. -/
structure LoadedSampleMassLedger where
  supportMassG : ℝ
  catalystMassG : ℝ
  totalLoadedMassG : ℝ

/-- The catalyst mass obtained by solving
`w = m_cat / (m_cat + m_support)` for `m_cat`. -/
def derivedCatalystMassG : ℝ :=
  catalystMassFraction / (1 - catalystMassFraction) * supportMassG

/-- The mass ledger for the sample irradiated in T8-A6. -/
def irradiatedSampleMassLedger : LoadedSampleMassLedger where
  supportMassG := supportMassG
  catalystMassG := derivedCatalystMassG
  totalLoadedMassG := supportMassG + derivedCatalystMassG

/-- A valid loading ledger makes the numerator and denominator of the stated
mass fraction explicit and admits no untracked mass component. -/
def ValidLoadedSampleMassLedger (s : LoadedSampleMassLedger) : Prop :=
  0 < s.supportMassG ∧
  0 ≤ s.catalystMassG ∧
  s.totalLoadedMassG = s.supportMassG + s.catalystMassG ∧
  0 < s.totalLoadedMassG ∧
  catalystMassFraction = s.catalystMassG / s.totalLoadedMassG

/-- The source values and the solved catalyst mass satisfy the total-mixture
mass-fraction ledger. -/
theorem irradiatedSampleMassLedger_spec :
    ValidLoadedSampleMassLedger irradiatedSampleMassLedger := by
  norm_num [ValidLoadedSampleMassLedger, irradiatedSampleMassLedger,
    derivedCatalystMassG, catalystMassFraction, supportMassG]

/-! ## Inline derivation of the T8-A5 surface count -/

/-- Area and molecular-count ledger used to derive the previous-part surface
density without importing a result from another generated problem file. -/
structure A5SurfaceCountLedger where
  totalSupportAreaNm2 : ℝ
  catalystMoleculeCount : ℝ
  catalystMoleculesPerNm2 : ℝ

/-- Total C3N4 surface area of the 10 mg support sample, in square nanometres. -/
def totalSupportAreaNm2 : ℝ :=
  supportMassG * specificSurfaceAreaM2PerG * nmSquaredPerMSquared

/-- Number of molecular-catalyst molecules loaded on the sample. -/
def loadedCatalystMoleculeCount : ℝ :=
  derivedCatalystMassG / catalystMolarMassGPerMol * avogadroConstantPerMol

/-- Inline T8-A5 result carrier: loaded catalyst molecules per square
nanometre of C3N4. -/
def catalystMoleculesPerNm2 : ℝ :=
  loadedCatalystMoleculeCount / totalSupportAreaNm2

/-- The concrete surface ledger used in this part. -/
def a5SurfaceCountLedger : A5SurfaceCountLedger where
  totalSupportAreaNm2 := totalSupportAreaNm2
  catalystMoleculeCount := loadedCatalystMoleculeCount
  catalystMoleculesPerNm2 := catalystMoleculesPerNm2

/-- Governing relations for the inline T8-A5 derivation. -/
def ValidA5SurfaceCountLedger
    (mass : LoadedSampleMassLedger) (surface : A5SurfaceCountLedger) : Prop :=
  surface.totalSupportAreaNm2 =
      mass.supportMassG * specificSurfaceAreaM2PerG * nmSquaredPerMSquared ∧
  surface.catalystMoleculeCount =
      mass.catalystMassG / catalystMolarMassGPerMol * avogadroConstantPerMol ∧
  0 < surface.totalSupportAreaNm2 ∧
  surface.catalystMoleculesPerNm2 =
      surface.catalystMoleculeCount / surface.totalSupportAreaNm2

/-- The previous-part surface density is derived entirely from the printed
mass fraction, support mass, specific area, molar mass, and Avogadro constant. -/
theorem a5SurfaceCountLedger_spec :
    ValidA5SurfaceCountLedger irradiatedSampleMassLedger a5SurfaceCountLedger := by
  norm_num [ValidA5SurfaceCountLedger, a5SurfaceCountLedger,
    irradiatedSampleMassLedger, totalSupportAreaNm2,
    loadedCatalystMoleculeCount, catalystMoleculesPerNm2,
    derivedCatalystMassG, catalystMassFraction, supportMassG,
    catalystMolarMassGPerMol, specificSurfaceAreaM2PerG,
    nmSquaredPerMSquared, avogadroConstantPerMol]

/-! ## Electron count read from the depicted catalytic cycle -/

/-- The seven explicitly labelled intermediate states in the closed catalytic
cycle.  Catalyst precursor 1 is an external input to state 9, not an eighth
cycle state. -/
inductive CatalyticCycleState where
  | species9
  | species10
  | species11
  | species12
  | species13
  | species14
  | species15
  deriving DecidableEq, Fintype

/-- Finite source-labelled state domain used for the diagram audit. -/
def stagedCycleStateDomain : Finset CatalyticCycleState := Finset.univ

/-- The source diagram contains exactly the seven states 9 through 15. -/
theorem stagedCycleStateDomain_spec :
    stagedCycleStateDomain.card = 7 ∧
    ∀ state : CatalyticCycleState, state ∈ stagedCycleStateDomain := by
  native_decide

/-- An outcome-decisive directed edge records only the electron input and CO
output counts used by A6; it makes no assertion about omitted mechanistic
details or yields. -/
structure OutcomeDecisiveCycleEdge where
  source : CatalyticCycleState
  target : CatalyticCycleState
  incomingElectronCount : ℕ
  releasedCOCount : ℕ

/-- The first photoinduced one-electron arrow, from 9 to 10. -/
def species9To10ReductionEdge : OutcomeDecisiveCycleEdge where
  source := .species9
  target := .species10
  incomingElectronCount := 1
  releasedCOCount := 0

/-- The second photoinduced one-electron arrow, from 11 to 12. -/
def species11To12ReductionEdge : OutcomeDecisiveCycleEdge where
  source := .species11
  target := .species12
  incomingElectronCount := 1
  releasedCOCount := 0

/-- The depicted release of one CO molecule, from 14 to 15. -/
def species14To15COReleaseEdge : OutcomeDecisiveCycleEdge where
  source := .species14
  target := .species15
  incomingElectronCount := 0
  releasedCOCount := 1

/-- Source-first count of the two one-electron uptake arrows and the one CO
release arrow in the cycle on `T8_page-2.png`. -/
structure CatalyticCycleElectronLedger where
  species9To10Electrons : ℕ
  species11To12Electrons : ℕ
  species14To15COMolecules : ℕ

/-- The diagram labels both reduction arrows with `+1e-` and the product arrow
with loss of one CO molecule. -/
def sourceCycleElectronLedger : CatalyticCycleElectronLedger where
  species9To10Electrons := species9To10ReductionEdge.incomingElectronCount
  species11To12Electrons := species11To12ReductionEdge.incomingElectronCount
  species14To15COMolecules := species14To15COReleaseEdge.releasedCOCount

/-- Exact electron-to-CO ratio represented by a cycle ledger. -/
def electronsPerCOMolecule (cycle : CatalyticCycleElectronLedger) : ℝ :=
  ((cycle.species9To10Electrons : ℝ) +
      (cycle.species11To12Electrons : ℝ)) /
    (cycle.species14To15COMolecules : ℝ)

/-- The relevant T8-A4 mechanism information is two reacted electrons for
each CO molecule released. -/
theorem sourceCycleElectronLedger_spec :
    sourceCycleElectronLedger.species9To10Electrons = 1 ∧
    sourceCycleElectronLedger.species11To12Electrons = 1 ∧
    sourceCycleElectronLedger.species14To15COMolecules = 1 ∧
    electronsPerCOMolecule sourceCycleElectronLedger = 2 := by
  norm_num [sourceCycleElectronLedger, species9To10ReductionEdge,
    species11To12ReductionEdge, species14To15COReleaseEdge,
    electronsPerCOMolecule]

/-! ## One-hour reaction and photon ledgers -/

/-- Molecular counts on the reaction side of the quantum-yield ratio. -/
structure OneHourReactionLedger where
  tofReferenceCatalystMoleculeCount : ℝ
  coMoleculeCount : ℝ
  reactedElectronCount : ℝ

/-- The catalyst count reconstructed from the inline A5 surface density and
the surface area of the same 10 mg sample. -/
def tofReferenceCatalystMoleculeCount : ℝ :=
  a5SurfaceCountLedger.catalystMoleculesPerNm2 *
    a5SurfaceCountLedger.totalSupportAreaNm2

/-- Number of CO molecules formed in the common one-hour window. -/
def coMoleculeCountInObservation : ℝ :=
  coTurnoverFrequencyPerHour * observationDurationHours *
    tofReferenceCatalystMoleculeCount

/-- Number of reacted electrons corresponding to the CO formed. -/
def reactedElectronCountInObservation : ℝ :=
  electronsPerCOMolecule sourceCycleElectronLedger *
    coMoleculeCountInObservation

/-- Reaction-side ledger for the one-hour observation. -/
def oneHourReactionLedger : OneHourReactionLedger where
  tofReferenceCatalystMoleculeCount := tofReferenceCatalystMoleculeCount
  coMoleculeCount := coMoleculeCountInObservation
  reactedElectronCount := reactedElectronCountInObservation

/-- The TOF definition and the electron-per-CO diagram count govern the
reaction-side ledger. -/
def ValidOneHourReactionLedger
    (surface : A5SurfaceCountLedger)
    (cycle : CatalyticCycleElectronLedger)
    (reaction : OneHourReactionLedger) : Prop :=
  reaction.tofReferenceCatalystMoleculeCount =
      surface.catalystMoleculesPerNm2 * surface.totalSupportAreaNm2 ∧
  reaction.coMoleculeCount =
      coTurnoverFrequencyPerHour * observationDurationHours *
        reaction.tofReferenceCatalystMoleculeCount ∧
  reaction.reactedElectronCount =
      electronsPerCOMolecule cycle * reaction.coMoleculeCount

/-- Photon-energy and incident-photon counts for the same observation window. -/
structure OneHourPhotonLedger where
  elapsedSeconds : ℝ
  singlePhotonEnergyJ : ℝ
  incidentPhotonCount : ℝ

/-- Energy of one 390 nm photon, using the general law `E = h*c/lambda`. -/
def singlePhotonEnergyJ : ℝ :=
  planckConstantJouleSecond * speedOfLightMPerSecond / ledWavelengthM

/-- Number of photons incident during the common one-hour observation. -/
def incidentPhotonCountInObservation : ℝ :=
  ledPowerW * (observationDurationHours * secondsPerHour) /
    singlePhotonEnergyJ

/-- Photon-side ledger for the one-hour observation. -/
def oneHourPhotonLedger : OneHourPhotonLedger where
  elapsedSeconds := observationDurationHours * secondsPerHour
  singlePhotonEnergyJ := singlePhotonEnergyJ
  incidentPhotonCount := incidentPhotonCountInObservation

/-- The power-time energy balance and `E = h*c/lambda` govern the photon
ledger. -/
def ValidOneHourPhotonLedger (photons : OneHourPhotonLedger) : Prop :=
  photons.elapsedSeconds = observationDurationHours * secondsPerHour ∧
  photons.singlePhotonEnergyJ =
      planckConstantJouleSecond * speedOfLightMPerSecond / ledWavelengthM ∧
  0 < photons.singlePhotonEnergyJ ∧
  photons.incidentPhotonCount =
      ledPowerW * photons.elapsedSeconds / photons.singlePhotonEnergyJ ∧
  0 < photons.incidentPhotonCount

/-! ## Raw and reported quantum yield -/

/-- Exact, unrounded quantum yield in percent, as specified by the printed
electron-count / incident-photon-count formula. -/
def coQuantumYieldPercent : ℝ :=
  oneHourReactionLedger.reactedElectronCount /
      oneHourPhotonLedger.incidentPhotonCount * 100

/-- Complete source-to-raw-value specification.  It includes the loading mass
balance, the inline previous-part count, the diagram electron ledger, the TOF
relation, the photon-energy law, and the printed quantum-yield formula. -/
def CoQuantumYieldDerivationSpec : Prop :=
  ValidLoadedSampleMassLedger irradiatedSampleMassLedger ∧
  ValidA5SurfaceCountLedger irradiatedSampleMassLedger a5SurfaceCountLedger ∧
  electronsPerCOMolecule sourceCycleElectronLedger = 2 ∧
  ValidOneHourReactionLedger
    a5SurfaceCountLedger sourceCycleElectronLedger oneHourReactionLedger ∧
  ValidOneHourPhotonLedger oneHourPhotonLedger ∧
  coQuantumYieldPercent =
    oneHourReactionLedger.reactedElectronCount /
      oneHourPhotonLedger.incidentPhotonCount * 100

/-- Exact rational normal form of the source-derived raw expression. -/
def coQuantumYieldExactRational : ℝ :=
  (18940872892793693114789369 : ℝ) /
    9799408490625000000000000

/-- A mechanically checkable decimal enclosure of the exact rational raw
value; it is an arithmetic certificate, not a measurement tolerance. -/
def coQuantumYieldLowerBound : ℝ := (19328 : ℝ) / 10000

/-- Upper endpoint of the nondegenerate arithmetic enclosure. -/
def coQuantumYieldUpperBound : ℝ := (19329 : ℝ) / 10000

/-- Exact evaluation of the source-derived raw expression.  This theorem is
kept separate from the machine-readable interval contract: the candidate
record's rational value is only an interval witness, while this Lean theorem
certifies the stronger equality available for this fully rational example. -/
theorem coQuantumYieldExact :
    coQuantumYieldPercent = coQuantumYieldExactRational := by
  norm_num [coQuantumYieldPercent, oneHourReactionLedger,
    reactedElectronCountInObservation, electronsPerCOMolecule,
    sourceCycleElectronLedger, species9To10ReductionEdge,
    species11To12ReductionEdge, species14To15COReleaseEdge,
    coMoleculeCountInObservation, coTurnoverFrequencyPerHour,
    observationDurationHours, tofReferenceCatalystMoleculeCount,
    a5SurfaceCountLedger, catalystMoleculesPerNm2,
    loadedCatalystMoleculeCount, derivedCatalystMassG,
    catalystMassFraction, supportMassG, catalystMolarMassGPerMol,
    avogadroConstantPerMol, totalSupportAreaNm2,
    specificSurfaceAreaM2PerG, nmSquaredPerMSquared,
    oneHourPhotonLedger, incidentPhotonCountInObservation,
    ledPowerW, secondsPerHour, singlePhotonEnergyJ,
    planckConstantJouleSecond, speedOfLightMPerSecond,
    ledWavelengthM, coQuantumYieldExactRational]

/-- Raw result contract in the exact shape generated by the trusted
answer-blind helper: the governing derivation holds and the unrounded quantity
lies in a closed, nondegenerate arithmetic enclosure. -/
theorem coQuantumYieldRawResult :
    CoQuantumYieldDerivationSpec ∧
    ((1208 : ℝ) / 625 ≤ coQuantumYieldPercent ∧
      coQuantumYieldPercent ≤ (19329 : ℝ) / 10000) := by
  constructor
  · norm_num [CoQuantumYieldDerivationSpec, ValidLoadedSampleMassLedger,
      irradiatedSampleMassLedger, ValidA5SurfaceCountLedger,
      a5SurfaceCountLedger, ValidOneHourReactionLedger,
      oneHourReactionLedger, ValidOneHourPhotonLedger,
      oneHourPhotonLedger, derivedCatalystMassG, catalystMassFraction,
      supportMassG, totalSupportAreaNm2, loadedCatalystMoleculeCount,
      catalystMoleculesPerNm2, catalystMolarMassGPerMol,
      specificSurfaceAreaM2PerG, nmSquaredPerMSquared,
      avogadroConstantPerMol, tofReferenceCatalystMoleculeCount,
      coMoleculeCountInObservation, coTurnoverFrequencyPerHour,
      observationDurationHours, reactedElectronCountInObservation,
      electronsPerCOMolecule, sourceCycleElectronLedger,
      species9To10ReductionEdge, species11To12ReductionEdge,
      species14To15COReleaseEdge, singlePhotonEnergyJ,
      planckConstantJouleSecond, speedOfLightMPerSecond,
      ledWavelengthM, incidentPhotonCountInObservation, ledPowerW,
      secondsPerHour, coQuantumYieldPercent]
  · rw [coQuantumYieldExact]
    norm_num [coQuantumYieldExactRational]

/-- The raw value is in the unit decade, so three significant figures use a
hundredth-of-a-percent reporting quantum. -/
theorem coQuantumYieldMagnitudeForReporting :
    1 ≤ coQuantumYieldPercent ∧ coQuantumYieldPercent < 10 := by
  rw [coQuantumYieldExact]
  norm_num [coQuantumYieldExactRational]

/-- Three-significant-figure reporting quantum for this raw magnitude. -/
def coQuantumYieldReportingQuantumPercent : ℝ := (1 : ℝ) / 100

/-- Candidate final displayed value, in percent. -/
def coQuantumYieldReportedPercent : ℝ := (193 : ℝ) / 100

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"co_quantum_yield","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"1.93","reporting_quantum":"1/100","raw_declaration":"IChO2026Problems.ProblemIcho2026T8A6.coQuantumYieldPercent","reporting_declaration":"IChO2026Problems.ProblemIcho2026T8A6.coQuantumYieldReportedResult"}

/-- Reported result contract, using the project-wide half-away-from-zero
nearest-quantum relation fixed before this problem was solved. -/
theorem coQuantumYieldReportedResult :
    IChO2026Chem.Reporting.ReportsAtQuantum
      coQuantumYieldPercent
      ((193 : ℝ) / 100)
      ((1 : ℝ) / 100) := by
  rw [coQuantumYieldExact]
  norm_num [IChO2026Chem.Reporting.ReportsAtQuantum,
    coQuantumYieldExactRational]
  exact ⟨193, by norm_num⟩

end

end IChO2026Problems.ProblemIcho2026T8A6
