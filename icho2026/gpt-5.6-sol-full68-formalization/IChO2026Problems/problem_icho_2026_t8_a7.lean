import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem 8, part A7

This file formalizes the source-side calculation behind the qualitative trend
of the CO formation rate per gram of C₃N₄ support.  The plotted turnover
frequency is a rate per active catalyst molecule, so it is multiplied by the
number of catalyst molecules per gram of support.

The problem calls `ωcat` a mass fraction.  Accordingly, `ωcat / 100` is modeled
as catalyst mass divided by total loaded-sample mass
`catalyst mass + C₃N₄ mass`; it is not modeled as catalyst mass divided by
support mass.
-/

namespace IChO2026Problems
namespace T8A7

noncomputable section

/-- Chemical entities whose identities matter to the rate statement and to the
inline A1/A5/A6 derivations. -/
inductive ChemicalEntity where
  | catalystOne
  | carbonNitrideSupport
  | carbonDioxide
  | carbonMonoxide
  | proton
  | electron
  | water
  | photon
  deriving DecidableEq, Repr

inductive ChemicalPhase where
  | solid
  | gas
  | aqueous
  | unspecified
  deriving DecidableEq, Repr

inductive RateMassBasis where
  | perGramSupport
  | perGramTotalLoadedSample
  deriving DecidableEq, Repr

/-- Entity-level interpretation of the scalar A7 rate. -/
structure COFormationRateContext where
  product : ChemicalEntity
  support : ChemicalEntity
  activeCatalyst : ChemicalEntity
  supportPhase : ChemicalPhase
  massBasis : RateMassBasis

def sourceRateContext : COFormationRateContext where
  product := .carbonMonoxide
  support := .carbonNitrideSupport
  activeCatalyst := .catalystOne
  supportPhase := .solid
  massBasis := .perGramSupport

/-- Source carrier keeping CO, catalyst 1, and crystalline C₃N₄ distinct from
their numerical rate readouts. -/
def SourceChemicalContext : Prop :=
  sourceRateContext.product = .carbonMonoxide ∧
  sourceRateContext.support = .carbonNitrideSupport ∧
  sourceRateContext.activeCatalyst = .catalystOne ∧
  sourceRateContext.supportPhase = .solid ∧
  sourceRateContext.massBasis = .perGramSupport

/-- The three classifications printed in part A7. -/
inductive CoRateTrend where
  | increases
  | decreases
  | doesNotChange
  deriving DecidableEq, Repr

/-- One red point in the source plot.  The first field is `ωcat` in percent and
the second is CO TOF in inverse hours. -/
structure TOFObservation where
  loadingPercent : ℝ
  tofPerHour : ℝ

/-- The seven labeled points read from `T8_page-3.png`, in increasing loading
order. -/
def sourceGraph : Fin 7 → TOFObservation :=
  ![⟨(1 : ℝ) / 10, 62⟩,
    ⟨(3 : ℝ) / 10, 56⟩,
    ⟨(6 : ℝ) / 10, 37⟩,
    ⟨(1 : ℝ), 29⟩,
    ⟨(2 : ℝ), 15⟩,
    ⟨(29 : ℝ) / 10, 11⟩,
    ⟨(38 : ℝ) / 10, 8⟩]

/-- An explicit carrier for every labeled plot readout. -/
def SourceGraphReadout : Prop :=
  sourceGraph 0 = ⟨(1 : ℝ) / 10, 62⟩ ∧
  sourceGraph 1 = ⟨(3 : ℝ) / 10, 56⟩ ∧
  sourceGraph 2 = ⟨(6 : ℝ) / 10, 37⟩ ∧
  sourceGraph 3 = ⟨(1 : ℝ), 29⟩ ∧
  sourceGraph 4 = ⟨(2 : ℝ), 15⟩ ∧
  sourceGraph 5 = ⟨(29 : ℝ) / 10, 11⟩ ∧
  sourceGraph 6 = ⟨(38 : ℝ) / 10, 8⟩

/-- `ωPercent` uses the total-mixture convention
`100 * catalystMass / (catalystMass + supportMass)`.

Masses are in the same unit; the positivity clauses make the denominator a
genuine loaded sample. -/
def CatalystMassPercentOnTotalSample
    (ωPercent catalystMass supportMass : ℝ) : Prop :=
  0 ≤ catalystMass ∧
  0 < supportMass ∧
  ωPercent / 100 = catalystMass / (catalystMass + supportMass)

/-- Catalyst mass divided by support mass, obtained by solving the preceding
total-mixture mass-fraction equation. -/
def catalystToSupportMassRatio (ωPercent : ℝ) : ℝ :=
  (ωPercent / 100) / (1 - ωPercent / 100)

/-- Algebraic bridge from the stated mass-fraction basis to the catalyst mass
per unit support mass used in A5--A7. -/
theorem catalystToSupportMassRatio_of_totalSampleFraction
    {ωPercent catalystMass supportMass : ℝ}
    (hFraction : CatalystMassPercentOnTotalSample
      ωPercent catalystMass supportMass)
    (hLoading : ωPercent < 100) :
    catalystMass / supportMass = catalystToSupportMassRatio ωPercent := by
  rcases hFraction with ⟨hCatalystMass, hSupportMass, hFraction⟩
  have hTotalMass : catalystMass + supportMass ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos hCatalystMass hSupportMass)
  have hSupportMassNe : supportMass ≠ 0 := ne_of_gt hSupportMass
  have hLoadingDenominator : 1 - ωPercent / 100 ≠ 0 :=
    ne_of_gt (by nlinarith)
  unfold catalystToSupportMassRatio
  rw [eq_div_iff hLoadingDenominator, hFraction]
  field_simp
  ring

/-! ## Earlier-part quantities derived locally -/

/-- Exact SI defining value, in entities per mole. -/
def avogadroConstantPerMol : ℝ :=
  (602214076 : ℝ) * (10 : ℝ) ^ 15

/-- The molar mass of catalyst 1 printed in A5, in grams per mole. -/
def catalystMolarMassGPerMol : ℝ := (55721 : ℝ) / 100

/-- Catalyst molecules per gram of C₃N₄ support at a given total-sample mass
percentage. -/
def catalystMoleculesPerGramSupport (ωPercent : ℝ) : ℝ :=
  catalystToSupportMassRatio ωPercent /
      catalystMolarMassGPerMol * avogadroConstantPerMol

/-- A5's exact number of catalyst molecules per square nanometre.  The factor
`10^18` converts square metres to square nanometres. -/
def catalystMoleculesPerNm2
    (ωPercent specificSurfaceAreaM2PerG : ℝ) : ℝ :=
  catalystMoleculesPerGramSupport ωPercent /
    (specificSurfaceAreaM2PerG * (10 : ℝ) ^ 18)

def a5LoadingPercent : ℝ := (38 : ℝ) / 10

def a5SpecificSurfaceAreaM2PerG : ℝ := (178 : ℝ) / 10

/-- Catalyst mass, in grams, accompanying one gram of support under the A5
mass-fraction convention. -/
def a5CatalystMassForOneGramSupport : ℝ :=
  catalystToSupportMassRatio a5LoadingPercent

/-- The total-mixture mass ledger required before the A5 substitution. -/
def A5MassBalanceSpec : Prop :=
  CatalystMassPercentOnTotalSample
    a5LoadingPercent a5CatalystMassForOneGramSupport 1

def a5RawCatalystMoleculesPerNm2 : ℝ :=
  catalystMoleculesPerNm2 a5LoadingPercent a5SpecificSurfaceAreaM2PerG

/-- Exact, unrounded A5 result derived from the printed loading, area, and
molar mass, with the mass-fraction denominator made explicit. -/
def A5RawDerivation : Prop :=
  A5MassBalanceSpec ∧
  a5RawCatalystMoleculesPerNm2 =
    (5721033722 : ℝ) / 2385360289

/-- A5 reported at the project default of three significant figures. -/
def A5ReportedDerivation : Prop :=
  A5RawDerivation ∧
  IChO2026Chem.Reporting.ReportsAtQuantum
    a5RawCatalystMoleculesPerNm2 ((240 : ℝ) / 100) ((1 : ℝ) / 100)

theorem deriveA5FromPrintedData : A5ReportedDerivation := by
  have hMassBalance : A5MassBalanceSpec := by
    norm_num [A5MassBalanceSpec, CatalystMassPercentOnTotalSample,
      a5CatalystMassForOneGramSupport, catalystToSupportMassRatio,
      a5LoadingPercent]
  have hRaw :
      a5RawCatalystMoleculesPerNm2 =
        (5721033722 : ℝ) / 2385360289 := by
    norm_num [a5RawCatalystMoleculesPerNm2, catalystMoleculesPerNm2,
      catalystMoleculesPerGramSupport, catalystToSupportMassRatio,
      catalystMolarMassGPerMol, avogadroConstantPerMol, a5LoadingPercent,
      a5SpecificSurfaceAreaM2PerG]
  refine ⟨⟨hMassBalance, hRaw⟩, ?_⟩
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨240, by norm_num⟩, ?_⟩
  rw [if_pos]
  · rw [hRaw]
    norm_num
  · rw [hRaw]
    norm_num

/-- Stoichiometric coefficients for an acidic CO₂-to-CO reduction half
reaction. -/
structure AcidicCO2Reduction where
  carbonDioxide : ℕ
  protons : ℕ
  electrons : ℕ
  carbonMonoxide : ℕ
  water : ℕ

/-- Carbon, oxygen, hydrogen, and charge ledgers for the half reaction. -/
def IsBalancedAcidicCO2Reduction (r : AcidicCO2Reduction) : Prop :=
  r.carbonDioxide = r.carbonMonoxide ∧
  2 * r.carbonDioxide = r.carbonMonoxide + r.water ∧
  r.protons = 2 * r.water ∧
  (r.protons : ℤ) - (r.electrons : ℤ) = 0

def co2ToCoHalfReaction : AcidicCO2Reduction where
  carbonDioxide := 1
  protons := 2
  electrons := 2
  carbonMonoxide := 1
  water := 1

/-- Rootless derivation of the two reacted electrons per CO molecule used in
A6; no earlier answer is imported. -/
def A1ElectronLedger : Prop :=
  IsBalancedAcidicCO2Reduction co2ToCoHalfReaction ∧
  co2ToCoHalfReaction.electrons =
    2 * co2ToCoHalfReaction.carbonMonoxide

theorem deriveTwoElectronsPerCO : A1ElectronLedger := by
  norm_num [A1ElectronLedger, IsBalancedAcidicCO2Reduction,
    co2ToCoHalfReaction]

/-- Exact SI defining value of the Planck constant, in joule seconds. -/
def planckConstantJouleSeconds : ℝ :=
  (662607015 : ℝ) / (10 : ℝ) ^ 42

/-- Exact SI value of the speed of light, in metres per second. -/
def speedOfLightMetersPerSecond : ℝ := 299792458

def a6SupportMassG : ℝ := (10 : ℝ) / 1000

def a6WavelengthM : ℝ := (390 : ℝ) / (10 : ℝ) ^ 9

def a6PowerW : ℝ := (50 : ℝ) / 1000

def secondsPerHour : ℝ := 3600

def a6CatalystMolecules : ℝ :=
  a6SupportMassG * catalystMoleculesPerGramSupport a5LoadingPercent

def a6COMoleculesPerHour : ℝ := 8 * a6CatalystMolecules

def a6ReactedElectronsPerHour : ℝ :=
  (co2ToCoHalfReaction.electrons : ℝ) * a6COMoleculesPerHour

def a6PhotonEnergyJ : ℝ :=
  planckConstantJouleSeconds * speedOfLightMetersPerSecond / a6WavelengthM

def a6IncidentPhotonsPerHour : ℝ :=
  a6PowerW * secondsPerHour / a6PhotonEnergyJ

/-- Exact A6 quantum yield in percent, with no intermediate rounding. -/
def a6RawQuantumYieldPercent : ℝ :=
  a6ReactedElectronsPerHour / a6IncidentPhotonsPerHour * 100

/-- A6 is derived inline from the A1 electron ledger, the A5 total-mixture
loading ledger, the printed TOF/illumination data, and photon energy `h*c/λ`. -/
def A6RawDerivation : Prop :=
  A1ElectronLedger ∧
  A5MassBalanceSpec ∧
  a6RawQuantumYieldPercent =
    (18940872892793693114789369 : ℝ) /
      9799408490625000000000000

/-- A6 reported at the project default of three significant figures. -/
def A6ReportedDerivation : Prop :=
  A6RawDerivation ∧
  IChO2026Chem.Reporting.ReportsAtQuantum
    a6RawQuantumYieldPercent ((193 : ℝ) / 100) ((1 : ℝ) / 100)

theorem deriveA6FromProblemOnlyData : A6ReportedDerivation := by
  have hRaw :
      a6RawQuantumYieldPercent =
        (18940872892793693114789369 : ℝ) /
          9799408490625000000000000 := by
    norm_num [a6RawQuantumYieldPercent, a6ReactedElectronsPerHour,
      a6COMoleculesPerHour, a6CatalystMolecules, a6IncidentPhotonsPerHour,
      a6PhotonEnergyJ, a6PowerW, secondsPerHour, planckConstantJouleSeconds,
      speedOfLightMetersPerSecond, a6WavelengthM, a6SupportMassG,
      catalystMoleculesPerGramSupport, catalystToSupportMassRatio,
      catalystMolarMassGPerMol, avogadroConstantPerMol, a5LoadingPercent,
      co2ToCoHalfReaction]
  refine ⟨⟨deriveTwoElectronsPerCO, deriveA5FromPrintedData.1.1, hRaw⟩, ?_⟩
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨193, by norm_num⟩, ?_⟩
  rw [if_pos]
  · rw [hRaw]
    norm_num
  · rw [hRaw]
    norm_num

/-! ## Part A7 -/

/-- CO molecules formed per hour per gram of C₃N₄ support. -/
def coFormationRatePerGramSupport
    (ωPercent tofPerHour : ℝ) : ℝ :=
  tofPerHour * catalystMoleculesPerGramSupport ωPercent

def sourceCOFormationRatePerGramSupport (i : Fin 7) : ℝ :=
  coFormationRatePerGramSupport
    (sourceGraph i).loadingPercent (sourceGraph i).tofPerHour

/-- Measurement envelopes for the lowest and highest plotted loading points.
The half-widths are determined by the last displayed digit: `0.1 %` for
loading and `1 h⁻¹` for TOF. -/
def EndpointReadoutEnvelope
    (lowLoading lowTOF highLoading highTOF : ℝ) : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement
      lowLoading ((1 : ℝ) / 10) ((1 : ℝ) / 10) ∧
  IChO2026Chem.Reporting.ConsistentMeasurement lowTOF 62 1 ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      highLoading ((38 : ℝ) / 10) ((1 : ℝ) / 10) ∧
  IChO2026Chem.Reporting.ConsistentMeasurement highTOF 8 1

/-- The unreported source-level result: every value represented by the endpoint
readouts gives a larger overall rate at the high loading than at the low
loading.  `SourceGraphReadout` retains all seven supplied empirical points,
while the endpoint comparison gives the meaning of “overall” used by the
three-way question. -/
def RawCoRateTrend : Prop :=
  SourceChemicalContext ∧
  SourceGraphReadout ∧
  ∀ lowLoading lowTOF highLoading highTOF : ℝ,
    EndpointReadoutEnvelope lowLoading lowTOF highLoading highTOF →
    coFormationRatePerGramSupport lowLoading lowTOF <
      coFormationRatePerGramSupport highLoading highTOF

/-- Semantics of the three printed trend alternatives for two rates. -/
def TrendMatchesRates (trend : CoRateTrend) (lowRate highRate : ℝ) : Prop :=
  match trend with
  | .increases => lowRate < highRate
  | .decreases => highRate < lowRate
  | .doesNotChange => highRate = lowRate

/-- The reported symbolic classification, stated as a property of the measured
endpoint rates rather than as a reflexive equality of a preselected constant. -/
def ReportedCoRateTrend : Prop :=
  SourceChemicalContext ∧
  SourceGraphReadout ∧
  ∀ lowLoading lowTOF highLoading highTOF : ℝ,
    EndpointReadoutEnvelope lowLoading lowTOF highLoading highTOF →
    TrendMatchesRates .increases
      (coFormationRatePerGramSupport lowLoading lowTOF)
      (coFormationRatePerGramSupport highLoading highTOF)

/-- All controller-listed prerequisites and the A7 derivation are discharged
inside this rootless run.  A4 structural details are not used: the problem
prints the catalyst molar mass needed for A5/A6 directly. -/
def FullProblemOnlyDerivation : Prop :=
  A5ReportedDerivation ∧
  A6ReportedDerivation ∧
  RawCoRateTrend ∧
  ReportedCoRateTrend

theorem deriveFullProblemOnlyContract : FullProblemOnlyDerivation := by
  have hRawTrend : RawCoRateTrend := by
    refine ⟨by simp [SourceChemicalContext, sourceRateContext], ?_, ?_⟩
    · simp [SourceGraphReadout, sourceGraph]
    · intro lowLoading lowTOF highLoading highTOF hEnvelope
      rcases hEnvelope with
        ⟨⟨_, hLowLoadingAbs⟩, ⟨_, hLowTOFAbs⟩,
          ⟨_, hHighLoadingAbs⟩, ⟨_, hHighTOFAbs⟩⟩
      have hLowLoadingAbs' := abs_le.mp hLowLoadingAbs
      have hLowTOFAbs' := abs_le.mp hLowTOFAbs
      have hHighLoadingAbs' := abs_le.mp hHighLoadingAbs
      have hHighTOFAbs' := abs_le.mp hHighTOFAbs
      have hLowLoadingLower : (1 : ℝ) / 20 ≤ lowLoading := by
        linarith
      have hLowLoadingUpper : lowLoading ≤ (3 : ℝ) / 20 := by
        linarith
      have hLowTOFLower : (123 : ℝ) / 2 ≤ lowTOF := by
        linarith
      have hLowTOFUpper : lowTOF ≤ (125 : ℝ) / 2 := by
        linarith
      have hHighLoadingLower : (15 : ℝ) / 4 ≤ highLoading := by
        linarith
      have hHighLoadingUpper : highLoading ≤ (77 : ℝ) / 20 := by
        linarith
      have hHighTOFLower : (15 : ℝ) / 2 ≤ highTOF := by
        linarith
      have hHighTOFUpper : highTOF ≤ (17 : ℝ) / 2 := by
        linarith
      have ratio_mono : ∀ {x y : ℝ},
          0 ≤ x → x ≤ y → y < 100 →
            catalystToSupportMassRatio x ≤
              catalystToSupportMassRatio y := by
        intro x y hx hxy hy
        have hxDenom : 0 < 1 - x / 100 := by nlinarith
        have hyDenom : 0 < 1 - y / 100 := by nlinarith
        unfold catalystToSupportMassRatio
        rw [div_le_div_iff₀ hxDenom hyDenom]
        nlinarith
      have ratio_nonneg : ∀ {x : ℝ},
          0 ≤ x → x < 100 → 0 ≤ catalystToSupportMassRatio x := by
        intro x hx hxUpper
        have hxDenom : 0 < 1 - x / 100 := by nlinarith
        unfold catalystToSupportMassRatio
        exact div_nonneg (div_nonneg hx (by norm_num)) (le_of_lt hxDenom)
      have hLowRatio :
          catalystToSupportMassRatio lowLoading ≤
            catalystToSupportMassRatio ((3 : ℝ) / 20) := by
        apply ratio_mono (le_trans (by norm_num) hLowLoadingLower)
          hLowLoadingUpper
        norm_num
      have hHighRatio :
          catalystToSupportMassRatio ((15 : ℝ) / 4) ≤
            catalystToSupportMassRatio highLoading := by
        apply ratio_mono (by norm_num) hHighLoadingLower
        linarith
      have hLowProduct :
          lowTOF * catalystToSupportMassRatio lowLoading ≤
            ((125 : ℝ) / 2) *
              catalystToSupportMassRatio ((3 : ℝ) / 20) := by
        exact mul_le_mul hLowTOFUpper hLowRatio
          (ratio_nonneg
            (le_trans (by norm_num) hLowLoadingLower)
            (by linarith [hLowLoadingUpper]))
          (by norm_num)
      have hHighProduct :
          ((15 : ℝ) / 2) *
              catalystToSupportMassRatio ((15 : ℝ) / 4) ≤
            highTOF * catalystToSupportMassRatio highLoading := by
        exact mul_le_mul hHighTOFLower hHighRatio
          (ratio_nonneg (by norm_num) (by norm_num))
          (by linarith)
      have hExtremeProducts :
          ((125 : ℝ) / 2) *
              catalystToSupportMassRatio ((3 : ℝ) / 20) <
            ((15 : ℝ) / 2) *
              catalystToSupportMassRatio ((15 : ℝ) / 4) := by
        norm_num [catalystToSupportMassRatio]
      have hProxy :
          lowTOF * catalystToSupportMassRatio lowLoading <
            highTOF * catalystToSupportMassRatio highLoading :=
        lt_of_le_of_lt hLowProduct (lt_of_lt_of_le hExtremeProducts hHighProduct)
      have hPositiveScale :
          0 < avogadroConstantPerMol / catalystMolarMassGPerMol := by
        norm_num [avogadroConstantPerMol, catalystMolarMassGPerMol]
      have hScaled := mul_lt_mul_of_pos_right hProxy hPositiveScale
      change
        lowTOF *
            (catalystToSupportMassRatio lowLoading /
              catalystMolarMassGPerMol * avogadroConstantPerMol) <
          highTOF *
            (catalystToSupportMassRatio highLoading /
              catalystMolarMassGPerMol * avogadroConstantPerMol)
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hScaled
  have hReportedTrend : ReportedCoRateTrend := by
    rcases hRawTrend with ⟨hContext, hGraph, hEndpoints⟩
    refine ⟨hContext, hGraph, ?_⟩
    intro lowLoading lowTOF highLoading highTOF hEnvelope
    simpa [TrendMatchesRates] using
      hEndpoints lowLoading lowTOF highLoading highTOF hEnvelope
  exact ⟨deriveA5FromPrintedData, deriveA6FromProblemOnlyData,
    hRawTrend, hReportedTrend⟩

/-- Primary carrier for requested output `co_rate_trend`. -/
theorem problem_icho_2026_t8_a7 : ReportedCoRateTrend := by
  exact deriveFullProblemOnlyContract.2.2.2

/-- Payload-bound raw-result contract for the answer-blind solve record. -/
theorem rawResultContract :
    ("bf58349e3fb6359e5aceab933977290b494f81deb11cdd3f75479bb15255597b" : String) =
        "bf58349e3fb6359e5aceab933977290b494f81deb11cdd3f75479bb15255597b" ∧
      IChO2026Problems.T8A7.RawCoRateTrend := by
  exact ⟨rfl, deriveFullProblemOnlyContract.2.2.1⟩

/-- Payload-bound reported-result contract for the answer-blind solve record. -/
theorem reportedResultContract :
    ("57cdbe9c967d49838130bd6c659e46a61d8df9335bf989c4458919ce438fd3cf" : String) =
        "57cdbe9c967d49838130bd6c659e46a61d8df9335bf989c4458919ce438fd3cf" ∧
      IChO2026Problems.T8A7.ReportedCoRateTrend := by
  exact ⟨rfl, deriveFullProblemOnlyContract.2.2.2⟩

end
end T8A7
end IChO2026Problems
