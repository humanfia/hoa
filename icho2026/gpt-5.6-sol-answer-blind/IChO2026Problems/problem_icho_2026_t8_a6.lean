import Mathlib
import Physlib.Units.WithDim.Speed
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem T8-A6: quantum yield for CO formation

The calculation is carried out over one hour, the time unit used by the given
turnover frequency.  All printed decimal data and all SI defining constants
are represented as exact real numbers.  In particular, no intermediate value
is rounded.

The `3.8%` catalyst mass fraction is interpreted in its standard mass-fraction
sense

`catalyst mass / (support mass + catalyst mass)`.

Thus the catalyst mass is solved from a mass balance; it is not taken to be
`3.8%` of the support mass.
-/

open scoped BigOperators

namespace IChO2026Problems
namespace T8A6

noncomputable section

/-! ## Species and the acidic CO₂/CO half-reaction -/

/-- The closed species domain needed to balance the acidic CO₂-to-CO half-reaction. -/
inductive RedoxSpecies
  | carbonDioxide
  | proton
  | electron
  | carbonMonoxide
  | water
  deriving DecidableEq, Fintype

/-- Elements whose atom ledgers are needed for the CO₂-to-CO half-reaction. -/
inductive Element
  | carbon
  | hydrogen
  | oxygen
  deriving DecidableEq, Fintype

/-- Atom count of an element in one particle of a species. -/
def atomsInSpecies : RedoxSpecies → Element → ℕ
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .oxygen => 2
  | .proton, .hydrogen => 1
  | .carbonMonoxide, .carbon => 1
  | .carbonMonoxide, .oxygen => 1
  | .water, .hydrogen => 2
  | .water, .oxygen => 1
  | _, _ => 0

/-- Formal charge of one particle of a species. -/
def formalCharge : RedoxSpecies → ℤ
  | .proton => 1
  | .electron => -1
  | _ => 0

/-- Total number of atoms of `e` in a CRNT complex. -/
def complexAtomCount (c : CRNT.Complex RedoxSpecies) (e : Element) : ℕ :=
  ∑ s, c s * atomsInSpecies s e

/-- Total formal charge of a CRNT complex. -/
def complexCharge (c : CRNT.Complex RedoxSpecies) : ℤ :=
  ∑ s, (c s : ℤ) * formalCharge s

/-- Atom and charge conservation for a reaction. -/
def IsBalanced (r : CRNT.Reaction RedoxSpecies) : Prop :=
  (∀ e, complexAtomCount r.source e = complexAtomCount r.target e) ∧
    complexCharge r.source = complexCharge r.target

/--
Source-first characterization of the reduction direction `CO₂ → CO` in an
acidic medium.  The coefficients of water, protons, and electrons are not fixed
by this predicate; they must follow from atom and charge balance.
-/
def IsAcidicCO2ToCOHalfReaction (r : CRNT.Reaction RedoxSpecies) : Prop :=
  IsBalanced r ∧
    r.source .carbonDioxide = 1 ∧
    r.target .carbonDioxide = 0 ∧
    r.source .carbonMonoxide = 0 ∧
    r.target .carbonMonoxide = 1 ∧
    r.source .water = 0 ∧
    r.target .proton = 0 ∧
    r.target .electron = 0

/-- The candidate half-reaction `CO₂ + 2 H⁺ + 2 e⁻ → CO + H₂O`. -/
def co2ToCOHalfReaction : CRNT.Reaction RedoxSpecies where
  source
    | .carbonDioxide => 1
    | .proton => 2
    | .electron => 2
    | _ => 0
  target
    | .carbonMonoxide => 1
    | .water => 1
    | _ => 0

/-- The displayed candidate satisfies the source-first balance specification. -/
theorem co2ToCOHalfReaction_spec :
    IsAcidicCO2ToCOHalfReaction co2ToCOHalfReaction := by
  refine ⟨⟨?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro e
    fin_cases e <;> decide
  · decide

/-- Balancing, rather than an assumed coefficient, forces two electrons per CO. -/
theorem acidicCO2ToCO_electronCount
    {r : CRNT.Reaction RedoxSpecies}
    (hr : IsAcidicCO2ToCOHalfReaction r) :
    r.source .electron = 2 := by
  rcases hr with ⟨⟨hatoms, hcharge⟩, hCO₂s, hCO₂t, hCOs, hCOt,
    hwaters, hprotont, helectront⟩
  have hspecies : (Finset.univ : Finset RedoxSpecies) =
      {.carbonDioxide, .proton, .electron, .carbonMonoxide, .water} := by
    decide
  have hoxygen := hatoms Element.oxygen
  have hhydrogen := hatoms Element.hydrogen
  simp [complexAtomCount, hspecies, atomsInSpecies] at hoxygen hhydrogen
  simp [complexCharge, hspecies, formalCharge] at hcharge
  omega

/-! ## Printed experiment data and SI constants -/

/-- Catalyst mass divided by total loaded-sample mass: `3.8%`. -/
def catalystMassFraction : ℝ := 3.8 / 100

/-- Mass of the stated carbon-nitride support: `10 mg = 10/1000 g`. -/
def supportMassGrams : ℝ := 10 / 1000

/-- Specific surface area of crystalline carbon nitride: `17.8 m² g⁻¹`. -/
def specificSurfaceAreaSquareMetresPerGram : ℝ := 17.8

/-- Catalyst molar mass: `557.21 g mol⁻¹`. -/
def catalystMolarMassGramsPerMole : ℝ := 557.21

/-- Turnover frequency: `8` CO molecules per active catalyst molecule per hour. -/
def turnoverFrequencyPerHour : ℝ := 8

/-- Wavelength of the LED: `390 nm = 390e-9 m`. -/
def ledWavelengthMetres : ℝ := 390e-9

/-- Incident LED power: `50 mW = 50e-3 W`. -/
def ledPowerWatts : ℝ := 50e-3

/-- Seconds in the one-hour counting interval used by the TOF. -/
def secondsPerHour : ℝ := 3600

/-- Square nanometres in one square metre. -/
def squareNanometresPerSquareMetre : ℝ := 10 ^ 18

/--
Exact SI defining value of the Avogadro constant, in `mol⁻¹`:
`6.02214076e23`.
-/
def avogadroConstantPerMole : ℝ := 6.02214076e23

/--
Exact SI defining value of the Planck constant, in `J s`:
`6.62607015e-34`.
-/
def planckConstantJouleSeconds : ℝ := 6.62607015e-34

/-- Exact SI defining value of the speed of light, in `m s⁻¹`. -/
def speedOfLightMetresPerSecond : ℝ := 299792458

/-- The scalar speed used here agrees with Physlib's dimensionful SI value. -/
theorem speedOfLight_physlib_bridge :
    DimSpeed.speedOfLight UnitChoices.SI = ⟨speedOfLightMetresPerSecond⟩ := by
  simp [speedOfLightMetresPerSecond]

/-! ## Mass loading and the previous-part surface-density calculation -/

/--
The mass-fraction ledger.  Its denominator is the total loaded-sample mass,
not the support mass alone.
-/
def LoadedCatalystMassBalance (catalystMass : ℝ) : Prop :=
  0 ≤ catalystMass ∧
    0 < supportMassGrams + catalystMass ∧
    catalystMassFraction =
      catalystMass / (supportMassGrams + catalystMass)

/-- Catalyst mass obtained by solving the mass-fraction balance. -/
def catalystMassGrams : ℝ :=
  catalystMassFraction * supportMassGrams / (1 - catalystMassFraction)

/-- The solved catalyst mass satisfies the total-mixture mass-fraction equation. -/
theorem catalystMassGrams_spec :
    LoadedCatalystMassBalance catalystMassGrams := by
  norm_num [LoadedCatalystMassBalance, catalystMassGrams,
    catalystMassFraction, supportMassGrams]

/-- Number of moles of catalyst in the irradiated loaded sample. -/
def catalystMoles : ℝ :=
  catalystMassGrams / catalystMolarMassGramsPerMole

/-- Number of catalyst molecules in the irradiated loaded sample. -/
def catalystMoleculeCount : ℝ :=
  catalystMoles * avogadroConstantPerMole

/-- Surface area of the `10 mg` support, expressed in `nm²`. -/
def illuminatedSupportAreaSquareNanometres : ℝ :=
  supportMassGrams * specificSurfaceAreaSquareMetresPerGram *
    squareNanometresPerSquareMetre

/-- The part-8.5 catalyst surface density, rederived inline from problem data. -/
def catalystSurfaceDensityPerSquareNanometre : ℝ :=
  catalystMoleculeCount / illuminatedSupportAreaSquareNanometres

/-- Nontrivial carrier for the previous-part molecule/area calculation. -/
def CatalystSurfaceDensitySpec (density : ℝ) : Prop :=
  0 < illuminatedSupportAreaSquareNanometres ∧
    density * illuminatedSupportAreaSquareNanometres = catalystMoleculeCount

/-- Part 8.5 is derived in this answer-blind run, rather than imported. -/
theorem previousPart_surfaceDensity_derived :
    LoadedCatalystMassBalance catalystMassGrams ∧
      CatalystSurfaceDensitySpec catalystSurfaceDensityPerSquareNanometre := by
  refine ⟨catalystMassGrams_spec, ?_⟩
  norm_num [CatalystSurfaceDensitySpec,
    catalystSurfaceDensityPerSquareNanometre, catalystMoleculeCount,
    catalystMoles, catalystMassGrams, catalystMassFraction,
    catalystMolarMassGramsPerMole, avogadroConstantPerMole,
    illuminatedSupportAreaSquareNanometres, supportMassGrams,
    specificSurfaceAreaSquareMetresPerGram,
    squareNanometresPerSquareMetre]

/-! ## Product, electron, photon, and quantum-yield ledgers -/

/-- CO molecules formed during one hour according to the supplied TOF. -/
def carbonMonoxideMoleculesPerHour : ℝ :=
  turnoverFrequencyPerHour *
    catalystSurfaceDensityPerSquareNanometre *
    illuminatedSupportAreaSquareNanometres

/-- Electrons reacted during that hour, using the balanced half-reaction. -/
def reactedElectronsPerHour : ℝ :=
  (co2ToCOHalfReaction.source .electron : ℝ) *
    carbonMonoxideMoleculesPerHour

/-- Energy of one monochromatic `390 nm` photon, in joules. -/
def photonEnergyJoules : ℝ :=
  planckConstantJouleSeconds * speedOfLightMetresPerSecond /
    ledWavelengthMetres

/-- Carrier for the law `E_photon = h c / λ`, including its domain condition. -/
def PhotonEnergySpec (energy : ℝ) : Prop :=
  0 < ledWavelengthMetres ∧
    energy = planckConstantJouleSeconds * speedOfLightMetresPerSecond /
      ledWavelengthMetres

/-- The photon-energy candidate satisfies the wavelength law. -/
theorem photonEnergyJoules_spec : PhotonEnergySpec photonEnergyJoules := by
  constructor
  · norm_num [ledWavelengthMetres]
  · rfl

/-- Incident LED energy during one hour, in joules. -/
def incidentLightEnergyJoulesPerHour : ℝ :=
  ledPowerWatts * secondsPerHour

/-- Number of incident photons during the same one-hour interval. -/
def incidentPhotonsPerHour : ℝ :=
  incidentLightEnergyJoulesPerHour / photonEnergyJoules

/-- The exact, unrounded quantum yield for CO formation, in percent. -/
def coQuantumYieldPercent : ℝ :=
  reactedElectronsPerHour / incidentPhotonsPerHour * 100

/--
End-to-end source specification for the raw result.  It records the loading
basis, the inline previous-part area calculation, the balanced redox electron
count, the TOF product count, the photon-energy law, and the problem's printed
electron/photon percentage formula.
-/
def CoQuantumYieldDerivationSpec (φ : ℝ) : Prop :=
  LoadedCatalystMassBalance catalystMassGrams ∧
    CatalystSurfaceDensitySpec catalystSurfaceDensityPerSquareNanometre ∧
    IsAcidicCO2ToCOHalfReaction co2ToCOHalfReaction ∧
    co2ToCOHalfReaction.source .electron = 2 ∧
    carbonMonoxideMoleculesPerHour =
      turnoverFrequencyPerHour *
        catalystSurfaceDensityPerSquareNanometre *
        illuminatedSupportAreaSquareNanometres ∧
    reactedElectronsPerHour =
      (co2ToCOHalfReaction.source .electron : ℝ) *
        carbonMonoxideMoleculesPerHour ∧
    PhotonEnergySpec photonEnergyJoules ∧
    incidentLightEnergyJoulesPerHour = ledPowerWatts * secondsPerHour ∧
    incidentPhotonsPerHour =
      incidentLightEnergyJoulesPerHour / photonEnergyJoules ∧
    φ = reactedElectronsPerHour / incidentPhotonsPerHour * 100

/-- Closed problem-specific proposition used by the raw-result contract. -/
def CoQuantumYieldRawDerivation : Prop :=
  CoQuantumYieldDerivationSpec coQuantumYieldPercent

/--
Raw answer-blind result: the exact derivation holds and the unrounded value is
certified in a nondegenerate interval before final reporting.
-/
theorem coQuantumYield_raw_result :
    CoQuantumYieldRawDerivation ∧
      (1932858 / 1000000 : ℝ) < coQuantumYieldPercent ∧
      coQuantumYieldPercent < (1932859 / 1000000 : ℝ) := by
  constructor
  · unfold CoQuantumYieldRawDerivation CoQuantumYieldDerivationSpec
    refine ⟨catalystMassGrams_spec, previousPart_surfaceDensity_derived.2,
      co2ToCOHalfReaction_spec, acidicCO2ToCO_electronCount co2ToCOHalfReaction_spec,
      rfl, rfl, photonEnergyJoules_spec, rfl, rfl, rfl⟩
  · constructor <;>
      norm_num [coQuantumYieldPercent, reactedElectronsPerHour,
        carbonMonoxideMoleculesPerHour, turnoverFrequencyPerHour,
        catalystSurfaceDensityPerSquareNanometre, catalystMoleculeCount,
        catalystMoles, catalystMassGrams, catalystMassFraction,
        supportMassGrams, catalystMolarMassGramsPerMole,
        avogadroConstantPerMole, illuminatedSupportAreaSquareNanometres,
        specificSurfaceAreaSquareMetresPerGram,
        squareNanometresPerSquareMetre, co2ToCOHalfReaction,
        incidentPhotonsPerHour, incidentLightEnergyJoulesPerHour,
        ledPowerWatts, secondsPerHour, photonEnergyJoules,
        planckConstantJouleSeconds, speedOfLightMetresPerSecond,
        ledWavelengthMetres]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"co_quantum_yield","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"1.93","reporting_quantum":"0.01","raw_declaration":"IChO2026Problems.T8A6.coQuantumYieldPercent","reporting_declaration":"IChO2026Problems.T8A6.coQuantumYield_reported_result"}
theorem coQuantumYield_reported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      coQuantumYieldPercent (193 / 100 : ℝ) (1 / 100 : ℝ) := by
  refine ⟨by norm_num, ⟨193, by norm_num⟩, ?_⟩
  have hlower := coQuantumYield_raw_result.2.1
  have hupper := coQuantumYield_raw_result.2.2
  have hnonnegative : 0 ≤ coQuantumYieldPercent := by
    linarith
  rw [if_pos hnonnegative]
  constructor <;> norm_num at * <;> linarith

end
end T8A6
end IChO2026Problems
