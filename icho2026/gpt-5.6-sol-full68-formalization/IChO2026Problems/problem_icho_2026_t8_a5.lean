import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T8-A5: catalyst molecules per support area

The current subquestion asks for one scalar: the number of molecules of
molecular catalyst `1` per square nanometre of the crystalline carbon-nitride
support.  The printed mass fraction is interpreted as catalyst mass divided by
the total mass of the loaded composite.  Consequently, an arbitrary composite
sample of total mass `m` contains `0.038 m` grams of catalyst and `0.962 m`
grams of support; only the latter mass is multiplied by the support's specific
surface area.

The calculation is independent of the chosen sample mass.  This file exposes
that cancellation through `LoadedCompositeSample` and
`CatalystSurfaceDensityDerivationSpec`, keeps the unrounded source expression
in `catalystSurfaceDensityRaw`, and rounds only in the final
`ReportsAtQuantum` theorem.

The reaction mechanisms on the two bound pages are not used to infer a
formula, molar mass, yield, or surface coverage.  The problem directly supplies
the catalyst molar mass needed here.
-/

namespace IChO2026Problems
namespace ProblemIChO2026T8A5

noncomputable section

/-- Source classes used by the numerical input ledger. -/
inductive Provenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- A real-valued datum together with an auditable source locator.  Units are
recorded in each declaration's name and docstring so arithmetic remains an
exact scalar calculation in the source's chosen units. -/
structure SourcedReal where
  value : ℝ
  provenance : Provenance
  locator : String

/-- The source-stipulated catalyst mass fraction, `3.8 % = 0.038`.

Its numerator is catalyst mass and its denominator is the total mass of the
loaded catalyst/support composite. -/
def catalystMassFraction : SourcedReal where
  value := 19 / 500
  provenance := .problemText
  locator := "T8_page-2.png, T8-A5: omega_cat = 3.8%; total-loaded-composite mass basis"

/-- The source-stipulated molar mass of molecular catalyst `1`, in g mol⁻¹. -/
def catalystMolarMassGPerMol : SourcedReal where
  value := 55721 / 100
  provenance := .problemText
  locator := "T8_page-2.png, T8-A5: M_cat = 557.21 g mol^-1"

/-- The source-stipulated specific surface area of the crystalline C₃N₄
support, in m² per gram of support. -/
def supportSpecificAreaM2PerG : SourcedReal where
  value := 89 / 5
  provenance := .problemText
  locator := "T8_page-2.png, T8-A5: specific surface area of C3N4 = 17.8 m^2 g^-1"

/-- Exact SI Avogadro constant, in molecules mol⁻¹.

NIST's 2022 CODATA page gives `6.02214076 × 10^23 mol⁻¹` with exact standard
uncertainty: <https://physics.nist.gov/cgi-bin/cuu/Value?na>, numerical-value
and standard-uncertainty rows. -/
def avogadroConstantMoleculesPerMol : SourcedReal where
  value := 602214076 * (10 : ℝ) ^ 15
  provenance := .trustedGeneralLaw
  locator := "NIST CODATA Avogadro constant, numerical-value and standard-uncertainty rows"

/-- Exact area conversion, `1 m² = 10^18 nm²`. -/
def squareNanometresPerSquareMetre : SourcedReal where
  value := (10 : ℝ) ^ 18
  provenance := .trustedGeneralLaw
  locator := "SI prefix law: 1 m = 10^9 nm, squared"

/-- An arbitrary loaded catalyst/support sample.

`catalystFraction` is the defining mass-fraction equation
`m_cat / m_total = omega_cat`; `massBalance` ensures that the remainder of the
total mass is the support mass.  These hypotheses encode the source-side input
convention, not the requested surface-density result. -/
structure LoadedCompositeSample where
  totalMassG : ℝ
  catalystMassG : ℝ
  supportMassG : ℝ
  totalMassPositive : 0 < totalMassG
  catalystMassNonnegative : 0 ≤ catalystMassG
  supportMassNonnegative : 0 ≤ supportMassG
  massBalance : catalystMassG + supportMassG = totalMassG
  catalystFraction : catalystMassG / totalMassG = catalystMassFraction.value

/-- A concrete one-gram sample witnessing that the loading assumptions are
consistent.  Its catalyst/support masses are `0.038 g` and `0.962 g`. -/
def oneGramLoadedComposite : LoadedCompositeSample where
  totalMassG := 1
  catalystMassG := 19 / 500
  supportMassG := 481 / 500
  totalMassPositive := by norm_num
  catalystMassNonnegative := by norm_num
  supportMassNonnegative := by norm_num
  massBalance := by norm_num
  catalystFraction := by norm_num [catalystMassFraction]

/-- The mass-balance consequence that the support, rather than the whole
composite, has mass `(1 - omega_cat) m_total`. -/
theorem supportMass_eq_fractionComplement (sample : LoadedCompositeSample) :
    sample.supportMassG =
      (1 - catalystMassFraction.value) * sample.totalMassG := by
  have htotal : sample.totalMassG ≠ 0 := ne_of_gt sample.totalMassPositive
  have hcatalyst :
      sample.catalystMassG =
        catalystMassFraction.value * sample.totalMassG :=
    (div_eq_iff htotal).mp sample.catalystFraction
  calc
    sample.supportMassG = sample.totalMassG - sample.catalystMassG := by
      linarith [sample.massBalance]
    _ = (1 - catalystMassFraction.value) * sample.totalMassG := by
      rw [hcatalyst]
      ring

/-- The support mass is strictly positive for every admissible loaded sample. -/
theorem supportMass_positive (sample : LoadedCompositeSample) :
    0 < sample.supportMassG := by
  rw [supportMass_eq_fractionComplement]
  apply mul_pos
  · norm_num [catalystMassFraction]
  · exact sample.totalMassPositive

/-- Number of catalyst molecules in a loaded sample.  This is
`(m_cat / M_cat) N_A`. -/
def catalystMoleculeCount (sample : LoadedCompositeSample) : ℝ :=
  (sample.catalystMassG / catalystMolarMassGPerMol.value) *
    avogadroConstantMoleculesPerMol.value

/-- Accessible support area of a loaded sample, in nm².  The specific area is
multiplied by support mass and then by `10^18 nm²/m²`. -/
def supportSurfaceAreaNm2 (sample : LoadedCompositeSample) : ℝ :=
  sample.supportMassG * supportSpecificAreaM2PerG.value *
    squareNanometresPerSquareMetre.value

/-- Catalyst molecules per nm² for an arbitrary admissible sample. -/
def catalystSurfaceDensityFor (sample : LoadedCompositeSample) : ℝ :=
  catalystMoleculeCount sample / supportSurfaceAreaNm2 sample

/-- Exact, unrounded requested quantity in molecules nm⁻².

The first factor is the catalyst-to-support mass ratio obtained from the
total-composite mass fraction.  The remaining factors convert catalyst mass to
molecules and support mass to nm². -/
def catalystSurfaceDensityRaw : ℝ :=
  (catalystMassFraction.value / (1 - catalystMassFraction.value)) *
    (avogadroConstantMoleculesPerMol.value /
      (catalystMolarMassGPerMol.value * supportSpecificAreaM2PerG.value *
        squareNanometresPerSquareMetre.value))

/-- Source-to-target bridge: every positive loaded-composite sample satisfying
the mass-balance and total-mass-fraction equations gives the same surface
density as the explicit raw expression. -/
def CatalystSurfaceDensityDerivationSpec : Prop :=
  ∀ sample : LoadedCompositeSample,
    catalystSurfaceDensityFor sample = catalystSurfaceDensityRaw

/-- The arbitrary-sample calculation is scale-independent. -/
theorem catalystSurfaceDensityFor_eq_raw (sample : LoadedCompositeSample) :
    catalystSurfaceDensityFor sample = catalystSurfaceDensityRaw := by
  have htotal : sample.totalMassG ≠ 0 := ne_of_gt sample.totalMassPositive
  have hcatalyst :
      sample.catalystMassG =
        catalystMassFraction.value * sample.totalMassG :=
    (div_eq_iff htotal).mp sample.catalystFraction
  unfold catalystSurfaceDensityFor catalystMoleculeCount supportSurfaceAreaNm2
    catalystSurfaceDensityRaw
  rw [hcatalyst, supportMass_eq_fractionComplement]
  field_simp [catalystMassFraction, catalystMolarMassGPerMol,
    supportSpecificAreaM2PerG, avogadroConstantMoleculesPerMol,
    squareNanometresPerSquareMetre, htotal]

/-- Exact rational normal form of the unrounded source expression.  This is a
derived value, not an input or a rounded decimal. -/
theorem catalystSurfaceDensityRaw_eq_exactFraction :
    catalystSurfaceDensityRaw = (5721033722 : ℝ) / 2385360289 := by
  norm_num [catalystSurfaceDensityRaw, catalystMassFraction,
    catalystMolarMassGPerMol, supportSpecificAreaM2PerG,
    avogadroConstantMoleculesPerMol, squareNanometresPerSquareMetre]

/-- Lower endpoint of a certified, non-degenerate interval for the raw value. -/
def catalystSurfaceDensityLowerBound : ℝ := 2398 / 1000

/-- Upper endpoint of a certified, non-degenerate interval for the raw value. -/
def catalystSurfaceDensityUpperBound : ℝ := 2399 / 1000

/-- Raw answer-blind result contract.

It proves the governing arbitrary-sample specification together with the
independently checkable interval `2.398 < N_cat < 2.399`; no displayed-answer
decimal is built into the raw definition. -/
theorem catalystSurfaceDensity_raw_result :
    CatalystSurfaceDensityDerivationSpec ∧
      catalystSurfaceDensityLowerBound < catalystSurfaceDensityUpperBound ∧
      catalystSurfaceDensityLowerBound < catalystSurfaceDensityRaw ∧
      catalystSurfaceDensityRaw < catalystSurfaceDensityUpperBound := by
  refine ⟨(fun sample => catalystSurfaceDensityFor_eq_raw sample), ?_, ?_, ?_⟩
  · norm_num [catalystSurfaceDensityLowerBound,
      catalystSurfaceDensityUpperBound]
  · rw [catalystSurfaceDensityRaw_eq_exactFraction]
    norm_num [catalystSurfaceDensityLowerBound]
  · rw [catalystSurfaceDensityRaw_eq_exactFraction]
    norm_num [catalystSurfaceDensityUpperBound]

/-- The raw density is in `[1, 10)`, so three significant figures use quantum
`0.01` molecules nm⁻². -/
theorem catalystSurfaceDensity_orderOfMagnitude :
    (1 : ℝ) ≤ catalystSurfaceDensityRaw ∧ catalystSurfaceDensityRaw < 10 := by
  rw [catalystSurfaceDensityRaw_eq_exactFraction]
  constructor <;> norm_num

/-- Three-significant-figure displayed value, `2.40` molecules nm⁻². -/
def catalystSurfaceDensityReported : ℝ := 12 / 5

/-- Reporting quantum for three significant figures at this magnitude. -/
def catalystSurfaceDensityReportingQuantum : ℝ := 1 / 100

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"catalyst_surface_density","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"2.40","reporting_quantum":"0.01","raw_declaration":"IChO2026Problems.ProblemIChO2026T8A5.catalystSurfaceDensityRaw","reporting_declaration":"IChO2026Problems.ProblemIChO2026T8A5.catalystSurfaceDensity_reported_result"}
/-- Final answer-blind reporting contract.  `ReportsAtQuantum` implements the
source report's half-away-from-zero tie rule and is applied only here. -/
theorem catalystSurfaceDensity_reported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      catalystSurfaceDensityRaw catalystSurfaceDensityReported
      catalystSurfaceDensityReportingQuantum := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num [catalystSurfaceDensityReportingQuantum],
    ⟨240, by norm_num [catalystSurfaceDensityReported,
      catalystSurfaceDensityReportingQuantum]⟩, ?_⟩
  have hraw : 0 ≤ catalystSurfaceDensityRaw :=
    le_trans (by norm_num) catalystSurfaceDensity_orderOfMagnitude.1
  rw [if_pos hraw, catalystSurfaceDensityRaw_eq_exactFraction]
  norm_num [catalystSurfaceDensityReported,
    catalystSurfaceDensityReportingQuantum]

/-- Combined requested-output theorem: the source-to-Lean derivation and the
three-significant-figure reporting certificate both hold. -/
theorem catalystSurfaceDensity_target :
    CatalystSurfaceDensityDerivationSpec ∧
      IChO2026Chem.Reporting.ReportsAtQuantum
        catalystSurfaceDensityRaw catalystSurfaceDensityReported
        catalystSurfaceDensityReportingQuantum := by
  exact ⟨catalystSurfaceDensity_raw_result.1,
    catalystSurfaceDensity_reported_result⟩

end
end ProblemIChO2026T8A5
end IChO2026Problems
