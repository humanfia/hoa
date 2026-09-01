import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, problem T8-A9

This file formalizes the reductive dynamic-quenching calculation for the
singlet `S₁` and triplet `T₁` states of the photosensitizer.  All printed
decimal inputs are represented exactly.  Rates are normalized to seconds and
concentrations to molar before the dimensionless Stern--Volmer factor is
formed.
-/

namespace IChO2026Problems.T8A9

noncomputable section

/-- The two photosensitizer excited states distinguished by the source. -/
inductive ExcitedState
  | singletS1
  | tripletT1
  deriving DecidableEq, Repr

/-- Chemical entities in either source reductive-quenching step. -/
inductive QuenchingSpecies
  | excitedPhotosensitizer (state : ExcitedState)
  | reductant
  | photosensitizerRadicalAnion
  | reductantRadicalCation
  deriving DecidableEq, Repr

/-- Source data for one reductive-quenching step.

The field names record the unit convention: `M⁻¹ s⁻¹`, `M`, and `s`.
-/
structure QuenchingInput where
  state : ExcitedState
  bimolecularRateConstant_perMolarSecond : ℝ
  reductantConcentration_molar : ℝ
  unquenchedLifetime_seconds : ℝ

/-- The reactants `PS(state) + Red` named in the source reaction. -/
def reductiveQuenchingReactants (input : QuenchingInput) : List QuenchingSpecies :=
  [.excitedPhotosensitizer input.state, .reductant]

/-- The products `PS•⁻ + Red•⁺` named in the source reaction. -/
def reductiveQuenchingProducts : List QuenchingSpecies :=
  [.photosensitizerRadicalAnion, .reductantRadicalCation]

/-- Positivity conditions required for a physical competing-rate model. -/
def PhysicallyAdmissible (input : QuenchingInput) : Prop :=
  0 < input.bimolecularRateConstant_perMolarSecond ∧
    0 < input.reductantConcentration_molar ∧
    0 < input.unquenchedLifetime_seconds

/-- A transparent quantitative carrier for the qualitative source statement
`k_F ≫ k_ISC`.  Since the source supplies no numerical meaning for `≫`, this
records a positive relative upper bound strictly below one rather than
inventing a tolerance. -/
def QualitativeRateDominance (major minor : ℝ) : Prop :=
  0 ≤ minor ∧ 0 < major ∧
    ∃ relativeBound : ℝ,
      0 < relativeBound ∧ relativeBound < 1 ∧ minor ≤ relativeBound * major

/-- The pseudo-first-order quenching rate `k_q [Red]`, in `s⁻¹`. -/
def pseudoFirstOrderQuenchingRate (input : QuenchingInput) : ℝ :=
  input.bimolecularRateConstant_perMolarSecond * input.reductantConcentration_molar

/-- The total non-quenching decay rate inferred from the supplied unquenched
emission lifetime, in `s⁻¹`. -/
def unquenchedDecayRate (input : QuenchingInput) : ℝ :=
  1 / input.unquenchedLifetime_seconds

/-- The dimensionless Stern--Volmer factor `k_q [Red] τ₀`. -/
def sternVolmerFactor (input : QuenchingInput) : ℝ :=
  input.bimolecularRateConstant_perMolarSecond *
    input.reductantConcentration_molar * input.unquenchedLifetime_seconds

/-- Percentage entering the reductive-quenching channel when its
pseudo-first-order rate competes with all unquenched decay channels.

This is `100 * k_q[Red] / (1/τ₀ + k_q[Red])`, written in the equivalent
dimensionless form that avoids an intermediate reciprocal.
-/
def dynamicQuenchingPercent (input : QuenchingInput) : ℝ :=
  100 * sternVolmerFactor input / (1 + sternVolmerFactor input)

/-- Under the physical side conditions, the dimensionless formula is exactly
the desired pseudo-first-order rate divided by the sum of the quenching and
unquenched decay rates. -/
theorem dynamicQuenchingPercent_eq_competingRates
    (input : QuenchingInput) (hInput : PhysicallyAdmissible input) :
    dynamicQuenchingPercent input =
      100 * pseudoFirstOrderQuenchingRate input /
        (unquenchedDecayRate input + pseudoFirstOrderQuenchingRate input) := by
  rcases hInput with ⟨hk, hc, hτ⟩
  have hτ0 : input.unquenchedLifetime_seconds ≠ 0 := ne_of_gt hτ
  have hPseudo :
      0 < input.bimolecularRateConstant_perMolarSecond *
        input.reductantConcentration_molar :=
    mul_pos hk hc
  have hFactor :
      0 < input.bimolecularRateConstant_perMolarSecond *
        input.reductantConcentration_molar * input.unquenchedLifetime_seconds :=
    mul_pos hPseudo hτ
  have hDimensionlessDenominator :
      1 + input.bimolecularRateConstant_perMolarSecond *
        input.reductantConcentration_molar * input.unquenchedLifetime_seconds ≠ 0 :=
    ne_of_gt (add_pos (by norm_num) hFactor)
  have hRateDenominator :
      1 / input.unquenchedLifetime_seconds +
        input.bimolecularRateConstant_perMolarSecond *
          input.reductantConcentration_molar ≠ 0 :=
    ne_of_gt (add_pos (one_div_pos.mpr hτ) hPseudo)
  unfold dynamicQuenchingPercent sternVolmerFactor
    pseudoFirstOrderQuenchingRate unquenchedDecayRate
  field_simp [hτ0, hDimensionlessDenominator, hRateDenominator]

/-- Exact source inputs for the singlet state:
`k_S = 2.7 × 10⁹ M⁻¹ s⁻¹`, `[Red] = 0.1 M`, and `τ₀(S₁) = 2.9 ns`.
-/
def s1Input : QuenchingInput where
  state := .singletS1
  bimolecularRateConstant_perMolarSecond := (27 : ℝ) / 10 * (10 : ℝ) ^ 9
  reductantConcentration_molar := (1 : ℝ) / 10
  unquenchedLifetime_seconds := (29 : ℝ) / 10 * (1 / (10 : ℝ) ^ 9)

/-- Exact source inputs for the triplet state:
`k_T = 1.5 × 10⁸ M⁻¹ s⁻¹`, `[Red] = 0.1 M`, and `τ₀(T₁) = 84 μs`.
-/
def t1Input : QuenchingInput where
  state := .tripletT1
  bimolecularRateConstant_perMolarSecond := (15 : ℝ) / 10 * (10 : ℝ) ^ 8
  reductantConcentration_molar := (1 : ℝ) / 10
  unquenchedLifetime_seconds := (84 : ℝ) * (1 / (10 : ℝ) ^ 6)

/-- Unrounded source-derived percentage quenching of `S₁`. -/
def s1QuenchingRawPercent : ℝ :=
  dynamicQuenchingPercent s1Input

/-- Unrounded source-derived percentage quenching of `T₁`. -/
def t1QuenchingRawPercent : ℝ :=
  dynamicQuenchingPercent t1Input

/-- End-to-end exact derivation specification for the `S₁` output. -/
def S1RawDerivationSpec : Prop :=
  PhysicallyAdmissible s1Input ∧
    sternVolmerFactor s1Input = (783 : ℝ) / 1000 ∧
    s1QuenchingRawPercent = (78300 : ℝ) / 1783

/-- End-to-end exact derivation specification for the `T₁` output. -/
def T1RawDerivationSpec : Prop :=
  PhysicallyAdmissible t1Input ∧
    sternVolmerFactor t1Input = (1260 : ℝ) ∧
    t1QuenchingRawPercent = (126000 : ℝ) / 1261

/-- The raw result contract covers both requested outputs, in source order. -/
def RawResult : Prop :=
  S1RawDerivationSpec ∧ T1RawDerivationSpec

/-- The exact source constants and the transparent competing-rate model imply
both unrounded requested outputs. -/
theorem rawResult : RawResult := by
  norm_num [RawResult, S1RawDerivationSpec, T1RawDerivationSpec,
    PhysicallyAdmissible, sternVolmerFactor, s1QuenchingRawPercent,
    t1QuenchingRawPercent, dynamicQuenchingPercent, s1Input, t1Input]

/-- Retains the source's qualitative `k_F ≫ k_ISC` condition explicitly.
The numerical result is independent of a decomposition into `k_F` and
`k_ISC`, because the source directly supplies the total unquenched lifetime.
-/
theorem rawResult_under_fluorescence_dominance
    (fluorescenceRate intersystemCrossingRate : ℝ)
    (_hDominance : QualitativeRateDominance fluorescenceRate intersystemCrossingRate) :
    RawResult := by
  exact rawResult

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"s1_quenching","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"43.9","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.T8A9.s1QuenchingRawPercent","reporting_declaration":"IChO2026Problems.T8A9.s1QuenchingReported"}
theorem s1QuenchingReported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      s1QuenchingRawPercent ((439 : ℝ) / 10) ((1 : ℝ) / 10) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ?_, ?_⟩
  · exact ⟨439, by norm_num⟩
  · have hRaw : 0 ≤ s1QuenchingRawPercent := by
      norm_num [s1QuenchingRawPercent, dynamicQuenchingPercent,
        sternVolmerFactor, s1Input]
    rw [if_pos hRaw]
    norm_num [s1QuenchingRawPercent, dynamicQuenchingPercent,
      sternVolmerFactor, s1Input]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"t1_quenching","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"99.9","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.T8A9.t1QuenchingRawPercent","reporting_declaration":"IChO2026Problems.T8A9.t1QuenchingReported"}
theorem t1QuenchingReported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      t1QuenchingRawPercent ((999 : ℝ) / 10) ((1 : ℝ) / 10) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ?_, ?_⟩
  · exact ⟨999, by norm_num⟩
  · have hRaw : 0 ≤ t1QuenchingRawPercent := by
      norm_num [t1QuenchingRawPercent, dynamicQuenchingPercent,
        sternVolmerFactor, t1Input]
    rw [if_pos hRaw]
    norm_num [t1QuenchingRawPercent, dynamicQuenchingPercent,
      sternVolmerFactor, t1Input]

/-- The final reporting contract covers both requested outputs, in source
order, and uses no intermediate rounding. -/
def ReportedResult : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum
      s1QuenchingRawPercent ((439 : ℝ) / 10) ((1 : ℝ) / 10) ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      t1QuenchingRawPercent ((999 : ℝ) / 10) ((1 : ℝ) / 10)

theorem reportedResult : ReportedResult := by
  exact ⟨s1QuenchingReported, t1QuenchingReported⟩

end

end IChO2026Problems.T8A9
