import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem T8-A9

This file formalizes the reductive quenching calculation for the singlet `S₁`
and triplet `T₁` states of the photosensitizer.  All printed decimal data are
represented by exact rational real numbers in coherent units before any
arithmetic is performed.

The governing kinetic model is competition between the intrinsic first-order
disappearance rate `1 / τ₀` and the pseudo-first-order quenching rate
`k * [Red]`.  Consequently the quenching percentage is

`100 * (k * [Red]) / (1 / τ₀ + k * [Red])`.

No staged material transformation is inferred here: the depicted reactions
only identify the two bimolecular quenching channels used by the kinetic model.
-/

namespace IChO2026Problems
namespace ProblemIcho2026T8A9

noncomputable section

/-- The two electronically excited photosensitizer states requested in A9. -/
inductive ExcitedState
  | singletS1
  | tripletT1
  deriving DecidableEq, Fintype

/-- Species explicitly occurring in the two reductive-quenching equations. -/
inductive PhotoredoxSpecies
  | photosensitizerS1
  | photosensitizerT1
  | reductant
  | photosensitizerRadicalAnion
  | reductantRadicalCation
  deriving DecidableEq, Fintype

/-- The photosensitizer species associated with an excited-state label. -/
def excitedPhotosensitizer : ExcitedState → PhotoredoxSpecies
  | .singletS1 => .photosensitizerS1
  | .tripletT1 => .photosensitizerT1

/-- Stoichiometric source complex `PS(state) + Red` printed on page 5. -/
def reductiveQuenchingSource (state : ExcitedState) :
    CRNT.Complex PhotoredoxSpecies :=
  fun species =>
    match species with
    | .photosensitizerS1 => if state = .singletS1 then 1 else 0
    | .photosensitizerT1 => if state = .tripletT1 then 1 else 0
    | .reductant => 1
    | .photosensitizerRadicalAnion => 0
    | .reductantRadicalCation => 0

/-- Stoichiometric target complex `PS•⁻ + Red•⁺` printed on page 5. -/
def reductiveQuenchingTarget : CRNT.Complex PhotoredoxSpecies :=
  fun species =>
    match species with
    | .photosensitizerRadicalAnion => 1
    | .reductantRadicalCation => 1
    | .photosensitizerS1 => 0
    | .photosensitizerT1 => 0
    | .reductant => 0

/-- Either printed reductive-quenching arrow as a directed CRNT reaction. -/
def reductiveQuenchingReaction (state : ExcitedState) :
    CRNT.Reaction PhotoredoxSpecies where
  source := reductiveQuenchingSource state
  target := reductiveQuenchingTarget

/-- The source and target complexes of either printed arrow are distinct. -/
theorem reductiveQuenchingReaction_nontrivial (state : ExcitedState) :
    CRNT.Reaction.Nontrivial (reductiveQuenchingReaction state) := by
  unfold CRNT.Reaction.Nontrivial
  intro h
  have hAtReductant := congrFun h PhotoredoxSpecies.reductant
  norm_num [reductiveQuenchingReaction, reductiveQuenchingSource,
    reductiveQuenchingTarget] at hAtReductant

/-- Named arrows in the Jablonski diagram.  Only `reductiveQuenching` carries
numerical rate data in the current subquestion. -/
inductive PhotophysicalProcess
  | fluorescence
  | internalConversion
  | intersystemCrossing
  | reverseIntersystemCrossing
  | phosphorescence
  | tripletNonradiative
  | reductiveQuenching (state : ExcitedState)
  deriving DecidableEq

/-- A concentration whose stored real value is measured in molar (`M`). -/
structure MolarConcentration where
  value : ℝ

/-- A bimolecular rate constant in `M⁻¹ s⁻¹`. -/
structure BimolecularRateConstant where
  value : ℝ

/-- A first-order rate constant in `s⁻¹`. -/
structure FirstOrderRateConstant where
  value : ℝ

/-- A lifetime converted to seconds. -/
structure LifetimeSeconds where
  value : ℝ

/-- Kinetic data tied to one chemically identified excited state. -/
structure StateKinetics where
  state : ExcitedState
  bimolecularRate : BimolecularRateConstant
  unquenchedLifetime : LifetimeSeconds

/-- `[Red] = 0.1 M`, exact as stipulated by the problem. -/
def reductantConcentration : MolarConcentration :=
  ⟨(1 : ℝ) / 10⟩

/-- `k_S = 2.7 × 10⁹ M⁻¹ s⁻¹` and `τ₀(S₁) = 2.9 ns` in SI units. -/
def s1Kinetics : StateKinetics where
  state := .singletS1
  bimolecularRate := ⟨2700000000⟩
  unquenchedLifetime := ⟨(29 : ℝ) / 10000000000⟩

/-- `k_T = 1.5 × 10⁸ M⁻¹ s⁻¹` and `τ₀(T₁) = 84 μs` in SI units. -/
def t1Kinetics : StateKinetics where
  state := .tripletT1
  bimolecularRate := ⟨150000000⟩
  unquenchedLifetime := ⟨(84 : ℝ) / 1000000⟩

/-- Positivity side conditions for every printed kinetic input. -/
def SourceKineticSideConditions : Prop :=
  0 < reductantConcentration.value ∧
  0 < s1Kinetics.bimolecularRate.value ∧
  0 < s1Kinetics.unquenchedLifetime.value ∧
  0 < t1Kinetics.bimolecularRate.value ∧
  0 < t1Kinetics.unquenchedLifetime.value

theorem sourceKineticSideConditions : SourceKineticSideConditions := by
  unfold SourceKineticSideConditions reductantConcentration s1Kinetics t1Kinetics
  norm_num

/-- Quantitative reading of the qualitative note `k_F >> k_ISC`: both rates
are physically nonnegative and fluorescence exceeds ISC by some multiplicative
factor strictly greater than one.  The source supplies no numerical factor, so
none is invented here. -/
def FluorescenceDominatesISC
    (kF kISC : FirstOrderRateConstant) : Prop :=
  0 ≤ kISC.value ∧
  ∃ separationFactor : ℝ,
    1 < separationFactor ∧
    separationFactor * kISC.value ≤ kF.value

/-- Intrinsic first-order disappearance rate `1 / τ₀` in `s⁻¹`. -/
def intrinsicDisappearanceRatePerSecond (kinetics : StateKinetics) : ℝ :=
  1 / kinetics.unquenchedLifetime.value

/-- Pseudo-first-order quenching rate `k [Red]` in `s⁻¹`. -/
def pseudoFirstOrderQuenchingRatePerSecond
    (kinetics : StateKinetics) (quencher : MolarConcentration) : ℝ :=
  kinetics.bimolecularRate.value * quencher.value

/-- The dimensionless Stern--Volmer loading `k [Red] τ₀`. -/
def quenchingLoading
    (kinetics : StateKinetics) (quencher : MolarConcentration) : ℝ :=
  kinetics.bimolecularRate.value * quencher.value *
    kinetics.unquenchedLifetime.value

/-- Percentage of excited-state decay events assigned to the quenching channel
under competition of the intrinsic and pseudo-first-order rates. -/
def quenchingPercent
    (kinetics : StateKinetics) (quencher : MolarConcentration) : ℝ :=
  100 * pseudoFirstOrderQuenchingRatePerSecond kinetics quencher /
    (intrinsicDisappearanceRatePerSecond kinetics +
      pseudoFirstOrderQuenchingRatePerSecond kinetics quencher)

/-- The competing-rate expression is the usual Stern--Volmer loading formula.
All hypotheses are explicit so that division by zero and rate signs are not
silently discarded. -/
theorem quenchingPercent_eq_loading
    (kinetics : StateKinetics) (quencher : MolarConcentration)
    (hRate : 0 ≤ kinetics.bimolecularRate.value)
    (hConcentration : 0 ≤ quencher.value)
    (hLifetime : 0 < kinetics.unquenchedLifetime.value) :
    quenchingPercent kinetics quencher =
      100 * quenchingLoading kinetics quencher /
        (1 + quenchingLoading kinetics quencher) := by
  unfold quenchingPercent quenchingLoading
  unfold pseudoFirstOrderQuenchingRatePerSecond intrinsicDisappearanceRatePerSecond
  have hQuenchingRate :
      0 ≤ kinetics.bimolecularRate.value * quencher.value :=
    mul_nonneg hRate hConcentration
  have hIntrinsicRate : 0 < 1 / kinetics.unquenchedLifetime.value :=
    one_div_pos.mpr hLifetime
  have hCompetingRate :
      0 < 1 / kinetics.unquenchedLifetime.value +
        kinetics.bimolecularRate.value * quencher.value :=
    add_pos_of_pos_of_nonneg hIntrinsicRate hQuenchingRate
  have hLoadingRate :
      0 < 1 + kinetics.bimolecularRate.value * quencher.value *
        kinetics.unquenchedLifetime.value :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg hQuenchingRate hLifetime.le)
  field_simp [ne_of_gt hLifetime, ne_of_gt hCompetingRate,
    ne_of_gt hLoadingRate]

/-- Exact, unrounded percentage requested for the `S₁` state. -/
def s1QuenchingPercentRaw : ℝ :=
  quenchingPercent s1Kinetics reductantConcentration

/-- Exact, unrounded percentage requested for the `T₁` state. -/
def t1QuenchingPercentRaw : ℝ :=
  quenchingPercent t1Kinetics reductantConcentration

/-- Source-to-result derivation contract.  It records both intermediate
dimensionless loadings, both exact percentages, and narrow certified intervals
without performing intermediate rounding. -/
def RawResultSpec : Prop :=
  quenchingLoading s1Kinetics reductantConcentration = (783 : ℝ) / 1000 ∧
  quenchingLoading t1Kinetics reductantConcentration = (1260 : ℝ) ∧
  s1QuenchingPercentRaw = (78300 : ℝ) / 1783 ∧
  t1QuenchingPercentRaw = (126000 : ℝ) / 1261 ∧
  (4391 : ℝ) / 100 < s1QuenchingPercentRaw ∧
  s1QuenchingPercentRaw < (1098 : ℝ) / 25 ∧
  (2498 : ℝ) / 25 < t1QuenchingPercentRaw ∧
  t1QuenchingPercentRaw < (9993 : ℝ) / 100

/-- Raw answer-blind result: both requested values are derived from the printed
rates, concentration, and lifetimes. -/
theorem rawResult : RawResultSpec := by
  unfold RawResultSpec
  norm_num [quenchingLoading, s1Kinetics, t1Kinetics,
    reductantConcentration, s1QuenchingPercentRaw, t1QuenchingPercentRaw,
    quenchingPercent, pseudoFirstOrderQuenchingRatePerSecond,
    intrinsicDisappearanceRatePerSecond]

/-- Candidate display for `S₁`, chosen only after deriving the raw value. -/
def s1QuenchingPercentReported : ℝ := (439 : ℝ) / 10

/-- Candidate display for `T₁`, chosen only after deriving the raw value. -/
def t1QuenchingPercentReported : ℝ := (999 : ℝ) / 10

/-- On the interval `[10,100)`, three significant figures use quantum `0.1`.
This problem-specific relation is deliberately narrower than a global
significant-figure implementation. -/
def ThreeSignificantFigurePercentQuantum (raw quantum : ℝ) : Prop :=
  10 ≤ raw ∧ raw < 100 ∧ quantum = (1 : ℝ) / 10

/-- Mechanical three-significant-figure certificate for the `S₁` output. -/
theorem s1QuenchingReporting :
    IChO2026Chem.Reporting.ReportsAtQuantum
      s1QuenchingPercentRaw ((439 : ℝ) / 10) ((1 : ℝ) / 10) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨439, by norm_num⟩, ?_⟩
  rw [if_pos]
  · norm_num [s1QuenchingPercentRaw, quenchingPercent, s1Kinetics,
      reductantConcentration, pseudoFirstOrderQuenchingRatePerSecond,
      intrinsicDisappearanceRatePerSecond]
  · norm_num [s1QuenchingPercentRaw, quenchingPercent, s1Kinetics,
      reductantConcentration, pseudoFirstOrderQuenchingRatePerSecond,
      intrinsicDisappearanceRatePerSecond]

/-- Mechanical three-significant-figure certificate for the `T₁` output. -/
theorem t1QuenchingReporting :
    IChO2026Chem.Reporting.ReportsAtQuantum
      t1QuenchingPercentRaw ((999 : ℝ) / 10) ((1 : ℝ) / 10) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨999, by norm_num⟩, ?_⟩
  rw [if_pos]
  · norm_num [t1QuenchingPercentRaw, quenchingPercent, t1Kinetics,
      reductantConcentration, pseudoFirstOrderQuenchingRatePerSecond,
      intrinsicDisappearanceRatePerSecond]
  · norm_num [t1QuenchingPercentRaw, quenchingPercent, t1Kinetics,
      reductantConcentration, pseudoFirstOrderQuenchingRatePerSecond,
      intrinsicDisappearanceRatePerSecond]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"s1_quenching","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"439/10","reporting_quantum":"1/10","raw_declaration":"IChO2026Problems.ProblemIcho2026T8A9.s1QuenchingPercentRaw","reporting_declaration":"IChO2026Problems.ProblemIcho2026T8A9.s1QuenchingReporting"}
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"t1_quenching","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"999/10","reporting_quantum":"1/10","raw_declaration":"IChO2026Problems.ProblemIcho2026T8A9.t1QuenchingPercentRaw","reporting_declaration":"IChO2026Problems.ProblemIcho2026T8A9.t1QuenchingReporting"}

/-- Combined reported-result contract covering both requested outputs in their
source order. -/
def ReportedResultSpec : Prop :=
  ThreeSignificantFigurePercentQuantum s1QuenchingPercentRaw ((1 : ℝ) / 10) ∧
  IChO2026Chem.Reporting.ReportsAtQuantum
    s1QuenchingPercentRaw s1QuenchingPercentReported ((1 : ℝ) / 10) ∧
  ThreeSignificantFigurePercentQuantum t1QuenchingPercentRaw ((1 : ℝ) / 10) ∧
  IChO2026Chem.Reporting.ReportsAtQuantum
    t1QuenchingPercentRaw t1QuenchingPercentReported ((1 : ℝ) / 10)

theorem reportedResult : ReportedResultSpec := by
  unfold ReportedResultSpec ThreeSignificantFigurePercentQuantum
  refine ⟨?_, s1QuenchingReporting, ?_, t1QuenchingReporting⟩
  · norm_num [s1QuenchingPercentRaw, quenchingPercent, s1Kinetics,
      reductantConcentration, pseudoFirstOrderQuenchingRatePerSecond,
      intrinsicDisappearanceRatePerSecond]
  · norm_num [t1QuenchingPercentRaw, quenchingPercent, t1Kinetics,
      reductantConcentration, pseudoFirstOrderQuenchingRatePerSecond,
      intrinsicDisappearanceRatePerSecond]

/-- Assumption/target split for the complete current subquestion.  The
qualitative fluorescence/ISC dominance note is retained as an assumption, while
the measured `τ₀` values make the two quenching calculations independent of an
invented numerical `k_F / k_ISC` ratio. -/
theorem requestedQuenchingPercentages
    (kF kISC : FirstOrderRateConstant)
    (_hDominance : FluorescenceDominatesISC kF kISC) :
    RawResultSpec ∧ ReportedResultSpec := by
  exact ⟨rawResult, reportedResult⟩

end
end ProblemIcho2026T8A9
end IChO2026Problems
