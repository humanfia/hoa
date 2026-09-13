import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T4, part A5

The neutron starts at `2 MeV = 2 * 10^6 eV` and is slowed to `0.012 eV`.
For water, the mean logarithmic energy decrement per collision is `0.948`.
Since logarithmic decrements add over collisions, an average collision count
`n` obeys

`n * 0.948 = log ((2 * 10^6) / 0.012)`.

The exact real-valued result is kept separate from its final three-significant-
figure report.
-/

namespace IChO2026Problems.T4A5

/-- The moderator named in the problem. -/
inductive Moderator where
  | water
  deriving DecidableEq

/-- Source data for one neutron-moderation calculation, expressed in a common
energy unit so that the logarithm receives a dimensionless ratio. -/
structure ModerationInput where
  moderator : Moderator
  initialEnergyEV : ℝ
  finalEnergyEV : ℝ
  logarithmicDecrementPerCollision : ℝ

/-- One megaelectronvolt is `10^6` electronvolts. -/
def electronVoltsPerMegaElectronVolt : ℝ := 10 ^ 6

/-- The data printed for the water-moderated neutron in T4-A5. -/
noncomputable def waterModerationInput : ModerationInput where
  moderator := .water
  initialEnergyEV := 2 * electronVoltsPerMegaElectronVolt
  finalEnergyEV := 12 / 1000
  logarithmicDecrementPerCollision := 948 / 1000

/-- Positivity and the slowing direction needed for the logarithmic model. -/
def ValidModerationInput (input : ModerationInput) : Prop :=
  0 < input.initialEnergyEV ∧
    0 < input.finalEnergyEV ∧
    input.finalEnergyEV < input.initialEnergyEV ∧
    0 < input.logarithmicDecrementPerCollision

/-- Governing relation for a constant average logarithmic decrement: after an
average of `collisions` scatterings, the total logarithmic energy decrease is
`collisions` times the decrement per collision. -/
def AverageCollisionCountSpec
    (input : ModerationInput) (collisions : ℝ) : Prop :=
  ValidModerationInput input ∧
    0 ≤ collisions ∧
    collisions * input.logarithmicDecrementPerCollision =
      Real.log (input.initialEnergyEV / input.finalEnergyEV)

/-- Exact, unrounded average collision count obtained by solving the governing
relation with all source values retained exactly. -/
noncomputable def averageCollisionCount : ℝ :=
  Real.log
      (waterModerationInput.initialEnergyEV /
        waterModerationInput.finalEnergyEV) /
    waterModerationInput.logarithmicDecrementPerCollision

/-- The candidate satisfies the source-derived moderation equation and is its
unique nonnegative real solution. -/
def AverageCollisionCountDerivation : Prop :=
  AverageCollisionCountSpec waterModerationInput averageCollisionCount ∧
    ∀ collisions : ℝ,
      AverageCollisionCountSpec waterModerationInput collisions →
        collisions = averageCollisionCount

/-- Raw answer-blind result contract.  The rational interval is a certified
enclosure of the exact logarithmic expression, not an equality to a rounded
decimal. -/
theorem averageCollisionCount_raw :
    (AverageCollisionCountDerivation) ∧
      (((499 : ℝ) / 25) ≤ (averageCollisionCount) ∧
        (averageCollisionCount) ≤ ((999 : ℝ) / 50)) := by
  have hratio :
      1 < waterModerationInput.initialEnergyEV /
        waterModerationInput.finalEnergyEV := by
    norm_num [waterModerationInput, electronVoltsPerMegaElectronVolt]
  have hdecrement :
      0 < waterModerationInput.logarithmicDecrementPerCollision := by
    norm_num [waterModerationInput]
  have hlogPositive :
      0 < Real.log
        (waterModerationInput.initialEnergyEV /
          waterModerationInput.finalEnergyEV) :=
    Real.log_pos hratio
  have hcandidateEquation :
      averageCollisionCount *
          waterModerationInput.logarithmicDecrementPerCollision =
        Real.log
          (waterModerationInput.initialEnergyEV /
            waterModerationInput.finalEnergyEV) := by
    simp [averageCollisionCount, ne_of_gt hdecrement]
  have hderivation : AverageCollisionCountDerivation := by
    constructor
    · refine ⟨?_, ?_, hcandidateEquation⟩
      · norm_num [ValidModerationInput, waterModerationInput,
          electronVoltsPerMegaElectronVolt]
      · simpa [averageCollisionCount] using
          (div_pos hlogPositive hdecrement).le
    · intro collisions hcollisions
      rw [averageCollisionCount]
      exact (eq_div_iff (ne_of_gt hdecrement)).2 hcollisions.2.2
  have hlogIdentity :
      Real.log
          (waterModerationInput.initialEnergyEV /
            waterModerationInput.finalEnergyEV) =
        8 * Real.log 2 + 9 * Real.log 5 - Real.log 3 := by
    rw [show waterModerationInput.initialEnergyEV /
          waterModerationInput.finalEnergyEV =
        ((2 : ℝ) ^ 8 * (5 : ℝ) ^ 9) / 3 by
      norm_num [waterModerationInput, electronVoltsPerMegaElectronVolt]]
    rw [Real.log_div (by positivity) (by norm_num),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
  have hlogLower :
      ((118263 : ℝ) / 6250) <
        Real.log
          (waterModerationInput.initialEnergyEV /
            waterModerationInput.finalEnergyEV) := by
    rw [hlogIdentity]
    nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9,
      Real.log_three_lt_d9]
  have hlogUpper :
      Real.log
          (waterModerationInput.initialEnergyEV /
            waterModerationInput.finalEnergyEV) <
        ((236763 : ℝ) / 12500) := by
    rw [hlogIdentity]
    nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9,
      Real.log_three_gt_d9]
  refine ⟨hderivation, ?_, ?_⟩
  · rw [averageCollisionCount]
    apply (le_div_iff₀ hdecrement).2
    norm_num [waterModerationInput] at hlogLower ⊢
    exact hlogLower.le
  · rw [averageCollisionCount]
    apply (div_le_iff₀ hdecrement).2
    norm_num [waterModerationInput] at hlogUpper ⊢
    exact hlogUpper.le

/-- Final reporting contract: `20.0` is the nearest multiple of `0.1`, using
the project-fixed half-away-from-zero tie convention. -/
theorem averageCollisionCount_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      (averageCollisionCount) ((200 : ℝ) / 10) ((1 : ℝ) / 10) := by
  rcases averageCollisionCount_raw with ⟨hderivation, hlower, hupper⟩
  have hnonnegative : 0 ≤ averageCollisionCount := hderivation.1.2.1
  refine ⟨by norm_num, ?_, ?_⟩
  · refine ⟨(200 : ℤ), by norm_num⟩
  · rw [if_pos hnonnegative]
    constructor
    · norm_num at hlower ⊢
      linarith
    · norm_num at hupper ⊢
      linarith

/-- Canonical rational form used by the trusted numeric-reporting probe. -/
theorem averageCollisionCount_reportingCertificate :
    IChO2026Chem.Reporting.ReportsAtQuantum
      averageCollisionCount (20 : ℝ) ((1 : ℝ) / 10) := by
  have hcanonical : ((200 : ℝ) / 10) = 20 := by norm_num
  rw [← hcanonical]
  exact averageCollisionCount_reported

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"average_collision_count","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"20.0","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.T4A5.averageCollisionCount","reporting_declaration":"IChO2026Problems.T4A5.averageCollisionCount_reportingCertificate"}

end IChO2026Problems.T4A5
