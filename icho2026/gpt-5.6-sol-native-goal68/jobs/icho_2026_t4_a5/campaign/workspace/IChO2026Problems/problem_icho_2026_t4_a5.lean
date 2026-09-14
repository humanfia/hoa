import IChO2026Chem.Reporting
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# IChO 2026, theory problem 4, part 4.5

The printed problem gives an initial neutron energy of `2 MeV`, a final energy
of `0.012 eV`, and the logarithmic energy decrement of water `ξ = 0.948`.
All three printed decimal data are represented exactly below.  The conversion
`1 MeV = 10^6 eV` is used to put the energies in a common unit.

The problem's constant-decrement model says that `n` average collisions give a
total logarithmic decrement `n * ξ`.  Thus the requested real-valued average
collision count is the unique solution of

`n * ξ = log (E_initial / E_final)`.

The remaining theorems derive this solution, rigorously bound its logarithm,
and prove that the displayed answer `20.0` satisfies the fixed three-significant-
figure reporting contract (quantum `0.1`).
-/

namespace IChO2026Problems.T4A5

open IChO2026Chem.Reporting

noncomputable section

/-! ## Problem-stated inputs and the unit conversion -/

/-- The initial energy printed in the problem, in MeV. -/
def initialEnergyMeV : ℝ := 2

/-- Exact conversion factor from MeV to eV. -/
def electronVoltsPerMeV : ℝ := 10 ^ 6

/-- The initial energy expressed in eV so that both energies use the same unit. -/
def initialEnergyEV : ℝ := initialEnergyMeV * electronVoltsPerMeV

/-- The final energy `0.012 eV`, represented exactly. -/
def finalEnergyEV : ℝ := 12 / 1000

/-- The water logarithmic energy decrement `0.948`, represented exactly. -/
def waterLogDecrement : ℝ := 948 / 1000

theorem initialEnergyEV_value : initialEnergyEV = 2000000 := by
  norm_num [initialEnergyEV, initialEnergyMeV, electronVoltsPerMeV]

theorem finalEnergyEV_value : finalEnergyEV = 3 / 250 := by
  norm_num [finalEnergyEV]

theorem waterLogDecrement_value : waterLogDecrement = 237 / 250 := by
  norm_num [waterLogDecrement]

theorem waterLogDecrement_pos : 0 < waterLogDecrement := by
  norm_num [waterLogDecrement]

/-! ## Derivation of the average collision count -/

/-- The total logarithmic decrease needed between the two stated energies. -/
def totalLogDecrement : ℝ := Real.log (initialEnergyEV / finalEnergyEV)

/-- The raw (unrounded) average number of collisions. -/
def averageCollisionCount : ℝ := totalLogDecrement / waterLogDecrement

/-- The moderation equation obtained by summing the same average logarithmic
decrement over `n` collisions. -/
def ModerationEquation (n : ℝ) : Prop :=
  n * waterLogDecrement = totalLogDecrement

/-- Solving a nonzero constant-decrement equation gives the collision-count
formula used here. -/
theorem count_eq_log_ratio_div_decrement
    {initial final decrement n : ℝ}
    (hdecrement : decrement ≠ 0)
    (hmodel : n * decrement = Real.log (initial / final)) :
    n = Real.log (initial / final) / decrement := by
  exact (eq_div_iff hdecrement).2 hmodel

theorem averageCollisionCount_satisfies :
    ModerationEquation averageCollisionCount := by
  unfold ModerationEquation averageCollisionCount
  exact div_mul_cancel₀ totalLogDecrement waterLogDecrement_pos.ne'

theorem averageCollisionCount_unique {n : ℝ}
    (hmodel : ModerationEquation n) : n = averageCollisionCount := by
  exact (eq_div_iff waterLogDecrement_pos.ne').2 hmodel

theorem averageCollisionCount_formula :
    averageCollisionCount =
      Real.log ((2 * 10 ^ 6 : ℝ) / (12 / 1000)) / (948 / 1000) := by
  rfl

/-! ## Certified numerical bounds and final reporting -/

theorem energyRatio_factorization :
    initialEnergyEV / finalEnergyEV = (2 : ℝ) ^ 8 * (5 : ℝ) ^ 9 / 3 := by
  norm_num [initialEnergyEV, initialEnergyMeV, electronVoltsPerMeV, finalEnergyEV]

theorem totalLogDecrement_decomposition :
    totalLogDecrement =
      8 * Real.log 2 + 9 * Real.log 5 - Real.log 3 := by
  rw [totalLogDecrement, energyRatio_factorization,
    Real.log_div (by positivity) (by norm_num),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  norm_num

/-- Tight rational bounds on the raw logarithmic energy ratio.  They follow
from mathlib's proved decimal bounds for `log 2`, `log 3`, and `log 5`. -/
theorem totalLogDecrement_bounds :
    (189315063643 / 10000000000 : ℝ) < totalLogDecrement ∧
      totalLogDecrement < (189315063713 / 10000000000 : ℝ) := by
  rw [totalLogDecrement_decomposition]
  constructor
  · linarith [Real.log_two_gt_d9, Real.log_five_gt_d9, Real.log_three_lt_d9]
  · linarith [Real.log_two_lt_d9, Real.log_five_lt_d9, Real.log_three_gt_d9]

/-- The exact raw expression lies strictly inside the rounding cell for
`20.0` at quantum `0.1`: `(19.95, 20.05)`. -/
theorem averageCollisionCount_rounding_interval :
    (399 / 20 : ℝ) < averageCollisionCount ∧
      averageCollisionCount < (401 / 20 : ℝ) := by
  constructor
  · rw [averageCollisionCount]
    apply (lt_div_iff₀ waterLogDecrement_pos).2
    nlinarith [totalLogDecrement_bounds.1, waterLogDecrement_value]
  · rw [averageCollisionCount]
    apply (div_lt_iff₀ waterLogDecrement_pos).2
    nlinarith [totalLogDecrement_bounds.2, waterLogDecrement_value]

/-- Submission object keeping the raw expression separate from its final
three-significant-figure display `20.0` (represented numerically by `20`). -/
def answerSubmission : NumericSubmission where
  rawValue := averageCollisionCount
  reportedValue := 20
  reportingQuantum := 1 / 10

theorem reported_twenty_at_quantum :
    ReportsAtQuantum averageCollisionCount 20 (1 / 10) := by
  have hbounds := averageCollisionCount_rounding_interval
  have hnonneg : 0 ≤ averageCollisionCount := by linarith [hbounds.1]
  refine ⟨by norm_num, ⟨200, by norm_num⟩, ?_⟩
  rw [if_pos hnonneg]
  constructor
  · have hleft : (20 : ℝ) - (1 / 10) / 2 = 399 / 20 := by norm_num
    rw [hleft]
    exact hbounds.1.le
  · have hright : (20 : ℝ) + (1 / 10) / 2 = 401 / 20 := by norm_num
    rw [hright]
    exact hbounds.2

theorem answerSubmission_valid :
    ValidNumericSubmission averageCollisionCount answerSubmission := by
  exact ⟨rfl, reported_twenty_at_quantum⟩

/-- Final theorem: the raw collision count solves the stated moderation law
uniquely, and `20.0` is its valid three-significant-figure report. -/
theorem icho_2026_t4_a5_answer :
    ModerationEquation averageCollisionCount ∧
      (∀ n : ℝ, ModerationEquation n → n = averageCollisionCount) ∧
      ValidNumericSubmission averageCollisionCount answerSubmission := by
  exact ⟨averageCollisionCount_satisfies,
    fun _ hmodel ↦ averageCollisionCount_unique hmodel,
    answerSubmission_valid⟩

#print axioms icho_2026_t4_a5_answer

end

end IChO2026Problems.T4A5
