import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026 T4-A5: neutron moderation in water

The problem gives the logarithmic energy decrement per collision and asks for
the average number of collisions needed to reduce a neutron's energy.  Energy
magnitudes are represented in explicitly named MeV/eV fields; the logarithm is
taken only after converting both endpoint energies to eV, so its argument is
dimensionless.
-/

namespace IChO2026Problems
namespace T4A5

/-- The particle whose kinetic energy is being moderated. -/
inductive Particle where
  | neutron
  deriving DecidableEq

/-- The material used as moderator in the stated experiment. -/
inductive Moderator where
  | water
  deriving DecidableEq

/-- Source data for one neutron-slowing scenario.

`initialEnergyMeV` and `finalEnergyEV` retain the units in which the two source
values are printed.  The decrement is dimensionless. -/
structure NeutronSlowingScenario where
  particle : Particle
  moderator : Moderator
  initialEnergyMeV : ℝ
  finalEnergyEV : ℝ
  logarithmicEnergyDecrement : ℝ

/-- Exact conversion of the source's initial energy from MeV to eV. -/
def initialEnergyInElectronVolts (scenario : NeutronSlowingScenario) : ℝ :=
  scenario.initialEnergyMeV * (10 : ℝ) ^ 6

/-- The complete problem-stated scenario: a neutron slowed in water from
`2 MeV` to `0.012 eV`, with water decrement `0.948`. -/
noncomputable def sourceScenario : NeutronSlowingScenario where
  particle := .neutron
  moderator := .water
  initialEnergyMeV := 2
  finalEnergyEV := (12 : ℝ) / 1000
  logarithmicEnergyDecrement := (948 : ℝ) / 1000

/-- The cumulative form of the constant per-collision logarithmic-decrement
law.  For an average collision count `n`, additivity of logarithmic decrements
gives `n * ξ = log (E_initial / E_final)`. -/
def SatisfiesAverageCollisionLaw
    (scenario : NeutronSlowingScenario) (n : ℝ) : Prop :=
  0 < scenario.initialEnergyMeV ∧
    0 < scenario.finalEnergyEV ∧
    scenario.finalEnergyEV < initialEnergyInElectronVolts scenario ∧
    0 < scenario.logarithmicEnergyDecrement ∧
    0 ≤ n ∧
    n * scenario.logarithmicEnergyDecrement =
      Real.log
        (initialEnergyInElectronVolts scenario / scenario.finalEnergyEV)

/-- The unrounded, end-to-end average collision count derived from the source
inputs.  No intermediate value is rounded. -/
noncomputable def averageCollisionCountRaw : ℝ :=
  Real.log
      (initialEnergyInElectronVolts sourceScenario /
        sourceScenario.finalEnergyEV) /
    sourceScenario.logarithmicEnergyDecrement

/-- Problem-specific derivation specification for the raw result.  It records
the particle and moderator identities, all printed values, satisfaction of the
cumulative decrement law, and uniqueness of the resulting nonnegative average
collision count. -/
def averageCollisionCountDerivationSpec : Prop :=
  sourceScenario.particle = .neutron ∧
    sourceScenario.moderator = .water ∧
    sourceScenario.initialEnergyMeV = 2 ∧
    sourceScenario.finalEnergyEV = (12 : ℝ) / 1000 ∧
    sourceScenario.logarithmicEnergyDecrement = (948 : ℝ) / 1000 ∧
    SatisfiesAverageCollisionLaw sourceScenario averageCollisionCountRaw ∧
    ∀ n : ℝ,
      SatisfiesAverageCollisionLaw sourceScenario n →
        n = averageCollisionCountRaw

/-- The display candidate fixed by the source report's three-significant-figure
policy.  Its validity is certified separately below. -/
def averageCollisionCountReported : ℝ := 20

/-- Raw result contract: the source-derived specification holds and the exact
logarithmic expression lies in a nondegenerate rational enclosure. -/
theorem averageCollisionCount_raw_result :
    (IChO2026Problems.T4A5.averageCollisionCountDerivationSpec) ∧
      (((19969 : ℝ) / 1000) ≤
          (IChO2026Problems.T4A5.averageCollisionCountRaw) ∧
        (IChO2026Problems.T4A5.averageCollisionCountRaw) ≤
          ((1997 : ℝ) / 100)) := by
  constructor
  · unfold averageCollisionCountDerivationSpec
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · unfold SatisfiesAverageCollisionLaw averageCollisionCountRaw
      dsimp [sourceScenario, initialEnergyInElectronVolts]
      refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
      · exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
      · field_simp
    · intro n hn
      unfold SatisfiesAverageCollisionLaw at hn
      dsimp [sourceScenario, initialEnergyInElectronVolts] at hn
      unfold averageCollisionCountRaw
      dsimp [sourceScenario, initialEnergyInElectronVolts]
      apply (eq_div_iff (by norm_num : (948 : ℝ) / 1000 ≠ 0)).2
      exact hn.2.2.2.2.2
  · have hraw :
        averageCollisionCountRaw =
          Real.log ((500000000 : ℝ) / 3) / ((948 : ℝ) / 1000) := by
      norm_num [averageCollisionCountRaw, sourceScenario,
        initialEnergyInElectronVolts]
    have hlog_factorization :
        Real.log ((500000000 : ℝ) / 3) =
          8 * Real.log 2 + 9 * Real.log 5 - Real.log 3 := by
      calc
        Real.log ((500000000 : ℝ) / 3) =
            Real.log (500000000 : ℝ) - Real.log 3 := by
              rw [Real.log_div] <;> norm_num
        _ = Real.log (((2 : ℝ) ^ 8) * ((5 : ℝ) ^ 9)) -
              Real.log 3 := by norm_num
        _ = (Real.log ((2 : ℝ) ^ 8) + Real.log ((5 : ℝ) ^ 9)) -
              Real.log 3 := by
                rw [Real.log_mul] <;> norm_num
        _ = 8 * Real.log 2 + 9 * Real.log 5 - Real.log 3 := by
              rw [Real.log_pow, Real.log_pow]
              norm_num
    have hlog_lower :
        ((19969 : ℝ) / 1000) * ((948 : ℝ) / 1000) ≤
          Real.log ((500000000 : ℝ) / 3) := by
      rw [hlog_factorization]
      linarith [Real.log_two_gt_d9, Real.log_five_gt_d9,
        Real.log_three_lt_d9]
    have hlog_upper :
        Real.log ((500000000 : ℝ) / 3) ≤
          ((1997 : ℝ) / 100) * ((948 : ℝ) / 1000) := by
      rw [hlog_factorization]
      linarith [Real.log_two_lt_d9, Real.log_five_lt_d9,
        Real.log_three_gt_d9]
    rw [hraw]
    exact ⟨(le_div_iff₀ (by norm_num)).2 hlog_lower,
      (div_le_iff₀ (by norm_num)).2 hlog_upper⟩

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"average_collision_count","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"20.0","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.T4A5.averageCollisionCountRaw","reporting_declaration":"IChO2026Problems.T4A5.averageCollisionCount_reported_result"}
theorem averageCollisionCount_reported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      (IChO2026Problems.T4A5.averageCollisionCountRaw)
      (20 : ℝ) ((1 : ℝ) / 10) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨200, by norm_num⟩, ?_⟩
  have hbounds := averageCollisionCount_raw_result.2
  have hnonnegative : 0 ≤ averageCollisionCountRaw := by
    exact (by norm_num : (0 : ℝ) ≤ 19969 / 1000).trans hbounds.1
  rw [if_pos hnonnegative]
  exact ⟨
    (by
      calc
        (20 : ℝ) - (1 / 10) / 2 ≤ 19969 / 1000 := by norm_num
        _ ≤ averageCollisionCountRaw := hbounds.1),
    (by
      calc
        averageCollisionCountRaw ≤ 1997 / 100 := hbounds.2
        _ < (20 : ℝ) + (1 / 10) / 2 := by norm_num)⟩

end T4A5
end IChO2026Problems
