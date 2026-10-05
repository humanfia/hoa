import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T4-A1: atomic abundance of uranium-235

The problem restricts natural uranium to two isotopes.  The two printed isotope
masses are modeled exactly, while the conventional atomic weight of natural
uranium is taken from the answer-blind, version-pinned offline chemistry table.
All masses use the same atomic-mass scale, so the weighted-average equation can
be expressed with dimensionless real scalars.
-/

namespace IChO2026Problems.T4A1

/-- The complete isotope domain stipulated by the problem. -/
inductive UraniumIsotope where
  | uranium235
  | uranium238
  deriving DecidableEq

/-- Problem-stipulated isotope masses, in atomic mass units. -/
noncomputable def isotopeAtomicMass : UraniumIsotope → ℝ
  | .uranium235 => 23504 / 100
  | .uranium238 => 23805 / 100

/--
The conventional atomic weight of natural uranium used by the contest
calculation.  Provenance: `atomic_weight U` from the pinned offline registry,
dataset `ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+
contest-interpretation-v1+trusted-empirical-rules-v1`, dataset SHA-256
`11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`,
record SHA-256
`18330650985fd5a061184983d3884beb83604e75446c7ec00dd6f33766382767`.
-/
noncomputable def naturalUraniumAtomicWeight : ℝ := 23803 / 100

/--
`TwoIsotopeWeightedAverage x` says that `x` is a physically admissible atomic
fraction of uranium-235 and that the mean atomic mass is the two-isotope
weighted average stipulated by the problem.
-/
def TwoIsotopeWeightedAverage (x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧
    naturalUraniumAtomicWeight =
      x * isotopeAtomicMass .uranium235 +
        (1 - x) * isotopeAtomicMass .uranium238

/-- Candidate uranium-235 atomic fraction obtained by solving the weighted average. -/
noncomputable def uranium235AtomicFraction : ℝ :=
  (isotopeAtomicMass .uranium238 - naturalUraniumAtomicWeight) /
    (isotopeAtomicMass .uranium238 - isotopeAtomicMass .uranium235)

/-- Requested atomic abundance of uranium-235, expressed as a percentage. -/
noncomputable def uranium235AbundancePercent : ℝ :=
  100 * uranium235AtomicFraction

/--
Problem-specific derivation specification: the derived fraction satisfies the
physical bounds and weighted-average law, and the requested carrier is its
percentage conversion.
-/
def uranium235AbundanceDerivation : Prop :=
  TwoIsotopeWeightedAverage uranium235AtomicFraction ∧
    uranium235AbundancePercent = 100 * uranium235AtomicFraction

/--
Raw answer-blind result, including a nondegenerate exact rational interval
certificate for the unrounded expression.
-/
theorem uranium235Abundance_raw :
    (IChO2026Problems.T4A1.uranium235AbundanceDerivation) ∧
      (((13289 : ℝ) / 20000) ≤
          (IChO2026Problems.T4A1.uranium235AbundancePercent) ∧
        (IChO2026Problems.T4A1.uranium235AbundancePercent) ≤
          ((33223 : ℝ) / 50000)) := by
  norm_num [uranium235AbundanceDerivation, TwoIsotopeWeightedAverage,
    uranium235AbundancePercent, uranium235AtomicFraction,
    isotopeAtomicMass, naturalUraniumAtomicWeight]

theorem uranium235Abundance_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      (IChO2026Problems.T4A1.uranium235AbundancePercent)
      ((664 : ℝ) / 1000) ((1 : ℝ) / 1000) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  constructor
  · norm_num
  constructor
  · refine ⟨(664 : ℤ), ?_⟩
    norm_num
  · have h_nonnegative :
        0 ≤ IChO2026Problems.T4A1.uranium235AbundancePercent := by
      norm_num [uranium235AbundancePercent, uranium235AtomicFraction,
        isotopeAtomicMass, naturalUraniumAtomicWeight]
    simp only [if_pos h_nonnegative]
    constructor <;>
      norm_num [uranium235AbundancePercent, uranium235AtomicFraction,
        isotopeAtomicMass, naturalUraniumAtomicWeight]

/--
Canonical reduced-rational form of the same reported value.  The deterministic
reporting guard normalizes exact decimal certificate values before generating
its kernel-level probe, while the answer-blind payload contract preserves the
decimal expression above.  This theorem explicitly binds those two equal
representations.
-/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"uranium235_abundance","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"0.664","reporting_quantum":"0.001","raw_declaration":"IChO2026Problems.T4A1.uranium235AbundancePercent","reporting_declaration":"IChO2026Problems.T4A1.uranium235Abundance_reportedCanonical"}
theorem uranium235Abundance_reportedCanonical :
    IChO2026Chem.Reporting.ReportsAtQuantum
      (IChO2026Problems.T4A1.uranium235AbundancePercent)
      ((83 : ℝ) / 125) ((1 : ℝ) / 1000) := by
  convert uranium235Abundance_reported using 1
  norm_num

end IChO2026Problems.T4A1
