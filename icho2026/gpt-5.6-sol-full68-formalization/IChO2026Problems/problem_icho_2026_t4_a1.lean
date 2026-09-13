import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026 T4-A1: atomic abundance of uranium-235

The problem closes the natural-uranium isotope domain to uranium-235 and
uranium-238.  If `x` is the atom fraction of uranium-235, the complementary
atom fraction of uranium-238 is `1 - x`, and the conventional mean atomic mass
is their atom-fraction-weighted mean.

The two isotope masses below are exact problem-stipulated decimal values in
unified atomic mass units.  The conventional natural-uranium mean atomic mass
comes from the task-authorized, version-pinned offline `atomic_weight U`
lookup:

* dataset version:
  `ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1`;
* dataset SHA-256:
  `11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`;
* record SHA-256:
  `18330650985fd5a061184983d3884beb83604e75446c7ec00dd6f33766382767`.

The registry uncertainty is metadata rather than a source measurement, so the
nominal conventional value is used exactly, as required by the source policy.
-/

namespace IChO2026Problems.ProblemIChO2026T4A1

/-- The complete isotope domain stipulated for this subquestion. -/
inductive UraniumIsotope where
  | uranium235
  | uranium238
  deriving DecidableEq, Repr

/-- Problem-stipulated isotope masses, numerically expressed in unified atomic
mass units. -/
def isotopeAtomicMass : UraniumIsotope → ℝ
  | .uranium235 => 235.04
  | .uranium238 => 238.05

/-- Conventional atomic weight of natural uranium from the pinned offline
registry lookup described in the module documentation. -/
def naturalUraniumMeanAtomicMass : ℝ := 238.03

/-- The source assumptions for a candidate uranium-235 atom fraction `x`.

The bounds make `x` an atom fraction.  Because the problem permits only the two
named isotopes, uranium-238 has fraction `1 - x`; the last conjunct is the
governing atom-fraction-weighted mean-mass equation. -/
def NaturalUraniumTwoIsotopeModel (x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧
    naturalUraniumMeanAtomicMass =
      x * isotopeAtomicMass .uranium235 +
        (1 - x) * isotopeAtomicMass .uranium238

/-- Exact uranium-235 atom fraction obtained by isolating `x` in the weighted
mean-mass equation.  No intermediate rounding is present. -/
noncomputable def uranium235AtomicFractionRaw : ℝ :=
  (isotopeAtomicMass .uranium238 - naturalUraniumMeanAtomicMass) /
    (isotopeAtomicMass .uranium238 - isotopeAtomicMass .uranium235)

/-- Exact requested uranium-235 atomic abundance, expressed in percent. -/
noncomputable def uranium235AbundanceRaw : ℝ :=
  100 * uranium235AtomicFractionRaw

/-- The weighted-average equation has only the source-derived raw atom
fraction as a solution. -/
theorem uranium235AtomicFraction_unique
    {x : ℝ} (h : NaturalUraniumTwoIsotopeModel x) :
    x = uranium235AtomicFractionRaw := by
  rcases h with ⟨_hx_nonnegative, _hx_at_most_one, h_weighted_mean⟩
  dsimp [naturalUraniumMeanAtomicMass, isotopeAtomicMass,
    uranium235AtomicFractionRaw] at h_weighted_mean ⊢
  norm_num at h_weighted_mean ⊢
  linarith

/-- Problem-specific raw derivation specification: the exact percentage gives
a valid two-isotope composition, and every percentage satisfying the same
source model equals it. -/
def uranium235AbundanceDerivationSpec : Prop :=
  NaturalUraniumTwoIsotopeModel (uranium235AbundanceRaw / 100) ∧
    ∀ p : ℝ,
      NaturalUraniumTwoIsotopeModel (p / 100) →
        p = uranium235AbundanceRaw

theorem uranium235AbundanceDerivationSpec_holds :
    uranium235AbundanceDerivationSpec := by
  constructor
  · norm_num [NaturalUraniumTwoIsotopeModel, uranium235AbundanceRaw,
      uranium235AtomicFractionRaw, naturalUraniumMeanAtomicMass,
      isotopeAtomicMass]
  · intro p hp
    have hp_fraction := uranium235AtomicFraction_unique hp
    dsimp [uranium235AbundanceRaw]
    linarith

/-- Raw answer-blind result contract.  Its interval is a non-degenerate exact
rational enclosure derived independently from the unrounded expression. -/
theorem uranium235AbundanceRawResult :
    (uranium235AbundanceDerivationSpec) ∧
      (((1661 : ℝ) / 2500) ≤ uranium235AbundanceRaw ∧
        uranium235AbundanceRaw ≤ ((1329 : ℝ) / 2000)) := by
  constructor
  · exact uranium235AbundanceDerivationSpec_holds
  · norm_num [uranium235AbundanceRaw, uranium235AtomicFractionRaw,
      naturalUraniumMeanAtomicMass, isotopeAtomicMass]

/-- Final answer-blind reporting contract.  At the magnitude of this result,
three significant figures correspond to the fixed quantum `0.001 %`. -/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"uranium235_abundance","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"0.664","reporting_quantum":"0.001","raw_declaration":"IChO2026Problems.ProblemIChO2026T4A1.uranium235AbundanceRaw","reporting_declaration":"IChO2026Problems.ProblemIChO2026T4A1.uranium235AbundanceReportingCertificate"}
theorem uranium235AbundanceReportedResult :
    IChO2026Chem.Reporting.ReportsAtQuantum
      uranium235AbundanceRaw ((664 : ℝ) / 1000) ((1 : ℝ) / 1000) := by
  rw [IChO2026Chem.Reporting.ReportsAtQuantum]
  refine ⟨by norm_num, ?_, ?_⟩
  · exact ⟨664, by norm_num⟩
  · rw [if_pos]
    · constructor <;>
        norm_num [uranium235AbundanceRaw, uranium235AtomicFractionRaw,
          naturalUraniumMeanAtomicMass, isotopeAtomicMass]
    · norm_num [uranium235AbundanceRaw, uranium235AtomicFractionRaw,
        naturalUraniumMeanAtomicMass, isotopeAtomicMass]

/-- Syntactic normalization bridge for the deterministic reporting guard,
which reduces the displayed decimal `0.664` to `83 / 125`. -/
theorem uranium235AbundanceReportingCertificate :
    IChO2026Chem.Reporting.ReportsAtQuantum
      uranium235AbundanceRaw ((83 : ℝ) / 125) ((1 : ℝ) / 1000) := by
  have h : ((83 : ℝ) / 125) = (664 : ℝ) / 1000 := by norm_num
  rw [h]
  exact uranium235AbundanceReportedResult

end IChO2026Problems.ProblemIChO2026T4A1
