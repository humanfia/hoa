import IChO2026Chem.Reporting

/-!
# IChO 2026 T4-A1: isotopic abundance of uranium-235

The problem page supplies the two isotope masses.  The general periodic table
on PDF page 5 supplies the natural-uranium atomic mass `238.03`.  The trusted
weighted-average law says that, when `x` is the atomic fraction of uranium-235,

`238.03 = x * 235.04 + (1 - x) * 238.05`.

The declarations in `ProblemInputs` record only those printed numerical data.
The remaining declarations and theorems derive the requested percentage and
certify its answer-blind three-significant-figure report.
-/

namespace IChO2026Problems.T4A1

open IChO2026Chem.Reporting

noncomputable section

namespace ProblemInputs

/-- Isotopic mass of uranium-235 printed in question 4.1, in atomic mass units. -/
def uranium235Mass : ℝ := 23504 / 100

/-- Isotopic mass of uranium-238 printed in question 4.1, in atomic mass units. -/
def uranium238Mass : ℝ := 23805 / 100

/-- Natural uranium atomic mass printed in the supplied general periodic table,
in atomic mass units. -/
def naturalUraniumAtomicMass : ℝ := 23803 / 100

end ProblemInputs

open ProblemInputs

/-- The weighted-average atomic-mass law specialized to the problem data.
Here `x` is the atomic fraction (not the percentage) of uranium-235. -/
def SatisfiesAtomicMassBalance (x : ℝ) : Prop :=
  naturalUraniumAtomicMass =
    x * uranium235Mass + (1 - x) * uranium238Mass

/-- Physical range condition for an atomic fraction. -/
def IsAtomicFraction (x : ℝ) : Prop := 0 ≤ x ∧ x ≤ 1

/-- Exact uranium-235 abundance as a percentage. -/
def uranium235RawPercent : ℝ := 200 / 301

/-- Three-significant-figure displayed percentage required by `TASK.json`. -/
def uranium235ReportedPercent : ℝ := 664 / 1000

/-- The display quantum for `0.664%`; its last significant decimal place is
one thousandth of a percentage point. -/
def uranium235ReportingQuantum : ℝ := 1 / 1000

/-- The isotope mass balance has exactly one uranium-235 atomic fraction. -/
theorem uranium235_atomic_fraction_characterization (x : ℝ) :
    SatisfiesAtomicMassBalance x ↔ x = 2 / 301 := by
  constructor
  · intro h
    norm_num [SatisfiesAtomicMassBalance, naturalUraniumAtomicMass,
      uranium235Mass, uranium238Mass] at h ⊢
    linarith
  · rintro rfl
    norm_num [SatisfiesAtomicMassBalance, naturalUraniumAtomicMass,
      uranium235Mass, uranium238Mass]

/-- Expressed in percent, the unique solution of the printed mass balance is
the exact raw value `200/301 %`. -/
theorem uranium235_abundance_percent_characterization (p : ℝ) :
    SatisfiesAtomicMassBalance (p / 100) ↔ p = uranium235RawPercent := by
  constructor
  · intro h
    have hx := (uranium235_atomic_fraction_characterization (p / 100)).mp h
    norm_num [uranium235RawPercent] at hx ⊢
    linarith
  · intro hp
    apply (uranium235_atomic_fraction_characterization (p / 100)).mpr
    rw [hp]
    norm_num [uranium235RawPercent]

/-- The exact raw percentage satisfies the source-grounded isotope balance. -/
theorem uranium235_raw_percent_satisfies_balance :
    SatisfiesAtomicMassBalance (uranium235RawPercent / 100) := by
  exact (uranium235_abundance_percent_characterization uranium235RawPercent).mpr rfl

/-- The derived fraction is physically meaningful: it lies between zero and
one. -/
theorem uranium235_atomic_fraction_is_physical :
    IsAtomicFraction (uranium235RawPercent / 100) := by
  constructor <;> norm_num [IsAtomicFraction, uranium235RawPercent]

/-- The chosen displayed answer `0.664%` is the nearest thousandth of a
percentage point to the exact raw answer, with the stipulated tie rule. -/
theorem uranium235_reported_percent_correct :
    ReportsAtQuantum uranium235RawPercent uranium235ReportedPercent
      uranium235ReportingQuantum := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [uranium235ReportingQuantum]
  · refine ⟨(664 : ℤ), ?_⟩
    norm_num [uranium235ReportedPercent, uranium235ReportingQuantum]
  · have hnonneg : 0 ≤ uranium235RawPercent := by
      norm_num [uranium235RawPercent]
    rw [if_pos hnonneg]
    constructor <;>
      norm_num [uranium235RawPercent, uranium235ReportedPercent,
        uranium235ReportingQuantum]

/-- Complete raw/reported submission for the requested numerical output. -/
def uranium235Submission : NumericSubmission where
  rawValue := uranium235RawPercent
  reportedValue := uranium235ReportedPercent
  reportingQuantum := uranium235ReportingQuantum

/-- The submission keeps the exact raw result and carries a proved reporting
certificate rather than rounding during the chemistry calculation. -/
theorem uranium235_submission_valid :
    ValidNumericSubmission uranium235RawPercent uranium235Submission := by
  refine ⟨rfl, ?_⟩
  exact uranium235_reported_percent_correct

/-- Final requested output: the valid submission displays `0.664%`, while its
raw value is the unique percentage compatible with the supplied masses. -/
theorem uranium235_abundance_output :
    uranium235Submission.reportedValue = 664 / 1000 ∧
    SatisfiesAtomicMassBalance (uranium235Submission.rawValue / 100) ∧
    IsAtomicFraction (uranium235Submission.rawValue / 100) ∧
    (∀ p : ℝ, SatisfiesAtomicMassBalance (p / 100) →
      p = uranium235Submission.rawValue) ∧
    ValidNumericSubmission uranium235RawPercent uranium235Submission := by
  refine ⟨rfl, uranium235_raw_percent_satisfies_balance,
    uranium235_atomic_fraction_is_physical, ?_, uranium235_submission_valid⟩
  intro p hp
  exact (uranium235_abundance_percent_characterization p).mp hp

#print axioms uranium235_atomic_fraction_characterization
#print axioms uranium235_abundance_percent_characterization
#print axioms uranium235_raw_percent_satisfies_balance
#print axioms uranium235_atomic_fraction_is_physical
#print axioms uranium235_reported_percent_correct
#print axioms uranium235_submission_valid
#print axioms uranium235_abundance_output

end

end IChO2026Problems.T4A1
