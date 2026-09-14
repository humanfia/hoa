import IChO2026Chem

/-!
# IChO 2026, Problem T4, part A1 (Q4-1, item 4.1): atomic abundance of ²³⁵U

Official problem statement (theory_problem.pdf, source page 37; page image
`T4_page-1.png`):

> 4.1  **Calculate** the atomic abundance of ²³⁵U in natural uranium, assuming
> it consists only of isotopes ²³⁵U (235.04 a.u.) and ²³⁸U (238.05 a.u.).

Inputs taken from the problem-only source materials:

* Isotopic masses (problem text): m(²³⁵U) = 235.04 a.u., m(²³⁸U) = 238.05 a.u.
  These are stipulated constants of the problem, exact as printed.
* Average atomic weight of natural uranium: A(U) = 238.03, printed under the
  symbol `U` in the official "Periodic Table of Elements" distributed with the
  same booklet (theory_problem.pdf, page header G1-5).

The model used (two-component isotopic mixture, average atomic mass equal to the
abundance-weighted sum of the isotopic masses) is the standard content of the
task itself.

Solution: with x = atomic (mole) fraction of ²³⁵U,

    235.04 · x + 238.05 · (1 − x) = 238.03
    x = (238.05 − 238.03) / (238.05 − 235.04) = 0.02 / 3.01 = 2/301.

Hence the atomic abundance is 100·x % = 200/301 % ≈ 0.6644518… %.

Reported with three significant figures (the project-wide answer-blind default
recorded for this target; the problem does not specify a reporting precision):

    abundance of ²³⁵U ≈ 0.664 %.

The raw value 200/301 = 0.664451… is strictly inside the half-quantum interval
(0.6635, 0.6645) of the reported value 0.664 at quantum 0.001, so no tie rule
is ever invoked.

All arithmetic below is verified by `norm_num`; no `sorry`, no custom axioms.
-/

namespace IChO2026Problems.T4A1

open IChO2026Chem.Reporting

/-! ## Problem inputs -/

/-- Isotopic mass of ²³⁵U in atomic mass units, as printed in the problem. -/
def m235 : ℝ := 235.04

/-- Isotopic mass of ²³⁸U in atomic mass units, as printed in the problem. -/
def m238 : ℝ := 238.05

/-- Standard (average) atomic weight of natural uranium, as printed in the
    official IChO 2026 periodic table accompanying the examination. -/
def mAvg : ℝ := 238.03

/-! ## Model -/

/-- `abundance x` asserts that `x` is the atomic (mole) fraction of ²³⁵U in a
    two-component mixture of ²³⁵U and ²³⁸U whose average atomic weight equals
    the tabulated value `mAvg`: the mean isotopic mass is the
    abundance-weighted sum  m235·x + m238·(1−x). -/
def abundance (x : ℝ) : Prop := m235 * x + m238 * (1 - x) = mAvg

/-! ## Solution

   m235·x + m238·(1−x) = mAvg
   ⟺ (m238 − m235)·x = m238 − mAvg              (collecting terms in x)
   ⟺ 3.01·x = 0.02                              (substituting the inputs)
   ⟺ x = 0.02/3.01 = 2/301.                     -/

/-- The abundance is uniquely determined: any atomic fraction consistent with
    the tabulated average mass equals 2/301. -/
theorem abundance_unique (x : ℝ) (hx : abundance x) : x = 2 / 301 := by
  have h : (301 : ℝ) * x = 2 := by
    have := hx
    unfold abundance m235 m238 mAvg at this
    norm_num at this ⊢
    linarith
  have h301 : (301 : ℝ) ≠ 0 := by norm_num
  field_simp
  linarith

/-- The fraction 2/301 indeed satisfies the model (existence). -/
theorem abundance_iff (x : ℝ) : abundance x ↔ x = 2 / 301 := by
  constructor
  · exact abundance_unique x
  · intro hx
    rw [hx]
    unfold abundance m235 m238 mAvg
    norm_num

/-- The exact atomic abundance of ²³⁵U as a percentage: 200/301 %. -/
noncomputable def exactAbundancePercent : ℝ := 200 / 301

theorem abundance_percent (x : ℝ) (hx : abundance x) :
    100 * x = exactAbundancePercent := by
  rw [abundance_unique x hx]
  unfold exactAbundancePercent
  norm_num

/-! ## Reporting (three significant figures, quantum 0.001 %) -/

/-- The final reported value at three significant figures. -/
def reportedAbundancePercent : ℝ := 0.664

/-- Reporting quantum: last displayed digit is the 0.001 % place. -/
def reportingQuantum : ℝ := 0.001

/-- The official submission: raw exact value 200/301 %, reported 0.664 % at
    quantum 0.001 %. -/
noncomputable def submission : NumericSubmission where
  rawValue := exactAbundancePercent
  reportedValue := reportedAbundancePercent
  reportingQuantum := reportingQuantum

/-- 0.664 is a multiple of the quantum: 0.664 = 664 · 0.001. -/
theorem reported_is_multiple :
    ∃ k : ℤ, reportedAbundancePercent = reportingQuantum * k := by
  refine ⟨664, ?_⟩
  unfold reportedAbundancePercent reportingQuantum
  norm_num

/-- The raw value lies in the half-quantum reporting interval of 0.664 with the
    tie rule "half away from zero": 0.6635 ≤ 200/301 < 0.6645.  The strictness
    on the right shows no tie ever occurs, so the tie rule is only a
    specification detail. -/
theorem raw_in_reporting_interval :
    reportedAbundancePercent - reportingQuantum / 2 ≤ exactAbundancePercent ∧
    exactAbundancePercent < reportedAbundancePercent + reportingQuantum / 2 := by
  constructor
  · -- (664 - 1/2)/1000 ≤ 200/301  ⟺  1327·301 ≤ 200·2000  ⟺  399427 ≤ 400000
    unfold reportedAbundancePercent reportingQuantum exactAbundancePercent
    norm_num
  · -- 200/301 < (664 + 1/2)/1000  ⟺  200·2000 < 1329·301  ⟺  400000 < 400029
    unfold reportedAbundancePercent reportingQuantum exactAbundancePercent
    norm_num

/-- Main theorem: the reported answer 0.664 % is the correct three-significant
    figure reporting (at quantum 0.001 %, ties away from zero) of the unique
    atomic abundance 200/301 % of ²³⁵U determined by the problem inputs. -/
theorem uranium235_abundance_reports_three_sig_figs :
    ReportsAtQuantum exactAbundancePercent
      reportedAbundancePercent reportingQuantum := by
  refine ⟨by norm_num [reportingQuantum], reported_is_multiple, ?_⟩
  have hpos : 0 ≤ exactAbundancePercent := by
    unfold exactAbundancePercent; positivity
  rw [if_pos hpos]
  exact raw_in_reporting_interval

/-- The packaged submission is valid for the raw expression 200/301 %. -/
theorem submission_valid :
    ValidNumericSubmission exactAbundancePercent submission :=
  ⟨rfl, uranium235_abundance_reports_three_sig_figs⟩

/-- Consistency of the tabulated uranium weight with the two-isotope model:
    at abundance 2/301 the weighted mean reproduces 238.03. -/
theorem tabulated_weight_consistent :
    m235 * (2 / 301) + m238 * (1 - 2 / 301) = mAvg := by
  unfold m235 m238 mAvg
  norm_num

#print axioms uranium235_abundance_reports_three_sig_figs
#print axioms submission_valid
#print axioms abundance_unique
#print axioms abundance_percent

end IChO2026Problems.T4A1
