import IChO2026Chem.Reporting

/-!
# IChO 2026, theory problem 2, subquestion 2.2

This file formalizes the steady-state calculation for `HBrO₂` in Processes A
and B.  The rate laws are mass-action laws for the elementary reactions printed
in the problem.  All printed numerical data are represented by exact rational
real numbers; rounding is used only for the final submissions.
-/

namespace IChO2026Problems.T2A2

open IChO2026Chem.Reporting

noncomputable section

/-! ## Problem data -/

/-- The printed rate constant `k₁ = 1.0 × 10⁴ M⁻² s⁻¹`. -/
def k1 : ℝ := 1 * 10 ^ 4

/-- The printed rate constant `k₂ = 6.2 × 10⁴ M⁻² s⁻¹`. -/
def k2 : ℝ := (62 / 10) * 10 ^ 4

/-- The printed rate constant `k₃ = 4.0 × 10⁷ M⁻¹ s⁻¹`. -/
def k3 : ℝ := 4 * 10 ^ 7

/-- The printed rate constant `k₄ = 2.0 × 10⁹ M⁻² s⁻¹`. -/
def k4 : ℝ := 2 * 10 ^ 9

/-- The printed rate constant `k₅ = 2.1 M⁻³ s⁻¹`. -/
def k5 : ℝ := 21 / 10

/-- The maintained bromate concentration `[BrO₃⁻] = 0.06 M`. -/
def bromate : ℝ := 6 / 100

/-- The maintained proton concentration `[H⁺] = 0.8 M`. -/
def proton : ℝ := 8 / 10

/-! ## Mass-action rates and steady-state balances -/

/-- Rate of Process-A elementary step (1). -/
def rateA1 (hbro2 : ℝ) : ℝ := k1 * hbro2 * bromate * proton

/-- Rate of Process-A elementary step (2). -/
def rateA2 (bro2Radical ce3 : ℝ) : ℝ := k2 * bro2Radical * ce3 * proton

/-- Rate of Process-A elementary step (3). -/
def rateA3 (hbro2 : ℝ) : ℝ := k3 * hbro2 ^ 2

/-- The two Process-A steady-state equations.  Step (1) creates two `BrO₂·`,
step (2) consumes one, while steps (1), (2), and (3) change `HBrO₂` by
`-1`, `+1`, and `-2`, respectively. -/
def ProcessASteadyState (hbro2 bro2Radical ce3 : ℝ) : Prop :=
  2 * rateA1 hbro2 - rateA2 bro2Radical ce3 = 0 ∧
  -rateA1 hbro2 + rateA2 bro2Radical ce3 - 2 * rateA3 hbro2 = 0

/-- Rate of Process-B elementary step (4). -/
def rateB4 (hbro2 bromide : ℝ) : ℝ := k4 * hbro2 * bromide * proton

/-- Rate of Process-B elementary step (5). -/
def rateB5 (bromide : ℝ) : ℝ := k5 * bromate * bromide * proton ^ 2

/-- The Process-B steady-state equation for `HBrO₂`: step (4) consumes one
molecule and step (5) produces one molecule. -/
def ProcessBSteadyState (hbro2 bromide : ℝ) : Prop :=
  -rateB4 hbro2 bromide + rateB5 bromide = 0

/-! ## Symbolic elimination of the intermediates -/

/-- The two Process-A steady-state equations eliminate the unknown rate of
step (2), leaving `r₁ = 2 r₃`. -/
theorem processA_rate_relation {hbro2 bro2Radical ce3 : ℝ}
    (hss : ProcessASteadyState hbro2 bro2Radical ce3) :
    rateA1 hbro2 = 2 * rateA3 hbro2 := by
  unfold ProcessASteadyState at hss
  linarith

/-- On the active (positive-concentration) Process-A branch, the stationary
concentration is uniquely `6 × 10⁻⁶ M`.  Positivity selects the chemically
active branch from the additional algebraic root `hbro2 = 0`. -/
theorem hbro2_process_a_stationary
    {hbro2 bro2Radical ce3 : ℝ}
    (hactive : 0 < hbro2)
    (hss : ProcessASteadyState hbro2 bro2Radical ce3) :
    hbro2 = 6 / 1000000 := by
  have hrel := processA_rate_relation hss
  unfold rateA1 rateA3 k1 k3 bromate proton at hrel
  norm_num at hrel ⊢
  nlinarith

/-- With bromide present, the Process-B steady-state equation uniquely fixes
the stationary concentration at `5.04 × 10⁻¹¹ M`. -/
theorem hbro2_process_b_stationary
    {hbro2 bromide : ℝ}
    (hbromide : 0 < bromide)
    (hss : ProcessBSteadyState hbro2 bromide) :
    hbro2 = 504 / 10000000000000 := by
  unfold ProcessBSteadyState rateB4 rateB5 k4 k5 bromate proton at hss
  norm_num at hss ⊢
  nlinarith

/-! ## Exact raw values and required three-significant-figure displays -/

def hbro2ProcessARaw : ℝ := 6 / 1000000

def hbro2ProcessBRaw : ℝ := 504 / 10000000000000

/-- `6.00 × 10⁻⁶ M`, whose last displayed-place quantum is `10⁻⁸ M`. -/
def hbro2ProcessASubmission : NumericSubmission where
  rawValue := hbro2ProcessARaw
  reportedValue := hbro2ProcessARaw
  reportingQuantum := 1 / 100000000

/-- `5.04 × 10⁻¹¹ M`, whose last displayed-place quantum is `10⁻¹³ M`. -/
def hbro2ProcessBSubmission : NumericSubmission where
  rawValue := hbro2ProcessBRaw
  reportedValue := hbro2ProcessBRaw
  reportingQuantum := 1 / 10000000000000

theorem hbro2_process_a_submission_valid :
    ValidNumericSubmission hbro2ProcessARaw hbro2ProcessASubmission := by
  constructor
  · rfl
  unfold ReportsAtQuantum hbro2ProcessASubmission hbro2ProcessARaw
  constructor
  · norm_num
  constructor
  · refine ⟨600, ?_⟩
    norm_num
  · norm_num

theorem hbro2_process_b_submission_valid :
    ValidNumericSubmission hbro2ProcessBRaw hbro2ProcessBSubmission := by
  constructor
  · rfl
  unfold ReportsAtQuantum hbro2ProcessBSubmission hbro2ProcessBRaw
  constructor
  · norm_num
  constructor
  · refine ⟨504, ?_⟩
    norm_num
  · norm_num

/-- Combined formal answer to both requested outputs. -/
theorem icho_2026_t2_a2
    {hbro2A bro2Radical ce3 hbro2B bromide : ℝ}
    (hAactive : 0 < hbro2A)
    (hAss : ProcessASteadyState hbro2A bro2Radical ce3)
    (hBactive : 0 < bromide)
    (hBss : ProcessBSteadyState hbro2B bromide) :
    hbro2A = hbro2ProcessARaw ∧ hbro2B = hbro2ProcessBRaw := by
  constructor
  · simpa [hbro2ProcessARaw] using hbro2_process_a_stationary hAactive hAss
  · simpa [hbro2ProcessBRaw] using hbro2_process_b_stationary hBactive hBss

#print axioms processA_rate_relation
#print axioms hbro2_process_a_stationary
#print axioms hbro2_process_b_stationary
#print axioms hbro2_process_a_submission_valid
#print axioms hbro2_process_b_submission_valid
#print axioms icho_2026_t2_a2

end
end IChO2026Problems.T2A2
