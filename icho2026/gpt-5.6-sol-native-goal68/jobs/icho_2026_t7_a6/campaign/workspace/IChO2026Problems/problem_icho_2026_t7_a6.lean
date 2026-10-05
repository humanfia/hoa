import Mathlib

/-!
# IChO 2026, theory problem 7.6

The problem gives four calibration experiments and asks for a qualitative
ranking of four new reductant/additive pairs.  All printed decimal inputs are
stored below as exact scaled integers: reduction potentials are in hundredths
of a volt, `pKa10` is ten times the printed pKa, and calibration yields are ten
times the printed molar amount.

The ranking rule is deliberately named `problemTrendAbove`: it is the
empirical classifier requested by the question, not a universal law asserting
that the yield of every nitrogen-fixation catalyst is monotone in these two
numbers.  It first separates reductants stronger than the zero-yield
chromocene calibration, and then applies the pKa direction exhibited by
calibrations 3 and 4.  Since all A--D additives have triflate counterions, the
large chloride/triflate effect visible in calibrations 2 and 4 is controlled.
-/

namespace IChO2026Problems.T7A6

inductive Counterion
  | chloride
  | triflate
  deriving DecidableEq, Repr

/-- One row of the printed calibration table. -/
structure Calibration where
  reductionPotential100 : ℤ
  pKa10 : ℤ
  counterion : Counterion
  ammoniaYield10 : ℕ
  deriving DecidableEq, Repr

/-- The four calibration rows, transcribed from page Q7-3. -/
def calibration1 : Calibration := ⟨-88, 144, .triflate, 0⟩
def calibration2 : Calibration := ⟨-115, 144, .chloride, 7⟩
def calibration3 : Calibration := ⟨-115, 139, .triflate, 91⟩
def calibration4 : Calibration := ⟨-115, 144, .triflate, 118⟩

/-- The reductant comparison isolated by rows 1 and 4. -/
theorem calibration_reductant_trend :
    calibration4.reductionPotential100 < calibration1.reductionPotential100 ∧
    calibration4.pKa10 = calibration1.pKa10 ∧
    calibration4.counterion = calibration1.counterion ∧
    calibration1.ammoniaYield10 < calibration4.ammoniaYield10 := by
  norm_num [calibration1, calibration4]

/-- The additive-pKa comparison isolated by rows 3 and 4. -/
theorem calibration_pKa_trend :
    calibration3.reductionPotential100 = calibration4.reductionPotential100 ∧
    calibration3.counterion = calibration4.counterion ∧
    calibration3.pKa10 < calibration4.pKa10 ∧
    calibration3.ammoniaYield10 < calibration4.ammoniaYield10 := by
  norm_num [calibration3, calibration4]

/-- The counterion comparison isolated by rows 2 and 4. -/
theorem calibration_counterion_effect :
    calibration2.reductionPotential100 = calibration4.reductionPotential100 ∧
    calibration2.pKa10 = calibration4.pKa10 ∧
    calibration2.counterion ≠ calibration4.counterion ∧
    calibration2.ammoniaYield10 < calibration4.ammoniaYield10 := by
  simp [calibration2, calibration4]

inductive Choice
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Printed properties of one proposed Red/Ad combination. -/
structure Candidate where
  reductionPotential100 : ℤ
  pKa10 : ℤ
  counterion : Counterion
  deriving DecidableEq, Repr

/-- Exact transcription of candidates A--D from page Q7-3. -/
def candidate : Choice → Candidate
  | .A => ⟨-9, 137, .triflate⟩
  | .B => ⟨-110, 150, .triflate⟩
  | .C => ⟨-110, 137, .triflate⟩
  | .D => ⟨-110, 106, .triflate⟩

/-- The boundary supplied by calibration 1, which produced no ammonia. -/
def zeroYieldReductionBoundary : ℤ :=
  calibration1.reductionPotential100

/-- A candidate passes the problem's empirical reductant screen when its
potential is more negative than the zero-yield calibration potential. -/
def passesReductionScreen (x : Choice) : Bool :=
  decide ((candidate x).reductionPotential100 < zeroYieldReductionBoundary)

/-- The qualitative order inferred from the printed experiments.

Candidates that pass the reductant screen precede those that do not.  Within
one screen class, the larger pKa precedes the smaller pKa, following the
direction of calibration rows 3 and 4. -/
def problemTrendAbove (x y : Choice) : Bool :=
  if passesReductionScreen x = passesReductionScreen y then
    decide ((candidate y).pKa10 < (candidate x).pKa10)
  else
    passesReductionScreen x

theorem candidates_all_triflate :
    ∀ x : Choice, (candidate x).counterion = .triflate := by
  intro x
  cases x <;> rfl

theorem reduction_screen_values :
    passesReductionScreen .A = false ∧
    passesReductionScreen .B = true ∧
    passesReductionScreen .C = true ∧
    passesReductionScreen .D = true := by
  norm_num [passesReductionScreen, zeroYieldReductionBoundary,
    calibration1, candidate]

theorem vanadocene_pKa_order :
    (candidate .D).pKa10 < (candidate .C).pKa10 ∧
    (candidate .C).pKa10 < (candidate .B).pKa10 := by
  norm_num [candidate]

theorem decisive_candidate_comparisons :
    problemTrendAbove .B .C = true ∧
    problemTrendAbove .C .D = true ∧
    problemTrendAbove .D .A = true := by
  norm_num [problemTrendAbove, passesReductionScreen,
    zeroYieldReductionBoundary, calibration1, candidate]

/-- Generic insertion into a list using a Boolean "comes before" test. -/
def insertBy {α : Type} (before : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: bs =>
      if before a b then a :: b :: bs
      else b :: insertBy before a bs

/-- Generic insertion sort; the chemistry is confined to `problemTrendAbove`. -/
def insertionSort {α : Type} (before : α → α → Bool) : List α → List α
  | [] => []
  | a :: as => insertBy before a (insertionSort before as)

/-- The four labels before applying any answer-specific ordering. -/
def allChoices : List Choice := [.A, .B, .C, .D]

/-- The ranking computed from source data and `problemTrendAbove`. -/
def computedRanking : List Choice :=
  insertionSort problemTrendAbove allChoices

/-- Requested output: decreasing predicted ammonia yield is B, C, D, A. -/
theorem ammonia_yield_decreasing_order :
    computedRanking = [.B, .C, .D, .A] := by
  decide

/-- The computed answer contains every candidate exactly once. -/
theorem ammonia_yield_ranking_is_complete :
    computedRanking.Perm allChoices := by
  decide

/-- Every earlier entry of the output ranks above every later entry, not only
each adjacent pair. -/
theorem ammonia_yield_ranking_is_strict :
    computedRanking.Pairwise (fun x y => problemTrendAbove x y = true) := by
  decide

/-- A numerical yield assignment is compatible with the qualitative model
when every model comparison is realized as a strict yield inequality. -/
def TrendCompatibleYield (yield : Choice → ℝ) : Prop :=
  ∀ x y, problemTrendAbove x y = true → yield y < yield x

/-- Semantic bridge to actual numerical yields.  The problem does not print
the four candidate yields, so compatibility is displayed as a hypothesis
rather than introduced as an unchecked axiom. -/
theorem numerical_ammonia_yields_follow_ranking
    (yield : Choice → ℝ) (h : TrendCompatibleYield yield) :
    yield .C < yield .B ∧ yield .D < yield .C ∧ yield .A < yield .D := by
  exact ⟨h .B .C decisive_candidate_comparisons.1,
    h .C .D decisive_candidate_comparisons.2.1,
    h .D .A decisive_candidate_comparisons.2.2⟩

#print axioms calibration_reductant_trend
#print axioms calibration_pKa_trend
#print axioms calibration_counterion_effect
#print axioms ammonia_yield_decreasing_order
#print axioms ammonia_yield_ranking_is_complete
#print axioms ammonia_yield_ranking_is_strict
#print axioms numerical_ammonia_yields_follow_ranking

end IChO2026Problems.T7A6
