import Mathlib

/-!
# IChO 2026, theory problem 8, part 7

The source graph gives catalyst loading in percent and CO turnover frequency
in inverse hours.  By the problem's definition of TOF, the CO formation rate
per gram of support is the number of catalyst molecules per gram multiplied
by TOF.  The first factor is proportional to catalyst loading, with a fixed
positive conversion factor.  Consequently `loadingPercent * tofPerHour` is a
rate index whose ordering is the ordering of the physical rates.

The graph readings below are problem inputs.  All later declarations are
definitions or proved consequences of those inputs.
-/

namespace IChO2026Problems.T8A7

/-- The three boxes offered by question 8.7. -/
inductive Trend where
  | increases
  | decreases
  | unchanged
  deriving DecidableEq, Repr

/-- One labelled point of the graph in question 8.7. -/
structure GraphPoint where
  loadingPercent : ℚ
  tofPerHour : ℚ
  deriving DecidableEq, Repr

/-- The seven labelled graph points, in order of increasing catalyst loading.
These values are transcribed directly from Q8-3 of the problem PDF. -/
def displayedGraphPoints : List GraphPoint :=
  [⟨1 / 10, 62⟩, ⟨3 / 10, 56⟩, ⟨3 / 5, 37⟩, ⟨1, 29⟩,
   ⟨2, 15⟩, ⟨29 / 10, 11⟩, ⟨19 / 5, 8⟩]

/-- Loading times TOF.  The omitted conversion from one percent loading to
catalyst molecules per gram is fixed and positive, so it cannot change any
rate comparison. -/
def overallRateIndex (p : GraphPoint) : ℚ :=
  p.loadingPercent * p.tofPerHour

/-- Exact rate indices calculated from every labelled point in the graph. -/
def displayedRateIndices : List ℚ :=
  displayedGraphPoints.map overallRateIndex

theorem displayed_rate_indices :
    displayedRateIndices =
      [31 / 5, 84 / 5, 111 / 5, 29, 30, 319 / 10, 152 / 5] := by
  norm_num [displayedRateIndices, displayedGraphPoints, overallRateIndex]

/-- Classify the net change between two rates. -/
def classifyTrend (initialRate finalRate : ℚ) : Trend :=
  if initialRate < finalRate then .increases
  else if finalRate < initialRate then .decreases
  else .unchanged

/-- At the displayed endpoint values, the answer is box `a`, increases. -/
theorem co_rate_trend :
    classifyTrend
        (overallRateIndex ⟨1 / 10, 62⟩)
        (overallRateIndex ⟨19 / 5, 8⟩) = Trend.increases := by
  norm_num [classifyTrend, overallRateIndex]

/-- An exact rational version of the prescribed half-last-displayed-quantum
measurement convention. -/
def WithinDisplayedHalfQuantum
    (actual shown quantum : ℚ) : Prop :=
  0 < quantum ∧ |actual - shown| ≤ quantum / 2

/-- Even under half-last-digit intervals on both graph axes, every possible
rate at the highest displayed loading exceeds every possible rate at the
lowest displayed loading. -/
theorem endpoint_rate_increase_under_rounding
    (lowLoading highLoading lowTof highTof : ℚ)
    (hLowLoading : WithinDisplayedHalfQuantum lowLoading (1 / 10) (1 / 10))
    (hHighLoading : WithinDisplayedHalfQuantum highLoading (19 / 5) (1 / 10))
    (hLowTof : WithinDisplayedHalfQuantum lowTof 62 1)
    (hHighTof : WithinDisplayedHalfQuantum highTof 8 1) :
    overallRateIndex ⟨lowLoading, lowTof⟩ <
      overallRateIndex ⟨highLoading, highTof⟩ := by
  rcases abs_le.mp hLowLoading.2 with ⟨hLowLoadingLower, hLowLoadingUpper⟩
  rcases abs_le.mp hHighLoading.2 with
    ⟨hHighLoadingLower, hHighLoadingUpper⟩
  rcases abs_le.mp hLowTof.2 with ⟨hLowTofLower, hLowTofUpper⟩
  rcases abs_le.mp hHighTof.2 with ⟨hHighTofLower, hHighTofUpper⟩
  have hLowLoadingNonnegative : 0 ≤ lowLoading := by linarith
  have hLowTofNonnegative : 0 ≤ lowTof := by linarith
  have hHighTofNonnegative : 0 ≤ highTof := by linarith
  have hLowLoadingBound : lowLoading ≤ 3 / 20 := by linarith
  have hHighLoadingBound : 15 / 4 ≤ highLoading := by linarith
  have hLowTofBound : lowTof ≤ 125 / 2 := by linarith
  have hHighTofBound : 15 / 2 ≤ highTof := by linarith
  have hLowRateBound : lowLoading * lowTof ≤ (3 / 20) * (125 / 2) := by
    nlinarith
      [mul_nonneg (sub_nonneg.mpr hLowLoadingBound)
          (show (0 : ℚ) ≤ 125 / 2 by norm_num),
       mul_nonneg hLowLoadingNonnegative (sub_nonneg.mpr hLowTofBound)]
  have hHighRateBound : (15 / 4) * (15 / 2) ≤ highLoading * highTof := by
    nlinarith
      [mul_nonneg (sub_nonneg.mpr hHighLoadingBound) hHighTofNonnegative,
       mul_nonneg (show (0 : ℚ) ≤ 15 / 4 by norm_num)
         (sub_nonneg.mpr hHighTofBound)]
  norm_num [overallRateIndex] at hLowRateBound hHighRateBound ⊢
  linarith

/-- Applying any fixed positive conversion factor (catalyst molecules per
gram per percentage point) preserves the source-grounded rate increase. -/
theorem physical_rate_increase_under_rounding
    (moleculesPerGramPerPercent lowLoading highLoading lowTof highTof : ℚ)
    (hConversion : 0 < moleculesPerGramPerPercent)
    (hLowLoading : WithinDisplayedHalfQuantum lowLoading (1 / 10) (1 / 10))
    (hHighLoading : WithinDisplayedHalfQuantum highLoading (19 / 5) (1 / 10))
    (hLowTof : WithinDisplayedHalfQuantum lowTof 62 1)
    (hHighTof : WithinDisplayedHalfQuantum highTof 8 1) :
    moleculesPerGramPerPercent * overallRateIndex ⟨lowLoading, lowTof⟩ <
      moleculesPerGramPerPercent * overallRateIndex ⟨highLoading, highTof⟩ := by
  exact mul_lt_mul_of_pos_left
    (endpoint_rate_increase_under_rounding lowLoading highLoading lowTof highTof
      hLowLoading hHighLoading hLowTof hHighTof)
    hConversion

/-- The classification remains `increases` for all actual endpoint values
consistent with the displayed precision. -/
theorem co_rate_trend_under_display_rounding
    (lowLoading highLoading lowTof highTof : ℚ)
    (hLowLoading : WithinDisplayedHalfQuantum lowLoading (1 / 10) (1 / 10))
    (hHighLoading : WithinDisplayedHalfQuantum highLoading (19 / 5) (1 / 10))
    (hLowTof : WithinDisplayedHalfQuantum lowTof 62 1)
    (hHighTof : WithinDisplayedHalfQuantum highTof 8 1) :
    classifyTrend
        (overallRateIndex ⟨lowLoading, lowTof⟩)
        (overallRateIndex ⟨highLoading, highTof⟩) = Trend.increases := by
  have hIncrease := endpoint_rate_increase_under_rounding
    lowLoading highLoading lowTof highTof
    hLowLoading hHighLoading hLowTof hHighTof
  simp [classifyTrend, hIncrease]

#print axioms displayed_rate_indices
#print axioms co_rate_trend
#print axioms endpoint_rate_increase_under_rounding
#print axioms physical_rate_increase_under_rounding
#print axioms co_rate_trend_under_display_rounding

end IChO2026Problems.T8A7
