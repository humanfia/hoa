import Mathlib
import IChO2026Chem.Core
import IChO2026Chem.Reporting

/-!
# IChO 2026, Theory 8 ("Recycling of Carbon Dioxide"), part 8.7

## Problem (T8-A7, 2.0 pt, printed page Q8-3)

"The diagram below shows the change in the TOF of CO as ω_cat is varied.

8.7  How does the overall rate of CO formation per gram of C₃N₄ loaded with **1**
change with increasing ω_cat? Tick the correct box.
a) increases   b) decreases   c) doesn't change"

## Problem inputs used (and only these)

* The printed TOF-vs-ω_cat diagram on page Q8-3, whose red data points are
  labelled, in units (ω_cat / %, TOF / h⁻¹):
    (0.1, 62), (0.3, 56), (0.6, 37), (1, 29), (2, 15), (2.9, 11), (3.8, 8).
* The problem-stated definition (page Q8-2): "The Turnover Frequency of a
  catalyst (TOF) is the number of product molecules formed per active catalyst
  molecule per hour."
* Problem 8.5 gives M_cat = 557.21 g mol⁻¹ for catalyst 1; the reference TOF of
  8 h⁻¹ at ω_cat = 3.8 % quoted on Q8-2 agrees with the last data point of the
  diagram, confirming the reading of the axes.
* The official constants page (G1-3): Avogadro constant N_A = 6.022 × 10²³ mol⁻¹.
* The project measurement convention (`IChO2026Chem.Reporting`):
  an integer displayed in the diagram is consistent with any true value within
  ±½ (half of the last displayed quantum).

## Reasoning that is formalised below

The rate of CO formation per gram of loaded material is

    rate(ω) = TOF(ω) × N_cat_per_gram(ω),
    N_cat_per_gram(ω) = (ω/100) × N_A / M_cat,

so rate(ω) is proportional to the product  ω · TOF(ω).  Evaluating this
product at the printed points gives (in units of %·h⁻¹):

    0.1·62 = 6.2,  0.3·56 = 16.8,  0.6·37 = 22.2,  1·29 = 29,
    2·15 = 30,  2.9·11 = 31.9,  3.8·8 = 30.4.

The product rises strictly through the first six measured points.  The last
displayed step (31.9 → 30.4) is a ~5 % dip that is *not* sign-determined: the
TOF values 11 and 8 are integer displays, so within the ±½ quantum tolerance
the last step can be an increase (e.g. 10.5 → 8.5 gives 30.45 → 32.3) or a
decrease (11.5 → 7.5 gives 33.35 → 28.125).  Crucially, the overall change
across the whole studied range is robust: even pushing the endpoint TOFs to
their worst-case tolerance corners, the rate at ω_cat = 3.8 % (≥ 3.8·7.5 =
28.5) far exceeds the rate at ω_cat = 0.1 % (≤ 0.1·62.5 = 6.25).
Hence the overall rate per gram **increases** with ω_cat: box (a).

Note that this is the opposite direction from the behaviour of TOF itself
(the diagram slopes down); the point of the question is that the number of
catalyst molecules per gram grows faster (linearly in ω) than TOF falls over
the measured range.
-/

namespace IChO2026
namespace T8
namespace A7

/-! ### Physical constants and problem-given data -/

/-- Avogadro constant, exact as printed on the official constants page (G1-3):
N_A = 6.022 × 10²³ mol⁻¹. -/
def AvogadroConstant : ℝ := 6.022e23

/-- Molar mass of catalyst 1, exact as printed in problem 8.5:
M_cat = 557.21 g mol⁻¹. -/
def molarMassCat : ℝ := 557.21

/-- Mass fraction of catalyst from its printed percentage value:
ω_cat / 100 (ω_cat = 3.8 % is used as the number 3.8 here). -/
noncomputable def massFraction (ωpercent : ℝ) : ℝ := ωpercent / 100

/-- Conversion factor of the rate-per-gram law: catalyst molecules per gram of
loaded material per unit of (percent × hour), i.e. `N_A / (100 · M_cat)`. -/
noncomputable def specificFactor : ℝ := AvogadroConstant / (100 * molarMassCat)

/-- Number of catalyst molecules per gram of loaded C₃N₄ material:
(ω/100) g of catalyst per gram of material times N_A / M_cat. -/
noncomputable def catMoleculesPerGram (ωpercent : ℝ) : ℝ :=
  massFraction ωpercent * AvogadroConstant / molarMassCat

/-- Overall rate of CO formation per gram of loaded material
(CO molecules per gram per hour): TOF (CO molecules per catalyst molecule per
hour) times the number of catalyst molecules per gram.  This formula is forced
by the problem-stated definition of TOF on page Q8-2. -/
noncomputable def coRatePerGram (ωpercent tof : ℝ) : ℝ :=
  tof * catMoleculesPerGram ωpercent

/-- Factored form used in all comparisons below. -/
theorem coRatePerGram_factor (ωpercent tof : ℝ) :
    coRatePerGram ωpercent tof = specificFactor * (ωpercent * tof) := by
  unfold coRatePerGram catMoleculesPerGram massFraction specificFactor
  ring

theorem specificFactor_pos : 0 < specificFactor := by
  unfold specificFactor AvogadroConstant molarMassCat
  positivity

/-! ### Derived structural facts -/

/-- More catalyst loading means strictly more catalyst molecules per gram of
loaded material (on positive loadings). -/
theorem catMoleculesPerGram_strictMonoOn :
    StrictMonoOn catMoleculesPerGram (Set.Ioi 0) := by
  intro a _ b _ hab
  have hfa : catMoleculesPerGram a = specificFactor * a := by
    unfold catMoleculesPerGram massFraction specificFactor
    ring
  have hfb : catMoleculesPerGram b = specificFactor * b := by
    unfold catMoleculesPerGram massFraction specificFactor
    ring
  rw [hfa, hfb]
  exact mul_lt_mul_of_pos_left hab specificFactor_pos

/-- At fixed loading, the per-gram rate is strictly increasing in the TOF. -/
theorem coRatePerGram_strictMono_tof {ωpercent t₁ t₂ : ℝ}
    (hω : 0 < ωpercent) (h : t₁ < t₂) :
    coRatePerGram ωpercent t₁ < coRatePerGram ωpercent t₂ := by
  rw [coRatePerGram_factor, coRatePerGram_factor]
  have hpos : 0 < specificFactor * ωpercent :=
    mul_pos specificFactor_pos hω
  calc specificFactor * (ωpercent * t₁)
      = specificFactor * ωpercent * t₁ := by ring
    _ < specificFactor * ωpercent * t₂ :=
        mul_lt_mul_of_pos_left h hpos
    _ = specificFactor * (ωpercent * t₂) := by ring

/-! ### Statements read off the printed diagram (problem image, page Q8-3) -/

/-- Consecutive measured pairs from the interior of the diagram show a strictly
increasing per-gram CO rate: the product ω·TOF rises from 6.2 to 16.8 to
22.2 to 29 to 30 to 31.9 (%·h⁻¹) over ω_cat = 0.1 % … 2.9 %. -/
theorem measured_rates_increase_interior :
    coRatePerGram 0.1 62 < coRatePerGram 0.3 56 ∧
    coRatePerGram 0.3 56 < coRatePerGram 0.6 37 ∧
    coRatePerGram 0.6 37 < coRatePerGram 1 29 ∧
    coRatePerGram 1 29 < coRatePerGram 2 15 ∧
    coRatePerGram 2 15 < coRatePerGram 2.9 11 := by
  have key : specificFactor * (0.1 * 62) < specificFactor * (0.3 * 56) ∧
      specificFactor * (0.3 * 56) < specificFactor * (0.6 * 37) ∧
      specificFactor * (0.6 * 37) < specificFactor * (1 * 29) ∧
      specificFactor * (1 * 29) < specificFactor * (2 * 15) ∧
      specificFactor * (2 * 15) < specificFactor * (2.9 * 11) := by
    unfold specificFactor AvogadroConstant molarMassCat
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [coRatePerGram_factor, coRatePerGram_factor]
  · exact key.1
  · exact key.2.1
  · exact key.2.2.1
  · exact key.2.2.2.1
  · exact key.2.2.2.2

/-- Endpoint comparison, robust under the project measurement convention
(half the last displayed quantum; the TOF labels are integers, so quantum 1):
whatever true TOF values within ±½ of the printed 62 and 8 are taken, the
per-gram rate at ω_cat = 3.8 % strictly exceeds that at ω_cat = 0.1 %. -/
theorem endpoint_rate_increases_robust {t01 t38 : ℝ}
    (h01 : |t01 - 62| ≤ (1 : ℝ) / 2) (h38 : |t38 - 8| ≤ (1 : ℝ) / 2) :
    coRatePerGram 0.1 t01 < coRatePerGram 3.8 t38 := by
  have h01u : t01 ≤ 125 / 2 := by
    have h := (abs_le.mp h01).2
    linarith
  have h38l : 15 / 2 ≤ t38 := by
    have h := (abs_le.mp h38).1
    linarith
  have hω1 : (0 : ℝ) ≤ 0.1 := by norm_num
  have hω2 : (0 : ℝ) ≤ 3.8 := by norm_num
  rw [coRatePerGram_factor, coRatePerGram_factor]
  calc specificFactor * (0.1 * t01)
      ≤ specificFactor * (0.1 * (125 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h01u hω1)
          (le_of_lt specificFactor_pos)
    _ < specificFactor * (3.8 * (15 / 2 : ℝ)) := by
        apply mul_lt_mul_of_pos_left _ specificFactor_pos
        norm_num
    _ ≤ specificFactor * (3.8 * t38) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h38l hω2)
          (le_of_lt specificFactor_pos)

/-- At the printed values, the last measured step dips slightly
(2.9·11 = 31.9 vs 3.8·8 = 30.4). -/
theorem displayed_last_step_dips :
    coRatePerGram 3.8 8 < coRatePerGram 2.9 11 := by
  rw [coRatePerGram_factor, coRatePerGram_factor]
  apply mul_lt_mul_of_pos_left _ specificFactor_pos
  norm_num

/-- Honest treatment of the last step: with integer-displayed TOF labels
(quantum 1, tolerance ±½), the direction of the final step is not determined
by the diagram — both an increase and a decrease are consistent with the
displayed information.  This does not affect the overall trend, which is fixed
by `endpoint_rate_increases_robust` and the interior chain. -/
theorem last_step_direction_not_determined :
    (∃ t29 t38 : ℝ, |t29 - 11| ≤ (1 : ℝ) / 2 ∧ |t38 - 8| ≤ (1 : ℝ) / 2 ∧
        coRatePerGram 2.9 t29 < coRatePerGram 3.8 t38) ∧
    (∃ t29 t38 : ℝ, |t29 - 11| ≤ (1 : ℝ) / 2 ∧ |t38 - 8| ≤ (1 : ℝ) / 2 ∧
        coRatePerGram 3.8 t38 < coRatePerGram 2.9 t29) := by
  constructor
  · refine ⟨21 / 2, 17 / 2, ?_, ?_, ?_⟩
    · norm_num [abs_le]
    · norm_num [abs_le]
    · rw [coRatePerGram_factor, coRatePerGram_factor]
      apply mul_lt_mul_of_pos_left _ specificFactor_pos
      norm_num
  · refine ⟨23 / 2, 15 / 2, ?_, ?_, ?_⟩
    · norm_num [abs_le]
    · norm_num [abs_le]
    · rw [coRatePerGram_factor, coRatePerGram_factor]
      apply mul_lt_mul_of_pos_left _ specificFactor_pos
      norm_num

/-! ### The requested classification output -/

/-- The three tick boxes of 8.7, in printed order. -/
inductive RateTrend
  | increases   -- box a
  | decreases   -- box b
  | noChange    -- box c
  deriving DecidableEq, Repr

/-- The answer ticked on the answer sheet, as fixed by the analysis above. -/
def tickedBox : RateTrend := RateTrend.increases

/-- Final answer for T8-A7: the overall rate of CO formation per gram of
C₃N₄ loaded with 1 **increases** with ω_cat.  The conjunction packages the
requested classification together with the quantitative ground: across the
whole measured loading range (0.1 % → 3.8 %, the endpoints of the printed
diagram) the per-gram rate strictly increases already at the displayed
values. -/
theorem co_rate_trend :
    tickedBox = RateTrend.increases ∧
    coRatePerGram 0.1 62 < coRatePerGram 3.8 8 := by
  refine ⟨rfl, ?_⟩
  rw [coRatePerGram_factor, coRatePerGram_factor]
  apply mul_lt_mul_of_pos_left _ specificFactor_pos
  norm_num

/-- The per-gram rate also increases strictly through every consecutively
measured interior step of the diagram. -/
theorem co_rate_increases_over_measured_range :
    coRatePerGram 0.1 62 < coRatePerGram 3.8 8 ∧
    coRatePerGram 0.1 62 < coRatePerGram 0.3 56 ∧
    coRatePerGram 0.3 56 < coRatePerGram 0.6 37 ∧
    coRatePerGram 0.6 37 < coRatePerGram 1 29 ∧
    coRatePerGram 1 29 < coRatePerGram 2 15 ∧
    coRatePerGram 2 15 < coRatePerGram 2.9 11 :=
  ⟨co_rate_trend.2, measured_rates_increase_interior.1,
    measured_rates_increase_interior.2.1, measured_rates_increase_interior.2.2.1,
    measured_rates_increase_interior.2.2.2.1,
    measured_rates_increase_interior.2.2.2.2⟩

#print axioms co_rate_trend
#print axioms measured_rates_increase_interior
#print axioms endpoint_rate_increases_robust
#print axioms last_step_direction_not_determined

end A7
end T8
end IChO2026
