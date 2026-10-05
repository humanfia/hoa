import IChO2026Chem.Reporting

/-!
# IChO 2026 T8-A9: reductive quenching of excited states

The problem supplies a bimolecular quenching rate constant, reductant
concentration, and unquenched lifetime for each excited state.  Mass action
makes the quenching channel pseudo-first-order, with rate `k * concentration`.
The unquenched lifetime gives the combined first-order rate of all competing
intrinsic channels as `1 / lifetime`.  Thus the fraction leaving through the
quenching channel is its rate divided by the total rate.

All printed decimal data are represented below as exact rational real numbers.
The two final decimal values are introduced only at the reporting boundary.
-/

namespace IChO2026Problems.T8A9

open IChO2026Chem.Reporting

noncomputable section

/-- The three problem inputs needed for one excited state.  Units are
`M⁻¹ s⁻¹`, `M`, and `s`, respectively. -/
structure QuenchingInputs where
  bimolecularRate : ℝ
  concentration : ℝ
  unquenchedLifetime : ℝ

/-- Mass action at fixed reductant concentration turns the bimolecular
quenching channel into a pseudo-first-order channel. -/
def pseudoFirstOrderQuenchingRate (d : QuenchingInputs) : ℝ :=
  d.bimolecularRate * d.concentration

/-- The total rate of the non-quenching channels, obtained from the supplied
emission lifetime measured in the absence of quencher. -/
def intrinsicFirstOrderRate (d : QuenchingInputs) : ℝ :=
  1 / d.unquenchedLifetime

/-- Branching fraction for quenching among the competing first-order exit
channels from an excited state. -/
def quenchingFraction (d : QuenchingInputs) : ℝ :=
  pseudoFirstOrderQuenchingRate d /
    (intrinsicFirstOrderRate d + pseudoFirstOrderQuenchingRate d)

/-- The requested percentage rather than a fraction. -/
def quenchingPercentage (d : QuenchingInputs) : ℝ :=
  100 * quenchingFraction d

/-- Algebraic form of the competition law in terms of the dimensionless
Stern--Volmer strength `k * concentration * lifetime`. -/
theorem quenchingFraction_eq_dimensionless
    (d : QuenchingInputs)
    (hlife : 0 < d.unquenchedLifetime)
    (hq : 0 ≤ pseudoFirstOrderQuenchingRate d) :
    quenchingFraction d =
      (pseudoFirstOrderQuenchingRate d * d.unquenchedLifetime) /
        (1 + pseudoFirstOrderQuenchingRate d * d.unquenchedLifetime) := by
  have hlife0 : d.unquenchedLifetime ≠ 0 := ne_of_gt hlife
  have hintrinsic : 0 < intrinsicFirstOrderRate d := by
    exact one_div_pos.mpr hlife
  have hleft : intrinsicFirstOrderRate d + pseudoFirstOrderQuenchingRate d ≠ 0 := by
    exact ne_of_gt (add_pos_of_pos_of_nonneg hintrinsic hq)
  have hright :
      1 + pseudoFirstOrderQuenchingRate d * d.unquenchedLifetime ≠ 0 := by
    apply ne_of_gt
    exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hq (le_of_lt hlife))
  unfold quenchingFraction intrinsicFirstOrderRate
  field_simp [hlife0, hleft, hright]

/-! ## Problem-stated numerical data -/

/-- `[Red] = 0.1 M`, common to the two requested calculations. -/
def reductantConcentration : ℝ := 1 / 10

/-- `k_S = 2.7 × 10⁹ M⁻¹ s⁻¹` and `τ₀(S₁) = 2.9 ns`. -/
def s1Inputs : QuenchingInputs where
  bimolecularRate := 2700000000
  concentration := reductantConcentration
  unquenchedLifetime := 29 / 10000000000

/-- `k_T = 1.5 × 10⁸ M⁻¹ s⁻¹` and `τ₀(T₁) = 84 μs`. -/
def t1Inputs : QuenchingInputs where
  bimolecularRate := 150000000
  concentration := reductantConcentration
  unquenchedLifetime := 84 / 1000000

/-! ## Exact derived quantities -/

theorem s1_pseudoFirstOrder_rate :
    pseudoFirstOrderQuenchingRate s1Inputs = 270000000 := by
  norm_num [pseudoFirstOrderQuenchingRate, s1Inputs, reductantConcentration]

theorem t1_pseudoFirstOrder_rate :
    pseudoFirstOrderQuenchingRate t1Inputs = 15000000 := by
  norm_num [pseudoFirstOrderQuenchingRate, t1Inputs, reductantConcentration]

theorem s1_dimensionless_strength :
    pseudoFirstOrderQuenchingRate s1Inputs * s1Inputs.unquenchedLifetime =
      783 / 1000 := by
  norm_num [pseudoFirstOrderQuenchingRate, s1Inputs, reductantConcentration]

theorem t1_dimensionless_strength :
    pseudoFirstOrderQuenchingRate t1Inputs * t1Inputs.unquenchedLifetime =
      1260 := by
  norm_num [pseudoFirstOrderQuenchingRate, t1Inputs, reductantConcentration]

/-- Exact raw S₁ quenching percentage, before decimal reporting. -/
theorem s1_quenchingPercentage_exact :
    quenchingPercentage s1Inputs = 78300 / 1783 := by
  norm_num [quenchingPercentage, quenchingFraction,
    pseudoFirstOrderQuenchingRate, intrinsicFirstOrderRate,
    s1Inputs, reductantConcentration]

/-- Exact raw T₁ quenching percentage, before decimal reporting. -/
theorem t1_quenchingPercentage_exact :
    quenchingPercentage t1Inputs = 126000 / 1261 := by
  norm_num [quenchingPercentage, quenchingFraction,
    pseudoFirstOrderQuenchingRate, intrinsicFirstOrderRate,
    t1Inputs, reductantConcentration]

/-! ## Three-significant-figure reporting -/

/-- S₁ result displayed as `43.9 %`, with last-place quantum `0.1 %`. -/
def s1Submission : NumericSubmission where
  rawValue := 78300 / 1783
  reportedValue := 439 / 10
  reportingQuantum := 1 / 10

/-- T₁ result displayed as `99.9 %`, with last-place quantum `0.1 %`. -/
def t1Submission : NumericSubmission where
  rawValue := 126000 / 1261
  reportedValue := 999 / 10
  reportingQuantum := 1 / 10

theorem s1_quenching_report :
    ValidNumericSubmission (quenchingPercentage s1Inputs) s1Submission := by
  constructor
  · change 78300 / 1783 = quenchingPercentage s1Inputs
    exact s1_quenchingPercentage_exact.symm
  · change ReportsAtQuantum (78300 / 1783) (439 / 10) (1 / 10)
    refine ⟨by norm_num, ?_, ?_⟩
    · exact ⟨439, by norm_num⟩
    · norm_num

theorem t1_quenching_report :
    ValidNumericSubmission (quenchingPercentage t1Inputs) t1Submission := by
  constructor
  · change 126000 / 1261 = quenchingPercentage t1Inputs
    exact t1_quenchingPercentage_exact.symm
  · change ReportsAtQuantum (126000 / 1261) (999 / 10) (1 / 10)
    refine ⟨by norm_num, ?_, ?_⟩
    · exact ⟨999, by norm_num⟩
    · norm_num

/-- Both requested answer-sheet entries.  The theorem exposes the exact raw
percentages and the displayed values directly, and also proves that each
display is a valid rounding at the independently fixed `0.1 %` quantum. -/
theorem final_quenching_outputs :
    quenchingPercentage s1Inputs = 78300 / 1783 ∧
    quenchingPercentage t1Inputs = 126000 / 1261 ∧
    s1Submission.reportedValue = 439 / 10 ∧
    t1Submission.reportedValue = 999 / 10 ∧
    ValidNumericSubmission (quenchingPercentage s1Inputs) s1Submission ∧
    ValidNumericSubmission (quenchingPercentage t1Inputs) t1Submission := by
  exact ⟨s1_quenchingPercentage_exact, t1_quenchingPercentage_exact,
    by norm_num [s1Submission], by norm_num [t1Submission],
    s1_quenching_report, t1_quenching_report⟩

#print axioms quenchingFraction_eq_dimensionless
#print axioms final_quenching_outputs

end
end IChO2026Problems.T8A9
