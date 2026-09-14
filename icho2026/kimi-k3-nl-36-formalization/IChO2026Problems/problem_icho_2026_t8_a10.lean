import Mathlib

/-!
# IChO 2026, problem 8.10: dynamic-quenching lifetime trend

The problem gives positive bimolecular reductive-quenching rate constants for
the singlet and triplet excited states and their emission lifetimes in the
absence of reductant.  Concentration is represented in molar units, time in
seconds, and rate constants in `M⁻¹ s⁻¹`, so the product `k * c` is a
pseudo-first-order rate in `s⁻¹`.

For competing first-order processes, rates add.  Thus the effective lifetime is
the reciprocal of `1 / τ₀ + k * c`.  The two requested answer carriers below
state strict antitonicity on the physically admissible domain `c ≥ 0`; the
reported choice is then checked against that quantitative specification.
-/

namespace IChO2026Problems.T8A10

noncomputable section

/-- The three alternatives printed in the T8-A10 choice panel. -/
inductive LifetimeTrend where
  | increases
  | decreases
  | unchanged
deriving DecidableEq, Repr

/-- Permitted provenance tags for a source-bounded candidate domain. -/
inductive CandidateDomainProvenance where
  | problem_text
  | problem_image
  | problem_stated_fallback
  | trusted_general_law
  | derived_theorem
deriving DecidableEq, Repr

/-- The alternatives come directly from the current-question choice panel. -/
def lifetimeTrendChoiceProvenance : CandidateDomainProvenance :=
  .problem_text

/-- Physically admissible reductant concentrations, expressed in molar units. -/
def nonnegativeMolarConcentrations : Set ℝ := Set.Ici 0

/-! ## Exact data printed on problem page 5 -/

/-- `τ₀(S₁) = 2.9 ns`, converted exactly to seconds. -/
def singletUnquenchedLifetimeSeconds : ℝ :=
  29 / 10 ^ 10

/-- `τ₀(T₁) = 84 μs`, converted exactly to seconds. -/
def tripletUnquenchedLifetimeSeconds : ℝ :=
  84 / 10 ^ 6

/-- `k_S = 2.7 × 10⁹ M⁻¹ s⁻¹`, represented exactly. -/
def singletQuenchingRatePerMolarSecond : ℝ :=
  27 * 10 ^ 8

/-- `k_T = 1.5 × 10⁸ M⁻¹ s⁻¹`, represented exactly. -/
def tripletQuenchingRatePerMolarSecond : ℝ :=
  15 * 10 ^ 7

/-- The concentration `[Red] = 0.1 M` specified in the prerequisite T8-A9. -/
def previousPartReductantConcentrationMolar : ℝ :=
  1 / 10

/-! ## Kinetic bridge -/

/-- Effective first-order decay rate in the absence of reductant. -/
def intrinsicDecayRatePerSecond (τ₀ : ℝ) : ℝ :=
  1 / τ₀

/-- Pseudo-first-order reductive-quenching rate `k_q [Red]`. -/
def quenchingRatePerSecond (k concentrationMolar : ℝ) : ℝ :=
  k * concentrationMolar

/-- Total rate for intrinsic decay competing with reductive quenching. -/
def totalDecayRatePerSecond
    (τ₀ k concentrationMolar : ℝ) : ℝ :=
  intrinsicDecayRatePerSecond τ₀ +
    quenchingRatePerSecond k concentrationMolar

/-- Emission lifetime under dynamic reductive quenching. -/
def quenchedLifetimeSeconds
    (τ₀ k concentrationMolar : ℝ) : ℝ :=
  1 / totalDecayRatePerSecond τ₀ k concentrationMolar

/-- The usual Stern--Volmer lifetime formula follows from the additive-rate
model. -/
theorem quenchedLifetime_eq_sternVolmer
    {τ₀ k concentrationMolar : ℝ}
    (hτ₀ : τ₀ ≠ 0) :
    quenchedLifetimeSeconds τ₀ k concentrationMolar =
      τ₀ / (1 + k * τ₀ * concentrationMolar) := by
  unfold quenchedLifetimeSeconds totalDecayRatePerSecond
    intrinsicDecayRatePerSecond quenchingRatePerSecond
  field_simp

/-- At zero reductant concentration the model recovers the printed unquenched
lifetime. -/
theorem quenchedLifetime_zero
    {τ₀ k : ℝ} (hτ₀ : τ₀ ≠ 0) :
    quenchedLifetimeSeconds τ₀ k 0 = τ₀ := by
  rw [quenchedLifetime_eq_sternVolmer hτ₀]
  simp

/-- A positive unquenched lifetime and positive bimolecular quenching constant
make the emission lifetime strictly decrease as nonnegative reductant
concentration increases. -/
theorem quenchedLifetime_strictAntiOn
    {τ₀ k : ℝ} (hτ₀ : 0 < τ₀) (hk : 0 < k) :
    StrictAntiOn (quenchedLifetimeSeconds τ₀ k)
      nonnegativeMolarConcentrations := by
  intro c₁ hc₁ c₂ hc₂ hc₁₂
  change 0 ≤ c₁ at hc₁
  have hintrinsic : 0 < 1 / τ₀ := one_div_pos.mpr hτ₀
  have hquench₁ : 0 ≤ k * c₁ := mul_nonneg hk.le hc₁
  have htotal₁ : 0 < 1 / τ₀ + k * c₁ :=
    add_pos_of_pos_of_nonneg hintrinsic hquench₁
  have htotal : 1 / τ₀ + k * c₁ < 1 / τ₀ + k * c₂ :=
    by nlinarith [mul_lt_mul_of_pos_left hc₁₂ hk]
  exact one_div_lt_one_div_of_lt htotal₁ htotal

/-! ## Inline derivation of the T8-A9 prerequisite -/

/-- Fraction of excited states removed through the added quenching channel. -/
def quenchingFraction
    (τ₀ k concentrationMolar : ℝ) : ℝ :=
  quenchingRatePerSecond k concentrationMolar /
    totalDecayRatePerSecond τ₀ k concentrationMolar

/-- Quenching fraction expressed as a percentage. -/
def quenchingPercentage
    (τ₀ k concentrationMolar : ℝ) : ℝ :=
  100 * quenchingFraction τ₀ k concentrationMolar

/-- Exact, unrounded S₁ quenching percentage at `[Red] = 0.1 M`. -/
theorem previousPart_singletQuenchingPercentage :
    quenchingPercentage singletUnquenchedLifetimeSeconds
        singletQuenchingRatePerMolarSecond
        previousPartReductantConcentrationMolar =
      (78300 : ℝ) / 1783 := by
  norm_num [quenchingPercentage, quenchingFraction,
    quenchingRatePerSecond, totalDecayRatePerSecond,
    intrinsicDecayRatePerSecond, singletUnquenchedLifetimeSeconds,
    singletQuenchingRatePerMolarSecond,
    previousPartReductantConcentrationMolar]

/-- Exact, unrounded T₁ quenching percentage at `[Red] = 0.1 M`. -/
theorem previousPart_tripletQuenchingPercentage :
    quenchingPercentage tripletUnquenchedLifetimeSeconds
        tripletQuenchingRatePerMolarSecond
        previousPartReductantConcentrationMolar =
      (126000 : ℝ) / 1261 := by
  norm_num [quenchingPercentage, quenchingFraction,
    quenchingRatePerSecond, totalDecayRatePerSecond,
    intrinsicDecayRatePerSecond, tripletUnquenchedLifetimeSeconds,
    tripletQuenchingRatePerMolarSecond,
    previousPartReductantConcentrationMolar]

/-! ## Classification semantics and requested outputs -/

/-- Meaning of each choice in terms of the concentration-dependent lifetime.
The domain restriction excludes chemically meaningless negative
concentrations. -/
def HasLifetimeTrend (τ₀ k : ℝ) : LifetimeTrend → Prop
  | .increases =>
      StrictMonoOn (quenchedLifetimeSeconds τ₀ k)
        nonnegativeMolarConcentrations
  | .decreases =>
      StrictAntiOn (quenchedLifetimeSeconds τ₀ k)
        nonnegativeMolarConcentrations
  | .unchanged =>
      ∀ ⦃c₁ c₂ : ℝ⦄,
        c₁ ∈ nonnegativeMolarConcentrations →
        c₂ ∈ nonnegativeMolarConcentrations →
        quenchedLifetimeSeconds τ₀ k c₁ =
          quenchedLifetimeSeconds τ₀ k c₂

/-- Candidate selected for the requested S₁ classification.  Its specification
below is the nontrivial strict-antitonicity obligation. -/
def lifetimeS1Answer : LifetimeTrend := .decreases

/-- Candidate selected for the requested T₁ classification.  Its specification
below is the nontrivial strict-antitonicity obligation. -/
def lifetimeT1Answer : LifetimeTrend := .decreases

/-- Source-derived raw proposition for requested output `lifetime_s1`. -/
def LifetimeS1RawResult : Prop :=
  StrictAntiOn
    (quenchedLifetimeSeconds singletUnquenchedLifetimeSeconds
      singletQuenchingRatePerMolarSecond)
    nonnegativeMolarConcentrations

/-- Source-derived raw proposition for requested output `lifetime_t1`. -/
def LifetimeT1RawResult : Prop :=
  StrictAntiOn
    (quenchedLifetimeSeconds tripletUnquenchedLifetimeSeconds
      tripletQuenchingRatePerMolarSecond)
    nonnegativeMolarConcentrations

/-- Exact reported classification proposition for requested output
`lifetime_s1`. -/
def LifetimeS1ReportedResult : Prop :=
  HasLifetimeTrend singletUnquenchedLifetimeSeconds
    singletQuenchingRatePerMolarSecond lifetimeS1Answer

/-- Exact reported classification proposition for requested output
`lifetime_t1`. -/
def LifetimeT1ReportedResult : Prop :=
  HasLifetimeTrend tripletUnquenchedLifetimeSeconds
    tripletQuenchingRatePerMolarSecond lifetimeT1Answer

/-- Raw-result carrier for the S₁ output. -/
theorem lifetimeS1_raw_result : LifetimeS1RawResult := by
  unfold LifetimeS1RawResult
  apply quenchedLifetime_strictAntiOn
  · norm_num [singletUnquenchedLifetimeSeconds]
  · norm_num [singletQuenchingRatePerMolarSecond]

/-- Raw-result carrier for the T₁ output. -/
theorem lifetimeT1_raw_result : LifetimeT1RawResult := by
  unfold LifetimeT1RawResult
  apply quenchedLifetime_strictAntiOn
  · norm_num [tripletUnquenchedLifetimeSeconds]
  · norm_num [tripletQuenchingRatePerMolarSecond]

/-- Reported-result carrier certifying choice (b) for S₁. -/
theorem lifetimeS1_reported_result : LifetimeS1ReportedResult := by
  simpa [LifetimeS1ReportedResult, HasLifetimeTrend, lifetimeS1Answer,
    LifetimeS1RawResult] using lifetimeS1_raw_result

/-- Reported-result carrier certifying choice (b) for T₁. -/
theorem lifetimeT1_reported_result : LifetimeT1ReportedResult := by
  simpa [LifetimeT1ReportedResult, HasLifetimeTrend, lifetimeT1Answer,
    LifetimeT1RawResult] using lifetimeT1_raw_result

/-- Combined raw proposition, preserving the source output order S₁ then T₁. -/
def RawResult : Prop :=
  LifetimeS1RawResult ∧ LifetimeT1RawResult

/-- Combined exact-symbolic reported proposition, preserving the source output
order S₁ then T₁. -/
def ReportedResult : Prop :=
  LifetimeS1ReportedResult ∧ LifetimeT1ReportedResult

/-- Combined raw result contract for T8-A10. -/
theorem raw_result : RawResult := by
  exact ⟨lifetimeS1_raw_result, lifetimeT1_raw_result⟩

/-- Combined reported result contract for T8-A10. -/
theorem reported_result : ReportedResult := by
  exact ⟨lifetimeS1_reported_result, lifetimeT1_reported_result⟩

end

end IChO2026Problems.T8A10
