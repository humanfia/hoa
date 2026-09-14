import IChO2026Chem

/-!
# IChO 2026, Theory Problem 8 (T8), Subquestion 8.9 — target `icho_2026_t8_a9`

## Problem statement (official English paper, page Q8‑5)

> Photosensitisers (PS) offer some advantages over C₃N₄ for the reduction of CO₂. …
> In this system, reductive quenching of the *singlet* (S₁) and *triplet* (T₁)
> excited states of a PS by reductant (Red) forms PS•⁻, which donates electrons
> to CO₂ through the Mn(I)-containing complex.
>
> PS(S₁) + Red →(k_S) PS•⁻ + Red•⁺        k_S = 2.7 × 10⁹ M⁻¹ s⁻¹
> PS(T₁) + Red →(k_T) PS•⁻ + Red•⁺        k_T = 1.5 × 10⁸ M⁻¹ s⁻¹
>
> τ₀(S₁) = 2.9 ns and τ₀(T₁) = 84 μs, where τ₀ is the emission lifetime in the
> absence of the quencher.
>
> **8.9** *Calculate* the percentage of quenching, η_q, (in %) of S₁ and T₁
> states, when [Red] = 0.1 M.  Note: here k_F >> k_ISC.

## Kinetic model (derived, not assumed)

For each excited state the natural decay channels (fluorescence k_F and
internal conversion k_IC for S₁ under the note k_F >> k_ISC; phosphorescence
k_P and non-radiative decay k_N for T₁) are collected into a single unimolecular
rate constant k₀ = 1/τ₀, since τ₀ is by definition the lifetime with no
quencher present.  Quenching by Red at fixed concentration acts as a competing
pseudo-first-order channel with rate constant kq = k_Q·[Red].

The excited-state population N(t) then decays monoexponentially,
`N(t) = N0 * exp (-(k0 + kq) * t)`, and the probability that a PS molecule
initially in the excited state ends up quenched is the integral of the
quenching channel's rate over the whole decay:

  η_q = ∫₀^∞ kq · exp(−(k₀ + kq) t) dt = kq / (k₀ + kq).

We *prove* this integral below (`fractionQuenched_of_competingChannels`) using
the second fundamental theorem of calculus on `(0, ∞)`.

## Results

* S₁: kq(S₁) = k_S·[Red] = 2.7×10⁹ × 0.1 = 2.7×10⁸ s⁻¹; k₀(S₁) = 1/(2.9 ns).
  Dimensionless Stern–Volmer product kq/k₀ = 2.7×10⁸ × 2.9×10⁻⁹ = 0.783.
  η_q(S₁) = 0.783/1.783 = 783/1783 ≈ 0.439147… → **43.9 %**.

* T₁: kq(T₁) = k_T·[Red] = 1.5×10⁸ × 0.1 = 1.5×10⁷ s⁻¹; k₀(T₁) = 1/(84 μs).
  Dimensionless product kq/k₀ = 1.5×10⁷ × 84×10⁻⁶ = 1260.
  η_q(T₁) = 1260/1261 ≈ 0.999207… → **99.9 %**.

The note k_F >> k_ISC means almost no triplet population is generated from S₁
quenching competition, so the two states quench as independent populations —
exactly the model the printed lifetimes τ₀ describe.
-/

open scoped Interval Real
open MeasureTheory Set

namespace IChO2026.ProbT8A9

/-! ## Problem data (exactly as printed in the paper) -/

/-- Bimolecular quenching rate constant of the S₁ state, in M⁻¹ s⁻¹. -/
noncomputable def kS : ℝ := 2.7e9

/-- Bimolecular quenching rate constant of the T₁ state, in M⁻¹ s⁻¹. -/
noncomputable def kT : ℝ := 1.5e8

/-- Reductant concentration at which the quenching percentages are requested, in M. -/
noncomputable def redConc : ℝ := 0.1

/-- Emission lifetime of S₁ in the absence of quencher, in seconds (2.9 ns). -/
noncomputable def τ0S1 : ℝ := 2.9e-9

/-- Emission lifetime of T₁ in the absence of quencher, in seconds (84 μs). -/
noncomputable def τ0T1 : ℝ := 84e-6

/-- Quenching percentage asked for by the paper, in %: fraction quenched × 100. -/
noncomputable def quenchingPercentage (kQ τ : ℝ) : ℝ :=
  (kQ * redConc) / (kQ * redConc + 1 / τ) * 100

/-! ## Derivation of the quenching-fraction formula from the kinetic model

We model the population of an excited state decaying through two competing
first-order channels: natural decay (rate constant k₀, unimolecular) and
pseudo-first-order quenching by Red (rate constant kq).  The fraction of the
initial population that ends up quenched is the integral of the quenching
channel's instantaneous rate over the whole decay, divided by the initial
population. -/

/-- Excited-state population under competing first-order natural decay (k₀)
and quenching (kq), both per second. -/
noncomputable def excitedPopulation (N0 k0 kq : ℝ) (t : ℝ) : ℝ :=
  N0 * Real.exp (-(k0 + kq) * t)

private theorem hasDerivAt_excitedPopulation_aux {k : ℝ} (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-k * s)) (-k * Real.exp (-k * t)) t := by
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_exp (-k * t)).comp t ((hasDerivAt_id t).const_mul (-k))

private theorem tendsto_exp_neg_mul_atTop {k : ℝ} (hk : 0 < k) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-(k * t))) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun t : ℝ => k * t) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hk Filter.tendsto_id
  have hneg : Filter.Tendsto (fun t : ℝ => -(k * t)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp h
  exact Real.tendsto_exp_atBot.comp hneg

private theorem integral_exp_neg_mul_Ioi_zero {k : ℝ} (hk : 0 < k) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(k * t)) = 1 / k := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun s : ℝ => Real.exp (-(k * s))) (-k * Real.exp (-(k * x))) x :=
    fun x _ => by
      simpa [neg_mul] using hasDerivAt_excitedPopulation_aux (k := k) x
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(k * t))) (Ioi (0 : ℝ)) := by
    have h := integrableOn_exp_mul_Ioi (a := -k) (by simpa using hk) (0 : ℝ)
    have heq : (fun x : ℝ => Real.exp ((-k) * x))
        = fun t : ℝ => Real.exp (-(k * t)) := by
      funext t; rw [neg_mul]
    rw [heq] at h
    exact h
  have hlim : Filter.Tendsto (fun t : ℝ => Real.exp (-(k * t))) Filter.atTop (nhds 0) :=
    tendsto_exp_neg_mul_atTop hk
  have heq2 : (fun t : ℝ => -k * Real.exp (-(k * t)))
      = fun t : ℝ => Real.exp (-(k * t)) * (-k) := by
    funext t; ring
  have hint' : IntegrableOn (fun t : ℝ => -k * Real.exp (-(k * t))) (Ioi (0 : ℝ)) := by
    rw [heq2]
    exact hint.mul_const _
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint' hlim
  have hzero : Real.exp (-(k * 0)) = 1 := by simp
  rw [hzero] at hmain
  have hinteg : ∫ t in Ioi (0 : ℝ), -k * Real.exp (-(k * t)) = -1 := by
    rw [hmain]; ring
  have hinteg' : ∫ t in Ioi (0 : ℝ), Real.exp (-(k * t)) * (-k) = -1 := by
    rwa [heq2] at hinteg
  have hpull : ∫ t in Ioi (0 : ℝ), Real.exp (-(k * t)) * (-k)
      = (∫ t in Ioi (0 : ℝ), Real.exp (-(k * t))) * (-k) :=
    integral_mul_const (-k) (fun t : ℝ => Real.exp (-(k * t)))
  rw [hpull] at hinteg'
  have heq_intmul : (∫ t in Ioi (0 : ℝ), Real.exp (-(k * t))) * k = 1 := by
    nlinarith [hinteg']
  have hk' : k ≠ 0 := hk.ne'
  rw [show (∫ t in Ioi (0 : ℝ), Real.exp (-(k * t)))
      = ((∫ t in Ioi (0 : ℝ), Real.exp (-(k * t))) * k) / k from (mul_div_cancel_right₀ _ hk').symm]
  rw [heq_intmul]

/-- If the excited-state population exactly follows the competition model
`N(t) = N0 * exp (−(k0 + kq) t)` with positive total rate `k0 + kq`, then the
fraction of the initial population that is quenched by the channel of rate
constant `kq` is exactly `kq / (k0 + kq)`.  This is the derivation of the
quenching percentage formula used below. -/
theorem fractionQuenched_of_competingChannels {N0 k0 kq : ℝ}
    (hN0 : 0 < N0) (hk : 0 < k0 + kq)
    (hpop : ∀ t : ℝ, excitedPopulation N0 k0 kq t = N0 * Real.exp (-(k0 + kq) * t) := by
      intro t; rfl) :
    (∫ t in Ioi (0 : ℝ), kq * excitedPopulation N0 k0 kq t) / N0 = kq / (k0 + kq) := by
  simp_rw [excitedPopulation]
  have h_int : ∫ t in Ioi (0 : ℝ), kq * (N0 * Real.exp (-(k0 + kq) * t))
      = kq * N0 * (1 / (k0 + kq)) := by
    have h_factor : (fun t : ℝ => kq * (N0 * Real.exp (-(k0 + kq) * t))) =
        fun t : ℝ => Real.exp (-(k0 + kq) * t) * (kq * N0) := by
      funext t; ring
    rw [h_factor, integral_mul_const]
    have hconv : ∀ t : ℝ, -(k0 + kq) * t = -((k0 + kq) * t) := fun t => neg_mul _ _
    simp_rw [hconv, integral_exp_neg_mul_Ioi_zero hk]
    ring
  rw [h_int]
  field_simp

/-! ## Instantiation with the printed data -/

-- The unimolecular natural decay rate constants implied by the lifetimes (exact):
--   k₀(S₁) = 1/τ₀(S₁) = 10⁹ / 2.9 = 10¹⁰ / 29 s⁻¹
--   k₀(T₁) = 1/τ₀(T₁) = 10⁶ / 84 = 250 000 / 21 s⁻¹
-- The pseudo-first-order quenching rate constants at [Red] = 0.1 M:
--   kq(S₁) = k_S · [Red] = 2.7 × 10⁸ s⁻¹
--   kq(T₁) = k_T · [Red] = 1.5 × 10⁷ s⁻¹

/-- The pseudo-first-order quenching rate constant of S₁ at [Red] = 0.1 M
in exact rational form. -/
theorem kq_S1 : kS * redConc = 2.7e8 := by
  unfold kS redConc; norm_num

/-- The natural decay rate constant of S₁ implied by τ₀(S₁) = 2.9 ns. -/
theorem k0_S1 : 1 / τ0S1 = 1e10 / 29 := by
  unfold τ0S1; norm_num

/-- The pseudo-first-order quenching rate constant of T₁ at [Red] = 0.1 M. -/
theorem kq_T1 : kT * redConc = 1.5e7 := by
  unfold kT redConc; norm_num

/-- The natural decay rate constant of T₁ implied by τ₀(T₁) = 84 μs. -/
theorem k0_T1 : 1 / τ0T1 = 250000 / 21 := by
  unfold τ0T1; norm_num

/-- Dimensionless Stern–Volmer competition ratio for S₁: kq(S₁)·τ₀(S₁) = 0.783. -/
theorem competitionRatio_S1 : kS * redConc * τ0S1 = 7.83e-1 := by
  unfold kS redConc τ0S1; norm_num

/-- Dimensionless Stern–Volmer competition ratio for T₁: kq(T₁)·τ₀(T₁) = 1260. -/
theorem competitionRatio_T1 : kT * redConc * τ0T1 = 1260 := by
  unfold kT redConc τ0T1; norm_num

/-- **Main result, S₁ state**: the quenching percentage at [Red] = 0.1 M is
exactly `78300/1783 %` ≈ 43.9147… %, which displays to **43.9 %** at three
significant figures. -/
theorem quenchingPercentage_S1 : quenchingPercentage kS τ0S1 = 78300 / 1783 := by
  unfold quenchingPercentage
  rw [kq_S1, k0_S1]
  norm_num

/-- **Main result, T₁ state**: the quenching percentage at [Red] = 0.1 M is
exactly `126000/1261 %` ≈ 99.9207… %, which displays to **99.9 %** at three
significant figures. -/
theorem quenchingPercentage_T1 : quenchingPercentage kT τ0T1 = 126000 / 1261 := by
  unfold quenchingPercentage
  rw [kq_T1, k0_T1]
  norm_num

/-- S₁ is only partly quenched (43.9147… % < 100), so even at [Red] = 0.1 M the
quenching of the singlet is far from saturating. -/
theorem quenchingPercentage_S1_lt_100 : quenchingPercentage kS τ0S1 < 100 := by
  rw [quenchingPercentage_S1]; norm_num

/-- T₁ is essentially fully quenched (99.9207… % > 99 %). -/
theorem quenchingPercentage_T1_gt_99 : 99 < quenchingPercentage kT τ0T1 := by
  rw [quenchingPercentage_T1]; norm_num

/-- The T₁ state is quenched more strongly than the S₁ state at [Red] = 0.1 M. -/
theorem quenchingPercentage_T1_gt_S1 :
    quenchingPercentage kS τ0S1 < quenchingPercentage kT τ0T1 := by
  rw [quenchingPercentage_T1, quenchingPercentage_S1]; norm_num

/-! ## Answer-blind final reporting at three significant figures

The reporting policy for this target fixes the final display quantum of
0.1 percentage points for both outputs (three significant figures: 43.9 % and
99.9 %).  The raw values stay exact; rounding happens only at this boundary. -/

/-- The exact requested S₁ output is reported as `43.9 %` at quantum 0.1,
with the nearest-multiple-with-ties-away-from-zero rule. -/
theorem reportsAt_S1 :
    IChO2026Chem.Reporting.ReportsAtQuantum (78300 / 1783) (43.9 : ℝ) 0.1 := by
  refine ⟨by norm_num, ⟨439, by norm_num⟩, ?_⟩
  norm_num

/-- The exact requested T₁ output is reported as `99.9 %` at quantum 0.1. -/
theorem reportsAt_T1 :
    IChO2026Chem.Reporting.ReportsAtQuantum (126000 / 1261) (99.9 : ℝ) 0.1 := by
  refine ⟨by norm_num, ⟨999, by norm_num⟩, ?_⟩
  norm_num

/-- Final submission for the S₁ quenching percentage: raw value `78300/1783 %`,
reported value `43.9 %` at quantum `0.1` percentage points. -/
noncomputable def submissionS1 : IChO2026Chem.Reporting.NumericSubmission where
  rawValue := quenchingPercentage kS τ0S1
  reportedValue := 43.9
  reportingQuantum := 0.1

/-- Final submission for the T₁ quenching percentage: raw value `126000/1261 %`,
reported value `99.9 %` at quantum `0.1` percentage points. -/
noncomputable def submissionT1 : IChO2026Chem.Reporting.NumericSubmission where
  rawValue := quenchingPercentage kT τ0T1
  reportedValue := 99.9
  reportingQuantum := 0.1

/-- The S₁ submission satisfies the project answer-blind numeric contract. -/
theorem validSubmission_S1 :
    IChO2026Chem.Reporting.ValidNumericSubmission
      (quenchingPercentage kS τ0S1) submissionS1 := by
  refine ⟨rfl, ?_⟩
  rw [show submissionS1.rawValue = quenchingPercentage kS τ0S1 from rfl,
    show submissionS1.reportedValue = 43.9 from rfl,
    show submissionS1.reportingQuantum = 0.1 from rfl]
  refine ⟨by norm_num, ⟨439, by norm_num⟩, ?_⟩
  rw [if_pos (by rw [quenchingPercentage_S1]; norm_num)]
  rw [quenchingPercentage_S1]
  norm_num

/-- The T₁ submission satisfies the project answer-blind numeric contract. -/
theorem validSubmission_T1 :
    IChO2026Chem.Reporting.ValidNumericSubmission
      (quenchingPercentage kT τ0T1) submissionT1 := by
  refine ⟨rfl, ?_⟩
  rw [show submissionT1.rawValue = quenchingPercentage kT τ0T1 from rfl,
    show submissionT1.reportedValue = 99.9 from rfl,
    show submissionT1.reportingQuantum = 0.1 from rfl]
  refine ⟨by norm_num, ⟨999, by norm_num⟩, ?_⟩
  rw [if_pos (by rw [quenchingPercentage_T1]; norm_num)]
  rw [quenchingPercentage_T1]
  norm_num

#print axioms quenchingPercentage_S1
#print axioms quenchingPercentage_T1
#print axioms fractionQuenched_of_competingChannels
#print axioms validSubmission_S1
#print axioms validSubmission_T1

end IChO2026.ProbT8A9
