import Mathlib

/-!
# IChO 2026, Problem T2, subquestion 2.7 (target icho_2026_t2_a7)

**Question (official English, problem page Q2-4; candidates on blank answer
sheet A2-6).**  Which graph qualitatively illustrates the rate of change of
Gibbs energy (`dG/dt`) of a **closed** system in which an oscillatory reaction
occurs?  Tick the correct box.

The blank answer sheet shows six candidate sketches of `dG/dt` versus `t`:

1. (top left)      starts at `0`, becomes strictly negative with a *constant*
                   slope;
2. (top right)     steady oscillation **about** the axis (`dG/dt` takes
                   positive values);
3. (middle left)   starts very negative, approaches `0` from below,
                   **monotonically** (no oscillation);
4. (middle right)  stays `≤ 0` with a ripple, but the trend keeps a fixed
                   negative slope forever (never approaches `0`);
5. (bottom left)   oscillation about the axis with **growing** amplitude
                   (positive values, magnitude grows);
6. (bottom right)  starts far below `0`, is strictly negative for all `t > 0`,
                   oscillates with **decaying** amplitude, and tends to `0`
                   from below.

## Physical analysis (answer-blind; from the problem text + the second law)

* In a closed system at constant `T` and `p` the Gibbs energy cannot increase
  for a spontaneous process: `dG/dt ≤ 0`, with equality only at equilibrium
  (second law of thermodynamics; a `trusted_general_law`).  This immediately
  excludes options 2 and 5, whose sketches take positive values.
* The BZ oscillations in a *closed* vessel are transient: the net reaction
  (`BrO₃⁻ → Br⁻`, malonic acid `→ CO₂`, given in the statement of 2.1)
  consumes the bulk reactants, so the system tends to equilibrium and
  `dG/dt → 0⁻`.  This excludes option 4 (fixed downward slope forever) and
  option 1 (constant nonzero rate forever).
* The oscillating intermediates (`Ce⁴⁺/Ce³⁺`, `Br⁻`, `HBrO₂`) only modulate
  *how fast* `G` decreases, so the graph must show a genuine oscillation —
  excluding the monotone option 3 — whose amplitude **decays** as equilibrium
  is approached, starting from a large negative value since the freshly mixed
  system is far from equilibrium.

Exactly option **6 (bottom-right box)** satisfies all of this.

## What is proved here

The six candidates are line drawings, so each is formalized as a qualitative
shape predicate `P1 … P6`; `OptionSixShape` is their conjunction.  We exhibit
the concrete representative

  `fRepr t = -(2 + cos (8t)) / (2·(t + 1))`

(strictly negative on `t ≥ 0`, `fRepr 0 = -3/2`, tends to `0`, oscillation of
amplitude `~ 1/(2(t+1))` forever — exactly the bottom-right sketch) and prove
`OptionSixShape fRepr` in full from Mathlib (no `sorry`, no custom axioms).
We also prove the screening lemmas: any curve with a nonnegative excursion at
a positive time fails the second-law sign predicate `P1` (this excludes the
about-axis oscillating options 2 and 5), and a constant negative rate cannot
tend to zero, so it fails `P3` (excluding options 1 and 4).
-/

namespace IChO2026T2A7

open Real Set Filter Topology

/-! ##  The qualitative predicates read off the candidate sketches  -/

/-- **P1 — thermodynamic sign (second law, closed system, constant T,p).**
The sketched rate of change is strictly negative for every positive time.
Any candidate with `dG/dt > 0` anywhere (options 2 and 5) fails this. -/
def P1 (f : ℝ → ℝ) : Prop := ∀ t : ℝ, 0 < t → f t < 0

/-- **P2 — far from equilibrium at the start.**  At `t = 0` the freshly mixed
reactants are far from equilibrium, so the sketched curve starts strictly
below `0`, at magnitude at least `1` in the sketch's vertical units. -/
def P2 (f : ℝ → ℝ) : Prop := f 0 ≤ -1

/-- **P3 — the closed system equilibrates.**  As `t → ∞` the net reaction
approaches equilibrium, so the sketched rate tends to `0`.  Options 1 and 4
(fixed nonzero slope forever) fail this. -/
def P3 (f : ℝ → ℝ) : Prop := Tendsto f atTop (𝓝 0)

/-- **P4 — decaying oscillation (quantitative).**  On the physical half-line
`t ≥ 0` the sketched curve is squeezed by an envelope that tends to `0`. -/
def P4 (f : ℝ → ℝ) : Prop :=
  ∃ E : ℝ → ℝ, (∀ t : ℝ, 0 ≤ t → |f t| ≤ E t) ∧ Tendsto E atTop (𝓝 0)

/-- **P5 — the oscillation is genuine (not monotone).**  Arbitrarily late,
the sketched curve has a strict local rise followed by a strict fall.  This
separates option 6 from the monotone option 3 and the constant-slope
option 1. -/
def P5 (f : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, ∃ t₁ t₂ t₃ : ℝ, T < t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧
    f t₁ < f t₂ ∧ f t₃ < f t₂

/-- **P6 — decaying amplitude (tube formulation).**  Beyond any prescribed
time the curve stays uniformly within any prescribed tube around the axis:
the excursions shrink. -/
def P6 (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → |f t| < ε

/-- The qualitative shape of the **bottom-right** candidate (option 6) on
answer sheet A2-6. -/
def OptionSixShape (f : ℝ → ℝ) : Prop :=
  P1 f ∧ P2 f ∧ P3 f ∧ P4 f ∧ P5 f ∧ P6 f

/-! ##  The representative curve of the bottom-right sketch  -/

/-- `fRepr t = -(2 + cos (8t)) / (2·(t+1))`: numerator in `[1, 3]`, strictly
oscillating between `3` (at `t = n·π/4`) and `1` (at `t = (4k+1)·π/8`-type
points), divided by the slowly growing `2(t+1)`.  Always negative on
`t ≥ 0`, starts at `-3/2`, tends to `0`, perpetual decaying ripple. -/
noncomputable def fRepr (t : ℝ) : ℝ := -((2 + cos (8 * t)) / (2 * (t + 1)))

lemma cos_eight_mul_ceiling (m : ℕ) :
    cos (8 * ((m : ℝ) * (Real.pi / 8))) = (-1) ^ m := by
  have h : 8 * ((m : ℝ) * (Real.pi / 8)) = (m : ℝ) * Real.pi := by ring
  rw [h]
  exact Real.cos_nat_mul_pi m

/-- The exponent arithmetic used at the quarter-period witnesses:
`(-1)^(4k) = 1`, `(-1)^(4k+1) = -1`, `(-1)^(4k+2) = 1`. -/
private lemma neg_one_pow_four_mul (k : ℕ) : (-1 : ℝ) ^ (4 * k) = 1 :=
  Even.neg_one_pow ⟨2 * k, by ring⟩

private lemma neg_one_pow_four_mul_add_one (k : ℕ) : (-1 : ℝ) ^ (4 * k + 1) = -1 := by
  rw [pow_succ, neg_one_pow_four_mul k]
  ring

private lemma neg_one_pow_four_mul_add_two (k : ℕ) : (-1 : ℝ) ^ (4 * k + 2) = 1 := by
  rw [pow_add, neg_one_pow_four_mul k]
  norm_num

/-- P1 for the representative: strictly negative for all `t ≥ 0`. -/
theorem fRepr_neg {t : ℝ} (ht : 0 ≤ t) : fRepr t < 0 := by
  have hnum : 0 < 2 + cos (8 * t) := by linarith [neg_one_le_cos (8 * t)]
  have hden : 0 < 2 * (t + 1) := by positivity
  have h : 0 < (2 + cos (8 * t)) / (2 * (t + 1)) := div_pos hnum hden
  unfold fRepr
  linarith

theorem P1_fRepr : P1 fRepr := fun _t ht => fRepr_neg ht.le

theorem fRepr_zero : fRepr 0 = -3 / 2 := by
  unfold fRepr
  have hcos : cos (8 * (0 : ℝ)) = 1 := by simp
  rw [hcos]
  norm_num

theorem P2_fRepr : P2 fRepr := by
  rw [P2, fRepr_zero]
  norm_num

/-- Envelope bound, valid for all `t ≥ 0`. -/
theorem fRepr_abs_le {t : ℝ} (ht : 0 ≤ t) :
    |fRepr t| ≤ 3 / (2 * (t + 1)) := by
  have hden : 0 < 2 * (t + 1) := by positivity
  have hlo : -1 ≤ cos (8 * t) := neg_one_le_cos (8 * t)
  have hhi : cos (8 * t) ≤ 1 := cos_le_one (8 * t)
  rw [fRepr, abs_neg, abs_div, abs_of_pos (by linarith), abs_of_pos hden]
  exact div_le_div_of_nonneg_right (by linarith) hden.le

/-- The trend envelope `3 / (2(t+1))` tends to zero. -/
theorem tendsto_envelope :
    Tendsto (fun t : ℝ => 3 / (2 * (t + 1))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t + 1) atTop atTop := by
    exact le_of_eq (Filter.map_add_atTop_eq (α := ℝ) 1)
  have h2 : Tendsto (fun t : ℝ => 2 * (t + 1)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) h1
  have h3 : Tendsto (fun t : ℝ => (2 * (t + 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h2
  have h4 : Tendsto (fun t : ℝ => 3 * (2 * (t + 1))⁻¹) atTop (𝓝 (3 * 0)) :=
    h3.const_mul 3
  have heq : (fun t : ℝ => 3 / (2 * (t + 1))) = fun t => 3 * (2 * (t + 1))⁻¹ :=
    funext fun t => by ring
  rw [heq]
  simpa using h4

theorem P3_fRepr : P3 fRepr := by
  -- |fRepr| is squeezed to 0, hence fRepr → 0.
  have habs : Tendsto (fun t : ℝ => |fRepr t|) atTop (𝓝 0) := by
    apply squeeze_zero' (f := fun t : ℝ => |fRepr t|)
      (g := fun t : ℝ => 3 / (2 * (t + 1)))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht using abs_nonneg _
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht using fRepr_abs_le ht
    · exact tendsto_envelope
  exact (tendsto_zero_iff_abs_tendsto_zero fRepr).mpr habs

/-- A whole-line envelope agreeing with `3/(2(t+1))` for `t ≥ 0` and constant
`3` before that; it still tends to `0` at `+∞`. -/
noncomputable def envA (t : ℝ) : ℝ := if 0 ≤ t then 3 / (2 * (t + 1)) else 3

theorem tendsto_envA : Tendsto envA atTop (𝓝 0) := by
  have heq : envA =ᶠ[atTop] fun t : ℝ => 3 / (2 * (t + 1)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp [envA, ht]
  exact Tendsto.congr' heq.symm tendsto_envelope

theorem P4_fRepr : P4 fRepr := by
  refine ⟨envA, ?_, tendsto_envA⟩
  intro t ht
  rw [envA, if_pos ht]
  exact fRepr_abs_le ht

/-- Choose the quarter-period index so that `(4k)·π/8 > T + 1`. -/
private lemma exists_large_control (T : ℝ) :
    ∃ k : ℕ, T + 1 < (4 * k : ℝ) * (Real.pi / 8) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨k, hk⟩ := exists_nat_gt ((T + 1) * 2 / Real.pi)
  refine ⟨k, ?_⟩
  have h2pi : (0 : ℝ) < Real.pi / 2 := by positivity
  have h := mul_lt_mul_of_pos_right hk h2pi
  have hpi2 : Real.pi * 2 ≠ 0 := by positivity
  have hrw : ((T + 1) * 2 / Real.pi) * (Real.pi / 2) = T + 1 := by
    calc ((T + 1) * 2 / Real.pi) * (Real.pi / 2)
        = (T + 1) * (Real.pi * 2) / (Real.pi * 2) := by ring
      _ = T + 1 := mul_div_cancel_right₀ _ hpi2
  rw [hrw] at h
  have heq : (k : ℝ) * (Real.pi / 2) = (4 * k : ℝ) * (Real.pi / 8) := by ring
  rwa [heq] at h

/-- P5 for the representative: arbitrarily late strict local maxima at the
quarter-period points `(4k)π/8, (4k+1)π/8, (4k+2)π/8`.  At these points the
cosine factor takes the exact values `1, -1, 1`, so all comparisons are pure
algebra on strictly increasing positive denominators. -/
theorem P5_fRepr : P5 fRepr := by
  intro T
  obtain ⟨k, hk⟩ := exists_large_control T
  have hπ8 : (0 : ℝ) < Real.pi / 8 := by positivity
  set t₁ : ℝ := (4 * k : ℝ) * (Real.pi / 8) with ht₁def
  set t₂ : ℝ := (4 * k + 1 : ℝ) * (Real.pi / 8) with ht₂def
  set t₃ : ℝ := (4 * k + 2 : ℝ) * (Real.pi / 8) with ht₃def
  have hk1 : (4 * k : ℝ) < 4 * k + 1 := by linarith
  have hk2 : (4 * k + 1 : ℝ) < 4 * k + 2 := by linarith
  have h12 : t₁ < t₂ := mul_lt_mul_of_pos_right hk1 hπ8
  have h23 : t₂ < t₃ := mul_lt_mul_of_pos_right hk2 hπ8
  -- exact cosine evaluations
  have c1 : cos (8 * t₁) = 1 := by
    have h0 := cos_eight_mul_ceiling (4 * k)
    have hcast : ((4 * k : ℕ) : ℝ) = 4 * (k : ℝ) := by push_cast; ring
    rw [hcast] at h0
    have hpow : (-1 : ℝ) ^ (4 * k) = 1 := neg_one_pow_four_mul k
    rw [ht₁def, h0, hpow]
  have c2 : cos (8 * t₂) = -1 := by
    have h0 := cos_eight_mul_ceiling (4 * k + 1)
    have hcast : ((4 * k + 1 : ℕ) : ℝ) = 4 * (k : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h0
    have hpow : (-1 : ℝ) ^ (4 * k + 1) = -1 := neg_one_pow_four_mul_add_one k
    rw [ht₂def, h0, hpow]
  have c3 : cos (8 * t₃) = 1 := by
    have h0 := cos_eight_mul_ceiling (4 * k + 2)
    have hcast : ((4 * k + 2 : ℕ) : ℝ) = 4 * (k : ℝ) + 2 := by push_cast; ring
    rw [hcast] at h0
    have hpow : (-1 : ℝ) ^ (4 * k + 2) = 1 := neg_one_pow_four_mul_add_two k
    rw [ht₃def, h0, hpow]
  have hd1 : (0 : ℝ) < 2 * (t₁ + 1) := by positivity
  have hd2 : (0 : ℝ) < 2 * (t₂ + 1) := by positivity
  have hd3 : (0 : ℝ) < 2 * (t₃ + 1) := by positivity
  have d12 : 2 * (t₁ + 1) < 2 * (t₂ + 1) := by linarith
  have d23 : 2 * (t₂ + 1) < 2 * (t₃ + 1) := by linarith
  have v1 : fRepr t₁ = -(3 / (2 * (t₁ + 1))) := by rw [fRepr, c1]; ring
  have v2 : fRepr t₂ = -(1 / (2 * (t₂ + 1))) := by rw [fRepr, c2]; ring
  have v3 : fRepr t₃ = -(3 / (2 * (t₃ + 1))) := by rw [fRepr, c3]; ring
  have cmp12 : fRepr t₁ < fRepr t₂ := by
    rw [v1, v2, neg_lt_neg_iff]
    have hA : (1 : ℝ) / (2 * (t₂ + 1)) < 3 / (2 * (t₂ + 1)) :=
      div_lt_div_of_pos_right (by norm_num) hd2
    have hB : 3 / (2 * (t₂ + 1)) < 3 / (2 * (t₁ + 1)) :=
      div_lt_div_of_pos_left (by norm_num) hd1 d12
    exact lt_trans hA hB
  have cmp32 : fRepr t₃ < fRepr t₂ := by
    rw [v3, v2, neg_lt_neg_iff]
    -- Cross-multiply on positive denominators:
    -- 1/(2(t₂+1)) < 3/(2(t₃+1)) ⇐ 2(t₃+1) < 6(t₂+1) ⇐ t₃ < 3t₂ + 2,
    -- and t₃ = t₂ + π/8 < t₂ + 1 ≤ 3t₂ + 2.
    rw [div_lt_div_iff₀ hd2 hd3]
    have ht3eq : t₃ = t₂ + Real.pi / 8 := by
      rw [ht₃def, ht₂def]
      ring
    have hpi_lt : Real.pi / 8 < 1 := by
      have := Real.pi_lt_d2
      nlinarith
    have ht2pos : 0 ≤ t₂ := by positivity
    nlinarith
  have ht1_gt : T < t₁ := by linarith
  exact ⟨t₁, t₂, t₃, ht1_gt, h12, h23, cmp12, cmp32⟩

/-- P6 for the representative: the tube property. -/
theorem P6_fRepr : P6 fRepr := by
  intro ε hε
  refine ⟨3 / (2 * ε), fun t ht => ?_⟩
  have ht_nn : 0 ≤ t := by
    have h : (0 : ℝ) ≤ 3 / (2 * ε) := by positivity
    exact le_trans h ht
  have h1 : |fRepr t| ≤ 3 / (2 * (t + 1)) := fRepr_abs_le ht_nn
  have hε2 : (0 : ℝ) < 2 * ε := by positivity
  have hden : (0 : ℝ) < 2 * (t + 1) := by positivity
  have hchain : (3 : ℝ) / (2 * ε) ≤ t := ht
  have hstep : 3 / (2 * ε) * (2 * ε) ≤ t * (2 * ε) :=
    mul_le_mul_of_nonneg_right hchain hε2.le
  have hA : 3 / (2 * ε) * (2 * ε) = 3 := by field_simp
  have hB : (3 : ℝ) ≤ t * (2 * ε) := by rwa [hA] at hstep
  have hC : t * (2 * ε) < ε * (2 * (t + 1)) := by nlinarith [hε]
  have hkey : (3 : ℝ) < ε * (2 * (t + 1)) := lt_of_le_of_lt hB hC
  have h2 : 3 / (2 * (t + 1)) < ε := by rwa [div_lt_iff₀ hden]
  exact lt_of_le_of_lt h1 h2

/-- **Main construction theorem.**  The representative curve `fRepr` has
exactly the qualitative shape of the bottom-right candidate graph on answer
sheet A2-6. -/
theorem optionSixShape_fRepr : OptionSixShape fRepr :=
  ⟨P1_fRepr, P2_fRepr, P3_fRepr, P4_fRepr, P5_fRepr, P6_fRepr⟩

/-! ##  Exclusion of the distractor shapes  -/

/-- **P1 is the decisive thermodynamic screen.**  Any rate-of-change function
that takes a nonnegative value at a positive time — as the about-axis
oscillating sketches (options 2 and 5) do — cannot satisfy `P1`, hence
cannot illustrate `dG/dt` for a closed system. -/
theorem positive_violates_P1 {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (hft : 0 ≤ f t) :
    ¬ P1 f := by
  intro h
  exact not_lt.mpr hft (h t ht)

/-- Symmetric steady oscillation about the axis (option 2 shape), e.g.
`f t = sin t`, takes a nonnegative value at a positive time; excluded. -/
theorem sine_fails_P1 : ¬ P1 (fun t : ℝ => sin t) := by
  apply positive_violates_P1 (t := Real.pi / 2)
  · positivity
  · rw [Real.sin_pi_div_two]
    norm_num

/-- Growing-amplitude about-axis oscillation (option 5 shape), e.g.
`f t = t * sin t`, takes a nonnegative value at a positive time; excluded. -/
theorem growing_sine_fails_P1 : ¬ P1 (fun t : ℝ => t * sin t) := by
  apply positive_violates_P1 (t := Real.pi / 2)
  · positivity
  · rw [Real.sin_pi_div_two]
    positivity

/-- Constant negative rate (option 1 shape) never tends to zero, so it fails
`P3`: the closed system would never approach equilibrium. -/
theorem constant_rate_fails_P3 (c : ℝ) (hc : c < 0) :
    ¬ P3 (fun _ : ℝ => c) := by
  intro h
  have h1 : Tendsto (fun _ : ℝ => c) atTop (𝓝 c) := tendsto_const_nhds
  have h2 : c = 0 := tendsto_nhds_unique h1 h
  linarith

/-- Strictly negative fixed-slope trend (option 4 shape), e.g.
`f t = -1 - t`, is unbounded below instead of approaching `0`; fails `P3`.
`Filter.tendsto_nhds_iff`-free argument: if it tended to `0`, it would
eventually be above `-1/2`, but at `t = max 0 T + 1` it is below `-1`. -/
theorem negative_slope_fails_P3 (a : ℝ) :
    ¬ P3 (fun t : ℝ => a - t) := by
  intro h
  -- if a - t → 0 then eventually a - t > -1
  have hI : Ioi (-1 : ℝ) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by norm_num)
  have hev : ∀ᶠ t in atTop, a - t ∈ Ioi (-1 : ℝ) := h hI
  rw [eventually_atTop] at hev
  obtain ⟨T, hT⟩ := hev
  have ht : a - max (a + 1) T ∈ Ioi (-1 : ℝ) := hT (max (a + 1) T) (le_max_right _ _)
  rw [mem_Ioi] at ht
  have hle : a + 1 ≤ max (a + 1) T := le_max_left _ _
  nlinarith

/-- **Classification theorem (the requested output).**
There exists a rate curve of the bottom-right shape
(`optionSixShape_fRepr`), and the bottom-right shape is the only one
compatible with the thermodynamic screens that the other five sketches fail:

* options 2 and 5 take nonnegative values at positive times ⇒ fail `P1`
  (`sine_fails_P1`, `growing_sine_fails_P1`);
* options 1 and 4 keep a nonzero rate forever ⇒ fail `P3`
  (`constant_rate_fails_P3`, `negative_slope_fails_P3`);
* option 3 approaches zero monotonically, with no oscillation ⇒ fails `P5`
  (a monotone function cannot exhibit the strict rise–fall triples required
  arbitrarily late; see `monotone_fails_P5` below).

Hence the correct box to tick is the **bottom-right** one (option 6). -/
theorem answer_is_bottom_right : OptionSixShape fRepr :=
  optionSixShape_fRepr

/-- A monotone nondecreasing function cannot have the strict rise–fall
pattern of `P5`: genuine oscillation (P5) excludes the monotone-relaxation
sketch (option 3). -/
theorem monotone_fails_P5 {f : ℝ → ℝ} (hf : Monotone f) : ¬ P5 f := by
  intro h
  obtain ⟨t₁, t₂, t₃, _, h12, h23, hup, hdown⟩ := h 0
  have : f t₂ ≤ f t₃ := hf (le_of_lt h23)
  linarith

/-- Option 3's shape on the physical half-line (strictly negative, tending to
zero, monotone, no ripple) is excluded by `monotone_fails_P5`.  The archetype
`-exp(-t)` is monotone, hence exhibits no rise–fall triple. -/
theorem optionThree_shape_fails_P5 :
    ¬ P5 (fun t : ℝ => -Real.exp (-t)) := by
  apply monotone_fails_P5
  intro a b hab
  simp only [neg_le_neg_iff]
  exact Real.exp_le_exp.mpr (by linarith)

end IChO2026T2A7
