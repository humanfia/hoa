import IChO2026Chem
import Mathlib

/-!
# IChO 2026 — Theory 8, subquestion A10 (Q8.10)

**Problem statement (source: theory_problem.pdf, p. 76 / Q8-5; image T8_page-5.png).**

Reductive quenching of the singlet (S1) and triplet (T1) excited states of a
photosensitiser PS by reductant Red:

- PS(S1) + Red → PS•− + Red•+    k_S = 2.7 × 10⁹ M⁻¹ s⁻¹
- PS(T1) + Red → PS•− + Red•+    k_T = 1.5 × 10⁸ M⁻¹ s⁻¹

with emission lifetimes in the absence of quencher
τ₀(S1) = 2.9 ns and τ₀(T1) = 84 µs.

> **8.10.** How do the emission lifetimes of the S1 and T1 states change
> when [Red] increases? Tick the correct box.
> a) increases   b) decreases   c) doesn't change

**Answer: b) decreases — for both states.**

## Model (Stern–Volmer lifetime form)

With quencher present, the total first-order deactivation rate of the excited
state is `1/τ₀ + k_q·[Red]`, so the observed emission lifetime is

  `τ([Red]) = 1 / (1/τ₀ + k_q·[Red]) = τ₀ / (1 + k_q·τ₀·[Red])`,

the same quenching model used in Q8.9
(`η_q = 1 − τ/τ₀ = k_q τ₀ [Red] / (1 + k_q τ₀ [Red])`), grounded by the rate
constants and τ₀ values printed in the problem (Stern–Volmer quenching being a
standard general photophysical law).

## What is proved here

* `sternVolmerLifetime_strictAntiOn` — the general function
  `c ↦ τ₀ / (1 + K · c)` is strictly antitone on `[0, ∞)` whenever `τ₀ > 0`
  and `K > 0`.
* `emissionLifetime_eq_sternVolmer` — the two equivalent forms of the lifetime
  agree under the stated positivity hypotheses.
* `tauS1_strictAntiOn`, `tauT1_strictAntiOn` — the S1 and T1 lifetimes built
  from the printed constants `k_S, k_T, τ₀(S1), τ₀(T1)` are instances with
  `K_S = k_S·τ₀(S1) = 7.83 M⁻¹ > 0` and `K_T = k_T·τ₀(T1) = 1.26 × 10⁴ M⁻¹ > 0`.
* `lifetime_s1`, `lifetime_t1`, `answer_T8_A10` — the requested
  classifications: both equal `LifetimeTrend.decreases` (box b).

Everything is proved from the problem-printed constants (recorded as `def`s
below, tagged as *given inputs*) plus Mathlib; no `sorry`, no custom axioms.
-/

namespace IChO2026Problems

open Set

/-! ## Tick-box options -/

/-- The three mutually exclusive options offered in Q8.10. -/
inductive LifetimeTrend
  | increases        -- ^ option a
  | decreases        -- ^ option b
  | doesNotChange    -- ^ option c
  deriving DecidableEq, Repr

/-! ## Problem-printed constants (given inputs) -/

/-- Quenching rate constant for S1, printed: `k_S = 2.7 × 10⁹ M⁻¹ s⁻¹`. -/
noncomputable def kS : ℝ := 2.7e9
/-- Quenching rate constant for T1, printed: `k_T = 1.5 × 10⁸ M⁻¹ s⁻¹`. -/
noncomputable def kT : ℝ := 1.5e8
/-- Intrinsic S1 lifetime, printed: `τ₀(S1) = 2.9 ns = 2.9 × 10⁻⁹ s`. -/
noncomputable def tau0S1 : ℝ := 2.9e-9
/-- Intrinsic T1 lifetime, printed: `τ₀(T1) = 84 µs = 84 × 10⁻⁶ s`. -/
noncomputable def tau0T1 : ℝ := 84e-6

lemma kS_pos : 0 < kS := by norm_num [kS]
lemma kT_pos : 0 < kT := by norm_num [kT]
lemma tau0S1_pos : 0 < tau0S1 := by norm_num [tau0S1]
lemma tau0T1_pos : 0 < tau0T1 := by norm_num [tau0T1]

/-- The Stern–Volmer constants formed from the printed data:
`K_S = k_S·τ₀(S1)` and `K_T = k_T·τ₀(T1)`. -/
noncomputable def KS : ℝ := kS * tau0S1
noncomputable def KT : ℝ := kT * tau0T1

/-- Numerical value check: `K_S = 7.83 M⁻¹`. -/
theorem KS_val : KS = 7.83 := by norm_num [KS, kS, tau0S1]

/-- Numerical value check: `K_T = 1.26 × 10⁴ M⁻¹`. -/
theorem KT_val : KT = 12600 := by norm_num [KT, kT, tau0T1]

lemma KS_pos : 0 < KS := mul_pos kS_pos tau0S1_pos
lemma KT_pos : 0 < KT := mul_pos kT_pos tau0T1_pos

/-! ## Stern–Volmer lifetime model -/

/-- Observed emission lifetime of an excited state with intrinsic lifetime `τ₀`
and bimolecular quenching constant `kq` at quencher concentration `q`:
`τ(q) = 1 / (1/τ₀ + kq·q)`. -/
noncomputable def emissionLifetime (τ₀ kq q : ℝ) : ℝ := 1 / (τ₀⁻¹ + kq * q)

/-- Equivalent Stern–Volmer form `τ₀ / (1 + K·q)` with `K = kq·τ₀`. -/
noncomputable def sternVolmerLifetime (τ₀ K q : ℝ) : ℝ := τ₀ / (1 + K * q)

/-- The two forms of the lifetime agree whenever `τ₀ > 0` and the total decay
rate is nonzero. -/
theorem emissionLifetime_eq_sternVolmer {τ₀ kq q : ℝ} (hτ : 0 < τ₀)
    (hden : τ₀⁻¹ + kq * q ≠ 0) :
    emissionLifetime τ₀ kq q = sternVolmerLifetime τ₀ (kq * τ₀) q := by
  have hτ0 : τ₀ ≠ 0 := ne_of_gt hτ
  have hfactor : (1 : ℝ) + (kq * τ₀) * q = τ₀ * (τ₀⁻¹ + kq * q) := by
    field_simp
  have h1 : (1 : ℝ) + (kq * τ₀) * q ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero hτ0 hden
  unfold emissionLifetime sternVolmerLifetime
  field_simp

/-- The total decay rate `1/τ₀ + kq·q` is positive for `τ₀ > 0`, `kq > 0`,
`q ≥ 0`, so the lifetime is well-defined on the physically relevant domain. -/
theorem decayRate_pos {τ₀ kq q : ℝ} (hτ : 0 < τ₀) (hk : 0 < kq) (hq : 0 ≤ q) :
    0 < τ₀⁻¹ + kq * q :=
  add_pos_of_pos_of_nonneg (inv_pos.mpr hτ) (mul_nonneg hk.le hq)

/-- **Core result.** For `τ₀ > 0` and `K > 0`, the Stern–Volmer lifetime
`q ↦ τ₀ / (1 + K·q)` is strictly antitone on `[0, ∞)`: increasing the quencher
concentration strictly decreases the observed emission lifetime. -/
theorem sternVolmerLifetime_strictAntiOn {τ₀ K : ℝ} (hτ : 0 < τ₀) (hK : 0 < K) :
    StrictAntiOn (sternVolmerLifetime τ₀ K) (Ici 0) := by
  intro a ha b hb hab
  rw [mem_Ici] at ha hb
  have h1a : (0:ℝ) < 1 + K * a :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hK.le ha)
  have h1b : (0:ℝ) < 1 + K * b :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hK.le hb)
  have hden : (0:ℝ) < (1 + K * b) * (1 + K * a) := mul_pos h1b h1a
  -- cross-multiplied comparison of the two fractions
  have hcross : τ₀ * (1 + K * a) < τ₀ * (1 + K * b) := by
    have hstep : K * a + 1 < K * b + 1 :=
      add_lt_add_left (mul_lt_mul_of_pos_left hab hK) 1
    rw [add_comm (K * a) 1, add_comm (K * b) 1] at hstep
    exact mul_lt_mul_of_pos_left hstep hτ
  unfold sternVolmerLifetime
  -- `x/d₂ < x/d₁ ↔ x*(d₁*d₂)/d₂ < x*(d₁*d₂)/d₁` for positive denominators;
  -- cancelling gives exactly `hcross`.
  rw [div_lt_div_iff₀ h1b h1a]
  -- goal: τ₀ * (1 + K * a) < τ₀ * (1 + K * b)
  exact hcross

/-- **S1 answer.** With the printed constants, the S1 emission lifetime
`τ(S1)([Red]) = τ₀(S1) / (1 + K_S·[Red])` strictly decreases on `[0, ∞)`. -/
theorem tauS1_strictAntiOn :
    StrictAntiOn (sternVolmerLifetime tau0S1 KS) (Ici 0) :=
  sternVolmerLifetime_strictAntiOn tau0S1_pos KS_pos

/-- **T1 answer.** With the printed constants, the T1 emission lifetime
`τ(T1)([Red]) = τ₀(T1) / (1 + K_T·[Red])` strictly decreases on `[0, ∞)`. -/
theorem tauT1_strictAntiOn :
    StrictAntiOn (sternVolmerLifetime tau0T1 KT) (Ici 0) :=
  sternVolmerLifetime_strictAntiOn tau0T1_pos KT_pos

/-! ## Classification requested by the problem -/

/-- A lifetime function strictly decreases with quencher concentration:
predicate form of tick-box option **b**, on the physical domain `[0, ∞)`. -/
def LifetimeDecreases (τ : ℝ → ℝ) : Prop := StrictAntiOn τ (Ici 0)

/-- A lifetime function strictly increases with quencher concentration:
predicate form of tick-box option **a**, on the physical domain `[0, ∞)`. -/
def LifetimeIncreases (τ : ℝ → ℝ) : Prop := StrictMonoOn τ (Ici 0)

/-- Classification of a lifetime-as-function-of-concentration into the three
tick-box options: strict decrease on `[0, ∞)` (option **b**) is selected when
proved; then strict increase (option **a**); otherwise the constancy option
**c**.  Decidability of the `Prop`-valued guards is via
`Classical.propDecidable`; the final theorems consequently depend only on the
standard logical axioms `propext`, `Classical.choice`, `Quot.sound`. -/
noncomputable def classifyLifetimeTrend (τ : ℝ → ℝ) : LifetimeTrend :=
  @ite _ (LifetimeDecreases τ) (Classical.propDecidable _) LifetimeTrend.decreases
    (@ite _ (LifetimeIncreases τ) (Classical.propDecidable _)
      LifetimeTrend.increases LifetimeTrend.doesNotChange)

/-- The strict-decrease and strict-increase cases are mutually exclusive on
the physical domain `[0, ∞)` (it contains the two distinct points 0 and 1):
a function strictly antitone there is not strictly monotone there. -/
theorem not_lifetimeIncreases_of_lifetimeDecreases {τ : ℝ → ℝ}
    (h : LifetimeDecreases τ) : ¬ LifetimeIncreases τ := by
  intro hm
  have h0 : (0:ℝ) ∈ Ici 0 := mem_Ici.mpr le_rfl
  have h1 : (1:ℝ) ∈ Ici 0 := mem_Ici.mpr zero_le_one
  exact lt_asymm (h h0 h1 zero_lt_one) (hm h0 h1 zero_lt_one)

/-- **Requested output `lifetime_s1`:** the S1 emission lifetime *decreases*
as `[Red]` increases — box **b**. -/
theorem lifetime_s1 :
    classifyLifetimeTrend (sternVolmerLifetime tau0S1 KS)
      = LifetimeTrend.decreases := by
  unfold classifyLifetimeTrend
  exact if_pos tauS1_strictAntiOn

/-- **Requested output `lifetime_t1`:** the T1 emission lifetime *decreases*
as `[Red]` increases — box **b**. -/
theorem lifetime_t1 :
    classifyLifetimeTrend (sternVolmerLifetime tau0T1 KT)
      = LifetimeTrend.decreases := by
  unfold classifyLifetimeTrend
  exact if_pos tauT1_strictAntiOn

/-- **Combined final answer to Q8.10:** box **b) decreases** for both S1 and T1. -/
theorem answer_T8_A10 :
    classifyLifetimeTrend (sternVolmerLifetime tau0S1 KS) = LifetimeTrend.decreases ∧
    classifyLifetimeTrend (sternVolmerLifetime tau0T1 KT) = LifetimeTrend.decreases :=
  ⟨lifetime_s1, lifetime_t1⟩

/-- Alias with the target id, for the verification harness. -/
theorem icho_2026_t8_a10_answer :
    classifyLifetimeTrend (sternVolmerLifetime tau0S1 KS) = LifetimeTrend.decreases ∧
    classifyLifetimeTrend (sternVolmerLifetime tau0T1 KT) = LifetimeTrend.decreases :=
  answer_T8_A10

/-! Axiom audit (reported in verification.md). -/

#print axioms answer_T8_A10
#print axioms lifetime_s1
#print axioms lifetime_t1
#print axioms sternVolmerLifetime_strictAntiOn

end IChO2026Problems
