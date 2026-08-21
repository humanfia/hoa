/-
Copyright (c) 2026 Archon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon autoformalization agent
-/

import Mathlib

/-!
# IPhO 2026 · Experimental Exam · Problem 4 · Part B.3

Source task: "Use the graph from question B2 to extrapolate and find the value of
H₀ (H at 0 °C)." The official answer is deliberately withheld, so instead of
asserting a numeric value, this file characterizes H₀ uniquely as the intercept
(value at the reference temperature T₀ = 273.15 K) of the straight line that
best fits, in the least-squares sense, the experimental B1/B2 measurements of
the water-column height H as a function of the absolute temperature T.

## Modeling notes
  * `B2` is the table of (T, H) pairs recorded in B1/B2 (number of points left abstract).
  * The problem statement says the H(T) curve "may be approximated as linear" around room
    temperature, so the extrapolation line is taken to be affine.
  * The Clausius–Clapeyron context of Part B is recorded as a reusable structure.
  * All determinations are answer-free: the Lean statements only say that a best-fit
    line exists and that H₀ is its value at T₀.
-/

open Finset

namespace IPhO2026_4_B_3

/-- Experimental context of part B of IPhO 2026 problem 4: an inner cylinder (IC)
contains dry air plus water vapor at total pressure `P_atm`; the water-column height
`H` is recorded as the absolute temperature `T` falls. The vapor pressure obeys the
Clausius–Clapeyron law
`P_v (T) = P_v0 * exp (-(Q_v / R) * (1 / T - 1 / T₀))`,
where `T₀ = 273.15 K` is the reference temperature (0 °C), `P_v0` the vapor pressure
at `T₀`, `R` the universal gas constant, and `Q_v` the molar latent heat of vaporization
of water. The constants `P_v0` and `Q_v` are left opaque: B.3 does not determine them. -/
structure ClausiusClapeyronContext where
  /-- Atmospheric (total) pressure in the inner cylinder. -/
  P_atm : ℝ
  /-- Universal gas constant `R` (J/(mol·K)). -/
  R_g : ℝ
  /-- Reference temperature `T₀ = 0 °C = 273.15 K`. -/
  T₀ : ℝ
  /-- Vapor pressure at `T₀`. -/
  P_v0 : ℝ
  /-- Molar latent heat of vaporization of water. -/
  Q_v : ℝ
  R_pos : 0 < R_g
  T₀_pos : 0 < T₀
  /-- Vapor pressure given by Clausius–Clapeyron as a function of absolute temperature. -/
  P_v : ℝ → ℝ
  P_v_eq : ∀ T : ℝ, 0 < T →
    P_v T = P_v0 * Real.exp (-(Q_v / R_g) * (1 / T - 1 / T₀))

/-- Extrapolation data for question B.3: the context together with the B1/B2
measurements, i.e. a finite list of `(T, H)` pairs recorded while the temperature
fell, and the condition (stated in the problem) that the H(T) curve may be
approximated by an affine law. The straight line used for the B3 extrapolation is
the best affine (least-squares) fit through these experimental points. -/
structure ExtrapolationData extends ClausiusClapeyronContext where
  /-- Number of recorded measurement points. -/
  n : ℕ
  /-- Absolute temperatures at which the height `H` was recorded (in kelvin). -/
  T_meas : Fin n → ℝ
  /-- Recorded water-column heights (in cm, as read on the IC scale). -/
  H_meas : Fin n → ℝ
  /-- Every measurement was taken at a positive absolute temperature. -/
  T_meas_pos : ∀ i : Fin n, 0 < T_meas i
  /-- There are at least two distinct measurement temperatures, so a unique
  best-fit affine line through the data exists. -/
  two_distinct : ∃ i j : Fin n, T_meas i ≠ T_meas j

namespace ExtrapolationData

variable (d : ExtrapolationData)

/-- The affine value at temperature `T` of a (slope, intercept) candidate line. -/
def lineValue (p : ℝ × ℝ) (T : ℝ) : ℝ :=
  p.1 * T + p.2

/-- Sum of squared vertical deviations between the affine candidate `p` and the
measured heights `H_meas` at the measured temperatures. -/
def sumSquaredResiduals (p : ℝ × ℝ) : ℝ :=
  ∑ i : Fin d.n, (lineValue p (d.T_meas i) - d.H_meas i) ^ 2

/-- Candidate `p` is a least-squares best affine fit of the B2 data iff no other
(slope, intercept) pair has strictly smaller squared residual. -/
def IsBestAffineFit (p : ℝ × ℝ) : Prop :=
  ∀ q : ℝ × ℝ, d.sumSquaredResiduals p ≤ d.sumSquaredResiduals q

/-- Two best-fit affine lines through the same two-distinct-temperature data agree at
every temperature (in particular at `T₀`). The proof, to be filled in later, uses the
orthogonal-projection characterization of least squares: the column space of the
design matrix `[T 1]` has a unique orthogonal complement, and minimizers of the squared
residual are unique on the affine span of the measured temperatures whenever at least
two distinct temperatures were recorded (hypothesis `two_distinct`). -/
theorem lineValue_eq_of_isBestAffineFit {p q : ℝ × ℝ}
    (hp : d.IsBestAffineFit p) (hq : d.IsBestAffineFit q) (T : ℝ) :
    lineValue p T = lineValue q T := by
  classical
  -- Reduce to a self-contained least-squares uniqueness statement over the data.
  have hn : 0 < d.n := by
    obtain ⟨i, j, hij⟩ := d.two_distinct
    by_contra h
    push Not at h
    have h0 : d.n = 0 := by omega
    rw [h0] at i j
    exact Fin.elim0 i
  have hnc : ¬ ∀ i j : Fin d.n, d.T_meas i = d.T_meas j := by
    obtain ⟨i, j, hij⟩ := d.two_distinct
    intro h
    exact hij (h i j)
  -- Work with pointwise residuals; both are minimizers.
  set S : ℝ × ℝ → ℝ := fun r => ∑ i : Fin d.n, (r.1 * d.T_meas i + r.2 - d.H_meas i) ^ 2
  have hSp : S p = ∑ i : Fin d.n, (p.1 * d.T_meas i + p.2 - d.H_meas i) ^ 2 := rfl
  have hSq : S q = ∑ i : Fin d.n, (q.1 * d.T_meas i + q.2 - d.H_meas i) ^ 2 := rfl
  have hpS : ∀ r : ℝ × ℝ, S p ≤ S r := fun r => by
    have := hp r
    simpa only [sumSquaredResiduals, lineValue] using this
  have hqS : ∀ r : ℝ × ℝ, S q ≤ S r := fun r => by
    have := hq r
    simpa only [sumSquaredResiduals, lineValue] using this
  have hSS : S p = S q := by
    have h1 : S p ≤ S q := hpS q
    have h2 : S q ≤ S p := hqS p
    linarith
  -- Suppose the value at T differs; build the midpoint and contradict minimality.
  by_contra hdiff
  set m : ℝ × ℝ := ((p.1 + q.1) / 2, (p.2 + q.2) / 2)
  set r1 : Fin d.n → ℝ := fun i => p.1 * d.T_meas i + p.2 - d.H_meas i
  set r2 : Fin d.n → ℝ := fun i => q.1 * d.T_meas i + q.2 - d.H_meas i
  have hmid : ∀ i : Fin d.n, m.1 * d.T_meas i + m.2 - d.H_meas i = (r1 i + r2 i) / 2 := by
    intro i; dsimp [m, r1, r2]; ring
  have hSm : S m = (S p + S q) / 2 - (∑ i : Fin d.n, (r1 i - r2 i) ^ 2) / 4 := by
    have h1 : ∀ i : Fin d.n, (m.1 * d.T_meas i + m.2 - d.H_meas i) ^ 2
        = (r1 i ^ 2 + r2 i ^ 2) / 2 - (r1 i - r2 i) ^ 2 / 4 := by
      intro i; rw [hmid i]; ring
    calc S m
        = ∑ i : Fin d.n, ((r1 i ^ 2 + r2 i ^ 2) / 2 - (r1 i - r2 i) ^ 2 / 4) :=
          Finset.sum_congr rfl (fun i _ => h1 i)
      _ = (∑ i : Fin d.n, (r1 i ^ 2 + r2 i ^ 2)) / 2
            - (∑ i : Fin d.n, (r1 i - r2 i) ^ 2) / 4 := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
      _ = (S p + S q) / 2 - (∑ i : Fin d.n, (r1 i - r2 i) ^ 2) / 4 := by
          rw [hSp, hSq, Finset.sum_add_distrib]
  have hDiffPos : 0 < ∑ i : Fin d.n, (r1 i - r2 i) ^ 2 := by
    obtain ⟨c, hc⟩ : ∃ c : Fin d.n, r1 c - r2 c ≠ 0 := by
      by_contra h
      push Not at h
      apply hdiff
      have hd : ∀ i : Fin d.n, (p.1 - q.1) * d.T_meas i + (p.2 - q.2) = 0 := by
        intro i; have := h i; dsimp [r1, r2] at this; linarith
      have hbs : p.1 = q.1 := by
        obtain ⟨a, b, hab⟩ : ∃ a b : Fin d.n, d.T_meas a ≠ d.T_meas b := by
          by_contra h'; push Not at h'; exact hnc h'
        have hTT : d.T_meas a - d.T_meas b ≠ 0 := sub_ne_zero.mpr hab
        have e1 := hd a
        have e2 := hd b
        have sub : (p.1 - q.1) * (d.T_meas a - d.T_meas b) = 0 := by linarith [e1, e2]
        rcases mul_eq_zero.mp sub with h1 | h1
        · linarith
        · exact absurd h1 hTT
      have hb2 : p.2 = q.2 := by
        have e1 := hd ⟨0, hn⟩
        rw [show p.1 - q.1 = 0 by linarith] at e1
        linarith [e1]
      have : p.1 * T + p.2 = q.1 * T + q.2 := by
        rw [show p.1 = q.1 from hbs, show p.2 = q.2 from hb2]
      exact this
    have hnn : ∀ i : Fin d.n, 0 ≤ (r1 i - r2 i) ^ 2 := fun i => sq_nonneg _
    have hcp : 0 < (r1 c - r2 c) ^ 2 := sq_pos_of_ne_zero hc
    exact Finset.sum_pos' (fun i _ => hnn i) ⟨c, Finset.mem_univ c, hcp⟩
  have hSm_lt : S m < S p := by
    rw [hSm, hSS]
    linarith [hDiffPos]
  exact absurd (hpS m) (not_le.mpr hSm_lt)

/-- Two best-fit affine lines through data recorded at at least two distinct
temperatures coincide as parameter pairs. -/
theorem isBestAffineFit_unique {p q : ℝ × ℝ}
    (hp : d.IsBestAffineFit p) (hq : d.IsBestAffineFit q) :
    p = q := by
  obtain ⟨a, b, hab⟩ := d.two_distinct
  have eu : ∀ T : ℝ, lineValue p T = lineValue q T :=
    fun T => d.lineValue_eq_of_isBestAffineFit hp hq T
  have hTT : d.T_meas a - d.T_meas b ≠ 0 := sub_ne_zero.mpr hab
  have e1 := eu (d.T_meas a)
  have e2 := eu (d.T_meas b)
  have h1 : p.1 = q.1 := by
    have sub : (p.1 - q.1) * (d.T_meas a - d.T_meas b) = 0 := by
      dsimp [lineValue] at e1 e2
      linarith [e1, e2]
    rcases mul_eq_zero.mp sub with h | h
    · linarith
    · exact absurd h hTT
  have h2 : p.2 = q.2 := by
    dsimp [lineValue] at e1
    rw [show p.1 = q.1 from h1] at e1
    linarith
  exact Prod.ext h1 h2

/-- A value `H₀ : ℝ` is a legitimate answer to question B.3 iff it is the value, at
the reference temperature `T₀ = 273.15 K` (0 °C), of the least-squares best affine
fit through the B2 measurement points.  This is exactly "extrapolate the B2 graph
to 0 °C". The constant is not written explicitly: any closed form is to be
constructed in the proof, not smuggled into the statement. -/
def ExtrapolatedHeightAtZero (H₀ : ℝ) : Prop :=
  ∃ p : ℝ × ℝ, d.IsBestAffineFit p ∧ lineValue p d.T₀ = H₀

/-! There exists a value of `H₀` (a real, in the dimensional role of a height) obtained
by extrapolating the best affine fit of the B2 graph to `T₀ = 273.15 K`. -/
theorem extrapolated_height_at_zero_exists :
    ∃ H₀ : ℝ, d.ExtrapolatedHeightAtZero H₀ := by
  classical
  obtain ⟨a0, b0, hab⟩ := d.two_distinct
  have hn : 0 < d.n := by
    by_contra h
    push Not at h
    have h0 : d.n = 0 := by omega
    rw [h0] at a0 b0
    exact Fin.elim0 a0
  have hn' : (d.n : ℝ) ≠ 0 := by
    have : (0:ℝ) < d.n := by exact_mod_cast hn
    positivity
  set ST : ℝ := ∑ i : Fin d.n, d.T_meas i
  set SH : ℝ := ∑ i : Fin d.n, d.H_meas i
  set A : ℝ := ∑ i : Fin d.n, d.T_meas i ^ 2
  set B : ℝ := ∑ i : Fin d.n, d.T_meas i * d.H_meas i
  -- positivity of Sxx = n·A − ST² (strict because two distinct temperatures)
  have hSxx : 0 < d.n * A - ST ^ 2 := by
    have hvar : ∑ i : Fin d.n, (d.T_meas i - ST / d.n) ^ 2 = A - ST ^ 2 / d.n := by
      have hh : ∀ i : Fin d.n, (d.T_meas i - ST / d.n) ^ 2
          = d.T_meas i ^ 2 - 2 * (ST / d.n) * d.T_meas i + (ST / d.n) ^ 2 := by
        intro i; ring
      calc ∑ i : Fin d.n, (d.T_meas i - ST / d.n) ^ 2
          = ∑ i : Fin d.n, (d.T_meas i ^ 2 - 2 * (ST / d.n) * d.T_meas i + (ST / d.n) ^ 2) :=
            Finset.sum_congr rfl (fun i _ => hh i)
        _ = A - 2 * (ST / d.n) * ST + (d.n : ℝ) * (ST / d.n) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            have h2 : ∑ i : Fin d.n, 2 * (ST / d.n) * d.T_meas i = 2 * (ST / d.n) * ST := by
              rw [← Finset.mul_sum]
            have h3 : ∑ i : Fin d.n, (ST / d.n) ^ 2 = (d.n : ℝ) * (ST / d.n) ^ 2 := by
              simp [Finset.sum_const, nsmul_eq_mul]
            rw [h2, h3]
        _ = A - ST ^ 2 / d.n := by field_simp; ring
    have hs : d.T_meas a0 - ST / d.n ≠ 0 ∨ d.T_meas b0 - ST / d.n ≠ 0 := by
      by_contra h
      push Not at h
      rcases h with ⟨h1, h2⟩
      have : d.T_meas a0 = d.T_meas b0 := by linarith
      exact hab this
    have hp : 0 < ∑ i : Fin d.n, (d.T_meas i - ST / d.n) ^ 2 := by
      rcases hs with h | h
      · have hc : 0 < (d.T_meas a0 - ST / d.n) ^ 2 := sq_pos_of_ne_zero h
        exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨a0, Finset.mem_univ a0, hc⟩
      · have hc : 0 < (d.T_meas b0 - ST / d.n) ^ 2 := sq_pos_of_ne_zero h
        exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨b0, Finset.mem_univ b0, hc⟩
    rw [hvar] at hp
    have hnpos : (0:ℝ) < (d.n : ℝ) := by exact_mod_cast hn
    have h2 : (d.n : ℝ) * (A - ST ^ 2 / d.n) = d.n * A - ST ^ 2 := by field_simp
    have h3 : 0 < (d.n : ℝ) * (A - ST ^ 2 / d.n) := by positivity
    linarith
  set Sxx : ℝ := d.n * A - ST ^ 2
  set Sxy : ℝ := d.n * B - ST * SH
  set a1 : ℝ := Sxy / Sxx
  set b1 : ℝ := (SH - a1 * ST) / d.n
  -- exhibit lineValue ⟨a1,b1⟩ at T₀ as the required H₀
  refine ⟨lineValue ⟨a1, b1⟩ d.T₀, ⟨⟨a1, b1⟩, ?_, rfl⟩⟩
  intro q
  -- S(q) expansion and S(b̂) expansion
  have hSS : ∀ r : ℝ × ℝ, d.sumSquaredResiduals r
      = (d.n : ℝ) * r.2 ^ 2 + 2 * r.2 * (r.1 * ST - SH) + (r.1 ^ 2 * A - 2 * r.1 * B)
        + ∑ i : Fin d.n, d.H_meas i ^ 2 := by
    intro r
    have hh : ∀ i : Fin d.n, (r.1 * d.T_meas i + r.2 - d.H_meas i) ^ 2
        = r.1 ^ 2 * d.T_meas i ^ 2 + 2 * (r.1 * r.2) * d.T_meas i - 2 * r.1 * (d.T_meas i * d.H_meas i)
          + r.2 ^ 2 - 2 * r.2 * d.H_meas i + d.H_meas i ^ 2 := by
      intro i; ring
    calc d.sumSquaredResiduals r
        = ∑ i : Fin d.n, (r.1 ^ 2 * d.T_meas i ^ 2 + 2 * (r.1 * r.2) * d.T_meas i
            - 2 * r.1 * (d.T_meas i * d.H_meas i) + r.2 ^ 2 - 2 * r.2 * d.H_meas i + d.H_meas i ^ 2) := by
          rw [sumSquaredResiduals, show (∑ i : Fin d.n, (lineValue r (d.T_meas i) - d.H_meas i) ^ 2)
            = ∑ i : Fin d.n, (r.1 ^ 2 * d.T_meas i ^ 2 + 2 * (r.1 * r.2) * d.T_meas i
              - 2 * r.1 * (d.T_meas i * d.H_meas i) + r.2 ^ 2 - 2 * r.2 * d.H_meas i
              + d.H_meas i ^ 2) from Finset.sum_congr rfl (fun i _ => by
                dsimp [lineValue]; rw [hh i])]
      _ = ∑ i : Fin d.n, (r.1 ^ 2 * d.T_meas i ^ 2) + ∑ i : Fin d.n, (2 * (r.1 * r.2) * d.T_meas i)
            - ∑ i : Fin d.n, (2 * r.1 * (d.T_meas i * d.H_meas i)) + ∑ i : Fin d.n, r.2 ^ 2
            - ∑ i : Fin d.n, (2 * r.2 * d.H_meas i) + ∑ i : Fin d.n, d.H_meas i ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (d.n : ℝ) * r.2 ^ 2 + 2 * r.2 * (r.1 * ST - SH) + (r.1 ^ 2 * A - 2 * r.1 * B)
            + ∑ i : Fin d.n, d.H_meas i ^ 2 := by
          have h1 : ∑ i : Fin d.n, r.1 ^ 2 * d.T_meas i ^ 2 = r.1 ^ 2 * A := by rw [← Finset.mul_sum]
          have h2 : ∑ i : Fin d.n, 2 * (r.1 * r.2) * d.T_meas i = 2 * (r.1 * r.2) * ST := by
            rw [← Finset.mul_sum]
          have h3 : ∑ i : Fin d.n, 2 * r.1 * (d.T_meas i * d.H_meas i) = 2 * r.1 * B := by
            rw [← Finset.mul_sum]
          have h4 : ∑ i : Fin d.n, r.2 ^ 2 = (d.n : ℝ) * r.2 ^ 2 := by
            simp [Finset.sum_const, nsmul_eq_mul]
          have h5 : ∑ i : Fin d.n, 2 * r.2 * d.H_meas i = 2 * r.2 * SH := by
            rw [← Finset.mul_sum]
          rw [h1, h2, h3, h4, h5]; ring
  rw [hSS q, hSS ⟨a1, b1⟩]
  -- Decompose S(q) - S(b̂) into a slope-squared and an intercept-squared excess.
  set SH2 : ℝ := ∑ i : Fin d.n, d.H_meas i ^ 2
  have hSxxpos : (0:ℝ) < Sxx := by simpa [Sxx] using hSxx
  have hSxx_ne : Sxx ≠ 0 := ne_of_gt hSxxpos
  have hdo : a1 * Sxx = Sxy := by
    have h1 : a1 = Sxy / Sxx := rfl
    rw [h1]
    field_simp [hSxx_ne]
  have hnpos : (0:ℝ) < (d.n : ℝ) := by exact_mod_cast hn
  have hb1n : (d.n : ℝ) * b1 = SH - a1 * ST := by
    have h1 : (d.n : ℝ) * b1 = (d.n : ℝ) * ((SH - a1 * ST) / d.n) := congrArg _ rfl
    rw [h1]
    field_simp [hn']

  -- The completing-the-square (Bessel) identity for the least-squares fit:
  -- (S(q) − S(b̂))·n = (q.1−a1)²·(n·A) + n²(q.2−b1)² + 2·n·ST·(q.2−b1)(q.1−a1),
  -- whose RHS is nonneg via Cauchy (0 < n·A, from two distinct temperatures).
  have hmaster : (((d.n : ℝ) * q.2 ^ 2 + 2 * q.2 * (q.1 * ST - SH) + (q.1 ^ 2 * A - 2 * q.1 * B) + SH2)
        - ((d.n : ℝ) * b1 ^ 2 + 2 * b1 * (a1 * ST - SH) + (a1 ^ 2 * A - 2 * a1 * B) + SH2))
      * (d.n : ℝ)
      = (q.1 - a1) ^ 2 * ((d.n : ℝ) * A) + (d.n : ℝ) ^ 2 * (q.2 - b1) ^ 2
        + 2 * (d.n : ℝ) * ST * (q.2 - b1) * (q.1 - a1) := by
    have hb1' : SH = (d.n : ℝ) * b1 + a1 * ST := by linarith
    have hB' : B = (((d.n : ℝ) * b1 + a1 * ST) * ST + a1 * ((d.n : ℝ) * A - ST ^ 2)) / (d.n : ℝ) := by
      have h1 : (d.n : ℝ) * B = ((d.n : ℝ) * b1 + a1 * ST) * ST + a1 * ((d.n : ℝ) * A - ST ^ 2) := by
        have h2 : a1 * Sxx = Sxy := hdo
        have hSxx' : Sxx = d.n * A - ST ^ 2 := rfl
        have hSxy' : Sxy = d.n * B - ST * SH := rfl
        rw [hSxx', hSxy'] at h2
        rw [hb1'] at h2
        linarith [h2]
      rw [← h1]
      field_simp [hn']
    rw [hb1', hB']
    field_simp [hn']
    ring
  -- conclude: S(q) ≥ S(b̂)
  have hApos : (0:ℝ) < d.n * A := by
    have h0 := hSxx
    have h1 : (0:ℝ) < d.n * A - ST ^ 2 := h0
    have h2 : 0 ≤ ST ^ 2 := sq_nonneg _
    linarith [h1, h2]
  have hqsneg : 0 ≤ (q.1 - a1) ^ 2 * ((d.n : ℝ) * A) + (d.n : ℝ) ^ 2 * (q.2 - b1) ^ 2
        + 2 * (d.n : ℝ) * ST * (q.2 - b1) * (q.1 - a1) := by
    -- PSD quadratic form [[nA, n·ST],[n·ST, n²]] : value = nA·(q1-a1+u)²·n⁻¹ + const
    nlinarith [sq_nonneg (q.1 - a1), sq_nonneg (q.2 - b1),
      sq_nonneg ((d.n : ℝ) * (q.2 - b1) + ST * (q.1 - a1)),
      hApos, hnpos, sq_nonneg ST, hSxx]
  -- multiply the closed-form difference by n: translate to n·(S(q)−S(b̂)) ≥ 0 then derive.
  have hprod : 0 ≤ (((d.n : ℝ) * q.2 ^ 2 + 2 * q.2 * (q.1 * ST - SH) + (q.1 ^ 2 * A - 2 * q.1 * B) + SH2)
        - ((d.n : ℝ) * b1 ^ 2 + 2 * b1 * (a1 * ST - SH) + (a1 ^ 2 * A - 2 * a1 * B) + SH2))
        * (d.n : ℝ) := by
    rw [hmaster]; exact hqsneg
  have hdiff : 0 ≤ ((d.n : ℝ) * q.2 ^ 2 + 2 * q.2 * (q.1 * ST - SH) + (q.1 ^ 2 * A - 2 * q.1 * B) + SH2)
        - ((d.n : ℝ) * b1 ^ 2 + 2 * b1 * (a1 * ST - SH) + (a1 ^ 2 * A - 2 * a1 * B) + SH2) := by
    have hnn : (0:ℝ) < (d.n : ℝ) := hnpos
    exact (mul_nonneg_iff_of_pos_right hnn).mp hprod
  -- goal was rewritten by hSS into the expanded form; close it directly
  dsimp [SH2] at hdiff ⊢
  linarith [hdiff]

/-! The extrapolated height `H₀` at 0 °C determined from the B2 graph is unique:
two values both read off the best-fit line at `T₀` must agree. -/
theorem extrapolated_height_at_zero_unique (H₀ H₁ : ℝ)
    (h₀ : d.ExtrapolatedHeightAtZero H₀) (h₁ : d.ExtrapolatedHeightAtZero H₁) :
    H₀ = H₁ := by
  obtain ⟨p, hp, rfl⟩ := h₀
  obtain ⟨q, hq, rfl⟩ := h₁
  exact d.lineValue_eq_of_isBestAffineFit hp hq d.T₀

/-- Answer-free characterization of the value requested by question B.3: there is a
unique `H₀` that is the extrapolated height at 0 °C from the B2 graph.  The concrete
witness (a best-fit line through the measured points) is constructed in the (later)
proof of existence; no numerical value or closed form appears in the statement. -/
theorem extrapolated_height_at_zero_existsUnique :
    ∃! H₀ : ℝ, d.ExtrapolatedHeightAtZero H₀ := by
  obtain ⟨H₀, hH₀⟩ := d.extrapolated_height_at_zero_exists
  exact ⟨H₀, hH₀, fun H₁ hH₁ => d.extrapolated_height_at_zero_unique H₁ H₀ hH₁ hH₀⟩

end ExtrapolationData

end IPhO2026_4_B_3
