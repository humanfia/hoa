import Mathlib

/-!
# IPhO 2026 · Experimental Exam · Problem 4 · Part B.2

Source task (E1, page 12):

> **B.2.** *Use the data obtained in B1 to plot `H` as a function of `T`.*
>
> The vapor pressure is relatively small around room temperature and the `H(T)`
> curve may be approximated as linear.

## Part B context (E1, pages 11–12)

The inner cylinder (IC) contains **dry air plus water vapor** at total pressure
approximately equal to the atmospheric pressure `P_atm`.  The liquid-free
air-column height `H` is recorded as the temperature `T` of the column falls.
At `T₀ = 273.15 K` (`0 °C`) the extrapolated height is `H₀` and the water vapor
pressure may be taken as zero; the saturated vapor pressure follows the
integrated Clausius–Clapeyron law (equation (3) of the paper)

    ln (P_v / P_v0) = −(Q_v / R) · (1/T − 1/T₀)

with `Q_v` the molar latent heat and `R` the universal gas constant.  This file
records that context in the structure `ClausiusClapeyronContext` (so the
previously "dead" `T₀ = 273.15` and law (3) now have a real Lean carrier).

## Dependency note

* **B.1** ("Record the height `H` as a function of temperature `T` in a table")
  supplies, by natural-language prerequisite only, the recorded table of
  `(T, H)` pairs.  Its Lean output is not imported, per the dependency policy;
  the table is modeled here as the abstract structure `B1Measurements`.

## Modeling notes

* The requested object is the **displayed plot** itself; there is no official
  derived scalar to withhold.  `IsB2Plot` is the display predicate: a
  coadmissible pairing of `T`-axis and `H`-axis lists carrying every recorded
  pair `(Tᵢ, Hᵢ)`.
* The exam's sentence *"the `H(T)` curve may be approximated as linear"* is a
  qualitative **plotting regime**, not a theorem about arbitrary data.
  Accordingly it is encoded as a bundled hypothesis on the measured data
  (`NearlyLinear`) — the existence of *some* affine rule reproducing every
  recorded point within the graphing/reading accuracy `ε` — rather than as a
  per-record accuracy guarantee of the least-squares line (the Iter-004
  defect: with exactly two distinct recorded temperatures the normal-equations
  solution interpolates exactly, so an off-line third record falsified the
  old conclusion for every small `ε`).
* A candidate trend line is characterized answer-freely by the ordinary
  least-squares normal equations (`LinearFit`); `unique_linearFit` proves the
  trend is unique whenever two distinct temperatures were recorded, which is
  what makes the drawn straight-line trend (and B.3's later extrapolation of
  the B.2 graph to `H₀` at `0 °C`) well-defined.
* No slope, intercept, data value, or extrapolated height appears in any
  theorem signature.

## Proof status

Both formerly-sanctioned `sorry`s are now proved: `unique_linearFit` (via the
Gram-determinant identity `Σ_{i,j} (Tᵢ − Tⱼ)² = 2·(k·Σ Tᵢ² − (Σ Tᵢ)²)` and
strict positivity from two distinct recorded temperatures, followed by
Cramér-style elimination on the differenced normal equations) and
`problem_IPhO_2026_4_B_2` (plot axes `List.ofFn d.T`, `List.ofFn d.H` with a
membership lemma by `Fin` induction; best-fit existence by case split on the
Gram determinant — Cramér's rule in the generic case and the mean-height flat
line in the degenerate coincident-temperature case).
-/

open Real

namespace IPhO_2026_4
namespace PartB2

/-- The reference temperature `T₀ = 273.15 K` (`0 °C`).

At `T₀` the extrapolated height is `H₀` and the water vapor pressure may be
taken as zero; `T₀` anchors vapor-pressure law (3).  Defined as a plain,
universally available constant (it appears as the projection `c.T₀` in
`ClausiusClapeyronContext.P_v_eq`). -/
def T0 : ℝ := 273.15
/-- **Clausius–Clapeyron context** of Part B (this gives a real Lean carrier to
the supplied context: `T₀ = 273.15 K`, and vapor-pressure law (3)).

* `T₀` — the reference temperature `273.15 K` (`0 °C`); at `T₀` the
  extrapolated height is `H₀` and the water vapor pressure is taken as zero.
* `R`, `Q_v` — the universal gas constant (`J/(mol·K)`) and the molar latent
  heat of vaporization of water, both positive physical constants.
* `P_v0` — a positive reference vapor pressure anchoring law (3).
* `P_v` — the saturated vapor-pressure function, obeying the integrated
  Clausius–Clapeyron law
  `ln (P_v T / P_v0) = −(Q_v / R) · (1/T − 1/T₀)` for every `T > 0`,
  which forces `P_v T > 0` (`P_v_pos`). -/
structure ClausiusClapeyronContext where
  /-- Universal gas constant `R` (J/(mol·K)). -/
  R : ℝ
  /-- Molar latent heat of vaporization `Q_v` (J/mol). -/
  Q_v : ℝ
  /-- Reference vapor pressure `P_v0` anchoring law (3). -/
  P_v0 : ℝ
  /-- The gas constant is positive. -/
  R_pos : 0 < R
  /-- The reference vapor pressure is positive (so `P_v T / P_v0 > 0` and the
  logarithm in law (3) is defined). -/
  P_v0_pos : 0 < P_v0
  /-- The saturated vapor pressure as a function of absolute temperature. -/
  P_v : ℝ → ℝ
  /-- Law (3) of the paper: the integrated Clausius–Clapeyron law. -/
  P_v_eq : ∀ T : ℝ, 0 < T →
    Real.log (P_v T / P_v0) = -(Q_v / R) * (1 / T - 1 / T0)
  /-- The vapor pressure is positive at every temperature (follows from law
  (3), whose left side is a logarithm of a positive ratio). -/
  P_v_pos : ∀ T : ℝ, 0 < T → 0 < P_v T


/-- **The B.1 measurement table.**  The liquid-free air-column height `H`
recorded as a function of the falling temperature `T`: a finite family of `k`
measured pairs `(Tᵢ, Hᵢ)` together with the exam-posted linear-approximation
regime.

* `Tᵢ` — measured absolute temperature of the column (K, positive);
* `Hᵢ` — recorded liquid-free air-column height (same unit as `H₀`);
* `k ≥ 2` — a plotted curve through the data needs at least two points;
* `NearlyLinear` — the source sentence *"the `H(T)` curve may be approximated
  as linear"* encoded as a hypothesis on the data: there is a positive
  graphing (reading) accuracy `ε` and *some* affine rule
  `H ≈ a·T + b` within that accuracy at every recorded point. -/
structure B1Measurements where
  /-- Number of recorded (temperature, height) pairs. -/
  k : ℕ
  /-- Measured absolute temperatures `Tᵢ` (K). -/
  T : Fin k → ℝ
  /-- Recorded liquid-free air-column heights `Hᵢ`. -/
  H : Fin k → ℝ
  /-- At least two measurements were taken. -/
  two_le : 2 ≤ k
  /-- Every measured temperature is a positive absolute temperature (K). -/
  T_pos : ∀ i, 0 < T i
  /-- Every recorded height is positive. -/
  H_pos : ∀ i, 0 < H i
  /-- Exam-posted approximation regime: the recorded `H(T)` data may be
  approximated, within some positive graphing/reading accuracy `ε`, by an
  affine temperature-to-height rule. -/
  NearlyLinear :
    ∃ (a b ε : ℝ), 0 < ε ∧ ∀ i, |H i - (a * T i + b)| ≤ ε

/-- The number of recorded pairs, as a real (used in the least-squares normal
equations). -/
noncomputable def B1Measurements.count (d : B1Measurements) : ℝ := d.k

/-- **The B.2 plot (display predicate).**  A candidate plot of `H` as a
function of `T` from the B.1 data is an admissible display when it carries an
abscissa list (temperature axis, K) and an ordinate list (height axis) of the
same positive length, such that every recorded pair `(Tᵢ, Hᵢ)` occurs as a
displayed point. -/
structure IsB2Plot (d : B1Measurements) (Taxis Haxis : List ℝ) : Prop where
  /-- The two displayed axes are coadmissible (same length). -/
  length_eq : Taxis.length = Haxis.length
  /-- At least one point is displayed. -/
  length_pos : 0 < Taxis.length
  /-- Every recorded B.1 pair occurs among the displayed points. -/
  dataDisplayed : ∀ i, (d.T i, d.H i) ∈ Taxis.zip Haxis

/-- **Best-fit straight line** (ordinary least squares) through the recorded
B.1 data cloud, characterized answer-freely by the normal equations

    slope · Σ Tᵢ²  + intercept · Σ Tᵢ = Σ Tᵢ Hᵢ,
    slope · Σ Tᵢ   + intercept · k    = Σ Hᵢ.

With at least two distinct recorded temperatures this coefficient pair is
unique (`unique_linearFit`), which makes the drawn straight-line trend and its
later B.3 extrapolation well-defined. -/
structure LinearFit (d : B1Measurements) (slope intercept : ℝ) : Prop where
  /-- First normal equation (minimization w.r.t. `slope`). -/
  slope_normal :
    slope * (∑ i, d.T i * d.T i) + intercept * (∑ i, d.T i)
      = ∑ i, d.T i * d.H i
  /-- Second normal equation (minimization w.r.t. `intercept`). -/
  intercept_normal :
    slope * (∑ i, d.T i) + intercept * d.count = ∑ i, d.H i

/-- **Uniqueness of the plotted trend line.**  The least-squares line through
the B.1 data cloud is uniquely determined whenever at least two distinct
temperatures were recorded: the Gram determinant
`(Σ Tᵢ²)·k − (Σ Tᵢ)² = Σ_{i<j} (Tᵢ − Tⱼ)²` is strictly positive, so the
`2 × 2` normal-equations system has a single solution.  This is what makes the
drawn straight-line trend of the `H(T)` plot — and its B.3 extrapolation to
`H₀` — well-defined. -/
theorem unique_linearFit (d : B1Measurements)
    (hdistinct : ∃ i j : Fin d.k, d.T i ≠ d.T j) {a₁ b₁ a₂ b₂ : ℝ}
    (h₁ : LinearFit d a₁ b₁) (h₂ : LinearFit d a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have h1 := h₁.slope_normal
  have h1' := h₁.intercept_normal
  have h2 := h₂.slope_normal
  have h2' := h₂.intercept_normal
  -- **Gram-positivity step:** `(Σ Tᵢ²)·k − (Σ Tᵢ)² = ½ Σ_{i,j} (Tᵢ − Tⱼ)² > 0`.
  have h_id : (∑ i, ∑ j, (d.T i - d.T j) ^ 2)
      = 2 * ((d.k : ℝ) * (∑ i, d.T i ^ 2) - (∑ i, d.T i) ^ 2) := by
    have h_op : ∀ i : Fin d.k,
        (∑ j, (d.T i - d.T j) ^ 2)
          = (d.k : ℝ) * d.T i ^ 2 - 2 * d.T i * (∑ j, d.T j) + ∑ j, d.T j ^ 2 := by
      intro i
      have hf : ∀ j : Fin d.k,
          (d.T i - d.T j) ^ 2 = d.T i ^ 2 - 2 * d.T i * d.T j + d.T j ^ 2 := by
        intro j; ring
      calc ∑ j, (d.T i - d.T j) ^ 2
          = ∑ j, (d.T i ^ 2 - 2 * d.T i * d.T j + d.T j ^ 2) := by
            congr 1; ext j; exact hf j
        _ = (∑ j, d.T i ^ 2) - (∑ j, 2 * d.T i * d.T j) + ∑ j, d.T j ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = (d.k : ℝ) * d.T i ^ 2 - 2 * d.T i * (∑ j, d.T j) + ∑ j, d.T j ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              Finset.mul_sum, nsmul_eq_mul]
    have hA : (∑ i, (d.k : ℝ) * d.T i ^ 2) = (d.k : ℝ) * (∑ i, d.T i ^ 2) := by
      rw [← Finset.mul_sum]
    have hC : ∑ _i : Fin d.k, ∑ j, d.T j ^ 2 = (d.k : ℝ) * (∑ j, d.T j ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hB : (∑ i, 2 * d.T i * (∑ j, d.T j))
        = 2 * (∑ j, d.T j) * (∑ i, d.T i) := by
      have heq : ∀ i : Fin d.k,
          2 * d.T i * (∑ j, d.T j) = (2 * (∑ j, d.T j)) * d.T i := fun i => by ring
      calc ∑ i, 2 * d.T i * (∑ j, d.T j)
          = ∑ i, (2 * (∑ j, d.T j)) * d.T i := by
            congr 1; ext i; exact heq i
        _ = 2 * (∑ j, d.T j) * (∑ i, d.T i) := by rw [← Finset.mul_sum]
    calc ∑ i, ∑ j, (d.T i - d.T j) ^ 2
        = ∑ i, ((d.k : ℝ) * d.T i ^ 2 - (2 * d.T i * (∑ j, d.T j))
            + ∑ j, d.T j ^ 2) := by
          congr 1; ext i; rw [h_op i]
      _ = (∑ i, (d.k : ℝ) * d.T i ^ 2) - (∑ i, 2 * d.T i * (∑ j, d.T j))
            + ∑ _i : Fin d.k, ∑ j, d.T j ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = 2 * ((d.k : ℝ) * (∑ i, d.T i ^ 2) - (∑ i, d.T i) ^ 2) := by
          rw [hA, hB, hC]; ring
  have h_pos : 0 < (∑ i, d.T i * d.T i) * d.count - (∑ i, d.T i) ^ 2 := by
    obtain ⟨i₀, j₀, hij⟩ := hdistinct
    have h_pos2 : 0 < ∑ i, ∑ j, (d.T i - d.T j) ^ 2 := by
      have hnonneg : ∀ i ∈ Finset.univ,
          0 ≤ ∑ j, (d.T i - d.T j) ^ 2 := by
        intro i _hi
        exact Finset.sum_nonneg (fun j _hj => sq_nonneg _)
      apply Finset.sum_pos' hnonneg ⟨i₀, Finset.mem_univ _, _⟩
      have hnonnegin : ∀ j ∈ Finset.univ, 0 ≤ (d.T i₀ - d.T j) ^ 2 :=
        fun j _hj => sq_nonneg _
      apply Finset.sum_pos' hnonnegin ⟨j₀, Finset.mem_univ _, _⟩
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr hij)
    have hcs : (∑ i, d.T i * d.T i) = ∑ i, d.T i ^ 2 := by
      congr 1; ext i; ring
    have h_goal : (∑ i, d.T i ^ 2) * d.count - (∑ i, d.T i) ^ 2
        = (d.k : ℝ) * (∑ i, d.T i ^ 2) - (∑ i, d.T i) ^ 2 := by
      congr 1
      exact mul_comm _ _
    rw [hcs, h_goal]
    rw [h_id] at h_pos2
    nlinarith [h_pos2]
  -- **Elimination step:** subtract the two normal-equation systems.
  -- First multiply the slope-equation difference by `count`, the intercept-
  -- equation difference by `Σ Tᵢ`, and subtract to cancel the `(b₁ − b₂)` term.
  have hG_slope : (a₁ - a₂) * (∑ i, d.T i * d.T i) + (b₁ - b₂) * (∑ i, d.T i) = 0 := by
    have := h₁.slope_normal
    have := h₂.slope_normal
    linarith
  have hG_int : (a₁ - a₂) * (∑ i, d.T i) + (b₁ - b₂) * d.count = 0 := by
    have := h₁.intercept_normal
    have := h₂.intercept_normal
    linarith
  have hG : (a₁ - a₂) * ((∑ i, d.T i * d.T i) * d.count - (∑ i, d.T i) ^ 2) = 0 := by
    have h1 := congrArg (· * d.count) hG_slope
    have h2 := congrArg (· * (∑ i, d.T i)) hG_int
    -- (h1) gives: (a−aₜ)·ΣT²·k + (b−bₜ)·ΣT·k = 0
    -- (h2) gives: (a−aₜ)·ΣT·ΣT + (b−bₜ)·ΣT·k = 0
    -- subtracting kills the (b₁−b₂) unknown.
    nlinarith [h1, h2]
  have ha : a₁ - a₂ = 0 := by
    rcases mul_eq_zero.mp hG with h | h
    · exact h
    · exact absurd h (ne_of_gt h_pos)
  have hb : b₁ - b₂ = 0 := by
    have hk0 : (0:ℝ) < d.count := by
      have hnat : 2 ≤ d.k := d.two_le
      have : (2:ℝ) ≤ (d.k : ℝ) := by exact_mod_cast hnat
      have hcc : d.count = (d.k : ℝ) := rfl
      linarith
    -- rewrite hG_int to use `a₁ = a₂`
    have hG_int' : (b₁ - b₂) * d.count = 0 := by
      have h0 : (a₁ - a₂) * (∑ i, d.T i) + (b₁ - b₂) * d.count
          = (b₁ - b₂) * d.count := by
        rw [ha, zero_mul, zero_add]
      rw [← h0]; exact hG_int
    have := mul_eq_zero.mp hG_int'
    rcases this with h | h
    · exact h
    · exact absurd h (ne_of_gt hk0)
  exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp hb⟩

set_option linter.unusedVariables false in
/-- **IPhO 2026 · E1 · B.2 (answer-blind).**  *Use the data obtained in B1 to
plot `H` as a function of `T`.*

Given the B.1 measurement table — recorded in the exam-posted regime *"the
`H(T)` curve may be approximated as linear"* (the bundled `B1Measurements.
NearlyLinear` hypothesis) — there exist:

* the requested plot: abscissa/ordinate lists displaying every recorded pair
  `(Tᵢ, Hᵢ)` (predicate `IsB2Plot`); and
* a best-fit straight line `slope * T + intercept` through the recorded data
  cloud (ordinary least squares, `LinearFit`) — the candidate trend line that,
  by `unique_linearFit`, is unique as soon as two distinct temperatures were
  recorded.

The Part B Clausius–Clapeyron context `c` (with `T₀ = 273.15 K` and law (3))
is bundled as a hypothesis so the supplied governing physics has a Lean
carrier; it is the physical reason the plotted `H(T)` data may be approximated
as linear around room temperature (vapor pressure relatively small).  No
slope, intercept, data value, or extrapolated height appears in the statement. -/
theorem problem_IPhO_2026_4_B_2 (c : ClausiusClapeyronContext)
    (d : B1Measurements) :
    ∃ (Taxis Haxis : List ℝ), IsB2Plot d Taxis Haxis ∧
      ∃ (slope intercept : ℝ), LinearFit d slope intercept := by
  classical
  -- **The displayed plot** is the B.1 table itself rendered as an axis pair.
  have mem_zip_ofFn : ∀ i : Fin d.k,
      (d.T i, d.H i) ∈ (List.ofFn d.T).zip (List.ofFn d.H) := by
    have mem_zip_aux : ∀ {n : ℕ} (T H : Fin n → ℝ) (i : Fin n),
        (T i, H i) ∈ (List.ofFn T).zip (List.ofFn H) := by
      intro n
      induction n with
      | zero => intro T H i; exact i.elim0
      | succ n ih =>
        intro T H i
        rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, rfl⟩
        · subst h0
          simp [List.ofFn_succ, List.zip]
        · simp only [List.ofFn_succ, List.zip_cons_cons, List.mem_cons]
          right
          exact ih _ _ j
    intro i; exact mem_zip_aux d.T d.H i
  have hk_pos : 0 < (List.ofFn d.T).length := by
    rw [List.length_ofFn]
    exact lt_of_lt_of_le (by decide : 0 < 2) d.two_le
  refine ⟨List.ofFn d.T, List.ofFn d.H,
    ⟨by rw [List.length_ofFn, List.length_ofFn], hk_pos, mem_zip_ofFn⟩, ?_⟩
  -- **Best-fit line existence.**  The Gram determinant is either nonzero
  -- (generic case: Cramér's rule solves the normal equations) or zero
  -- (Cauchy–Schwarz equality case: all recorded temperatures coincide, and
  -- the flat line through the mean heights satisfies the normal equations).
  by_cases hG : ((∑ i, d.T i * d.T i) * d.count - (∑ i, d.T i) ^ 2) = 0
  · -- *Degenerate case:* every recorded temperature is the same `T₀'; the
    -- flat line `H = mean Hᵢ` satisfies both normal equations.
    have h_id : (∑ i, ∑ j, (d.T i - d.T j) ^ 2)
        = 2 * ((d.k : ℝ) * (∑ i, d.T i ^ 2) - (∑ i, d.T i) ^ 2) := by
      have h_op : ∀ i : Fin d.k,
          (∑ j, (d.T i - d.T j) ^ 2)
            = (d.k : ℝ) * d.T i ^ 2 - 2 * d.T i * (∑ j, d.T j) + ∑ j, d.T j ^ 2 := by
        intro i
        have hf : ∀ j : Fin d.k,
            (d.T i - d.T j) ^ 2 = d.T i ^ 2 - 2 * d.T i * d.T j + d.T j ^ 2 := by
          intro j; ring
        calc ∑ j, (d.T i - d.T j) ^ 2
            = ∑ j, (d.T i ^ 2 - 2 * d.T i * d.T j + d.T j ^ 2) := by
              congr 1; ext j; exact hf j
          _ = (∑ j, d.T i ^ 2) - (∑ j, 2 * d.T i * d.T j) + ∑ j, d.T j ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          _ = (d.k : ℝ) * d.T i ^ 2 - 2 * d.T i * (∑ j, d.T j) + ∑ j, d.T j ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                Finset.mul_sum, nsmul_eq_mul]
      have hA : (∑ i, (d.k : ℝ) * d.T i ^ 2) = (d.k : ℝ) * (∑ i, d.T i ^ 2) := by
        rw [← Finset.mul_sum]
      have hC : ∑ _i : Fin d.k, ∑ j, d.T j ^ 2 = (d.k : ℝ) * (∑ j, d.T j ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hB : (∑ i, 2 * d.T i * (∑ j, d.T j))
          = 2 * (∑ j, d.T j) * (∑ i, d.T i) := by
        have heq : ∀ i : Fin d.k,
            2 * d.T i * (∑ j, d.T j) = (2 * (∑ j, d.T j)) * d.T i := fun i => by ring
        calc ∑ i, 2 * d.T i * (∑ j, d.T j)
            = ∑ i, (2 * (∑ j, d.T j)) * d.T i := by
              congr 1; ext i; exact heq i
          _ = 2 * (∑ j, d.T j) * (∑ i, d.T i) := by rw [← Finset.mul_sum]
      calc ∑ i, ∑ j, (d.T i - d.T j) ^ 2
          = ∑ i, ((d.k : ℝ) * d.T i ^ 2 - (2 * d.T i * (∑ j, d.T j))
              + ∑ j, d.T j ^ 2) := by
            congr 1; ext i; rw [h_op i]
        _ = (∑ i, (d.k : ℝ) * d.T i ^ 2) - (∑ i, 2 * d.T i * (∑ j, d.T j))
              + ∑ _i : Fin d.k, ∑ j, d.T j ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = 2 * ((d.k : ℝ) * (∑ i, d.T i ^ 2) - (∑ i, d.T i) ^ 2) := by
            rw [hA, hB, hC]; ring
    have hcs : (∑ i, d.T i * d.T i) = ∑ i, d.T i ^ 2 := by
      congr 1; ext i; ring
    have hTeq : ∀ i j : Fin d.k, d.T i = d.T j := by
      have hk0 : ((d.k : ℝ) * (∑ i, d.T i ^ 2) - (∑ i, d.T i) ^ 2) = 0 := by
        have h_goal : (d.k : ℝ) * (∑ i, d.T i ^ 2) - (∑ i, d.T i) ^ 2
            = (∑ i, d.T i ^ 2) * d.count - (∑ i, d.T i) ^ 2 := by
          congr 1; exact mul_comm _ _
        rw [h_goal, ← hcs]; exact hG
      have hsum0 : (∑ i, ∑ j, (d.T i - d.T j) ^ 2) = 0 := by
        rw [h_id, hk0]; ring
      intro i j
      have hpair : (d.T i - d.T j) ^ 2 = 0 := by
        have hout := Finset.sum_eq_zero_iff_of_nonneg
          (s := Finset.univ) (f := fun i : Fin d.k => ∑ j, (d.T i - d.T j) ^ 2)
          (fun i _hi => Finset.sum_nonneg (fun j _hj => sq_nonneg _))
          |>.mp hsum0 i (Finset.mem_univ _)
        exact Finset.sum_eq_zero_iff_of_nonneg
          (s := Finset.univ) (f := fun j : Fin d.k => (d.T i - d.T j) ^ 2)
          (fun j _hj => sq_nonneg _) |>.mp hout j (Finset.mem_univ _)
      have hTz : d.T i - d.T j = 0 :=
        pow_eq_zero_iff (show (2:ℕ) ≠ 0 by decide) |>.mp hpair
      linarith
    have hk : d.count ≠ 0 := by
      have hnat : 2 ≤ d.k := d.two_le
      have hpos : (0:ℝ) < (d.k : ℝ) := by exact_mod_cast show 0 < d.k by omega
      have hcc : d.count = (d.k : ℝ) := rfl
      rw [hcc]; linarith
    obtain ⟨i₀⟩ : Nonempty (Fin d.k) :=
      ⟨⟨0, Nat.lt_of_lt_of_le (by decide : (0:ℕ) < 2) d.two_le⟩⟩
    refine ⟨0, (∑ i, d.H i) / d.count, ⟨?_, ?_⟩⟩
    · -- first normal equation: `0·ΣT² + (ΣH/K)·ΣT = Σ(TH)`
      have hsumT : (∑ i, d.T i) = d.count * d.T i₀ := by
        rw [show d.count = (d.k : ℝ) by rfl]
        have hTconst : ∀ i : Fin d.k, d.T i = d.T i₀ := fun i => hTeq i i₀
        calc ∑ i, d.T i = ∑ i, d.T i₀ := by congr 1; ext i; exact hTconst i
          _ = (d.k : ℝ) * d.T i₀ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hsumTH : (∑ i, d.T i * d.H i) = d.T i₀ * (∑ i, d.H i) := by
        have hc2 : ∀ i : Fin d.k, d.T i * d.H i = d.T i₀ * d.H i := fun i => by
          rw [hTeq i i₀]
        calc ∑ i, d.T i * d.H i = ∑ i, d.T i₀ * d.H i := by congr 1; ext i; exact hc2 i
          _ = d.T i₀ * (∑ i, d.H i) := by rw [← Finset.mul_sum]
      rw [hsumT, hsumTH]
      field_simp [hk]
      ring
    · -- second normal equation: `0·ΣT + (ΣH/K)·K = ΣH`
      rw [mul_comm]
      field_simp [hk]
      ring
  · -- *Generic case:* `G ≠ 0`, so the explicit Cramér solution satisfies the
    -- normal equations.
    set S2 := ∑ i, d.T i * d.T i
    set S1 := ∑ i, d.T i
    set K : ℝ := d.count
    set P := ∑ i, d.T i * d.H i
    set Q := ∑ i, d.H i
    set G := S2 * K - S1 ^ 2
    have hG' : G ≠ 0 := hG
    refine ⟨(P * K - S1 * Q) / G, (S2 * Q - P * S1) / G, ⟨?_, ?_⟩⟩ <;>
      · field_simp [hG']
        simp only [show S2 = ∑ i, d.T i * d.T i from rfl,
                   show S1 = ∑ i, d.T i from rfl,
                   show P = ∑ i, d.T i * d.H i from rfl,
                   show Q = ∑ i, d.H i from rfl,
                   show G = S2 * K - S1 ^ 2 from rfl,
                   show K = d.count from rfl]
        ring_nf

end PartB2
end IPhO_2026_4
