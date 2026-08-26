import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-!
# Fresh-feed recycling

This module models the retained inventory in a cyclic process with a fixed fresh
feed and recycle fraction.  Overall yield is normalized by the cumulative fresh
feed, with an explicit value at zero runs.

Source: `icho_2026_t7_a3:T7-A3`, IChO 2026 Theory Task T7-A3, source page 64.
-/

namespace ChemistryLib.Process

/-- Inventory retained after `runs` recycle cycles. -/
def recycleInventory (fresh recycleFraction : ℝ) (runs : Nat) : ℝ :=
  fresh * recycleFraction *
    Finset.sum (Finset.range runs) (fun n ↦ recycleFraction ^ n)

/-- Fresh-feed overall yield, with an explicit zero-run boundary. -/
noncomputable def overallYield (fresh recycleFraction : ℝ) (runs : Nat) : ℝ :=
  if runs = 0 then 0
  else 1 - recycleInventory fresh recycleFraction runs / ((runs : ℝ) * fresh)

/-- The recycle inventory obeys its cycle recurrence and geometric closed form. -/
theorem recycleInventory_spec : (fresh recycleFraction : ℝ) →
    (recycleInventory fresh recycleFraction 0 = 0 ∧
      ∀ runs : Nat, recycleInventory fresh recycleFraction (runs + 1) =
        recycleFraction * (fresh + recycleInventory fresh recycleFraction runs)) ∧
    ∀ runs : Nat, recycleFraction ≠ 1 →
      recycleInventory fresh recycleFraction runs =
        fresh * recycleFraction * (1 - recycleFraction ^ runs) / (1 - recycleFraction) := by
  intro fresh recycleFraction
  have hrec : ∀ runs : Nat,
      recycleInventory fresh recycleFraction (runs + 1) =
        recycleFraction * (fresh + recycleInventory fresh recycleFraction runs) := by
    intro runs
    by_cases hq : recycleFraction = 1
    · simp [recycleInventory, hq]
      ring
    · have hden : 1 - recycleFraction ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
      have hsum : ∀ n : Nat,
          Finset.sum (Finset.range n) (fun i ↦ recycleFraction ^ i) =
            (1 - recycleFraction ^ n) / (1 - recycleFraction) := by
        intro n
        apply (eq_div_iff hden).2
        exact geom_sum_mul_neg recycleFraction n
      rw [recycleInventory, recycleInventory, hsum (runs + 1), hsum runs]
      field_simp [hden]
      ring_nf
  refine ⟨⟨?_, hrec⟩, ?_⟩
  · simp [recycleInventory]
  · intro runs hq
    have hden : 1 - recycleFraction ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
    have hsum : Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) =
        (1 - recycleFraction ^ runs) / (1 - recycleFraction) := by
      apply (eq_div_iff hden).2
      exact geom_sum_mul_neg recycleFraction runs
    rw [recycleInventory, hsum]
    field_simp [hden]

/-- Converted material plus retained inventory equals all fresh feed supplied. -/
theorem recycle_mass_conservation : (fresh recycleFraction : ℝ) → (runs : Nat) →
    Finset.sum (Finset.range runs)
        (fun n ↦ (1 - recycleFraction) *
          (fresh + recycleInventory fresh recycleFraction n)) +
      recycleInventory fresh recycleFraction runs = (runs : ℝ) * fresh := by
  intro fresh recycleFraction runs
  have hrec := (recycleInventory_spec fresh recycleFraction).1.2
  induction runs with
  | zero => simp [recycleInventory]
  | succ runs ih =>
      rw [Finset.sum_range_succ]
      rw [hrec runs]
      calc
        Finset.sum (Finset.range runs)
              (fun n ↦ (1 - recycleFraction) *
                (fresh + recycleInventory fresh recycleFraction n)) +
            (1 - recycleFraction) *
              (fresh + recycleInventory fresh recycleFraction runs) +
            recycleFraction *
              (fresh + recycleInventory fresh recycleFraction runs) =
            (Finset.sum (Finset.range runs)
                (fun n ↦ (1 - recycleFraction) *
                  (fresh + recycleInventory fresh recycleFraction n)) +
              recycleInventory fresh recycleFraction runs) + fresh := by ring
        _ = (runs : ℝ) * fresh + fresh := by rw [ih]
        _ = ((runs + 1 : Nat) : ℝ) * fresh := by push_cast; ring

/-- The definition is zero at zero runs and otherwise has its inventory ratio form. -/
theorem overallYield_spec : (fresh recycleFraction : ℝ) →
    overallYield fresh recycleFraction 0 = 0 ∧
    ∀ runs : Nat, 0 < runs → overallYield fresh recycleFraction runs =
      1 - recycleInventory fresh recycleFraction runs / ((runs : ℝ) * fresh) := by
  intro fresh recycleFraction
  constructor
  · simp [overallYield]
  · intro runs hruns
    simp [overallYield, Nat.ne_of_gt hruns]

/-- At positive runs, fresh-feed yield has the geometric closed form. -/
theorem overallYield_closedForm : (fresh recycleFraction : ℝ) →
    fresh ≠ 0 → recycleFraction ≠ 1 → (runs : Nat) → 0 < runs →
    overallYield fresh recycleFraction runs =
      1 - recycleFraction * (1 - recycleFraction ^ runs) /
        ((runs : ℝ) * (1 - recycleFraction)) := by
  intro fresh recycleFraction hfresh hrecycle runs hruns
  rw [(overallYield_spec fresh recycleFraction).2 runs hruns]
  rw [(recycleInventory_spec fresh recycleFraction).2 runs hrecycle]
  have hruns0 : (runs : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hruns
  have hden : 1 - recycleFraction ≠ 0 := sub_ne_zero.mpr (Ne.symm hrecycle)
  field_simp [hfresh, hruns0, hden]

/-- For physical recycle fractions, positive-run yield is nonnegative and monotone. -/
theorem overallYield_order_properties : (fresh recycleFraction : ℝ) →
    0 < fresh → 0 ≤ recycleFraction → recycleFraction ≤ 1 →
    (∀ runs : Nat, 0 < runs → 0 ≤ overallYield fresh recycleFraction runs) ∧
    ∀ {earlier later : Nat}, 0 < earlier → earlier ≤ later →
      overallYield fresh recycleFraction earlier ≤
        overallYield fresh recycleFraction later := by
  intro fresh recycleFraction hfresh hq0 hq1
  have hfresh0 : fresh ≠ 0 := ne_of_gt hfresh
  have hyield : ∀ runs : Nat, 0 < runs →
      overallYield fresh recycleFraction runs =
        1 - recycleFraction *
          Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) /
            (runs : ℝ) := by
    intro runs hruns
    rw [(overallYield_spec fresh recycleFraction).2 runs hruns, recycleInventory]
    have hruns0 : (runs : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hruns
    field_simp [hfresh0, hruns0]
  have hadjacent : ∀ runs : Nat, 0 < runs →
      overallYield fresh recycleFraction runs ≤
        overallYield fresh recycleFraction (runs + 1) := by
    intro runs hruns
    have hrunsR : 0 < (runs : ℝ) := by exact_mod_cast hruns
    have hsuccR : 0 < ((runs + 1 : Nat) : ℝ) := by positivity
    have hpowSum : (runs : ℝ) * recycleFraction ^ runs ≤
        Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) := by
      calc
        (runs : ℝ) * recycleFraction ^ runs =
            Finset.sum (Finset.range runs) (fun _ ↦ recycleFraction ^ runs) := by simp
        _ ≤ Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) := by
          apply Finset.sum_le_sum
          intro i hi
          exact pow_le_pow_of_le_one hq0 hq1
            (Nat.le_of_lt (Finset.mem_range.mp hi))
    have hscaled := mul_le_mul_of_nonneg_left hpowSum hq0
    rw [hyield runs hruns, hyield (runs + 1) (Nat.zero_lt_succ runs),
      Finset.sum_range_succ]
    apply sub_le_sub_left
    apply (div_le_div_iff₀ hsuccR hrunsR).2
    calc
      (recycleFraction *
            (Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) +
              recycleFraction ^ runs)) * (runs : ℝ) =
          recycleFraction *
              Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) *
              (runs : ℝ) +
            recycleFraction * ((runs : ℝ) * recycleFraction ^ runs) := by ring
      _ ≤ recycleFraction *
              Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) *
              (runs : ℝ) +
            recycleFraction *
              Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) :=
        by
          convert add_le_add_right hscaled
            (recycleFraction *
              Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) *
                (runs : ℝ)) using 1
      _ = (recycleFraction *
            Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i)) *
          ((runs + 1 : Nat) : ℝ) := by push_cast; ring
  constructor
  · intro runs hruns
    have hrunsR : 0 < (runs : ℝ) := by exact_mod_cast hruns
    have hsum0 : 0 ≤ Finset.sum (Finset.range runs)
        (fun i ↦ recycleFraction ^ i) := by
      exact Finset.sum_nonneg fun _ _ ↦ pow_nonneg hq0 _
    have hsum1 : Finset.sum (Finset.range runs)
          (fun i ↦ recycleFraction ^ i) ≤ (runs : ℝ) := by
      calc
        Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) ≤
            Finset.sum (Finset.range runs) (fun _ ↦ (1 : ℝ)) := by
          apply Finset.sum_le_sum
          intro i _
          simpa using pow_le_pow_of_le_one hq0 hq1 (Nat.zero_le i)
        _ = (runs : ℝ) := by simp
    have hqsum : recycleFraction *
          Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) ≤
        (runs : ℝ) :=
      le_trans (mul_le_of_le_one_left hsum0 hq1) hsum1
    rw [hyield runs hruns]
    have := (div_le_one hrunsR).2 hqsum
    linarith
  · intro earlier later hearlier hle
    obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hle
    induction steps with
    | zero => simp
    | succ steps ih =>
        have hpos : 0 < earlier + steps := by omega
        exact ((ih (by omega)).trans (hadjacent (earlier + steps) hpos))

/-- Every target below one has a least positive run count that reaches it. -/
theorem exists_minimal_run_meeting_threshold : (fresh recycleFraction target : ℝ) →
    0 < fresh → 0 ≤ recycleFraction → recycleFraction < 1 → target < 1 →
    ∃ runs : Nat, 0 < runs ∧ target ≤ overallYield fresh recycleFraction runs ∧
      ∀ m : Nat, 0 < m → target ≤ overallYield fresh recycleFraction m → runs ≤ m := by
  intro fresh recycleFraction target hfresh hq0 hq1 htarget
  have hfresh0 : fresh ≠ 0 := ne_of_gt hfresh
  have hgap : 0 < 1 - target := by linarith
  have honeq : 0 < 1 - recycleFraction := by linarith
  let bound : ℝ := recycleFraction / (1 - recycleFraction)
  obtain ⟨n, hn⟩ := Archimedean.arch bound hgap
  let runs : Nat := n + 1
  have hruns : 0 < runs := by simp [runs]
  have hrunsR : 0 < (runs : ℝ) := by exact_mod_cast hruns
  have hyield : overallYield fresh recycleFraction runs =
      1 - recycleFraction *
        Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) /
          (runs : ℝ) := by
    rw [(overallYield_spec fresh recycleFraction).2 runs hruns, recycleInventory]
    have hruns0 : (runs : ℝ) ≠ 0 := ne_of_gt hrunsR
    field_simp [hfresh0, hruns0]
  have hsumLe : Finset.sum (Finset.range runs)
        (fun i ↦ recycleFraction ^ i) ≤ 1 / (1 - recycleFraction) := by
    apply (le_div_iff₀ honeq).2
    rw [geom_sum_mul_neg]
    linarith [pow_nonneg hq0 runs]
  have hretained : recycleFraction *
        Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) ≤ bound := by
    calc
      recycleFraction *
            Finset.sum (Finset.range runs) (fun i ↦ recycleFraction ^ i) ≤
          recycleFraction * (1 / (1 - recycleFraction)) :=
        mul_le_mul_of_nonneg_left hsumLe hq0
      _ = bound := by simp [bound]; ring
  have hboundGap : bound / (runs : ℝ) ≤ 1 - target := by
    apply (div_le_iff₀ hrunsR).2
    calc
      bound ≤ (n : ℝ) * (1 - target) := by
        simpa [nsmul_eq_mul] using hn
      _ ≤ (runs : ℝ) * (1 - target) := by
        dsimp [runs]
        push_cast
        nlinarith
      _ = (1 - target) * (runs : ℝ) := by ring
  have hreach : target ≤ overallYield fresh recycleFraction runs := by
    rw [hyield]
    have hdiv := (div_le_div_iff_of_pos_right hrunsR).2 hretained
    linarith
  let p : Nat → Prop := fun m ↦ 0 < m ∧ target ≤ overallYield fresh recycleFraction m
  have hexists : ∃ m, p m := ⟨runs, hruns, hreach⟩
  refine ⟨Nat.find hexists, (Nat.find_spec hexists).1,
    (Nat.find_spec hexists).2, ?_⟩
  intro m hm hmeets
  exact Nat.find_min' hexists ⟨hm, hmeets⟩

end ChemistryLib.Process
