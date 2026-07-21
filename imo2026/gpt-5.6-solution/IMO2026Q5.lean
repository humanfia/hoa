import Mathlib
set_option backward.isDefEq.respectTransparency false

/-- The subtype of positive real numbers, representing `\mathbb{R}_{>0}`. -/
abbrev PositiveReal : Type := {x : ℝ // 0 < x}

/-- The two-sided inequality defining admissible functions on positive real numbers. -/
def IsAdmissible (f : PositiveReal → PositiveReal) : Prop :=
  ∀ x y : PositiveReal,
    Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) ≥
        ((f x : ℝ) + (y : ℝ)) / 2 ∧
      ((f x : ℝ) + (y : ℝ)) / 2 ≥
        Real.sqrt ((x : ℝ) * (f y : ℝ))

private def displacement (f : PositiveReal → PositiveReal) (x : PositiveReal) : ℝ :=
  (f x : ℝ) - (x : ℝ)

private lemma admissible_sq_upper {f : PositiveReal → PositiveReal} (hf : IsAdmissible f)
    (x y : PositiveReal) :
    ((f x : ℝ) + (y : ℝ)) ^ 2 ≤ 2 * ((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) := by
  have h := (hf x y).1
  have hrad : 0 ≤ (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) := by positivity
  have hsqrt : 0 ≤ Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) :=
    Real.sqrt_nonneg _
  have hfxpos : 0 < (f x : ℝ) := (f x).property
  have hypos : 0 < (y : ℝ) := y.property
  have hmid : 0 ≤ ((f x : ℝ) + (y : ℝ)) / 2 := by linarith
  have hsq := Real.sq_sqrt hrad
  nlinarith [sq_nonneg
    (Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) -
      ((f x : ℝ) + (y : ℝ)) / 2)]

private lemma admissible_sq_lower {f : PositiveReal → PositiveReal} (hf : IsAdmissible f)
    (x y : PositiveReal) :
    4 * (x : ℝ) * (f y : ℝ) ≤ ((f x : ℝ) + (y : ℝ)) ^ 2 := by
  have h := (hf x y).2
  have hxpos : 0 < (x : ℝ) := x.property
  have hfypos : 0 < (f y : ℝ) := (f y).property
  have hprod : 0 ≤ (x : ℝ) * (f y : ℝ) := (mul_pos hxpos hfypos).le
  have hsqrt : 0 ≤ Real.sqrt ((x : ℝ) * (f y : ℝ)) := Real.sqrt_nonneg _
  have hfxpos : 0 < (f x : ℝ) := (f x).property
  have hypos : 0 < (y : ℝ) := y.property
  have hmid : 0 ≤ ((f x : ℝ) + (y : ℝ)) / 2 := by linarith
  have hsq := Real.sq_sqrt hprod
  nlinarith [sq_nonneg
    (((f x : ℝ) + (y : ℝ)) / 2 - Real.sqrt ((x : ℝ) * (f y : ℝ)))]

private lemma admissible_orbit {f : PositiveReal → PositiveReal} (hf : IsAdmissible f)
    (y : PositiveReal) :
    (f (f y) : ℝ) = 2 * (f y : ℝ) - (y : ℝ) := by
  have hu := admissible_sq_upper hf (f y) y
  have hl := admissible_sq_lower hf (f y) y
  have hfactor :
      ((f (f y) : ℝ) + (y : ℝ) - 2 * (f y : ℝ)) *
        ((f (f y) : ℝ) + (y : ℝ) + 2 * (f y : ℝ)) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · have hffy : 0 < (f (f y) : ℝ) := (f (f y)).property
    have hfy : 0 < (f y : ℝ) := (f y).property
    have hy : 0 < (y : ℝ) := y.property
    linarith

private lemma admissible_displacement_f {f : PositiveReal → PositiveReal} (hf : IsAdmissible f)
    (y : PositiveReal) : displacement f (f y) = displacement f y := by
  rw [displacement, displacement, admissible_orbit hf]
  ring

private lemma admissible_displacement_iterate {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) (y : PositiveReal) (n : ℕ) :
    displacement f ((f^[n]) y) = displacement f y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', admissible_displacement_f hf, ih]

private lemma admissible_iterate_coe {f : PositiveReal → PositiveReal} (hf : IsAdmissible f)
    (y : PositiveReal) (n : ℕ) :
    ((f^[n]) y : ℝ) = (y : ℝ) + (n : ℝ) * displacement f y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        (f ((f^[n]) y) : ℝ) = ((f^[n]) y : ℝ) + displacement f ((f^[n]) y) := by
          dsimp [displacement]
          ring
        _ = ((f^[n]) y : ℝ) + displacement f y := by
          rw [admissible_displacement_iterate hf]
        _ = (y : ℝ) + (n.succ : ℝ) * displacement f y := by
          rw [ih]
          push_cast
          ring

private lemma admissible_displacement_nonneg {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) (y : PositiveReal) : 0 ≤ displacement f y := by
  by_contra h
  have hp : displacement f y < 0 := lt_of_not_ge h
  obtain ⟨n, hn⟩ := exists_nat_gt ((y : ℝ) / (-displacement f y))
  have hneg : 0 < -displacement f y := neg_pos.mpr hp
  have hyn : (y : ℝ) < (n : ℝ) * (-displacement f y) :=
    (div_lt_iff₀ hneg).mp hn
  have hiter := admissible_iterate_coe hf y n
  have hpos : 0 < ((f^[n]) y : ℝ) := ((f^[n]) y).property
  nlinarith

private lemma admissible_positive_displacements_eq {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) (x y : PositiveReal)
    (hx : 0 < displacement f x) (hy : 0 < displacement f y) :
    displacement f x = displacement f y := by
  have hle : ∀ a b : PositiveReal, 0 < displacement f a → 0 < displacement f b →
      displacement f a ≤ displacement f b := by
    intro a b ha hb
    by_contra hab
    have hba : displacement f b < displacement f a := lt_of_not_ge hab
    set p : ℝ := displacement f a
    set q : ℝ := displacement f b
    set r : ℝ := p - q
    have hp : 0 < p := by simpa [p] using ha
    have hq : 0 < q := by simpa [q] using hb
    have hr : 0 < r := by simpa [r, p, q] using sub_pos.mpr hba
    obtain ⟨n, hn⟩ := exists_nat_gt
      (((b : ℝ) + q ^ 2 / (2 * r)) / p)
    have hnlarge : (b : ℝ) + q ^ 2 / (2 * r) < (n : ℝ) * p :=
      (div_lt_iff₀ hp).mp hn
    set A : ℝ := (a : ℝ) + (n : ℝ) * p
    have hbA : (b : ℝ) < A := by
      have ha0 : 0 < (a : ℝ) := a.property
      have hfrac : 0 ≤ q ^ 2 / (2 * r) := by positivity
      dsimp [A]
      nlinarith
    have hqA : q ^ 2 < 2 * r * A := by
      have ha0 : 0 < (a : ℝ) := a.property
      have hfrac : q ^ 2 / (2 * r) < A := by
        dsimp [A]
        nlinarith [b.property]
      have := (div_lt_iff₀ (by positivity : 0 < 2 * r)).mp hfrac
      nlinarith
    set t : ℝ := (A - (b : ℝ)) / q
    have ht : 0 ≤ t := by
      dsimp [t]
      positivity
    let m : ℕ := ⌊t⌋₊
    have hmle : (m : ℝ) ≤ t := Nat.floor_le ht
    have htlt : t < (m : ℝ) + 1 := Nat.lt_floor_add_one t
    set B : ℝ := (b : ℝ) + (m : ℝ) * q
    set C : ℝ := B + q
    have hBA : B ≤ A := by
      have hmul : (m : ℝ) * q ≤ A - (b : ℝ) :=
        (le_div_iff₀ hq).mp (by simpa [t] using hmle)
      dsimp [B]
      nlinarith
    have hAC : A < C := by
      have hmul : A - (b : ℝ) < ((m : ℝ) + 1) * q :=
        (div_lt_iff₀ hq).mp (by simpa [t] using htlt)
      dsimp [C, B]
      nlinarith
    have hCpos : 0 < C := by
      have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      dsimp [C, B]
      nlinarith [b.property, mul_nonneg hm0 hq.le]
    have habs : |A - C| ≤ q := by
      have hdiff : A - C ≤ 0 := by linarith
      rw [abs_of_nonpos hdiff]
      dsimp [C]
      nlinarith
    have hsq : (A - C) ^ 2 ≤ q ^ 2 := by
      have hs := (sq_le_sq₀ (abs_nonneg (A - C)) hq.le).2 habs
      simpa only [sq_abs] using hs
    let X : PositiveReal := (f^[n]) a
    let Y : PositiveReal := (f^[m]) b
    have hX : (X : ℝ) = A := by
      dsimp [X, A]
      simpa [p] using admissible_iterate_coe hf a n
    have hY : (Y : ℝ) = B := by
      dsimp [Y, B]
      simpa [q] using admissible_iterate_coe hf b m
    have hdX : displacement f X = p := by
      dsimp [X]
      simpa [p] using admissible_displacement_iterate hf a n
    have hdY : displacement f Y = q := by
      dsimp [Y]
      simpa [q] using admissible_displacement_iterate hf b m
    have hfX : (f X : ℝ) = A + p := by
      rw [← hX]
      dsimp [displacement] at hdX
      nlinarith
    have hfY : (f Y : ℝ) = C := by
      dsimp [displacement] at hdY
      dsimp [C]
      nlinarith [hY]
    have hu := admissible_sq_upper hf X Y
    rw [hX, hY, hfX, hfY] at hu
    have hsum : A + p + B = A + C + r := by
      dsimp [C, r]
      ring
    rw [hsum] at hu
    have hrC : 0 < 2 * r * C := mul_pos (mul_pos (by norm_num) hr) hCpos
    have hgap : 2 * r * (A + C) + r ^ 2 ≤ (A - C) ^ 2 := by
      nlinarith only [hu]
    have hlarge : q ^ 2 < 2 * r * (A + C) + r ^ 2 := by
      nlinarith only [hqA, hrC, sq_nonneg r]
    linarith
  exact le_antisymm (hle x y hx hy) (hle y x hy hx)

private lemma admissible_zero_positive_separated {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) {x y : PositiveReal} {c : ℝ}
    (hx : displacement f x = 0) (hy : displacement f y = c) (hc : 0 < c) :
    c < dist x y := by
  have hfx : (f x : ℝ) = (x : ℝ) := by
    dsimp [displacement] at hx
    linarith
  have hfy : (f y : ℝ) = (y : ℝ) + c := by
    dsimp [displacement] at hy
    linarith
  have hu := admissible_sq_upper hf y x
  rw [hfx, hfy] at hu
  have hxy : 0 < (x : ℝ) + (y : ℝ) := by nlinarith [x.property, y.property]
  have hsum : 0 < 2 * c * ((x : ℝ) + (y : ℝ)) :=
    mul_pos (mul_pos (by norm_num) hc) hxy
  have hsq : c ^ 2 < ((y : ℝ) - (x : ℝ)) ^ 2 := by
    nlinarith
  have habs : c < |(y : ℝ) - (x : ℝ)| := by
    apply (sq_lt_sq₀ hc.le (abs_nonneg _)).mp
    simpa only [sq_abs] using hsq
  simpa only [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using habs

private lemma admissible_displacements_eq {f : PositiveReal → PositiveReal}
    (hf : IsAdmissible f) (x y : PositiveReal) :
    displacement f x = displacement f y := by
  by_cases hex : ∃ a : PositiveReal, 0 < displacement f a
  · obtain ⟨a, ha⟩ := hex
    set c : ℝ := displacement f a
    have hc : 0 < c := by simpa [c] using ha
    have hvalues : ∀ z : PositiveReal, displacement f z = 0 ∨ displacement f z = c := by
      intro z
      rcases (admissible_displacement_nonneg hf z).eq_or_lt with hz | hz
      · exact Or.inl hz.symm
      · exact Or.inr (admissible_positive_displacements_eq hf z a hz ha)
    have hlocal : IsLocallyConstant (displacement f) := by
      rw [IsLocallyConstant.iff_exists_open]
      intro z
      refine ⟨Metric.ball z c, Metric.isOpen_ball, Metric.mem_ball_self hc, ?_⟩
      intro w hw
      have hw' : dist w z < c := Metric.mem_ball.mp hw
      rcases hvalues z with hz | hz <;> rcases hvalues w with hw0 | hwc
      · rw [hz, hw0]
      · exfalso
        have hsep := admissible_zero_positive_separated hf hz hwc hc
        rw [dist_comm] at hsep
        linarith
      · exfalso
        have hsep := admissible_zero_positive_separated hf hw0 hz hc
        linarith
      · rw [hz, hwc]
    letI : PreconnectedSpace PositiveReal :=
      Subtype.preconnectedSpace isPreconnected_Ioi
    exact hlocal.apply_eq_of_preconnectedSpace x y
  · have hz : ∀ z : PositiveReal, displacement f z = 0 := by
      intro z
      have hn := admissible_displacement_nonneg hf z
      by_contra hne
      have hp : 0 < displacement f z := lt_of_le_of_ne hn (Ne.symm hne)
      exact hex ⟨z, hp⟩
    rw [hz x, hz y]

theorem main_theorem (f : PositiveReal → PositiveReal) :
    IsAdmissible f ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x : PositiveReal, (f x : ℝ) = (x : ℝ) + c := by
  constructor
  · intro hf
    let one : PositiveReal := ⟨1, by norm_num⟩
    refine ⟨displacement f one, admissible_displacement_nonneg hf one, ?_⟩
    intro x
    have h := admissible_displacements_eq hf x one
    dsimp [displacement] at h ⊢
    linarith
  · rintro ⟨c, hc, hfc⟩
    intro x y
    rw [hfc x, hfc y]
    constructor
    · apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg ((x : ℝ) - ((y : ℝ) + c))]
    · have hmid : 0 ≤ ((x : ℝ) + c + (y : ℝ)) / 2 := by
        nlinarith [x.property, y.property]
      apply (Real.sqrt_le_left hmid).2
      nlinarith [sq_nonneg ((x : ℝ) - ((y : ℝ) + c))]
