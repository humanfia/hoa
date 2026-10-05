import Chemlib.ReactionNetwork.PseudoHelmholtz
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Positive compatibility geometry

This module proves the finite-dimensional Birch intersection theorem used by
the deficiency-zero stability campaign. It imports the library's normalized
`pseudoHelmholtz` functional and uses a continuous KL boundary extension only
to obtain a minimizer on the closed nonnegative compatibility class.

Source references:

* GUNAWARDENA-2003, Section 6, Theorems 6.2 and 6.4
  (source SHA-256 `f191f4cdfe12d2a6bf5f91ce1e3358a12780f12a4b6f296b0b095f0fa42fd530`).
* YU-CRACIUN-2018, Section 2.1, Theorem 2.3
  (source SHA-256 `087c3303f891486c8056bd60bd540dc85bf1b862999249906199e8b57a6dc671`).
-/

open scoped BigOperators

namespace Chemlib.ReactionNetwork

open Filter Set InformationTheory

private noncomputable def logRatio {ι : Type} (xStar y : ι → ℝ) : ι → ℝ :=
  fun i ↦ Real.log (y i) - Real.log (xStar i)

private def IsOrthogonalTo {ι : Type} [Fintype ι]
    (S : Submodule ℝ (ι → ℝ)) (z : ι → ℝ) : Prop :=
  ∀ v ∈ S, ∑ i, z i * v i = 0

private def IsCompatible {ι : Type}
    (S : Submodule ℝ (ι → ℝ)) (x y : ι → ℝ) : Prop :=
  y - x ∈ S

private noncomputable def scaledKL {ι : Type} [Fintype ι]
    (xStar y : ι → ℝ) : ℝ :=
  ∑ i, xStar i * klFun (y i / xStar i)

/-- On the positive orthant, the continuous boundary extension used in the
existence argument is exactly the library's normalized pseudo-Helmholtz
functional. -/
private theorem scaledKL_eq_pseudoHelmholtz_of_pos
    {ι : Type} [Fintype ι]
    (xStar y : ι → ℝ) (hxStar : ∀ i, 0 < xStar i)
    (hy : ∀ i, 0 < y i) :
    scaledKL xStar y = pseudoHelmholtz xStar y := by
  unfold scaledKL pseudoHelmholtz
  apply Finset.sum_congr rfl
  intro i _
  rw [klFun_apply, Real.log_div (hy i).ne' (hxStar i).ne']
  field_simp [ne_of_gt (hxStar i)]
  ring

private theorem continuous_scaledKL {ι : Type} [Fintype ι] (xStar : ι → ℝ) :
    Continuous (scaledKL xStar) := by
  unfold scaledKL
  fun_prop

private theorem scaledKL_nonneg {ι : Type} [Fintype ι]
    (xStar y : ι → ℝ) (hxStar : ∀ i, 0 < xStar i)
    (hy : ∀ i, 0 ≤ y i) :
    0 ≤ scaledKL xStar y := by
  unfold scaledKL
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hxStar i).le
    (klFun_nonneg (div_nonneg (hy i) (hxStar i).le))

private theorem scaledKL_coordinate_tendsto_atTop {ι : Type} [Fintype ι]
    (xStar : ι → ℝ) (hxStar : ∀ i, 0 < xStar i) (i : ι) :
    Tendsto (fun t : ℝ ↦ xStar i * klFun (t / xStar i)) atTop atTop := by
  exact (tendsto_klFun_atTop.comp
    (tendsto_id.atTop_div_const (hxStar i))).const_mul_atTop (hxStar i)

private theorem scaledKL_nonnegative_sublevel_bounded {ι : Type} [Fintype ι]
    (xStar : ι → ℝ) (hxStar : ∀ i, 0 < xStar i) (C : ℝ) :
    Bornology.IsBounded
      {y : ι → ℝ | (∀ i, 0 ≤ y i) ∧ scaledKL xStar y ≤ C} := by
  have hthreshold : ∀ i, ∃ B : ℝ, ∀ t, B ≤ t →
      C < xStar i * klFun (t / xStar i) := by
    intro i
    have hevent : ∀ᶠ t : ℝ in atTop,
        C < xStar i * klFun (t / xStar i) :=
      (scaledKL_coordinate_tendsto_atTop xStar hxStar i)
        (eventually_gt_atTop C)
    rw [eventually_atTop] at hevent
    exact hevent
  choose B hB using hthreshold
  let M : ℝ := ∑ i, |B i|
  refine isBounded_iff_forall_norm_le.mpr ⟨M, ?_⟩
  intro y hy
  have hcoord : ∀ i, y i < B i := by
    intro i
    by_contra hnot
    have hBi : B i ≤ y i := le_of_not_gt hnot
    have hsingle : xStar i * klFun (y i / xStar i) ≤ scaledKL xStar y := by
      unfold scaledKL
      exact Finset.single_le_sum
        (fun j _ ↦ mul_nonneg (hxStar j).le
          (klFun_nonneg (div_nonneg (hy.1 j) (hxStar j).le)))
        (Finset.mem_univ i)
    exact (not_lt_of_ge (hsingle.trans hy.2)) (hB i (y i) hBi)
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)).2
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hy.1 i)]
  exact (le_of_lt (hcoord i)).trans <|
    (le_abs_self (B i)).trans <|
      Finset.single_le_sum (fun j _ ↦ abs_nonneg (B j)) (Finset.mem_univ i)

private def nonnegativeCompatibilitySet {ι : Type}
    (S : Submodule ℝ (ι → ℝ)) (x : ι → ℝ) : Set (ι → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ y - x ∈ S}

private theorem isClosed_nonnegativeCompatibilitySet {ι : Type} [Fintype ι]
    (S : Submodule ℝ (ι → ℝ)) (x : ι → ℝ) :
    IsClosed (nonnegativeCompatibilitySet S x) := by
  have hnonneg : IsClosed {y : ι → ℝ | ∀ i, 0 ≤ y i} := by
    simp only [show {y : ι → ℝ | ∀ i, 0 ≤ y i} =
        ⋂ i, {y : ι → ℝ | (0 : ℝ) ≤ y i} by ext; simp]
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (continuous_apply i)
  have hcompat : IsClosed {y : ι → ℝ | y - x ∈ S} := by
    exact (Submodule.closed_of_finiteDimensional S).preimage
      (continuous_id.sub continuous_const)
  exact hnonneg.inter hcompat

private theorem exists_scaledKL_minimizer_on_compatibility
    {ι : Type} [Fintype ι]
    (S : Submodule ℝ (ι → ℝ))
    (xStar x : ι → ℝ)
    (hxStar : ∀ i, 0 < xStar i) (hx : ∀ i, 0 < x i) :
    ∃ y ∈ nonnegativeCompatibilitySet S x,
      IsMinOn (scaledKL xStar) (nonnegativeCompatibilitySet S x) y := by
  let K := nonnegativeCompatibilitySet S x
  let L : Set (ι → ℝ) := K ∩ {y | scaledKL xStar y ≤ scaledKL xStar x}
  have hxK : x ∈ K := by
    exact ⟨fun i ↦ (hx i).le, by simp⟩
  have hxL : x ∈ L := ⟨hxK, show scaledKL xStar x ≤ scaledKL xStar x from le_rfl⟩
  have hLclosed : IsClosed L := by
    exact (isClosed_nonnegativeCompatibilitySet S x).inter
      (isClosed_le (continuous_scaledKL xStar) continuous_const)
  have hLbounded : Bornology.IsBounded L := by
    apply (scaledKL_nonnegative_sublevel_bounded xStar hxStar
      (scaledKL xStar x)).subset
    intro y hy
    exact ⟨hy.1.1, hy.2⟩
  have hLcompact : IsCompact L :=
    Metric.isCompact_of_isClosed_isBounded hLclosed hLbounded
  obtain ⟨y, hyL, hyMinL⟩ :=
    hLcompact.exists_isMinOn ⟨x, hxL⟩ (continuous_scaledKL xStar).continuousOn
  refine ⟨y, hyL.1, ?_⟩
  intro z hzK
  by_cases hz : scaledKL xStar z ≤ scaledKL xStar x
  · exact hyMinL ⟨hzK, hz⟩
  · exact (hyMinL hxL).trans (le_of_lt (lt_of_not_ge hz))

private theorem scaledKL_coordinate_convex
    (a u v t : ℝ) (ha : 0 < a) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a * klFun (((1 - t) * u + t * v) / a) ≤
      (1 - t) * (a * klFun (u / a)) + t * (a * klFun (v / a)) := by
  have h := convexOn_klFun.2
    (div_nonneg hu ha.le) (div_nonneg hv ha.le)
    (sub_nonneg.mpr ht1) ht0 (by ring)
  have hamul := mul_le_mul_of_nonneg_left h ha.le
  have harg : (((1 - t) * u + t * v) / a) =
      (1 - t) • (u / a) + t • (v / a) := by
    simp only [smul_eq_mul]
    field_simp [ha.ne']
  rw [harg]
  calc
    _ ≤ a * ((1 - t) • klFun (u / a) + t • klFun (v / a)) := hamul
    _ = _ := by simp only [smul_eq_mul]; ring

private theorem scaledKL_coordinate_zero_gap
    (a v t : ℝ) (ha : 0 < a) (hv : 0 < v) (ht : 0 < t) :
    a * klFun ((t * v) / a) =
      (1 - t) * (a * klFun (0 / a)) + t * (a * klFun (v / a)) +
        t * v * Real.log t := by
  rw [klFun_apply, klFun_apply, klFun_apply]
  rw [Real.log_div (mul_ne_zero ht.ne' hv.ne') ha.ne',
    Real.log_mul ht.ne' hv.ne', Real.log_div hv.ne' ha.ne']
  field_simp
  ring

private theorem scaledKL_segment_le_with_zero_gap
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (xStar x y : ι → ℝ) (i : ι) (t : ℝ)
    (hxStar : ∀ j, 0 < xStar j)
    (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 ≤ y j)
    (hyi : y i = 0) (ht0 : 0 < t) (ht1 : t < 1) :
    scaledKL xStar (fun j ↦ (1 - t) * y j + t * x j) ≤
      (1 - t) * scaledKL xStar y + t * scaledKL xStar x +
        t * x i * Real.log t := by
  have hpoint : ∀ j,
      xStar j * klFun (((1 - t) * y j + t * x j) / xStar j) ≤
        (1 - t) * (xStar j * klFun (y j / xStar j)) +
          t * (xStar j * klFun (x j / xStar j)) +
            (if j = i then t * x i * Real.log t else 0) := by
    intro j
    by_cases hji : j = i
    · subst j
      rw [if_pos rfl]
      simp only [hyi, mul_zero, zero_add]
      exact le_of_eq (scaledKL_coordinate_zero_gap
        (xStar i) (x i) t (hxStar i) (hx i) ht0)
    · rw [if_neg hji, add_zero]
      exact scaledKL_coordinate_convex (xStar j) (y j) (x j) t
        (hxStar j) (hy j) (hx j).le ht0.le ht1.le
  unfold scaledKL
  calc
    _ ≤ ∑ j, ((1 - t) * (xStar j * klFun (y j / xStar j)) +
        t * (xStar j * klFun (x j / xStar j)) +
          (if j = i then t * x i * Real.log t else 0)) :=
      Finset.sum_le_sum fun j _ ↦ hpoint j
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]

private theorem minimizer_on_compatibility_is_positive
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule ℝ (ι → ℝ))
    (xStar x y : ι → ℝ)
    (hxStar : ∀ i, 0 < xStar i) (hx : ∀ i, 0 < x i)
    (hyK : y ∈ nonnegativeCompatibilitySet S x)
    (hyMin : IsMinOn (scaledKL xStar) (nonnegativeCompatibilitySet S x) y) :
    ∀ i, 0 < y i := by
  intro i
  apply lt_of_le_of_ne (hyK.1 i)
  intro hyi'
  have hyi : y i = 0 := hyi'.symm
  let A : ℝ := (scaledKL xStar x - scaledKL xStar y) / x i
  let q : ℝ := |A| + 1
  let t : ℝ := Real.exp (-q)
  have hq : 0 < q := by dsimp [q]; positivity
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := by
    dsimp [t]
    rw [show (1 : ℝ) = Real.exp 0 by simp, Real.exp_lt_exp]
    linarith
  have hlogt : Real.log t = -q := by
    dsimp [t]
    rw [Real.log_exp]
  let yt : ι → ℝ := fun j ↦ (1 - t) * y j + t * x j
  have hytK : yt ∈ nonnegativeCompatibilitySet S x := by
    constructor
    · intro j
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr ht1.le) (hyK.1 j))
        (mul_nonneg ht0.le (hx j).le)
    · have hscale : yt - x = (1 - t) • (y - x) := by
        funext j
        dsimp [yt]
        ring
      rw [hscale]
      exact S.smul_mem _ hyK.2
  have hgap := scaledKL_segment_le_with_zero_gap
    xStar x y i t hxStar hx hyK.1 hyi ht0 ht1
  have hlog_lt : Real.log t < -A := by
    rw [hlogt]
    dsimp [q]
    have hAle : A ≤ |A| := le_abs_self A
    linarith
  have hbracket :
      scaledKL xStar x - scaledKL xStar y + x i * Real.log t < 0 := by
    have hmul := mul_lt_mul_of_pos_left hlog_lt (hx i)
    have hA : x i * A = scaledKL xStar x - scaledKL xStar y := by
      dsimp [A]
      field_simp [ne_of_gt (hx i)]
    rw [mul_neg, hA] at hmul
    linarith
  have hstrict : scaledKL xStar yt < scaledKL xStar y := by
    calc
      scaledKL xStar yt ≤
          (1 - t) * scaledKL xStar y + t * scaledKL xStar x +
            t * x i * Real.log t := hgap
      _ < scaledKL xStar y := by
        have hmul := mul_neg_of_pos_of_neg ht0 hbracket
        nlinarith
  exact (not_lt_of_ge (hyMin hytK)) hstrict

private theorem minimizer_on_compatibility_is_logOrthogonal
    {ι : Type} [Fintype ι]
    (S : Submodule ℝ (ι → ℝ))
    (xStar x y : ι → ℝ)
    (hxStar : ∀ i, 0 < xStar i) (hyPos : ∀ i, 0 < y i)
    (hyK : y ∈ nonnegativeCompatibilitySet S x)
    (hyPseudoMin : ∀ z, (∀ i, 0 < z i) → z - x ∈ S →
      pseudoHelmholtz xStar y ≤ pseudoHelmholtz xStar z) :
    IsOrthogonalTo S (logRatio xStar y) := by
  intro v hv
  let line : ℝ → (ι → ℝ) := fun t i ↦ y i + t * v i
  have hpos_event : ∀ᶠ t : ℝ in nhds 0, ∀ i, 0 < line t i := by
    rw [eventually_all]
    intro i
    have hcont : ContinuousAt (fun t : ℝ ↦ line t i) 0 := by
      dsimp [line]
      fun_prop
    exact continuousAt_const.eventually_lt hcont (by simpa [line] using hyPos i)
  have hlocal : IsLocalMin (fun t ↦ scaledKL xStar (line t)) 0 := by
    filter_upwards [hpos_event] with t ht
    have hlineK : line t ∈ nonnegativeCompatibilitySet S x := by
      constructor
      · exact fun i ↦ (ht i).le
      · have heq : line t - x = (y - x) + t • v := by
          funext i
          dsimp [line]
          ring
        rw [heq]
        exact S.add_mem hyK.2 (S.smul_mem t hv)
    have hpseudo := hyPseudoMin (line t) ht hlineK.2
    rw [← scaledKL_eq_pseudoHelmholtz_of_pos xStar y hxStar hyPos,
      ← scaledKL_eq_pseudoHelmholtz_of_pos xStar (line t) hxStar ht] at hpseudo
    simpa [line] using hpseudo
  have hderiv : HasDerivAt (fun t ↦ scaledKL xStar (line t))
      (∑ i, Real.log (y i / xStar i) * v i) 0 := by
    unfold scaledKL
    apply HasDerivAt.fun_sum
    intro i _
    have hinner : HasDerivAt (fun t : ℝ ↦ line t i / xStar i)
        (v i / xStar i) 0 := by
      simpa [line] using (((hasDerivAt_const (x := (0 : ℝ)) (y i)).add
        ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (v i))).div_const (xStar i))
    have hklBase : HasDerivAt klFun (Real.log (y i / xStar i))
        (line 0 i / xStar i) := by
      simpa [line] using hasDerivAt_klFun
        (div_ne_zero (hyPos i).ne' (hxStar i).ne')
    have hkl := hklBase.comp 0 hinner
    have hscaled := hkl.const_mul (xStar i)
    have heq : xStar i * (Real.log (y i / xStar i) * (v i / xStar i)) =
        Real.log (y i / xStar i) * v i := by
      field_simp [ne_of_gt (hxStar i)]
    rw [← heq]
    simpa only [Function.comp_apply] using hscaled
  have hzero := hlocal.hasDerivAt_eq_zero hderiv
  unfold logRatio
  rw [← hzero]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.log_div (hyPos i).ne' (hxStar i).ne']

private theorem birch_unique
    {ι : Type} [Fintype ι]
    (S : Submodule ℝ (ι → ℝ))
    (xStar x y z : ι → ℝ)
    (hy : ∀ i, 0 < y i) (hz : ∀ i, 0 < z i)
    (hyComp : IsCompatible S x y) (hzComp : IsCompatible S x z)
    (hyOrth : IsOrthogonalTo S (logRatio xStar y))
    (hzOrth : IsOrthogonalTo S (logRatio xStar z)) :
    y = z := by
  have hyzS : y - z ∈ S := by
    have := S.sub_mem hyComp hzComp
    simpa [IsCompatible, sub_sub_sub_cancel_right] using this
  have hdotY := hyOrth (y - z) hyzS
  have hdotZ := hzOrth (y - z) hyzS
  have hsum : ∑ i, (Real.log (y i) - Real.log (z i)) * (y i - z i) = 0 := by
    unfold logRatio at hdotY hdotZ
    calc
      _ = (∑ i, (Real.log (y i) - Real.log (xStar i)) * (y - z) i) -
          (∑ i, (Real.log (z i) - Real.log (xStar i)) * (y - z) i) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i _
            simp only [Pi.sub_apply]
            ring
      _ = 0 := by rw [hdotY, hdotZ, sub_self]
  have hterm : ∀ i, 0 ≤ (Real.log (y i) - Real.log (z i)) * (y i - z i) := by
    intro i
    rcases le_total (y i) (z i) with hyz | hzy
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (Real.strictMonoOn_log.monotoneOn (hy i) (hz i) hyz))
        (sub_nonpos.mpr hyz)
    · exact mul_nonneg
        (sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn (hz i) (hy i) hzy))
        (sub_nonneg.mpr hzy)
  funext i
  have hi : (Real.log (y i) - Real.log (z i)) * (y i - z i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hterm j)).mp hsum i (Finset.mem_univ i)
  rcases mul_eq_zero.mp hi with hlog | hdiff
  · exact Real.strictMonoOn_log.injOn (hy i) (hz i) (sub_eq_zero.mp hlog)
  · exact sub_eq_zero.mp hdiff

/-- A positive affine compatibility class meets the relative-log orthogonal
manifold in exactly one point. -/
theorem existsUnique_positive_logOrthogonal_mem_affineClass
    {Species : Type} [Fintype Species] [DecidableEq Species]
    (S : Submodule ℝ (Species → ℝ))
    (xStar x : Species → ℝ)
    (hxStar : ∀ s, 0 < xStar s)
    (hx : ∀ s, 0 < x s) :
    ∃! y : Species → ℝ, (∀ s, 0 < y s) ∧ y - x ∈ S ∧
      (∀ v ∈ S, ∑ s,
        (Real.log (y s) - Real.log (xStar s)) * v s = 0) := by
  obtain ⟨y, hyK, hyMin⟩ :=
    exists_scaledKL_minimizer_on_compatibility S xStar x hxStar hx
  have hyPos := minimizer_on_compatibility_is_positive
    S xStar x y hxStar hx hyK hyMin
  have hyPseudoMin : ∀ z, (∀ i, 0 < z i) → z - x ∈ S →
      pseudoHelmholtz xStar y ≤ pseudoHelmholtz xStar z := by
    intro z hzPos hzComp
    rw [← scaledKL_eq_pseudoHelmholtz_of_pos xStar y hxStar hyPos,
      ← scaledKL_eq_pseudoHelmholtz_of_pos xStar z hxStar hzPos]
    exact hyMin ⟨fun i ↦ (hzPos i).le, hzComp⟩
  have hyOrth := minimizer_on_compatibility_is_logOrthogonal
    S xStar x y hxStar hyPos hyK hyPseudoMin
  refine ⟨y, ⟨hyPos, hyK.2, ?_⟩, ?_⟩
  · simpa [IsOrthogonalTo, logRatio] using hyOrth
  · intro z hz
    symm
    apply birch_unique S xStar x y z hyPos hz.1
    · exact hyK.2
    · exact hz.2.1
    · exact hyOrth
    · simpa [IsOrthogonalTo, logRatio] using hz.2.2

end Chemlib.ReactionNetwork

