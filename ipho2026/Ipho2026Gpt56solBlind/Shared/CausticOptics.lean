import Ipho2026Gpt56solBlind.Shared.GeometricOptics
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic

/-!
# Differentiable reflected-ray caustics and small-angle asymptotics

This module builds differentiable reflected-ray families, neighboring-line
limits, their forward-propagating physical branch, and normalized one-sided
caustic asymptotics on the common geometric-optics kernel.
-/

noncomputable section

namespace Ipho2026Gpt56solBlind.Shared.GeometricOptics

/-! ## Differentiable reflected-ray families and line coefficients -/

/-- A one-parameter family of parallel-incidence, radially reflected rays. -/
structure ReflectedRayFamily where
  domain : Set ℝ
  mirror : Circle
  incidence : ℝ → Point2
  incoming : UnitDirection
  normal : ℝ → UnitDirection
  outgoing : ℝ → UnitDirection
  incidence_on_mirror : ∀ θ ∈ domain, OnCircle mirror (incidence θ)
  normal_is_radial : ∀ θ, ∀ hθ : θ ∈ domain,
    normal θ = radialUnitNormal mirror (incidence θ) (incidence_on_mirror θ hθ)
  outgoing_is_specular : ∀ θ ∈ domain,
    IsSpecularReflection incoming (normal θ) (outgoing θ)

/-- Axial reflected-ray family on an oriented semicircle. -/
def axialReflectedRayFamily (c : Circle) (o : VerticalOrientation) :
    ReflectedRayFamily :=
  { domain := {θ | InAxialIncidenceDomain θ}
    mirror := c
    incidence := fun θ => (semicirclePoint c o θ).1
    incoming := axisDirection o
    normal := fun θ => ⟨(semicirclePoint c o θ).2, by
      cases o <;>
        simp only [semicirclePoint, directionNormSq, directionDot, orientationSign,
          one_mul, neg_mul] <;>
        nlinarith [Real.sin_sq_add_cos_sq θ]⟩
    outgoing := fun θ => (axialReflectedRay c o θ).direction
    incidence_on_mirror := by
      intro θ hθ
      exact (semicirclePoint_invariants c o .aperture θ hθ).1.1
    normal_is_radial := by
      intro θ hθ
      apply Subtype.ext
      simp only [semicirclePoint, radialUnitNormal, Direction2.mk.injEq]
      constructor <;> field_simp [ne_of_gt c.radius_pos] <;> ring
    outgoing_is_specular := by
      intro θ _hθ
      simpa [axialReflectedRay, IsSpecularReflection, reflectedUnitDirection] using
        (reflectedDirection_components (axisDirection o).1
          (⟨(semicirclePoint c o θ).2, by
            cases o <;>
              simp only [semicirclePoint, directionNormSq, directionDot, orientationSign,
                one_mul, neg_mul] <;>
              nlinarith [Real.sin_sq_add_cos_sq θ]⟩ : UnitDirection)) }

/-- Coefficients describing the reflected supporting line at one parameter. -/
def IsReflectedLineCoefficients (F : ReflectedRayFamily) (θ : ℝ)
    (c : LineCoefficients) : Prop :=
  θ ∈ F.domain ∧ DescribesNonverticalLine (F.incidence θ) (F.outgoing θ).1 c

/-- A nonvertical reflected ray has a unique slope-intercept pair. -/
theorem existsUnique_reflectedLineCoefficients (F : ReflectedRayFamily) (θ : ℝ)
    (hθ : θ ∈ F.domain) (hx : (F.outgoing θ).1.x ≠ 0) :
    ∃! c : LineCoefficients, IsReflectedLineCoefficients F θ c := by
  rcases existsUnique_lineCoefficients (F.incidence θ) (F.outgoing θ).1 hx with
    ⟨c, hc, huniq⟩
  refine ⟨c, ⟨hθ, hc⟩, ?_⟩
  intro y hy
  exact huniq y hy.2

/-- Openness and componentwise differentiability of a reflected-ray family. -/
def DifferentiableReflectedRayFamily (F : ReflectedRayFamily) : Prop :=
  IsOpen F.domain ∧
    DifferentiableOn ℝ (fun θ => (F.incidence θ).x) F.domain ∧
    DifferentiableOn ℝ (fun θ => (F.incidence θ).y) F.domain ∧
    DifferentiableOn ℝ (fun θ => (F.outgoing θ).1.x) F.domain ∧
    DifferentiableOn ℝ (fun θ => (F.outgoing θ).1.y) F.domain

/-- Componentwise derivatives of incidence point and outgoing direction. -/
structure RayDerivativeData where
  pointDerivative : Displacement2
  directionDerivative : Direction2

/-- Four derivative equalities for a ray family at an interior parameter. -/
def HasRayDerivativesAt (F : ReflectedRayFamily) (θ : ℝ)
    (data : RayDerivativeData) : Prop :=
  θ ∈ F.domain ∧
    HasDerivAt (fun t => (F.incidence t).x) data.pointDerivative.x θ ∧
    HasDerivAt (fun t => (F.incidence t).y) data.pointDerivative.y θ ∧
    HasDerivAt (fun t => (F.outgoing t).1.x) data.directionDerivative.x θ ∧
    HasDerivAt (fun t => (F.outgoing t).1.y) data.directionDerivative.y θ

/-- Derivative data for slope and intercept functions. -/
structure CoefficientDerivativeData where
  slopeDerivative : ℝ
  interceptDerivative : Length

/-- Derivative equalities for coefficient functions. -/
def HasCoefficientDerivativesAt (m b : ℝ → ℝ) (θ : ℝ)
    (data : CoefficientDerivativeData) : Prop :=
  HasDerivAt m data.slopeDerivative θ ∧ HasDerivAt b data.interceptDerivative θ

/-- Quotient- and product-rule derivatives of canonical reflected-line coefficients. -/
theorem reflectedLineCoefficients_derivatives (F : ReflectedRayFamily) (θ : ℝ)
    (rayData : RayDerivativeData) (hDeriv : HasRayDerivativesAt F θ rayData)
    (hx : (F.outgoing θ).1.x ≠ 0) :
    let coeff := fun t => nonverticalLineCoefficients (F.incidence t) (F.outgoing t).1
    let dm :=
      (rayData.directionDerivative.y * (F.outgoing θ).1.x -
        (F.outgoing θ).1.y * rayData.directionDerivative.x) /
          (F.outgoing θ).1.x ^ 2
    let db := rayData.pointDerivative.y - dm * (F.incidence θ).x -
      (coeff θ).slope * rayData.pointDerivative.x
    HasCoefficientDerivativesAt (fun t => (coeff t).slope)
      (fun t => (coeff t).intercept) θ
      { slopeDerivative := dm, interceptDerivative := db } := by
  have hasDerivDiv (f g : ℝ → ℝ) (f' g' : ℝ)
      (hf : HasDerivAt f f' θ) (hg : HasDerivAt g g' θ) (hg0 : g θ ≠ 0) :
      HasDerivAt (fun t => f t / g t)
        ((f' * g θ - f θ * g') / g θ ^ 2) θ := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    let af := fun h : ℝ => f (θ + h) - f θ - h * f'
    let ag := fun h : ℝ => g (θ + h) - g θ - h * g'
    have haf : af =o[nhds 0] (fun h : ℝ => h) := by
      simpa only [af, smul_eq_mul] using
        (hasDerivAt_iff_isLittleO_nhds_zero.mp hf)
    have hag : ag =o[nhds 0] (fun h : ℝ => h) := by
      simpa only [ag, smul_eq_mul] using
        (hasDerivAt_iff_isLittleO_nhds_zero.mp hg)
    have haft := haf.tendsto_div_nhds_zero
    have hagt := hag.tendsto_div_nhds_zero
    have hshift : Filter.Tendsto (fun h : ℝ => θ + h) (nhds 0) (nhds θ) := by
      simpa only [add_zero] using
        (Filter.Tendsto.add
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => θ) (nhds 0) (nhds θ))
          (show Filter.Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0) from
            continuousAt_id.tendsto))
    have hgt : Filter.Tendsto (fun h => g (θ + h)) (nhds 0) (nhds (g θ)) :=
      hg.continuousAt.tendsto.comp hshift
    refine (Asymptotics.isLittleO_iff_tendsto (fun h hh => ?_)).2 ?_
    · subst h
      simp
    let R := fun h : ℝ =>
      (((f' + af h / h) * g θ - f θ * (g' + ag h / h)) /
        (g (θ + h) * g θ)) - (f' * g θ - f θ * g') / g θ ^ 2
    have hR : Filter.Tendsto R (nhds 0) (nhds 0) := by
      have hfq : Filter.Tendsto (fun h : ℝ => f' + af h / h)
          (nhds 0) (nhds f') := by
        simpa only [add_zero] using
          (Filter.Tendsto.add
            (tendsto_const_nhds :
              Filter.Tendsto (fun _ : ℝ => f') (nhds 0) (nhds f')) haft)
      have hgq : Filter.Tendsto (fun h : ℝ => g' + ag h / h)
          (nhds 0) (nhds g') := by
        simpa only [add_zero] using
          (Filter.Tendsto.add
            (tendsto_const_nhds :
              Filter.Tendsto (fun _ : ℝ => g') (nhds 0) (nhds g')) hagt)
      have hnum := (hfq.mul_const (g θ)).sub (hgq.const_mul (f θ))
      have hden : Filter.Tendsto (fun h : ℝ => g (θ + h) * g θ)
          (nhds 0) (nhds (g θ ^ 2)) := by
        simpa only [pow_two] using hgt.mul_const (g θ)
      have hquot' : Filter.Tendsto
          (fun h : ℝ => ((f' + af h / h) * g θ - f θ * (g' + ag h / h)) /
            (g (θ + h) * g θ)) (nhds 0)
          (nhds ((f' * g θ - f θ * g') / g θ ^ 2)) := by
        simpa only [div_eq_mul_inv, pow_two] using
          hnum.mul (hden.inv₀ (pow_ne_zero 2 hg0))
      simpa only [R, sub_self] using hquot'.sub
        (tendsto_const_nhds : Filter.Tendsto
          (fun _ : ℝ => (f' * g θ - f θ * g') / g θ ^ 2) (nhds 0)
          (nhds ((f' * g θ - f θ * g') / g θ ^ 2)))
    apply Filter.Tendsto.congr' _ hR
    have hgnz : ∀ᶠ h in nhds (0 : ℝ), g (θ + h) ≠ 0 :=
      hgt.eventually (eventually_ne_nhds hg0)
    filter_upwards [hgnz] with h hgh
    dsimp only [R, af, ag]
    by_cases hh : h = 0
    · subst h
      simp [pow_two]
    · have halg :
          ((f (θ + h) / g (θ + h) - f θ / g θ -
              h * ((f' * g θ - f θ * g') / g θ ^ 2)) / h) =
            (((f' + (f (θ + h) - f θ - h * f') / h) * g θ -
                f θ * (g' + (g (θ + h) - g θ - h * g') / h)) /
              (g (θ + h) * g θ) - (f' * g θ - f θ * g') / g θ ^ 2) := by
        field_simp [hh, hgh, hg0]
        ring
      simpa only [smul_eq_mul] using halg.symm
  have hasDerivMul (f g : ℝ → ℝ) (f' g' : ℝ)
      (hf : HasDerivAt f f' θ) (hg : HasDerivAt g g' θ) :
      HasDerivAt (fun t => f t * g t) (f' * g θ + f θ * g') θ := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    let af := fun h : ℝ => f (θ + h) - f θ - h * f'
    let ag := fun h : ℝ => g (θ + h) - g θ - h * g'
    have haf : af =o[nhds 0] (fun h : ℝ => h) := by
      simpa only [af, smul_eq_mul] using
        (hasDerivAt_iff_isLittleO_nhds_zero.mp hf)
    have hag : ag =o[nhds 0] (fun h : ℝ => h) := by
      simpa only [ag, smul_eq_mul] using
        (hasDerivAt_iff_isLittleO_nhds_zero.mp hg)
    have haft := haf.tendsto_div_nhds_zero
    have hagt := hag.tendsto_div_nhds_zero
    have hshift : Filter.Tendsto (fun h : ℝ => θ + h) (nhds 0) (nhds θ) := by
      simpa only [add_zero] using
        (Filter.Tendsto.add
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => θ) (nhds 0) (nhds θ))
          (show Filter.Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0) from
            continuousAt_id.tendsto))
    have hgt : Filter.Tendsto (fun h => g (θ + h)) (nhds 0) (nhds (g θ)) :=
      hg.continuousAt.tendsto.comp hshift
    refine (Asymptotics.isLittleO_iff_tendsto (fun h hh => ?_)).2 ?_
    · subst h
      simp
    let R := fun h : ℝ =>
      f' * (g (θ + h) - g θ) + (af h / h) * g (θ + h) +
        f θ * (ag h / h)
    have hR : Filter.Tendsto R (nhds 0) (nhds 0) := by
      have h1 : Filter.Tendsto (fun h : ℝ => f' * (g (θ + h) - g θ))
          (nhds 0) (nhds 0) := by
        simpa only [sub_self, mul_zero] using
          (hgt.sub (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => g θ) (nhds 0) (nhds (g θ)))).const_mul f'
      have h2 : Filter.Tendsto (fun h : ℝ => (af h / h) * g (θ + h))
          (nhds 0) (nhds 0) := by
        simpa only [zero_mul] using haft.mul hgt
      have h3 : Filter.Tendsto (fun h : ℝ => f θ * (ag h / h))
          (nhds 0) (nhds 0) := by
        simpa only [mul_zero] using hagt.const_mul (f θ)
      simpa only [R, zero_add] using (h1.add h2).add h3
    apply Filter.Tendsto.congr' _ hR
    filter_upwards with h
    dsimp only [R, af, ag]
    by_cases hh : h = 0
    · subst h
      simp
    · field_simp [hh]
      ring
  have hasDerivSub (f g : ℝ → ℝ) (f' g' : ℝ)
      (hf : HasDerivAt f f' θ) (hg : HasDerivAt g g' θ) :
      HasDerivAt (fun t => f t - g t) (f' - g') θ := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have hfO := hasDerivAt_iff_isLittleO_nhds_zero.mp hf
    have hgO := hasDerivAt_iff_isLittleO_nhds_zero.mp hg
    refine (hfO.sub hgO).congr ?_ (fun _ => rfl)
    intro h
    simp only [smul_eq_mul]
    ring
  rcases hDeriv with ⟨_hθ, hPx, hPy, hDx, hDy⟩
  dsimp only
  let dm :=
    (rayData.directionDerivative.y * (F.outgoing θ).1.x -
      (F.outgoing θ).1.y * rayData.directionDerivative.x) /
        (F.outgoing θ).1.x ^ 2
  have hm : HasDerivAt
      (fun t => (F.outgoing t).1.y / (F.outgoing t).1.x) dm θ := by
    exact hasDerivDiv _ _ _ _ hDy hDx hx
  have hmp : HasDerivAt
      (fun t => ((F.outgoing t).1.y / (F.outgoing t).1.x) * (F.incidence t).x)
      (dm * (F.incidence θ).x +
        ((F.outgoing θ).1.y / (F.outgoing θ).1.x) * rayData.pointDerivative.x) θ := by
    exact hasDerivMul _ _ _ _ hm hPx
  have hb := hasDerivSub (fun t => (F.incidence t).y)
    (fun t => ((F.outgoing t).1.y / (F.outgoing t).1.x) * (F.incidence t).x)
    rayData.pointDerivative.y
    (dm * (F.incidence θ).x +
      ((F.outgoing θ).1.y / (F.outgoing θ).1.x) * rayData.pointDerivative.x)
    hPy hmp
  constructor
  · simpa only [nonverticalLineCoefficients, LineCoefficients.slope] using hm
  · convert hb using 1 <;>
      simp only [nonverticalLineCoefficients, LineCoefficients.intercept, dm] <;>
      ring

/-- Epsilon-delta little-o of the identity at zero. -/
def IsLittleOAtZero (r : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ h : ℝ, 0 < |h| → |h| < δ → |r h| ≤ ε * |h|

/-- Exact first-order expansion with a little-o remainder on an explicit domain. -/
def HasFirstOrderExpansionOn (D : Set ℝ) (f : ℝ → ℝ) (θ f' : ℝ)
    (r : ℝ → ℝ) : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧
    (∀ h : ℝ, |h| < δ₀ → θ + h ∈ D) ∧
    (∀ h : ℝ, |h| < δ₀ → f (θ + h) = f θ + f' * h + r h) ∧
    IsLittleOAtZero r

/-- Simultaneous first-order expansions of slope and intercept. -/
def HasCoefficientFirstOrderExpansion (D : Set ℝ) (m b : ℝ → ℝ) (θ : ℝ)
    (data : CoefficientDerivativeData) (rm rb : ℝ → ℝ) : Prop :=
  HasCoefficientDerivativesAt m b θ data ∧
    HasFirstOrderExpansionOn D m θ data.slopeDerivative rm ∧
    HasFirstOrderExpansionOn D b θ data.interceptDerivative rb

/-- Derivative equalities at an interior point supply exact little-o remainders. -/
theorem hasFirstOrderExpansion_of_hasDeriv (D : Set ℝ) (m b : ℝ → ℝ) (θ : ℝ)
    (data : CoefficientDerivativeData) (hOpen : IsOpen D) (hθ : θ ∈ D)
    (hDeriv : HasCoefficientDerivativesAt m b θ data) :
    ∃ rm rb : ℝ → ℝ,
      HasCoefficientFirstOrderExpansion D m b θ data rm rb := by
  have derivativeLittle (f : ℝ → ℝ) (f' : ℝ) (hf : HasDerivAt f f' θ) :
      IsLittleOAtZero (fun h => f (θ + h) - f θ - f' * h) := by
    intro ε hε
    have ho := hasDerivAt_iff_isLittleO_nhds_zero.mp hf
    have hev : ∀ᶠ h in nhds (0 : ℝ),
        |f (θ + h) - f θ - f' * h| ≤ ε * |h| := by
      filter_upwards [Asymptotics.isLittleO_iff.mp ho hε] with h hh
      simpa only [Real.norm_eq_abs, smul_eq_mul, mul_comm] using hh
    rcases Metric.eventually_nhds_iff.mp hev with ⟨δ, hδ, hall⟩
    refine ⟨δ, hδ, ?_⟩
    intro h _hhpos hhδ
    apply hall
    simpa only [Real.dist_eq, sub_zero] using hhδ
  rcases Metric.mem_nhds_iff.mp (hOpen.mem_nhds hθ) with ⟨δ, hδ, hball⟩
  let rm := fun h => m (θ + h) - m θ - data.slopeDerivative * h
  let rb := fun h => b (θ + h) - b θ - data.interceptDerivative * h
  refine ⟨rm, rb, hDeriv, ?_, ?_⟩
  · refine ⟨δ, hδ, ?_, ?_, ?_⟩
    · intro h hh
      apply hball
      simpa only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left] using hh
    · intro h _hh
      dsimp only [rm]
      ring
    · exact derivativeLittle m data.slopeDerivative hDeriv.1
  · refine ⟨δ, hδ, ?_, ?_, ?_⟩
    · intro h hh
      apply hball
      simpa only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left] using hh
    · intro h _hh
      dsimp only [rb]
      ring
    · exact derivativeLittle b data.interceptDerivative hDeriv.2

/-! ## Neighboring intersections and the limiting caustic -/

/-- Intersection of two nonparallel neighboring reflected supporting lines. -/
def IsNeighboringIntersection (F : ReflectedRayFamily) (θ h : ℝ) (Q : Point2) : Prop :=
  θ ∈ F.domain ∧ θ + h ∈ F.domain ∧ h ≠ 0 ∧
    directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1 ≠ 0 ∧
    ∃ s t : Length,
      Q = translate (F.incidence θ) (directionDisplacement s (F.outgoing θ).1) ∧
      Q = translate (F.incidence (θ + h))
        (directionDisplacement t (F.outgoing (θ + h)).1)

/-- Determinant formula for the canonical neighboring-line intersection. -/
def neighboringIntersectionPoint (F : ReflectedRayFamily) (θ h : ℝ) : Point2 :=
  let ΔP := displacement (F.incidence θ) (F.incidence (θ + h))
  let s := displacementDirectionDet ΔP (F.outgoing (θ + h)).1 /
    directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1
  translate (F.incidence θ) (directionDisplacement s (F.outgoing θ).1)

/-- Nonzero neighboring determinant gives exactly one supporting-line intersection. -/
theorem neighboringIntersection_existsUnique (F : ReflectedRayFamily) (θ h : ℝ)
    (hθ : θ ∈ F.domain) (hθh : θ + h ∈ F.domain) (hh : h ≠ 0)
    (hdet : directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1 ≠ 0) :
    ∃! Q : Point2, IsNeighboringIntersection F θ h Q := by
  let P := F.incidence θ
  let Ph := F.incidence (θ + h)
  let u := (F.outgoing θ).1
  let v := (F.outgoing (θ + h)).1
  let ΔP := displacement P Ph
  let D := directionDet u v
  let s := displacementDirectionDet ΔP v / D
  let t := displacementDirectionDet ΔP u / D
  have hD : D ≠ 0 := by exact hdet
  have hline : translate P (directionDisplacement s u) =
      translate Ph (directionDisplacement t v) := by
    refine congrArg₂ Point2.mk ?_ ?_
    · dsimp only [translate, directionDisplacement, s, t, ΔP, displacement,
        displacementDirectionDet]
      field_simp [hD]
      dsimp only [D, directionDet]
      ring
    · dsimp only [translate, directionDisplacement, s, t, ΔP, displacement,
        displacementDirectionDet]
      field_simp [hD]
      dsimp only [D, directionDet]
      ring
  let Q := neighboringIntersectionPoint F θ h
  have hQfirst : Q = translate P (directionDisplacement s u) := by rfl
  have hQsecond : Q = translate Ph (directionDisplacement t v) :=
    hQfirst.trans hline
  refine ⟨Q, ⟨hθ, hθh, hh, hdet, s, t, hQfirst, hQsecond⟩, ?_⟩
  intro Y hY
  rcases hY.2.2.2.2 with ⟨sy, ty, hy1, hy2⟩
  have hxy : translate P (directionDisplacement sy u) =
      translate Ph (directionDisplacement ty v) := hy1.symm.trans hy2
  have hx := congrArg Point2.x hxy
  have hy := congrArg Point2.y hxy
  have hs : sy = s := by
    dsimp only [translate, directionDisplacement, P, Ph, u, v] at hx hy
    dsimp only [s, ΔP, displacement, displacementDirectionDet]
    apply (eq_div_iff hD).2
    dsimp only [D, directionDet, u, v] at hD ⊢
    linear_combination (F.outgoing (θ + h)).1.y * hx -
      (F.outgoing (θ + h)).1.x * hy
  rw [hy1, hs]
  exact hQfirst.symm

/-- Punctured-neighborhood nondegeneracy of neighboring ray directions. -/
def IsLocallyNondegenerate (F : ReflectedRayFamily) (θ : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
    θ + h ∈ F.domain ∧
      directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1 ≠ 0

/-- First-order determinant expansion from the outgoing-direction derivative. -/
theorem neighboringDet_firstOrder (F : ReflectedRayFamily) (θ : ℝ)
    (data : RayDerivativeData) (hDeriv : HasRayDerivativesAt F θ data) :
    ∃ rdet : ℝ → ℝ, IsLittleOAtZero rdet ∧ ∀ h : ℝ,
      directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1 =
        h * directionDet (F.outgoing θ).1 data.directionDerivative + rdet h := by
  rcases hDeriv with ⟨_hθ, _hPx, _hPy, hDx, hDy⟩
  let rx := fun h : ℝ => (F.outgoing (θ + h)).1.x - (F.outgoing θ).1.x -
    h * data.directionDerivative.x
  let ry := fun h : ℝ => (F.outgoing (θ + h)).1.y - (F.outgoing θ).1.y -
    h * data.directionDerivative.y
  have hrx : rx =o[nhds 0] (fun h : ℝ => h) := by
    simpa only [rx, smul_eq_mul] using
      (hasDerivAt_iff_isLittleO_nhds_zero.mp hDx)
  have hry : ry =o[nhds 0] (fun h : ℝ => h) := by
    simpa only [ry, smul_eq_mul] using
      (hasDerivAt_iff_isLittleO_nhds_zero.mp hDy)
  let rdet := fun h => (F.outgoing θ).1.x * ry h - (F.outgoing θ).1.y * rx h
  have hrdet : rdet =o[nhds 0] (fun h : ℝ => h) := by
    refine (Asymptotics.isLittleO_iff_tendsto (fun h hh => ?_)).2 ?_
    · subst h
      simp [rdet, rx, ry]
    have ht := (hry.tendsto_div_nhds_zero.const_mul (F.outgoing θ).1.x).sub
      (hrx.tendsto_div_nhds_zero.const_mul (F.outgoing θ).1.y)
    have ht0 : Filter.Tendsto
        (fun h => (F.outgoing θ).1.x * (ry h / h) -
          (F.outgoing θ).1.y * (rx h / h)) (nhds 0) (nhds 0) := by
      simpa only [mul_zero, sub_zero] using ht
    apply Filter.Tendsto.congr' _ ht0
    filter_upwards with h
    dsimp only [rdet]
    by_cases hh : h = 0
    · subst h
      simp [rx, ry]
    · field_simp [hh]
  have hcustom : IsLittleOAtZero rdet := by
    intro ε hε
    have hev : ∀ᶠ h in nhds (0 : ℝ), |rdet h| ≤ ε * |h| := by
      filter_upwards [Asymptotics.isLittleO_iff.mp hrdet hε] with h hh
      simpa only [Real.norm_eq_abs] using hh
    rcases Metric.eventually_nhds_iff.mp hev with ⟨δ, hδ, hall⟩
    refine ⟨δ, hδ, ?_⟩
    intro h _hhpos hhδ
    apply hall
    simpa only [Real.dist_eq, sub_zero] using hhδ
  refine ⟨rdet, hcustom, ?_⟩
  intro h
  dsimp only [rdet, rx, ry, directionDet]
  ring

/-- A nonzero turning determinant makes sufficiently close neighboring rays nonparallel. -/
theorem locallyNondegenerate_of_turning (F : ReflectedRayFamily) (θ : ℝ)
    (data : RayDerivativeData) (hDiff : DifferentiableReflectedRayFamily F)
    (hDeriv : HasRayDerivativesAt F θ data)
    (hTurn : directionDet (F.outgoing θ).1 data.directionDerivative ≠ 0) :
    IsLocallyNondegenerate F θ := by
  let K := directionDet (F.outgoing θ).1 data.directionDerivative
  have hK : K ≠ 0 := hTurn
  have hKabs : 0 < |K| := abs_pos.mpr hK
  rcases neighboringDet_firstOrder F θ data hDeriv with ⟨r, hr, hexp⟩
  rcases hr (|K| / 2) (by positivity) with ⟨δr, hδr, hrbound⟩
  rcases Metric.mem_nhds_iff.mp (hDiff.1.mem_nhds hDeriv.1) with
    ⟨δD, hδD, hDball⟩
  refine ⟨min δr δD, lt_min hδr hδD, ?_⟩
  intro h hhpos hhsmall
  have hhr : |h| < δr := lt_of_lt_of_le hhsmall (min_le_left _ _)
  have hhD : |h| < δD := lt_of_lt_of_le hhsmall (min_le_right _ _)
  constructor
  · apply hDball
    simpa only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left] using hhD
  · have hrb := hrbound h hhpos hhr
    have he := hexp h
    intro hzero
    rw [hzero] at he
    have hre : r h = -(h * K) := by linarith
    have habsr : |r h| = |h| * |K| := by
      rw [hre, abs_neg, abs_mul]
    rw [habsr] at hrb
    have hprod : 0 < |h| * |K| := mul_pos hhpos hKabs
    nlinarith

/-- Differential envelope point obtained from ray derivative data. -/
def differentialCausticPoint (F : ReflectedRayFamily) (θ : ℝ)
    (data : RayDerivativeData)
    (_hTurn : directionDet (F.outgoing θ).1 data.directionDerivative ≠ 0) : Point2 :=
  let envelopeParameter :=
    displacementDirectionDet data.pointDerivative (F.outgoing θ).1 /
    directionDet (F.outgoing θ).1 data.directionDerivative
  translate (F.incidence θ)
    (directionDisplacement envelopeParameter (F.outgoing θ).1)

/-- Epsilon-delta limit of canonical neighboring-line intersections. -/
def IsLimitingCausticPoint (F : ReflectedRayFamily) (θ : ℝ) (C : Point2) : Prop :=
  θ ∈ F.domain ∧ IsLocallyNondegenerate F θ ∧
    ∀ ε : Length, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, 0 < |h| → |h| < δ →
        displacementNormSq (displacement C (neighboringIntersectionPoint F θ h)) < ε ^ 2

/-- Neighboring intersections converge to the differential caustic point. -/
theorem differentialCausticPoint_isLimit (F : ReflectedRayFamily) (θ : ℝ)
    (data : RayDerivativeData) (hDiff : DifferentiableReflectedRayFamily F)
    (hDeriv : HasRayDerivativesAt F θ data)
    (hTurn : directionDet (F.outgoing θ).1 data.directionDerivative ≠ 0) :
    IsLimitingCausticPoint F θ (differentialCausticPoint F θ data hTurn) := by
  let L := nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)
  have hL : L ≤ nhds (0 : ℝ) := by
    dsimp only [L, nhdsWithin]
    exact inf_le_left
  have hLne : ∀ᶠ h in L, h ≠ 0 := by
    have hm : ∀ᶠ h in L, h ∈ ({0}ᶜ : Set ℝ) := by
      dsimp only [L]
      exact self_mem_nhdsWithin
    filter_upwards [hm] with h hh
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
  have hshift : Filter.Tendsto (fun h : ℝ => θ + h) (nhds 0) (nhds θ) := by
    simpa only [add_zero] using
      (Filter.Tendsto.add
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => θ) (nhds 0) (nhds θ))
        (show Filter.Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0) from
          continuousAt_id.tendsto))
  have diffQuot (f : ℝ → ℝ) (f' : ℝ) (hf : HasDerivAt f f' θ) :
      Filter.Tendsto (fun h => (f (θ + h) - f θ) / h) L (nhds f') := by
    let r := fun h : ℝ => f (θ + h) - f θ - h * f'
    have hr : r =o[nhds 0] (fun h : ℝ => h) := by
      simpa only [r, smul_eq_mul] using
        (hasDerivAt_iff_isLittleO_nhds_zero.mp hf)
    have ht : Filter.Tendsto (fun h => f' + r h / h) L (nhds f') := by
      have hrt := hr.tendsto_div_nhds_zero.mono_left hL
      simpa only [add_zero] using
        (Filter.Tendsto.add
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => f') L (nhds f')) hrt)
    apply Filter.Tendsto.congr' _ ht
    filter_upwards [hLne] with h hh
    dsimp only [r]
    field_simp [hh]
    ring
  rcases hDeriv with ⟨hθ, hPx, hPy, hDx, hDy⟩
  have hqPx := diffQuot (fun t => (F.incidence t).x) data.pointDerivative.x hPx
  have hqPy := diffQuot (fun t => (F.incidence t).y) data.pointDerivative.y hPy
  have hqDx := diffQuot (fun t => (F.outgoing t).1.x) data.directionDerivative.x hDx
  have hqDy := diffQuot (fun t => (F.outgoing t).1.y) data.directionDerivative.y hDy
  have hdX : Filter.Tendsto (fun h => (F.outgoing (θ + h)).1.x) L
      (nhds (F.outgoing θ).1.x) :=
    (hDx.continuousAt.tendsto.comp hshift).mono_left hL
  have hdY : Filter.Tendsto (fun h => (F.outgoing (θ + h)).1.y) L
      (nhds (F.outgoing θ).1.y) :=
    (hDy.continuousAt.tendsto.comp hshift).mono_left hL
  let N := fun h => displacementDirectionDet
    (displacement (F.incidence θ) (F.incidence (θ + h))) (F.outgoing (θ + h)).1
  let D := fun h => directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1
  let A := displacementDirectionDet data.pointDerivative (F.outgoing θ).1
  let K := directionDet (F.outgoing θ).1 data.directionDerivative
  have hNq : Filter.Tendsto (fun h => N h / h) L (nhds A) := by
    have ht := (hqPx.mul hdY).sub (hqPy.mul hdX)
    apply Filter.Tendsto.congr' _ ht
    filter_upwards [hLne] with h hh
    dsimp only [N, A, displacementDirectionDet, displacement]
    field_simp [hh]
  have hDq : Filter.Tendsto (fun h => D h / h) L (nhds K) := by
    have ht := (hqDy.const_mul (F.outgoing θ).1.x).sub
      (hqDx.const_mul (F.outgoing θ).1.y)
    apply Filter.Tendsto.congr' _ ht
    filter_upwards [hLne] with h hh
    dsimp only [D, K, directionDet]
    field_simp [hh]
    ring
  let sfun := fun h => N h / D h
  let lam := A / K
  have hs : Filter.Tendsto sfun L (nhds lam) := by
    have hquot := hNq.div hDq hTurn
    apply Filter.Tendsto.congr' _ hquot
    filter_upwards [hLne] with h hh
    dsimp only [sfun]
    change (N h / h) / (D h / h) = N h / D h
    by_cases hDh : D h = 0
    · simp [hDh]
    · field_simp [hh, hDh]
  have hnorm : Filter.Tendsto
      (fun h => displacementNormSq (displacement
        (differentialCausticPoint F θ data hTurn)
        (neighboringIntersectionPoint F θ h))) L (nhds 0) := by
    have ht := (hs.sub
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => lam) L (nhds lam))).pow 2
    have ht0 : Filter.Tendsto (fun h => (sfun h - lam) ^ 2) L (nhds 0) := by
      simpa using ht
    apply Filter.Tendsto.congr' _ ht0
    filter_upwards with h
    dsimp only [sfun, lam, N, D, A, K, differentialCausticPoint,
      neighboringIntersectionPoint, displacementNormSq, displacement, translate,
      directionDisplacement]
    have hu := (F.outgoing θ).2
    dsimp only [directionNormSq, directionDot] at hu
    nlinarith
  refine ⟨hθ, locallyNondegenerate_of_turning F θ data hDiff
    ⟨hθ, hPx, hPy, hDx, hDy⟩ hTurn, ?_⟩
  intro ε hε
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hev : ∀ᶠ h in L,
      displacementNormSq (displacement
        (differentialCausticPoint F θ data hTurn)
        (neighboringIntersectionPoint F θ h)) < ε ^ 2 :=
    hnorm.eventually (Iio_mem_nhds hεsq)
  have hmem : {h : ℝ | displacementNormSq (displacement
        (differentialCausticPoint F θ data hTurn)
        (neighboringIntersectionPoint F θ h)) < ε ^ 2} ∈ L := hev
  rcases Metric.mem_nhdsWithin_iff.mp hmem with ⟨δ, hδ, hsub⟩
  refine ⟨δ, hδ, ?_⟩
  intro h hhpos hhδ
  apply hsub
  constructor
  · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hhδ
  · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (abs_pos.mp hhpos)

/-- A neighboring supporting-line intersection lying on both forward rays. -/
def IsForwardNeighboringIntersection (F : ReflectedRayFamily) (θ h : ℝ)
    (Q : Point2) : Prop :=
  IsNeighboringIntersection F θ h Q ∧
    ∃ s t : Length, 0 ≤ s ∧ 0 ≤ t ∧
      Q = translate (F.incidence θ) (directionDisplacement s (F.outgoing θ).1) ∧
      Q = translate (F.incidence (θ + h))
        (directionDisplacement t (F.outgoing (θ + h)).1)

/-- A limiting supporting-line caustic whose base and neighboring points lie on forward rays. -/
def IsForwardLimitingCausticPoint (F : ReflectedRayFamily) (θ : ℝ)
    (C : Point2) : Prop :=
  IsLimitingCausticPoint F θ C ∧
    (∃ s : Length, 0 ≤ s ∧
      C = translate (F.incidence θ) (directionDisplacement s (F.outgoing θ).1)) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
      θ + h ∈ F.domain ∧
        directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1 ≠ 0 ∧
        IsForwardNeighboringIntersection F θ h (neighboringIntersectionPoint F θ h)

/-- A positive differential envelope distance selects the physical forward branch. -/
theorem forwardCaustic_of_positive_parameter (F : ReflectedRayFamily) (θ : ℝ)
    (data : RayDerivativeData) (hDiff : DifferentiableReflectedRayFamily F)
    (hDeriv : HasRayDerivativesAt F θ data)
    (hTurn : directionDet (F.outgoing θ).1 data.directionDerivative ≠ 0)
    (hParameter : 0 < displacementDirectionDet data.pointDerivative (F.outgoing θ).1 /
      directionDet (F.outgoing θ).1 data.directionDerivative) :
    IsForwardLimitingCausticPoint F θ
      (differentialCausticPoint F θ data hTurn) := by
  let L := nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)
  have hL : L ≤ nhds (0 : ℝ) := by
    dsimp only [L, nhdsWithin]
    exact inf_le_left
  have hLne : ∀ᶠ h in L, h ≠ 0 := by
    have hm : ∀ᶠ h in L, h ∈ ({0}ᶜ : Set ℝ) := by
      dsimp only [L]
      exact self_mem_nhdsWithin
    filter_upwards [hm] with h hh
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
  have hshift : Filter.Tendsto (fun h : ℝ => θ + h) (nhds 0) (nhds θ) := by
    simpa only [add_zero] using
      (Filter.Tendsto.add
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => θ) (nhds 0) (nhds θ))
        (show Filter.Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0) from
          continuousAt_id.tendsto))
  have diffQuot (f : ℝ → ℝ) (f' : ℝ) (hf : HasDerivAt f f' θ) :
      Filter.Tendsto (fun h => (f (θ + h) - f θ) / h) L (nhds f') := by
    let r := fun h : ℝ => f (θ + h) - f θ - h * f'
    have hr : r =o[nhds 0] (fun h : ℝ => h) := by
      simpa only [r, smul_eq_mul] using
        (hasDerivAt_iff_isLittleO_nhds_zero.mp hf)
    have ht : Filter.Tendsto (fun h => f' + r h / h) L (nhds f') := by
      have hrt := hr.tendsto_div_nhds_zero.mono_left hL
      simpa only [add_zero] using
        (Filter.Tendsto.add
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => f') L (nhds f')) hrt)
    apply Filter.Tendsto.congr' _ ht
    filter_upwards [hLne] with h hh
    dsimp only [r]
    field_simp [hh]
    ring
  rcases hDeriv with ⟨hθ, hPx, hPy, hDx, hDy⟩
  have hqPx := diffQuot (fun t => (F.incidence t).x) data.pointDerivative.x hPx
  have hqPy := diffQuot (fun t => (F.incidence t).y) data.pointDerivative.y hPy
  have hqDx := diffQuot (fun t => (F.outgoing t).1.x) data.directionDerivative.x hDx
  have hqDy := diffQuot (fun t => (F.outgoing t).1.y) data.directionDerivative.y hDy
  have hdX : Filter.Tendsto (fun h => (F.outgoing (θ + h)).1.x) L
      (nhds (F.outgoing θ).1.x) :=
    (hDx.continuousAt.tendsto.comp hshift).mono_left hL
  have hdY : Filter.Tendsto (fun h => (F.outgoing (θ + h)).1.y) L
      (nhds (F.outgoing θ).1.y) :=
    (hDy.continuousAt.tendsto.comp hshift).mono_left hL
  let N := fun h => displacementDirectionDet
    (displacement (F.incidence θ) (F.incidence (θ + h))) (F.outgoing (θ + h)).1
  let T := fun h => displacementDirectionDet
    (displacement (F.incidence θ) (F.incidence (θ + h))) (F.outgoing θ).1
  let D := fun h => directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1
  let A := displacementDirectionDet data.pointDerivative (F.outgoing θ).1
  let K := directionDet (F.outgoing θ).1 data.directionDerivative
  have hNq : Filter.Tendsto (fun h => N h / h) L (nhds A) := by
    have ht := (hqPx.mul hdY).sub (hqPy.mul hdX)
    apply Filter.Tendsto.congr' _ ht
    filter_upwards [hLne] with h hh
    dsimp only [N, A, displacementDirectionDet, displacement]
    field_simp [hh]
  have hTq : Filter.Tendsto (fun h => T h / h) L (nhds A) := by
    have ht := (hqPx.mul_const (F.outgoing θ).1.y).sub
      (hqPy.mul_const (F.outgoing θ).1.x)
    apply Filter.Tendsto.congr' _ ht
    filter_upwards [hLne] with h hh
    dsimp only [T, A, displacementDirectionDet, displacement]
    field_simp [hh]
  have hDq : Filter.Tendsto (fun h => D h / h) L (nhds K) := by
    have ht := (hqDy.const_mul (F.outgoing θ).1.x).sub
      (hqDx.const_mul (F.outgoing θ).1.y)
    apply Filter.Tendsto.congr' _ ht
    filter_upwards [hLne] with h hh
    dsimp only [D, K, directionDet]
    field_simp [hh]
    ring
  let sfun := fun h => N h / D h
  let tfun := fun h => T h / D h
  let lam := A / K
  have hs : Filter.Tendsto sfun L (nhds lam) := by
    have hquot := hNq.div hDq hTurn
    apply Filter.Tendsto.congr' _ hquot
    filter_upwards [hLne] with h hh
    dsimp only [sfun]
    change (N h / h) / (D h / h) = N h / D h
    by_cases hDh : D h = 0
    · simp [hDh]
    · field_simp [hh, hDh]
  have ht : Filter.Tendsto tfun L (nhds lam) := by
    have hquot := hTq.div hDq hTurn
    apply Filter.Tendsto.congr' _ hquot
    filter_upwards [hLne] with h hh
    dsimp only [tfun]
    change (T h / h) / (D h / h) = T h / D h
    by_cases hDh : D h = 0
    · simp [hDh]
    · field_simp [hh, hDh]
  have hposEv : ∀ᶠ h in L, 0 < sfun h ∧ 0 < tfun h := by
    filter_upwards [hs.eventually (Ioi_mem_nhds hParameter),
      ht.eventually (Ioi_mem_nhds hParameter)] with h hspos htpos
    exact ⟨hspos, htpos⟩
  have hposMem : {h : ℝ | 0 < sfun h ∧ 0 < tfun h} ∈ L := hposEv
  rcases Metric.mem_nhdsWithin_iff.mp hposMem with ⟨δp, hδp, hpsub⟩
  rcases locallyNondegenerate_of_turning F θ data hDiff
      ⟨hθ, hPx, hPy, hDx, hDy⟩ hTurn with ⟨δn, hδn, hn⟩
  refine ⟨differentialCausticPoint_isLimit F θ data hDiff
      ⟨hθ, hPx, hPy, hDx, hDy⟩ hTurn, ?_, ?_⟩
  · refine ⟨lam, le_of_lt hParameter, ?_⟩
    rfl
  · refine ⟨min δp δn, lt_min hδp hδn, ?_⟩
    intro h hhpos hhsmall
    have hhp : |h| < δp := lt_of_lt_of_le hhsmall (min_le_left _ _)
    have hhn : |h| < δn := lt_of_lt_of_le hhsmall (min_le_right _ _)
    rcases hn h hhpos hhn with ⟨hdom, hdet⟩
    have hstpos : 0 < sfun h ∧ 0 < tfun h := by
      apply hpsub
      constructor
      · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hhp
      · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (abs_pos.mp hhpos)
    let ΔP := displacement (F.incidence θ) (F.incidence (θ + h))
    let Dh := directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1
    let s := displacementDirectionDet ΔP (F.outgoing (θ + h)).1 / Dh
    let t := displacementDirectionDet ΔP (F.outgoing θ).1 / Dh
    have hDh : Dh ≠ 0 := hdet
    have hsfun : s = sfun h := by rfl
    have htfun : t = tfun h := by rfl
    have hspos : 0 < s := by simpa only [hsfun] using hstpos.1
    have htpos : 0 < t := by simpa only [htfun] using hstpos.2
    have hline : translate (F.incidence θ)
        (directionDisplacement s (F.outgoing θ).1) =
        translate (F.incidence (θ + h))
          (directionDisplacement t (F.outgoing (θ + h)).1) := by
      refine congrArg₂ Point2.mk ?_ ?_
      · dsimp only [translate, directionDisplacement, s, t, ΔP, displacement,
          displacementDirectionDet]
        field_simp [hDh]
        dsimp only [Dh, directionDet]
        ring
      · dsimp only [translate, directionDisplacement, s, t, ΔP, displacement,
          displacementDirectionDet]
        field_simp [hDh]
        dsimp only [Dh, directionDet]
        ring
    have hQfirst : neighboringIntersectionPoint F θ h = translate (F.incidence θ)
        (directionDisplacement s (F.outgoing θ).1) := by rfl
    have hQsecond : neighboringIntersectionPoint F θ h =
        translate (F.incidence (θ + h))
          (directionDisplacement t (F.outgoing (θ + h)).1) := hQfirst.trans hline
    refine ⟨hdom, hdet, ?_⟩
    constructor
    · exact ⟨hθ, hdom, abs_pos.mp hhpos, hdet, s, t, hQfirst, hQsecond⟩
    · exact ⟨s, t, le_of_lt hspos, le_of_lt htpos, hQfirst, hQsecond⟩

/-- Slope-intercept coordinates of a neighboring intersection. -/
theorem neighboringIntersection_coefficients (F : ReflectedRayFamily) (θ h : ℝ)
    (c ch : LineCoefficients) (hc : IsReflectedLineCoefficients F θ c)
    (hch : IsReflectedLineCoefficients F (θ + h) ch)
    (hm : ch.slope ≠ c.slope) :
    let Q := neighboringIntersectionPoint F θ h
    Q.x = (ch.intercept - c.intercept) / (c.slope - ch.slope) ∧
      Q.y = c.slope * Q.x + c.intercept ∧
      Q.y = ch.slope * Q.x + ch.intercept := by
  rcases hc with ⟨_hθ, hx, hdy, hP⟩
  rcases hch with ⟨_hθh, hxh, hdyh, hPh⟩
  have hdet : directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1 ≠ 0 := by
    intro hzero
    have hfac : (F.outgoing θ).1.x * (F.outgoing (θ + h)).1.x *
        (ch.slope - c.slope) = 0 := by
      dsimp only [directionDet] at hzero
      rw [hdy, hdyh] at hzero
      linarith
    rcases mul_eq_zero.mp hfac with hxx | hmc
    · exact (mul_ne_zero hx hxh) hxx
    · exact hm (sub_eq_zero.mp hmc)
  let ΔP := displacement (F.incidence θ) (F.incidence (θ + h))
  let D := directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1
  let s := displacementDirectionDet ΔP (F.outgoing (θ + h)).1 / D
  let t := displacementDirectionDet ΔP (F.outgoing θ).1 / D
  have hD : D ≠ 0 := hdet
  have hline : translate (F.incidence θ)
      (directionDisplacement s (F.outgoing θ).1) =
      translate (F.incidence (θ + h))
        (directionDisplacement t (F.outgoing (θ + h)).1) := by
    refine congrArg₂ Point2.mk ?_ ?_
    · dsimp only [translate, directionDisplacement, s, t, ΔP, displacement,
        displacementDirectionDet]
      field_simp [hD]
      dsimp only [D, directionDet]
      ring
    · dsimp only [translate, directionDisplacement, s, t, ΔP, displacement,
        displacementDirectionDet]
      field_simp [hD]
      dsimp only [D, directionDet]
      ring
  let Q := neighboringIntersectionPoint F θ h
  have hQfirst : Q = translate (F.incidence θ)
      (directionDisplacement s (F.outgoing θ).1) := by rfl
  have hQsecond : Q = translate (F.incidence (θ + h))
      (directionDisplacement t (F.outgoing (θ + h)).1) := hQfirst.trans hline
  have hQc : Q.y = c.slope * Q.x + c.intercept := by
    rw [hQfirst]
    dsimp only [translate, directionDisplacement]
    rw [hdy, hP]
    ring
  have hQch : Q.y = ch.slope * Q.x + ch.intercept := by
    rw [hQsecond]
    dsimp only [translate, directionDisplacement]
    rw [hdyh, hPh]
    ring
  dsimp only
  refine ⟨?_, hQc, hQch⟩
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hm))).2
  linarith

/-- Coefficient derivatives characterize the unique limiting caustic coordinates. -/
theorem limitingCaustic_coefficients (F : ReflectedRayFamily) (θ : ℝ)
    (coeff : ℝ → LineCoefficients) (data : CoefficientDerivativeData)
    (hDiff : DifferentiableReflectedRayFamily F) (hθ : θ ∈ F.domain)
    (hCoeff : ∀ t ∈ F.domain, IsReflectedLineCoefficients F t (coeff t))
    (hDeriv : HasCoefficientDerivativesAt (fun t => (coeff t).slope)
      (fun t => (coeff t).intercept) θ data)
    (hm : data.slopeDerivative ≠ 0) :
    ∃! C : Point2,
      IsLimitingCausticPoint F θ C ∧
        C.x = -data.interceptDerivative / data.slopeDerivative ∧
        C.y = (coeff θ).slope * C.x + (coeff θ).intercept := by
  let m := fun t => (coeff t).slope
  let b := fun t => (coeff t).intercept
  let X := -data.interceptDerivative / data.slopeDerivative
  let Y := m θ * X + b θ
  let C : Point2 := { x := X, y := Y }
  let L := nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)
  have hL : L ≤ nhds (0 : ℝ) := by
    dsimp only [L, nhdsWithin]
    exact inf_le_left
  have hLne : ∀ᶠ h in L, h ≠ 0 := by
    have he : ∀ᶠ h in L, h ∈ ({0}ᶜ : Set ℝ) := by
      dsimp only [L]
      exact self_mem_nhdsWithin
    filter_upwards [he] with h hh
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
  have hshift : Filter.Tendsto (fun h : ℝ => θ + h) (nhds 0) (nhds θ) := by
    simpa only [add_zero] using
      (Filter.Tendsto.add
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => θ) (nhds 0) (nhds θ))
        (show Filter.Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0) from
          continuousAt_id.tendsto))
  have diffQuot (f : ℝ → ℝ) (f' : ℝ) (hf : HasDerivAt f f' θ) :
      Filter.Tendsto (fun h => (f (θ + h) - f θ) / h) L (nhds f') := by
    let r := fun h : ℝ => f (θ + h) - f θ - h * f'
    have hr : r =o[nhds 0] (fun h : ℝ => h) := by
      simpa only [r, smul_eq_mul] using
        (hasDerivAt_iff_isLittleO_nhds_zero.mp hf)
    have ht : Filter.Tendsto (fun h => f' + r h / h) L (nhds f') := by
      have hrt := hr.tendsto_div_nhds_zero.mono_left hL
      simpa only [add_zero] using
        (Filter.Tendsto.add
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => f') L (nhds f')) hrt)
    apply Filter.Tendsto.congr' _ ht
    filter_upwards [hLne] with h hh
    dsimp only [r]
    field_simp [hh]
    ring
  have hmq := diffQuot m data.slopeDerivative hDeriv.1
  have hbq := diffQuot b data.interceptDerivative hDeriv.2
  have hdom : ∀ᶠ h in L, θ + h ∈ F.domain :=
    (hshift.mono_left hL).eventually (hDiff.1.mem_nhds hθ)
  have hmqne : ∀ᶠ h in L, (m (θ + h) - m θ) / h ≠ 0 :=
    hmq.eventually (eventually_ne_nhds hm)
  have hmslope : ∀ᶠ h in L, m (θ + h) ≠ m θ := by
    filter_upwards [hmqne] with h hne
    intro heq
    rw [heq, sub_self, zero_div] at hne
    exact hne rfl
  have det_ne (h : ℝ) (hhdom : θ + h ∈ F.domain)
      (hms : m (θ + h) ≠ m θ) :
      directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1 ≠ 0 := by
    rcases (hCoeff θ hθ).2 with ⟨hx, hdy, _hP⟩
    rcases (hCoeff (θ + h) hhdom).2 with ⟨hxh, hdyh, _hPh⟩
    intro hzero
    have hfac : (F.outgoing θ).1.x * (F.outgoing (θ + h)).1.x *
        (m (θ + h) - m θ) = 0 := by
      dsimp only [directionDet] at hzero
      change (F.outgoing θ).1.y = m θ * (F.outgoing θ).1.x at hdy
      change (F.outgoing (θ + h)).1.y =
        m (θ + h) * (F.outgoing (θ + h)).1.x at hdyh
      rw [hdy, hdyh] at hzero
      linarith
    rcases mul_eq_zero.mp hfac with hxx | hsl
    · exact (mul_ne_zero hx hxh) hxx
    · exact hms (sub_eq_zero.mp hsl)
  have hlocal : IsLocallyNondegenerate F θ := by
    have hgood : ∀ᶠ h in L, θ + h ∈ F.domain ∧
        directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1 ≠ 0 := by
      filter_upwards [hdom, hmslope] with h hd hs
      exact ⟨hd, det_ne h hd hs⟩
    have hmem : {h : ℝ | θ + h ∈ F.domain ∧
        directionDet (F.outgoing θ).1 (F.outgoing (θ + h)).1 ≠ 0} ∈ L := hgood
    rcases Metric.mem_nhdsWithin_iff.mp hmem with ⟨δ, hδ, hsub⟩
    refine ⟨δ, hδ, ?_⟩
    intro h hhpos hhδ
    apply hsub
    constructor
    · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hhδ
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (abs_pos.mp hhpos)
  let xfun := fun h => -(((b (θ + h) - b θ) / h) /
    ((m (θ + h) - m θ) / h))
  have hxlim : Filter.Tendsto xfun L (nhds X) := by
    have hdiv : Filter.Tendsto
        (fun h => ((b (θ + h) - b θ) / h) / ((m (θ + h) - m θ) / h))
        L (nhds (data.interceptDerivative / data.slopeDerivative)) := by
      simpa only [div_eq_mul_inv] using hbq.mul (hmq.inv₀ hm)
    have ht : Filter.Tendsto xfun L
        (nhds (-(data.interceptDerivative / data.slopeDerivative))) := by
      simpa only [xfun] using hdiv.neg
    have htarget : -(data.interceptDerivative / data.slopeDerivative) = X := by
      dsimp only [X]
      field_simp [hm]
    rw [← htarget]
    exact ht
  have hQx : Filter.Tendsto (fun h => (neighboringIntersectionPoint F θ h).x)
      L (nhds X) := by
    apply Filter.Tendsto.congr' _ hxlim
    filter_upwards [hLne, hdom, hmslope] with h hh hd hs
    have hi := neighboringIntersection_coefficients F θ h (coeff θ) (coeff (θ + h))
      (hCoeff θ hθ) (hCoeff (θ + h) hd) hs
    dsimp only at hi
    rw [hi.1]
    dsimp only [xfun, m, b]
    rw [div_div_div_cancel_right₀ hh,
      show (coeff θ).slope - (coeff (θ + h)).slope =
      -((coeff (θ + h)).slope - (coeff θ).slope) by ring, div_neg,
      neg_inj]
  have hQy : Filter.Tendsto (fun h => (neighboringIntersectionPoint F θ h).y)
      L (nhds Y) := by
    have ht : Filter.Tendsto
        (fun h => m θ * (neighboringIntersectionPoint F θ h).x + b θ)
        L (nhds Y) := by
      dsimp only [Y]
      exact (hQx.const_mul (m θ)).add_const (b θ)
    apply Filter.Tendsto.congr' _ ht
    filter_upwards [hdom, hmslope] with h hd hs
    have hi := neighboringIntersection_coefficients F θ h (coeff θ) (coeff (θ + h))
      (hCoeff θ hθ) (hCoeff (θ + h) hd) hs
    simpa only [m, b] using hi.2.1.symm
  have hnorm : Filter.Tendsto (fun h => displacementNormSq
      (displacement C (neighboringIntersectionPoint F θ h))) L (nhds 0) := by
    have hx0 := hQx.sub
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => X) L (nhds X))
    have hy0 := hQy.sub
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => Y) L (nhds Y))
    have ht := (hx0.pow 2).add (hy0.pow 2)
    simpa [C, displacementNormSq, displacement] using ht
  have hlimit : IsLimitingCausticPoint F θ C := by
    refine ⟨hθ, hlocal, ?_⟩
    intro ε hε
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hev : ∀ᶠ h in L, displacementNormSq
        (displacement C (neighboringIntersectionPoint F θ h)) < ε ^ 2 :=
      hnorm.eventually (Iio_mem_nhds hεsq)
    have hmem : {h : ℝ | displacementNormSq
        (displacement C (neighboringIntersectionPoint F θ h)) < ε ^ 2} ∈ L := hev
    rcases Metric.mem_nhdsWithin_iff.mp hmem with ⟨δ, hδ, hsub⟩
    refine ⟨δ, hδ, ?_⟩
    intro h hhpos hhδ
    apply hsub
    constructor
    · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hhδ
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (abs_pos.mp hhpos)
  refine ⟨C, ⟨hlimit, ?_, ?_⟩, ?_⟩
  · rfl
  · rfl
  · intro Z hZ
    refine congrArg₂ Point2.mk ?_ ?_
    · simpa only [C, X] using hZ.2.1
    · rw [hZ.2.2, hZ.2.1]

/-- The axial reflected family is differentiable on the strict non-rim domain. -/
theorem axialReflectedRayFamily_differentiable (c : Circle) (o : VerticalOrientation) :
    DifferentiableReflectedRayFamily (axialReflectedRayFamily c o) := by
  unfold DifferentiableReflectedRayFamily
  constructor
  · exact isOpen_lt (continuous_abs.comp continuous_id)
      (continuous_const.div_const 2)
  constructor
  · change DifferentiableOn ℝ (fun θ : ℝ => c.center.x + c.radius * Real.sin θ)
      {θ | InAxialIncidenceDomain θ}
    exact ((differentiable_const _).add
      (Real.differentiable_sin.const_mul c.radius)).differentiableOn
  constructor
  · change DifferentiableOn ℝ (fun θ : ℝ =>
      c.center.y + orientationSign o * c.radius * Real.cos θ)
      {θ | InAxialIncidenceDomain θ}
    exact ((differentiable_const _).add
      (Real.differentiable_cos.const_mul
        (orientationSign o * c.radius))).differentiableOn
  constructor
  · change DifferentiableOn ℝ (fun θ : ℝ =>
      (reflectedDirection (axisDirection o).1
        (⟨(semicirclePoint c o θ).2, by
          cases o <;>
            simp only [semicirclePoint, directionNormSq, directionDot, orientationSign,
              one_mul, neg_mul] <;>
            nlinarith [Real.sin_sq_add_cos_sq θ]⟩ : UnitDirection)).x)
      {θ | InAxialIncidenceDomain θ}
    dsimp only [reflectedDirection, subtractDirection, scaleDirection, directionDot,
      axisDirection, semicirclePoint]
    have hd0 : Differentiable ℝ (fun θ : ℝ =>
        0 - 2 * (0 * Real.sin θ + (orientationSign o * orientationSign o) *
          Real.cos θ) * Real.sin θ) :=
      (differentiable_const (c := (0 : ℝ))).sub
        (((Real.differentiable_sin.const_mul 0).add
          (Real.differentiable_cos.const_mul
            (orientationSign o * orientationSign o))).const_mul 2 |>.mul
              Real.differentiable_sin)
    have heq : (fun θ : ℝ =>
        0 - 2 * (0 * Real.sin θ + (orientationSign o * orientationSign o) *
          Real.cos θ) * Real.sin θ) =
        (fun θ : ℝ => 0 - 2 * (0 * Real.sin θ + orientationSign o *
          (orientationSign o * Real.cos θ)) * Real.sin θ) := by
      funext θ
      ring
    rw [heq] at hd0
    exact hd0.differentiableOn
  · change DifferentiableOn ℝ (fun θ : ℝ =>
      (reflectedDirection (axisDirection o).1
        (⟨(semicirclePoint c o θ).2, by
          cases o <;>
            simp only [semicirclePoint, directionNormSq, directionDot, orientationSign,
              one_mul, neg_mul] <;>
            nlinarith [Real.sin_sq_add_cos_sq θ]⟩ : UnitDirection)).y)
      {θ | InAxialIncidenceDomain θ}
    dsimp only [reflectedDirection, subtractDirection, scaleDirection, directionDot,
      axisDirection, semicirclePoint]
    have hd0 : Differentiable ℝ (fun θ : ℝ =>
        orientationSign o - 2 * (0 * Real.sin θ +
          (orientationSign o * orientationSign o) * Real.cos θ) *
            (orientationSign o * Real.cos θ)) :=
      (differentiable_const (c := orientationSign o)).sub
        (((Real.differentiable_sin.const_mul 0).add
          (Real.differentiable_cos.const_mul
            (orientationSign o * orientationSign o))).const_mul 2 |>.mul
              (Real.differentiable_cos.const_mul (orientationSign o)))
    have heq : (fun θ : ℝ =>
        orientationSign o - 2 * (0 * Real.sin θ +
          (orientationSign o * orientationSign o) * Real.cos θ) *
            (orientationSign o * Real.cos θ)) =
        (fun θ : ℝ => orientationSign o - 2 *
          (0 * Real.sin θ + orientationSign o * (orientationSign o * Real.cos θ)) *
            (orientationSign o * Real.cos θ)) := by
      funext θ
      ring
    rw [heq] at hd0
    exact hd0.differentiableOn

/-! ## Normalized one-sided small-angle caustic asymptotics -/

/-- Positive coherent-SI horizontal and vertical normalization scales. -/
structure CausticScales where
  horizontal : Length
  vertical : Length
  horizontal_pos : IsPositiveLength horizontal
  vertical_pos : IsPositiveLength vertical

/-- Coprime positive numerator and denominator for a rational exponent. -/
structure ReducedPositiveExponent where
  numerator : ℕ
  denominator : ℕ
  numerator_pos : 0 < numerator
  denominator_pos : 0 < denominator
  coprime : Nat.Coprime numerator denominator

/-- Real value of a reduced positive rational exponent. -/
def ReducedPositiveExponent.value (r : ReducedPositiveExponent) : ℝ :=
  (r.numerator : ℝ) / (r.denominator : ℝ)

/-- Offset, nonzero normalized amplitude, and reduced rational power. -/
structure CausticAsymptoticData where
  offset : Length
  amplitude : ℝ
  amplitude_ne_zero : amplitude ≠ 0
  exponent : ReducedPositiveExponent

/-- Relative small-angle power law on the physical positive caustic branch. -/
def IsSmallAngleCausticAsymptotic (F : ReflectedRayFamily) (C : ℝ → Point2)
    (scales : CausticScales) (data : CausticAsymptoticData) : Prop :=
  let ξ := fun θ => |(C θ).x - F.mirror.center.x| / scales.horizontal
  let η := fun θ => ((C θ).y - data.offset) / scales.vertical
  (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ θ : ℝ, 0 < θ → θ < δ₀ →
      θ ∈ F.domain ∧ IsForwardLimitingCausticPoint F θ (C θ) ∧ 0 < ξ θ) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ,
      0 < θ → θ < δ → ξ θ < ε) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ,
      0 < θ → θ < δ →
        |η θ - data.amplitude * Real.rpow (ξ θ) data.exponent.value| ≤
          ε * Real.rpow (ξ θ) data.exponent.value

/-- Nonzero one-sided leading amplitude and reduced positive rational order. -/
def HasLeadingPowerAtZero (D : Set ℝ) (f : ℝ → ℝ) (A : ℝ)
    (order : ReducedPositiveExponent) : Prop :=
  (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ θ : ℝ, 0 < θ → θ < δ₀ → θ ∈ D) ∧
    A ≠ 0 ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ,
      0 < θ → θ < δ →
        |f θ / (A * Real.rpow θ order.value) - 1| < ε

/-- Eliminate a positive small parameter between two rational leading powers. -/
theorem smallAngleAsymptotic_of_leadingPowers (F : ReflectedRayFamily)
    (C : ℝ → Point2) (scales : CausticScales) (offset : Length)
    (horizontalAmplitude verticalAmplitude : ℝ)
    (horizontalOrder verticalOrder : ReducedPositiveExponent)
    (hBranch : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ θ : ℝ, 0 < θ → θ < δ₀ →
      θ ∈ F.domain ∧ IsForwardLimitingCausticPoint F θ (C θ))
    (hHorizontal : HasLeadingPowerAtZero F.domain
      (fun θ => |(C θ).x - F.mirror.center.x| / scales.horizontal)
      horizontalAmplitude horizontalOrder)
    (hHorizontalPositive : 0 < horizontalAmplitude)
    (hVertical : HasLeadingPowerAtZero F.domain
      (fun θ => ((C θ).y - offset) / scales.vertical)
      verticalAmplitude verticalOrder) :
    ∃ data : CausticAsymptoticData,
      data.offset = offset ∧
        data.exponent.value = verticalOrder.value / horizontalOrder.value ∧
        data.amplitude = verticalAmplitude /
          Real.rpow horizontalAmplitude
            (verticalOrder.value / horizontalOrder.value) ∧
        IsSmallAngleCausticAsymptotic F C scales data := by
  let n := verticalOrder.numerator * horizontalOrder.denominator
  let d := verticalOrder.denominator * horizontalOrder.numerator
  let g := Nat.gcd n d
  have hn : 0 < n := Nat.mul_pos verticalOrder.numerator_pos
    horizontalOrder.denominator_pos
  have hd : 0 < d := Nat.mul_pos verticalOrder.denominator_pos
    horizontalOrder.numerator_pos
  have hg : 0 < g := Nat.pos_of_ne_zero
    (Nat.gcd_ne_zero_left (Nat.ne_of_gt hn))
  have hgn : g ≤ n := Nat.gcd_le_left d hn
  have hgd : g ≤ d := Nat.gcd_le_right n hd
  let exponent : ReducedPositiveExponent :=
    { numerator := n / g
      denominator := d / g
      numerator_pos := Nat.div_pos hgn hg
      denominator_pos := Nat.div_pos hgd hg
      coprime := Nat.coprime_div_gcd_div_gcd hg }
  have hexponent : exponent.value = verticalOrder.value / horizontalOrder.value := by
    dsimp only [ReducedPositiveExponent.value, exponent]
    have hgR : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hg)
    rw [Nat.cast_div (Nat.gcd_dvd_left n d) hgR,
      Nat.cast_div (Nat.gcd_dvd_right n d) hgR,
      div_div_div_cancel_right₀ hgR]
    dsimp only [n, d]
    push_cast
    field_simp [Nat.cast_ne_zero.mpr
        (Nat.ne_of_gt horizontalOrder.denominator_pos),
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt verticalOrder.denominator_pos),
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt horizontalOrder.numerator_pos)]
  let α := horizontalOrder.value
  let β := verticalOrder.value
  let γ := exponent.value
  have hα : 0 < α := by
    exact div_pos (Nat.cast_pos.mpr horizontalOrder.numerator_pos)
      (Nat.cast_pos.mpr horizontalOrder.denominator_pos)
  have hβ : 0 < β := by
    exact div_pos (Nat.cast_pos.mpr verticalOrder.numerator_pos)
      (Nat.cast_pos.mpr verticalOrder.denominator_pos)
  have hγ : 0 < γ := by
    dsimp only [γ]
    rw [hexponent]
    exact div_pos hβ hα
  have hαγ : α * γ = β := by
    dsimp only [γ]
    rw [hexponent]
    exact mul_div_cancel₀ β (ne_of_gt hα)
  let ξ := fun θ => |(C θ).x - F.mirror.center.x| / scales.horizontal
  let η := fun θ => ((C θ).y - offset) / scales.vertical
  let L := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have ratioTendsto (f : ℝ → ℝ) (A : ℝ) (order : ReducedPositiveExponent)
      (h : HasLeadingPowerAtZero F.domain f A order) :
      Filter.Tendsto (fun θ => f θ / (A * Real.rpow θ order.value))
        L (nhds 1) := by
    apply Metric.tendsto_nhdsWithin_nhds.mpr
    intro ε hε
    rcases h.2.2 ε hε with ⟨δ, hδ, hb⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hx hxd
    have hxpos : 0 < x := hx
    have hxlt : x < δ := by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos hxpos] using hxd
    simpa only [Real.dist_eq] using hb x hxpos hxlt
  let Rx := fun θ => ξ θ / (horizontalAmplitude * Real.rpow θ α)
  let Ry := fun θ => η θ / (verticalAmplitude * Real.rpow θ β)
  have hRx : Filter.Tendsto Rx L (nhds 1) := by
    simpa only [Rx, ξ, α] using ratioTendsto _ _ _ hHorizontal
  have hRy : Filter.Tendsto Ry L (nhds 1) := by
    simpa only [Ry, η, β] using ratioTendsto _ _ _ hVertical
  have hposMem : ∀ᶠ θ in L, 0 < θ := by
    exact self_mem_nhdsWithin
  have hpowα : Filter.Tendsto (fun θ => Real.rpow θ α) L (nhds 0) := by
    have ht := Real.tendsto_exp_atBot.comp
      (Real.tendsto_log_nhdsGT_zero.atBot_mul_const hα)
    apply Filter.Tendsto.congr' _ ht
    filter_upwards [hposMem] with θ hθ
    change Real.exp (Real.log θ * α) = Real.rpow θ α
    calc
      Real.exp (Real.log θ * α) = θ ^ α :=
        (Real.rpow_def_of_pos hθ α).symm
      _ = Real.rpow θ α := (Real.rpow_eq_pow θ α).symm
  have hRxpos : ∀ᶠ θ in L, 0 < Rx θ :=
    hRx.eventually (Ioi_mem_nhds zero_lt_one)
  have hξzero : Filter.Tendsto ξ L (nhds 0) := by
    have ht := (hpowα.const_mul horizontalAmplitude).mul hRx
    have ht0 : Filter.Tendsto
        (fun θ => (horizontalAmplitude * Real.rpow θ α) * Rx θ)
        L (nhds 0) := by
      simpa only [mul_one, zero_mul, mul_zero] using ht
    apply Filter.Tendsto.congr' _ ht0
    filter_upwards [hposMem] with θ hθ
    dsimp only [Rx]
    have hp := Real.rpow_pos_of_pos hθ α
    field_simp [ne_of_gt hHorizontalPositive, ne_of_gt hp]
  have hlogRx : Filter.Tendsto (fun θ => Real.log (Rx θ)) L (nhds 0) := by
    have ht := (Real.continuousAt_log one_ne_zero).tendsto.comp hRx
    change Filter.Tendsto (fun θ => Real.log (Rx θ)) L (nhds (Real.log 1)) at ht
    simpa only [Real.log_one] using ht
  have hRxpow : Filter.Tendsto (fun θ => Real.rpow (Rx θ) γ) L (nhds 1) := by
    have ht := Real.continuous_exp.continuousAt.tendsto.comp (hlogRx.mul_const γ)
    change Filter.Tendsto (fun θ => Real.exp (Real.log (Rx θ) * γ)) L
      (nhds (Real.exp (0 * γ))) at ht
    have ht1 : Filter.Tendsto
        (fun θ => Real.exp (Real.log (Rx θ) * γ)) L (nhds 1) := by
      have heq : Real.exp (0 * γ) = 1 := by
        rw [zero_mul, Real.exp_zero]
      rw [heq] at ht
      exact ht
    apply Filter.Tendsto.congr' _ ht1
    filter_upwards [hRxpos] with θ hθ
    change Real.exp (Real.log (Rx θ) * γ) = Real.rpow (Rx θ) γ
    calc
      Real.exp (Real.log (Rx θ) * γ) = Rx θ ^ γ :=
        (Real.rpow_def_of_pos hθ γ).symm
      _ = Real.rpow (Rx θ) γ := (Real.rpow_eq_pow (Rx θ) γ).symm
  let amplitude := verticalAmplitude / Real.rpow horizontalAmplitude γ
  have hamp : amplitude ≠ 0 := by
    exact div_ne_zero hVertical.2.1
      (ne_of_gt (Real.rpow_pos_of_pos hHorizontalPositive γ))
  let E := fun θ => Ry θ / Real.rpow (Rx θ) γ - 1
  have hE : Filter.Tendsto E L (nhds 0) := by
    have hratio : Filter.Tendsto
        (fun θ => Ry θ / Real.rpow (Rx θ) γ) L (nhds 1) := by
      simpa only [div_eq_mul_inv, inv_one, mul_one] using
        hRy.mul (hRxpow.inv₀ one_ne_zero)
    have ht := hratio.sub
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) L (nhds 1))
    simpa only [E, sub_self] using ht
  have hidentity : ∀ᶠ θ in L,
      η θ - amplitude * Real.rpow (ξ θ) γ =
        amplitude * Real.rpow (ξ θ) γ * E θ := by
    filter_upwards [hposMem, hRxpos] with θ hθ hRpos
    have hθα := Real.rpow_pos_of_pos hθ α
    have hθβ := Real.rpow_pos_of_pos hθ β
    have hAγ := Real.rpow_pos_of_pos hHorizontalPositive γ
    have hRγ := Real.rpow_pos_of_pos hRpos γ
    have hxid : ξ θ = horizontalAmplitude * Real.rpow θ α * Rx θ := by
      dsimp only [Rx]
      field_simp [ne_of_gt hHorizontalPositive, ne_of_gt hθα]
    have hyid : η θ = verticalAmplitude * Real.rpow θ β * Ry θ := by
      dsimp only [Ry]
      field_simp [hVertical.2.1, ne_of_gt hθβ]
    have hxpow : Real.rpow (ξ θ) γ =
        Real.rpow horizontalAmplitude γ * Real.rpow θ β *
          Real.rpow (Rx θ) γ := by
      rw [hxid]
      change (horizontalAmplitude * (θ ^ α) * Rx θ) ^ γ =
        horizontalAmplitude ^ γ * θ ^ β * Rx θ ^ γ
      rw [Real.mul_rpow (mul_nonneg (le_of_lt hHorizontalPositive)
        (le_of_lt hθα)) (le_of_lt hRpos)]
      rw [Real.mul_rpow (le_of_lt hHorizontalPositive) (le_of_lt hθα)]
      rw [← Real.rpow_mul (le_of_lt hθ) α γ, hαγ]
    rw [hyid, hxpow]
    dsimp only [amplitude, E]
    field_simp [ne_of_gt hAγ, ne_of_gt hRγ]
  let data : CausticAsymptoticData :=
    { offset := offset
      amplitude := amplitude
      amplitude_ne_zero := hamp
      exponent := exponent }
  refine ⟨data, rfl, ?_, ?_, ?_⟩
  · exact hexponent
  · dsimp only [data, amplitude, γ]
    rw [hexponent]
  · change
      (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ θ : ℝ, 0 < θ → θ < δ₀ →
        θ ∈ F.domain ∧ IsForwardLimitingCausticPoint F θ (C θ) ∧ 0 < ξ θ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ,
        0 < θ → θ < δ → ξ θ < ε) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ,
        0 < θ → θ < δ →
          |η θ - amplitude * Real.rpow (ξ θ) γ| ≤
            ε * Real.rpow (ξ θ) γ
    constructor
    · rcases hBranch with ⟨δb, hδb, hb⟩
      have hpMem : {θ : ℝ | 0 < Rx θ} ∈ L := hRxpos
      rcases Metric.mem_nhdsWithin_iff.mp hpMem with ⟨δp, hδp, hpsub⟩
      refine ⟨min δb δp, lt_min hδb hδp, ?_⟩
      intro θ hθ hθδ
      have hθb : θ < δb := lt_of_lt_of_le hθδ (min_le_left _ _)
      have hθp : θ < δp := lt_of_lt_of_le hθδ (min_le_right _ _)
      rcases hb θ hθ hθb with ⟨hdom, hforward⟩
      have hRpos : 0 < Rx θ := by
        apply hpsub
        constructor
        · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ] using hθp
        · exact hθ
      have hden : 0 < horizontalAmplitude * Real.rpow θ α :=
        mul_pos hHorizontalPositive (Real.rpow_pos_of_pos hθ α)
      have hξpos : 0 < ξ θ := by
        rcases div_pos_iff.mp hRpos with hp | hn
        · exact hp.1
        · exfalso
          linarith [hn.2, hden]
      exact ⟨hdom, hforward, hξpos⟩
    constructor
    · intro ε hε
      rcases (Metric.tendsto_nhdsWithin_nhds.mp hξzero) ε hε with
        ⟨δ, hδ, hb⟩
      refine ⟨δ, hδ, ?_⟩
      intro θ hθ hθδ
      have hd := hb hθ (by
        simpa only [Real.dist_eq, sub_zero, abs_of_pos hθ] using hθδ)
      rw [Real.dist_eq, sub_zero] at hd
      exact lt_of_le_of_lt (le_abs_self (ξ θ)) hd
    · intro ε hε
      have habsamp : 0 < |amplitude| := abs_pos.mpr hamp
      rcases (Metric.tendsto_nhdsWithin_nhds.mp hE) (ε / |amplitude|)
        (div_pos hε habsamp) with ⟨δe, hδe, he⟩
      have hiMem : {θ : ℝ | η θ - amplitude * Real.rpow (ξ θ) γ =
          amplitude * Real.rpow (ξ θ) γ * E θ} ∈ L := hidentity
      rcases Metric.mem_nhdsWithin_iff.mp hiMem with ⟨δi, hδi, hisub⟩
      refine ⟨min δe δi, lt_min hδe hδi, ?_⟩
      intro θ hθ hθδ
      have hθe : θ < δe := lt_of_lt_of_le hθδ (min_le_left _ _)
      have hθi : θ < δi := lt_of_lt_of_le hθδ (min_le_right _ _)
      have hEb := he hθ (by
        simpa only [Real.dist_eq, sub_zero, abs_of_pos hθ] using hθe)
      rw [Real.dist_eq, sub_zero] at hEb
      have hid := hisub ⟨by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ] using hθi,
        hθ⟩
      rw [hid]
      have hξnonneg : 0 ≤ ξ θ := div_nonneg (abs_nonneg _)
        (le_of_lt scales.horizontal_pos)
      have hpownonneg := Real.rpow_nonneg hξnonneg γ
      have hcE : |amplitude| * |E θ| ≤ ε := by
        have hlt := (lt_div_iff₀ habsamp).mp hEb
        nlinarith
      calc
        |amplitude * Real.rpow (ξ θ) γ * E θ| =
            (|amplitude| * |E θ|) * Real.rpow (ξ θ) γ := by
              have habspow : |Real.rpow (ξ θ) γ| = Real.rpow (ξ θ) γ :=
                abs_of_nonneg hpownonneg
              rw [abs_mul, abs_mul, habspow]
              ring
        _ ≤ ε * Real.rpow (ξ θ) γ :=
          mul_le_mul_of_nonneg_right hcE hpownonneg

/-- Positive changes of normalization preserve offset and exponent and rescale amplitude only. -/
theorem smallAngleAsymptotic_changeScales (F : ReflectedRayFamily) (C : ℝ → Point2)
    (oldScales newScales : CausticScales) (data : CausticAsymptoticData)
    (hAsymptotic : IsSmallAngleCausticAsymptotic F C oldScales data) :
    ∃ newData : CausticAsymptoticData,
      newData.offset = data.offset ∧
        newData.exponent = data.exponent ∧
        newData.amplitude = data.amplitude *
          (oldScales.vertical / newScales.vertical) *
          Real.rpow (newScales.horizontal / oldScales.horizontal)
            data.exponent.value ∧
        IsSmallAngleCausticAsymptotic F C newScales newData := by
  let ξ := fun θ => |(C θ).x - F.mirror.center.x| / oldScales.horizontal
  let η := fun θ => ((C θ).y - data.offset) / oldScales.vertical
  let ξ' := fun θ => |(C θ).x - F.mirror.center.x| / newScales.horizontal
  let η' := fun θ => ((C θ).y - data.offset) / newScales.vertical
  let a := oldScales.horizontal / newScales.horizontal
  let b := oldScales.vertical / newScales.vertical
  let q := newScales.horizontal / oldScales.horizontal
  let r := data.exponent.value
  have ha : 0 < a := div_pos oldScales.horizontal_pos newScales.horizontal_pos
  have hb : 0 < b := div_pos oldScales.vertical_pos newScales.vertical_pos
  have hq : 0 < q := div_pos newScales.horizontal_pos oldScales.horizontal_pos
  have hqa : q * a = 1 := by
    dsimp only [q, a]
    field_simp [ne_of_gt oldScales.horizontal_pos,
      ne_of_gt newScales.horizontal_pos]
  have hpowprod : Real.rpow q r * Real.rpow a r = 1 := by
    change q ^ r * a ^ r = 1
    rw [← Real.mul_rpow (le_of_lt hq) (le_of_lt ha), hqa, Real.one_rpow]
  have hξ (θ : ℝ) : ξ' θ = a * ξ θ := by
    dsimp only [ξ', ξ, a]
    field_simp [ne_of_gt oldScales.horizontal_pos,
      ne_of_gt newScales.horizontal_pos]
  have hη (θ : ℝ) : η' θ = b * η θ := by
    dsimp only [η', η, b]
    field_simp [ne_of_gt oldScales.vertical_pos,
      ne_of_gt newScales.vertical_pos]
  let amplitude := data.amplitude * b * Real.rpow q r
  have hamp : amplitude ≠ 0 := mul_ne_zero
    (mul_ne_zero data.amplitude_ne_zero (ne_of_gt hb))
    (ne_of_gt (Real.rpow_pos_of_pos hq r))
  let newData : CausticAsymptoticData :=
    { offset := data.offset
      amplitude := amplitude
      amplitude_ne_zero := hamp
      exponent := data.exponent }
  change
    (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ θ : ℝ, 0 < θ → θ < δ₀ →
      θ ∈ F.domain ∧ IsForwardLimitingCausticPoint F θ (C θ) ∧ 0 < ξ θ) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ,
      0 < θ → θ < δ → ξ θ < ε) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ,
      0 < θ → θ < δ →
        |η θ - data.amplitude * Real.rpow (ξ θ) r| ≤
          ε * Real.rpow (ξ θ) r at hAsymptotic
  refine ⟨newData, rfl, rfl, ?_, ?_⟩
  · rfl
  · change
      (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ θ : ℝ, 0 < θ → θ < δ₀ →
        θ ∈ F.domain ∧ IsForwardLimitingCausticPoint F θ (C θ) ∧ 0 < ξ' θ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ,
        0 < θ → θ < δ → ξ' θ < ε) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ,
        0 < θ → θ < δ →
          |η' θ - amplitude * Real.rpow (ξ' θ) r| ≤
            ε * Real.rpow (ξ' θ) r
    constructor
    · rcases hAsymptotic.1 with ⟨δ, hδ, hbch⟩
      refine ⟨δ, hδ, ?_⟩
      intro θ hθ hθδ
      rcases hbch θ hθ hθδ with ⟨hdom, hfwd, hξpos⟩
      exact ⟨hdom, hfwd, by rw [hξ]; exact mul_pos ha hξpos⟩
    constructor
    · intro ε hε
      rcases hAsymptotic.2.1 (ε / a) (div_pos hε ha) with
        ⟨δ, hδ, hsmall⟩
      refine ⟨δ, hδ, ?_⟩
      intro θ hθ hθδ
      rw [hξ]
      have hs := hsmall θ hθ hθδ
      have := (lt_div_iff₀ ha).mp hs
      nlinarith
    · intro ε hε
      have hapow : 0 < Real.rpow a r := Real.rpow_pos_of_pos ha r
      have htol : 0 < ε * Real.rpow a r / b :=
        div_pos (mul_pos hε hapow) hb
      rcases hAsymptotic.2.2 (ε * Real.rpow a r / b) htol with
        ⟨δ, hδ, hrem⟩
      refine ⟨δ, hδ, ?_⟩
      intro θ hθ hθδ
      have hold := hrem θ hθ hθδ
      have hξnonneg : 0 ≤ ξ θ := div_nonneg (abs_nonneg _)
        (le_of_lt oldScales.horizontal_pos)
      have hξpow : 0 ≤ Real.rpow (ξ θ) r := Real.rpow_nonneg hξnonneg r
      have hnewpow : Real.rpow (ξ' θ) r =
          Real.rpow a r * Real.rpow (ξ θ) r := by
        rw [hξ]
        change (a * ξ θ) ^ r = a ^ r * (ξ θ) ^ r
        exact Real.mul_rpow (le_of_lt ha) hξnonneg
      have herr : η' θ - amplitude * Real.rpow (ξ' θ) r =
          b * (η θ - data.amplitude * Real.rpow (ξ θ) r) := by
        rw [hη, hnewpow]
        dsimp only [amplitude]
        calc
          b * η θ - data.amplitude * b * Real.rpow q r *
              (Real.rpow a r * Real.rpow (ξ θ) r) =
              b * η θ - data.amplitude * b *
                (Real.rpow q r * Real.rpow a r) * Real.rpow (ξ θ) r := by ring
          _ = b * (η θ - data.amplitude * Real.rpow (ξ θ) r) := by
            rw [hpowprod]
            ring
      rw [herr, abs_mul, abs_of_pos hb, hnewpow]
      have hscaled := mul_le_mul_of_nonneg_left hold (le_of_lt hb)
      calc
        b * |η θ - data.amplitude * Real.rpow (ξ θ) r| ≤
            b * ((ε * Real.rpow a r / b) * Real.rpow (ξ θ) r) := hscaled
        _ = ε * (Real.rpow a r * Real.rpow (ξ θ) r) := by
          field_simp [ne_of_gt hb]

end Ipho2026Gpt56solBlind.Shared.GeometricOptics
