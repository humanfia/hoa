import Ipho2026Gpt56solBlind.Shared.ConcentratorOptics

/- USER: Focused proof-performance retry. Preserve every declaration signature.
The previous lane left four proof gaps and made `OpticalState.existsUnique`
depend on a ten-million-heartbeat local option. No option escape is permitted:
refactor/extract exact aperture and optical-state helper steps until direct
`lake env lean` succeeds at the project defaults. Close the four gaps identified
by the latest independent review: illuminated-measure continuity, both endpoint
signs, and strict antitonicity. Do not read prior logs, task-result archives,
Git history, other Solution proofs, or any existing answer artifact. -/

/-!
# IPhO 2026 Problem 2.B.3: fivefold cylindrical solar concentrator

This answer-blind specification models the Figure 2f concentrator directly
from the shared first-contact ray optics.  The requested radius is represented
by a physical solution predicate, and the reported centimetre value appears
only under an existence-and-uniqueness theorem.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_2_B_3

open Shared
open Shared.GeometricOptics

/-- Fixed coherent-SI source and apparatus data.  In particular, the mirror
radius has coherent-SI coordinate one metre. -/
structure SourceData where
  mirrorCenter : PhysicalPoint2
  mirrorRadius : ISQDimensions.Length
  mirrorRadius_si :
    ISQDimensions.coordinateInSI SIUnitChoices.SI mirrorRadius = 1
  irradiance : Irradiance
  irradiance_pos :
    0 < ISQDimensions.coordinateInSI SIUnitChoices.SI irradiance
  axialExtent : ISQDimensions.Length
  axialExtent_pos :
    IsPositiveAxialExtent SIUnitChoices.SI axialExtent

/-- Strict positivity of the fixed source irradiance implies admissibility as
a uniform irradiance. -/
lemma SourceData.uniformIrradiance (S : SourceData) :
    UniformIrradiance SIUnitChoices.SI S.irradiance := by
  exact S.irradiance_pos.le

/-- An absorber radius in the geometric range of the one-reflection model. -/
structure CandidateRadius (S : SourceData) where
  absorberRadius : ISQDimensions.Length
  absorberRadius_pos :
    0 < ISQDimensions.coordinateInSI SIUnitChoices.SI absorberRadius
  absorberRadius_lt_half :
    ISQDimensions.coordinateInSI SIUnitChoices.SI absorberRadius <
      ISQDimensions.coordinateInSI SIUnitChoices.SI S.mirrorRadius / 2

/-- The typed Figure 2f concentrator determined by a source and candidate
absorber radius. -/
def physicalConcentrator (S : SourceData) (A : CandidateRadius S) :
    PhysicalConcentratorGeometry SIUnitChoices.SI :=
  { mirrorCenter := S.mirrorCenter
    mirrorRadius := S.mirrorRadius
    absorberRadius := A.absorberRadius
    absorberRadius_pos := A.absorberRadius_pos
    absorberRadius_lt_half := A.absorberRadius_lt_half }

/-- The coherent-SI scalar geometry used by the shared ray kernel. -/
def kernelGeometry (S : SourceData) (A : CandidateRadius S) :
    ConcentratorGeometry :=
  physicalConcentratorGeometryCoordinateInSI SIUnitChoices.SI
    (physicalConcentrator S A)

/-- The construction has exactly the Figure 2f centre displacement, lower
mirror, mirror-owned rims, and open diameter aperture. -/
lemma physicalConcentrator_figure2f (S : SourceData) (A : CandidateRadius S) :
    let PG := physicalConcentrator S A
    let G := kernelGeometry S A
    PG.mirrorCenter = S.mirrorCenter ∧
      PG.mirrorRadius = S.mirrorRadius ∧
      PG.absorberRadius = A.absorberRadius ∧
      G.mirror.radius = 1 ∧
      G.absorber.radius =
        ISQDimensions.coordinateInSI SIUnitChoices.SI A.absorberRadius ∧
      G.absorber.center.x = G.mirror.center.x ∧
      G.absorber.center.y = G.mirror.center.y - G.mirror.radius / 2 ∧
      G.lowerMirror.orientation = VerticalOrientation.lower ∧
      G.lowerMirror.rims = RimConvention.mirror ∧
      ∀ Q : Point2,
        OnAperture G.lowerMirror Q ↔
          Q.y = G.mirror.center.y ∧
            |Q.x - G.mirror.center.x| < G.mirror.radius := by
  dsimp [physicalConcentrator, kernelGeometry,
    physicalConcentratorGeometryCoordinateInSI,
    ConcentratorGeometry.absorber, ConcentratorGeometry.lowerMirror]
  refine ⟨rfl, rfl, rfl, S.mirrorRadius_si, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro Q
  rfl

/-- A complete optical state: the global one-reflection condition, its
attained maximal tangent angle, and measurable mirrored/reference apertures. -/
structure OpticalState (S : SourceData) (A : CandidateRadius S) where
  oneReflectionRegime : InOneReflectionRegime (kernelGeometry S A)
  limitingAngle : ℝ
  limitingAngle_spec :
    IsLimitingTangentAngle (kernelGeometry S A) limitingAngle
  illuminatedMeasurable :
    HasMeasurableIlluminatedAperture (kernelGeometry S A)
  referenceMeasurable :
    HasMeasurableReferenceAperture (kernelGeometry S A)

/-- Every optical state is governed by the shared first-contact model.  The
statement exposes the limiting tangent ray, exact branch ordering, reference
first contacts, finite aperture measures, and their typed coordinates. -/
lemma OpticalState.governedBySharedModel {S : SourceData} {A : CandidateRadius S}
    (W : OpticalState S A) :
    let G := kernelGeometry S A
    AcceptedReflectedRay G W.limitingAngle ∧
      (∃ s : Length, ∃ Q : Point2,
        IsTangentContainerContact G
          (axialReflectedRay G.mirror VerticalOrientation.lower W.limitingAngle)
          s Q) ∧
      (∀ θ : ℝ, AcceptedReflectedRay G θ → |θ| ≤ W.limitingAngle) ∧
      (∀ x ∈ illuminatedAperture G,
        |x - G.mirror.center.x| < G.mirror.radius ∧
          (IsDirectlyAbsorbed G x ∨ IsAbsorbedAfterOneReflection G x) ∧
          ¬(IsDirectlyAbsorbed G x ∧ IsAbsorbedAfterOneReflection G x)) ∧
      (∀ x ∈ unmirroredReferenceAperture G,
        ∃ s : Length, ∃ Q : Point2,
          IsFirstContainerContact G (incomingSunlightRay G x) s Q) ∧
      volume (illuminatedAperture G) ≠ ⊤ ∧
      volume (unmirroredReferenceAperture G) ≠ ⊤ ∧
      ISQDimensions.coordinateInSI SIUnitChoices.SI
          (transverseFluxMeasure SIUnitChoices.SI G W.illuminatedMeasurable) =
        (volume (illuminatedAperture G)).toReal ∧
      ISQDimensions.coordinateInSI SIUnitChoices.SI
          (referenceTransverseMeasure SIUnitChoices.SI G W.referenceMeasurable) =
        (volume (unmirroredReferenceAperture G)).toReal ∧
      0 ≤ ISQDimensions.coordinateInSI SIUnitChoices.SI
        (transverseFluxMeasure SIUnitChoices.SI G W.illuminatedMeasurable) ∧
      0 ≤ ISQDimensions.coordinateInSI SIUnitChoices.SI
        (referenceTransverseMeasure SIUnitChoices.SI G W.referenceMeasurable) := by
  dsimp
  have hbounded := transverseApertures_bounded (kernelGeometry S A)
  have hmeasure := transverseMeasures_coordinate SIUnitChoices.SI
    (kernelGeometry S A) W.illuminatedMeasurable W.referenceMeasurable
  refine ⟨W.limitingAngle_spec.2.2.1, W.limitingAngle_spec.2.2.2.1,
    W.limitingAngle_spec.2.2.2.2, ?_, ?_, hbounded.2.2.1,
    hbounded.2.2.2, hmeasure.1, hmeasure.2.1, hmeasure.2.2.1,
    hmeasure.2.2.2.1⟩
  · intro x hx
    have haccepted : AcceptedIncomingCoordinate (kernelGeometry S A) x := hx
    have hordering := acceptedIncomingCoordinate_ordering (kernelGeometry S A) x haccepted
    exact ⟨haccepted.1, hordering.1, hordering.2⟩
  · intro x hx
    exact hx

private lemma tangentProfile_strictMonoOn (R : ℝ) (hR : 0 < R) :
    StrictMonoOn (fun t : ℝ => R * Real.sin t * (1 - Real.cos t))
      (Set.Icc 0 (Real.pi / 2)) := by
  intro x hx y hy hxy
  have hsin_lt : Real.sin x < Real.sin y :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two
      ((neg_nonpos.mpr (show (0 : ℝ) ≤ Real.pi / 2 by positivity)).trans hx.1)
      hy.2 hxy
  have hcos_lt : Real.cos y < Real.cos x :=
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hx.1 hy.2 hxy
  have hsin_x : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1
      (by linarith [hy.2, Real.pi_pos])
  have hy_pos : 0 < y := lt_of_le_of_lt hx.1 hxy
  have hcos_y_lt_one : Real.cos y < 1 := by
    simpa using
      (Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
        (show 0 ≤ (0 : ℝ) by norm_num) hy.2 hy_pos)
  have hleft :
      Real.sin x * (1 - Real.cos x) ≤
        Real.sin x * (1 - Real.cos y) :=
    mul_le_mul_of_nonneg_left (by linarith) hsin_x
  have hright :
      Real.sin x * (1 - Real.cos y) <
        Real.sin y * (1 - Real.cos y) :=
    mul_lt_mul_of_pos_right hsin_lt (by linarith)
  simpa only [mul_assoc] using
    (mul_lt_mul_of_pos_left (hleft.trans_lt hright) hR)

private lemma axialReflectedRay_origin_x (G : ConcentratorGeometry) (t : ℝ) :
    (axialReflectedRay G.mirror .lower t).origin.x =
      G.mirror.center.x + G.mirror.radius * Real.sin t := by
  rfl

private lemma axialReflectedRay_origin_y (G : ConcentratorGeometry) (t : ℝ) :
    (axialReflectedRay G.mirror .lower t).origin.y =
      G.mirror.center.y - G.mirror.radius * Real.cos t := by
  change
    G.mirror.center.y + (-1) * G.mirror.radius * Real.cos t =
      G.mirror.center.y - G.mirror.radius * Real.cos t
  ring

private lemma axialReflectedRay_direction_x (G : ConcentratorGeometry) (t : ℝ) :
    (axialReflectedRay G.mirror .lower t).direction.1.x =
      -2 * Real.sin t * Real.cos t := by
  have htrig : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq t
  let data := semicirclePoint G.mirror .lower t
  let normal : UnitDirection :=
    ⟨data.2, by
      change
        Real.sin t * Real.sin t +
            ((-1) * Real.cos t) * ((-1) * Real.cos t) = 1
      nlinarith [htrig]⟩
  have hraw :
      (axialReflectedRay G.mirror .lower t).direction.1 =
        reflectedDirection (axisDirection .lower).1 normal := by
    rfl
  rw [hraw]
  change
    0 -
        (2 * (0 * Real.sin t + (-1) * ((-1) * Real.cos t))) *
          Real.sin t =
      -2 * Real.sin t * Real.cos t
  ring

private lemma axialReflectedRay_direction_y (G : ConcentratorGeometry) (t : ℝ) :
    (axialReflectedRay G.mirror .lower t).direction.1.y =
      2 * Real.cos t ^ 2 - 1 := by
  have htrig : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq t
  let data := semicirclePoint G.mirror .lower t
  let normal : UnitDirection :=
    ⟨data.2, by
      change
        Real.sin t * Real.sin t +
            ((-1) * Real.cos t) * ((-1) * Real.cos t) = 1
      nlinarith [htrig]⟩
  have hraw :
      (axialReflectedRay G.mirror .lower t).direction.1 =
        reflectedDirection (axisDirection .lower).1 normal := by
    rfl
  rw [hraw]
  change
    -1 -
        (2 * (0 * Real.sin t + (-1) * ((-1) * Real.cos t))) *
          ((-1) * Real.cos t) =
      2 * Real.cos t ^ 2 - 1
  ring

private lemma axialReflectedRay_point_x (G : ConcentratorGeometry) (t u : ℝ) :
    ((axialReflectedRay G.mirror .lower t).pointAt u).x =
      G.mirror.center.x + G.mirror.radius * Real.sin t +
        u * (-2 * Real.sin t * Real.cos t) := by
  simp [ForwardRay.pointAt, translate, directionDisplacement,
    axialReflectedRay_origin_x, axialReflectedRay_direction_x]

private lemma axialReflectedRay_point_y (G : ConcentratorGeometry) (t u : ℝ) :
    ((axialReflectedRay G.mirror .lower t).pointAt u).y =
      G.mirror.center.y - G.mirror.radius * Real.cos t +
        u * (2 * Real.cos t ^ 2 - 1) := by
  simp [ForwardRay.pointAt, translate, directionDisplacement,
    axialReflectedRay_origin_y, axialReflectedRay_direction_y]

private lemma axialReflectedRay_mirror_norm (G : ConcentratorGeometry) (t u : ℝ) :
    displacementNormSq
        (displacement G.mirror.center
          ((axialReflectedRay G.mirror .lower t).pointAt u)) =
      G.mirror.radius ^ 2 - 2 * G.mirror.radius * Real.cos t * u + u ^ 2 := by
  simp only [displacementNormSq, displacement, axialReflectedRay_point_x,
    axialReflectedRay_point_y]
  have htrig := Real.sin_sq_add_cos_sq t
  have hsin_sq : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by linarith
  ring_nf
  rw [hsin_sq]
  ring

private lemma axialReflectedRay_absorber_norm (G : ConcentratorGeometry)
    (t u : ℝ) :
    displacementNormSq
        (displacement G.absorber.center
          ((axialReflectedRay G.mirror .lower t).pointAt u)) =
      (G.mirror.radius * Real.sin t * (1 - Real.cos t)) ^ 2 +
        (u - G.mirror.radius *
          (1 / 2 + Real.cos t - Real.cos t ^ 2)) ^ 2 := by
  simp only [displacementNormSq, displacement, axialReflectedRay_point_x,
    axialReflectedRay_point_y]
  simp only [ConcentratorGeometry.absorber]
  have htrig := Real.sin_sq_add_cos_sq t
  have hsin_sq : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by linarith
  ring_nf
  rw [hsin_sq]
  ring

private lemma concentrator_inOneReflectionRegime (G : ConcentratorGeometry) :
    InOneReflectionRegime G := by
  let R : ℝ := G.mirror.radius
  let a : ℝ := G.absorber.radius
  have hR : 0 < R := G.mirror.radius_pos
  have ha : 0 < a := G.absorber.radius_pos
  have ha_half : a < R / 2 := G.absorberRadius_lt_half
  intro t ht s Q hcontact
  rcases hcontact with ⟨hs, hQ, hcircle, hbefore⟩
  have hcos : 0 < Real.cos t := by
    apply Real.cos_pos_of_mem_Ioo
    exact abs_lt.mp ht
  have hcircle_eq :
      (Q.x - G.mirror.center.x) ^ 2 +
          (Q.y - (G.mirror.center.y - R / 2)) ^ 2 = a ^ 2 := by
    simpa [OnCircle, displacementNormSq, displacement,
      ConcentratorGeometry.absorber, R, a] using hcircle
  have hy_sq :
      (Q.y - (G.mirror.center.y - R / 2)) ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg (Q.x - G.mirror.center.x)]
  have hy_abs :
      |Q.y - (G.mirror.center.y - R / 2)| ≤ a :=
    abs_le_of_sq_le_sq hy_sq ha.le
  have hy_lower :
      -a ≤ Q.y - (G.mirror.center.y - R / 2) := (abs_le.mp hy_abs).1
  have hy_mul := mul_le_mul_of_nonneg_left hy_lower hR.le
  have hQinside :
      displacementNormSq (displacement G.mirror.center Q) < R ^ 2 := by
    dsimp [displacementNormSq, displacement]
    nlinarith [sq_nonneg (a + R / 2), sq_nonneg (R / 2 - a)]
  have hnorm_s :
      displacementNormSq (displacement G.mirror.center Q) =
        R ^ 2 - 2 * R * Real.cos t * s + s ^ 2 := by
    rw [hQ]
    simpa [R] using axialReflectedRay_mirror_norm G t s
  have hs_exit : s < 2 * R * Real.cos t := by
    by_contra hnot
    have hdiff : 0 ≤ s - 2 * R * Real.cos t := by linarith
    have hprod := mul_nonneg hs.le hdiff
    nlinarith
  intro u hu hus harc
  have hu_exit : u < 2 * R * Real.cos t := lt_of_le_of_lt hus hs_exit
  have hprod_u : u * (u - 2 * R * Real.cos t) < 0 :=
    mul_neg_of_pos_of_neg hu (by linarith)
  have hinside_u :
      displacementNormSq
          (displacement G.mirror.center
            ((axialReflectedRay G.mirror .lower t).pointAt u)) < R ^ 2 := by
    rw [show displacementNormSq
        (displacement G.mirror.center
          ((axialReflectedRay G.mirror .lower t).pointAt u)) =
          R ^ 2 - 2 * R * Real.cos t * u + u ^ 2 by
      simpa [R] using axialReflectedRay_mirror_norm G t u]
    nlinarith
  have hon := harc.1
  change displacementNormSq
      (displacement G.mirror.center
        ((axialReflectedRay G.mirror .lower t).pointAt u)) = R ^ 2 at hon
  linarith

private lemma containerFirstContact_of_abs_le (G : ConcentratorGeometry) (x : ℝ)
    (hx : |x - G.mirror.center.x| ≤ G.absorber.radius) :
    ∃ s : ℝ, ∃ Q : Point2,
      IsFirstContainerContact G (incomingSunlightRay G x) s Q := by
  let R : ℝ := G.mirror.radius
  let a : ℝ := G.absorber.radius
  have ha : 0 < a := G.absorber.radius_pos
  have ha_half : a < R / 2 := G.absorberRadius_lt_half
  have hdx_sq : (x - G.mirror.center.x) ^ 2 ≤ a ^ 2 := by
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg (x - G.mirror.center.x)) ha.le).2 (by simpa [a] using hx)
    simpa only [sq_abs] using hsquare
  have hrad : 0 ≤ a ^ 2 - (x - G.mirror.center.x) ^ 2 := by linarith
  let t : ℝ := Real.sqrt (a ^ 2 - (x - G.mirror.center.x) ^ 2)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht_sq : t ^ 2 = a ^ 2 - (x - G.mirror.center.x) ^ 2 :=
    Real.sq_sqrt hrad
  have ht_le_a : t ≤ a := by
    nlinarith [sq_nonneg (x - G.mirror.center.x)]
  let s : ℝ := R / 2 - t
  have hs : 0 < s := by
    dsimp [s]
    linarith
  let Q : Point2 := (incomingSunlightRay G x).pointAt s
  refine ⟨s, Q, hs, rfl, ?_, ?_⟩
  · change displacementNormSq (displacement G.absorber.center Q) =
      G.absorber.radius ^ 2
    dsimp [Q, ForwardRay.pointAt, incomingSunlightRay, translate,
      directionDisplacement, axisDirection, orientationSign,
      ConcentratorGeometry.absorber, s]
    dsimp [displacementNormSq, displacement]
    norm_num
    dsimp [R, a, ConcentratorGeometry.absorber] at ht_sq ⊢
    ring_nf at ⊢
    linarith
  · intro u hu hus
    have hvertical : t < R / 2 - u := by
      dsimp [s] at hus
      linarith
    have hvertical_sq : t ^ 2 < (R / 2 - u) ^ 2 :=
      (sq_lt_sq₀ ht (by linarith)).2 hvertical
    dsimp [ForwardRay.pointAt, incomingSunlightRay, translate,
      directionDisplacement, axisDirection, orientationSign,
      ConcentratorGeometry.absorber]
    dsimp [displacementNormSq, displacement]
    norm_num
    dsimp [R, a, ConcentratorGeometry.absorber] at ht_sq hvertical_sq ⊢
    ring_nf at ⊢
    linarith

private lemma unmirroredReferenceAperture_eq_Icc (G : ConcentratorGeometry) :
    unmirroredReferenceAperture G =
      Set.Icc (G.mirror.center.x - G.absorber.radius)
        (G.mirror.center.x + G.absorber.radius) := by
  ext x
  constructor
  · intro hx
    have hbound := (transverseApertures_bounded G).2.1 x hx
    have hbound' : |x - G.mirror.center.x| ≤ G.absorber.radius := by
      simpa [ConcentratorGeometry.absorber] using hbound
    rw [Set.mem_Icc]
    rw [abs_le] at hbound'
    constructor <;> linarith [hbound'.1, hbound'.2]
  · intro hx
    rw [Set.mem_Icc] at hx
    have habs : |x - G.mirror.center.x| ≤ G.absorber.radius := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    exact containerFirstContact_of_abs_le G x habs

private lemma absorberBoundary_insideMirror (G : ConcentratorGeometry)
    (Q : Point2) (hcircle : OnCircle G.absorber Q) :
    displacementNormSq (displacement G.mirror.center Q) <
      G.mirror.radius ^ 2 := by
  let R : ℝ := G.mirror.radius
  let a : ℝ := G.absorber.radius
  have hR : 0 < R := G.mirror.radius_pos
  have ha : 0 < a := G.absorber.radius_pos
  have ha_half : a < R / 2 := G.absorberRadius_lt_half
  have hcircle_eq :
      (Q.x - G.mirror.center.x) ^ 2 +
          (Q.y - (G.mirror.center.y - R / 2)) ^ 2 = a ^ 2 := by
    simpa [OnCircle, displacementNormSq, displacement,
      ConcentratorGeometry.absorber, R, a] using hcircle
  have hy_sq :
      (Q.y - (G.mirror.center.y - R / 2)) ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg (Q.x - G.mirror.center.x)]
  have hy_abs : |Q.y - (G.mirror.center.y - R / 2)| ≤ a :=
    abs_le_of_sq_le_sq hy_sq ha.le
  have hy_lower : -a ≤ Q.y - (G.mirror.center.y - R / 2) :=
    (abs_le.mp hy_abs).1
  have hy_mul := mul_le_mul_of_nonneg_left hy_lower hR.le
  dsimp [displacementNormSq, displacement, R]
  nlinarith [sq_nonneg (R / 2 - a)]

private lemma directlyAbsorbed_iff_abs_le (G : ConcentratorGeometry) (x : ℝ) :
    IsDirectlyAbsorbed G x ↔
      |x - G.mirror.center.x| ≤ G.absorber.radius := by
  let a : ℝ := G.absorber.radius
  have ha : 0 < a := G.absorber.radius_pos
  constructor
  · rintro ⟨s, Q, hfirst, hcircle⟩
    rcases hfirst with ⟨_hs, hQ, _hboundary, _hbefore⟩
    have hQx : Q.x = x := by
      rw [hQ]
      simp [ForwardRay.pointAt, incomingSunlightRay, translate,
        directionDisplacement, axisDirection, orientationSign]
    have hcircle_eq :
        (Q.x - G.mirror.center.x) ^ 2 +
            (Q.y - (G.mirror.center.y - G.mirror.radius / 2)) ^ 2 = a ^ 2 := by
      simpa [OnCircle, displacementNormSq, displacement,
        ConcentratorGeometry.absorber, a] using hcircle
    rw [hQx] at hcircle_eq
    have hx_sq : (x - G.mirror.center.x) ^ 2 ≤ a ^ 2 := by
      nlinarith [sq_nonneg (Q.y -
        (G.mirror.center.y - G.mirror.radius / 2))]
    simpa [a] using abs_le_of_sq_le_sq hx_sq ha.le
  · intro hx
    rcases containerFirstContact_of_abs_le G x hx with ⟨s, Q, hcontact⟩
    rcases hcontact with ⟨hs, hQ, hcircle, hbefore⟩
    refine ⟨s, Q, ⟨hs, hQ, Or.inr hcircle, ?_⟩, hcircle⟩
    intro u hu hus
    constructor
    · constructor
      · simpa [ConcentratorGeometry.lowerMirror, ForwardRay.pointAt,
          incomingSunlightRay, translate, directionDisplacement,
          axisDirection, orientationSign] using hu
      · have hQinside := absorberBoundary_insideMirror G Q hcircle
        have hnormQ :
            displacementNormSq (displacement G.mirror.center Q) =
              (x - G.mirror.center.x) ^ 2 + s ^ 2 := by
          rw [hQ]
          simp [displacementNormSq, displacement, ForwardRay.pointAt,
            incomingSunlightRay, translate, directionDisplacement,
            axisDirection, orientationSign]
        have hu_sq : u ^ 2 < s ^ 2 := (sq_lt_sq₀ hu.le hs.le).2 hus
        change displacementNormSq
            (displacement G.mirror.center ((incomingSunlightRay G x).pointAt u)) <
          G.mirror.radius ^ 2
        simp [displacementNormSq, displacement, ForwardRay.pointAt,
          incomingSunlightRay, translate, directionDisplacement,
          axisDirection, orientationSign]
        nlinarith
    · intro hclosed
      have hout := hbefore u hu.le hus
      exact (not_lt_of_ge hclosed) hout

private lemma point2_ext (P Q : Point2) (hx : P.x = Q.x) (hy : P.y = Q.y) :
    P = Q := by
  rcases P with ⟨px, py⟩
  rcases Q with ⟨qx, qy⟩
  simp_all

private lemma canonicalMirrorFirst (G : ConcentratorGeometry) (x : ℝ)
    (houtside : G.absorber.radius < |x - G.mirror.center.x|)
    (hrim : |x - G.mirror.center.x| < G.mirror.radius) :
    ∃ t s : ℝ,
      InAxialIncidenceDomain t ∧
        (semicirclePoint G.mirror .lower t).1.x = x ∧
        IsFirstConcentratorContact G (incomingSunlightRay G x) s
          (semicirclePoint G.mirror .lower t).1 ∧
        OnReflectingArc G.lowerMirror
          (semicirclePoint G.mirror .lower t).1 := by
  let R : ℝ := G.mirror.radius
  have hR : 0 < R := G.mirror.radius_pos
  let z : ℝ := (x - G.mirror.center.x) / R
  have hz : |z| < 1 := by
    rw [abs_div, abs_of_pos hR]
    exact (div_lt_one hR).2 (by simpa [R] using hrim)
  have hz_lower : -1 < z := (abs_lt.mp hz).1
  have hz_upper : z < 1 := (abs_lt.mp hz).2
  let t : ℝ := Real.arcsin z
  have htdomain : InAxialIncidenceDomain t := by
    change |t| < Real.pi / 2
    rw [abs_lt]
    exact ⟨Real.neg_pi_div_two_lt_arcsin.mpr hz_lower,
      Real.arcsin_lt_pi_div_two.mpr hz_upper⟩
  have hsin : Real.sin t = z := Real.sin_arcsin hz_lower.le hz_upper.le
  let P : Point2 := (semicirclePoint G.mirror .lower t).1
  have hPx : P.x = x := by
    calc
      P.x = G.mirror.center.x + R * Real.sin t := by rfl
      _ = G.mirror.center.x + R * z := by rw [hsin]
      _ = G.mirror.center.x + ((x - G.mirror.center.x) / R) * R := by
        rw [mul_comm R z]
      _ = G.mirror.center.x + (x - G.mirror.center.x) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hR)]
      _ = x := by ring
  have hmirror : OnReflectingArc G.lowerMirror P :=
    (semicirclePoint_invariants G.mirror .lower .mirror t htdomain).1
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo (abs_lt.mp htdomain)
  let s : ℝ := R * Real.cos t
  have hs : 0 < s := mul_pos hR hcos
  have hPy : P.y = G.mirror.center.y - R * Real.cos t := by
    dsimp [P, semicirclePoint, orientationSign, R]
    ring
  have hfirst : IsFirstConcentratorContact G (incomingSunlightRay G x) s P := by
    refine ⟨hs, ?_, Or.inl hmirror, ?_⟩
    · apply point2_ext
      · simpa [ForwardRay.pointAt, incomingSunlightRay, translate,
          directionDisplacement, axisDirection, orientationSign] using hPx
      · rw [hPy]
        simp [s, ForwardRay.pointAt, incomingSunlightRay, translate,
          directionDisplacement, axisDirection, orientationSign]
        ring
    · intro u hu hus
      constructor
      · constructor
        · simpa [ConcentratorGeometry.lowerMirror, ForwardRay.pointAt,
            incomingSunlightRay, translate, directionDisplacement,
            axisDirection, orientationSign] using hu
        · change displacementNormSq
              (displacement G.mirror.center
                ((incomingSunlightRay G x).pointAt u)) < G.mirror.radius ^ 2
          simp [displacementNormSq, displacement, ForwardRay.pointAt,
            incomingSunlightRay, translate, directionDisplacement,
            axisDirection, orientationSign]
          have hxcoord : x - G.mirror.center.x = R * Real.sin t := by
            rw [← hPx]
            dsimp [P, semicirclePoint, R]
            ring
          rw [hxcoord]
          have hu_sq : u ^ 2 < (R * Real.cos t) ^ 2 :=
            (sq_lt_sq₀ hu.le hs.le).2 (by simpa [s] using hus)
          have hcircle_sq :
              (R * Real.sin t) ^ 2 + (R * Real.cos t) ^ 2 = R ^ 2 := by
            calc
              (R * Real.sin t) ^ 2 + (R * Real.cos t) ^ 2 =
                  R ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
              _ = R ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]
          change (R * Real.sin t) ^ 2 + u ^ 2 < R ^ 2
          linarith
      · intro hin
        change displacementNormSq
            (displacement G.absorber.center
              ((incomingSunlightRay G x).pointAt u)) ≤
          G.absorber.radius ^ 2 at hin
        have hx_sq : G.absorber.radius ^ 2 <
            (x - G.mirror.center.x) ^ 2 := by
          have hsquare :=
            (sq_lt_sq₀ G.absorber.radius_pos.le (abs_nonneg _)).2 houtside
          simpa only [sq_abs] using hsquare
        dsimp [displacementNormSq, displacement, ForwardRay.pointAt,
          incomingSunlightRay, translate, directionDisplacement,
          axisDirection, orientationSign, ConcentratorGeometry.absorber] at hin
        norm_num at hin
        have hle0 : (x - G.mirror.center.x) ^ 2 ≤ G.absorberRadius ^ 2 :=
          (le_add_of_nonneg_right (sq_nonneg _)).trans hin
        have hle : (x - G.mirror.center.x) ^ 2 ≤ G.absorber.radius ^ 2 := by
          simpa [ConcentratorGeometry.absorber] using hle0
        exact (not_lt_of_ge hle) hx_sq
  exact ⟨t, s, htdomain, hPx, hfirst, hmirror⟩

private lemma direction2_ext (d₁ d₂ : Direction2) (hx : d₁.x = d₂.x)
    (hy : d₁.y = d₂.y) : d₁ = d₂ := by
  rcases d₁ with ⟨x₁, y₁⟩
  rcases d₂ with ⟨x₂, y₂⟩
  simp_all

private lemma forwardRay_ext (r₁ r₂ : ForwardRay) (ho : r₁.origin = r₂.origin)
    (hd : r₁.direction = r₂.direction) : r₁ = r₂ := by
  rcases r₁ with ⟨o₁, d₁⟩
  rcases r₂ with ⟨o₂, d₂⟩
  simp_all

private lemma reflectedKernel_eq_axial (G : ConcentratorGeometry) (t : ℝ)
    (_ht : InAxialIncidenceDomain t)
    (hmirror : OnReflectingArc G.lowerMirror
      (semicirclePoint G.mirror .lower t).1) :
    rayAfterReflection G.mirror
        (incomingSunlightRay G (semicirclePoint G.mirror .lower t).1.x)
        (semicirclePoint G.mirror .lower t).1 hmirror.1 =
      axialReflectedRay G.mirror .lower t := by
  have hRne : G.mirror.radius ≠ 0 := ne_of_gt G.mirror.radius_pos
  have hnx :
      ((semicirclePoint G.mirror .lower t).1.x - G.mirror.center.x) /
          G.mirror.radius = Real.sin t := by
    change
      (G.mirror.center.x + G.mirror.radius * Real.sin t -
          G.mirror.center.x) / G.mirror.radius = Real.sin t
    rw [show
      G.mirror.center.x + G.mirror.radius * Real.sin t -
          G.mirror.center.x = G.mirror.radius * Real.sin t by ring]
    exact mul_div_cancel_left₀ _ hRne
  have hny :
      ((semicirclePoint G.mirror .lower t).1.y - G.mirror.center.y) /
          G.mirror.radius = (-1) * Real.cos t := by
    change
      (G.mirror.center.y + (-1) * G.mirror.radius * Real.cos t -
          G.mirror.center.y) / G.mirror.radius = (-1) * Real.cos t
    rw [show
      G.mirror.center.y + (-1) * G.mirror.radius * Real.cos t -
          G.mirror.center.y = G.mirror.radius * ((-1) * Real.cos t) by ring]
    exact mul_div_cancel_left₀ _ hRne
  apply forwardRay_ext
  · rfl
  · apply Subtype.ext
    apply direction2_ext
    · change
        0 -
              (2 *
                (0 *
                      (((semicirclePoint G.mirror .lower t).1.x -
                            G.mirror.center.x) /
                        G.mirror.radius) +
                  (-1) *
                      (((semicirclePoint G.mirror .lower t).1.y -
                            G.mirror.center.y) /
                        G.mirror.radius))) *
                (((semicirclePoint G.mirror .lower t).1.x -
                      G.mirror.center.x) /
                  G.mirror.radius) =
          0 -
              (2 *
                (0 * Real.sin t + (-1) * ((-1) * Real.cos t))) *
                Real.sin t
      rw [hnx, hny]
    · change
        -1 -
              (2 *
                (0 *
                      (((semicirclePoint G.mirror .lower t).1.x -
                            G.mirror.center.x) /
                        G.mirror.radius) +
                  (-1) *
                      (((semicirclePoint G.mirror .lower t).1.y -
                            G.mirror.center.y) /
                        G.mirror.radius))) *
                (((semicirclePoint G.mirror .lower t).1.y -
                      G.mirror.center.y) /
                  G.mirror.radius) =
          -1 -
              (2 *
                (0 * Real.sin t + (-1) * ((-1) * Real.cos t))) *
                ((-1) * Real.cos t)
      rw [hnx, hny]

private lemma axialHit_of_profile_le (G : ConcentratorGeometry) (t : ℝ)
    (ht : InAxialIncidenceDomain t)
    (houtside : G.absorber.radius < |G.mirror.radius * Real.sin t|)
    (hperp : G.mirror.radius * Real.sin |t| * (1 - Real.cos |t|) ≤
      G.absorber.radius) :
    ∃ s : ℝ, ∃ Q : Point2,
      IsFirstContainerContact G (axialReflectedRay G.mirror .lower t) s Q ∧
        HasNoSecondMirrorContact G (axialReflectedRay G.mirror .lower t) s := by
  let R : ℝ := G.mirror.radius
  let a : ℝ := G.absorber.radius
  have hR : 0 < R := G.mirror.radius_pos
  have ha : 0 < a := G.absorber.radius_pos
  have htmem : |t| ∈ Set.Icc 0 (Real.pi / 2) := ⟨abs_nonneg t, ht.le⟩
  have hft_nonneg :
      0 ≤ R * Real.sin |t| * (1 - Real.cos |t|) := by
    have hsin_nonneg : 0 ≤ Real.sin |t| :=
      Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg t)
        (by linarith [htmem.2, Real.pi_pos])
    exact mul_nonneg (mul_nonneg hR.le hsin_nonneg)
      (sub_nonneg.mpr (Real.cos_le_one _))
  have hft_sq :
      (R * Real.sin |t| * (1 - Real.cos |t|)) ^ 2 =
        (R * Real.sin t * (1 - Real.cos t)) ^ 2 := by
    by_cases ht0 : 0 ≤ t
    · simp [abs_of_nonneg ht0]
    · have ht0' : t ≤ 0 := le_of_not_ge ht0
      rw [abs_of_nonpos ht0']
      simp only [Real.sin_neg, Real.cos_neg]
      ring
  have hb_sq_le :
      (R * Real.sin t * (1 - Real.cos t)) ^ 2 ≤ a ^ 2 := by
    rw [← hft_sq]
    exact (sq_le_sq₀ hft_nonneg ha.le).2 (by simpa [R, a] using hperp)
  let s₀ : ℝ := R * (1 / 2 + Real.cos t - Real.cos t ^ 2)
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo (abs_lt.mp ht)
  have hcos_le : Real.cos t ≤ 1 := Real.cos_le_one t
  have hs₀ : 0 < s₀ := by
    have hc : 0 ≤ Real.cos t * (1 - Real.cos t) :=
      mul_nonneg hcos.le (sub_nonneg.mpr hcos_le)
    dsimp [s₀]
    have hinterior : 0 < (1 / 2 : ℝ) +
        Real.cos t * (1 - Real.cos t) := by linarith
    have heq :
        (1 / 2 : ℝ) + Real.cos t - Real.cos t ^ 2 =
          1 / 2 + Real.cos t * (1 - Real.cos t) := by ring
    rw [heq]
    exact mul_pos hR hinterior
  let δ : ℝ := Real.sqrt
    (a ^ 2 - (R * Real.sin t * (1 - Real.cos t)) ^ 2)
  have hrad : 0 ≤ a ^ 2 -
      (R * Real.sin t * (1 - Real.cos t)) ^ 2 := sub_nonneg.mpr hb_sq_le
  have hδ : 0 ≤ δ := Real.sqrt_nonneg _
  have hδsq :
      δ ^ 2 = a ^ 2 - (R * Real.sin t * (1 - Real.cos t)) ^ 2 :=
    Real.sq_sqrt hrad
  have hstart_gt :
      a ^ 2 < (R * Real.sin t * (1 - Real.cos t)) ^ 2 + s₀ ^ 2 := by
    have hout_sq : a ^ 2 < (R * Real.sin t) ^ 2 := by
      have houtside' : a < |R * Real.sin t| := by
        simpa [R, a] using houtside
      have hsquare :=
        (sq_lt_sq₀ ha.le (abs_nonneg (R * Real.sin t))).2 houtside'
      simpa only [sq_abs] using hsquare
    have hnorm0 := axialReflectedRay_absorber_norm G t 0
    have hhorizontal_le :
        (R * Real.sin t) ^ 2 ≤
          displacementNormSq
            (displacement G.absorber.center
              (axialReflectedRay G.mirror .lower t).origin) := by
      simp [displacementNormSq, displacement, axialReflectedRay_origin_x,
        axialReflectedRay_origin_y, ConcentratorGeometry.absorber, R]
      positivity
    have hformula :
        displacementNormSq
            (displacement G.absorber.center
              (axialReflectedRay G.mirror .lower t).origin) =
          (R * Real.sin t * (1 - Real.cos t)) ^ 2 + s₀ ^ 2 := by
      simpa [s₀, R, ForwardRay.pointAt, translate, directionDisplacement] using hnorm0
    rw [hformula] at hhorizontal_le
    exact hout_sq.trans_le hhorizontal_le
  have hδ_lt : δ < s₀ := by
    apply (sq_lt_sq₀ hδ hs₀.le).mp
    rw [hδsq]
    linarith
  let s : ℝ := s₀ - δ
  have hs : 0 < s := sub_pos.mpr hδ_lt
  let Q : Point2 := (axialReflectedRay G.mirror .lower t).pointAt s
  have hcontact : IsFirstContainerContact G
      (axialReflectedRay G.mirror .lower t) s Q := by
    refine ⟨hs, rfl, ?_, ?_⟩
    · change displacementNormSq (displacement G.absorber.center Q) =
        G.absorber.radius ^ 2
      rw [show Q = (axialReflectedRay G.mirror .lower t).pointAt s by rfl,
        axialReflectedRay_absorber_norm]
      have heq :
          (R * Real.sin t * (1 - Real.cos t)) ^ 2 + (s - s₀) ^ 2 =
            a ^ 2 := by
        dsimp [s]
        nlinarith [hδsq]
      simpa [s₀, R, a, ConcentratorGeometry.absorber] using heq
    · intro u hu hus
      rw [axialReflectedRay_absorber_norm]
      have hu_lt : u < s₀ - δ := by simpa [s] using hus
      have hdist : δ < s₀ - u := by linarith
      have hdist_sq : δ ^ 2 < (u - s₀) ^ 2 := by
        have := (sq_lt_sq₀ hδ (by linarith : 0 ≤ s₀ - u)).2 hdist
        nlinarith
      have hsum :
          a ^ 2 < (R * Real.sin t * (1 - Real.cos t)) ^ 2 +
            (u - s₀) ^ 2 := by
        linarith [hδsq, hdist_sq]
      simpa [s₀, R, a, ConcentratorGeometry.absorber] using hsum
  exact ⟨s, Q, hcontact,
    concentrator_inOneReflectionRegime G t ht s Q hcontact⟩

private lemma illuminatedAperture_eq_Icc (G : ConcentratorGeometry) (θ : ℝ)
    (hθpos : 0 < θ) (hθtop : θ < Real.pi / 2)
    (hmax : ∀ t : ℝ, AcceptedReflectedRay G t → |t| ≤ θ)
    (hformula :
      G.mirror.radius * Real.sin θ * (1 - Real.cos θ) =
        G.absorber.radius) :
    illuminatedAperture G =
      Set.Icc (G.mirror.center.x - G.mirror.radius * Real.sin θ)
        (G.mirror.center.x + G.mirror.radius * Real.sin θ) := by
  let R : ℝ := G.mirror.radius
  let a : ℝ := G.absorber.radius
  let f : ℝ → ℝ := fun t => R * Real.sin t * (1 - Real.cos t)
  have hR : 0 < R := G.mirror.radius_pos
  have ha : 0 < a := G.absorber.radius_pos
  have hregime : InOneReflectionRegime G := concentrator_inOneReflectionRegime G
  have hθmem : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨hθpos.le, hθtop.le⟩
  have hf_strict : StrictMonoOn f (Set.Icc 0 (Real.pi / 2)) := by
    simpa [f] using tangentProfile_strictMonoOn R hR
  have hcosθ : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθpos], hθtop⟩
  have hsinθ : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [hθtop, Real.pi_pos])
  have hhorizontal : a < R * Real.sin θ := by
    have hformula' : R * Real.sin θ * (1 - Real.cos θ) = a := by
      simpa [R, a] using hformula
    rw [← hformula']
    have hRs : 0 < R * Real.sin θ := mul_pos hR hsinθ
    nlinarith [mul_pos hRs hcosθ]
  have hsinθ_lt_one : Real.sin θ < 1 := by
    have hsinlt := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      ((neg_nonpos.mpr (show (0 : ℝ) ≤ Real.pi / 2 by positivity)).trans hθpos.le)
      (le_rfl : Real.pi / 2 ≤ Real.pi / 2) hθtop
    simpa using hsinlt
  have houter_lt_R : R * Real.sin θ < R := by
    nlinarith [mul_pos hR (sub_pos.mpr hsinθ_lt_one)]
  have parameter_abs_coordinate (t : ℝ) (ht : InAxialIncidenceDomain t) :
      |(semicirclePoint G.mirror .lower t).1.x - G.mirror.center.x| =
        R * Real.sin |t| := by
    have habs_pi : |t| ≤ Real.pi :=
      ht.le.trans (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi)
    have hsinabs := Real.abs_sin_eq_sin_abs_of_abs_le_pi habs_pi
    dsimp [semicirclePoint]
    have heq :
        G.mirror.center.x + G.mirror.radius * Real.sin t - G.mirror.center.x =
          R * Real.sin t := by dsimp [R]; ring
    rw [heq, abs_mul, abs_of_pos hR, hsinabs]
  ext x
  constructor
  · intro hx
    have haccepted : AcceptedIncomingCoordinate G x := hx
    have hordering := acceptedIncomingCoordinate_ordering G x haccepted
    have habs_outer : |x - G.mirror.center.x| ≤ R * Real.sin θ := by
      rcases haccepted.2 with hdirect | hreflected
      · have habs_a := (directlyAbsorbed_iff_abs_le G x).1 hdirect
        have habs_a' : |x - G.mirror.center.x| ≤ a := by
          simpa [a] using habs_a
        exact habs_a'.trans hhorizontal.le
      · have hnotdirect : ¬ IsDirectlyAbsorbed G x := by
          intro hd
          exact hordering.2 ⟨hd, hreflected⟩
        have houtside : a < |x - G.mirror.center.x| := by
          have hnle : ¬ |x - G.mirror.center.x| ≤ a := by
            intro hle
            exact hnotdirect ((directlyAbsorbed_iff_abs_le G x).2
              (by simpa [a] using hle))
          exact lt_of_not_ge hnle
        rcases canonicalMirrorFirst G x (by simpa [a] using houtside) haccepted.1 with
          ⟨t, sMirror, htdomain, hPx, hfirstCanonical, hmirror⟩
        rcases hreflected with
          ⟨sOld, QOld, hfirstOld, hmirrorOld, sHit, QHit, hHit, hNoSecond⟩
        have hdisjoint :
            ∀ P, InConcentratorFreeRegion G P → ¬ OnConcentratorBoundary G P := by
          intro P hfree hboundary
          exact concentratorRegion_disjoint_boundary G P ⟨hfree, hboundary⟩
        have hunique := firstForwardBoundaryContact_unique
          (InConcentratorFreeRegion G) (OnConcentratorBoundary G) hdisjoint
          (incomingSunlightRay G x) hfirstCanonical hfirstOld
        have hQeq : (semicirclePoint G.mirror .lower t).1 = QOld := hunique.2
        subst QOld
        have hray :
            rayAfterReflection G.mirror (incomingSunlightRay G x)
                (semicirclePoint G.mirror .lower t).1 hmirrorOld.1 =
              axialReflectedRay G.mirror .lower t := by
          rw [← hPx]
          exact reflectedKernel_eq_axial G t htdomain hmirrorOld
        rw [hray] at hHit hNoSecond
        have htaccepted : AcceptedReflectedRay G t := by
          refine ⟨hregime, htdomain, ?_⟩
          dsimp
          refine ⟨sMirror, ?_, hmirror, sHit, QHit, hHit, hNoSecond⟩
          simpa [hPx] using hfirstCanonical
        have htbound := hmax t htaccepted
        have hsinle : Real.sin |t| ≤ Real.sin θ :=
          Real.sin_le_sin_of_le_of_le_pi_div_two
            ((neg_nonpos.mpr (show (0 : ℝ) ≤ Real.pi / 2 by positivity)).trans
              (abs_nonneg t)) hθtop.le htbound
        have habscoord := parameter_abs_coordinate t htdomain
        rw [hPx] at habscoord
        rw [habscoord]
        exact mul_le_mul_of_nonneg_left hsinle hR.le
    rw [Set.mem_Icc]
    rw [abs_le] at habs_outer
    constructor <;> linarith [habs_outer.1, habs_outer.2]
  · intro hx
    rw [Set.mem_Icc] at hx
    have habs_outer : |x - G.mirror.center.x| ≤ R * Real.sin θ := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hrim : |x - G.mirror.center.x| < G.mirror.radius := by
      simpa [R] using habs_outer.trans_lt houter_lt_R
    refine ⟨hrim, ?_⟩
    by_cases hdirect : |x - G.mirror.center.x| ≤ a
    · exact Or.inl ((directlyAbsorbed_iff_abs_le G x).2
        (by simpa [a] using hdirect))
    · have houtside : a < |x - G.mirror.center.x| := lt_of_not_ge hdirect
      rcases canonicalMirrorFirst G x (by simpa [a] using houtside) hrim with
        ⟨t, sMirror, htdomain, hPx, hfirstMirror, hmirror⟩
      have habscoord := parameter_abs_coordinate t htdomain
      rw [hPx] at habscoord
      have hmul_le : R * Real.sin |t| ≤ R * Real.sin θ := by
        rw [← habscoord]
        exact habs_outer
      have hsinle : Real.sin |t| ≤ Real.sin θ :=
        (mul_le_mul_iff_of_pos_left hR).mp hmul_le
      have htmem : |t| ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨(neg_nonpos.mpr (show (0 : ℝ) ≤ Real.pi / 2 by positivity)).trans
            (abs_nonneg t), htdomain.le⟩
      have hθsinmem : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨(neg_nonpos.mpr (show (0 : ℝ) ≤ Real.pi / 2 by positivity)).trans
            hθpos.le, hθtop.le⟩
      have htbound : |t| ≤ θ :=
        (Real.strictMonoOn_sin.le_iff_le htmem hθsinmem).mp hsinle
      have htmem_f : |t| ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨abs_nonneg t, htdomain.le⟩
      have hperp : f |t| ≤ a := by
        have hmono := hf_strict.monotoneOn htmem_f hθmem htbound
        have hformula' : f θ = a := by simpa [f, R, a] using hformula
        rw [hformula'] at hmono
        exact hmono
      have hxcoord : x - G.mirror.center.x = R * Real.sin t := by
        rw [← hPx]
        dsimp [semicirclePoint, R]
        ring
      have houtparam : G.absorber.radius <
          |G.mirror.radius * Real.sin t| := by
        simpa [a, R, ← hxcoord] using houtside
      rcases axialHit_of_profile_le G t htdomain houtparam
          (by simpa [f, a, R] using hperp) with
        ⟨sHit, QHit, hHit, hNoSecond⟩
      have hray :
          rayAfterReflection G.mirror (incomingSunlightRay G x)
              (semicirclePoint G.mirror .lower t).1 hmirror.1 =
            axialReflectedRay G.mirror .lower t := by
        rw [← hPx]
        exact reflectedKernel_eq_axial G t htdomain hmirror
      refine Or.inr ⟨sMirror, (semicirclePoint G.mirror .lower t).1,
        hfirstMirror, hmirror, sHit, QHit, ?_, ?_⟩
      · rw [hray]
        exact hHit
      · rw [hray]
        exact hNoSecond

private lemma illuminatedAperture_measure_formula (G : ConcentratorGeometry) (θ : ℝ)
    (hθpos : 0 < θ) (hθtop : θ < Real.pi / 2)
    (hmax : ∀ t : ℝ, AcceptedReflectedRay G t → |t| ≤ θ)
    (hformula :
      G.mirror.radius * Real.sin θ * (1 - Real.cos θ) =
        G.absorber.radius) :
    (volume (illuminatedAperture G)).toReal =
      2 * G.mirror.radius * Real.sin θ := by
  rw [illuminatedAperture_eq_Icc G θ hθpos hθtop hmax hformula,
    Real.volume_Icc]
  have hnonneg :
      0 ≤ G.mirror.center.x + G.mirror.radius * Real.sin θ -
        (G.mirror.center.x - G.mirror.radius * Real.sin θ) := by
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [hθtop, Real.pi_pos])
    nlinarith [mul_pos G.mirror.radius_pos hsin]
  rw [ENNReal.toReal_ofReal hnonneg]
  ring

private lemma unmirroredReferenceAperture_measure_formula
    (G : ConcentratorGeometry) :
    (volume (unmirroredReferenceAperture G)).toReal =
      2 * G.absorber.radius := by
  rw [unmirroredReferenceAperture_eq_Icc G, Real.volume_Icc]
  have hnonneg :
      0 ≤ G.mirror.center.x + G.absorber.radius -
        (G.mirror.center.x - G.absorber.radius) := by
    have ha : 0 < G.absorber.radius := G.absorber.radius_pos
    linarith
  rw [ENNReal.toReal_ofReal hnonneg]
  ring

private lemma opticalState_tangent_formula {S : SourceData}
    {A : CandidateRadius S} (V : OpticalState S A) :
    (kernelGeometry S A).absorber.radius =
      (kernelGeometry S A).mirror.radius * Real.sin V.limitingAngle *
        (1 - Real.cos V.limitingAngle) := by
  let G := kernelGeometry S A
  let θ := V.limitingAngle
  rcases V.limitingAngle_spec.2.2.2.1 with ⟨s, Q, htangent⟩
  have hsq :=
    (tangentContact_distanceSq G
      (axialReflectedRay G.mirror .lower θ) htangent).2
  have hdet :
      displacementDirectionDet
          (displacement G.absorber.center
            (axialReflectedRay G.mirror .lower θ).origin)
          (axialReflectedRay G.mirror .lower θ).direction.1 =
        -(G.mirror.radius * Real.sin θ * (1 - Real.cos θ)) := by
    change
      ((axialReflectedRay G.mirror .lower θ).origin.x -
            G.mirror.center.x) *
          (axialReflectedRay G.mirror .lower θ).direction.1.y -
        ((axialReflectedRay G.mirror .lower θ).origin.y -
            (G.mirror.center.y - G.mirror.radius / 2)) *
          (axialReflectedRay G.mirror .lower θ).direction.1.x =
        -(G.mirror.radius * Real.sin θ * (1 - Real.cos θ))
    rw [axialReflectedRay_origin_x, axialReflectedRay_origin_y,
      axialReflectedRay_direction_x, axialReflectedRay_direction_y]
    ring
  rw [hdet] at hsq
  have hθpos : 0 < θ := V.limitingAngle_spec.1
  have hθtop : θ < Real.pi / 2 := V.limitingAngle_spec.2.1
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [hθtop, Real.pi_pos])
  have hcos : Real.cos θ < 1 := by
    simpa using
      (Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
        (show 0 ≤ (0 : ℝ) by norm_num) hθtop.le hθpos)
  have hfpos :
      0 < G.mirror.radius * Real.sin θ * (1 - Real.cos θ) :=
    mul_pos (mul_pos G.mirror.radius_pos hsin) (sub_pos.mpr hcos)
  change G.absorber.radius =
    G.mirror.radius * Real.sin θ * (1 - Real.cos θ)
  apply (sq_eq_sq₀ G.absorber.radius_pos.le hfpos.le).mp
  calc
    G.absorber.radius ^ 2 =
        (-(G.mirror.radius * Real.sin θ * (1 - Real.cos θ))) ^ 2 := hsq
    _ = (G.mirror.radius * Real.sin θ * (1 - Real.cos θ)) ^ 2 := by ring

/-- Each admissible candidate has exactly one complete limiting optical state. -/
theorem OpticalState.existsUnique (S : SourceData) (A : CandidateRadius S) :
    ∃ W : OpticalState S A, ∀ V : OpticalState S A, V = W := by
  let G := kernelGeometry S A
  let R : ℝ := G.mirror.radius
  let a : ℝ := G.absorber.radius
  have hR : 0 < R := G.mirror.radius_pos
  have ha : 0 < a := G.absorber.radius_pos
  have ha_half : a < R / 2 := G.absorberRadius_lt_half
  have haR : a < R := by linarith
  let f : ℝ → ℝ := fun t => R * Real.sin t * (1 - Real.cos t)
  have hf_cont : Continuous f := by
    fun_prop
  have hf_zero : f 0 = 0 := by simp [f]
  have hf_top : f (Real.pi / 2) = R := by simp [f]
  have hf_strict : StrictMonoOn f (Set.Icc 0 (Real.pi / 2)) := by
    simpa [f] using tangentProfile_strictMonoOn R hR
  have ha_mem : a ∈ Set.Icc (f 0) (f (Real.pi / 2)) := by
    rw [hf_zero, hf_top]
    exact ⟨ha.le, haR.le⟩
  rcases (intermediate_value_Icc (show (0 : ℝ) ≤ Real.pi / 2 by
      linarith [Real.pi_pos]) hf_cont.continuousOn ha_mem) with
    ⟨θ, hθmem, hθeq⟩
  have hfθ : f θ = a := hθeq
  have hθpos : 0 < θ := by
    rcases hθmem with ⟨hθnonneg, _⟩
    apply lt_of_le_of_ne hθnonneg
    intro hzero
    have : θ = 0 := hzero.symm
    subst θ
    rw [hf_zero] at hfθ
    linarith
  have hθtop : θ < Real.pi / 2 := by
    rcases hθmem with ⟨_, hθle⟩
    apply lt_of_le_of_ne hθle
    intro htop
    have : θ = Real.pi / 2 := htop
    subst θ
    rw [hf_top] at hfθ
    linarith
  have hθdomain : InAxialIncidenceDomain θ := by
    change |θ| < Real.pi / 2
    rw [abs_of_pos hθpos]
    exact hθtop
  have reflected_origin_x (t : ℝ) := axialReflectedRay_origin_x G t
  have reflected_origin_y (t : ℝ) := axialReflectedRay_origin_y G t
  have reflected_direction_x (t : ℝ) := axialReflectedRay_direction_x G t
  have reflected_direction_y (t : ℝ) := axialReflectedRay_direction_y G t
  have reflected_point_x (t u : ℝ) := axialReflectedRay_point_x G t u
  have reflected_point_y (t u : ℝ) := axialReflectedRay_point_y G t u
  have reflected_mirror_norm (t u : ℝ) :
      displacementNormSq
          (displacement G.mirror.center
            ((axialReflectedRay G.mirror .lower t).pointAt u)) =
        R ^ 2 - 2 * R * Real.cos t * u + u ^ 2 := by
    simpa [R] using axialReflectedRay_mirror_norm G t u
  have reflected_absorber_norm (t u : ℝ) :
      displacementNormSq
          (displacement G.absorber.center
            ((axialReflectedRay G.mirror .lower t).pointAt u)) =
        (R * Real.sin t * (1 - Real.cos t)) ^ 2 +
          (u - R * (1 / 2 + Real.cos t - Real.cos t ^ 2)) ^ 2 := by
    simpa [R] using axialReflectedRay_absorber_norm G t u
  have hregime : InOneReflectionRegime G := concentrator_inOneReflectionRegime G
  have hcosθ : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp hθdomain)
  have hcosθ_lt_one : Real.cos θ < 1 := by
    simpa using
      (Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (show 0 ≤ (0 : ℝ) by norm_num)
        hθtop.le hθpos)
  have hsinθ : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [hθtop, Real.pi_pos])
  have hfa : R * Real.sin θ * (1 - Real.cos θ) = a := by
    simpa [f] using hfθ
  let sT : ℝ := R * (1 / 2 + Real.cos θ - Real.cos θ ^ 2)
  have hsT : 0 < sT := by
    dsimp [sT]
    have hcprod : 0 < Real.cos θ * (1 - Real.cos θ) :=
      mul_pos hcosθ (by linarith)
    nlinarith [mul_pos hR (by nlinarith :
      0 < (1 / 2 : ℝ) + Real.cos θ * (1 - Real.cos θ))]
  let QT : Point2 := (axialReflectedRay G.mirror .lower θ).pointAt sT
  have hfirstT : IsFirstContainerContact G
      (axialReflectedRay G.mirror .lower θ) sT QT := by
    refine ⟨hsT, rfl, ?_, ?_⟩
    · change displacementNormSq (displacement G.absorber.center QT) =
        G.absorber.radius ^ 2
      rw [show QT = (axialReflectedRay G.mirror .lower θ).pointAt sT by rfl,
        reflected_absorber_norm]
      dsimp [sT, a] at hfa ⊢
      rw [hfa]
      ring
    · intro u hu hus
      rw [reflected_absorber_norm]
      have hune : u - sT ≠ 0 := by linarith
      have hsqpos : 0 < (u - sT) ^ 2 := sq_pos_of_ne_zero hune
      have hsqpos' :
          0 < (u - R * (1 / 2 + Real.cos θ - Real.cos θ ^ 2)) ^ 2 := by
        simpa [sT] using hsqpos
      dsimp [sT, a] at hfa ⊢
      rw [hfa]
      nlinarith [hsqpos']
  have htangentT : IsTangentContainerContact G
      (axialReflectedRay G.mirror .lower θ) sT QT := by
    refine ⟨hfirstT, ?_⟩
    dsimp [displacementDirectionDot, displacement, QT]
    rw [reflected_point_x, reflected_point_y, reflected_direction_x,
      reflected_direction_y]
    simp only [ConcentratorGeometry.absorber]
    have htrig := Real.sin_sq_add_cos_sq θ
    have hsin_sq : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith
    dsimp [sT, R]
    ring_nf
    rw [hsin_sq]
    ring
  let Pθ : Point2 := (semicirclePoint G.mirror .lower θ).1
  have hmirrorθ : OnReflectingArc G.lowerMirror Pθ := by
    exact (semicirclePoint_invariants G.mirror .lower .mirror θ hθdomain).1
  let sM : ℝ := R * Real.cos θ
  have hsM : 0 < sM := mul_pos hR hcosθ
  have hPθx : Pθ.x = G.mirror.center.x + R * Real.sin θ := by rfl
  have hPθy : Pθ.y = G.mirror.center.y - R * Real.cos θ := by
    dsimp [Pθ, semicirclePoint, orientationSign, R]
    ring
  have hhorizontal : a < R * Real.sin θ := by
    rw [← hfa]
    have hRs : 0 < R * Real.sin θ := mul_pos hR hsinθ
    nlinarith [mul_pos hRs hcosθ]
  have hincomingT : IsFirstConcentratorContact G
      (incomingSunlightRay G Pθ.x) sM Pθ := by
    refine ⟨hsM, ?_, Or.inl hmirrorθ, ?_⟩
    · simp [Pθ, sM, R, ForwardRay.pointAt, incomingSunlightRay, translate,
        directionDisplacement, axisDirection, orientationSign, semicirclePoint]
    · intro u hu hus
      constructor
      · constructor
        · simpa [ConcentratorGeometry.lowerMirror, ForwardRay.pointAt,
            incomingSunlightRay, translate, directionDisplacement,
            axisDirection, orientationSign] using hu
        · change displacementNormSq
              (displacement G.mirror.center
                ((incomingSunlightRay G Pθ.x).pointAt u)) < G.mirror.radius ^ 2
          dsimp [displacementNormSq, displacement, ForwardRay.pointAt,
            incomingSunlightRay, translate, directionDisplacement,
            axisDirection, orientationSign]
          rw [hPθx]
          have hu_sq : u ^ 2 < (R * Real.cos θ) ^ 2 := by
            exact (sq_lt_sq₀ hu.le hsM.le).2 (by simpa [sM] using hus)
          have hcircle_sq :
              (R * Real.sin θ) ^ 2 + (R * Real.cos θ) ^ 2 = R ^ 2 := by
            calc
              (R * Real.sin θ) ^ 2 + (R * Real.cos θ) ^ 2 =
                  R ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
              _ = R ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]
          norm_num at ⊢
          change (R * Real.sin θ) ^ 2 + u ^ 2 < R ^ 2
          linarith
      · intro hin
        change displacementNormSq
            (displacement G.absorber.center
              ((incomingSunlightRay G Pθ.x).pointAt u)) ≤
          G.absorber.radius ^ 2 at hin
        dsimp [displacementNormSq, displacement, ForwardRay.pointAt,
          incomingSunlightRay, translate, directionDisplacement,
          axisDirection, orientationSign, ConcentratorGeometry.absorber, a]
          at hin
        rw [hPθx] at hin
        norm_num at hin
        have hh_sq : a ^ 2 < (R * Real.sin θ) ^ 2 :=
          (sq_lt_sq₀ ha.le (mul_pos hR hsinθ).le).2 hhorizontal
        change (R * Real.sin θ) ^ 2 +
            (-u + G.mirror.radius / 2) ^ 2 ≤ G.absorberRadius ^ 2 at hin
        have hle0 : (R * Real.sin θ) ^ 2 ≤ G.absorberRadius ^ 2 :=
          (le_add_of_nonneg_right (sq_nonneg _)).trans hin
        have hle : (R * Real.sin θ) ^ 2 ≤ a ^ 2 := by
          simpa [a, ConcentratorGeometry.absorber] using hle0
        exact (not_lt_of_ge hle) hh_sq
  have hacceptedT : AcceptedReflectedRay G θ := by
    refine ⟨hregime, hθdomain, ?_⟩
    dsimp
    refine ⟨sM, ?_, hmirrorθ, sT, QT, hfirstT, ?_⟩
    · simpa [Pθ] using hincomingT
    · exact hregime θ hθdomain sT QT hfirstT
  have hmax : ∀ t : ℝ, AcceptedReflectedRay G t → |t| ≤ θ := by
    intro t haccepted
    rcases haccepted with ⟨_htregime, htdomain, htdata⟩
    dsimp at htdata
    rcases htdata with
      ⟨_sMirror, _hfirstMirror, _hmirror, sHit, QHit, hhit, _hnoSecond⟩
    rcases hhit with ⟨hsHit, hQHit, hcircleHit, _hbeforeHit⟩
    have hhit_norm :
        (R * Real.sin t * (1 - Real.cos t)) ^ 2 +
            (sHit - R * (1 / 2 + Real.cos t - Real.cos t ^ 2)) ^ 2 =
          a ^ 2 := by
      calc
        (R * Real.sin t * (1 - Real.cos t)) ^ 2 +
              (sHit - R * (1 / 2 + Real.cos t - Real.cos t ^ 2)) ^ 2 =
            displacementNormSq
              (displacement G.absorber.center
                ((axialReflectedRay G.mirror .lower t).pointAt sHit)) :=
          (reflected_absorber_norm t sHit).symm
        _ = displacementNormSq (displacement G.absorber.center QHit) := by rw [hQHit]
        _ = a ^ 2 := by
          simpa [OnCircle, a] using hcircleHit
    have hperp_sq :
        (R * Real.sin t * (1 - Real.cos t)) ^ 2 ≤ a ^ 2 := by
      calc
        (R * Real.sin t * (1 - Real.cos t)) ^ 2 ≤
            (R * Real.sin t * (1 - Real.cos t)) ^ 2 +
              (sHit - R * (1 / 2 + Real.cos t - Real.cos t ^ 2)) ^ 2 :=
          le_add_of_nonneg_right (sq_nonneg _)
        _ = a ^ 2 := hhit_norm
    have htmem : |t| ∈ Set.Icc 0 (Real.pi / 2) := by
      exact ⟨abs_nonneg t, (le_of_lt htdomain)⟩
    have hft_nonneg : 0 ≤ f |t| := by
      have hsin_nonneg : 0 ≤ Real.sin |t| :=
        Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg t)
          (by linarith [htmem.2, Real.pi_pos])
      have hcos_le : Real.cos |t| ≤ 1 := Real.cos_le_one _
      dsimp [f]
      exact mul_nonneg (mul_nonneg hR.le hsin_nonneg) (sub_nonneg.mpr hcos_le)
    have hft_sq :
        (f |t|) ^ 2 = (R * Real.sin t * (1 - Real.cos t)) ^ 2 := by
      by_cases ht : 0 ≤ t
      · simp [abs_of_nonneg ht, f]
      · have ht' : t ≤ 0 := le_of_not_ge ht
        rw [abs_of_nonpos ht']
        simp only [f, Real.sin_neg, Real.cos_neg]
        ring
    have hft_le : f |t| ≤ a := by
      apply (sq_le_sq₀ hft_nonneg ha.le).mp
      rw [hft_sq]
      exact hperp_sq
    by_contra hnot
    have hθt : θ < |t| := not_le.mp hnot
    have hstrict := hf_strict hθmem htmem hθt
    rw [hfθ] at hstrict
    exact (not_lt_of_ge hft_le) hstrict
  have href_eq :
      unmirroredReferenceAperture G =
        Set.Icc (G.mirror.center.x - a) (G.mirror.center.x + a) := by
    simpa [a] using unmirroredReferenceAperture_eq_Icc G
  have href_meas : HasMeasurableReferenceAperture G := by
    change MeasurableSet (unmirroredReferenceAperture G)
    rw [href_eq]
    exact measurableSet_Icc
  have hill_eq :
      illuminatedAperture G =
        Set.Icc (G.mirror.center.x - R * Real.sin θ)
          (G.mirror.center.x + R * Real.sin θ) := by
    simpa [R, a] using
      illuminatedAperture_eq_Icc G θ hθpos hθtop hmax hfa
  have hill_meas : HasMeasurableIlluminatedAperture G := by
    change MeasurableSet (illuminatedAperture G)
    rw [hill_eq]
    exact measurableSet_Icc
  let W : OpticalState S A :=
    { oneReflectionRegime := hregime
      limitingAngle := θ
      limitingAngle_spec :=
        ⟨hθpos, hθtop, hacceptedT, ⟨sT, QT, htangentT⟩, hmax⟩
      illuminatedMeasurable := hill_meas
      referenceMeasurable := href_meas }
  refine ⟨W, ?_⟩
  intro V
  have hVle : V.limitingAngle ≤ θ := by
    have := hmax V.limitingAngle V.limitingAngle_spec.2.2.1
    simpa [abs_of_pos V.limitingAngle_spec.1] using this
  have hθle : θ ≤ V.limitingAngle := by
    have := V.limitingAngle_spec.2.2.2.2 θ hacceptedT
    simpa [abs_of_pos hθpos] using this
  have hangle : V.limitingAngle = W.limitingAngle := by
    dsimp [W]
    exact le_antisymm hVle hθle
  rcases V with ⟨vregime, vangle, vspec, vill, vref⟩
  rcases W with ⟨wregime, wangle, wspec, will, wref⟩
  dsimp at hangle
  subst wangle
  rfl

/-- The unmirrored absorber presents a strictly positive transverse measure. -/
lemma referenceTransverseMeasure_pos (S : SourceData) (A : CandidateRadius S)
    (W : OpticalState S A) :
    0 < ISQDimensions.coordinateInSI SIUnitChoices.SI
      (referenceTransverseMeasure SIUnitChoices.SI (kernelGeometry S A)
        W.referenceMeasurable) := by
  let G := kernelGeometry S A
  let a : ℝ := G.absorber.radius
  let c : ℝ := G.absorber.center.x
  have ha : 0 < a := G.absorber.radius_pos
  have haR : a < G.mirror.radius / 2 := by
    exact G.absorberRadius_lt_half
  have hsubset : Set.Ioo (c - a) (c + a) ⊆ unmirroredReferenceAperture G := by
    intro x hx
    have habs : |x - c| < a := by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have hdxsq : (x - c) ^ 2 < a ^ 2 := by
      have hsquare := (sq_lt_sq₀ (abs_nonneg (x - c)) ha.le).2 habs
      simpa only [sq_abs] using hsquare
    have hrad : 0 ≤ a ^ 2 - (x - c) ^ 2 := by linarith
    let t : ℝ := Real.sqrt (a ^ 2 - (x - c) ^ 2)
    have ht : 0 ≤ t := Real.sqrt_nonneg _
    have ht_sq : t ^ 2 = a ^ 2 - (x - c) ^ 2 := by
      exact Real.sq_sqrt hrad
    have ht_sq' :
        t ^ 2 = G.absorberRadius ^ 2 - (x - G.mirror.center.x) ^ 2 := by
      simpa [a, c, ConcentratorGeometry.absorber] using ht_sq
    have ht_le_a : t ≤ a := by
      nlinarith [sq_nonneg (x - c)]
    let s : ℝ := G.mirror.radius / 2 - t
    have hs : 0 < s := by dsimp [s]; linarith
    let Q := (incomingSunlightRay G x).pointAt s
    refine ⟨s, Q, hs, rfl, ?_, ?_⟩
    · change displacementNormSq (displacement G.absorber.center Q) =
        G.absorber.radius ^ 2
      dsimp [Q, ForwardRay.pointAt, incomingSunlightRay, translate,
        directionDisplacement, axisDirection, orientationSign,
        ConcentratorGeometry.absorber, a, c, s] at ⊢
      dsimp [displacementNormSq, displacement]
      norm_num at ⊢
      nlinarith [ht_sq']
    · intro u hu hus
      change displacementNormSq
          (displacement G.absorber.center ((incomingSunlightRay G x).pointAt u)) >
        G.absorber.radius ^ 2
      have hvertical : t < G.mirror.radius / 2 - u := by
        dsimp [s] at hus
        linarith
      have hvertical_sq :
          t ^ 2 < (G.mirror.radius / 2 - u) ^ 2 := by
        exact (sq_lt_sq₀ ht (by linarith)).2 hvertical
      dsimp [ForwardRay.pointAt, incomingSunlightRay, translate,
        directionDisplacement, axisDirection, orientationSign,
        ConcentratorGeometry.absorber, a, c]
      dsimp [displacementNormSq, displacement]
      norm_num at ⊢
      nlinarith [ht_sq']
  have hinterval_pos : 0 < volume (Set.Ioo (c - a) (c + a)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.2 (by linarith)
  have href_pos : 0 < volume (unmirroredReferenceAperture G) :=
    lt_of_lt_of_le hinterval_pos (measure_mono hsubset)
  have href_ne_top := (transverseApertures_bounded G).2.2.2
  have hcoord := (transverseMeasures_coordinate SIUnitChoices.SI G
    W.illuminatedMeasurable W.referenceMeasurable).2.1
  rw [hcoord]
  exact ENNReal.toReal_pos (ne_of_gt href_pos) href_ne_top

/-- Dimensionless residual of the mirrored-to-reference aperture ratio from
the required fivefold factor. -/
def fivefoldResidual (S : SourceData) (A : CandidateRadius S)
    (W : OpticalState S A) : ℝ :=
  ISQDimensions.coordinateInSI SIUnitChoices.SI
      (transverseFluxMeasure SIUnitChoices.SI (kernelGeometry S A)
        W.illuminatedMeasurable) /
    ISQDimensions.coordinateInSI SIUnitChoices.SI
      (referenceTransverseMeasure SIUnitChoices.SI (kernelGeometry S A)
        W.referenceMeasurable) - 5

private lemma fivefoldResidual_formula (S : SourceData) (A : CandidateRadius S)
    (W : OpticalState S A) :
    fivefoldResidual S A W =
      1 / (1 - Real.cos W.limitingAngle) - 5 := by
  let G := kernelGeometry S A
  let θ := W.limitingAngle
  have hθpos : 0 < θ := W.limitingAngle_spec.1
  have hθtop : θ < Real.pi / 2 := W.limitingAngle_spec.2.1
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [hθtop, Real.pi_pos])
  have hcos : Real.cos θ < 1 := by
    simpa using
      (Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
        (show 0 ≤ (0 : ℝ) by norm_num) hθtop.le hθpos)
  have hformula :
      G.mirror.radius * Real.sin θ * (1 - Real.cos θ) =
        G.absorber.radius := by
    simpa [G, θ] using (opticalState_tangent_formula W).symm
  have hill :
      (volume (illuminatedAperture G)).toReal =
        2 * G.mirror.radius * Real.sin θ :=
    illuminatedAperture_measure_formula G θ hθpos hθtop
      W.limitingAngle_spec.2.2.2.2 hformula
  have href :
      (volume (unmirroredReferenceAperture G)).toReal =
        2 * G.absorber.radius :=
    unmirroredReferenceAperture_measure_formula G
  have hcoords := transverseMeasures_coordinate SIUnitChoices.SI G
    W.illuminatedMeasurable W.referenceMeasurable
  dsimp [θ] at hθpos hθtop hsin hcos hformula hill
  change
    ISQDimensions.coordinateInSI SIUnitChoices.SI
          (transverseFluxMeasure SIUnitChoices.SI (kernelGeometry S A)
            W.illuminatedMeasurable) /
        ISQDimensions.coordinateInSI SIUnitChoices.SI
          (referenceTransverseMeasure SIUnitChoices.SI (kernelGeometry S A)
            W.referenceMeasurable) - 5 =
      1 / (1 - Real.cos W.limitingAngle) - 5
  rw [hcoords.1, hcoords.2.1, hill, href, ← hformula]
  change
    (2 * G.mirror.radius * Real.sin θ) /
          (2 * (G.mirror.radius * Real.sin θ * (1 - Real.cos θ))) - 5 =
      1 / (1 - Real.cos θ) - 5
  have hkne : 2 * G.mirror.radius * Real.sin θ ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (ne_of_gt G.mirror.radius_pos))
      (ne_of_gt hsin)
  have hquot :
      (2 * G.mirror.radius * Real.sin θ) /
          (2 * (G.mirror.radius * Real.sin θ * (1 - Real.cos θ))) =
        1 / (1 - Real.cos θ) := by
    rw [show
      2 * (G.mirror.radius * Real.sin θ * (1 - Real.cos θ)) =
          (2 * G.mirror.radius * Real.sin θ) * (1 - Real.cos θ) by ring]
    calc
      (2 * G.mirror.radius * Real.sin θ) /
            ((2 * G.mirror.radius * Real.sin θ) * (1 - Real.cos θ)) =
          (2 * G.mirror.radius * Real.sin θ) /
              (2 * G.mirror.radius * Real.sin θ) /
                (1 - Real.cos θ) :=
        (div_div (2 * G.mirror.radius * Real.sin θ)
          (2 * G.mirror.radius * Real.sin θ) (1 - Real.cos θ)).symm
      _ = 1 / (1 - Real.cos θ) := by rw [div_self hkne]
  rw [hquot]

/-- The common-input uniform-power laws and the fivefold power relation at an
arbitrary uniform irradiance. -/
def IsRadiusSolutionAtIrradiance (S : SourceData) (I : Irradiance)
    (A : CandidateRadius S) : Prop :=
  ∃ hI : UniformIrradiance SIUnitChoices.SI I,
    ∃ W : OpticalState S A,
      ∃ P P₀ : ISQDimensions.HeatRate,
        IsUniformPowerPair SIUnitChoices.SI (physicalConcentrator S A)
            W.oneReflectionRegime W.illuminatedMeasurable W.referenceMeasurable
            I hI S.axialExtent S.axialExtent_pos P P₀ ∧
          0 < ISQDimensions.coordinateInSI SIUnitChoices.SI P₀ ∧
          IsPowerRatio SIUnitChoices.SI (physicalConcentrator S A)
            W.oneReflectionRegime W.illuminatedMeasurable W.referenceMeasurable
            I hI S.axialExtent S.axialExtent_pos P P₀ 5

/-- For fixed state, irradiance, and axial extent, both typed uniform powers
are uniquely determined. -/
lemma uniformPowerPair_unique {S : SourceData} {A : CandidateRadius S}
    (W : OpticalState S A) (I : Irradiance)
    (hI : UniformIrradiance SIUnitChoices.SI I)
    (P P₀ Q Q₀ : ISQDimensions.HeatRate)
    (hP : IsUniformPowerPair SIUnitChoices.SI (physicalConcentrator S A)
      W.oneReflectionRegime W.illuminatedMeasurable W.referenceMeasurable
      I hI S.axialExtent S.axialExtent_pos P P₀)
    (hQ : IsUniformPowerPair SIUnitChoices.SI (physicalConcentrator S A)
      W.oneReflectionRegime W.illuminatedMeasurable W.referenceMeasurable
      I hI S.axialExtent S.axialExtent_pos Q Q₀) :
    P = Q ∧ P₀ = Q₀ := by
  have hunique := existsUnique_uniformPowers SIUnitChoices.SI
    (physicalConcentrator S A) W.oneReflectionRegime W.illuminatedMeasurable
    W.referenceMeasurable I hI S.axialExtent S.axialExtent_pos
  exact ⟨hunique.1.unique hP.1 hQ.1,
    hunique.2.unique hP.2 hQ.2⟩

/-- Scaling a strictly positive uniform irradiance cannot change which radius
satisfies the common-input fivefold power condition. -/
theorem isRadiusSolutionAtIrradiance_iff (S : SourceData)
    (A : CandidateRadius S) (I J : Irradiance)
    (hIpos : 0 < ISQDimensions.coordinateInSI SIUnitChoices.SI I)
    (hJpos : 0 < ISQDimensions.coordinateInSI SIUnitChoices.SI J)
    (hI : UniformIrradiance SIUnitChoices.SI I)
    (hJ : UniformIrradiance SIUnitChoices.SI J) :
    IsRadiusSolutionAtIrradiance S I A ↔
      IsRadiusSolutionAtIrradiance S J A := by
  have transfer (I J : Irradiance)
      (hIpos : 0 < ISQDimensions.coordinateInSI SIUnitChoices.SI I)
      (hJpos : 0 < ISQDimensions.coordinateInSI SIUnitChoices.SI J)
      (hJ : UniformIrradiance SIUnitChoices.SI J)
      (hsol : IsRadiusSolutionAtIrradiance S I A) :
      IsRadiusSolutionAtIrradiance S J A := by
    rcases hsol with ⟨_hI, W, P, P₀, hpair, _hP₀pos, hratio⟩
    let G := kernelGeometry S A
    let μ := transverseFluxMeasure SIUnitChoices.SI G W.illuminatedMeasurable
    let μ₀ := referenceTransverseMeasure SIUnitChoices.SI G W.referenceMeasurable
    have hmeasures := transverseMeasures_coordinate SIUnitChoices.SI G
      W.illuminatedMeasurable W.referenceMeasurable
    have harea := collectingArea_coordinate SIUnitChoices.SI μ S.axialExtent
      hmeasures.2.2.1 S.axialExtent_pos
    have harea₀ := collectingArea_coordinate SIUnitChoices.SI μ₀ S.axialExtent
      hmeasures.2.2.2.1 S.axialExtent_pos
    have hPcoord :
        ISQDimensions.coordinateInSI SIUnitChoices.SI P =
          ISQDimensions.coordinateInSI SIUnitChoices.SI I *
            (ISQDimensions.coordinateInSI SIUnitChoices.SI μ *
              ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent) := by
      have h := hpair.1
      change ISQDimensions.coordinateInSI SIUnitChoices.SI P =
        ISQDimensions.coordinateInSI SIUnitChoices.SI I *
          ISQDimensions.coordinateInSI SIUnitChoices.SI
            (collectingArea SIUnitChoices.SI μ S.axialExtent) at h
      rw [harea.1] at h
      exact h
    have hP₀coord :
        ISQDimensions.coordinateInSI SIUnitChoices.SI P₀ =
          ISQDimensions.coordinateInSI SIUnitChoices.SI I *
            (ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀ *
              ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent) := by
      have h := hpair.2
      change ISQDimensions.coordinateInSI SIUnitChoices.SI P₀ =
        ISQDimensions.coordinateInSI SIUnitChoices.SI I *
          ISQDimensions.coordinateInSI SIUnitChoices.SI
            (collectingArea SIUnitChoices.SI μ₀ S.axialExtent) at h
      rw [harea₀.1] at h
      exact h
    have hμ :
        ISQDimensions.coordinateInSI SIUnitChoices.SI μ =
          5 * ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀ := by
      have hpower := hratio.2.2
      have hfactor :
          ISQDimensions.coordinateInSI SIUnitChoices.SI I *
              ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent ≠ 0 :=
        mul_ne_zero (ne_of_gt hIpos) (ne_of_gt S.axialExtent_pos)
      apply mul_left_cancel₀ hfactor
      calc
        (ISQDimensions.coordinateInSI SIUnitChoices.SI I *
              ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent) *
            ISQDimensions.coordinateInSI SIUnitChoices.SI μ =
            ISQDimensions.coordinateInSI SIUnitChoices.SI P := by
              rw [hPcoord]
              ring
        _ = 5 * ISQDimensions.coordinateInSI SIUnitChoices.SI P₀ := hpower
        _ = (ISQDimensions.coordinateInSI SIUnitChoices.SI I *
              ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent) *
            (5 * ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀) := by
              rw [hP₀coord]
              ring
    rcases (existsUnique_uniformPowers SIUnitChoices.SI
      (physicalConcentrator S A) W.oneReflectionRegime W.illuminatedMeasurable
      W.referenceMeasurable J hJ S.axialExtent S.axialExtent_pos).1 with
      ⟨Q, hQ, _⟩
    rcases (existsUnique_uniformPowers SIUnitChoices.SI
      (physicalConcentrator S A) W.oneReflectionRegime W.illuminatedMeasurable
      W.referenceMeasurable J hJ S.axialExtent S.axialExtent_pos).2 with
      ⟨Q₀, hQ₀, _⟩
    have hQcoord :
        ISQDimensions.coordinateInSI SIUnitChoices.SI Q =
          ISQDimensions.coordinateInSI SIUnitChoices.SI J *
            (ISQDimensions.coordinateInSI SIUnitChoices.SI μ *
              ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent) := by
      change ISQDimensions.coordinateInSI SIUnitChoices.SI Q =
        ISQDimensions.coordinateInSI SIUnitChoices.SI J *
          ISQDimensions.coordinateInSI SIUnitChoices.SI
            (collectingArea SIUnitChoices.SI μ S.axialExtent) at hQ
      rw [harea.1] at hQ
      exact hQ
    have hQ₀coord :
        ISQDimensions.coordinateInSI SIUnitChoices.SI Q₀ =
          ISQDimensions.coordinateInSI SIUnitChoices.SI J *
            (ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀ *
              ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent) := by
      change ISQDimensions.coordinateInSI SIUnitChoices.SI Q₀ =
        ISQDimensions.coordinateInSI SIUnitChoices.SI J *
          ISQDimensions.coordinateInSI SIUnitChoices.SI
            (collectingArea SIUnitChoices.SI μ₀ S.axialExtent) at hQ₀
      rw [harea₀.1] at hQ₀
      exact hQ₀
    have hμ₀pos : 0 < ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀ := by
      exact referenceTransverseMeasure_pos S A W
    have hQ₀pos : 0 < ISQDimensions.coordinateInSI SIUnitChoices.SI Q₀ := by
      rw [hQ₀coord]
      exact mul_pos hJpos (mul_pos hμ₀pos S.axialExtent_pos)
    have hQratio :
        ISQDimensions.coordinateInSI SIUnitChoices.SI Q =
          5 * ISQDimensions.coordinateInSI SIUnitChoices.SI Q₀ := by
      rw [hQcoord, hQ₀coord, hμ]
      ring
    refine ⟨hJ, W, Q, Q₀, ⟨hQ, hQ₀⟩, hQ₀pos, ?_⟩
    exact ⟨⟨hQ, hQ₀⟩, hQ₀pos, hQratio⟩
  exact ⟨transfer I J hIpos hJpos hJ,
    transfer J I hJpos hIpos hI⟩

/-- Physical radius solution for the fixed one-metre source and its fixed
nonzero uniform irradiance. -/
def IsRadiusSolution (S : SourceData) (A : CandidateRadius S) : Prop :=
  IsRadiusSolutionAtIrradiance S S.irradiance A

/-- For any (necessarily unique) optical state, the physical fivefold power
condition is equivalent to vanishing dimensionless aperture residual. -/
lemma isRadiusSolution_iff_fivefoldResidual_eq_zero (S : SourceData)
    (A : CandidateRadius S) (W : OpticalState S A) :
    IsRadiusSolution S A ↔ fivefoldResidual S A W = 0 := by
  let G := kernelGeometry S A
  let μ := transverseFluxMeasure SIUnitChoices.SI G W.illuminatedMeasurable
  let μ₀ := referenceTransverseMeasure SIUnitChoices.SI G W.referenceMeasurable
  have hmeasures := transverseMeasures_coordinate SIUnitChoices.SI G
    W.illuminatedMeasurable W.referenceMeasurable
  have harea := collectingArea_coordinate SIUnitChoices.SI μ S.axialExtent
    hmeasures.2.2.1 S.axialExtent_pos
  have harea₀ := collectingArea_coordinate SIUnitChoices.SI μ₀ S.axialExtent
    hmeasures.2.2.2.1 S.axialExtent_pos
  have hμ₀pos : 0 < ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀ :=
    referenceTransverseMeasure_pos S A W
  have hμ₀ne : ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀ ≠ 0 :=
    ne_of_gt hμ₀pos
  constructor
  · rintro ⟨_hI, V, P, P₀, hpair, _hP₀pos, hratio⟩
    have hVW : V = W := by
      rcases OpticalState.existsUnique S A with ⟨W₀, hW₀⟩
      exact (hW₀ V).trans (hW₀ W).symm
    subst V
    have hPcoord :
        ISQDimensions.coordinateInSI SIUnitChoices.SI P =
          ISQDimensions.coordinateInSI SIUnitChoices.SI S.irradiance *
            (ISQDimensions.coordinateInSI SIUnitChoices.SI μ *
              ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent) := by
      have h := hpair.1
      change ISQDimensions.coordinateInSI SIUnitChoices.SI P =
        ISQDimensions.coordinateInSI SIUnitChoices.SI S.irradiance *
          ISQDimensions.coordinateInSI SIUnitChoices.SI
            (collectingArea SIUnitChoices.SI μ S.axialExtent) at h
      rw [harea.1] at h
      exact h
    have hP₀coord :
        ISQDimensions.coordinateInSI SIUnitChoices.SI P₀ =
          ISQDimensions.coordinateInSI SIUnitChoices.SI S.irradiance *
            (ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀ *
              ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent) := by
      have h := hpair.2
      change ISQDimensions.coordinateInSI SIUnitChoices.SI P₀ =
        ISQDimensions.coordinateInSI SIUnitChoices.SI S.irradiance *
          ISQDimensions.coordinateInSI SIUnitChoices.SI
            (collectingArea SIUnitChoices.SI μ₀ S.axialExtent) at h
      rw [harea₀.1] at h
      exact h
    have hfactor :
        ISQDimensions.coordinateInSI SIUnitChoices.SI S.irradiance *
            ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent ≠ 0 :=
      mul_ne_zero (ne_of_gt S.irradiance_pos) (ne_of_gt S.axialExtent_pos)
    have hμ :
        ISQDimensions.coordinateInSI SIUnitChoices.SI μ =
          5 * ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀ := by
      apply mul_left_cancel₀ hfactor
      calc
        (ISQDimensions.coordinateInSI SIUnitChoices.SI S.irradiance *
              ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent) *
            ISQDimensions.coordinateInSI SIUnitChoices.SI μ =
            ISQDimensions.coordinateInSI SIUnitChoices.SI P := by
              rw [hPcoord]
              ring
        _ = 5 * ISQDimensions.coordinateInSI SIUnitChoices.SI P₀ := hratio.2.2
        _ = (ISQDimensions.coordinateInSI SIUnitChoices.SI S.irradiance *
              ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent) *
            (5 * ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀) := by
              rw [hP₀coord]
              ring
    change ISQDimensions.coordinateInSI SIUnitChoices.SI μ /
        ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀ - 5 = 0
    rw [hμ]
    field_simp [hμ₀ne]
    ring
  · intro hzero
    have hμ :
        ISQDimensions.coordinateInSI SIUnitChoices.SI μ =
          5 * ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀ := by
      change ISQDimensions.coordinateInSI SIUnitChoices.SI μ /
          ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀ - 5 = 0 at hzero
      apply (div_eq_iff hμ₀ne).mp
      linarith
    let hI := S.uniformIrradiance
    rcases (existsUnique_uniformPowers SIUnitChoices.SI
      (physicalConcentrator S A) W.oneReflectionRegime W.illuminatedMeasurable
      W.referenceMeasurable S.irradiance hI S.axialExtent S.axialExtent_pos).1 with
      ⟨P, hP, _⟩
    rcases (existsUnique_uniformPowers SIUnitChoices.SI
      (physicalConcentrator S A) W.oneReflectionRegime W.illuminatedMeasurable
      W.referenceMeasurable S.irradiance hI S.axialExtent S.axialExtent_pos).2 with
      ⟨P₀, hP₀, _⟩
    have hPcoord :
        ISQDimensions.coordinateInSI SIUnitChoices.SI P =
          ISQDimensions.coordinateInSI SIUnitChoices.SI S.irradiance *
            (ISQDimensions.coordinateInSI SIUnitChoices.SI μ *
              ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent) := by
      change ISQDimensions.coordinateInSI SIUnitChoices.SI P =
        ISQDimensions.coordinateInSI SIUnitChoices.SI S.irradiance *
          ISQDimensions.coordinateInSI SIUnitChoices.SI
            (collectingArea SIUnitChoices.SI μ S.axialExtent) at hP
      rw [harea.1] at hP
      exact hP
    have hP₀coord :
        ISQDimensions.coordinateInSI SIUnitChoices.SI P₀ =
          ISQDimensions.coordinateInSI SIUnitChoices.SI S.irradiance *
            (ISQDimensions.coordinateInSI SIUnitChoices.SI μ₀ *
              ISQDimensions.coordinateInSI SIUnitChoices.SI S.axialExtent) := by
      change ISQDimensions.coordinateInSI SIUnitChoices.SI P₀ =
        ISQDimensions.coordinateInSI SIUnitChoices.SI S.irradiance *
          ISQDimensions.coordinateInSI SIUnitChoices.SI
            (collectingArea SIUnitChoices.SI μ₀ S.axialExtent) at hP₀
      rw [harea₀.1] at hP₀
      exact hP₀
    have hP₀pos : 0 < ISQDimensions.coordinateInSI SIUnitChoices.SI P₀ := by
      rw [hP₀coord]
      exact mul_pos S.irradiance_pos (mul_pos hμ₀pos S.axialExtent_pos)
    have hratio :
        ISQDimensions.coordinateInSI SIUnitChoices.SI P =
          5 * ISQDimensions.coordinateInSI SIUnitChoices.SI P₀ := by
      rw [hPcoord, hP₀coord, hμ]
      ring
    refine ⟨hI, W, P, P₀, ⟨hP, hP₀⟩, hP₀pos, ?_⟩
    exact ⟨⟨hP, hP₀⟩, hP₀pos, hratio⟩

/-- A real number is the centimetre reading of a typed physical length exactly
when division by one hundred gives its coherent-SI metre coordinate. -/
def IsCentimetreValue (a : ISQDimensions.Length) (x : ℝ) : Prop :=
  ISQDimensions.coordinateInSI SIUnitChoices.SI a = x / 100

/-- A reported value comes from a physical fivefold candidate radius through
the explicit centimetre conversion relation. -/
def IsSolutionCentimetres (S : SourceData) (x : ℝ) : Prop :=
  ∃ A : CandidateRadius S,
    IsRadiusSolution S A ∧ IsCentimetreValue A.absorberRadius x

/-- Sequential continuity of the unique optical state, direct/reflected
aperture boundaries, finite aperture measures, and fivefold residual with
respect to the coherent-SI candidate radius. -/
theorem fivefoldResidual_radius_continuous (S : SourceData)
    (Aseq : ℕ → CandidateRadius S) (A : CandidateRadius S)
    (Wseq : ∀ n : ℕ, OpticalState S (Aseq n)) (W : OpticalState S A)
    (hA : Tendsto
      (fun n : ℕ =>
        ISQDimensions.coordinateInSI SIUnitChoices.SI (Aseq n).absorberRadius)
      atTop
      (𝓝 (ISQDimensions.coordinateInSI SIUnitChoices.SI A.absorberRadius))) :
    Tendsto (fun n : ℕ => (Wseq n).limitingAngle) atTop (𝓝 W.limitingAngle) ∧
      (∀ σ : ℝ, σ = -1 ∨ σ = 1 →
        Tendsto
          (fun n : ℕ =>
            (physicalPointCoordinateInSI SIUnitChoices.SI S.mirrorCenter).x +
              σ * ISQDimensions.coordinateInSI SIUnitChoices.SI
                (Aseq n).absorberRadius)
          atTop
          (𝓝 ((physicalPointCoordinateInSI SIUnitChoices.SI S.mirrorCenter).x +
            σ * ISQDimensions.coordinateInSI SIUnitChoices.SI A.absorberRadius))) ∧
      (∀ σ : ℝ, σ = -1 ∨ σ = 1 →
        Tendsto
          (fun n : ℕ =>
            (physicalPointCoordinateInSI SIUnitChoices.SI S.mirrorCenter).x +
              σ * ISQDimensions.coordinateInSI SIUnitChoices.SI S.mirrorRadius *
                Real.sin (Wseq n).limitingAngle)
          atTop
          (𝓝 ((physicalPointCoordinateInSI SIUnitChoices.SI S.mirrorCenter).x +
            σ * ISQDimensions.coordinateInSI SIUnitChoices.SI S.mirrorRadius *
              Real.sin W.limitingAngle))) ∧
      Tendsto
        (fun n : ℕ =>
          (volume (illuminatedAperture (kernelGeometry S (Aseq n)))).toReal)
        atTop (𝓝 ((volume (illuminatedAperture (kernelGeometry S A))).toReal)) ∧
      Tendsto
        (fun n : ℕ =>
          (volume (unmirroredReferenceAperture
            (kernelGeometry S (Aseq n)))).toReal)
        atTop
        (𝓝 ((volume (unmirroredReferenceAperture (kernelGeometry S A))).toReal)) ∧
      Tendsto (fun n : ℕ => fivefoldResidual S (Aseq n) (Wseq n))
        atTop (𝓝 (fivefoldResidual S A W)) := by
  let R : ℝ :=
    ISQDimensions.coordinateInSI SIUnitChoices.SI S.mirrorRadius
  have hR : 0 < R := by
    dsimp [R]
    rw [S.mirrorRadius_si]
    norm_num
  have tangent_formula (B : CandidateRadius S) (V : OpticalState S B) :
      ISQDimensions.coordinateInSI SIUnitChoices.SI B.absorberRadius =
        R * Real.sin V.limitingAngle * (1 - Real.cos V.limitingAngle) := by
    let G := kernelGeometry S B
    let θ := V.limitingAngle
    rcases V.limitingAngle_spec.2.2.2.1 with ⟨s, Q, htangent⟩
    have hsq :=
      (tangentContact_distanceSq G
        (axialReflectedRay G.mirror .lower θ) htangent).2
    have hdet :
        displacementDirectionDet
            (displacement G.absorber.center
              (axialReflectedRay G.mirror .lower θ).origin)
            (axialReflectedRay G.mirror .lower θ).direction.1 =
          -(G.mirror.radius * Real.sin θ * (1 - Real.cos θ)) := by
      change
        ((axialReflectedRay G.mirror .lower θ).origin.x -
              G.mirror.center.x) *
            (axialReflectedRay G.mirror .lower θ).direction.1.y -
          ((axialReflectedRay G.mirror .lower θ).origin.y -
              (G.mirror.center.y - G.mirror.radius / 2)) *
            (axialReflectedRay G.mirror .lower θ).direction.1.x =
          -(G.mirror.radius * Real.sin θ * (1 - Real.cos θ))
      rw [axialReflectedRay_origin_x, axialReflectedRay_origin_y,
        axialReflectedRay_direction_x, axialReflectedRay_direction_y]
      ring
    rw [hdet] at hsq
    have hθpos : 0 < θ := V.limitingAngle_spec.1
    have hθtop : θ < Real.pi / 2 := V.limitingAngle_spec.2.1
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [hθtop, Real.pi_pos])
    have hcos : Real.cos θ < 1 := by
      simpa using
        (Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
          (show 0 ≤ (0 : ℝ) by norm_num) hθtop.le hθpos)
    have hGRadius : G.mirror.radius = R := by
      rfl
    have hGAbsorber : G.absorber.radius =
        ISQDimensions.coordinateInSI SIUnitChoices.SI B.absorberRadius := by
      rfl
    rw [hGRadius, hGAbsorber] at hsq
    have hfpos :
        0 < R * Real.sin θ * (1 - Real.cos θ) :=
      mul_pos (mul_pos hR hsin) (sub_pos.mpr hcos)
    nlinarith [B.absorberRadius_pos]
  let f : ℝ → ℝ := fun t => R * Real.sin t * (1 - Real.cos t)
  have hf_strict : StrictMonoOn f (Set.Icc 0 (Real.pi / 2)) := by
    intro x hx y hy hxy
    have hsin_lt : Real.sin x < Real.sin y :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        ((neg_nonpos.mpr (show (0 : ℝ) ≤ Real.pi / 2 by positivity)).trans hx.1)
        hy.2 hxy
    have hcos_lt : Real.cos y < Real.cos x :=
      Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hx.1 hy.2 hxy
    have hsin_x : 0 ≤ Real.sin x :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx.1
        (by linarith [hy.2, Real.pi_pos])
    have hy_pos : 0 < y := lt_of_le_of_lt hx.1 hxy
    have hcos_y_lt_one : Real.cos y < 1 := by
      simpa using
        (Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
          (show 0 ≤ (0 : ℝ) by norm_num) hy.2 hy_pos)
    have hleft :
        Real.sin x * (1 - Real.cos x) ≤
          Real.sin x * (1 - Real.cos y) :=
      mul_le_mul_of_nonneg_left (by linarith) hsin_x
    have hright :
        Real.sin x * (1 - Real.cos y) <
          Real.sin y * (1 - Real.cos y) :=
      mul_lt_mul_of_pos_right hsin_lt (by linarith)
    dsimp [f]
    simpa only [mul_assoc] using
      (mul_lt_mul_of_pos_left (hleft.trans_lt hright) hR)
  let K := Set.Icc (0 : ℝ) (Real.pi / 2)
  let θseq : ℕ → K := fun n =>
    ⟨(Wseq n).limitingAngle,
      (Wseq n).limitingAngle_spec.1.le,
      (Wseq n).limitingAngle_spec.2.1.le⟩
  let θlim : K :=
    ⟨W.limitingAngle, W.limitingAngle_spec.1.le,
      W.limitingAngle_spec.2.1.le⟩
  let fs : K → ℝ := fun t => f (t : ℝ)
  have hfscont : Continuous fs := by
    fun_prop
  have hfsinj : Function.Injective fs := by
    intro x y hxy
    apply Subtype.ext
    exact hf_strict.injOn x.property y.property hxy
  letI : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_Icc
  have hfsEmbedding : Topology.IsEmbedding fs :=
    (hfscont.isClosedEmbedding hfsinj).isEmbedding
  have hθsub : Tendsto θseq atTop (𝓝 θlim) := by
    apply (hfsEmbedding.tendsto_nhds_iff).2
    have hfun : fs ∘ θseq =
        (fun n : ℕ => ISQDimensions.coordinateInSI SIUnitChoices.SI
          (Aseq n).absorberRadius) := by
      funext n
      dsimp [fs, θseq, f]
      exact (tangent_formula (Aseq n) (Wseq n)).symm
    have hlim : fs θlim =
        ISQDimensions.coordinateInSI SIUnitChoices.SI A.absorberRadius := by
      dsimp [fs, θlim, f]
      exact (tangent_formula A W).symm
    rw [hfun, hlim]
    exact hA
  have hθ : Tendsto (fun n : ℕ => (Wseq n).limitingAngle) atTop
      (𝓝 W.limitingAngle) := by
    simpa [θseq, θlim] using (tendsto_subtype_rng.mp hθsub)
  have habsorberBoundary : ∀ σ : ℝ, σ = -1 ∨ σ = 1 →
      Tendsto
        (fun n : ℕ =>
          (physicalPointCoordinateInSI SIUnitChoices.SI S.mirrorCenter).x +
            σ * ISQDimensions.coordinateInSI SIUnitChoices.SI
              (Aseq n).absorberRadius)
        atTop
        (𝓝 ((physicalPointCoordinateInSI SIUnitChoices.SI S.mirrorCenter).x +
          σ * ISQDimensions.coordinateInSI SIUnitChoices.SI A.absorberRadius)) := by
    intro σ _hσ
    exact tendsto_const_nhds.add (tendsto_const_nhds.mul hA)
  have hreflectedBoundary : ∀ σ : ℝ, σ = -1 ∨ σ = 1 →
      Tendsto
        (fun n : ℕ =>
          (physicalPointCoordinateInSI SIUnitChoices.SI S.mirrorCenter).x +
            σ * ISQDimensions.coordinateInSI SIUnitChoices.SI S.mirrorRadius *
              Real.sin (Wseq n).limitingAngle)
        atTop
        (𝓝 ((physicalPointCoordinateInSI SIUnitChoices.SI S.mirrorCenter).x +
          σ * ISQDimensions.coordinateInSI SIUnitChoices.SI S.mirrorRadius *
            Real.sin W.limitingAngle)) := by
    intro σ _hσ
    have hsin := (Real.continuous_sin.tendsto W.limitingAngle).comp hθ
    exact tendsto_const_nhds.add
      (tendsto_const_nhds.mul hsin)
  have reference_interval (B : CandidateRadius S) :
      unmirroredReferenceAperture (kernelGeometry S B) =
        Set.Icc
          ((kernelGeometry S B).mirror.center.x -
            (kernelGeometry S B).absorber.radius)
          ((kernelGeometry S B).mirror.center.x +
            (kernelGeometry S B).absorber.radius) := by
    let G := kernelGeometry S B
    let RB : ℝ := G.mirror.radius
    let aB : ℝ := G.absorber.radius
    have hRB : 0 < RB := G.mirror.radius_pos
    have haB : 0 < aB := G.absorber.radius_pos
    have haBhalf : aB < RB / 2 := G.absorberRadius_lt_half
    have container_first_of_abs_le (x : ℝ)
        (hx : |x - G.mirror.center.x| ≤ aB) :
        ∃ s : ℝ, ∃ Q : Point2,
          IsFirstContainerContact G (incomingSunlightRay G x) s Q := by
      have hdx_sq : (x - G.mirror.center.x) ^ 2 ≤ aB ^ 2 := by
        have hsquare :=
          (sq_le_sq₀ (abs_nonneg (x - G.mirror.center.x)) haB.le).2 hx
        simpa only [sq_abs] using hsquare
      have hrad : 0 ≤ aB ^ 2 - (x - G.mirror.center.x) ^ 2 := by
        linarith
      let t : ℝ := Real.sqrt (aB ^ 2 - (x - G.mirror.center.x) ^ 2)
      have ht : 0 ≤ t := Real.sqrt_nonneg _
      have ht_sq : t ^ 2 = aB ^ 2 - (x - G.mirror.center.x) ^ 2 :=
        Real.sq_sqrt hrad
      have ht_le_a : t ≤ aB := by
        nlinarith [sq_nonneg (x - G.mirror.center.x)]
      let s : ℝ := RB / 2 - t
      have hs : 0 < s := by
        dsimp [s]
        linarith
      let Q : Point2 := (incomingSunlightRay G x).pointAt s
      refine ⟨s, Q, hs, rfl, ?_, ?_⟩
      · change displacementNormSq (displacement G.absorber.center Q) =
          G.absorber.radius ^ 2
        dsimp [Q, ForwardRay.pointAt, incomingSunlightRay, translate,
          directionDisplacement, axisDirection, orientationSign,
          ConcentratorGeometry.absorber, s]
        dsimp [displacementNormSq, displacement]
        norm_num
        dsimp [RB, aB, ConcentratorGeometry.absorber] at ht_sq ⊢
        ring_nf at ⊢
        linarith
      · intro u hu hus
        have hvertical : t < RB / 2 - u := by
          dsimp [s] at hus
          linarith
        have hvertical_sq : t ^ 2 < (RB / 2 - u) ^ 2 :=
          (sq_lt_sq₀ ht (by linarith)).2 hvertical
        dsimp [ForwardRay.pointAt, incomingSunlightRay, translate,
          directionDisplacement, axisDirection, orientationSign,
          ConcentratorGeometry.absorber]
        dsimp [displacementNormSq, displacement]
        norm_num
        dsimp [RB, aB, ConcentratorGeometry.absorber] at ht_sq hvertical_sq ⊢
        ring_nf at ⊢
        linarith
    change unmirroredReferenceAperture G =
      Set.Icc (G.mirror.center.x - G.absorber.radius)
        (G.mirror.center.x + G.absorber.radius)
    ext x
    constructor
    · intro hx
      have hbound := (transverseApertures_bounded G).2.1 x hx
      have hbound' : |x - G.mirror.center.x| ≤ aB := by
        simpa [aB, ConcentratorGeometry.absorber] using hbound
      rw [Set.mem_Icc]
      rw [abs_le] at hbound'
      constructor <;> linarith [hbound'.1, hbound'.2]
    · intro hx
      rw [Set.mem_Icc] at hx
      have habs : |x - G.mirror.center.x| ≤ aB := by
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2]
      exact container_first_of_abs_le x habs
  have reference_measure_formula (B : CandidateRadius S) :
      (volume (unmirroredReferenceAperture (kernelGeometry S B))).toReal =
        2 * ISQDimensions.coordinateInSI SIUnitChoices.SI B.absorberRadius := by
    rw [reference_interval B, Real.volume_Icc]
    have hnonneg :
        0 ≤ (kernelGeometry S B).mirror.center.x +
            (kernelGeometry S B).absorber.radius -
          ((kernelGeometry S B).mirror.center.x -
            (kernelGeometry S B).absorber.radius) := by
      have haKernel : 0 < (kernelGeometry S B).absorber.radius :=
        (kernelGeometry S B).absorber.radius_pos
      nlinarith
    rw [ENNReal.toReal_ofReal hnonneg]
    change
      (kernelGeometry S B).mirror.center.x +
            (kernelGeometry S B).absorber.radius -
          ((kernelGeometry S B).mirror.center.x -
            (kernelGeometry S B).absorber.radius) =
        2 * ISQDimensions.coordinateInSI SIUnitChoices.SI B.absorberRadius
    have hrad : (kernelGeometry S B).absorber.radius =
        ISQDimensions.coordinateInSI SIUnitChoices.SI B.absorberRadius := by
      rfl
    rw [hrad]
    ring
  have hrefLimit : Tendsto
      (fun n : ℕ =>
        (volume (unmirroredReferenceAperture
          (kernelGeometry S (Aseq n)))).toReal)
      atTop
      (𝓝 ((volume (unmirroredReferenceAperture (kernelGeometry S A))).toReal)) := by
    simpa only [reference_measure_formula] using
      (tendsto_const_nhds.mul hA)
  have hillLimit : Tendsto
      (fun n : ℕ =>
        (volume (illuminatedAperture (kernelGeometry S (Aseq n)))).toReal)
      atTop (𝓝 ((volume (illuminatedAperture (kernelGeometry S A))).toReal)) := by
    have hmeasure (B : CandidateRadius S) (V : OpticalState S B) :
        (volume (illuminatedAperture (kernelGeometry S B))).toReal =
          2 * R * Real.sin V.limitingAngle := by
      have htangent := opticalState_tangent_formula V
      have hformula :
          (kernelGeometry S B).mirror.radius * Real.sin V.limitingAngle *
              (1 - Real.cos V.limitingAngle) =
            (kernelGeometry S B).absorber.radius := htangent.symm
      have hm := illuminatedAperture_measure_formula (kernelGeometry S B)
          V.limitingAngle V.limitingAngle_spec.1
          V.limitingAngle_spec.2.1 V.limitingAngle_spec.2.2.2.2 hformula
      have hRkernel : (kernelGeometry S B).mirror.radius = R := by rfl
      rw [hRkernel] at hm
      exact hm
    have hsin := (Real.continuous_sin.tendsto W.limitingAngle).comp hθ
    have hlimit : Tendsto
        (fun n : ℕ => (2 * R) * Real.sin (Wseq n).limitingAngle) atTop
        (nhds ((2 * R) * Real.sin W.limitingAngle)) :=
      tendsto_const_nhds.mul hsin
    have hfun :
        (fun n : ℕ =>
          (volume (illuminatedAperture (kernelGeometry S (Aseq n)))).toReal) =
        (fun n : ℕ => 2 * R * Real.sin (Wseq n).limitingAngle) := by
      funext n
      exact hmeasure (Aseq n) (Wseq n)
    rw [hfun, hmeasure A W]
    exact hlimit
  have hIllCoord (B : CandidateRadius S) (V : OpticalState S B) :
      ISQDimensions.coordinateInSI SIUnitChoices.SI
          (transverseFluxMeasure SIUnitChoices.SI (kernelGeometry S B)
            V.illuminatedMeasurable) =
        (volume (illuminatedAperture (kernelGeometry S B))).toReal :=
    (transverseMeasures_coordinate SIUnitChoices.SI (kernelGeometry S B)
      V.illuminatedMeasurable V.referenceMeasurable).1
  have hRefCoord (B : CandidateRadius S) (V : OpticalState S B) :
      ISQDimensions.coordinateInSI SIUnitChoices.SI
          (referenceTransverseMeasure SIUnitChoices.SI (kernelGeometry S B)
            V.referenceMeasurable) =
        (volume (unmirroredReferenceAperture (kernelGeometry S B))).toReal :=
    (transverseMeasures_coordinate SIUnitChoices.SI (kernelGeometry S B)
      V.illuminatedMeasurable V.referenceMeasurable).2.1
  have hNumerator : Tendsto
      (fun n : ℕ => ISQDimensions.coordinateInSI SIUnitChoices.SI
        (transverseFluxMeasure SIUnitChoices.SI (kernelGeometry S (Aseq n))
          (Wseq n).illuminatedMeasurable)) atTop
      (𝓝 (ISQDimensions.coordinateInSI SIUnitChoices.SI
        (transverseFluxMeasure SIUnitChoices.SI (kernelGeometry S A)
          W.illuminatedMeasurable))) := by
    have hfun :
        (fun n : ℕ => ISQDimensions.coordinateInSI SIUnitChoices.SI
          (transverseFluxMeasure SIUnitChoices.SI (kernelGeometry S (Aseq n))
            (Wseq n).illuminatedMeasurable)) =
          (fun n : ℕ =>
            (volume (illuminatedAperture (kernelGeometry S (Aseq n)))).toReal) := by
      funext n
      exact hIllCoord (Aseq n) (Wseq n)
    rw [hfun, hIllCoord A W]
    exact hillLimit
  have hDenominator : Tendsto
      (fun n : ℕ => ISQDimensions.coordinateInSI SIUnitChoices.SI
        (referenceTransverseMeasure SIUnitChoices.SI (kernelGeometry S (Aseq n))
          (Wseq n).referenceMeasurable)) atTop
      (𝓝 (ISQDimensions.coordinateInSI SIUnitChoices.SI
        (referenceTransverseMeasure SIUnitChoices.SI (kernelGeometry S A)
          W.referenceMeasurable))) := by
    have hfun :
        (fun n : ℕ => ISQDimensions.coordinateInSI SIUnitChoices.SI
          (referenceTransverseMeasure SIUnitChoices.SI (kernelGeometry S (Aseq n))
            (Wseq n).referenceMeasurable)) =
          (fun n : ℕ =>
            (volume (unmirroredReferenceAperture
              (kernelGeometry S (Aseq n)))).toReal) := by
      funext n
      exact hRefCoord (Aseq n) (Wseq n)
    rw [hfun, hRefCoord A W]
    exact hrefLimit
  have hrefPos := referenceTransverseMeasure_pos S A W
  have hResidual :=
    (hNumerator.div hDenominator (ne_of_gt hrefPos)).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (5 : ℝ)) atTop (nhds 5))
  refine ⟨hθ, habsorberBoundary, hreflectedBoundary, hillLimit, hrefLimit, ?_⟩
  exact hResidual

/-- Two admissible radii bracket a residual zero, with the optical state at
each endpoint explicitly identified as unique. -/
theorem exists_fivefoldResidual_bracket (S : SourceData) :
    ∃ Aminus Aplus : CandidateRadius S,
      ∃ Wminus : OpticalState S Aminus,
        ∃ Wplus : OpticalState S Aplus,
          ISQDimensions.coordinateInSI SIUnitChoices.SI Aminus.absorberRadius <
              ISQDimensions.coordinateInSI SIUnitChoices.SI Aplus.absorberRadius ∧
            (∀ V : OpticalState S Aminus, V = Wminus) ∧
            (∀ V : OpticalState S Aplus, V = Wplus) ∧
            0 < fivefoldResidual S Aminus Wminus ∧
            fivefoldResidual S Aplus Wplus < 0 := by
  let q : ℝ := Real.sqrt 3
  have hq0 : 0 ≤ q := Real.sqrt_nonneg 3
  have hq2 : q ^ 2 = 3 := by
    dsimp [q]
    norm_num
  have hqpos : 0 < q := by nlinarith
  have hqone : 1 < q := by nlinarith
  have hqtwo : q < 2 := by nlinarith
  let aminus : ℝ := (1 / 2 : ℝ) * (1 - q / 2)
  let aplus : ℝ := q / 4
  have haminus_pos : 0 < aminus := by
    dsimp [aminus]
    nlinarith
  have haminus_half : aminus < (1 : ℝ) / 2 := by
    dsimp [aminus]
    nlinarith
  have haplus_pos : 0 < aplus := by
    dsimp [aplus]
    nlinarith
  have haplus_half : aplus < (1 : ℝ) / 2 := by
    dsimp [aplus]
    nlinarith
  have haminus_aplus : aminus < aplus := by
    dsimp [aminus, aplus]
    nlinarith
  have hcoord (x : ℝ) :
      ISQDimensions.coordinateInSI SIUnitChoices.SI
          (lengthFromSICoordinate SIUnitChoices.SI x) = x := by
    change
      ISQDimensions.coordinateInSI SIUnitChoices.SI
          (quantityFromSICoordinate SIUnitChoices.SI
            ISQDimensions.lengthDimension x) = x
    exact
      (quantityFromSICoordinate_roundtrip SIUnitChoices.SI
        ISQDimensions.lengthDimension x
        (⟨0⟩ : ISQDimensions.Length)).1
  let Aminus : CandidateRadius S :=
    { absorberRadius := lengthFromSICoordinate SIUnitChoices.SI aminus
      absorberRadius_pos := by simpa [hcoord] using haminus_pos
      absorberRadius_lt_half := by
        rw [hcoord, S.mirrorRadius_si]
        exact haminus_half }
  let Aplus : CandidateRadius S :=
    { absorberRadius := lengthFromSICoordinate SIUnitChoices.SI aplus
      absorberRadius_pos := by simpa [hcoord] using haplus_pos
      absorberRadius_lt_half := by
        rw [hcoord, S.mirrorRadius_si]
        exact haplus_half }
  rcases OpticalState.existsUnique S Aminus with ⟨Wminus, hWminus⟩
  rcases OpticalState.existsUnique S Aplus with ⟨Wplus, hWplus⟩
  refine ⟨Aminus, Aplus, Wminus, Wplus, ?_, hWminus, hWplus, ?_, ?_⟩
  · simpa [Aminus, Aplus, hcoord] using haminus_aplus
  · have hRkernel : (kernelGeometry S Aminus).mirror.radius = 1 := by
      change ISQDimensions.coordinateInSI SIUnitChoices.SI S.mirrorRadius = 1
      exact S.mirrorRadius_si
    have htprofile :
        (1 : ℝ) * Real.sin Wminus.limitingAngle *
            (1 - Real.cos Wminus.limitingAngle) = aminus := by
      calc
        (1 : ℝ) * Real.sin Wminus.limitingAngle *
              (1 - Real.cos Wminus.limitingAngle) =
            (kernelGeometry S Aminus).mirror.radius *
              Real.sin Wminus.limitingAngle *
                (1 - Real.cos Wminus.limitingAngle) := by rw [hRkernel]
        _ = (kernelGeometry S Aminus).absorber.radius :=
          (opticalState_tangent_formula Wminus).symm
        _ = ISQDimensions.coordinateInSI SIUnitChoices.SI
              Aminus.absorberRadius := rfl
        _ = aminus := by simpa [Aminus] using hcoord aminus
    have hwitprofile :
        (1 : ℝ) * Real.sin (Real.pi / 6) *
            (1 - Real.cos (Real.pi / 6)) = aminus := by
      rw [Real.sin_pi_div_six, Real.cos_pi_div_six]
      dsimp [aminus, q]
      ring
    have hθmem : Wminus.limitingAngle ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨Wminus.limitingAngle_spec.1.le, Wminus.limitingAngle_spec.2.1.le⟩
    have hwitmem : Real.pi / 6 ∈ Set.Icc 0 (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    have hθeq : Wminus.limitingAngle = Real.pi / 6 :=
      (tangentProfile_strictMonoOn 1 (by norm_num)).injOn hθmem hwitmem
        (htprofile.trans hwitprofile.symm)
    have hqbound : (8 / 5 : ℝ) < q := by nlinarith
    have hd : 0 < 1 - q / 2 := by linarith
    have hratio : 5 < 1 / (1 - q / 2) := by
      apply (lt_div_iff₀ hd).2
      nlinarith
    rw [fivefoldResidual_formula, hθeq, Real.cos_pi_div_six]
    simpa [q] using (sub_pos.mpr hratio)
  · have hRkernel : (kernelGeometry S Aplus).mirror.radius = 1 := by
      change ISQDimensions.coordinateInSI SIUnitChoices.SI S.mirrorRadius = 1
      exact S.mirrorRadius_si
    have htprofile :
        (1 : ℝ) * Real.sin Wplus.limitingAngle *
            (1 - Real.cos Wplus.limitingAngle) = aplus := by
      calc
        (1 : ℝ) * Real.sin Wplus.limitingAngle *
              (1 - Real.cos Wplus.limitingAngle) =
            (kernelGeometry S Aplus).mirror.radius *
              Real.sin Wplus.limitingAngle *
                (1 - Real.cos Wplus.limitingAngle) := by rw [hRkernel]
        _ = (kernelGeometry S Aplus).absorber.radius :=
          (opticalState_tangent_formula Wplus).symm
        _ = ISQDimensions.coordinateInSI SIUnitChoices.SI
              Aplus.absorberRadius := rfl
        _ = aplus := by simpa [Aplus] using hcoord aplus
    have hwitprofile :
        (1 : ℝ) * Real.sin (Real.pi / 3) *
            (1 - Real.cos (Real.pi / 3)) = aplus := by
      rw [Real.sin_pi_div_three, Real.cos_pi_div_three]
      dsimp [aplus, q]
      ring
    have hθmem : Wplus.limitingAngle ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨Wplus.limitingAngle_spec.1.le, Wplus.limitingAngle_spec.2.1.le⟩
    have hwitmem : Real.pi / 3 ∈ Set.Icc 0 (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    have hθeq : Wplus.limitingAngle = Real.pi / 3 :=
      (tangentProfile_strictMonoOn 1 (by norm_num)).injOn hθmem hwitmem
        (htprofile.trans hwitprofile.symm)
    rw [fivefoldResidual_formula, hθeq, Real.cos_pi_div_three]
    norm_num

/-- The normalized aperture residual strictly decreases as the physical
absorber radius increases. -/
theorem fivefoldResidual_strictAnti (S : SourceData)
    (A₁ A₂ : CandidateRadius S) (W₁ : OpticalState S A₁)
    (W₂ : OpticalState S A₂)
    (hRadius :
      ISQDimensions.coordinateInSI SIUnitChoices.SI A₁.absorberRadius <
        ISQDimensions.coordinateInSI SIUnitChoices.SI A₂.absorberRadius) :
    fivefoldResidual S A₂ W₂ < fivefoldResidual S A₁ W₁ := by
  let R : ℝ :=
    ISQDimensions.coordinateInSI SIUnitChoices.SI S.mirrorRadius
  have hR : 0 < R := by
    dsimp [R]
    rw [S.mirrorRadius_si]
    norm_num
  have tangent_formula (B : CandidateRadius S) (V : OpticalState S B) :
      ISQDimensions.coordinateInSI SIUnitChoices.SI B.absorberRadius =
        R * Real.sin V.limitingAngle * (1 - Real.cos V.limitingAngle) := by
    let G := kernelGeometry S B
    let θ := V.limitingAngle
    rcases V.limitingAngle_spec.2.2.2.1 with ⟨s, Q, htangent⟩
    have hsq :=
      (tangentContact_distanceSq G
        (axialReflectedRay G.mirror .lower θ) htangent).2
    have hdet :
        displacementDirectionDet
            (displacement G.absorber.center
              (axialReflectedRay G.mirror .lower θ).origin)
            (axialReflectedRay G.mirror .lower θ).direction.1 =
          -(G.mirror.radius * Real.sin θ * (1 - Real.cos θ)) := by
      change
        ((axialReflectedRay G.mirror .lower θ).origin.x -
              G.mirror.center.x) *
            (axialReflectedRay G.mirror .lower θ).direction.1.y -
          ((axialReflectedRay G.mirror .lower θ).origin.y -
              (G.mirror.center.y - G.mirror.radius / 2)) *
            (axialReflectedRay G.mirror .lower θ).direction.1.x =
          -(G.mirror.radius * Real.sin θ * (1 - Real.cos θ))
      rw [axialReflectedRay_origin_x, axialReflectedRay_origin_y,
        axialReflectedRay_direction_x, axialReflectedRay_direction_y]
      ring
    rw [hdet] at hsq
    have hθpos : 0 < θ := V.limitingAngle_spec.1
    have hθtop : θ < Real.pi / 2 := V.limitingAngle_spec.2.1
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [hθtop, Real.pi_pos])
    have hcos : Real.cos θ < 1 := by
      simpa using
        (Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
          (show 0 ≤ (0 : ℝ) by norm_num) hθtop.le hθpos)
    have hGRadius : G.mirror.radius = R := by rfl
    have hGAbsorber : G.absorber.radius =
        ISQDimensions.coordinateInSI SIUnitChoices.SI B.absorberRadius := by rfl
    rw [hGRadius, hGAbsorber] at hsq
    have hfpos : 0 < R * Real.sin θ * (1 - Real.cos θ) :=
      mul_pos (mul_pos hR hsin) (sub_pos.mpr hcos)
    nlinarith [B.absorberRadius_pos]
  let f : ℝ → ℝ := fun t => R * Real.sin t * (1 - Real.cos t)
  have hf_strict : StrictMonoOn f (Set.Icc 0 (Real.pi / 2)) := by
    intro x hx y hy hxy
    have hsin_lt : Real.sin x < Real.sin y :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        ((neg_nonpos.mpr (show (0 : ℝ) ≤ Real.pi / 2 by positivity)).trans hx.1)
        hy.2 hxy
    have hcos_lt : Real.cos y < Real.cos x :=
      Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hx.1 hy.2 hxy
    have hsin_x : 0 ≤ Real.sin x :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx.1
        (by linarith [hy.2, Real.pi_pos])
    have hy_pos : 0 < y := lt_of_le_of_lt hx.1 hxy
    have hcos_y_lt_one : Real.cos y < 1 := by
      simpa using
        (Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
          (show 0 ≤ (0 : ℝ) by norm_num) hy.2 hy_pos)
    have hleft :
        Real.sin x * (1 - Real.cos x) ≤
          Real.sin x * (1 - Real.cos y) :=
      mul_le_mul_of_nonneg_left (by linarith) hsin_x
    have hright :
        Real.sin x * (1 - Real.cos y) <
          Real.sin y * (1 - Real.cos y) :=
      mul_lt_mul_of_pos_right hsin_lt (by linarith)
    dsimp [f]
    simpa only [mul_assoc] using
      (mul_lt_mul_of_pos_left (hleft.trans_lt hright) hR)
  have hθ₁mem : W₁.limitingAngle ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨W₁.limitingAngle_spec.1.le, W₁.limitingAngle_spec.2.1.le⟩
  have hθ₂mem : W₂.limitingAngle ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨W₂.limitingAngle_spec.1.le, W₂.limitingAngle_spec.2.1.le⟩
  have hformula₁ := tangent_formula A₁ W₁
  have hformula₂ := tangent_formula A₂ W₂
  have hθ : W₁.limitingAngle < W₂.limitingAngle := by
    by_contra hnot
    have hle : W₂.limitingAngle ≤ W₁.limitingAngle := le_of_not_gt hnot
    have hf_le := hf_strict.monotoneOn hθ₂mem hθ₁mem hle
    dsimp [f] at hf_le
    linarith
  have hcos : Real.cos W₂.limitingAngle < Real.cos W₁.limitingAngle :=
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
      W₁.limitingAngle_spec.1.le W₂.limitingAngle_spec.2.1.le hθ
  have residual_formula (B : CandidateRadius S) (V : OpticalState S B) :
      fivefoldResidual S B V =
        1 / (1 - Real.cos V.limitingAngle) - 5 := by
    exact fivefoldResidual_formula S B V
  rw [residual_formula A₂ W₂, residual_formula A₁ W₁]
  have hd₁ : 0 < 1 - Real.cos W₁.limitingAngle := by
    have hc : Real.cos W₁.limitingAngle < 1 := by
      simpa using
        (Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
          (show 0 ≤ (0 : ℝ) by norm_num)
          W₁.limitingAngle_spec.2.1.le W₁.limitingAngle_spec.1)
    linarith
  have hdlt : 1 - Real.cos W₁.limitingAngle <
      1 - Real.cos W₂.limitingAngle := by linarith
  exact sub_lt_sub_right (one_div_lt_one_div_of_lt hd₁ hdlt) 5

/-- Continuity and the opposite-sign bracket produce an admissible zero of the
fivefold residual, together with its unique optical state. -/
theorem exists_fivefoldResidual_zero (S : SourceData) :
    ∃ A : CandidateRadius S,
      ∃ W : OpticalState S A,
        fivefoldResidual S A W = 0 ∧
          ∀ V : OpticalState S A, V = W := by
  rcases exists_fivefoldResidual_bracket S with
    ⟨Aminus, Aplus, Wminus, Wplus, hlt, huniqminus, huniqplus,
      hminus, hplus⟩
  let aminus : ℝ :=
    ISQDimensions.coordinateInSI SIUnitChoices.SI Aminus.absorberRadius
  let aplus : ℝ :=
    ISQDimensions.coordinateInSI SIUnitChoices.SI Aplus.absorberRadius
  let T := Set.Icc aminus aplus
  have hcoord (x : ℝ) :
      ISQDimensions.coordinateInSI SIUnitChoices.SI
          (lengthFromSICoordinate SIUnitChoices.SI x) = x := by
    change
      ISQDimensions.coordinateInSI SIUnitChoices.SI
          (quantityFromSICoordinate SIUnitChoices.SI
            ISQDimensions.lengthDimension x) = x
    exact
      (quantityFromSICoordinate_roundtrip SIUnitChoices.SI
        ISQDimensions.lengthDimension x
        (⟨0⟩ : ISQDimensions.Length)).1
  let Aof : T → CandidateRadius S := fun t =>
    { absorberRadius := lengthFromSICoordinate SIUnitChoices.SI (t : ℝ)
      absorberRadius_pos := by
        rw [hcoord]
        exact lt_of_lt_of_le Aminus.absorberRadius_pos t.property.1
      absorberRadius_lt_half := by
        rw [hcoord]
        exact lt_of_le_of_lt t.property.2 Aplus.absorberRadius_lt_half }
  have candidate_eq_of_radius {A B : CandidateRadius S}
      (h : A.absorberRadius = B.absorberRadius) : A = B := by
    cases A with
    | mk ar hapos halt =>
      cases B with
      | mk br hbpos hblt =>
        dsimp at h
        subst br
        rfl
  let tminus : T := ⟨aminus, le_rfl, hlt.le⟩
  let tplus : T := ⟨aplus, hlt.le, le_rfl⟩
  have hAminus : Aof tminus = Aminus := by
    apply candidate_eq_of_radius
    apply (ISQDimensions.coordinateInSI_eq_iff SIUnitChoices.SI _ _).mp
    simpa [Aof, tminus, aminus] using hcoord aminus
  have hAplus : Aof tplus = Aplus := by
    apply candidate_eq_of_radius
    apply (ISQDimensions.coordinateInSI_eq_iff SIUnitChoices.SI _ _).mp
    simpa [Aof, tplus, aplus] using hcoord aplus
  let Wof : ∀ t : T, OpticalState S (Aof t) := fun t =>
    Classical.choose (OpticalState.existsUnique S (Aof t))
  have hWof_unique (t : T) :
      ∀ V : OpticalState S (Aof t), V = Wof t :=
    Classical.choose_spec (OpticalState.existsUnique S (Aof t))
  let F : T → ℝ := fun t => fivefoldResidual S (Aof t) (Wof t)
  have hFseq : SeqContinuous F := by
    intro p x hp
    change Tendsto (fun n : ℕ => F (p n)) atTop (𝓝 (F x))
    have hpval : Tendsto (fun n : ℕ => ((p n : T) : ℝ)) atTop
        (𝓝 ((x : T) : ℝ)) :=
      (continuous_subtype_val.tendsto x).comp hp
    have hAseq : Tendsto
        (fun n : ℕ => ISQDimensions.coordinateInSI SIUnitChoices.SI
          (Aof (p n)).absorberRadius)
        atTop
        (𝓝 (ISQDimensions.coordinateInSI SIUnitChoices.SI
          (Aof x).absorberRadius)) := by
      simpa [Aof, hcoord] using hpval
    have hall := fivefoldResidual_radius_continuous S
      (fun n : ℕ => Aof (p n)) (Aof x)
      (fun n : ℕ => Wof (p n)) (Wof x) hAseq
    simpa [F] using hall.2.2.2.2.2
  have hFcont : Continuous F := hFseq.continuous
  have residual_transport {A B : CandidateRadius S} (h : A = B)
      (W : OpticalState S A) :
      fivefoldResidual S A W = fivefoldResidual S B (h ▸ W) := by
    subst B
    rfl
  let Wminus' : OpticalState S (Aof tminus) := hAminus.symm ▸ Wminus
  let Wplus' : OpticalState S (Aof tplus) := hAplus.symm ▸ Wplus
  have hminus' : 0 < fivefoldResidual S (Aof tminus) Wminus' := by
    dsimp [Wminus']
    rw [← residual_transport hAminus.symm Wminus]
    exact hminus
  have hplus' : fivefoldResidual S (Aof tplus) Wplus' < 0 := by
    dsimp [Wplus']
    rw [← residual_transport hAplus.symm Wplus]
    exact hplus
  have hFminus : 0 < F tminus := by
    have hW := hWof_unique tminus Wminus'
    simpa [F, hW] using hminus'
  have hFplus : F tplus < 0 := by
    have hW := hWof_unique tplus Wplus'
    simpa [F, hW] using hplus'
  letI : PreconnectedSpace T := Subtype.preconnectedSpace isPreconnected_Icc
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (F tplus) (F tminus) :=
    ⟨hFplus.le, hFminus.le⟩
  rcases intermediate_value_univ tplus tminus hFcont hzero_mem with ⟨t, ht⟩
  exact ⟨Aof t, Wof t, ht, hWof_unique t⟩

/-- At least one admissible physical absorber radius satisfies the complete
fivefold uniform-power condition. -/
theorem exists_isRadiusSolution (S : SourceData) :
    ∃ A : CandidateRadius S, IsRadiusSolution S A := by
  rcases exists_fivefoldResidual_zero S with ⟨A, W, hzero, _hunique⟩
  exact ⟨A, (isRadiusSolution_iff_fivefoldResidual_eq_zero S A W).2 hzero⟩

/-- Any two physical solutions have the same typed absorber radius. -/
theorem isRadiusSolution_radius_unique (S : SourceData)
    (A₁ A₂ : CandidateRadius S) (hA₁ : IsRadiusSolution S A₁)
    (hA₂ : IsRadiusSolution S A₂) :
    A₁.absorberRadius = A₂.absorberRadius := by
  rcases OpticalState.existsUnique S A₁ with ⟨W₁, _hW₁⟩
  rcases OpticalState.existsUnique S A₂ with ⟨W₂, _hW₂⟩
  have hz₁ := (isRadiusSolution_iff_fivefoldResidual_eq_zero S A₁ W₁).1 hA₁
  have hz₂ := (isRadiusSolution_iff_fivefoldResidual_eq_zero S A₂ W₂).1 hA₂
  have hcoord :
      ISQDimensions.coordinateInSI SIUnitChoices.SI A₁.absorberRadius =
        ISQDimensions.coordinateInSI SIUnitChoices.SI A₂.absorberRadius := by
    rcases lt_trichotomy
      (ISQDimensions.coordinateInSI SIUnitChoices.SI A₁.absorberRadius)
      (ISQDimensions.coordinateInSI SIUnitChoices.SI A₂.absorberRadius) with
      hlt | heq | hgt
    · have hanti := fivefoldResidual_strictAnti S A₁ A₂ W₁ W₂ hlt
      rw [hz₁, hz₂] at hanti
      linarith
    · exact heq
    · have hanti := fivefoldResidual_strictAnti S A₂ A₁ W₂ W₁ hgt
      rw [hz₁, hz₂] at hanti
      linarith
  exact (ISQDimensions.coordinateInSI_eq_iff SIUnitChoices.SI
    A₁.absorberRadius A₂.absorberRadius).mp hcoord

/-- Answer-free target theorem: the governing model determines exactly one
real centimetre report, without placing its evaluated value in the signature. -/
theorem existsUnique_solutionCentimetres (S : SourceData) :
    ∃! x : ℝ, IsSolutionCentimetres S x := by
  rcases exists_isRadiusSolution S with ⟨A, hA⟩
  let x := 100 * ISQDimensions.coordinateInSI SIUnitChoices.SI A.absorberRadius
  have hx : IsCentimetreValue A.absorberRadius x := by
    dsimp [IsCentimetreValue, x]
    ring
  refine ⟨x, ⟨A, hA, hx⟩, ?_⟩
  intro y hy
  rcases hy with ⟨B, hB, hy⟩
  have hradius := isRadiusSolution_radius_unique S B A hB hA
  dsimp [IsCentimetreValue] at hy hx
  rw [hradius] at hy
  dsimp [x] at hy ⊢
  linarith

end Ipho2026Gpt56solBlind.ProblemIPhO2026_2_B_3
