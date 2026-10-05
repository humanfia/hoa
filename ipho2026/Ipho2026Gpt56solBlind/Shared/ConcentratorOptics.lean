import Ipho2026Gpt56solBlind.Shared.GeometricOptics
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic

/-!
# Displaced-cylinder concentrator optics and typed radiometry

This module specializes the common geometric-optics kernel to a lower
semicircular mirror with a displaced absorbing cylinder, then reconstructs
typed aperture lengths, collecting areas, and absorbed powers.
-/

noncomputable section

open MeasureTheory

namespace Ipho2026Gpt56solBlind.Shared.GeometricOptics

/-! ## Displaced absorbing-cylinder and concentrator geometry -/

/-- A circular cross-section whose closed disk absorbs incident rays. -/
abbrev AbsorbingCircle := Circle

/-- Scalar geometry of a lower semicircular mirror and displaced absorber. -/
structure ConcentratorGeometry where
  mirror : Circle
  absorberRadius : Length
  absorberRadius_pos : 0 < absorberRadius
  absorberRadius_lt_half : absorberRadius < mirror.radius / 2

/-- The absorbing circle derived from concentrator data. -/
def ConcentratorGeometry.absorber (G : ConcentratorGeometry) : AbsorbingCircle :=
  { center := { x := G.mirror.center.x, y := G.mirror.center.y - G.mirror.radius / 2 }
    radius := G.absorberRadius
    radius_pos := G.absorberRadius_pos }

/-- The lower, mirror-rim-owned semicircle of a concentrator. -/
def ConcentratorGeometry.lowerMirror (G : ConcentratorGeometry) : Semicircle :=
  { circle := G.mirror, orientation := .lower, rims := .mirror }

/-- Typed concentrator geometry relative to one common source unit choice. -/
structure PhysicalConcentratorGeometry (u : SIUnitChoices) where
  mirrorCenter : PhysicalPoint2
  mirrorRadius : ISQDimensions.Length
  absorberRadius : ISQDimensions.Length
  absorberRadius_pos : 0 < ISQDimensions.coordinateInSI u absorberRadius
  absorberRadius_lt_half :
    ISQDimensions.coordinateInSI u absorberRadius <
      ISQDimensions.coordinateInSI u mirrorRadius / 2

/-- Scalar coherent-SI representation of typed concentrator geometry. -/
def physicalConcentratorGeometryCoordinateInSI (u : SIUnitChoices)
    (G : PhysicalConcentratorGeometry u) : ConcentratorGeometry :=
  { mirror :=
      { center := physicalPointCoordinateInSI u G.mirrorCenter
        radius := lengthCoordinateInSI u G.mirrorRadius
        radius_pos := by
          change 0 < ISQDimensions.coordinateInSI u G.mirrorRadius
          linarith [G.absorberRadius_pos, G.absorberRadius_lt_half] }
    absorberRadius := lengthCoordinateInSI u G.absorberRadius
    absorberRadius_pos := G.absorberRadius_pos
    absorberRadius_lt_half := G.absorberRadius_lt_half }

/-- Typed concentrator scalarization is injective and has a unique lift. -/
theorem physicalConcentratorGeometryCoordinateInSI_injective (u : SIUnitChoices) :
    Function.Injective (physicalConcentratorGeometryCoordinateInSI u) ∧
      ∀ G : ConcentratorGeometry, ∃! PG : PhysicalConcentratorGeometry u,
        physicalConcentratorGeometryCoordinateInSI u PG = G := by
  have physical_ext (G₁ G₂ : PhysicalConcentratorGeometry u)
      (hcenter : G₁.mirrorCenter = G₂.mirrorCenter)
      (hmirror : G₁.mirrorRadius = G₂.mirrorRadius)
      (habsorber : G₁.absorberRadius = G₂.absorberRadius) : G₁ = G₂ := by
    cases G₁
    cases G₂
    cases hcenter
    cases hmirror
    cases habsorber
    rfl
  have circle_ext (c₁ c₂ : Circle) (hcenter : c₁.center = c₂.center)
      (hradius : c₁.radius = c₂.radius) : c₁ = c₂ := by
    cases c₁
    cases c₂
    cases hcenter
    cases hradius
    rfl
  have geometry_ext (G₁ G₂ : ConcentratorGeometry) (hmirror : G₁.mirror = G₂.mirror)
      (habsorber : G₁.absorberRadius = G₂.absorberRadius) : G₁ = G₂ := by
    cases G₁
    cases G₂
    cases hmirror
    cases habsorber
    rfl
  have hinjective : Function.Injective (physicalConcentratorGeometryCoordinateInSI u) := by
    intro G₁ G₂ hG
    apply physical_ext
    · apply (physicalPointCoordinateInSI_faithful u).1
      simpa [physicalConcentratorGeometryCoordinateInSI] using
        congrArg (fun G : ConcentratorGeometry => G.mirror.center) hG
    · apply (ISQDimensions.coordinateInSI_eq_iff u _ _).mp
      simpa [physicalConcentratorGeometryCoordinateInSI, lengthCoordinateInSI] using
        congrArg (fun G : ConcentratorGeometry => G.mirror.radius) hG
    · apply (ISQDimensions.coordinateInSI_eq_iff u _ _).mp
      simpa [physicalConcentratorGeometryCoordinateInSI, lengthCoordinateInSI] using
        congrArg ConcentratorGeometry.absorberRadius hG
  refine ⟨hinjective, fun G => ?_⟩
  have hlength (x : Length) :
      lengthCoordinateInSI u (lengthFromSICoordinate u x) = x :=
    (lengthCoordinateInSI_faithful u
      (lengthFromSICoordinate u x) (lengthFromSICoordinate u x)
      (lengthFromSICoordinate u x) x).2.2
  have hpoint (P : Point2) :
      physicalPointCoordinateInSI u (physicalPointFromKernel u P) = P :=
    (physicalPointCoordinateInSI_faithful u).2.2 P
  let PG : PhysicalConcentratorGeometry u :=
    { mirrorCenter := physicalPointFromKernel u G.mirror.center
      mirrorRadius := lengthFromSICoordinate u G.mirror.radius
      absorberRadius := lengthFromSICoordinate u G.absorberRadius
      absorberRadius_pos := by
        change 0 < lengthCoordinateInSI u (lengthFromSICoordinate u G.absorberRadius)
        rw [hlength]
        exact G.absorberRadius_pos
      absorberRadius_lt_half := by
        change lengthCoordinateInSI u (lengthFromSICoordinate u G.absorberRadius) <
          lengthCoordinateInSI u (lengthFromSICoordinate u G.mirror.radius) / 2
        rw [hlength, hlength]
        exact G.absorberRadius_lt_half }
  have hPG : physicalConcentratorGeometryCoordinateInSI u PG = G := by
    apply geometry_ext
    · apply circle_ext
      · change physicalPointCoordinateInSI u (physicalPointFromKernel u G.mirror.center) =
          G.mirror.center
        exact hpoint G.mirror.center
      · change lengthCoordinateInSI u (lengthFromSICoordinate u G.mirror.radius) =
          G.mirror.radius
        exact hlength G.mirror.radius
    · change lengthCoordinateInSI u (lengthFromSICoordinate u G.absorberRadius) =
        G.absorberRadius
      exact hlength G.absorberRadius
  refine ⟨PG, hPG, ?_⟩
  intro PG' hPG'
  exact hinjective (hPG'.trans hPG.symm)

/-- Open lower half-disk with the closed absorber removed. -/
def InConcentratorFreeRegion (G : ConcentratorGeometry) (P : Point2) : Prop :=
  InSemicircleInterior G.lowerMirror P ∧ ¬ InClosedDisk G.absorber P

/-- Union of lower mirror arc and absorber boundary. -/
def OnConcentratorBoundary (G : ConcentratorGeometry) (P : Point2) : Prop :=
  OnReflectingArc G.lowerMirror P ∨ OnCircle G.absorber P

/-- The free propagation region is disjoint from both optical boundary pieces. -/
theorem concentratorRegion_disjoint_boundary (G : ConcentratorGeometry) (P : Point2) :
    ¬(InConcentratorFreeRegion G P ∧ OnConcentratorBoundary G P) := by
  rintro ⟨hfree, hboundary⟩
  rcases hboundary with hmirror | habsorber
  · exact (ne_of_lt hfree.1.2) hmirror.1
  · apply hfree.2
    exact le_of_eq habsorber

/-- Ordered first contact with either concentrator boundary component. -/
def IsFirstConcentratorContact (G : ConcentratorGeometry) (r : ForwardRay)
    (s : Length) (Q : Point2) : Prop :=
  IsFirstForwardBoundaryContact (InConcentratorFreeRegion G)
    (OnConcentratorBoundary G) r s Q

/-- First positive contact with the absorber, starting outside its closed disk. -/
def IsFirstContainerContact (G : ConcentratorGeometry) (r : ForwardRay)
    (s : Length) (Q : Point2) : Prop :=
  0 < s ∧ Q = r.pointAt s ∧ OnCircle G.absorber Q ∧
    ∀ u : Length, 0 ≤ u → u < s →
      displacementNormSq (displacement G.absorber.center (r.pointAt u)) >
        G.absorber.radius ^ 2

/-- A fixed ray has at most one ordered first absorber contact. -/
theorem firstContainerContact_unique (G : ConcentratorGeometry) (r : ForwardRay)
    {s₁ s₂ : Length} {Q₁ Q₂ : Point2}
    (h₁ : IsFirstContainerContact G r s₁ Q₁)
    (h₂ : IsFirstContainerContact G r s₂ Q₂) :
    s₁ = s₂ ∧ Q₁ = Q₂ := by
  rcases h₁ with ⟨hs₁, hQ₁, hcircle₁, hbefore₁⟩
  rcases h₂ with ⟨hs₂, hQ₂, hcircle₂, hbefore₂⟩
  have hs : s₁ = s₂ := by
    rcases lt_trichotomy s₁ s₂ with hslt | hseq | hsgt
    · have hout := hbefore₂ s₁ hs₁.le hslt
      have hon :
          displacementNormSq
              (displacement G.absorber.center (r.pointAt s₁)) =
            G.absorber.radius ^ 2 := by
        simpa [OnCircle, hQ₁] using hcircle₁
      linarith
    · exact hseq
    · have hout := hbefore₁ s₂ hs₂.le hsgt
      have hon :
          displacementNormSq
              (displacement G.absorber.center (r.pointAt s₂)) =
            G.absorber.radius ^ 2 := by
        simpa [OnCircle, hQ₂] using hcircle₂
      linarith
  refine ⟨hs, ?_⟩
  calc
    Q₁ = r.pointAt s₁ := hQ₁
    _ = r.pointAt s₂ := congrArg r.pointAt hs
    _ = Q₂ := hQ₂.symm

/-- A first absorber contact tangent to the ray direction. -/
def IsTangentContainerContact (G : ConcentratorGeometry) (r : ForwardRay)
    (s : Length) (Q : Point2) : Prop :=
  IsFirstContainerContact G r s Q ∧
    displacementDirectionDot (displacement G.absorber.center Q) r.direction.1 = 0

/-- Pythagorean and determinant identities at a tangent absorber contact. -/
theorem tangentContact_distanceSq (G : ConcentratorGeometry) (r : ForwardRay)
    {s : Length} {Q : Point2} (h : IsTangentContainerContact G r s Q) :
    let w := displacement G.absorber.center r.origin
    G.absorber.radius ^ 2 =
        displacementNormSq w - (displacementDirectionDot w r.direction.1) ^ 2 ∧
      G.absorber.radius ^ 2 =
        (displacementDirectionDet w r.direction.1) ^ 2 := by
  rcases h with ⟨hcontact, htangent⟩
  rcases hcontact with ⟨_hs, hQ, hcircle, _hbefore⟩
  let w := displacement G.absorber.center r.origin
  let d := r.direction.1
  change G.absorber.radius ^ 2 =
      displacementNormSq w - (displacementDirectionDot w d) ^ 2 ∧
    G.absorber.radius ^ 2 = (displacementDirectionDet w d) ^ 2
  have hunit : directionNormSq d = 1 := r.direction.2
  have hcircleRay :
      displacementNormSq (displacement G.absorber.center (r.pointAt s)) =
        G.absorber.radius ^ 2 := by
    simpa [OnCircle, hQ] using hcircle
  have htangentRay :
      displacementDirectionDot
          (displacement G.absorber.center (r.pointAt s)) d = 0 := by
    simpa [hQ, d] using htangent
  have hdotShift :
      displacementDirectionDot
          (displacement G.absorber.center (r.pointAt s)) d =
        displacementDirectionDot w d + s * directionNormSq d := by
    simp [ForwardRay.pointAt, translate, directionDisplacement, displacement,
      displacementDirectionDot, directionNormSq, directionDot, w, d]
    ring
  have hnormShift :
      displacementNormSq (displacement G.absorber.center (r.pointAt s)) =
        displacementNormSq w + 2 * s * displacementDirectionDot w d +
          s ^ 2 * directionNormSq d := by
    simp [ForwardRay.pointAt, translate, directionDisplacement, displacement,
      displacementNormSq, displacementDirectionDot, directionNormSq, directionDot,
      w, d]
    ring
  have hdotzero : displacementDirectionDot w d + s = 0 := by
    rw [hdotShift, hunit, mul_one] at htangentRay
    exact htangentRay
  have hs : s = -displacementDirectionDot w d := by
    linarith
  have hcontactNorm :
      displacementNormSq w + 2 * s * displacementDirectionDot w d + s ^ 2 =
        G.absorber.radius ^ 2 := by
    rw [hnormShift, hunit, mul_one] at hcircleRay
    exact hcircleRay
  have hfirst :
      G.absorber.radius ^ 2 =
        displacementNormSq w - (displacementDirectionDot w d) ^ 2 := by
    rw [hs] at hcontactNorm
    nlinarith
  have hlagrange :
      displacementNormSq w * directionNormSq d =
        (displacementDirectionDot w d) ^ 2 +
          (displacementDirectionDet w d) ^ 2 := by
    simp [displacementNormSq, displacementDirectionDot, displacementDirectionDet,
      directionNormSq, directionDot]
    ring
  have hpythagoras :
      displacementNormSq w =
        (displacementDirectionDot w d) ^ 2 +
          (displacementDirectionDet w d) ^ 2 := by
    simpa [hunit] using hlagrange
  refine ⟨hfirst, ?_⟩
  linarith

/-- No return to the mirror after launch and before the stated absorption time. -/
def HasNoSecondMirrorContact (G : ConcentratorGeometry) (r : ForwardRay)
    (sHit : Length) : Prop :=
  ∀ u : Length, 0 < u → u ≤ sHit → ¬ OnReflectingArc G.lowerMirror (r.pointAt u)

/-- Global regime in which accepted reflected branches reach the absorber
before a second reflection. -/
def InOneReflectionRegime (G : ConcentratorGeometry) : Prop :=
  ∀ θ : ℝ, InAxialIncidenceDomain θ →
    ∀ s : Length, ∀ Q : Point2,
      IsFirstContainerContact G (axialReflectedRay G.mirror .lower θ) s Q →
        HasNoSecondMirrorContact G (axialReflectedRay G.mirror .lower θ) s

/-- Downward sunlight ray launched from the mirror-diameter line. -/
def incomingSunlightRay (G : ConcentratorGeometry) (x : Length) : ForwardRay :=
  { origin := { x := x, y := G.mirror.center.y }
    direction := axisDirection .lower }

/-- A signed mirror parameter accepted by the one-reflection branch. -/
def AcceptedReflectedRay (G : ConcentratorGeometry) (θ : ℝ) : Prop :=
  InOneReflectionRegime G ∧ InAxialIncidenceDomain θ ∧
    let P := (semicirclePoint G.mirror .lower θ).1
    ∃ sMirror : Length,
      IsFirstConcentratorContact G (incomingSunlightRay G P.x) sMirror P ∧
        OnReflectingArc G.lowerMirror P ∧
        ∃ sHit : Length, ∃ QHit : Point2,
          IsFirstContainerContact G (axialReflectedRay G.mirror .lower θ) sHit QHit ∧
            HasNoSecondMirrorContact G (axialReflectedRay G.mirror .lower θ) sHit

/-- Positive attained tangent angle maximal among all accepted signed parameters. -/
def IsLimitingTangentAngle (G : ConcentratorGeometry) (θmax : ℝ) : Prop :=
  0 < θmax ∧ θmax < Real.pi / 2 ∧ AcceptedReflectedRay G θmax ∧
    (∃ s : Length, ∃ Q : Point2,
      IsTangentContainerContact G (axialReflectedRay G.mirror .lower θmax) s Q) ∧
    ∀ θ : ℝ, AcceptedReflectedRay G θ → |θ| ≤ θmax

/-- Incoming coordinate whose first system contact is the absorber. -/
def IsDirectlyAbsorbed (G : ConcentratorGeometry) (x : Length) : Prop :=
  ∃ s : Length, ∃ Q : Point2,
    IsFirstConcentratorContact G (incomingSunlightRay G x) s Q ∧ OnCircle G.absorber Q

/-- Incoming coordinate absorbed after one first mirror contact and before a second. -/
def IsAbsorbedAfterOneReflection (G : ConcentratorGeometry) (x : Length) : Prop :=
  ∃ sMirror : Length, ∃ QMirror : Point2,
    IsFirstConcentratorContact G (incomingSunlightRay G x) sMirror QMirror ∧
      ∃ hMirror : OnReflectingArc G.lowerMirror QMirror,
      ∃ sHit : Length, ∃ QHit : Point2,
        IsFirstContainerContact G
            (rayAfterReflection G.mirror (incomingSunlightRay G x) QMirror
              hMirror.1)
            sHit QHit ∧
          HasNoSecondMirrorContact G
            (rayAfterReflection G.mirror (incomingSunlightRay G x) QMirror
              hMirror.1)
            sHit

/-- Strict-rim transverse coordinate accepted directly or after one reflection. -/
def AcceptedIncomingCoordinate (G : ConcentratorGeometry) (x : Length) : Prop :=
  |x - G.mirror.center.x| < G.mirror.radius ∧
    (IsDirectlyAbsorbed G x ∨ IsAbsorbedAfterOneReflection G x)

/-- Set of all accepted incoming forward rays. -/
def acceptedRayFamily (G : ConcentratorGeometry) : Set ForwardRay :=
  {r | ∃ x : Length, AcceptedIncomingCoordinate G x ∧ r = incomingSunlightRay G x}

/-- Accepted rays obey exactly the direct-or-one-reflection ordering, and the
branches are disjoint. -/
theorem acceptedIncomingCoordinate_ordering (G : ConcentratorGeometry) (x : Length)
    (h : AcceptedIncomingCoordinate G x) :
    (IsDirectlyAbsorbed G x ∨ IsAbsorbedAfterOneReflection G x) ∧
      ¬(IsDirectlyAbsorbed G x ∧ IsAbsorbedAfterOneReflection G x) := by
  refine ⟨h.2, ?_⟩
  rintro ⟨hdirect, hreflected⟩
  rcases hdirect with ⟨sDirect, QDirect, hfirstDirect, habsorberDirect⟩
  rcases hreflected with ⟨sMirror, QMirror, hfirstMirror, hmirrorData⟩
  rcases hmirrorData with ⟨hmirror, _sHit, _QHit, _hHit, _hNoSecond⟩
  have hsystemDisjoint :
      ∀ P, InConcentratorFreeRegion G P → ¬ OnConcentratorBoundary G P := by
    intro P hfree hboundary
    exact concentratorRegion_disjoint_boundary G P ⟨hfree, hboundary⟩
  have hcontactUnique :=
    firstForwardBoundaryContact_unique
      (InConcentratorFreeRegion G) (OnConcentratorBoundary G)
      hsystemDisjoint (incomingSunlightRay G x) hfirstDirect hfirstMirror
  have hQ : QDirect = QMirror := hcontactUnique.2
  have habsorber : OnCircle G.absorber QMirror := hQ ▸ habsorberDirect
  have habsorberEq :
      (QMirror.x - G.mirror.center.x) ^ 2 +
          (QMirror.y - (G.mirror.center.y - G.mirror.radius / 2)) ^ 2 =
        G.absorberRadius ^ 2 := by
    simpa [OnCircle, ConcentratorGeometry.absorber, displacementNormSq, displacement]
      using habsorber
  have hmirrorEq :
      (QMirror.x - G.mirror.center.x) ^ 2 +
          (QMirror.y - G.mirror.center.y) ^ 2 = G.mirror.radius ^ 2 := by
    simpa [OnCircle, ConcentratorGeometry.lowerMirror, displacementNormSq, displacement]
      using hmirror.1
  have hySq :
      (QMirror.y - (G.mirror.center.y - G.mirror.radius / 2)) ^ 2 ≤
        G.absorberRadius ^ 2 := by
    nlinarith [sq_nonneg (QMirror.x - G.mirror.center.x)]
  have hyAbs :
      |QMirror.y - (G.mirror.center.y - G.mirror.radius / 2)| ≤
        G.absorberRadius :=
    abs_le_of_sq_le_sq hySq G.absorberRadius_pos.le
  have hyLower :
      -G.absorberRadius ≤
        QMirror.y - (G.mirror.center.y - G.mirror.radius / 2) :=
    (abs_le.mp hyAbs).1
  have hR : 0 < G.mirror.radius := by
    linarith [G.absorberRadius_pos, G.absorberRadius_lt_half]
  have hsumNonneg : 0 ≤ G.absorberRadius + G.mirror.radius / 2 := by
    linarith [G.absorberRadius_pos, hR]
  have hsumLt :
      G.absorberRadius + G.mirror.radius / 2 < G.mirror.radius := by
    linarith [G.absorberRadius_lt_half]
  have hsumSq :
      (G.absorberRadius + G.mirror.radius / 2) ^ 2 < G.mirror.radius ^ 2 :=
    (sq_lt_sq₀ hsumNonneg hR.le).2 hsumLt
  have hproduct := mul_le_mul_of_nonpos_left hyLower (neg_nonpos.mpr hR.le)
  nlinarith

/-! ## Typed aperture lengths, collecting areas, and powers -/

/-- Irradiance is heat-rate dimension divided by area dimension. -/
def irradianceDimension : Dimension ISQDimensionBase :=
  ISQDimensions.heatRateDimension * ISQDimensions.areaDimension⁻¹

/-- ISQ-typed irradiance quantities. -/
abbrev Irradiance := ISQDimensions.Quantity irradianceDimension

/-- Two length factors have the Shared area dimension. -/
theorem length_mul_length_dimension :
    ISQDimensions.lengthDimension * ISQDimensions.lengthDimension =
      ISQDimensions.areaDimension := by
  simp [ISQDimensions.areaDimension, pow_two]

/-- Irradiance times area has the Shared heat-rate dimension. -/
theorem irradiance_mul_area_dimension :
    irradianceDimension * ISQDimensions.areaDimension =
      ISQDimensions.heatRateDimension := by
  simp [irradianceDimension]

/-- Scalar transverse aperture accepted by the complete optical model. -/
def illuminatedAperture (G : ConcentratorGeometry) : Set ℝ :=
  {x | AcceptedIncomingCoordinate G x}

/-- Scalar transverse aperture of the same absorber with the mirror omitted. -/
def unmirroredReferenceAperture (G : ConcentratorGeometry) : Set ℝ :=
  {x | ∃ s : Length, ∃ Q : Point2,
    IsFirstContainerContact G (incomingSunlightRay G x) s Q}

/-- Measurability of the illuminated scalar aperture. -/
def HasMeasurableIlluminatedAperture (G : ConcentratorGeometry) : Prop :=
  MeasurableSet (illuminatedAperture G)

/-- Measurability of the unmirrored reference scalar aperture. -/
def HasMeasurableReferenceAperture (G : ConcentratorGeometry) : Prop :=
  MeasurableSet (unmirroredReferenceAperture G)

/-- Both transverse apertures have explicit finite interval bounds and finite measure. -/
theorem transverseApertures_bounded (G : ConcentratorGeometry) :
    (∀ x ∈ illuminatedAperture G,
      |x - G.mirror.center.x| < G.mirror.radius) ∧
    (∀ x ∈ unmirroredReferenceAperture G,
      |x - G.absorber.center.x| ≤ G.absorber.radius) ∧
    volume (illuminatedAperture G) ≠ ⊤ ∧
    volume (unmirroredReferenceAperture G) ≠ ⊤ := by
  have hIlluminated :
      ∀ x ∈ illuminatedAperture G,
        |x - G.mirror.center.x| < G.mirror.radius := by
    intro x hx
    change AcceptedIncomingCoordinate G x at hx
    exact hx.1
  have hReference :
      ∀ x ∈ unmirroredReferenceAperture G,
        |x - G.absorber.center.x| ≤ G.absorber.radius := by
    intro x hx
    change ∃ s : Length, ∃ Q : Point2,
      IsFirstContainerContact G (incomingSunlightRay G x) s Q at hx
    rcases hx with ⟨s, Q, _hs, hQ, hcircle, _hbefore⟩
    have hQx : Q.x = x := by
      rw [hQ]
      simp [ForwardRay.pointAt, incomingSunlightRay, translate, directionDisplacement,
        axisDirection, orientationSign]
    have hcircleEq :
        (Q.x - G.absorber.center.x) ^ 2 +
            (Q.y - G.absorber.center.y) ^ 2 = G.absorber.radius ^ 2 := by
      simpa [OnCircle, displacementNormSq, displacement] using hcircle
    rw [hQx] at hcircleEq
    have hxSq :
        (x - G.absorber.center.x) ^ 2 ≤ G.absorber.radius ^ 2 := by
      nlinarith [sq_nonneg (Q.y - G.absorber.center.y)]
    exact abs_le_of_sq_le_sq hxSq G.absorber.radius_pos.le
  have hIlluminatedSubset :
      illuminatedAperture G ⊆
        Set.Icc (G.mirror.center.x - G.mirror.radius)
          (G.mirror.center.x + G.mirror.radius) := by
    intro x hx
    have hbound := hIlluminated x hx
    rw [abs_lt] at hbound
    constructor <;> linarith
  have hReferenceSubset :
      unmirroredReferenceAperture G ⊆
        Set.Icc (G.absorber.center.x - G.absorber.radius)
          (G.absorber.center.x + G.absorber.radius) := by
    intro x hx
    have hbound := hReference x hx
    rw [abs_le] at hbound
    constructor <;> linarith
  have hIlluminatedFinite : volume (illuminatedAperture G) ≠ ⊤ :=
    measure_ne_top_of_subset hIlluminatedSubset (by simp [Real.volume_Icc])
  have hReferenceFinite : volume (unmirroredReferenceAperture G) ≠ ⊤ :=
    measure_ne_top_of_subset hReferenceSubset (by simp [Real.volume_Icc])
  exact ⟨hIlluminated, hReference, hIlluminatedFinite, hReferenceFinite⟩

/-- Typed captured transverse aperture length reconstructed from Lebesgue measure. -/
def transverseFluxMeasure (u : SIUnitChoices) (G : ConcentratorGeometry)
    (_hMeas : HasMeasurableIlluminatedAperture G) : ISQDimensions.Length :=
  quantityFromSICoordinate u ISQDimensions.lengthDimension
    (volume (illuminatedAperture G)).toReal

/-- Typed unmirrored transverse aperture length. -/
def referenceTransverseMeasure (u : SIUnitChoices) (G : ConcentratorGeometry)
    (_hMeas : HasMeasurableReferenceAperture G) : ISQDimensions.Length :=
  quantityFromSICoordinate u ISQDimensions.lengthDimension
    (volume (unmirroredReferenceAperture G)).toReal

/-- Coordinates, nonnegativity, and equality of the two typed transverse measures. -/
theorem transverseMeasures_coordinate (u : SIUnitChoices) (G : ConcentratorGeometry)
    (hIll : HasMeasurableIlluminatedAperture G)
    (hRef : HasMeasurableReferenceAperture G) :
    ISQDimensions.coordinateInSI u (transverseFluxMeasure u G hIll) =
        (volume (illuminatedAperture G)).toReal ∧
      ISQDimensions.coordinateInSI u (referenceTransverseMeasure u G hRef) =
        (volume (unmirroredReferenceAperture G)).toReal ∧
      0 ≤ ISQDimensions.coordinateInSI u (transverseFluxMeasure u G hIll) ∧
      0 ≤ ISQDimensions.coordinateInSI u (referenceTransverseMeasure u G hRef) ∧
      (transverseFluxMeasure u G hIll = referenceTransverseMeasure u G hRef ↔
        (volume (illuminatedAperture G)).toReal =
          (volume (unmirroredReferenceAperture G)).toReal) := by
  have hIllCoord :
      ISQDimensions.coordinateInSI u (transverseFluxMeasure u G hIll) =
        (volume (illuminatedAperture G)).toReal := by
    exact (quantityFromSICoordinate_roundtrip u ISQDimensions.lengthDimension
      (volume (illuminatedAperture G)).toReal
      (transverseFluxMeasure u G hIll)).1
  have hRefCoord :
      ISQDimensions.coordinateInSI u (referenceTransverseMeasure u G hRef) =
        (volume (unmirroredReferenceAperture G)).toReal := by
    exact (quantityFromSICoordinate_roundtrip u ISQDimensions.lengthDimension
      (volume (unmirroredReferenceAperture G)).toReal
      (referenceTransverseMeasure u G hRef)).1
  refine ⟨hIllCoord, hRefCoord, ?_, ?_, ?_⟩
  · rw [hIllCoord]
    exact ENNReal.toReal_nonneg
  · rw [hRefCoord]
    exact ENNReal.toReal_nonneg
  constructor
  · intro hEq
    have hCoordEq :=
      (ISQDimensions.coordinateInSI_eq_iff u
        (transverseFluxMeasure u G hIll) (referenceTransverseMeasure u G hRef)).mpr hEq
    simpa [hIllCoord, hRefCoord] using hCoordEq
  · intro hCoordEq
    apply (ISQDimensions.coordinateInSI_eq_iff u
      (transverseFluxMeasure u G hIll) (referenceTransverseMeasure u G hRef)).mp
    simpa [hIllCoord, hRefCoord] using hCoordEq

/-- A strictly positive common physical extent along the cylinder axes. -/
def IsPositiveAxialExtent (u : SIUnitChoices) (L : ISQDimensions.Length) : Prop :=
  0 < ISQDimensions.coordinateInSI u L

/-- Typed strip area formed from transverse aperture length and axial extent. -/
def collectingArea (u : SIUnitChoices) (μ L : ISQDimensions.Length) :
    ISQDimensions.Area :=
  quantityFromSICoordinate u ISQDimensions.areaDimension
    (ISQDimensions.coordinateInSI u μ * ISQDimensions.coordinateInSI u L)

/-- The collecting-area coordinate is the length product, with its expected signs. -/
theorem collectingArea_coordinate (u : SIUnitChoices) (μ L : ISQDimensions.Length)
    (hμ : 0 ≤ ISQDimensions.coordinateInSI u μ)
    (hL : IsPositiveAxialExtent u L) :
    ISQDimensions.coordinateInSI u (collectingArea u μ L) =
        ISQDimensions.coordinateInSI u μ * ISQDimensions.coordinateInSI u L ∧
      0 ≤ ISQDimensions.coordinateInSI u (collectingArea u μ L) ∧
      (0 < ISQDimensions.coordinateInSI u μ →
        0 < ISQDimensions.coordinateInSI u (collectingArea u μ L)) := by
  have hcoord :
      ISQDimensions.coordinateInSI u (collectingArea u μ L) =
        ISQDimensions.coordinateInSI u μ * ISQDimensions.coordinateInSI u L := by
    exact (quantityFromSICoordinate_roundtrip u ISQDimensions.areaDimension
      (ISQDimensions.coordinateInSI u μ * ISQDimensions.coordinateInSI u L)
      (collectingArea u μ L)).1
  change 0 < ISQDimensions.coordinateInSI u L at hL
  refine ⟨hcoord, ?_, ?_⟩
  · rw [hcoord]
    exact mul_nonneg hμ hL.le
  · intro hμpos
    rw [hcoord]
    exact mul_pos hμpos hL

/-- A single nonnegative typed irradiance used uniformly on both collectors. -/
def UniformIrradiance (u : SIUnitChoices) (I : Irradiance) : Prop :=
  0 ≤ ISQDimensions.coordinateInSI u I

/-- Typed absorbed-power law for the mirrored concentrator. -/
def uniformAbsorbedPower (u : SIUnitChoices) (PG : PhysicalConcentratorGeometry u)
    (_hRegime : InOneReflectionRegime
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (hMeas : HasMeasurableIlluminatedAperture
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (I : Irradiance) (_hI : UniformIrradiance u I)
    (L : ISQDimensions.Length) (_hL : IsPositiveAxialExtent u L)
    (P : ISQDimensions.HeatRate) : Prop :=
  let G := physicalConcentratorGeometryCoordinateInSI u PG
  ISQDimensions.coordinateInSI u P =
    ISQDimensions.coordinateInSI u I *
      ISQDimensions.coordinateInSI u
        (collectingArea u (transverseFluxMeasure u G hMeas) L)

/-- Typed reference-power law with the same irradiance and axial extent. -/
def uniformReferencePower (u : SIUnitChoices) (PG : PhysicalConcentratorGeometry u)
    (hMeas : HasMeasurableReferenceAperture
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (I : Irradiance) (_hI : UniformIrradiance u I)
    (L : ISQDimensions.Length) (_hL : IsPositiveAxialExtent u L)
    (P₀ : ISQDimensions.HeatRate) : Prop :=
  let G := physicalConcentratorGeometryCoordinateInSI u PG
  ISQDimensions.coordinateInSI u P₀ =
    ISQDimensions.coordinateInSI u I *
      ISQDimensions.coordinateInSI u
        (collectingArea u (referenceTransverseMeasure u G hMeas) L)

/-- The two common-input typed power laws each determine a unique heat rate. -/
theorem existsUnique_uniformPowers (u : SIUnitChoices)
    (PG : PhysicalConcentratorGeometry u)
    (hRegime : InOneReflectionRegime
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (hIll : HasMeasurableIlluminatedAperture
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (hRef : HasMeasurableReferenceAperture
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (I : Irradiance) (hI : UniformIrradiance u I)
    (L : ISQDimensions.Length) (hL : IsPositiveAxialExtent u L) :
    (∃! P : ISQDimensions.HeatRate,
      uniformAbsorbedPower u PG hRegime hIll I hI L hL P) ∧
    (∃! P₀ : ISQDimensions.HeatRate,
      uniformReferencePower u PG hRef I hI L hL P₀) := by
  have uniqueCoordinate (x : ℝ) :
      ∃! P : ISQDimensions.HeatRate, ISQDimensions.coordinateInSI u P = x := by
    let P := quantityFromSICoordinate u ISQDimensions.heatRateDimension x
    have hP : ISQDimensions.coordinateInSI u P = x :=
      (quantityFromSICoordinate_roundtrip u ISQDimensions.heatRateDimension x P).1
    refine ⟨P, hP, ?_⟩
    intro P' hP'
    apply (ISQDimensions.coordinateInSI_eq_iff u P' P).mp
    exact hP'.trans hP.symm
  constructor
  · simpa [uniformAbsorbedPower] using
      uniqueCoordinate
        (ISQDimensions.coordinateInSI u I *
          ISQDimensions.coordinateInSI u
            (collectingArea u
              (transverseFluxMeasure u
                (physicalConcentratorGeometryCoordinateInSI u PG) hIll) L))
  · simpa [uniformReferencePower] using
      uniqueCoordinate
        (ISQDimensions.coordinateInSI u I *
          ISQDimensions.coordinateInSI u
            (collectingArea u
              (referenceTransverseMeasure u
                (physicalConcentratorGeometryCoordinateInSI u PG) hRef) L))

/-- A mirrored/reference power pair sharing every physical input. -/
def IsUniformPowerPair (u : SIUnitChoices) (PG : PhysicalConcentratorGeometry u)
    (hRegime : InOneReflectionRegime
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (hIll : HasMeasurableIlluminatedAperture
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (hRef : HasMeasurableReferenceAperture
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (I : Irradiance) (hI : UniformIrradiance u I)
    (L : ISQDimensions.Length) (hL : IsPositiveAxialExtent u L)
    (P P₀ : ISQDimensions.HeatRate) : Prop :=
  uniformAbsorbedPower u PG hRegime hIll I hI L hL P ∧
    uniformReferencePower u PG hRef I hI L hL P₀

/-- Dimensionless ratio characterized by a positive reference power coordinate. -/
def IsPowerRatio (u : SIUnitChoices) (PG : PhysicalConcentratorGeometry u)
    (hRegime : InOneReflectionRegime
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (hIll : HasMeasurableIlluminatedAperture
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (hRef : HasMeasurableReferenceAperture
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (I : Irradiance) (hI : UniformIrradiance u I)
    (L : ISQDimensions.Length) (hL : IsPositiveAxialExtent u L)
    (P P₀ : ISQDimensions.HeatRate) (ρ : ℝ) : Prop :=
  IsUniformPowerPair u PG hRegime hIll hRef I hI L hL P P₀ ∧
    0 < ISQDimensions.coordinateInSI u P₀ ∧
    ISQDimensions.coordinateInSI u P = ρ * ISQDimensions.coordinateInSI u P₀

/-- A common-input pair with positive reference coordinate has one power ratio. -/
theorem existsUnique_powerRatio (u : SIUnitChoices)
    (PG : PhysicalConcentratorGeometry u)
    (hRegime : InOneReflectionRegime
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (hIll : HasMeasurableIlluminatedAperture
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (hRef : HasMeasurableReferenceAperture
      (physicalConcentratorGeometryCoordinateInSI u PG))
    (I : Irradiance) (hI : UniformIrradiance u I)
    (L : ISQDimensions.Length) (hL : IsPositiveAxialExtent u L)
    (P P₀ : ISQDimensions.HeatRate)
    (hPair : IsUniformPowerPair u PG hRegime hIll hRef I hI L hL P P₀)
    (hP₀ : 0 < ISQDimensions.coordinateInSI u P₀) :
    ∃! ρ : ℝ, IsPowerRatio u PG hRegime hIll hRef I hI L hL P P₀ ρ := by
  let ρ := ISQDimensions.coordinateInSI u P /
    ISQDimensions.coordinateInSI u P₀
  have hP₀ne : ISQDimensions.coordinateInSI u P₀ ≠ 0 := ne_of_gt hP₀
  have hratio :
      ISQDimensions.coordinateInSI u P =
        ρ * ISQDimensions.coordinateInSI u P₀ := by
    dsimp [ρ]
    rw [div_mul_cancel₀ _ hP₀ne]
  refine ⟨ρ, ⟨hPair, hP₀, hratio⟩, ?_⟩
  intro ρ' hρ'
  apply mul_right_cancel₀ hP₀ne
  exact hρ'.2.2.symm.trans hratio

end Ipho2026Gpt56solBlind.Shared.GeometricOptics
