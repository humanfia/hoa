import Ipho2026Gpt56solBlind.Shared.CausticOptics

/-!
# IPhO 2026 Problem 2, C.4

Answer-blind specification of the small-angle cusp law for the reflected-ray
caustic in Figure 2g.  Physical lengths retain their ISQ dimension at the
source boundary; the shared geometric-optics kernel receives their real
coordinates only through `sourceLengthCoordinate`.
-/

noncomputable section

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_2_C_4

open Ipho2026Gpt56solBlind.Shared.GeometricOptics

/-- An ISQ-typed physical length at the source boundary. -/
abbrev ISQLength :=
  WithDim (Dimension.single ISQDimensionBase.length) ℝ

/-- The typed source datum for the half-cylindrical mirror. -/
structure SourceData where
  unitChoice : SIUnitChoices
  radius : ISQLength
  radius_pos : 0 < radius

/-- The real coordinate of a typed length in the source datum's fixed length
unit.  The unit choice is retained in `SourceData`; `WithDim.val` is the
coordinate supplied in that source unit. -/
def sourceLengthCoordinate (_source : SourceData) (length : ISQLength) : Length :=
  length.val

/-- The coordinate circle underlying the upper half-cylindrical mirror in
Figure 2g. -/
def sourceMirror (source : SourceData) : Circle where
  center := { x := 0, y := 0 }
  radius := sourceLengthCoordinate source source.radius
  radius_pos := source.radius_pos

/-- The Figure 2g family of vertically incident rays reflected from the upper
semicircle. -/
def sourceRayFamily (source : SourceData) : ReflectedRayFamily :=
  axialReflectedRayFamily (sourceMirror source) .upper

/-- The positive, non-rim branch through which the small-angle limit is
taken. -/
def IsAdmissibleSmallPositiveAngle (source : SourceData) (theta : ℝ) : Prop :=
  0 < theta ∧ theta ∈ (sourceRayFamily source).domain

/-- The coordinate derivative of the incidence point with respect to the
dimensionless incidence angle. -/
def canonicalIncidenceDerivative (source : SourceData) (theta : ℝ) :
    Displacement2 :=
  { x := sourceLengthCoordinate source source.radius * Real.cos theta
    y := -(sourceLengthCoordinate source source.radius * Real.sin theta) }

/-- The derivative of the dimensionless outgoing unit direction with respect
to the incidence angle. -/
def canonicalOutgoingDerivative (_source : SourceData) (theta : ℝ) :
    Direction2 :=
  { x := -(2 * Real.cos (2 * theta))
    y := 2 * Real.sin (2 * theta) }

/-- Named point and direction derivatives for the canonical ray family. -/
def canonicalRayDerivativeData (source : SourceData) (theta : ℝ) :
    RayDerivativeData where
  pointDerivative := canonicalIncidenceDerivative source theta
  directionDerivative := canonicalOutgoingDerivative source theta

/-- The named derivative data are the four coordinate derivatives of the
Figure 2g reflected-ray family. -/
theorem canonicalRayDerivativeData_spec (source : SourceData) (theta : ℝ)
    (htheta : theta ∈ (sourceRayFamily source).domain) :
    HasRayDerivativesAt (sourceRayFamily source) theta
      (canonicalRayDerivativeData source theta) := by
  refine ⟨htheta, ?_, ?_, ?_, ?_⟩
  · dsimp only [canonicalRayDerivativeData, canonicalIncidenceDerivative,
      sourceRayFamily, axialReflectedRayFamily, sourceMirror, semicirclePoint]
    convert (Real.hasDerivAt_sin theta).const_mul
      (sourceLengthCoordinate source source.radius) using 1 <;>
        first
        | rfl
        | (funext t; ring)
        | ring
  · dsimp only [canonicalRayDerivativeData, canonicalIncidenceDerivative,
      sourceRayFamily, axialReflectedRayFamily, sourceMirror, semicirclePoint,
      orientationSign]
    convert (Real.hasDerivAt_cos theta).const_mul
      (sourceLengthCoordinate source source.radius) using 1 <;>
        first
        | rfl
        | (funext t; ring)
        | ring
  · have hprod := (Real.hasDerivAt_cos theta).mul (Real.hasDerivAt_sin theta)
    have hderiv :
        (-2 : ℝ) *
            ((-Real.sin theta) * Real.sin theta +
              Real.cos theta * Real.cos theta) =
          -(2 * Real.cos (2 * theta)) := by
      rw [Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq theta]
    have hx := (hprod.const_mul (-2)).congr_deriv hderiv
    dsimp only [canonicalRayDerivativeData, canonicalOutgoingDerivative,
      sourceRayFamily, axialReflectedRayFamily, axialReflectedRay,
      reflectedUnitDirection, reflectedDirection, subtractDirection,
      scaleDirection, directionDot, axisDirection, semicirclePoint,
      orientationSign]
    convert hx using 1 <;>
      first
      | rfl
      | (ext t
         simp only [Pi.mul_apply]
         ring)
      | ring
  · have hprod := (Real.hasDerivAt_cos theta).mul (Real.hasDerivAt_cos theta)
    have hraw := (hasDerivAt_const (x := theta) (c := (1 : ℝ))).sub
      (hprod.const_mul 2)
    have hderiv :
        0 - 2 *
            ((-Real.sin theta) * Real.cos theta +
              Real.cos theta * (-Real.sin theta)) =
          2 * Real.sin (2 * theta) := by
      rw [Real.sin_two_mul]
      ring
    have hy := hraw.congr_deriv hderiv
    dsimp only [canonicalRayDerivativeData, canonicalOutgoingDerivative,
      sourceRayFamily, axialReflectedRayFamily, axialReflectedRay,
      reflectedUnitDirection, reflectedDirection, subtractDirection,
      scaleDirection, directionDot, axisDirection, semicirclePoint,
      orientationSign]
    convert hy using 1 <;>
      first
      | rfl
      | (ext t
         simp only [Pi.mul_apply, Pi.sub_apply]
         ring)
      | ring

/-- The outgoing direction turns nontrivially at every parameter value. -/
theorem canonicalTurningDet_ne_zero (source : SourceData) (theta : ℝ) :
    directionDet ((sourceRayFamily source).outgoing theta).1
      (canonicalOutgoingDerivative source theta) ≠ 0 := by
  have houtx : ((sourceRayFamily source).outgoing theta).1.x =
      -Real.sin (2 * theta) := by
    dsimp only [sourceRayFamily, axialReflectedRayFamily, axialReflectedRay,
      reflectedUnitDirection, reflectedDirection, subtractDirection,
      scaleDirection, directionDot, axisDirection, semicirclePoint,
      orientationSign]
    rw [Real.sin_two_mul]
    ring
  have houty : ((sourceRayFamily source).outgoing theta).1.y =
      -Real.cos (2 * theta) := by
    dsimp only [sourceRayFamily, axialReflectedRayFamily, axialReflectedRay,
      reflectedUnitDirection, reflectedDirection, subtractDirection,
      scaleDirection, directionDot, axisDirection, semicirclePoint,
      orientationSign]
    rw [Real.cos_two_mul]
    ring
  have hdet : directionDet ((sourceRayFamily source).outgoing theta).1
      (canonicalOutgoingDerivative source theta) = -2 := by
    change ((sourceRayFamily source).outgoing theta).1.x *
        (2 * Real.sin (2 * theta)) -
      ((sourceRayFamily source).outgoing theta).1.y *
        (-(2 * Real.cos (2 * theta))) = -2
    rw [houtx, houty]
    nlinarith [Real.sin_sq_add_cos_sq (2 * theta)]
  rw [hdet]
  norm_num

/-- The differential envelope of the Figure 2g reflected-ray family. -/
def canonicalCaustic (source : SourceData) (theta : ℝ) : Point2 :=
  differentialCausticPoint (sourceRayFamily source) theta
    (canonicalRayDerivativeData source theta)
    (canonicalTurningDet_ne_zero source theta)

/-- Determinant quotient and source-coordinate formula for the canonical
differential caustic. -/
theorem canonicalCaustic_coordinateFormula (source : SourceData) (theta : ℝ) :
    let radius := sourceLengthCoordinate source source.radius
    displacementDirectionDet (canonicalIncidenceDerivative source theta)
          ((sourceRayFamily source).outgoing theta).1 /
        directionDet ((sourceRayFamily source).outgoing theta).1
          (canonicalOutgoingDerivative source theta) =
        radius * Real.cos theta / 2 ∧
      (canonicalCaustic source theta).x = radius * Real.sin theta ^ 3 ∧
      (canonicalCaustic source theta).y =
        radius *
          ((1 / 2 : ℝ) * Real.cos theta +
            Real.sin theta ^ 2 * Real.cos theta) := by
  dsimp only
  let radius := sourceLengthCoordinate source source.radius
  have houtx : ((sourceRayFamily source).outgoing theta).1.x =
      -Real.sin (2 * theta) := by
    dsimp only [sourceRayFamily, axialReflectedRayFamily, axialReflectedRay,
      reflectedUnitDirection, reflectedDirection, subtractDirection,
      scaleDirection, directionDot, axisDirection, semicirclePoint,
      orientationSign]
    rw [Real.sin_two_mul]
    ring
  have houty : ((sourceRayFamily source).outgoing theta).1.y =
      -Real.cos (2 * theta) := by
    dsimp only [sourceRayFamily, axialReflectedRayFamily, axialReflectedRay,
      reflectedUnitDirection, reflectedDirection, subtractDirection,
      scaleDirection, directionDot, axisDirection, semicirclePoint,
      orientationSign]
    rw [Real.cos_two_mul]
    ring
  have hincx : ((sourceRayFamily source).incidence theta).x =
      radius * Real.sin theta := by
    change 0 + radius * Real.sin theta = radius * Real.sin theta
    ring
  have hincy : ((sourceRayFamily source).incidence theta).y =
      radius * Real.cos theta := by
    change 0 + 1 * radius * Real.cos theta = radius * Real.cos theta
    ring
  have hturn : directionDet ((sourceRayFamily source).outgoing theta).1
      (canonicalOutgoingDerivative source theta) = -2 := by
    change ((sourceRayFamily source).outgoing theta).1.x *
        (2 * Real.sin (2 * theta)) -
      ((sourceRayFamily source).outgoing theta).1.y *
        (-(2 * Real.cos (2 * theta))) = -2
    rw [houtx, houty]
    nlinarith [Real.sin_sq_add_cos_sq (2 * theta)]
  have hnum : displacementDirectionDet
      (canonicalIncidenceDerivative source theta)
      ((sourceRayFamily source).outgoing theta).1 =
        -(radius * Real.cos theta) := by
    change radius * Real.cos theta * ((sourceRayFamily source).outgoing theta).1.y -
        (-(radius * Real.sin theta)) *
          ((sourceRayFamily source).outgoing theta).1.x =
      -(radius * Real.cos theta)
    rw [houtx, houty]
    change radius * Real.cos theta * -Real.cos (2 * theta) -
        (-(radius * Real.sin theta)) * -Real.sin (2 * theta) =
      -(radius * Real.cos theta)
    rw [Real.sin_two_mul, Real.cos_two_mul]
    calc
      radius * Real.cos theta * -(2 * Real.cos theta ^ 2 - 1) -
          -(radius * Real.sin theta) * -(2 * Real.sin theta * Real.cos theta) =
          radius * Real.cos theta *
            (1 - 2 * (Real.sin theta ^ 2 + Real.cos theta ^ 2)) := by ring
      _ = -(radius * Real.cos theta) := by
        rw [Real.sin_sq_add_cos_sq]
        ring
  have hlambda : displacementDirectionDet
        (canonicalIncidenceDerivative source theta)
        ((sourceRayFamily source).outgoing theta).1 /
      directionDet ((sourceRayFamily source).outgoing theta).1
        (canonicalOutgoingDerivative source theta) =
      radius * Real.cos theta / 2 := by
    rw [hnum, hturn]
    ring
  refine ⟨hlambda, ?_, ?_⟩
  · change ((sourceRayFamily source).incidence theta).x +
        (displacementDirectionDet (canonicalIncidenceDerivative source theta)
              ((sourceRayFamily source).outgoing theta).1 /
            directionDet ((sourceRayFamily source).outgoing theta).1
              (canonicalOutgoingDerivative source theta)) *
          ((sourceRayFamily source).outgoing theta).1.x =
      radius * Real.sin theta ^ 3
    rw [hlambda, hincx, houtx, Real.sin_two_mul]
    change radius * Real.sin theta +
        radius * Real.cos theta / 2 * -(2 * Real.sin theta * Real.cos theta) =
      radius * Real.sin theta ^ 3
    have hsq : 1 - Real.cos theta ^ 2 = Real.sin theta ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq theta]
    calc
      radius * Real.sin theta +
          radius * Real.cos theta / 2 * -(2 * Real.sin theta * Real.cos theta) =
          radius * Real.sin theta * (1 - Real.cos theta ^ 2) := by ring
      _ = radius * Real.sin theta ^ 3 := by rw [hsq]; ring
  · change ((sourceRayFamily source).incidence theta).y +
        (displacementDirectionDet (canonicalIncidenceDerivative source theta)
              ((sourceRayFamily source).outgoing theta).1 /
            directionDet ((sourceRayFamily source).outgoing theta).1
              (canonicalOutgoingDerivative source theta)) *
          ((sourceRayFamily source).outgoing theta).1.y =
      radius * ((1 / 2 : ℝ) * Real.cos theta +
        Real.sin theta ^ 2 * Real.cos theta)
    rw [hlambda, hincy, houty, Real.cos_two_mul]
    change radius * Real.cos theta +
        radius * Real.cos theta / 2 * -(2 * Real.cos theta ^ 2 - 1) =
      radius * ((1 / 2 : ℝ) * Real.cos theta +
        Real.sin theta ^ 2 * Real.cos theta)
    have hsq : Real.cos theta ^ 2 = 1 - Real.sin theta ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq theta]
    rw [hsq]
    ring

/-- Positive typed horizontal and vertical normalization lengths. -/
structure DimensionedCausticScales where
  horizontal : ISQLength
  vertical : ISQLength
  horizontal_pos : 0 < horizontal
  vertical_pos : 0 < vertical

/-- Project typed normalization lengths to the scalar caustic kernel through
one source chart. -/
def DimensionedCausticScales.toShared (scales : DimensionedCausticScales)
    (source : SourceData) : CausticScales where
  horizontal := sourceLengthCoordinate source scales.horizontal
  vertical := sourceLengthCoordinate source scales.vertical
  horizontal_pos := scales.horizontal_pos
  vertical_pos := scales.vertical_pos

/-- Canonical dimensioned normalization scales: the mirror radius in both
coordinate directions. -/
def canonicalScaleQuantities (source : SourceData) : DimensionedCausticScales where
  horizontal := source.radius
  vertical := source.radius
  horizontal_pos := source.radius_pos
  vertical_pos := source.radius_pos

/-- Scalar projection of the canonical dimensioned normalization scales. -/
def canonicalScales (source : SourceData) : CausticScales :=
  (canonicalScaleQuantities source).toShared source

/-- On a sufficiently small positive branch, the canonical envelope is the
forward limiting intersection of neighboring physical rays. -/
theorem canonicalCaustic_isForward (source : SourceData) :
    ∃ deltaForward : ℝ, 0 < deltaForward ∧
      ∀ theta : ℝ, 0 < theta → theta < deltaForward →
        IsAdmissibleSmallPositiveAngle source theta ∧
          IsForwardLimitingCausticPoint (sourceRayFamily source) theta
            (canonicalCaustic source theta) := by
  refine ⟨Real.pi / 2, by positivity, ?_⟩
  intro theta htheta_pos htheta_lt
  have hdomain : theta ∈ (sourceRayFamily source).domain := by
    change |theta| < Real.pi / 2
    rw [abs_of_pos htheta_pos]
    exact htheta_lt
  refine ⟨⟨htheta_pos, hdomain⟩, ?_⟩
  have hcos : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], htheta_lt⟩
  have hformula := canonicalCaustic_coordinateFormula source theta
  dsimp only at hformula
  have hparameter :
      0 < displacementDirectionDet (canonicalIncidenceDerivative source theta)
            ((sourceRayFamily source).outgoing theta).1 /
          directionDet ((sourceRayFamily source).outgoing theta).1
            (canonicalOutgoingDerivative source theta) := by
    rw [hformula.1]
    exact div_pos (mul_pos source.radius_pos hcos) (by norm_num)
  apply forwardCaustic_of_positive_parameter
      (sourceRayFamily source) theta (canonicalRayDerivativeData source theta)
  · change DifferentiableReflectedRayFamily
      (axialReflectedRayFamily (sourceMirror source) .upper)
    exact axialReflectedRayFamily_differentiable (sourceMirror source) .upper
  · exact canonicalRayDerivativeData_spec source theta hdomain
  · dsimp only [canonicalRayDerivativeData]
    exact hparameter

/-- A typed candidate for the requested offset, normalized coefficient, and
reduced positive rational exponent. -/
structure CandidateData where
  offset : ISQLength
  amplitude : ℝ
  amplitude_ne_zero : amplitude ≠ 0
  exponent : ReducedPositiveExponent

/-- Project a typed candidate to the shared scalar asymptotic chart. -/
def candidateAsymptoticData (source : SourceData) (candidate : CandidateData) :
    CausticAsymptoticData where
  offset := sourceLengthCoordinate source candidate.offset
  amplitude := candidate.amplitude
  amplitude_ne_zero := candidate.amplitude_ne_zero
  exponent := candidate.exponent

/-- The typed length contribution represented by normalized power-law data.
Only a dimensionless ratio is raised to the rational power. -/
def normalizedPowerContribution (source : SourceData)
    (scales : DimensionedCausticScales) (candidate : CandidateData)
    (horizontalDisplacement : ISQLength) : ISQLength :=
  ⟨sourceLengthCoordinate source scales.vertical * candidate.amplitude *
    Real.rpow
      (|sourceLengthCoordinate source horizontalDisplacement| /
        sourceLengthCoordinate source scales.horizontal)
      candidate.exponent.value⟩

/-- Governing solution predicate for C.4: a relative-remainder power law for
the canonical forward caustic on the positive small-angle branch. -/
def IsRequestedSolution (source : SourceData) (candidate : CandidateData) : Prop :=
  IsSmallAngleCausticAsymptotic (sourceRayFamily source)
    (canonicalCaustic source) (canonicalScales source)
    (candidateAsymptoticData source candidate)

/-- Exact punctured-neighborhood quotients, zero-jets, and one-sided limits
for the canonical normalized caustic coordinates. -/
theorem canonicalCaustic_differenceQuotients (source : SourceData) :
    let radius := sourceLengthCoordinate source source.radius
    let offset : ISQLength := ⟨radius / 2⟩
    let horizontalCoordinate : ℝ → ℝ := fun theta =>
      ((canonicalCaustic source theta).x -
          (sourceRayFamily source).mirror.center.x) / radius
    let verticalCoordinate : ℝ → ℝ := fun theta =>
      ((canonicalCaustic source theta).y -
          sourceLengthCoordinate source offset) / radius
    horizontalCoordinate 0 = 0 ∧
      deriv horizontalCoordinate 0 = 0 ∧
      deriv (deriv horizontalCoordinate) 0 = 0 ∧
      deriv (deriv (deriv horizontalCoordinate)) 0 = 6 ∧
      verticalCoordinate 0 = 0 ∧
      deriv verticalCoordinate 0 = 0 ∧
      deriv (deriv verticalCoordinate) 0 = (3 : ℝ) / 2 ∧
      (∀ theta : ℝ, 0 < theta → theta < Real.pi / 2 →
        |(canonicalCaustic source theta).x -
              (sourceRayFamily source).mirror.center.x| / radius / theta ^ 3 =
            (Real.sin theta / theta) ^ 3 ∧
          verticalCoordinate theta / theta ^ 2 =
            (1 / 2 : ℝ) * ((Real.cos theta - 1) / theta ^ 2) +
              (Real.sin theta / theta) ^ 2 * Real.cos theta ∧
          (Real.cos theta - 1) / theta ^ 2 =
            -(1 / 2 : ℝ) *
              (Real.sin (theta / 2) / (theta / 2)) ^ 2) ∧
      Filter.Tendsto
        (fun theta : ℝ =>
          |(canonicalCaustic source theta).x -
                (sourceRayFamily source).mirror.center.x| /
              radius / theta ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
      Filter.Tendsto
        (fun theta : ℝ => verticalCoordinate theta / theta ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((3 : ℝ) / 4)) := by
  let radius := sourceLengthCoordinate source source.radius
  let offset : ISQLength := ⟨radius / 2⟩
  let horizontalCoordinate : ℝ → ℝ := fun theta =>
    ((canonicalCaustic source theta).x -
        (sourceRayFamily source).mirror.center.x) / radius
  let verticalCoordinate : ℝ → ℝ := fun theta =>
    ((canonicalCaustic source theta).y -
        sourceLengthCoordinate source offset) / radius
  change horizontalCoordinate 0 = 0 ∧
      deriv horizontalCoordinate 0 = 0 ∧
      deriv (deriv horizontalCoordinate) 0 = 0 ∧
      deriv (deriv (deriv horizontalCoordinate)) 0 = 6 ∧
      verticalCoordinate 0 = 0 ∧
      deriv verticalCoordinate 0 = 0 ∧
      deriv (deriv verticalCoordinate) 0 = (3 : ℝ) / 2 ∧
      (∀ theta : ℝ, 0 < theta → theta < Real.pi / 2 →
        |(canonicalCaustic source theta).x -
              (sourceRayFamily source).mirror.center.x| / radius / theta ^ 3 =
            (Real.sin theta / theta) ^ 3 ∧
          verticalCoordinate theta / theta ^ 2 =
            (1 / 2 : ℝ) * ((Real.cos theta - 1) / theta ^ 2) +
              (Real.sin theta / theta) ^ 2 * Real.cos theta ∧
          (Real.cos theta - 1) / theta ^ 2 =
            -(1 / 2 : ℝ) *
              (Real.sin (theta / 2) / (theta / 2)) ^ 2) ∧
      Filter.Tendsto
        (fun theta : ℝ =>
          |(canonicalCaustic source theta).x -
                (sourceRayFamily source).mirror.center.x| /
              radius / theta ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
      Filter.Tendsto
        (fun theta : ℝ => verticalCoordinate theta / theta ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((3 : ℝ) / 4))
  have hradius : 0 < radius := source.radius_pos
  have hradius_ne : radius ≠ 0 := ne_of_gt hradius
  have hcenterx : (sourceRayFamily source).mirror.center.x = 0 := by
    rfl
  have hxfun : horizontalCoordinate = fun theta => Real.sin theta ^ 3 := by
    funext theta
    have hformula := canonicalCaustic_coordinateFormula source theta
    dsimp only at hformula
    change ((canonicalCaustic source theta).x -
        (sourceRayFamily source).mirror.center.x) / radius = Real.sin theta ^ 3
    rw [hformula.2.1, hcenterx]
    change (radius * Real.sin theta ^ 3 - 0) / radius = Real.sin theta ^ 3
    rw [sub_zero]
    exact mul_div_cancel_left₀ _ hradius_ne
  have hyfun : verticalCoordinate = fun theta =>
      (1 / 2 : ℝ) * (Real.cos theta - 1) +
        Real.sin theta ^ 2 * Real.cos theta := by
    funext theta
    have hformula := canonicalCaustic_coordinateFormula source theta
    dsimp only at hformula
    change ((canonicalCaustic source theta).y - radius / 2) / radius =
      (1 / 2 : ℝ) * (Real.cos theta - 1) +
        Real.sin theta ^ 2 * Real.cos theta
    rw [hformula.2.2]
    have hfactor :
        radius * ((1 / 2 : ℝ) * Real.cos theta +
              Real.sin theta ^ 2 * Real.cos theta) - radius / 2 =
          radius * ((1 / 2 : ℝ) * (Real.cos theta - 1) +
            Real.sin theta ^ 2 * Real.cos theta) := by
      ring
    rw [hfactor]
    exact mul_div_cancel_left₀ _ hradius_ne
  have hdx1 : deriv (fun theta : ℝ => Real.sin theta ^ 3) =
      fun theta => 3 * Real.sin theta ^ 2 * Real.cos theta := by
    funext theta
    have h := ((Real.hasDerivAt_sin theta).pow 3).deriv
    convert h using 1 <;> norm_num <;> ring
  have hdx2 : deriv (fun theta : ℝ =>
      3 * Real.sin theta ^ 2 * Real.cos theta) =
      fun theta => 6 * Real.sin theta * Real.cos theta ^ 2 -
        3 * Real.sin theta ^ 3 := by
    funext theta
    have h := (((Real.hasDerivAt_sin theta).pow 2).mul
      (Real.hasDerivAt_cos theta)).const_mul 3
    have hh : HasDerivAt
        (fun t : ℝ => 3 * Real.sin t ^ 2 * Real.cos t)
        (6 * Real.sin theta * Real.cos theta ^ 2 -
          3 * Real.sin theta ^ 3) theta := by
      convert h using 1 <;>
        first
        | rfl
        | (funext t; simp; ring)
        | (simp; ring)
    exact hh.deriv
  have hdx3 : deriv (fun theta : ℝ =>
      6 * Real.sin theta * Real.cos theta ^ 2 -
        3 * Real.sin theta ^ 3) 0 = 6 := by
    have hfirst := ((Real.hasDerivAt_sin 0).mul
      ((Real.hasDerivAt_cos 0).pow 2)).const_mul 6
    have hsecond := ((Real.hasDerivAt_sin 0).pow 3).const_mul 3
    have h := hfirst.sub hsecond
    have hh : HasDerivAt
        (fun theta : ℝ =>
          6 * Real.sin theta * Real.cos theta ^ 2 -
            3 * Real.sin theta ^ 3) 6 0 := by
      convert h using 1 <;>
        first
        | rfl
        | (funext t; simp; ring)
        | norm_num
    exact hh.deriv
  have hdy1 : deriv (fun theta : ℝ =>
      (1 / 2 : ℝ) * (Real.cos theta - 1) +
        Real.sin theta ^ 2 * Real.cos theta) =
      fun theta =>
        -(1 / 2 : ℝ) * Real.sin theta +
          2 * Real.sin theta * Real.cos theta ^ 2 -
          Real.sin theta ^ 3 := by
    funext theta
    have hleft := ((Real.hasDerivAt_cos theta).sub
      (hasDerivAt_const (x := theta) (c := (1 : ℝ)))).const_mul (1 / 2 : ℝ)
    have hright := ((Real.hasDerivAt_sin theta).pow 2).mul
      (Real.hasDerivAt_cos theta)
    have h := hleft.add hright
    have hh : HasDerivAt
        (fun t : ℝ =>
          (1 / 2 : ℝ) * (Real.cos t - 1) +
            Real.sin t ^ 2 * Real.cos t)
        (-(1 / 2 : ℝ) * Real.sin theta +
          2 * Real.sin theta * Real.cos theta ^ 2 -
          Real.sin theta ^ 3) theta := by
      convert h using 1 <;>
        first
        | rfl
        | (funext t; simp; ring)
        | (simp; ring)
    exact hh.deriv
  have hdy2 : deriv (fun theta : ℝ =>
      -(1 / 2 : ℝ) * Real.sin theta +
        2 * Real.sin theta * Real.cos theta ^ 2 -
        Real.sin theta ^ 3) 0 = (3 : ℝ) / 2 := by
    have hfirst := (Real.hasDerivAt_sin 0).const_mul (-(1 / 2 : ℝ))
    have hsecond := ((Real.hasDerivAt_sin 0).mul
      ((Real.hasDerivAt_cos 0).pow 2)).const_mul 2
    have hthird := (Real.hasDerivAt_sin 0).pow 3
    have h := (hfirst.add hsecond).sub hthird
    have hh : HasDerivAt
        (fun theta : ℝ =>
          -(1 / 2 : ℝ) * Real.sin theta +
            2 * Real.sin theta * Real.cos theta ^ 2 -
            Real.sin theta ^ 3) ((3 : ℝ) / 2) 0 := by
      convert h using 1 <;>
        first
        | rfl
        | (funext t; simp; ring)
        | norm_num
    exact hh.deriv
  have hhalfQuotient (theta : ℝ) (htheta_ne : theta ≠ 0) :
      (-2 * Real.sin (theta / 2) ^ 2) / theta ^ 2 =
        -(1 / 2 : ℝ) *
          (Real.sin (theta / 2) / (theta / 2)) ^ 2 := by
    have hhalf_ne : theta / 2 ≠ 0 :=
      div_ne_zero htheta_ne (by norm_num)
    have htheta_sq : theta ^ 2 = 4 * (theta / 2) ^ 2 := by
      ring
    apply (div_eq_iff (pow_ne_zero 2 htheta_ne)).2
    rw [div_pow]
    symm
    calc
      -(1 / 2 : ℝ) *
            (Real.sin (theta / 2) ^ 2 / (theta / 2) ^ 2) * theta ^ 2 =
          -(1 / 2 : ℝ) *
            (Real.sin (theta / 2) ^ 2 / (theta / 2) ^ 2) *
              (4 * (theta / 2) ^ 2) := by rw [htheta_sq]
      _ = -2 *
          ((Real.sin (theta / 2) ^ 2 / (theta / 2) ^ 2) *
            (theta / 2) ^ 2) := by ring
      _ = -2 * Real.sin (theta / 2) ^ 2 := by
        rw [div_mul_cancel₀ _ (pow_ne_zero 2 hhalf_ne)]
  rw [hxfun, hyfun]
  refine ⟨by norm_num, ?_, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdx1]
    norm_num
  · rw [hdx1, hdx2]
    norm_num
  · rw [hdx1, hdx2]
    exact hdx3
  · rw [hdy1]
    norm_num
  · rw [hdy1]
    exact hdy2
  · intro theta htheta htheta_lt
    have htheta_ne : theta ≠ 0 := ne_of_gt htheta
    have hsin_pos : 0 < Real.sin theta :=
      Real.sin_pos_of_pos_of_lt_pi htheta (by nlinarith [Real.pi_pos])
    have hformula := canonicalCaustic_coordinateFormula source theta
    dsimp only at hformula
    constructor
    · rw [hformula.2.1, hcenterx]
      change |radius * Real.sin theta ^ 3 - 0| / radius / theta ^ 3 =
        (Real.sin theta / theta) ^ 3
      rw [sub_zero]
      rw [abs_of_pos (mul_pos hradius (pow_pos hsin_pos 3))]
      rw [mul_div_cancel_left₀ _ hradius_ne, div_pow]
    constructor
    · ring
    · have hhalf : Real.cos theta - 1 =
          -2 * Real.sin (theta / 2) ^ 2 := by
        have hcos_half : Real.cos theta =
            1 - 2 * Real.sin (theta / 2) ^ 2 := by
          calc
            Real.cos theta = Real.cos (theta / 2 + theta / 2) := by
              congr 1 <;> ring
            _ = 1 - 2 * Real.sin (theta / 2) ^ 2 := by
              rw [Real.cos_add]
              nlinarith [Real.sin_sq_add_cos_sq (theta / 2)]
        rw [hcos_half]
        ring
      rw [hhalf]
      exact hhalfQuotient theta htheta_ne
  · let L := nhdsWithin (0 : ℝ) (Set.Ioi 0)
    have hL : L ≤ nhds (0 : ℝ) := by
      exact inf_le_left
    have hpos : ∀ᶠ theta in L, 0 < theta := by
      exact self_mem_nhdsWithin
    have hid_ne : ∀ᶠ theta in L, id theta ≠ 0 := by
      filter_upwards [hpos] with theta htheta
      exact ne_of_gt htheta
    have hsin_equiv := Real.isEquivalent_sin.mono hL
    have hsin_ratio : Filter.Tendsto
        (fun theta : ℝ => Real.sin theta / theta) L (nhds 1) := by
      have ht := (Asymptotics.isEquivalent_iff_tendsto_one hid_ne).1 hsin_equiv
      convert ht using 1 <;>
        first
        | rfl
        | (funext theta; rfl)
    have hpow : Filter.Tendsto
        (fun theta : ℝ => (Real.sin theta / theta) ^ 3) L (nhds 1) := by
      simpa using hsin_ratio.pow 3
    apply Filter.Tendsto.congr' _ hpow
    have hlt : ∀ᶠ theta in L, theta < Real.pi / 2 :=
      hL (Iio_mem_nhds (by positivity : (0 : ℝ) < Real.pi / 2))
    filter_upwards [hpos, hlt] with theta htheta htheta_lt
    have htheta_ne : theta ≠ 0 := ne_of_gt htheta
    have hsin_pos : 0 < Real.sin theta :=
      Real.sin_pos_of_pos_of_lt_pi htheta (by nlinarith [Real.pi_pos])
    have hformula := canonicalCaustic_coordinateFormula source theta
    dsimp only at hformula
    symm
    rw [hformula.2.1, hcenterx]
    change |radius * Real.sin theta ^ 3 - 0| / radius / theta ^ 3 =
      (Real.sin theta / theta) ^ 3
    rw [sub_zero]
    rw [abs_of_pos (mul_pos hradius (pow_pos hsin_pos 3))]
    rw [mul_div_cancel_left₀ _ hradius_ne, div_pow]
  · let L := nhdsWithin (0 : ℝ) (Set.Ioi 0)
    have hL : L ≤ nhds (0 : ℝ) := by
      exact inf_le_left
    have hpos : ∀ᶠ theta in L, 0 < theta := by
      exact self_mem_nhdsWithin
    have hid_ne : ∀ᶠ theta in L, id theta ≠ 0 := by
      filter_upwards [hpos] with theta htheta
      exact ne_of_gt htheta
    have hsin_equiv := Real.isEquivalent_sin.mono hL
    have hsin_ratio : Filter.Tendsto
        (fun theta : ℝ => Real.sin theta / theta) L (nhds 1) := by
      have ht := (Asymptotics.isEquivalent_iff_tendsto_one hid_ne).1 hsin_equiv
      convert ht using 1 <;>
        first
        | rfl
        | (funext theta; rfl)
    have hhalf_map : Filter.Tendsto (fun theta : ℝ => theta / 2) L L := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa only [id_eq, zero_div] using
          (continuousAt_id.div_const (2 : ℝ)).mono_left hL
      · filter_upwards [hpos] with theta htheta
        exact div_pos htheta (by norm_num)
    have hhalf_ratio : Filter.Tendsto
        (fun theta : ℝ => Real.sin (theta / 2) / (theta / 2)) L (nhds 1) := by
      exact hsin_ratio.comp hhalf_map
    have hcos : Filter.Tendsto (fun theta : ℝ => Real.cos theta) L (nhds 1) := by
      simpa using Real.continuous_cos.continuousAt.mono_left hL
    have hcos_quot : Filter.Tendsto
        (fun theta : ℝ => (Real.cos theta - 1) / theta ^ 2) L
        (nhds (-(1 / 2 : ℝ))) := by
      have ht := (hhalf_ratio.pow 2).const_mul (-(1 / 2 : ℝ))
      have ht' : Filter.Tendsto
          (fun theta : ℝ => -(1 / 2 : ℝ) *
            (Real.sin (theta / 2) / (theta / 2)) ^ 2) L
          (nhds (-(1 / 2 : ℝ))) := by
        simpa using ht
      apply Filter.Tendsto.congr' _ ht'
      filter_upwards [hpos] with theta htheta
      have htheta_ne : theta ≠ 0 := ne_of_gt htheta
      have hhalf : Real.cos theta - 1 =
          -2 * Real.sin (theta / 2) ^ 2 := by
        have hcos_half : Real.cos theta =
            1 - 2 * Real.sin (theta / 2) ^ 2 := by
          calc
            Real.cos theta = Real.cos (theta / 2 + theta / 2) := by
              congr 1 <;> ring
            _ = 1 - 2 * Real.sin (theta / 2) ^ 2 := by
              rw [Real.cos_add]
              nlinarith [Real.sin_sq_add_cos_sq (theta / 2)]
        rw [hcos_half]
        ring
      rw [hhalf]
      exact (hhalfQuotient theta htheta_ne).symm
    have hvertical_expr : Filter.Tendsto
        (fun theta : ℝ =>
          (1 / 2 : ℝ) * ((Real.cos theta - 1) / theta ^ 2) +
            (Real.sin theta / theta) ^ 2 * Real.cos theta) L
        (nhds ((3 : ℝ) / 4)) := by
      have ht := (hcos_quot.const_mul (1 / 2 : ℝ)).add
        ((hsin_ratio.pow 2).mul hcos)
      convert ht using 1 <;> norm_num
    apply Filter.Tendsto.congr' _ hvertical_expr
    filter_upwards [hpos] with theta htheta
    ring

/-- The explicit first nonzero horizontal and vertical leading powers of the
canonical caustic. -/
theorem canonicalCaustic_explicitLeadingPowers (source : SourceData) :
    let radius := sourceLengthCoordinate source source.radius
    let offset : ISQLength := ⟨radius / 2⟩
    let orderThree : ReducedPositiveExponent :=
      { numerator := 3
        denominator := 1
        numerator_pos := by norm_num
        denominator_pos := by norm_num
        coprime := by norm_num }
    let orderTwo : ReducedPositiveExponent :=
      { numerator := 2
        denominator := 1
        numerator_pos := by norm_num
        denominator_pos := by norm_num
        coprime := by norm_num }
    HasLeadingPowerAtZero (sourceRayFamily source).domain
        (fun theta =>
          |(canonicalCaustic source theta).x -
                (sourceRayFamily source).mirror.center.x| /
            (canonicalScales source).horizontal)
        1 orderThree ∧
    HasLeadingPowerAtZero (sourceRayFamily source).domain
        (fun theta =>
          ((canonicalCaustic source theta).y -
              sourceLengthCoordinate source offset) /
            (canonicalScales source).vertical)
        ((3 : ℝ) / 4) orderTwo := by
  let radius := sourceLengthCoordinate source source.radius
  let offset : ISQLength := ⟨radius / 2⟩
  let orderThree : ReducedPositiveExponent :=
    { numerator := 3
      denominator := 1
      numerator_pos := by norm_num
      denominator_pos := by norm_num
      coprime := by norm_num }
  let orderTwo : ReducedPositiveExponent :=
    { numerator := 2
      denominator := 1
      numerator_pos := by norm_num
      denominator_pos := by norm_num
      coprime := by norm_num }
  change HasLeadingPowerAtZero (sourceRayFamily source).domain
      (fun theta =>
        |(canonicalCaustic source theta).x -
              (sourceRayFamily source).mirror.center.x| /
          (canonicalScales source).horizontal)
      1 orderThree ∧
    HasLeadingPowerAtZero (sourceRayFamily source).domain
      (fun theta =>
        ((canonicalCaustic source theta).y -
            sourceLengthCoordinate source offset) /
          (canonicalScales source).vertical)
      ((3 : ℝ) / 4) orderTwo
  have hquotients := canonicalCaustic_differenceQuotients source
  dsimp only at hquotients
  rcases hquotients with
    ⟨_hx0, _hx1, _hx2, _hx3, _hy0, _hy1, _hy2,
      _hexact, hxlimit, hylimit⟩
  have hxlimit' : Filter.Tendsto
      (fun theta : ℝ =>
        |(canonicalCaustic source theta).x -
              (sourceRayFamily source).mirror.center.x| /
            (canonicalScales source).horizontal / theta ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    dsimp only [canonicalScales, canonicalScaleQuantities,
      DimensionedCausticScales.toShared]
    exact hxlimit
  have hylimit' : Filter.Tendsto
      (fun theta : ℝ =>
        (((canonicalCaustic source theta).y -
              sourceLengthCoordinate source offset) /
            (canonicalScales source).vertical) / theta ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((3 : ℝ) / 4)) := by
    dsimp only [canonicalScales, canonicalScaleQuantities,
      DimensionedCausticScales.toShared, offset, radius]
    exact hylimit
  have horderThree : orderThree.value = 3 := by
    dsimp only [orderThree, ReducedPositiveExponent.value]
    norm_num
  have horderTwo : orderTwo.value = 2 := by
    dsimp only [orderTwo, ReducedPositiveExponent.value]
    norm_num
  constructor
  · refine ⟨?_, by norm_num, ?_⟩
    · refine ⟨Real.pi / 2, by positivity, ?_⟩
      intro theta htheta htheta_lt
      change |theta| < Real.pi / 2
      rw [abs_of_pos htheta]
      exact htheta_lt
    · intro epsilon hepsilon
      rcases (Metric.tendsto_nhdsWithin_nhds.mp hxlimit') epsilon hepsilon with
        ⟨delta, hdelta, hbound⟩
      refine ⟨delta, hdelta, ?_⟩
      intro theta htheta htheta_lt
      have hdist : dist theta 0 < delta := by
        simpa only [Real.dist_eq, sub_zero, abs_of_pos htheta] using htheta_lt
      have hb := hbound htheta hdist
      rw [Real.dist_eq] at hb
      rw [horderThree]
      have hrpow : Real.rpow theta 3 = theta ^ (3 : ℕ) := by
        exact Real.rpow_natCast theta 3
      rw [hrpow]
      simpa only [one_mul] using hb
  · refine ⟨?_, by norm_num, ?_⟩
    · refine ⟨Real.pi / 2, by positivity, ?_⟩
      intro theta htheta htheta_lt
      change |theta| < Real.pi / 2
      rw [abs_of_pos htheta]
      exact htheta_lt
    · have hratio0 : Filter.Tendsto
          (fun theta : ℝ =>
            ((((canonicalCaustic source theta).y -
                  sourceLengthCoordinate source offset) /
                (canonicalScales source).vertical) / theta ^ 2) /
              ((3 : ℝ) / 4))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
        have ht := hylimit'.div_const ((3 : ℝ) / 4)
        convert ht using 1 <;> norm_num
      have hratio : Filter.Tendsto
          (fun theta : ℝ =>
            ((canonicalCaustic source theta).y -
                sourceLengthCoordinate source offset) /
              (canonicalScales source).vertical /
              (((3 : ℝ) / 4) * Real.rpow theta orderTwo.value))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
        apply Filter.Tendsto.congr' _ hratio0
        filter_upwards [self_mem_nhdsWithin] with theta htheta
        have htheta_ne : theta ≠ 0 := ne_of_gt htheta
        rw [horderTwo]
        have hrpow : Real.rpow theta 2 = theta ^ (2 : ℕ) := by
          exact Real.rpow_natCast theta 2
        rw [hrpow]
        ring
      intro epsilon hepsilon
      rcases (Metric.tendsto_nhdsWithin_nhds.mp hratio) epsilon hepsilon with
        ⟨delta, hdelta, hbound⟩
      refine ⟨delta, hdelta, ?_⟩
      intro theta htheta htheta_lt
      have hdist : dist theta 0 < delta := by
        simpa only [Real.dist_eq, sub_zero, abs_of_pos htheta] using htheta_lt
      have hb := hbound htheta hdist
      simpa only [Real.dist_eq] using hb

/-- Source-specific existence of nonzero leading powers together with the
physical forward-branch condition. -/
theorem canonicalCaustic_hasLeadingPowers (source : SourceData) :
    ∃ offset : ISQLength,
      ∃ horizontalAmplitude verticalAmplitude : ℝ,
        ∃ horizontalOrder verticalOrder : ReducedPositiveExponent,
          0 < horizontalAmplitude ∧
            verticalAmplitude ≠ 0 ∧
            (∃ deltaForward : ℝ, 0 < deltaForward ∧
              ∀ theta : ℝ, 0 < theta → theta < deltaForward →
                theta ∈ (sourceRayFamily source).domain ∧
                  IsForwardLimitingCausticPoint
                    (sourceRayFamily source) theta
                    (canonicalCaustic source theta)) ∧
            HasLeadingPowerAtZero (sourceRayFamily source).domain
              (fun theta =>
                |(canonicalCaustic source theta).x -
                      (sourceRayFamily source).mirror.center.x| /
                  (canonicalScales source).horizontal)
              horizontalAmplitude horizontalOrder ∧
            HasLeadingPowerAtZero (sourceRayFamily source).domain
              (fun theta =>
                ((canonicalCaustic source theta).y -
                    sourceLengthCoordinate source offset) /
                  (canonicalScales source).vertical)
              verticalAmplitude verticalOrder := by
  let radius := sourceLengthCoordinate source source.radius
  let offset : ISQLength := ⟨radius / 2⟩
  let orderThree : ReducedPositiveExponent :=
    { numerator := 3
      denominator := 1
      numerator_pos := by norm_num
      denominator_pos := by norm_num
      coprime := by norm_num }
  let orderTwo : ReducedPositiveExponent :=
    { numerator := 2
      denominator := 1
      numerator_pos := by norm_num
      denominator_pos := by norm_num
      coprime := by norm_num }
  refine ⟨offset, 1, (3 : ℝ) / 4, orderThree, orderTwo,
    by norm_num, by norm_num, ?_, ?_, ?_⟩
  · rcases canonicalCaustic_isForward source with ⟨delta, hdelta, hforward⟩
    refine ⟨delta, hdelta, ?_⟩
    intro theta htheta htheta_lt
    rcases hforward theta htheta htheta_lt with ⟨hadmissible, hcaustic⟩
    exact ⟨hadmissible.2, hcaustic⟩
  · have hleading := canonicalCaustic_explicitLeadingPowers source
    dsimp only at hleading
    exact hleading.1
  · have hleading := canonicalCaustic_explicitLeadingPowers source
    dsimp only at hleading
    exact hleading.2

/-- Typed candidate data are unique for a fixed source chart, ray family,
caustic branch, and positive scalar normalization. -/
theorem smallAngleCausticAsymptotic_data_unique (source : SourceData)
    (family : ReflectedRayFamily) (caustic : ℝ → Point2)
    (scales : CausticScales) (first second : CandidateData)
    (hfirst : IsSmallAngleCausticAsymptotic family caustic scales
      (candidateAsymptoticData source first))
    (hsecond : IsSmallAngleCausticAsymptotic family caustic scales
      (candidateAsymptoticData source second)) :
    first = second := by
  let xi := fun theta : ℝ =>
    |(caustic theta).x - family.mirror.center.x| / scales.horizontal
  let etaFirst := fun theta : ℝ =>
    ((caustic theta).y - sourceLengthCoordinate source first.offset) /
      scales.vertical
  let etaSecond := fun theta : ℝ =>
    ((caustic theta).y - sourceLengthCoordinate source second.offset) /
      scales.vertical
  let alphaFirst := first.exponent.value
  let alphaSecond := second.exponent.value
  change
      (∃ delta : ℝ, 0 < delta ∧ ∀ theta : ℝ, 0 < theta → theta < delta →
        theta ∈ family.domain ∧
          IsForwardLimitingCausticPoint family theta (caustic theta) ∧
          0 < xi theta) ∧
      (∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
        ∀ theta : ℝ, 0 < theta → theta < delta → xi theta < epsilon) ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
        ∀ theta : ℝ, 0 < theta → theta < delta →
          |etaFirst theta - first.amplitude *
              Real.rpow (xi theta) alphaFirst| ≤
            epsilon * Real.rpow (xi theta) alphaFirst at hfirst
  change
      (∃ delta : ℝ, 0 < delta ∧ ∀ theta : ℝ, 0 < theta → theta < delta →
        theta ∈ family.domain ∧
          IsForwardLimitingCausticPoint family theta (caustic theta) ∧
          0 < xi theta) ∧
      (∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
        ∀ theta : ℝ, 0 < theta → theta < delta → xi theta < epsilon) ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
        ∀ theta : ℝ, 0 < theta → theta < delta →
          |etaSecond theta - second.amplitude *
              Real.rpow (xi theta) alphaSecond| ≤
            epsilon * Real.rpow (xi theta) alphaSecond at hsecond
  let L := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hL : L ≤ nhds (0 : ℝ) := by
    exact inf_le_left
  rcases hfirst.1 with ⟨branchDelta, hbranchDelta, hbranch⟩
  have hxi_nonneg (theta : ℝ) : 0 ≤ xi theta := by
    exact div_nonneg (abs_nonneg _) (le_of_lt scales.horizontal_pos)
  have hxi : Filter.Tendsto xi L (nhds 0) := by
    apply Metric.tendsto_nhdsWithin_nhds.mpr
    intro epsilon hepsilon
    rcases hfirst.2.1 epsilon hepsilon with ⟨delta, hdelta, hsmall⟩
    refine ⟨delta, hdelta, ?_⟩
    intro theta htheta htheta_dist
    have htheta_pos : 0 < theta := htheta
    have htheta_lt : theta < delta := by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos htheta_pos] using htheta_dist
    have hs := hsmall theta htheta_pos htheta_lt
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hxi_nonneg theta)]
    exact hs
  have hxi_pos : ∀ᶠ theta in L, 0 < xi theta := by
    have hlt : ∀ᶠ theta in L, theta < branchDelta :=
      hL (Iio_mem_nhds hbranchDelta)
    filter_upwards [self_mem_nhdsWithin, hlt] with theta htheta htheta_lt
    exact (hbranch theta htheta htheta_lt).2.2
  have halphaFirst : 0 < alphaFirst := by
    exact div_pos (Nat.cast_pos.mpr first.exponent.numerator_pos)
      (Nat.cast_pos.mpr first.exponent.denominator_pos)
  have halphaSecond : 0 < alphaSecond := by
    exact div_pos (Nat.cast_pos.mpr second.exponent.numerator_pos)
      (Nat.cast_pos.mpr second.exponent.denominator_pos)
  have rpow_tendsto_zero (alpha : ℝ) (halpha : 0 < alpha) :
      Filter.Tendsto (fun theta => Real.rpow (xi theta) alpha) L (nhds 0) := by
    let L0 := nhdsWithin (0 : ℝ) (Set.Ioi 0)
    have hbase : Filter.Tendsto (fun x : ℝ => Real.rpow x alpha) L0 (nhds 0) := by
      have hpos0 : ∀ᶠ x in L0, 0 < x := by
        exact self_mem_nhdsWithin
      have ht := Real.tendsto_exp_atBot.comp
        (Real.tendsto_log_nhdsGT_zero.atBot_mul_const halpha)
      apply Filter.Tendsto.congr' _ ht
      filter_upwards [hpos0] with x hx
      change Real.exp (Real.log x * alpha) = Real.rpow x alpha
      calc
        Real.exp (Real.log x * alpha) = x ^ alpha :=
          (Real.rpow_def_of_pos hx alpha).symm
        _ = Real.rpow x alpha := (Real.rpow_eq_pow x alpha).symm
    apply hbase.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨hxi, hxi_pos⟩
  have hpowFirst : Filter.Tendsto
      (fun theta => Real.rpow (xi theta) alphaFirst) L (nhds 0) := by
    exact rpow_tendsto_zero alphaFirst halphaFirst
  have hpowSecond : Filter.Tendsto
      (fun theta => Real.rpow (xi theta) alphaSecond) L (nhds 0) := by
    exact rpow_tendsto_zero alphaSecond halphaSecond
  have quotient_tendsto (eta : ℝ → ℝ) (amplitude alpha : ℝ)
      (hremainder : ∀ epsilon : ℝ, 0 < epsilon →
        ∃ delta : ℝ, 0 < delta ∧ ∀ theta : ℝ,
          0 < theta → theta < delta →
            |eta theta - amplitude * Real.rpow (xi theta) alpha| ≤
              epsilon * Real.rpow (xi theta) alpha) :
      Filter.Tendsto
        (fun theta => eta theta / Real.rpow (xi theta) alpha)
        L (nhds amplitude) := by
    apply Metric.tendsto_nhdsWithin_nhds.mpr
    intro epsilon hepsilon
    rcases hremainder (epsilon / 2) (by linarith) with
      ⟨delta, hdelta, hrem⟩
    refine ⟨min delta branchDelta, lt_min hdelta hbranchDelta, ?_⟩
    intro theta htheta htheta_dist
    have htheta_pos : 0 < theta := htheta
    have htheta_lt : theta < min delta branchDelta := by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos htheta_pos] using htheta_dist
    have htheta_delta : theta < delta :=
      lt_of_lt_of_le htheta_lt (min_le_left _ _)
    have htheta_branch : theta < branchDelta :=
      lt_of_lt_of_le htheta_lt (min_le_right _ _)
    have hxi_theta : 0 < xi theta :=
      (hbranch theta htheta_pos htheta_branch).2.2
    have hpower : 0 < Real.rpow (xi theta) alpha :=
      Real.rpow_pos_of_pos hxi_theta alpha
    have hb := hrem theta htheta_pos htheta_delta
    rw [Real.dist_eq]
    have heq :
        eta theta / Real.rpow (xi theta) alpha - amplitude =
          (eta theta - amplitude * Real.rpow (xi theta) alpha) /
            Real.rpow (xi theta) alpha := by
      rw [sub_div, mul_div_cancel_right₀ _ (ne_of_gt hpower)]
    rw [heq, abs_div, abs_of_pos hpower]
    calc
      |eta theta - amplitude * Real.rpow (xi theta) alpha| /
          Real.rpow (xi theta) alpha ≤ epsilon / 2 := by
            exact (div_le_iff₀ hpower).2 hb
      _ < epsilon := by linarith
  have hqFirst := quotient_tendsto etaFirst first.amplitude alphaFirst
    hfirst.2.2
  have hqSecond := quotient_tendsto etaSecond second.amplitude alphaSecond
    hsecond.2.2
  have hetaFirst : Filter.Tendsto etaFirst L (nhds 0) := by
    have ht := hqFirst.mul hpowFirst
    have ht' : Filter.Tendsto
        (fun theta =>
          (etaFirst theta / Real.rpow (xi theta) alphaFirst) *
            Real.rpow (xi theta) alphaFirst) L (nhds 0) := by
      simpa using ht
    apply Filter.Tendsto.congr' _ ht'
    filter_upwards [hxi_pos] with theta hxi_theta
    exact div_mul_cancel₀ _
      (ne_of_gt (Real.rpow_pos_of_pos hxi_theta alphaFirst))
  have hetaSecond : Filter.Tendsto etaSecond L (nhds 0) := by
    have ht := hqSecond.mul hpowSecond
    have ht' : Filter.Tendsto
        (fun theta =>
          (etaSecond theta / Real.rpow (xi theta) alphaSecond) *
            Real.rpow (xi theta) alphaSecond) L (nhds 0) := by
      simpa using ht
    apply Filter.Tendsto.congr' _ ht'
    filter_upwards [hxi_pos] with theta hxi_theta
    exact div_mul_cancel₀ _
      (ne_of_gt (Real.rpow_pos_of_pos hxi_theta alphaSecond))
  let offsetDifference :=
    (sourceLengthCoordinate source second.offset -
      sourceLengthCoordinate source first.offset) / scales.vertical
  have hoffset_tendsto : Filter.Tendsto (fun _ : ℝ => offsetDifference) L (nhds 0) := by
    have ht := hetaFirst.sub hetaSecond
    have heq : ∀ᶠ theta in L,
        etaFirst theta - etaSecond theta = offsetDifference := by
      filter_upwards with theta
      dsimp only [offsetDifference, etaFirst, etaSecond]
      calc
        ((caustic theta).y - sourceLengthCoordinate source first.offset) /
              scales.vertical -
            ((caustic theta).y - sourceLengthCoordinate source second.offset) /
              scales.vertical =
            (((caustic theta).y - sourceLengthCoordinate source first.offset) -
              ((caustic theta).y - sourceLengthCoordinate source second.offset)) /
                scales.vertical := (sub_div _ _ _).symm
        _ = (sourceLengthCoordinate source second.offset -
              sourceLengthCoordinate source first.offset) / scales.vertical := by
          apply congrArg (fun z : ℝ => z / scales.vertical)
          ring
    have ht' := ht.congr' heq
    simpa only [sub_zero] using ht'
  have hoffsetDifference : offsetDifference = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hoffset_tendsto
  have hoffsetCoordinate :
      sourceLengthCoordinate source first.offset =
        sourceLengthCoordinate source second.offset := by
    dsimp only [offsetDifference] at hoffsetDifference
    have hvertical_ne : scales.vertical ≠ 0 := ne_of_gt scales.vertical_pos
    apply (sub_eq_zero.mp ?_).symm
    exact (div_eq_zero_iff).mp hoffsetDifference |>.resolve_right hvertical_ne
  have hoffset : first.offset = second.offset := by
    apply WithDim.ext
    exact hoffsetCoordinate
  have heta_eq : etaFirst = etaSecond := by
    funext theta
    dsimp only [etaFirst, etaSecond]
    rw [hoffsetCoordinate]
  have not_lt_of_quotients (etaA etaB : ℝ → ℝ)
      (alphaA alphaB amplitudeA amplitudeB : ℝ)
      (heta : etaA = etaB) (hamplitudeA : amplitudeA ≠ 0)
      (hamplitudeB : amplitudeB ≠ 0)
      (hqA : Filter.Tendsto
        (fun theta => etaA theta / Real.rpow (xi theta) alphaA)
        L (nhds amplitudeA))
      (hqB : Filter.Tendsto
        (fun theta => etaB theta / Real.rpow (xi theta) alphaB)
        L (nhds amplitudeB)) :
      ¬ alphaA < alphaB := by
    intro halpha
    have hpowDifference : Filter.Tendsto
        (fun theta => Real.rpow (xi theta) (alphaB - alphaA)) L (nhds 0) := by
      have hdifference : 0 < alphaB - alphaA := sub_pos.mpr halpha
      exact rpow_tendsto_zero (alphaB - alphaA) hdifference
    have hratio := hqA.div hqB hamplitudeB
    have hqA_ne : ∀ᶠ theta in L,
        etaA theta / Real.rpow (xi theta) alphaA ≠ 0 :=
      hqA.eventually (eventually_ne_nhds hamplitudeA)
    have hquotient_eq : ∀ᶠ theta in L,
        (etaA theta / Real.rpow (xi theta) alphaA) /
            (etaB theta / Real.rpow (xi theta) alphaB) =
          Real.rpow (xi theta) (alphaB - alphaA) := by
      filter_upwards [hxi_pos, hqA_ne] with theta hxi_theta hq_ne
      have hpowerA : Real.rpow (xi theta) alphaA ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hxi_theta alphaA)
      have hpowerB : Real.rpow (xi theta) alphaB ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hxi_theta alphaB)
      have heta_ne : etaA theta ≠ 0 := by
        intro hz
        apply hq_ne
        rw [hz, zero_div]
      have hetaB_ne : etaB theta ≠ 0 := by
        rw [← congrFun heta theta]
        exact heta_ne
      rw [congrFun heta theta]
      have hrpowSub : Real.rpow (xi theta) (alphaB - alphaA) =
          Real.rpow (xi theta) alphaB / Real.rpow (xi theta) alphaA := by
        exact Real.rpow_sub hxi_theta alphaB alphaA
      rw [hrpowSub]
      exact div_div_div_cancel_left' _ _ hetaB_ne
    have hratio_zero : Filter.Tendsto
        (fun theta =>
          (etaA theta / Real.rpow (xi theta) alphaA) /
            (etaB theta / Real.rpow (xi theta) alphaB)) L (nhds 0) :=
      hpowDifference.congr' (hquotient_eq.mono fun _ h => h.symm)
    have hzero : amplitudeA / amplitudeB = 0 :=
      tendsto_nhds_unique hratio hratio_zero
    exact (div_ne_zero hamplitudeA hamplitudeB) hzero
  have halpha_not_lt : ¬ alphaFirst < alphaSecond :=
    not_lt_of_quotients etaFirst etaSecond alphaFirst alphaSecond
      first.amplitude second.amplitude heta_eq first.amplitude_ne_zero
      second.amplitude_ne_zero hqFirst hqSecond
  have halpha_not_gt : ¬ alphaSecond < alphaFirst :=
    not_lt_of_quotients etaSecond etaFirst alphaSecond alphaFirst
      second.amplitude first.amplitude heta_eq.symm second.amplitude_ne_zero
      first.amplitude_ne_zero hqSecond hqFirst
  have halpha : alphaFirst = alphaSecond :=
    le_antisymm (le_of_not_gt halpha_not_gt) (le_of_not_gt halpha_not_lt)
  have hcross : first.exponent.numerator * second.exponent.denominator =
      second.exponent.numerator * first.exponent.denominator := by
    dsimp only [alphaFirst, alphaSecond, ReducedPositiveExponent.value] at halpha
    have hdenFirst : (first.exponent.denominator : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt first.exponent.denominator_pos)
    have hdenSecond : (second.exponent.denominator : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt second.exponent.denominator_pos)
    have hcrossReal :
        (first.exponent.numerator : ℝ) * second.exponent.denominator =
          (second.exponent.numerator : ℝ) * first.exponent.denominator := by
      exact (div_eq_div_iff hdenFirst hdenSecond).mp halpha
    exact_mod_cast hcrossReal
  have hnumerator_dvd : first.exponent.numerator ∣ second.exponent.numerator := by
    apply first.exponent.coprime.dvd_mul_right.mp
    exact ⟨second.exponent.denominator, hcross.symm⟩
  have hnumerator_dvd' : second.exponent.numerator ∣ first.exponent.numerator := by
    apply second.exponent.coprime.dvd_mul_right.mp
    exact ⟨first.exponent.denominator, hcross⟩
  have hnumerator : first.exponent.numerator = second.exponent.numerator :=
    Nat.dvd_antisymm hnumerator_dvd hnumerator_dvd'
  have hdenominator : first.exponent.denominator = second.exponent.denominator := by
    apply Nat.mul_left_cancel first.exponent.numerator_pos
    simpa only [hnumerator] using hcross.symm
  have hexponent : first.exponent = second.exponent := by
    cases hfirstExponent : first.exponent with
    | mk n1 d1 hn1 hd1 hc1 =>
      cases hsecondExponent : second.exponent with
      | mk n2 d2 hn2 hd2 hc2 =>
        have hn : n1 = n2 := by
          exact
            (congrArg (fun e : ReducedPositiveExponent => e.numerator)
                hfirstExponent).symm.trans
              (hnumerator.trans
                (congrArg (fun e : ReducedPositiveExponent => e.numerator)
                  hsecondExponent))
        have hd : d1 = d2 := by
          exact
            (congrArg (fun e : ReducedPositiveExponent => e.denominator)
                hfirstExponent).symm.trans
              (hdenominator.trans
                (congrArg (fun e : ReducedPositiveExponent => e.denominator)
                  hsecondExponent))
        subst n2
        subst d2
        rfl
  have hqSecond' : Filter.Tendsto
      (fun theta => etaFirst theta / Real.rpow (xi theta) alphaFirst)
      L (nhds second.amplitude) := by
    simpa only [heta_eq, halpha] using hqSecond
  have hamplitude : first.amplitude = second.amplitude :=
    tendsto_nhds_unique hqFirst hqSecond'
  cases first
  cases second
  cases hoffset
  cases hamplitude
  cases hexponent
  rfl

/-- Changing positive normalization scales changes only the normalized
amplitude: the typed offset, reduced exponent, and dimensioned contribution
are invariant. -/
theorem requestedSolution_changeScales (source : SourceData)
    (candidate : CandidateData) (hsolution : IsRequestedSolution source candidate)
    (newScales : DimensionedCausticScales) :
    ∃! newCandidate : CandidateData,
      IsSmallAngleCausticAsymptotic (sourceRayFamily source)
          (canonicalCaustic source) (newScales.toShared source)
          (candidateAsymptoticData source newCandidate) ∧
        newCandidate.offset = candidate.offset ∧
        newCandidate.exponent = candidate.exponent ∧
        ∀ horizontalDisplacement : ISQLength,
          normalizedPowerContribution source newScales newCandidate
              horizontalDisplacement =
            normalizedPowerContribution source (canonicalScaleQuantities source)
              candidate horizontalDisplacement := by
  have hsolution' : IsSmallAngleCausticAsymptotic (sourceRayFamily source)
      (canonicalCaustic source) (canonicalScales source)
      (candidateAsymptoticData source candidate) := by
    exact hsolution
  rcases smallAngleAsymptotic_changeScales (sourceRayFamily source)
      (canonicalCaustic source) (canonicalScales source)
      (newScales.toShared source) (candidateAsymptoticData source candidate)
      hsolution' with
    ⟨newData, hdataOffset, hdataExponent, hdataAmplitude, hdataAsymptotic⟩
  let newCandidate : CandidateData :=
    { offset := candidate.offset
      amplitude := newData.amplitude
      amplitude_ne_zero := newData.amplitude_ne_zero
      exponent := candidate.exponent }
  have hprojection : candidateAsymptoticData source newCandidate = newData := by
    cases newData with
    | mk newOffset newAmplitude newAmplitude_ne_zero newExponent =>
      dsimp only [candidateAsymptoticData, newCandidate] at hdataOffset hdataExponent ⊢
      cases hdataOffset.symm
      cases hdataExponent.symm
      rfl
  have hnewAsymptotic : IsSmallAngleCausticAsymptotic
      (sourceRayFamily source) (canonicalCaustic source)
      (newScales.toShared source)
      (candidateAsymptoticData source newCandidate) := by
    rw [hprojection]
    exact hdataAsymptotic
  refine ⟨newCandidate, ?_, ?_⟩
  · refine ⟨hnewAsymptotic, rfl, rfl, ?_⟩
    intro horizontalDisplacement
    apply WithDim.ext
    let oldHorizontal := (canonicalScales source).horizontal
    let oldVertical := (canonicalScales source).vertical
    let newHorizontal := (newScales.toShared source).horizontal
    let newVertical := (newScales.toShared source).vertical
    let x := |sourceLengthCoordinate source horizontalDisplacement|
    let gamma := candidate.exponent.value
    have holdHorizontal : 0 < oldHorizontal :=
      (canonicalScales source).horizontal_pos
    have holdVertical : 0 < oldVertical :=
      (canonicalScales source).vertical_pos
    have hnewHorizontal : 0 < newHorizontal :=
      (newScales.toShared source).horizontal_pos
    have hnewVertical : 0 < newVertical :=
      (newScales.toShared source).vertical_pos
    have hq : 0 < newHorizontal / oldHorizontal :=
      div_pos hnewHorizontal holdHorizontal
    have hz : 0 ≤ x / newHorizontal :=
      div_nonneg (abs_nonneg _) (le_of_lt hnewHorizontal)
    have hqz : newHorizontal / oldHorizontal * (x / newHorizontal) =
        x / oldHorizontal := by
      calc
        newHorizontal / oldHorizontal * (x / newHorizontal) =
            (x / newHorizontal) * newHorizontal / oldHorizontal := by ring
        _ = x / oldHorizontal := by
          rw [div_mul_cancel₀ _ (ne_of_gt hnewHorizontal)]
    have hAmplitude : newData.amplitude =
        candidate.amplitude * (oldVertical / newVertical) *
          Real.rpow (newHorizontal / oldHorizontal) gamma := by
      dsimp only [candidateAsymptoticData, oldHorizontal, oldVertical,
        newHorizontal, newVertical, gamma] at hdataAmplitude
      exact hdataAmplitude
    have hmulRpow :
        Real.rpow (newHorizontal / oldHorizontal) gamma *
            Real.rpow (x / newHorizontal) gamma =
          Real.rpow
            (newHorizontal / oldHorizontal * (x / newHorizontal)) gamma := by
      symm
      exact Real.mul_rpow (le_of_lt hq) hz
    change newVertical * newData.amplitude *
          Real.rpow (x / newHorizontal) gamma =
      oldVertical * candidate.amplitude *
          Real.rpow (x / oldHorizontal) gamma
    rw [hAmplitude]
    calc
      newVertical *
            (candidate.amplitude * (oldVertical / newVertical) *
              Real.rpow (newHorizontal / oldHorizontal) gamma) *
          Real.rpow (x / newHorizontal) gamma =
          oldVertical * candidate.amplitude *
            (Real.rpow (newHorizontal / oldHorizontal) gamma *
              Real.rpow (x / newHorizontal) gamma) := by
        calc
          newVertical *
                (candidate.amplitude * (oldVertical / newVertical) *
                  Real.rpow (newHorizontal / oldHorizontal) gamma) *
              Real.rpow (x / newHorizontal) gamma =
              candidate.amplitude * ((oldVertical / newVertical) * newVertical) *
                (Real.rpow (newHorizontal / oldHorizontal) gamma *
                  Real.rpow (x / newHorizontal) gamma) := by ring
          _ = candidate.amplitude * oldVertical *
                (Real.rpow (newHorizontal / oldHorizontal) gamma *
                  Real.rpow (x / newHorizontal) gamma) := by
            rw [div_mul_cancel₀ _ (ne_of_gt hnewVertical)]
          _ = oldVertical * candidate.amplitude *
                (Real.rpow (newHorizontal / oldHorizontal) gamma *
                  Real.rpow (x / newHorizontal) gamma) := by ring
      _ = oldVertical * candidate.amplitude *
          Real.rpow
            (newHorizontal / oldHorizontal * (x / newHorizontal)) gamma := by
              rw [hmulRpow]
      _ = oldVertical * candidate.amplitude *
          Real.rpow (x / oldHorizontal) gamma := by rw [hqz]
  · intro other hother
    exact smallAngleCausticAsymptotic_data_unique source
      (sourceRayFamily source) (canonicalCaustic source)
      (newScales.toShared source) other newCandidate hother.1 hnewAsymptotic

/-- C.4 has exactly one typed candidate governed by the forward-caustic
asymptotic, and that candidate has the scale-covariant dimensioned
coefficient characterization.  No derived value occurs in this target
signature. -/
theorem existsUnique_requestedSolution (source : SourceData) :
    (∃! candidate : CandidateData, IsRequestedSolution source candidate) ∧
      ∀ candidate : CandidateData, IsRequestedSolution source candidate →
        ∀ newScales : DimensionedCausticScales,
          ∃! newCandidate : CandidateData,
            IsSmallAngleCausticAsymptotic (sourceRayFamily source)
                (canonicalCaustic source) (newScales.toShared source)
                (candidateAsymptoticData source newCandidate) ∧
              newCandidate.offset = candidate.offset ∧
              newCandidate.exponent = candidate.exponent ∧
              ∀ horizontalDisplacement : ISQLength,
                normalizedPowerContribution source newScales newCandidate
                    horizontalDisplacement =
                  normalizedPowerContribution source
                    (canonicalScaleQuantities source) candidate
                    horizontalDisplacement := by
  rcases canonicalCaustic_hasLeadingPowers source with
    ⟨offset, horizontalAmplitude, verticalAmplitude,
      horizontalOrder, verticalOrder, hhorizontalPositive,
      _hverticalNonzero, hbranch, hhorizontal, hvertical⟩
  rcases smallAngleAsymptotic_of_leadingPowers
      (sourceRayFamily source) (canonicalCaustic source)
      (canonicalScales source) (sourceLengthCoordinate source offset)
      horizontalAmplitude verticalAmplitude horizontalOrder verticalOrder
      hbranch hhorizontal hhorizontalPositive hvertical with
    ⟨data, hdataOffset, _hdataExponent, _hdataAmplitude, hdataAsymptotic⟩
  let candidate : CandidateData :=
    { offset := offset
      amplitude := data.amplitude
      amplitude_ne_zero := data.amplitude_ne_zero
      exponent := data.exponent }
  have hprojection : candidateAsymptoticData source candidate = data := by
    cases data with
    | mk dataOffset dataAmplitude dataAmplitude_ne_zero dataExponent =>
      dsimp only [candidateAsymptoticData, candidate] at hdataOffset ⊢
      cases hdataOffset.symm
      rfl
  have hcandidate : IsRequestedSolution source candidate := by
    change IsSmallAngleCausticAsymptotic (sourceRayFamily source)
      (canonicalCaustic source) (canonicalScales source)
      (candidateAsymptoticData source candidate)
    rw [hprojection]
    exact hdataAsymptotic
  constructor
  · refine ⟨candidate, hcandidate, ?_⟩
    intro other hother
    exact smallAngleCausticAsymptotic_data_unique source
      (sourceRayFamily source) (canonicalCaustic source)
      (canonicalScales source) other candidate hother hcandidate
  · intro other hother newScales
    exact requestedSolution_changeScales source other hother newScales

end Ipho2026Gpt56solBlind.ProblemIPhO2026_2_C_4
