import Ipho2026Gpt56solBlind.Shared.CausticOptics

/-!
# IPhO 2026, Problem 2, C.3

An answer-free model of the limiting intersection coordinates of neighboring
reflected rays in Figure 2g.  The requested physical point remains quantified;
the source laws identify the physical ray family and the analytic data used to
characterize its caustic.
-/

noncomputable section

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_2_C_3

open Shared.GeometricOptics

/-- Typed Figure 2g source data.  The physical mirror carries the source radius
and its strict positivity, while the ray and coefficient derivative objects are
only candidates until `SourceLaws` is assumed. -/
structure SourceData where
  unitChoice : SIUnitChoices
  mirror : PhysicalCircle unitChoice
  angle : ℝ
  rayFamily : ReflectedRayFamily
  rayDerivatives : RayDerivativeData
  coefficients : ℝ → LineCoefficients
  coefficientDerivatives : CoefficientDerivativeData

/-- The physical and analytic laws for the positive-angle, upper-semicircle
Figure 2g reflected-ray family.  No field specifies a caustic point or either
of its coordinates. -/
structure SourceLaws (S : SourceData) : Prop where
  mirror_center_is_origin :
    (physicalCircleCoordinateInSI S.unitChoice S.mirror).center =
      ({ x := 0, y := 0 } : Point2)
  ray_mirror_is_source_mirror :
    S.rayFamily.mirror = physicalCircleCoordinateInSI S.unitChoice S.mirror
  domain_is_positive_axial :
    S.rayFamily.domain = {t : ℝ | 0 < t ∧ InAxialIncidenceDomain t}
  incidence_is_upper_axial :
    ∀ t : ℝ,
      S.rayFamily.incidence t =
        (axialReflectedRayFamily
          (physicalCircleCoordinateInSI S.unitChoice S.mirror)
          .upper).incidence t
  incoming_is_upward_axial :
    S.rayFamily.incoming =
      (axialReflectedRayFamily
        (physicalCircleCoordinateInSI S.unitChoice S.mirror)
        .upper).incoming
  normal_is_upper_axial :
    ∀ t : ℝ,
      S.rayFamily.normal t =
        (axialReflectedRayFamily
          (physicalCircleCoordinateInSI S.unitChoice S.mirror)
          .upper).normal t
  outgoing_is_upper_axial :
    ∀ t : ℝ,
      S.rayFamily.outgoing t =
        (axialReflectedRayFamily
          (physicalCircleCoordinateInSI S.unitChoice S.mirror)
          .upper).outgoing t
  angle_mem_domain : S.angle ∈ S.rayFamily.domain
  rayFamily_differentiable : DifferentiableReflectedRayFamily S.rayFamily
  has_ray_derivatives :
    HasRayDerivativesAt S.rayFamily S.angle S.rayDerivatives
  turning_nonzero :
    directionDet (S.rayFamily.outgoing S.angle).1
      S.rayDerivatives.directionDerivative ≠ 0
  coefficients_describe_reflected_lines :
    ∀ t ∈ S.rayFamily.domain,
      IsReflectedLineCoefficients S.rayFamily t (S.coefficients t)
  has_coefficient_derivatives :
    HasCoefficientDerivativesAt
      (fun t => (S.coefficients t).slope)
      (fun t => (S.coefficients t).intercept)
      S.angle S.coefficientDerivatives
  slope_derivative_nonzero : S.coefficientDerivatives.slopeDerivative ≠ 0
  forward_envelope_parameter_positive :
    0 < displacementDirectionDet S.rayDerivatives.pointDerivative
          (S.rayFamily.outgoing S.angle).1 /
        directionDet (S.rayFamily.outgoing S.angle).1
          S.rayDerivatives.directionDerivative

/-- A typed point gives the requested coordinate pair exactly when its
coherent-SI image is the forward limiting caustic point of the Figure 2g ray
family. -/
def IsRequestedCoordinates (S : SourceData) (C : PhysicalPoint2) : Prop :=
  IsForwardLimitingCausticPoint S.rayFamily S.angle
    (physicalPointCoordinateInSI S.unitChoice C)

/-- The source laws identify the canonical neighboring-ray limit with the
differential caustic point and select its physical forward branch. -/
lemma source_caustic_bridge (S : SourceData) (hS : SourceLaws S) :
    let Cdiff := differentialCausticPoint S.rayFamily S.angle
      S.rayDerivatives hS.turning_nonzero
    IsForwardLimitingCausticPoint S.rayFamily S.angle Cdiff ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
        directionDet (S.rayFamily.outgoing S.angle).1
            (S.rayFamily.outgoing (S.angle + h)).1 ≠ 0 ∧
          IsForwardNeighboringIntersection S.rayFamily S.angle h
            (neighboringIntersectionPoint S.rayFamily S.angle h)) ∧
      ∀ Z : Point2,
        IsLimitingCausticPoint S.rayFamily S.angle Z ↔ Z = Cdiff := by
  dsimp only
  have hForward : IsForwardLimitingCausticPoint S.rayFamily S.angle
      (differentialCausticPoint S.rayFamily S.angle
        S.rayDerivatives hS.turning_nonzero) :=
    forwardCaustic_of_positive_parameter S.rayFamily S.angle
      S.rayDerivatives hS.rayFamily_differentiable hS.has_ray_derivatives
      hS.turning_nonzero hS.forward_envelope_parameter_positive
  have coordinate_close (P : Point2)
      (hP : IsLimitingCausticPoint S.rayFamily S.angle P)
      (e : ℝ) (he : 0 < e) :
      ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
        |(neighboringIntersectionPoint S.rayFamily S.angle h).x - P.x| < e ∧
        |(neighboringIntersectionPoint S.rayFamily S.angle h).y - P.y| < e := by
    rcases hP.2.2 e he with ⟨δ, hδ, hbound⟩
    refine ⟨δ, hδ, ?_⟩
    intro h hhpos hhsmall
    have hb := hbound h hhpos hhsmall
    dsimp only [displacementNormSq, displacement] at hb
    constructor
    · rw [abs_lt]
      constructor <;>
        nlinarith [sq_nonneg
          ((neighboringIntersectionPoint S.rayFamily S.angle h).y - P.y)]
    · rw [abs_lt]
      constructor <;>
        nlinarith [sq_nonneg
          ((neighboringIntersectionPoint S.rayFamily S.angle h).x - P.x)]
  have limiting_unique (P Q : Point2)
      (hP : IsLimitingCausticPoint S.rayFamily S.angle P)
      (hQ : IsLimitingCausticPoint S.rayFamily S.angle Q) : P = Q := by
    refine congrArg₂ Point2.mk ?_ ?_
    · by_contra hne
      have ha : 0 < |P.x - Q.x| := abs_pos.mpr (sub_ne_zero.mpr hne)
      rcases coordinate_close P hP (|P.x - Q.x| / 3) (by positivity) with
        ⟨δP, hδP, hcloseP⟩
      rcases coordinate_close Q hQ (|P.x - Q.x| / 3) (by positivity) with
        ⟨δQ, hδQ, hcloseQ⟩
      let h := min δP δQ / 2
      have hmin : 0 < min δP δQ := lt_min hδP hδQ
      have hh : 0 < h := by
        dsimp only [h]
        linarith
      have hhpos : 0 < |h| := abs_pos.mpr (ne_of_gt hh)
      have hhmin : |h| < min δP δQ := by
        rw [abs_of_pos hh]
        dsimp only [h]
        linarith
      have hhP : |h| < δP :=
        lt_of_lt_of_le hhmin (min_le_left δP δQ)
      have hhQ : |h| < δQ :=
        lt_of_lt_of_le hhmin (min_le_right δP δQ)
      have hPx := (hcloseP h hhpos hhP).1
      have hQx := (hcloseQ h hhpos hhQ).1
      rw [abs_sub_comm] at hPx
      have htriangle : |P.x - Q.x| ≤
          |P.x - (neighboringIntersectionPoint S.rayFamily S.angle h).x| +
            |(neighboringIntersectionPoint S.rayFamily S.angle h).x - Q.x| := by
        calc
          |P.x - Q.x| =
              |(P.x - (neighboringIntersectionPoint S.rayFamily S.angle h).x) +
                ((neighboringIntersectionPoint S.rayFamily S.angle h).x - Q.x)| := by
                  congr 1
                  ring
          _ ≤ |P.x - (neighboringIntersectionPoint S.rayFamily S.angle h).x| +
                |(neighboringIntersectionPoint S.rayFamily S.angle h).x - Q.x| :=
              abs_add_le _ _
      linarith
    · by_contra hne
      have ha : 0 < |P.y - Q.y| := abs_pos.mpr (sub_ne_zero.mpr hne)
      rcases coordinate_close P hP (|P.y - Q.y| / 3) (by positivity) with
        ⟨δP, hδP, hcloseP⟩
      rcases coordinate_close Q hQ (|P.y - Q.y| / 3) (by positivity) with
        ⟨δQ, hδQ, hcloseQ⟩
      let h := min δP δQ / 2
      have hmin : 0 < min δP δQ := lt_min hδP hδQ
      have hh : 0 < h := by
        dsimp only [h]
        linarith
      have hhpos : 0 < |h| := abs_pos.mpr (ne_of_gt hh)
      have hhmin : |h| < min δP δQ := by
        rw [abs_of_pos hh]
        dsimp only [h]
        linarith
      have hhP : |h| < δP :=
        lt_of_lt_of_le hhmin (min_le_left δP δQ)
      have hhQ : |h| < δQ :=
        lt_of_lt_of_le hhmin (min_le_right δP δQ)
      have hPy := (hcloseP h hhpos hhP).2
      have hQy := (hcloseQ h hhpos hhQ).2
      rw [abs_sub_comm] at hPy
      have htriangle : |P.y - Q.y| ≤
          |P.y - (neighboringIntersectionPoint S.rayFamily S.angle h).y| +
            |(neighboringIntersectionPoint S.rayFamily S.angle h).y - Q.y| := by
        calc
          |P.y - Q.y| =
              |(P.y - (neighboringIntersectionPoint S.rayFamily S.angle h).y) +
                ((neighboringIntersectionPoint S.rayFamily S.angle h).y - Q.y)| := by
                  congr 1
                  ring
          _ ≤ |P.y - (neighboringIntersectionPoint S.rayFamily S.angle h).y| +
                |(neighboringIntersectionPoint S.rayFamily S.angle h).y - Q.y| :=
              abs_add_le _ _
      linarith
  rcases limitingCaustic_coefficients S.rayFamily S.angle S.coefficients
      S.coefficientDerivatives hS.rayFamily_differentiable
      hS.angle_mem_domain hS.coefficients_describe_reflected_lines
      hS.has_coefficient_derivatives hS.slope_derivative_nonzero with
    ⟨Ccoeff, hCcoeff, _hCcoeff_unique⟩
  have hCcoeff_eq : Ccoeff =
      differentialCausticPoint S.rayFamily S.angle
        S.rayDerivatives hS.turning_nonzero :=
    limiting_unique Ccoeff
      (differentialCausticPoint S.rayFamily S.angle
        S.rayDerivatives hS.turning_nonzero) hCcoeff.1 hForward.1
  refine ⟨hForward, ?_, ?_⟩
  · rcases hForward.2.2 with ⟨δ, hδ, hnear⟩
    refine ⟨δ, hδ, ?_⟩
    intro h hhpos hhsmall
    rcases hnear h hhpos hhsmall with ⟨_hdomain, hdet, hforward⟩
    exact ⟨hdet, hforward⟩
  · intro Z
    constructor
    · intro hZ
      exact (limiting_unique Z Ccoeff hZ hCcoeff.1).trans hCcoeff_eq
    · rintro rfl
      exact hForward.1

/-- Under the Figure 2g source laws, exactly one typed physical point supplies
the limiting intersection coordinates. -/
theorem requestedCoordinates_existsUnique (S : SourceData)
    (hS : SourceLaws S) :
    ∃! C : PhysicalPoint2, IsRequestedCoordinates S C := by
  have hbridge := source_caustic_bridge S hS
  dsimp only at hbridge
  let Cdiff := differentialCausticPoint S.rayFamily S.angle
    S.rayDerivatives hS.turning_nonzero
  let Cphys := physicalPointFromKernel S.unitChoice Cdiff
  refine ⟨Cphys, ?_, ?_⟩
  · unfold IsRequestedCoordinates
    dsimp only [Cphys]
    rw [(physicalPointCoordinateInSI_faithful S.unitChoice).2.2]
    exact hbridge.1
  · intro Z hZ
    apply (physicalPointCoordinateInSI_faithful S.unitChoice).1
    change IsForwardLimitingCausticPoint S.rayFamily S.angle
      (physicalPointCoordinateInSI S.unitChoice Z) at hZ
    have hZeq : physicalPointCoordinateInSI S.unitChoice Z = Cdiff :=
      (hbridge.2.2 (physicalPointCoordinateInSI S.unitChoice Z)).mp hZ.1
    dsimp only [Cphys]
    rw [(physicalPointCoordinateInSI_faithful S.unitChoice).2.2]
    exact hZeq

end Ipho2026Gpt56solBlind.ProblemIPhO2026_2_C_3
