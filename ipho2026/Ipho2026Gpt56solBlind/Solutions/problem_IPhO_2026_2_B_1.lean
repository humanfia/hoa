import Ipho2026Gpt56solBlind.Shared.ConcentratorOptics
import Mathlib
import Physlib

/-!
# IPhO 2026, Problem 2, part B.1

Answer-blind formalization of the transverse Figure 2f optics.  Scalar
coordinates are measured in one fixed common length unit.  The shared
concentrator kernel supplies ordered first-system contact, the directly
absorbed incoming branch, accepted specular reflection, and the global
one-reflection regime.

The valid-configuration predicate deliberately contains maximality but not
limiting tangency or the displayed coefficient relation.  Tangency is a
derived bridge, and the requested coefficients occur only as existentially
quantified output data.
-/

namespace Ipho2026Gpt56solBlind
namespace ProblemIPhO2026_2_B_1

noncomputable section

/-! ## Coordinate quantities -/

/-- A physical length represented by its coordinate in one fixed common unit. -/
@[ext]
structure Length where
  value : ℝ

namespace Length

/-- Positivity appropriate to a nondegenerate physical radius. -/
def IsPositive (length : Length) : Prop := 0 < length.value

end Length

/-- An angle represented by its radian measure. -/
@[ext]
structure Angle where
  radians : ℝ

/-- A point in the transverse plane; both coordinates have the common length unit. -/
@[ext]
structure Point2 where
  x : ℝ
  y : ℝ

/-- A transverse displacement in the common length unit. -/
@[ext]
structure Displacement2 where
  x : ℝ
  y : ℝ

/-- A dimensionless transverse direction. -/
@[ext]
structure Direction2 where
  x : ℝ
  y : ℝ

/-- The displacement `point - origin`. -/
def displacement (point origin : Point2) : Displacement2 :=
  ⟨point.x - origin.x, point.y - origin.y⟩

/-- Squared Euclidean length of a displacement. -/
def displacementNormSq (v : Displacement2) : ℝ := v.x ^ 2 + v.y ^ 2

/-- Euclidean scalar product of a displacement and a direction. -/
def displacementDotDirection (v : Displacement2) (d : Direction2) : ℝ :=
  v.x * d.x + v.y * d.y

/-- Oriented determinant of a displacement and a direction. -/
def displacementDetDirection (v : Displacement2) (d : Direction2) : ℝ :=
  v.x * d.y - v.y * d.x

/-- Euclidean scalar product of two directions. -/
def directionDot (u v : Direction2) : ℝ := u.x * v.x + u.y * v.y

/-- Squared Euclidean norm of a direction. -/
def directionNormSq (v : Direction2) : ℝ := directionDot v v

/-- A direction is unit when its squared norm is one. -/
def IsUnitDirection (v : Direction2) : Prop := directionNormSq v = 1

/-- Scalar multiplication of a direction. -/
def scaleDirection (c : ℝ) (v : Direction2) : Direction2 :=
  ⟨c * v.x, c * v.y⟩

/-- Componentwise subtraction of directions. -/
def subtractDirection (u v : Direction2) : Direction2 :=
  ⟨u.x - v.x, u.y - v.y⟩

/-- Point at signed path coordinate `s` on a straight ray. -/
def rayPoint (origin : Point2) (v : Direction2) (s : ℝ) : Point2 :=
  ⟨origin.x + s * v.x, origin.y + s * v.y⟩

/-- Embed a local coordinate point into the shared scalar optics kernel. -/
def toSharedPoint (point : Point2) : Shared.GeometricOptics.Point2 :=
  ⟨point.x, point.y⟩

/-- Embed a local dimensionless direction into the shared optics kernel. -/
def toSharedDirection (direction : Direction2) : Shared.GeometricOptics.Direction2 :=
  ⟨direction.x, direction.y⟩

/-! ## Figure 2f geometry -/

/-- Mirror centre in the Figure 2f coordinate convention. -/
def mirrorCenter : Point2 := ⟨0, 0⟩

/-- Absorber centre, displaced toward the bottom of the lower semicircle. -/
def containerCenter (R : Length) : Point2 := ⟨0, -(R.value / 2)⟩

/-- Uniform sunlight propagates down the optical axis. -/
def sunlightDirection : Direction2 := ⟨0, -1⟩

/-- Parameterized point on the lower circular mirror. -/
def mirrorPoint (R : Length) (theta : Angle) : Point2 :=
  ⟨R.value * Real.sin theta.radians, -R.value * Real.cos theta.radians⟩

/-- Outward radial normal at the parameterized mirror point. -/
def mirrorNormal (theta : Angle) : Direction2 :=
  ⟨Real.sin theta.radians, -Real.cos theta.radians⟩

/-- Membership in the lower, mirror-rim-owned semicircular boundary. -/
def OnMirror (R : Length) (point : Point2) : Prop :=
  displacementNormSq (displacement point mirrorCenter) = R.value ^ 2 ∧
    point.y ≤ 0

/-- Membership in the absorbing container circle. -/
def OnContainerBoundary (R a : Length) (point : Point2) : Prop :=
  displacementNormSq (displacement point (containerCenter R)) = a.value ^ 2

/-- Membership in the closed absorbing container disk. -/
def InContainer (R a : Length) (point : Point2) : Prop :=
  displacementNormSq (displacement point (containerCenter R)) ≤ a.value ^ 2

/-- The shared concentrator geometry has exactly the Figure 2f scalar data. -/
def Figure2fSharedGeometry
    (G : Shared.GeometricOptics.ConcentratorGeometry) (R a : Length) : Prop :=
  G.mirror.center = toSharedPoint mirrorCenter ∧
    G.mirror.radius = R.value ∧
    G.absorberRadius = a.value

/-- Shared specialization exists uniquely exactly in the physical radius domain. -/
theorem figure2fSharedGeometry_existsUnique (R a : Length) :
    (∃! G : Shared.GeometricOptics.ConcentratorGeometry,
      Figure2fSharedGeometry G R a) ↔
      R.IsPositive ∧ a.IsPositive ∧ a.value < R.value / 2 := by
  have point_ext (P Q : Shared.GeometricOptics.Point2)
      (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q := by
    cases P
    cases Q
    simp_all
  have circle_ext (c₁ c₂ : Shared.GeometricOptics.Circle)
      (hc : c₁.center = c₂.center) (hr : c₁.radius = c₂.radius) : c₁ = c₂ := by
    cases c₁
    cases c₂
    cases hc
    cases hr
    rfl
  have geometry_ext (G₁ G₂ : Shared.GeometricOptics.ConcentratorGeometry)
      (hm : G₁.mirror = G₂.mirror)
      (ha : G₁.absorberRadius = G₂.absorberRadius) : G₁ = G₂ := by
    cases G₁
    cases G₂
    cases hm
    cases ha
    rfl
  constructor
  · rintro ⟨G, hG, _hunique⟩
    rcases hG with ⟨hcenter, hradius, habsorber⟩
    refine ⟨?_, ?_, ?_⟩
    · change 0 < R.value
      rw [← hradius]
      exact G.mirror.radius_pos
    · change 0 < a.value
      rw [← habsorber]
      exact G.absorberRadius_pos
    · rw [← habsorber, ← hradius]
      exact G.absorberRadius_lt_half
  · rintro ⟨hR, ha, hlt⟩
    let mirror : Shared.GeometricOptics.Circle :=
      { center := toSharedPoint mirrorCenter
        radius := R.value
        radius_pos := hR }
    let G : Shared.GeometricOptics.ConcentratorGeometry :=
      { mirror := mirror
        absorberRadius := a.value
        absorberRadius_pos := ha
        absorberRadius_lt_half := hlt }
    refine ⟨G, ?_, ?_⟩
    · exact ⟨rfl, rfl, rfl⟩
    · intro G' hG'
      apply geometry_ext
      · apply circle_ext
        · exact hG'.1.trans rfl
        · exact hG'.2.1.trans rfl
      · exact hG'.2.2.trans rfl

/-- Coordinate boundaries agree with the corresponding shared boundary pieces. -/
theorem figure2fSharedBoundaryBridge
    (G : Shared.GeometricOptics.ConcentratorGeometry) (R a : Length)
    (hG : Figure2fSharedGeometry G R a) :
    G.absorber.center = toSharedPoint (containerCenter R) ∧
      ∀ point : Point2,
        (Shared.GeometricOptics.OnCircle G.absorber (toSharedPoint point) ↔
            OnContainerBoundary R a point) ∧
          (Shared.GeometricOptics.InClosedDisk G.absorber (toSharedPoint point) ↔
            InContainer R a point) ∧
          (Shared.GeometricOptics.OnReflectingArc G.lowerMirror
              (toSharedPoint point) ↔ OnMirror R point) := by
  rcases hG with ⟨hcenter, hradius, habsorber⟩
  have hcx : G.mirror.center.x = 0 := by
    exact congrArg Shared.GeometricOptics.Point2.x hcenter
  have hcy : G.mirror.center.y = 0 := by
    exact congrArg Shared.GeometricOptics.Point2.y hcenter
  constructor
  · have hy : G.mirror.center.y - G.mirror.radius / 2 = -(R.value / 2) := by
      rw [hcy, hradius]
      ring
    change
      Shared.GeometricOptics.Point2.mk G.mirror.center.x
          (G.mirror.center.y - G.mirror.radius / 2) =
        Shared.GeometricOptics.Point2.mk 0 (-(R.value / 2))
    have hp :
        (G.mirror.center.x, G.mirror.center.y - G.mirror.radius / 2) =
          (0, -(R.value / 2)) := by
      apply Prod.ext
      · exact hcx
      · exact hy
    exact congrArg
      (fun p : ℝ × ℝ => Shared.GeometricOptics.Point2.mk p.1 p.2)
      hp
  · intro point
    constructor
    · change
        ((point.x - G.mirror.center.x) ^ 2 +
              (point.y - (G.mirror.center.y - G.mirror.radius / 2)) ^ 2 =
            G.absorberRadius ^ 2 ↔
          (point.x - 0) ^ 2 + (point.y - (-(R.value / 2))) ^ 2 =
            a.value ^ 2)
      rw [hcx, hcy, hradius, habsorber]
      ring_nf
    constructor
    · change
        ((point.x - G.mirror.center.x) ^ 2 +
              (point.y - (G.mirror.center.y - G.mirror.radius / 2)) ^ 2 ≤
            G.absorberRadius ^ 2 ↔
          (point.x - 0) ^ 2 + (point.y - (-(R.value / 2))) ^ 2 ≤
            a.value ^ 2)
      rw [hcx, hcy, hradius, habsorber]
      ring_nf
    · change
        ((point.x - G.mirror.center.x) ^ 2 +
              (point.y - G.mirror.center.y) ^ 2 = G.mirror.radius ^ 2 ∧
            -1 * (point.y - G.mirror.center.y) ≥ 0) ↔
          ((point.x - 0) ^ 2 + (point.y - 0) ^ 2 = R.value ^ 2 ∧
            point.y ≤ 0)
      rw [hcx, hcy, hradius]
      constructor <;> rintro ⟨hcircle, hside⟩ <;>
        exact ⟨hcircle, by linarith only [hside]⟩

/-- The shared incoming family is the uniform downward coordinate-ray family. -/
theorem figure2fIncomingSunlightRay
    (G : Shared.GeometricOptics.ConcentratorGeometry) (R a : Length)
    (hG : Figure2fSharedGeometry G R a) :
    (∀ x u : ℝ,
      (Shared.GeometricOptics.incomingSunlightRay G x).pointAt u =
        toSharedPoint (rayPoint ⟨x, 0⟩ sunlightDirection u)) ∧
      ∀ t : ℝ, |t| < Real.pi / 2 →
        0 < R.value * Real.cos t ∧
          (Shared.GeometricOptics.incomingSunlightRay G
              (R.value * Real.sin t)).pointAt (R.value * Real.cos t) =
            toSharedPoint (mirrorPoint R ⟨t⟩) := by
  rcases hG with ⟨hcenter, hradius, _habsorber⟩
  have hcy : G.mirror.center.y = 0 := by
    exact congrArg Shared.GeometricOptics.Point2.y hcenter
  have hR : 0 < R.value := by
    rw [← hradius]
    exact G.mirror.radius_pos
  constructor
  · intro x u
    change
      Shared.GeometricOptics.Point2.mk (x + u * 0)
          (G.mirror.center.y + u * (-1)) =
        Shared.GeometricOptics.Point2.mk (x + u * 0) (0 + u * (-1))
    rw [hcy]
  · intro t ht
    have hcos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo (abs_lt.mp ht)
    constructor
    · exact mul_pos hR hcos
    · change
        Shared.GeometricOptics.Point2.mk
            (R.value * Real.sin t + R.value * Real.cos t * 0)
            (G.mirror.center.y + R.value * Real.cos t * (-1)) =
          Shared.GeometricOptics.Point2.mk (R.value * Real.sin t)
            (-R.value * Real.cos t)
      rw [hcy]
      have hp :
          (R.value * Real.sin t + R.value * Real.cos t * 0,
              0 + R.value * Real.cos t * (-1)) =
            (R.value * Real.sin t, -R.value * Real.cos t) := by
        apply Prod.ext <;> ring
      exact congrArg
        (fun p : ℝ × ℝ => Shared.GeometricOptics.Point2.mk p.1 p.2) hp

/-! ## Reflection and ordered contacts -/

/-- Vector form of the law of specular reflection. -/
def IsSpecularReflection
    (incoming normal outgoing : Direction2) : Prop :=
  IsUnitDirection incoming ∧
    IsUnitDirection normal ∧
    IsUnitDirection outgoing ∧
    outgoing = subtractDirection incoming
      (scaleDirection (2 * directionDot incoming normal) normal)

/-- Signed non-rim incidence domain. -/
def InSignedIncidenceDomain (theta : Angle) : Prop :=
  |theta.radians| < Real.pi / 2

/-- Positive nondegenerate domain for the requested largest incidence angle. -/
def InMaximumAngleDomain (thetaMax : Angle) : Prop :=
  0 < thetaMax.radians ∧ thetaMax.radians < Real.pi / 2

/-- Coordinate incidence data and the specular law at a mirror point. -/
def IsReflectedAtMirror
    (R : Length) (theta : Angle) (outgoing : Direction2) : Prop :=
  InSignedIncidenceDomain theta ∧
    OnMirror R (mirrorPoint R theta) ∧
    directionDot sunlightDirection (mirrorNormal theta) =
      Real.cos theta.radians ∧
    IsSpecularReflection sunlightDirection (mirrorNormal theta) outgoing

/-- Positive first contact with the closed absorbing container. -/
def IsFirstContainerContact
    (R a : Length) (origin : Point2) (direction : Direction2) (s : ℝ) : Prop :=
  0 < s ∧
    OnContainerBoundary R a (rayPoint origin direction s) ∧
    ∀ u : ℝ, 0 ≤ u → u < s →
      ¬ InContainer R a (rayPoint origin direction u)

/-- First container contact whose radius is perpendicular to the ray. -/
def IsTangentContainerContact
    (R a : Length) (origin : Point2) (direction : Direction2) (s : ℝ) : Prop :=
  IsFirstContainerContact R a origin direction s ∧
    displacementDotDirection
      (displacement (rayPoint origin direction s) (containerCenter R))
      direction = 0

/-- No second lower-mirror contact before the stated absorption parameter. -/
def HasNoSecondMirrorContact
    (R : Length) (origin : Point2) (direction : Direction2) (sHit : ℝ) : Prop :=
  ∀ u : ℝ, 0 < u → u ≤ sHit →
    ¬ OnMirror R (rayPoint origin direction u)

/-- The incoming shared ray reaches the parameterized mirror point first. -/
def IncomingRayFirstMeetsMirror
    (G : Shared.GeometricOptics.ConcentratorGeometry) (t : ℝ) : Prop :=
  Shared.GeometricOptics.InAxialIncidenceDomain t ∧
    let P := (Shared.GeometricOptics.semicirclePoint G.mirror .lower t).1
    ∃ sMirror : ℝ,
      Shared.GeometricOptics.IsFirstConcentratorContact G
          (Shared.GeometricOptics.incomingSunlightRay G P.x) sMirror P ∧
        Shared.GeometricOptics.OnReflectingArc G.lowerMirror P

/-- The incoming coordinate associated with `t` is directly absorbed. -/
def DirectIncomingAbsorption
    (G : Shared.GeometricOptics.ConcentratorGeometry) (t : ℝ) : Prop :=
  let P := (Shared.GeometricOptics.semicirclePoint G.mirror .lower t).1
  Shared.GeometricOptics.IsDirectlyAbsorbed G P.x

/-- Exact, disjoint partition of incoming mirror-first and direct absorption. -/
theorem incomingContactPartition
    (G : Shared.GeometricOptics.ConcentratorGeometry) (R a : Length) (t : ℝ)
    (hG : Figure2fSharedGeometry G R a)
    (ht : |t| < Real.pi / 2) :
    (IncomingRayFirstMeetsMirror G t ↔
        a.value < R.value * Real.sin |t|) ∧
      (DirectIncomingAbsorption G t ↔
        R.value * Real.sin |t| ≤ a.value) ∧
      (IncomingRayFirstMeetsMirror G t ∨ DirectIncomingAbsorption G t) ∧
      ¬ (IncomingRayFirstMeetsMirror G t ∧ DirectIncomingAbsorption G t) := by
  rcases hG with ⟨hcenter, hradius, habsorber⟩
  have hcx : G.mirror.center.x = 0 := by
    exact congrArg Shared.GeometricOptics.Point2.x hcenter
  have hcy : G.mirror.center.y = 0 := by
    exact congrArg Shared.GeometricOptics.Point2.y hcenter
  have hR : 0 < R.value := by
    rw [← hradius]
    exact G.mirror.radius_pos
  have ha : 0 < a.value := by
    rw [← habsorber]
    exact G.absorberRadius_pos
  have haLt : a.value < R.value / 2 := by
    rw [← habsorber, ← hradius]
    exact G.absorberRadius_lt_half
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp ht)
  have hsinAbsNonneg : 0 ≤ Real.sin |t| := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact abs_nonneg t
    · have hpi : 0 < Real.pi := Real.pi_pos
      linarith only [ht, hpi]
  have hsinAbsSq : Real.sin |t| ^ 2 = Real.sin t ^ 2 := by
    rcases le_total 0 t with htNonneg | htNonpos
    · rw [abs_of_nonneg htNonneg]
    · rw [abs_of_nonpos htNonpos, Real.sin_neg]
      ring
  have htrig : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq t
  have hcircleEq :
      (R.value * Real.sin t) ^ 2 + (R.value * Real.cos t) ^ 2 =
        R.value ^ 2 := by
    calc
      (R.value * Real.sin t) ^ 2 + (R.value * Real.cos t) ^ 2 =
          R.value ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
      _ = R.value ^ 2 := by rw [htrig, mul_one]
  have hxSq :
      (R.value * Real.sin t) ^ 2 =
        (R.value * Real.sin |t|) ^ 2 := by
    calc
      (R.value * Real.sin t) ^ 2 =
          R.value ^ 2 * Real.sin t ^ 2 := by ring
      _ = R.value ^ 2 * Real.sin |t| ^ 2 := by rw [← hsinAbsSq]
      _ = (R.value * Real.sin |t|) ^ 2 := by ring
  have sharedPointExt (Q₁ Q₂ : Shared.GeometricOptics.Point2)
      (hx : Q₁.x = Q₂.x) (hy : Q₁.y = Q₂.y) : Q₁ = Q₂ := by
    cases Q₁
    cases Q₂
    simp_all
  let P := (Shared.GeometricOptics.semicirclePoint G.mirror .lower t).1
  let ray := Shared.GeometricOptics.incomingSunlightRay G P.x
  have hPx : P.x = R.value * Real.sin t := by
    simp [P, Shared.GeometricOptics.semicirclePoint, hcx, hradius]
  have hPy : P.y = -R.value * Real.cos t := by
    simp [P, Shared.GeometricOptics.semicirclePoint,
      Shared.GeometricOptics.orientationSign, hcy, hradius]
  have hrayPoint (u : ℝ) :
      ray.pointAt u =
        ({ x := R.value * Real.sin t, y := -u } :
          Shared.GeometricOptics.Point2) := by
    congr 1 <;>
      simp [ray, Shared.GeometricOptics.incomingSunlightRay,
        Shared.GeometricOptics.ForwardRay.pointAt,
        Shared.GeometricOptics.translate,
        Shared.GeometricOptics.directionDisplacement,
        Shared.GeometricOptics.axisDirection,
        Shared.GeometricOptics.orientationSign, hPx, hcy]
  have hParc : Shared.GeometricOptics.OnReflectingArc G.lowerMirror P := by
    exact (Shared.GeometricOptics.semicirclePoint_invariants
      G.mirror .lower .mirror t ht).1
  have firstContactUnique
      {s₁ s₂ : ℝ} {Q₁ Q₂ : Shared.GeometricOptics.Point2}
      (h₁ : Shared.GeometricOptics.IsFirstConcentratorContact G ray s₁ Q₁)
      (h₂ : Shared.GeometricOptics.IsFirstConcentratorContact G ray s₂ Q₂) :
      s₁ = s₂ ∧ Q₁ = Q₂ := by
    apply Shared.GeometricOptics.firstForwardBoundaryContact_unique
    · intro Q hfree hboundary
      exact Shared.GeometricOptics.concentratorRegion_disjoint_boundary G Q
        ⟨hfree, hboundary⟩
    · exact h₁
    · exact h₂
  have mirrorContact
      (hshadow : a.value < R.value * Real.sin |t|) :
      ∃ sMirror : ℝ,
        Shared.GeometricOptics.IsFirstConcentratorContact G ray sMirror P ∧
          Shared.GeometricOptics.OnReflectingArc G.lowerMirror P := by
    let sMirror := R.value * Real.cos t
    have hsMirror : 0 < sMirror := mul_pos hR hcos
    refine ⟨sMirror, ?_, hParc⟩
    refine ⟨hsMirror, ?_, Or.inl hParc, ?_⟩
    · rw [hrayPoint]
      apply sharedPointExt
      · exact hPx
      · dsimp [sMirror]
        calc
          P.y = -R.value * Real.cos t := hPy
          _ = -(R.value * Real.cos t) := by ring
    · intro u huPos huLt
      rw [hrayPoint]
      constructor
      · constructor
        · simp [Shared.GeometricOptics.ConcentratorGeometry.lowerMirror,
            Shared.GeometricOptics.orientationSign, hcy]
          exact huPos
        · have huSq : u ^ 2 < sMirror ^ 2 :=
            (sq_lt_sq₀ huPos.le hsMirror.le).2 huLt
          simp [Shared.GeometricOptics.ConcentratorGeometry.lowerMirror,
            Shared.GeometricOptics.displacementNormSq,
            Shared.GeometricOptics.displacement, hcx, hcy, hradius]
          dsimp [sMirror] at huSq
          nlinarith only [hcircleEq, huSq]
      · intro hin
        have hshadowNonneg : 0 ≤ R.value * Real.sin |t| :=
          mul_nonneg hR.le hsinAbsNonneg
        have hshadowSq :
            a.value ^ 2 < (R.value * Real.sin |t|) ^ 2 :=
          (sq_lt_sq₀ ha.le hshadowNonneg).2 hshadow
        change
          (R.value * Real.sin t - G.mirror.center.x) ^ 2 +
              (-u - (G.mirror.center.y - G.mirror.radius / 2)) ^ 2 ≤
            G.absorberRadius ^ 2 at hin
        rw [hcx, hcy, hradius, habsorber] at hin
        nlinarith only [hin, hshadowSq, hxSq,
          sq_nonneg (-u - (-(R.value / 2)))]
  have directContact
      (hshadow : R.value * Real.sin |t| ≤ a.value) :
      ∃ sDirect : ℝ, ∃ QDirect : Shared.GeometricOptics.Point2,
        Shared.GeometricOptics.IsFirstConcentratorContact G ray sDirect QDirect ∧
          Shared.GeometricOptics.OnCircle G.absorber QDirect ∧
          sDirect < R.value * Real.cos t := by
    have hshadowNonneg : 0 ≤ R.value * Real.sin |t| :=
      mul_nonneg hR.le hsinAbsNonneg
    have hshadowSq :
        (R.value * Real.sin |t|) ^ 2 ≤ a.value ^ 2 :=
      (sq_le_sq₀ hshadowNonneg ha.le).2 hshadow
    let D := a.value ^ 2 - (R.value * Real.sin t) ^ 2
    have hD : 0 ≤ D := by
      dsimp [D]
      nlinarith only [hshadowSq, hxSq]
    let q := Real.sqrt D
    have hqNonneg : 0 ≤ q := Real.sqrt_nonneg D
    have hqSq : q ^ 2 = D := Real.sq_sqrt hD
    have hqLe : q ≤ a.value := by
      apply (Real.sqrt_le_iff).2
      exact ⟨ha.le, by
        dsimp [D]
        nlinarith only [sq_nonneg (R.value * Real.sin t)]⟩
    let sDirect := R.value / 2 - q
    have hsDirect : 0 < sDirect := by
      dsimp [sDirect]
      linarith only [hqLe, haLt]
    have haHalfSq : a.value ^ 2 < (R.value / 2) ^ 2 :=
      (sq_lt_sq₀ ha.le (by linarith only [hR.le] : 0 ≤ R.value / 2)).2 haLt
    have hxHalf :
        (R.value * Real.sin t) ^ 2 < (R.value / 2) ^ 2 := by
      nlinarith only [hshadowSq, hxSq, haHalfSq]
    have hmirrorHalf : R.value / 2 < R.value * Real.cos t := by
      apply (sq_lt_sq₀ (by linarith only [hR.le] : 0 ≤ R.value / 2)
        (mul_pos hR hcos).le).1
      nlinarith only [hcircleEq, hxHalf]
    have hsDirectLt : sDirect < R.value * Real.cos t := by
      dsimp [sDirect]
      linarith only [hqNonneg, hmirrorHalf]
    refine ⟨sDirect, ray.pointAt sDirect, ?_, ?_, hsDirectLt⟩
    · refine ⟨hsDirect, rfl, Or.inr ?_, ?_⟩
      · rw [hrayPoint]
        simp [Shared.GeometricOptics.OnCircle,
          Shared.GeometricOptics.ConcentratorGeometry.absorber,
          Shared.GeometricOptics.displacementNormSq,
          Shared.GeometricOptics.displacement, hcx, hcy, hradius, habsorber]
        dsimp [sDirect, q] at hqSq ⊢
        nlinarith only [hqSq, hxSq]
      · intro u huPos huLt
        rw [hrayPoint]
        have huHalf : u < R.value / 2 := by
          dsimp [sDirect] at huLt
          linarith only [huLt, hqNonneg]
        constructor
        · constructor
          · simp [Shared.GeometricOptics.ConcentratorGeometry.lowerMirror,
              Shared.GeometricOptics.orientationSign, hcy]
            exact huPos
          · have huSq : u ^ 2 < (R.value / 2) ^ 2 :=
              (sq_lt_sq₀ huPos.le
                (by linarith only [hR.le] : 0 ≤ R.value / 2)).2 huHalf
            simp [Shared.GeometricOptics.ConcentratorGeometry.lowerMirror,
              Shared.GeometricOptics.displacementNormSq,
              Shared.GeometricOptics.displacement, hcx, hcy, hradius]
            nlinarith only [huSq, hxHalf, sq_pos_of_pos hR]
        · intro hin
          have hqLt : q < R.value / 2 - u := by
            dsimp [sDirect] at huLt
            linarith only [huLt]
          have hrightNonneg : 0 ≤ R.value / 2 - u := by
            linarith only [huHalf]
          have hqSqLt : q ^ 2 < (R.value / 2 - u) ^ 2 :=
            (sq_lt_sq₀ hqNonneg hrightNonneg).2 hqLt
          change
            (R.value * Real.sin t - G.mirror.center.x) ^ 2 +
                (-u - (G.mirror.center.y - G.mirror.radius / 2)) ^ 2 ≤
              G.absorberRadius ^ 2 at hin
          rw [hcx, hcy, hradius, habsorber] at hin
          dsimp [q, D] at hqSq ⊢
          nlinarith only [hin, hqSq, hqSqLt]
    · rw [hrayPoint]
      simp [Shared.GeometricOptics.OnCircle,
        Shared.GeometricOptics.ConcentratorGeometry.absorber,
        Shared.GeometricOptics.displacementNormSq,
        Shared.GeometricOptics.displacement, hcx, hcy, hradius, habsorber]
      dsimp [sDirect, q] at hqSq ⊢
      nlinarith only [hqSq, hxSq]
  have hmirrorIff :
      IncomingRayFirstMeetsMirror G t ↔
        a.value < R.value * Real.sin |t| := by
    constructor
    · intro hincoming
      by_contra hnot
      have hle : R.value * Real.sin |t| ≤ a.value := le_of_not_gt hnot
      rcases directContact hle with ⟨sD, QD, hfirstD, _hcircleD, hsDLt⟩
      rcases hincoming with ⟨_ht, sM, hfirstM, _hmirrorM⟩
      have hsM : sM = R.value * Real.cos t := by
        have hy := congrArg Shared.GeometricOptics.Point2.y hfirstM.2.1
        rw [hrayPoint] at hy
        change P.y = -sM at hy
        rw [hPy] at hy
        linarith only [hy]
      have heq := firstContactUnique hfirstD hfirstM
      linarith only [hsDLt, hsM, heq.1]
    · intro hshadow
      refine ⟨ht, ?_⟩
      simpa [P, ray] using mirrorContact hshadow
  have hdirectIff :
      DirectIncomingAbsorption G t ↔
        R.value * Real.sin |t| ≤ a.value := by
    constructor
    · intro hdirect
      by_contra hnot
      have hlt : a.value < R.value * Real.sin |t| := lt_of_not_ge hnot
      rcases hdirect with ⟨sD, QD, hfirstD, hcircleD⟩
      have hQx : QD.x = R.value * Real.sin t := by
        rw [hfirstD.2.1, hrayPoint]
      have hcircleDirect :
          QD.x ^ 2 + (QD.y + R.value / 2) ^ 2 = a.value ^ 2 := by
        simpa [Shared.GeometricOptics.OnCircle,
          Shared.GeometricOptics.ConcentratorGeometry.absorber,
          Shared.GeometricOptics.displacementNormSq,
          Shared.GeometricOptics.displacement, hcx, hcy, hradius, habsorber]
          using hcircleD
      have hhorizontal : (R.value * Real.sin t) ^ 2 ≤ a.value ^ 2 := by
        rw [← hQx]
        nlinarith only [hcircleDirect, sq_nonneg (QD.y + R.value / 2)]
      have hshadowNonneg : 0 ≤ R.value * Real.sin |t| :=
        mul_nonneg hR.le hsinAbsNonneg
      have hstrict :
          a.value ^ 2 < (R.value * Real.sin |t|) ^ 2 :=
        (sq_lt_sq₀ ha.le hshadowNonneg).2 hlt
      rw [← hxSq] at hstrict
      linarith only [hhorizontal, hstrict]
    · intro hshadow
      rcases directContact hshadow with ⟨sD, QD, hfirstD, hcircleD, _hsDLt⟩
      exact ⟨sD, QD, by simpa [P, ray] using hfirstD, hcircleD⟩
  refine ⟨hmirrorIff, hdirectIff, ?_, ?_⟩
  · rcases lt_or_ge a.value (R.value * Real.sin |t|) with hlt | hge
    · exact Or.inl (hmirrorIff.2 hlt)
    · exact Or.inr (hdirectIff.2 hge)
  · rintro ⟨hmirror, hdirect⟩
    have hlt := hmirrorIff.1 hmirror
    have hle := hdirectIff.1 hdirect
    linarith only [hlt, hle]

/-- A physically realized, accepted once-reflected ray strikes the container. -/
def ReflectedRayStrikesContainer (R a : Length) (theta : Angle) : Prop :=
  ∃ G : Shared.GeometricOptics.ConcentratorGeometry,
    Figure2fSharedGeometry G R a ∧
      Shared.GeometricOptics.AcceptedReflectedRay G theta.radians

/-- The unique Figure 2f specialization obeys the one-reflection regime. -/
def InOneReflectionDomain (R a : Length) : Prop :=
  ∃ G : Shared.GeometricOptics.ConcentratorGeometry,
    Figure2fSharedGeometry G R a ∧
      Shared.GeometricOptics.InOneReflectionRegime G

/-- `thetaMax` is attained and bounds all accepted signed reflected parameters. -/
def IsLargestStrikingIncidenceAngle
    (R a : Length) (thetaMax : Angle) : Prop :=
  ReflectedRayStrikesContainer R a thetaMax ∧
    ∀ theta : Angle,
      ReflectedRayStrikesContainer R a theta →
        |theta.radians| ≤ thetaMax.radians

/-- The accepted limiting reflected ray has a tangent first absorber contact. -/
def IsLimitingRayTangent (R a : Length) (thetaMax : Angle) : Prop :=
  ∃ G : Shared.GeometricOptics.ConcentratorGeometry,
    Figure2fSharedGeometry G R a ∧
      Shared.GeometricOptics.AcceptedReflectedRay G thetaMax.radians ∧
      ∃ s : ℝ, ∃ Q : Shared.GeometricOptics.Point2,
        Shared.GeometricOptics.IsTangentContainerContact G
          (Shared.GeometricOptics.axialReflectedRay
            G.mirror .lower thetaMax.radians) s Q

/-- Physical Figure 2f data, excluding derived tangency and the target relation. -/
def Figure2fConfiguration (R a : Length) (thetaMax : Angle) : Prop :=
  R.IsPositive ∧
    a.IsPositive ∧
    a.value < R.value / 2 ∧
    InMaximumAngleDomain thetaMax ∧
    InOneReflectionDomain R a ∧
    IsLargestStrikingIncidenceAngle R a thetaMax

/-! ## Coefficient contract -/

/-- The two requested dimensional coefficients. -/
@[ext]
structure CoefficientPair where
  alpha : Length
  beta : Length

/-- The displayed B.1 equation, without assigning either coefficient a value. -/
def SatisfiesDisplayedRelation
    (a : Length) (thetaMax : Angle) (coefficients : CoefficientPair) : Prop :=
  a.value =
    coefficients.alpha.value * Real.sin thetaMax.radians +
      coefficients.beta.value * Real.sin (2 * thetaMax.radians)

/-- A single coefficient pair satisfies the relation throughout the fixed-`R` family. -/
def CoefficientSolution (R : Length) (coefficients : CoefficientPair) : Prop :=
  ∀ (a : Length) (thetaMax : Angle),
    Figure2fConfiguration R a thetaMax →
      SatisfiesDisplayedRelation a thetaMax coefficients

/-! ## Ray-circle data and limiting tangency -/

/-- Exact reflected coordinate direction at signed parameter `t`. -/
def reflectedDirectionAt (t : ℝ) : Direction2 :=
  ⟨-Real.sin (2 * t), Real.cos (2 * t)⟩

/-- The dimensionless perpendicular-distance factor `sin x * (1 - cos x)`. -/
def perpendicularDistanceFactor (x : ℝ) : ℝ :=
  Real.sin x * (1 - Real.cos x)

/-- Dimensionless forward-projection factor `1/2 + cos t - cos² t`. -/
def reflectedRayProjectionFactor (t : ℝ) : ℝ :=
  1 / 2 + Real.cos t - Real.cos t ^ 2

/-- Forward parameter of the perpendicular projection of the absorber centre. -/
def reflectedRayProjection (R : Length) (t : ℝ) : ℝ :=
  R.value * reflectedRayProjectionFactor t

/-- Signed perpendicular displacement of the absorber centre from the ray line. -/
def reflectedRaySignedDistance (R : Length) (t : ℝ) : ℝ :=
  R.value * Real.sin t * (Real.cos t - 1)

/-- Ray-absorber discriminant; its sign classifies miss, transverse hit, and tangency. -/
def reflectedRayDiscriminant (R a : Length) (t : ℝ) : ℝ :=
  a.value ^ 2 - reflectedRaySignedDistance R t ^ 2

/-- Smaller supporting-line/container intersection parameter. -/
def reflectedRayFirstRoot (R a : Length) (t : ℝ) : ℝ :=
  reflectedRayProjection R t - Real.sqrt (reflectedRayDiscriminant R a t)

/-- Larger supporting-line/container intersection parameter. -/
def reflectedRaySecondRoot (R a : Length) (t : ℝ) : ℝ :=
  reflectedRayProjection R t + Real.sqrt (reflectedRayDiscriminant R a t)

/-- The coordinate and shared specular laws determine the same unique direction. -/
theorem reflectedDirectionFormula
    (R : Length) (t : ℝ) (hR : R.IsPositive)
    (ht : |t| < Real.pi / 2) :
    (∀ outgoing : Direction2,
      IsReflectedAtMirror R ⟨t⟩ outgoing ↔ outgoing = reflectedDirectionAt t) ∧
      ∀ (a : Length) (G : Shared.GeometricOptics.ConcentratorGeometry),
        Figure2fSharedGeometry G R a →
          (Shared.GeometricOptics.axialReflectedRay G.mirror .lower t).origin =
              toSharedPoint (mirrorPoint R ⟨t⟩) ∧
            (Shared.GeometricOptics.axialReflectedRay G.mirror .lower t).direction.1 =
              toSharedDirection (reflectedDirectionAt t) := by
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp ht)
  have htrig : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq t
  have hsinSq : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
    linarith
  constructor
  · intro outgoing
    constructor
    · intro hout
      rcases hout with ⟨_hdomain, _hmirror, _hdot, hspecular⟩
      calc
        outgoing = subtractDirection sunlightDirection
            (scaleDirection
              (2 * directionDot sunlightDirection (mirrorNormal ⟨t⟩))
              (mirrorNormal ⟨t⟩)) := hspecular.2.2.2
        _ = reflectedDirectionAt t := by
          apply Direction2.ext
          · change
              0 - (2 * (0 * Real.sin t + (-1) * (-Real.cos t))) *
                    Real.sin t =
                -Real.sin (2 * t)
            rw [Real.sin_two_mul]
            ring
          · change
              -1 - (2 * (0 * Real.sin t + (-1) * (-Real.cos t))) *
                    (-Real.cos t) =
                Real.cos (2 * t)
            rw [Real.cos_two_mul]
            ring
    · rintro rfl
      refine ⟨ht, ?_, ?_, ?_⟩
      · constructor
        · change
            (R.value * Real.sin t - 0) ^ 2 +
                (-R.value * Real.cos t - 0) ^ 2 = R.value ^ 2
          nlinarith [mul_self_nonneg R.value]
        · change -R.value * Real.cos t ≤ 0
          nlinarith [mul_pos hR hcos]
      · change 0 * Real.sin t + (-1) * (-Real.cos t) = Real.cos t
        ring
      · refine ⟨?_, ?_, ?_, ?_⟩
        · change 0 * 0 + (-1) * (-1) = 1
          norm_num
        · change Real.sin t * Real.sin t + (-Real.cos t) * (-Real.cos t) = 1
          nlinarith [htrig]
        · change
            (-Real.sin (2 * t)) * (-Real.sin (2 * t)) +
                Real.cos (2 * t) * Real.cos (2 * t) = 1
          nlinarith [Real.sin_sq_add_cos_sq (2 * t)]
        · apply Direction2.ext
          · change
              -Real.sin (2 * t) =
                0 - (2 * (0 * Real.sin t + (-1) * (-Real.cos t))) *
                  Real.sin t
            rw [Real.sin_two_mul]
            ring
          · change
              Real.cos (2 * t) =
                -1 - (2 * (0 * Real.sin t + (-1) * (-Real.cos t))) *
                  (-Real.cos t)
            rw [Real.cos_two_mul]
            ring
  · intro a G hG
    rcases hG with ⟨hcenter, hradius, _habsorber⟩
    have hcx : G.mirror.center.x = 0 := by
      exact congrArg Shared.GeometricOptics.Point2.x hcenter
    have hcy : G.mirror.center.y = 0 := by
      exact congrArg Shared.GeometricOptics.Point2.y hcenter
    constructor
    · change
        Shared.GeometricOptics.Point2.mk
            (G.mirror.center.x + G.mirror.radius * Real.sin t)
            (G.mirror.center.y + (-1) * G.mirror.radius * Real.cos t) =
          Shared.GeometricOptics.Point2.mk (R.value * Real.sin t)
            (-R.value * Real.cos t)
      rw [hcx, hcy, hradius]
      have hp :
          (0 + R.value * Real.sin t,
              0 + (-1) * R.value * Real.cos t) =
            (R.value * Real.sin t, -R.value * Real.cos t) := by
        apply Prod.ext <;> ring
      exact congrArg
        (fun p : ℝ × ℝ => Shared.GeometricOptics.Point2.mk p.1 p.2) hp
    · let data := Shared.GeometricOptics.semicirclePoint G.mirror .lower t
      let normal : Shared.GeometricOptics.UnitDirection :=
        ⟨data.2, by
          change
            Real.sin t * Real.sin t +
                ((-1) * Real.cos t) * ((-1) * Real.cos t) = 1
          nlinarith [htrig]⟩
      have hraw :
          (Shared.GeometricOptics.axialReflectedRay G.mirror .lower t).direction.1 =
            Shared.GeometricOptics.reflectedDirection
              (Shared.GeometricOptics.axisDirection .lower).1 normal := by
        rfl
      rw [hraw]
      change
        Shared.GeometricOptics.Direction2.mk
            (0 - 2 * (0 * Real.sin t + (-1) * ((-1) * Real.cos t)) *
              Real.sin t)
            (-1 - 2 * (0 * Real.sin t + (-1) * ((-1) * Real.cos t)) *
              ((-1) * Real.cos t)) =
          Shared.GeometricOptics.Direction2.mk (-Real.sin (2 * t))
            (Real.cos (2 * t))
      have hp :
          (0 - 2 * (0 * Real.sin t + (-1) * ((-1) * Real.cos t)) *
                Real.sin t,
              -1 - 2 * (0 * Real.sin t + (-1) * ((-1) * Real.cos t)) *
                ((-1) * Real.cos t)) =
            (-Real.sin (2 * t), Real.cos (2 * t)) := by
        apply Prod.ext
        · rw [Real.sin_two_mul]
          ring
        · rw [Real.cos_two_mul]
          ring
      exact congrArg
        (fun p : ℝ × ℝ => Shared.GeometricOptics.Direction2.mk p.1 p.2) hp

/-- Exact container and mirror quadratics, with their supporting-line roots. -/
theorem reflectedRayCircleQuadratics
    (R : Length) (t : ℝ) (hR : R.IsPositive)
    (ht : |t| < Real.pi / 2) :
    (∀ s : ℝ,
      displacementNormSq
          (displacement
            (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s)
            (containerCenter R)) =
          (s - reflectedRayProjection R t) ^ 2 +
            R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2 ∧
        displacementNormSq
            (displacement
              (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s)
              mirrorCenter) - R.value ^ 2 =
          s * (s - 2 * R.value * Real.cos t)) ∧
      (∀ A : Length,
        0 ≤ A.value ^ 2 -
            R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2 →
          ∀ s : ℝ,
            OnContainerBoundary R A
                (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s) ↔
              s = reflectedRayProjection R t -
                  Real.sqrt (A.value ^ 2 -
                    R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2) ∨
                s = reflectedRayProjection R t +
                  Real.sqrt (A.value ^ 2 -
                    R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2)) ∧
      ∀ s : ℝ,
        displacementNormSq
            (displacement
              (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s)
              mirrorCenter) = R.value ^ 2 ↔
          s = 0 ∨ s = 2 * R.value * Real.cos t := by
  have htrig : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq t
  have hsinSq : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
    linarith
  have habsFactor :
      perpendicularDistanceFactor |t| ^ 2 =
        (Real.sin t * (1 - Real.cos t)) ^ 2 := by
    rcases le_total 0 t with htNonneg | htNonpos
    · rw [abs_of_nonneg htNonneg]
      rfl
    · rw [abs_of_nonpos htNonpos]
      change
        (Real.sin (-t) * (1 - Real.cos (-t))) ^ 2 =
          (Real.sin t * (1 - Real.cos t)) ^ 2
      rw [Real.sin_neg, Real.cos_neg]
      ring
  have hquadratics : ∀ s : ℝ,
      displacementNormSq
          (displacement
            (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s)
            (containerCenter R)) =
          (s - reflectedRayProjection R t) ^ 2 +
            R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2 ∧
        displacementNormSq
            (displacement
              (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s)
              mirrorCenter) - R.value ^ 2 =
          s * (s - 2 * R.value * Real.cos t) := by
    intro s
    constructor
    · rw [habsFactor]
      change
        (R.value * Real.sin t + s * (-Real.sin (2 * t)) - 0) ^ 2 +
            (-R.value * Real.cos t + s * Real.cos (2 * t) -
              (-(R.value / 2))) ^ 2 =
          (s - R.value * (1 / 2 + Real.cos t - Real.cos t ^ 2)) ^ 2 +
            R.value ^ 2 * (Real.sin t * (1 - Real.cos t)) ^ 2
      rw [Real.sin_two_mul, Real.cos_two_mul]
      ring_nf
      rw [hsinSq]
      ring
    · change
        (R.value * Real.sin t + s * (-Real.sin (2 * t)) - 0) ^ 2 +
              (-R.value * Real.cos t + s * Real.cos (2 * t) - 0) ^ 2 -
            R.value ^ 2 =
          s * (s - 2 * R.value * Real.cos t)
      rw [Real.sin_two_mul, Real.cos_two_mul]
      ring_nf
      rw [hsinSq]
      ring
  refine ⟨hquadratics, ?_, ?_⟩
  · intro A hD s
    change
      displacementNormSq
          (displacement
            (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s)
            (containerCenter R)) = A.value ^ 2 ↔ _
    rw [(hquadratics s).1]
    let D := A.value ^ 2 -
      R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2
    have hsqrt : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD
    constructor
    · intro hs
      have hsquare :
          (s - reflectedRayProjection R t) ^ 2 = (Real.sqrt D) ^ 2 := by
        dsimp [D] at hsqrt ⊢
        nlinarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hplus | hminus
      · right
        dsimp [D] at hplus ⊢
        linarith
      · left
        dsimp [D] at hminus ⊢
        linarith
    · rintro (hs | hs)
      · dsimp [D] at hsqrt ⊢
        rw [hs]
        nlinarith
      · dsimp [D] at hsqrt ⊢
        rw [hs]
        nlinarith
  · intro s
    constructor
    · intro hs
      have hzero : s * (s - 2 * R.value * Real.cos t) = 0 := by
        rw [← (hquadratics s).2, hs]
        ring
      rcases mul_eq_zero.mp hzero with hs0 | hs0
      · exact Or.inl hs0
      · exact Or.inr (sub_eq_zero.mp hs0)
    · intro hs
      have hzero : s * (s - 2 * R.value * Real.cos t) = 0 := by
        rcases hs with rfl | rfl <;> ring
      rw [← (hquadratics s).2] at hzero
      linarith

/-- Complete discriminant classification in the shared ordered-contact model. -/
theorem reflectedRayDiscriminantCriterion
    (G : Shared.GeometricOptics.ConcentratorGeometry) (R a : Length) (t : ℝ)
    (hG : Figure2fSharedGeometry G R a)
    (ht : |t| < Real.pi / 2) :
    let ray := Shared.GeometricOptics.axialReflectedRay G.mirror .lower t
    let Δ := reflectedRayDiscriminant R a t
    let m := reflectedRayProjection R t
    let sMinus := reflectedRayFirstRoot R a t
    let sPlus := reflectedRaySecondRoot R a t
    (∀ s : ℝ,
      Shared.GeometricOptics.displacementNormSq
          (Shared.GeometricOptics.displacement G.absorber.center (ray.pointAt s)) -
          a.value ^ 2 = (s - m) ^ 2 - Δ) ∧
      (Δ < 0 ↔
        ∀ s : ℝ, ¬ Shared.GeometricOptics.OnCircle G.absorber (ray.pointAt s)) ∧
      (0 < Δ →
        (∀ s : ℝ,
          Shared.GeometricOptics.OnCircle G.absorber (ray.pointAt s) ↔
            s = sMinus ∨ s = sPlus) ∧
          (0 < sMinus →
            Shared.GeometricOptics.IsFirstContainerContact G ray sMinus
              (ray.pointAt sMinus))) ∧
      (Δ = 0 → 0 < m →
        (∀ s : ℝ,
          Shared.GeometricOptics.OnCircle G.absorber (ray.pointAt s) ↔ s = m) ∧
          Shared.GeometricOptics.IsTangentContainerContact G ray m (ray.pointAt m)) ∧
      (Shared.GeometricOptics.AcceptedReflectedRay G t →
        0 ≤ Δ ∧
          (0 < Δ →
            ∀ s : ℝ, ∀ Q : Shared.GeometricOptics.Point2,
              Shared.GeometricOptics.IsFirstContainerContact G ray s Q →
                s = sMinus)) := by
  dsimp
  have hcenter := hG.1
  have hradius := hG.2.1
  have habsorber := hG.2.2
  have hcx : G.mirror.center.x = 0 := by
    exact congrArg Shared.GeometricOptics.Point2.x hcenter
  have hcy : G.mirror.center.y = 0 := by
    exact congrArg Shared.GeometricOptics.Point2.y hcenter
  have hR : R.IsPositive := by
    change 0 < R.value
    rw [← hradius]
    exact G.mirror.radius_pos
  let ray := Shared.GeometricOptics.axialReflectedRay G.mirror .lower t
  have hrayData := (reflectedDirectionFormula R t hR ht).2 a G hG
  have hrayPoint (s : ℝ) :
      ray.pointAt s =
        toSharedPoint
          (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s) := by
    change
      Shared.GeometricOptics.translate ray.origin
          (Shared.GeometricOptics.directionDisplacement s ray.direction.1) =
        toSharedPoint
          (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s)
    rw [hrayData.1, hrayData.2]
    rfl
  have hnormBridge (s : ℝ) :
      Shared.GeometricOptics.displacementNormSq
          (Shared.GeometricOptics.displacement G.absorber.center (ray.pointAt s)) =
        displacementNormSq
          (displacement
            (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s)
            (containerCenter R)) := by
    rw [hrayPoint]
    let P := rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s
    change
      (P.x - G.mirror.center.x) ^ 2 +
          (P.y - (G.mirror.center.y - G.mirror.radius / 2)) ^ 2 =
        (P.x - 0) ^ 2 + (P.y - (-(R.value / 2))) ^ 2
    rw [hcx, hcy, hradius]
    ring
  have hcircleBridge (s : ℝ) :
      Shared.GeometricOptics.OnCircle G.absorber (ray.pointAt s) ↔
        OnContainerBoundary R a
          (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s) := by
    rw [hrayPoint]
    exact ((figure2fSharedBoundaryBridge G R a hG).2 _).1
  have hsignedSq :
      reflectedRaySignedDistance R t ^ 2 =
        R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2 := by
    rcases le_total 0 t with htNonneg | htNonpos
    · rw [abs_of_nonneg htNonneg]
      dsimp only [reflectedRaySignedDistance, perpendicularDistanceFactor]
      ring
    · rw [abs_of_nonpos htNonpos]
      change
        (R.value * Real.sin t * (Real.cos t - 1)) ^ 2 =
          R.value ^ 2 * (Real.sin (-t) * (1 - Real.cos (-t))) ^ 2
      rw [Real.sin_neg, Real.cos_neg]
      ring
  have hDelta :
      reflectedRayDiscriminant R a t =
        a.value ^ 2 - R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2 := by
    dsimp only [reflectedRayDiscriminant]
    rw [hsignedSq]
  have hfactor : ∀ s : ℝ,
      Shared.GeometricOptics.displacementNormSq
          (Shared.GeometricOptics.displacement G.absorber.center (ray.pointAt s)) -
          a.value ^ 2 =
        (s - reflectedRayProjection R t) ^ 2 -
          reflectedRayDiscriminant R a t := by
    intro s
    rw [hnormBridge, (reflectedRayCircleQuadratics R t hR ht).1 s |>.1,
      hDelta]
    ring
  have hmiss :
      reflectedRayDiscriminant R a t < 0 ↔
        ∀ s : ℝ,
          ¬ Shared.GeometricOptics.OnCircle G.absorber (ray.pointAt s) := by
    constructor
    · intro hneg s hcircle
      have hzero :
          Shared.GeometricOptics.displacementNormSq
              (Shared.GeometricOptics.displacement G.absorber.center
                (ray.pointAt s)) - a.value ^ 2 = 0 := by
        simpa [Shared.GeometricOptics.OnCircle,
          Shared.GeometricOptics.ConcentratorGeometry.absorber, habsorber] using
            sub_eq_zero.mpr hcircle
      rw [hfactor] at hzero
      nlinarith [sq_nonneg (s - reflectedRayProjection R t)]
    · intro hno
      by_contra hnot
      have hnonneg : 0 ≤ reflectedRayDiscriminant R a t := le_of_not_gt hnot
      have hroots :=
        (reflectedRayCircleQuadratics R t hR ht).2.1 a (by
          rw [← hDelta]
          exact hnonneg)
          (reflectedRayFirstRoot R a t)
      have hlocal :
          OnContainerBoundary R a
            (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t)
              (reflectedRayFirstRoot R a t)) := by
        apply hroots.2
        left
        change
          reflectedRayProjection R t -
              Real.sqrt (reflectedRayDiscriminant R a t) =
            reflectedRayProjection R t -
              Real.sqrt
                (a.value ^ 2 -
                  R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2)
        rw [hDelta]
      exact hno _ (hcircleBridge _ |>.2 hlocal)
  have htransverse : 0 < reflectedRayDiscriminant R a t →
      (∀ s : ℝ,
        Shared.GeometricOptics.OnCircle G.absorber (ray.pointAt s) ↔
          s = reflectedRayFirstRoot R a t ∨
            s = reflectedRaySecondRoot R a t) ∧
        (0 < reflectedRayFirstRoot R a t →
          Shared.GeometricOptics.IsFirstContainerContact G ray
            (reflectedRayFirstRoot R a t)
            (ray.pointAt (reflectedRayFirstRoot R a t))) := by
    intro hpos
    have hnonneg : 0 ≤ reflectedRayDiscriminant R a t := hpos.le
    have hsqrtSq :
        Real.sqrt (reflectedRayDiscriminant R a t) ^ 2 =
          reflectedRayDiscriminant R a t := Real.sq_sqrt hnonneg
    have hsqrtPos : 0 < Real.sqrt (reflectedRayDiscriminant R a t) :=
      Real.sqrt_pos.2 hpos
    constructor
    · intro s
      rw [hcircleBridge]
      have hroots :=
        (reflectedRayCircleQuadratics R t hR ht).2.1 a (by
          rw [← hDelta]
          exact hnonneg) s
      change
        OnContainerBoundary R a
              (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s) ↔
            s = reflectedRayProjection R t -
                Real.sqrt (reflectedRayDiscriminant R a t) ∨
              s = reflectedRayProjection R t +
                Real.sqrt (reflectedRayDiscriminant R a t)
      rw [hDelta]
      exact hroots
    · intro hsMinus
      refine ⟨hsMinus, rfl, ?_, ?_⟩
      · exact (by
          have hlocal :=
            ((reflectedRayCircleQuadratics R t hR ht).2.1 a
              (by rw [← hDelta]; exact hnonneg)
              (reflectedRayFirstRoot R a t)).2
              (Or.inl (by
                change
                  reflectedRayProjection R t -
                      Real.sqrt (reflectedRayDiscriminant R a t) =
                    reflectedRayProjection R t -
                      Real.sqrt
                        (a.value ^ 2 -
                          R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2)
                rw [hDelta]))
          exact hcircleBridge _ |>.2 hlocal)
      · intro u huNonneg huLt
        have hsumNeg :
            u - reflectedRayProjection R t +
                Real.sqrt (reflectedRayDiscriminant R a t) < 0 := by
          dsimp only [reflectedRayFirstRoot] at huLt
          linarith
        have hsqPos :
            0 < (u - reflectedRayProjection R t +
              Real.sqrt (reflectedRayDiscriminant R a t)) ^ 2 :=
          sq_pos_of_neg hsumNeg
        have hresidual :
            0 < (u - reflectedRayProjection R t) ^ 2 -
              reflectedRayDiscriminant R a t := by
          nlinarith
        have := hfactor u
        change
          Shared.GeometricOptics.displacementNormSq
              (Shared.GeometricOptics.displacement G.absorber.center
                (ray.pointAt u)) > G.absorberRadius ^ 2
        rw [habsorber]
        nlinarith
  have htangent : reflectedRayDiscriminant R a t = 0 →
      0 < reflectedRayProjection R t →
        (∀ s : ℝ,
          Shared.GeometricOptics.OnCircle G.absorber (ray.pointAt s) ↔
            s = reflectedRayProjection R t) ∧
          Shared.GeometricOptics.IsTangentContainerContact G ray
            (reflectedRayProjection R t)
            (ray.pointAt (reflectedRayProjection R t)) := by
    intro hzero hmPos
    have hcircleAt :
        Shared.GeometricOptics.OnCircle G.absorber
          (ray.pointAt (reflectedRayProjection R t)) := by
      have hnorm := hfactor (reflectedRayProjection R t)
      rw [hzero] at hnorm
      have heq :
          Shared.GeometricOptics.displacementNormSq
              (Shared.GeometricOptics.displacement G.absorber.center
                (ray.pointAt (reflectedRayProjection R t))) = a.value ^ 2 := by
        nlinarith
      simpa [Shared.GeometricOptics.OnCircle,
        Shared.GeometricOptics.ConcentratorGeometry.absorber, habsorber] using heq
    constructor
    · intro s
      constructor
      · intro hcircle
        have heq :
            Shared.GeometricOptics.displacementNormSq
                (Shared.GeometricOptics.displacement G.absorber.center
                  (ray.pointAt s)) - a.value ^ 2 = 0 := by
          simpa [Shared.GeometricOptics.OnCircle,
            Shared.GeometricOptics.ConcentratorGeometry.absorber, habsorber]
            using sub_eq_zero.mpr hcircle
        rw [hfactor, hzero, sub_zero] at heq
        nlinarith [sq_nonneg (s - reflectedRayProjection R t)]
      · rintro rfl
        exact hcircleAt
    · constructor
      · refine ⟨hmPos, rfl, hcircleAt, ?_⟩
        intro u huNonneg huLt
        have hsq : 0 < (u - reflectedRayProjection R t) ^ 2 :=
          sq_pos_of_neg (by linarith)
        have hresidual := hfactor u
        rw [hzero, sub_zero] at hresidual
        change
          Shared.GeometricOptics.displacementNormSq
              (Shared.GeometricOptics.displacement G.absorber.center
                (ray.pointAt u)) > G.absorberRadius ^ 2
        rw [habsorber]
        nlinarith
      · have hsinSq : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
          nlinarith [Real.sin_sq_add_cos_sq t]
        have hdirection :
            ray.direction.1 = toSharedDirection (reflectedDirectionAt t) :=
          hrayData.2
        rw [hrayPoint, hdirection]
        change
          (R.value * Real.sin t +
                  (R.value * (1 / 2 + Real.cos t - Real.cos t ^ 2)) *
                    (-Real.sin (2 * t)) -
                G.mirror.center.x) *
              (-Real.sin (2 * t)) +
            (-R.value * Real.cos t +
                  (R.value * (1 / 2 + Real.cos t - Real.cos t ^ 2)) *
                    Real.cos (2 * t) -
                (G.mirror.center.y - G.mirror.radius / 2)) *
              Real.cos (2 * t) = 0
        rw [hcx, hcy, hradius, Real.sin_two_mul, Real.cos_two_mul]
        ring_nf
        rw [hsinSq]
        ring
  refine ⟨hfactor, hmiss, htransverse, htangent, ?_⟩
  intro hAccepted
  have hnonneg : 0 ≤ reflectedRayDiscriminant R a t := by
    by_contra hnot
    have hneg : reflectedRayDiscriminant R a t < 0 := lt_of_not_ge hnot
    rcases hAccepted.2.2 with
      ⟨_sMirror, _hfirstMirror, _hmirror, sHit, QHit, hHit, _hNoSecond⟩
    have hcircleHit :
        Shared.GeometricOptics.OnCircle G.absorber (ray.pointAt sHit) :=
      hHit.2.1 ▸ hHit.2.2.1
    exact (hmiss.1 hneg sHit) hcircleHit
  refine ⟨hnonneg, ?_⟩
  intro hpos s Q hcontact
  have hcircleRay :
      Shared.GeometricOptics.OnCircle G.absorber (ray.pointAt s) := by
    simpa [hcontact.2.1] using hcontact.2.2.1
  rcases (htransverse hpos).1 s |>.1 hcircleRay with hsMinus | hsPlus
  · exact hsMinus
  · have hsPos : 0 < s := hcontact.1
    have hbeforeZero := hcontact.2.2.2 0 (by norm_num) hsPos
    have hfactorZero := hfactor 0
    have hsqrtSq :
        Real.sqrt (reflectedRayDiscriminant R a t) ^ 2 =
          reflectedRayDiscriminant R a t := Real.sq_sqrt hpos.le
    have hproductPos :
        0 < reflectedRayFirstRoot R a t * reflectedRaySecondRoot R a t := by
      dsimp only [reflectedRayFirstRoot, reflectedRaySecondRoot]
      change
        Shared.GeometricOptics.displacementNormSq
            (Shared.GeometricOptics.displacement G.absorber.center (ray.pointAt 0)) >
          G.absorberRadius ^ 2 at hbeforeZero
      rw [habsorber] at hbeforeZero
      nlinarith
    have hsMinusPos : 0 < reflectedRayFirstRoot R a t := by
      rw [hsPlus] at hsPos
      nlinarith
    have hfirstMinus := (htransverse hpos).2 hsMinusPos
    exact (Shared.GeometricOptics.firstContainerContact_unique G ray
      hcontact hfirstMinus).1

/-- Strict positivity of a continuous scalar datum persists locally. -/
def PositivityPersists (f : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < f t →
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℝ, |u - t| < ε → 0 < f u

/-- Continuity and local nondegeneracy of all reflected-ray scalar data. -/
theorem reflectedRayDataContinuous (R a : Length) :
    Continuous (fun t : ℝ => (mirrorPoint R ⟨t⟩).x) ∧
      Continuous (fun t : ℝ => (mirrorPoint R ⟨t⟩).y) ∧
      Continuous (fun t : ℝ => (reflectedDirectionAt t).x) ∧
      Continuous (fun t : ℝ => (reflectedDirectionAt t).y) ∧
      Continuous (reflectedRayProjection R) ∧
      Continuous (reflectedRaySignedDistance R) ∧
      Continuous (reflectedRayDiscriminant R a) ∧
      ContinuousOn (reflectedRayFirstRoot R a)
        {t : ℝ | 0 < reflectedRayDiscriminant R a t} ∧
      PositivityPersists (fun t => R.value * Real.sin t - a.value) ∧
      PositivityPersists (reflectedRayDiscriminant R a) ∧
      PositivityPersists (reflectedRayFirstRoot R a) ∧
      PositivityPersists (fun t => Real.pi / 2 - |t|) := by
  have persists (f : ℝ → ℝ) (hf : Continuous f) : PositivityPersists f := by
    intro t ht
    have hopen : IsOpen {u : ℝ | 0 < f u} :=
      isOpen_lt continuous_const hf
    rcases Metric.isOpen_iff.mp hopen t ht with ⟨ε, hε, hball⟩
    refine ⟨ε, hε, ?_⟩
    intro u hu
    apply hball
    simpa [Real.dist_eq, abs_sub_comm] using hu
  have hprojection : Continuous (reflectedRayProjection R) := by
    change Continuous (fun t : ℝ =>
      R.value * (1 / 2 + Real.cos t - Real.cos t ^ 2))
    fun_prop
  have hsignedDistance : Continuous (reflectedRaySignedDistance R) := by
    change Continuous (fun t : ℝ =>
      R.value * Real.sin t * (Real.cos t - 1))
    fun_prop
  have hdiscriminant : Continuous (reflectedRayDiscriminant R a) := by
    change Continuous (fun t : ℝ =>
      a.value ^ 2 - reflectedRaySignedDistance R t ^ 2)
    exact continuous_const.sub (hsignedDistance.pow 2)
  have hfirstRoot : Continuous (reflectedRayFirstRoot R a) := by
    change Continuous (fun t : ℝ =>
      reflectedRayProjection R t - Real.sqrt (reflectedRayDiscriminant R a t))
    exact hprojection.sub hdiscriminant.sqrt
  refine ⟨by fun_prop, by fun_prop, by fun_prop, by fun_prop,
    hprojection, hsignedDistance, hdiscriminant, hfirstRoot.continuousOn,
    ?_, ?_, ?_, ?_⟩
  · apply persists
    fun_prop
  · exact persists _ hdiscriminant
  · exact persists _ hfirstRoot
  · apply persists
    fun_prop

/-- A transverse accepted hit persists together with incoming mirror-first order. -/
theorem transverseFirstHitStable
    (G : Shared.GeometricOptics.ConcentratorGeometry) (R a : Length) (t0 : ℝ)
    (hG : Figure2fSharedGeometry G R a)
    (ht0 : 0 < t0 ∧ t0 < Real.pi / 2)
    (hAccepted : Shared.GeometricOptics.AcceptedReflectedRay G t0)
    (hTransverse : 0 < reflectedRayDiscriminant R a t0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ u : ℝ, |u - t0| < ε →
        |u| < Real.pi / 2 ∧
          IncomingRayFirstMeetsMirror G u ∧
          0 < reflectedRayDiscriminant R a u ∧
          0 < reflectedRayFirstRoot R a u ∧
          Shared.GeometricOptics.IsFirstContainerContact G
            (Shared.GeometricOptics.axialReflectedRay G.mirror .lower u)
            (reflectedRayFirstRoot R a u)
            ((Shared.GeometricOptics.axialReflectedRay G.mirror .lower u).pointAt
              (reflectedRayFirstRoot R a u)) := by
  rcases hAccepted with
    ⟨hRegime, hdomain0, sMirror, hfirstMirror, hmirror,
      sHit, QHit, hfirstHit, hnoSecond⟩
  have hincoming0 : IncomingRayFirstMeetsMirror G t0 :=
    ⟨hdomain0, sMirror, hfirstMirror, hmirror⟩
  have hshadow0 : 0 < R.value * Real.sin t0 - a.value := by
    have hpartition := incomingContactPartition G R a t0 hG (by
      rw [abs_of_pos ht0.1]
      exact ht0.2)
    have hlt := hpartition.1.1 hincoming0
    rw [abs_of_pos ht0.1] at hlt
    linarith
  have hroot0 : 0 < reflectedRayFirstRoot R a t0 := by
    rcases reflectedRayDiscriminantCriterion G R a t0 hG (by
      rw [abs_of_pos ht0.1]
      exact ht0.2) with ⟨_hfactor, _hmiss, _htransverse, _htangent, haccepted⟩
    have heq := (haccepted ⟨hRegime, hdomain0, sMirror, hfirstMirror,
      hmirror, sHit, QHit, hfirstHit, hnoSecond⟩).2 hTransverse
      sHit QHit hfirstHit
    rw [← heq]
    exact hfirstHit.1
  rcases reflectedRayDataContinuous R a with
    ⟨_hPx, _hPy, _hdx, _hdy, _hm, _heta, _hDelta, _hrootContinuous,
      hshadowPersists, hDeltaPersists, hrootPersists, hdomainPersists⟩
  rcases hshadowPersists t0 hshadow0 with ⟨εs, hεs, hshadowNear⟩
  rcases hDeltaPersists t0 hTransverse with ⟨εd, hεd, hDeltaNear⟩
  rcases hrootPersists t0 hroot0 with ⟨εr, hεr, hrootNear⟩
  have hmargin0 : 0 < Real.pi / 2 - |t0| := by
    rw [abs_of_pos ht0.1]
    linarith
  rcases hdomainPersists t0 hmargin0 with ⟨εi, hεi, hdomainNear⟩
  let ε := min εs (min εd (min εr (min εi t0)))
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hεs (lt_min hεd (lt_min hεr (lt_min hεi ht0.1)))
  refine ⟨ε, hε, ?_⟩
  intro u hu
  have hεsLe : ε ≤ εs := by
    dsimp [ε]
    exact min_le_left _ _
  have hεdLe : ε ≤ εd := by
    dsimp [ε]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεrLe : ε ≤ εr := by
    dsimp [ε]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεiLe : ε ≤ εi := by
    dsimp [ε]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hεtLe : ε ≤ t0 := by
    dsimp [ε]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hshadowU := hshadowNear u (lt_of_lt_of_le hu hεsLe)
  have hDeltaU := hDeltaNear u (lt_of_lt_of_le hu hεdLe)
  have hrootU := hrootNear u (lt_of_lt_of_le hu hεrLe)
  have hmarginU := hdomainNear u (lt_of_lt_of_le hu hεiLe)
  have hdomainU : |u| < Real.pi / 2 := by linarith
  have huPos : 0 < u := by
    have hlower := (abs_lt.mp hu).1
    linarith
  have hincomingU : IncomingRayFirstMeetsMirror G u := by
    apply (incomingContactPartition G R a u hG hdomainU).1.2
    rw [abs_of_pos huPos]
    linarith
  rcases reflectedRayDiscriminantCriterion G R a u hG hdomainU with
    ⟨_hfactor, _hmiss, htransverseU, _htangent, _haccepted⟩
  exact ⟨hdomainU, hincomingU, hDeltaU, hrootU,
    (htransverseU hDeltaU).2 hrootU⟩

/-- Nearby transverse first hits remain ordered before any mirror return. -/
theorem transverseNoReturnStable
    (G : Shared.GeometricOptics.ConcentratorGeometry) (R a : Length) (t0 : ℝ)
    (hG : Figure2fSharedGeometry G R a)
    (ht0 : 0 < t0 ∧ t0 < Real.pi / 2)
    (hAccepted : Shared.GeometricOptics.AcceptedReflectedRay G t0)
    (hTransverse : 0 < reflectedRayDiscriminant R a t0)
    (hRegime : Shared.GeometricOptics.InOneReflectionRegime G) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ u : ℝ, |u - t0| < ε →
        let ray := Shared.GeometricOptics.axialReflectedRay G.mirror .lower u
        let sMinus := reflectedRayFirstRoot R a u
        0 < sMinus ∧
          Shared.GeometricOptics.IsFirstContainerContact G ray sMinus
            (ray.pointAt sMinus) ∧
          Shared.GeometricOptics.HasNoSecondMirrorContact G ray sMinus := by
  rcases transverseFirstHitStable G R a t0 hG ht0 hAccepted hTransverse with
    ⟨ε, hε, hstable⟩
  refine ⟨ε, hε, ?_⟩
  intro u hu
  rcases hstable u hu with
    ⟨hdomain, _hincoming, _hDelta, hroot, hfirst⟩
  dsimp
  refine ⟨hroot, hfirst, ?_⟩
  exact hRegime u hdomain (reflectedRayFirstRoot R a u)
    ((Shared.GeometricOptics.axialReflectedRay G.mirror .lower u).pointAt
      (reflectedRayFirstRoot R a u)) hfirst

/-- A transverse accepted ray cannot be the largest positive accepted angle. -/
theorem transverseAcceptedRay_hasLarger
    (G : Shared.GeometricOptics.ConcentratorGeometry) (R a : Length) (t0 : ℝ)
    (hG : Figure2fSharedGeometry G R a)
    (ht0 : 0 < t0 ∧ t0 < Real.pi / 2)
    (hAccepted : Shared.GeometricOptics.AcceptedReflectedRay G t0)
    (hTransverse : 0 < reflectedRayDiscriminant R a t0) :
    ∃ t1 : ℝ, t0 < t1 ∧ t1 < Real.pi / 2 ∧
      Shared.GeometricOptics.AcceptedReflectedRay G t1 := by
  rcases transverseFirstHitStable G R a t0 hG ht0 hAccepted hTransverse with
    ⟨ε, hε, hstable⟩
  let delta := min ε (Real.pi / 2 - t0)
  have hmargin : 0 < Real.pi / 2 - t0 := by linarith [ht0.2]
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hε hmargin
  let t1 := t0 + delta / 2
  have ht1gt : t0 < t1 := by dsimp [t1]; linarith
  have ht1lt : t1 < Real.pi / 2 := by
    have hdeltaLe : delta ≤ Real.pi / 2 - t0 := by
      dsimp [delta]
      exact min_le_right _ _
    dsimp [t1]
    linarith
  have hnear : |t1 - t0| < ε := by
    have hdeltaLe : delta ≤ ε := by
      dsimp [delta]
      exact min_le_left _ _
    rw [show t1 - t0 = delta / 2 by dsimp [t1]; ring,
      abs_of_pos (by linarith)]
    linarith
  rcases hstable t1 hnear with
    ⟨hdomain1, hincoming1, _hDelta1, hroot1, hfirst1⟩
  rcases hincoming1 with ⟨_hdomain1', sMirror, hfirstMirror, hmirror⟩
  have hnoSecond := hAccepted.1 t1 hdomain1
    (reflectedRayFirstRoot R a t1)
    ((Shared.GeometricOptics.axialReflectedRay G.mirror .lower t1).pointAt
      (reflectedRayFirstRoot R a t1)) hfirst1
  refine ⟨t1, ht1gt, ht1lt, ?_⟩
  exact ⟨hAccepted.1, hdomain1, sMirror, hfirstMirror, hmirror,
    reflectedRayFirstRoot R a t1,
    (Shared.GeometricOptics.axialReflectedRay G.mirror .lower t1).pointAt
      (reflectedRayFirstRoot R a t1), hfirst1, hnoSecond⟩

/-- The attained largest accepted angle has zero ray-absorber discriminant. -/
theorem largestAngle_discriminant_zero
    (R a : Length) (thetaMax : Angle)
    (hFigure : Figure2fConfiguration R a thetaMax) :
    reflectedRayDiscriminant R a thetaMax.radians = 0 := by
  rcases hFigure with
    ⟨hR, _ha, _haLt, hangle, _honeReflection, hlargest⟩
  rcases hlargest.1 with ⟨G, hG, hAccepted⟩
  have hdomain : |thetaMax.radians| < Real.pi / 2 := by
    rw [abs_of_pos hangle.1]
    exact hangle.2
  rcases reflectedRayDiscriminantCriterion G R a thetaMax.radians hG hdomain with
    ⟨_hfactor, _hmiss, _htransverse, _htangent, haccepted⟩
  have hnonneg : 0 ≤ reflectedRayDiscriminant R a thetaMax.radians :=
    (haccepted hAccepted).1
  by_contra hne
  have hpos : 0 < reflectedRayDiscriminant R a thetaMax.radians :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  rcases transverseAcceptedRay_hasLarger G R a thetaMax.radians hG hangle
      hAccepted hpos with ⟨t1, ht1gt, _ht1lt, hAccepted1⟩
  have hbound := hlargest.2 ⟨t1⟩ ⟨G, hG, hAccepted1⟩
  rw [abs_of_pos (lt_trans hangle.1 ht1gt)] at hbound
  linarith

/-- Limiting tangency is derived from attained maximality, not assumed in validity. -/
theorem figure2fConfiguration_limitingTangent
    (R a : Length) (thetaMax : Angle)
    (hFigure : Figure2fConfiguration R a thetaMax) :
    IsLimitingRayTangent R a thetaMax := by
  rcases hFigure with
    ⟨hR, ha, haLt, hangle, honeReflection, hlargest⟩
  rcases hlargest.1 with ⟨G, hG, hAccepted⟩
  have hdomain : |thetaMax.radians| < Real.pi / 2 := by
    rw [abs_of_pos hangle.1]
    exact hangle.2
  have hzero : reflectedRayDiscriminant R a thetaMax.radians = 0 :=
    largestAngle_discriminant_zero R a thetaMax
      ⟨hR, ha, haLt, hangle, honeReflection, hlargest⟩
  have hcosPos : 0 < Real.cos thetaMax.radians :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp hdomain)
  have hcosLe : Real.cos thetaMax.radians ≤ 1 := Real.cos_le_one _
  have hfactorPos :
      0 < reflectedRayProjectionFactor thetaMax.radians := by
    have hprod :
        0 ≤ Real.cos thetaMax.radians * (1 - Real.cos thetaMax.radians) :=
      mul_nonneg hcosPos.le (sub_nonneg.mpr hcosLe)
    dsimp only [reflectedRayProjectionFactor]
    nlinarith
  have hmPos : 0 < reflectedRayProjection R thetaMax.radians := by
    exact mul_pos hR hfactorPos
  rcases reflectedRayDiscriminantCriterion G R a thetaMax.radians hG hdomain with
    ⟨_hfactor, _hmiss, _htransverse, htangent, _haccepted⟩
  have hcontact := (htangent hzero hmPos).2
  exact ⟨G, hG, hAccepted, reflectedRayProjection R thetaMax.radians,
    (Shared.GeometricOptics.axialReflectedRay G.mirror .lower
      thetaMax.radians).pointAt (reflectedRayProjection R thetaMax.radians),
    hcontact⟩

/-- Tangency identifies the absorber radius with the perpendicular line distance. -/
theorem figure2fConfiguration_tangentDistance
    (R a : Length) (thetaMax : Angle)
    (hFigure : Figure2fConfiguration R a thetaMax) :
    a.value ^ 2 =
      displacementDetDirection
          (displacement (mirrorPoint R thetaMax) (containerCenter R))
          (reflectedDirectionAt thetaMax.radians) ^ 2 := by
  have hlimiting := figure2fConfiguration_limitingTangent R a thetaMax hFigure
  rcases hlimiting with ⟨G, hG, _hAccepted, s, Q, htangent⟩
  have hR : R.IsPositive := hFigure.1
  have hangle := hFigure.2.2.2.1
  have hdomain : |thetaMax.radians| < Real.pi / 2 := by
    rw [abs_of_pos hangle.1]
    exact hangle.2
  have hrayData :=
    (reflectedDirectionFormula R thetaMax.radians hR hdomain).2 a G hG
  have hcenter := hG.1
  have hradius := hG.2.1
  have habsorber := hG.2.2
  have hcx : G.mirror.center.x = 0 := by
    exact congrArg Shared.GeometricOptics.Point2.x hcenter
  have hcy : G.mirror.center.y = 0 := by
    exact congrArg Shared.GeometricOptics.Point2.y hcenter
  have hdistance :=
    (Shared.GeometricOptics.tangentContact_distanceSq G
      (Shared.GeometricOptics.axialReflectedRay G.mirror .lower
        thetaMax.radians) htangent).2
  rw [hrayData.1, hrayData.2] at hdistance
  change
    G.absorberRadius ^ 2 =
      (((mirrorPoint R thetaMax).x - G.mirror.center.x) *
            (reflectedDirectionAt thetaMax.radians).y -
          ((mirrorPoint R thetaMax).y -
              (G.mirror.center.y - G.mirror.radius / 2)) *
            (reflectedDirectionAt thetaMax.radians).x) ^ 2 at hdistance
  rw [hcx, hcy, hradius, habsorber] at hdistance
  change
    a.value ^ 2 =
      (((mirrorPoint R thetaMax).x - 0) *
            (reflectedDirectionAt thetaMax.radians).y -
          ((mirrorPoint R thetaMax).y - (-(R.value / 2))) *
            (reflectedDirectionAt thetaMax.radians).x) ^ 2
  ring_nf at hdistance ⊢
  exact hdistance

/-! ## Fixed-radius small-angle family -/

/-- Radius obtained from the limiting perpendicular distance at angle `phi`. -/
def smallAngleRadius (R : Length) (phi : ℝ) : Length :=
  ⟨R.value * perpendicularDistanceFactor phi⟩

/-- Edge angle of the direct incoming shadow. -/
def directShadowCutoff (phi : ℝ) : Angle :=
  ⟨Real.arcsin (perpendicularDistanceFactor phi)⟩

/-- Dimensionless small-family discriminant. -/
def smallAngleDiscriminant (phi t : ℝ) : ℝ :=
  perpendicularDistanceFactor phi ^ 2 -
    perpendicularDistanceFactor |t| ^ 2

/-- First absorber-root parameter in the small-angle family. -/
def smallAngleFirstHitParameter (R : Length) (phi t : ℝ) : ℝ :=
  R.value *
    (reflectedRayProjectionFactor t - Real.sqrt (smallAngleDiscriminant phi t))

/-- Second absorber-root parameter in the small-angle family. -/
def smallAngleSecondHitParameter (R : Length) (phi t : ℝ) : ℝ :=
  R.value *
    (reflectedRayProjectionFactor t + Real.sqrt (smallAngleDiscriminant phi t))

/-- The perpendicular-distance factor is strictly increasing on the positive domain. -/
theorem perpendicularDistanceStrictMono :
    StrictMonoOn perpendicularDistanceFactor (Set.Ico 0 (Real.pi / 2)) ∧
      ∀ phi t : ℝ, 0 < phi → phi < Real.pi / 6 → |t| < Real.pi / 2 →
        (perpendicularDistanceFactor |t| ≤ perpendicularDistanceFactor phi ↔
          |t| ≤ phi) := by
  have hmono : StrictMonoOn perpendicularDistanceFactor (Set.Ico 0 (Real.pi / 2)) := by
    intro x hx y hy hxy
    have hpi : 0 < Real.pi := Real.pi_pos
    have hsinLt : Real.sin x < Real.sin y :=
      Real.strictMonoOn_sin
        ⟨by linarith [hx.1], hx.2.le⟩ ⟨by linarith [hy.1], hy.2.le⟩ hxy
    have hcosGt : Real.cos y < Real.cos x :=
      Real.strictAntiOn_cos
        ⟨hx.1, by linarith [hx.2]⟩ ⟨hy.1, by linarith [hy.2]⟩ hxy
    have hsinYPos : 0 < Real.sin y :=
      Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_lt hx.1 hxy) (by linarith [hy.2])
    have hfactorXNonneg : 0 ≤ 1 - Real.cos x :=
      sub_nonneg.mpr (Real.cos_le_one x)
    calc
      perpendicularDistanceFactor x = Real.sin x * (1 - Real.cos x) := rfl
      _ ≤ Real.sin y * (1 - Real.cos x) :=
        mul_le_mul_of_nonneg_right hsinLt.le hfactorXNonneg
      _ < Real.sin y * (1 - Real.cos y) := by
        apply mul_lt_mul_of_pos_left _ hsinYPos
        linarith
      _ = perpendicularDistanceFactor y := rfl
  refine ⟨hmono, ?_⟩
  intro phi t hphiPos hphiLt ht
  apply hmono.le_iff_le
  · exact ⟨abs_nonneg t, ht⟩
  · exact ⟨hphiPos.le, by linarith [Real.pi_pos]⟩

/-- The small-angle interval is nonempty and produces physical radii and angles. -/
theorem smallAngleRadiusDomain :
    (∃ phi : ℝ, 0 < phi ∧ phi < Real.pi / 6) ∧
      ∀ (R : Length) (phi : ℝ),
        R.IsPositive → 0 < phi → phi < Real.pi / 6 →
          (smallAngleRadius R phi).IsPositive ∧
            (smallAngleRadius R phi).value < R.value / 2 ∧
            InMaximumAngleDomain ⟨phi⟩ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · refine ⟨Real.pi / 12, by linarith, by linarith⟩
  · intro R phi hR hphiPos hphiLt
    have hphiHalf : phi < Real.pi / 2 := by linarith
    have hphiPi : phi < Real.pi := by linarith
    have hsinPos : 0 < Real.sin phi :=
      Real.sin_pos_of_pos_of_lt_pi hphiPos hphiPi
    have hsinLt : Real.sin phi < 1 := by
      have := Real.strictMonoOn_sin
        ⟨by linarith, hphiHalf.le⟩
        ⟨by linarith, le_rfl⟩ hphiHalf
      simpa [Real.sin_pi_div_two] using this
    have hcosLtOne : Real.cos phi < 1 := by
      have := Real.strictAntiOn_cos
        ⟨by norm_num, by linarith⟩ ⟨hphiPos.le, by linarith⟩ hphiPos
      simpa using this
    have hphiThird : phi < Real.pi / 3 := by linarith
    have hcosHalf : 1 / 2 < Real.cos phi := by
      have := Real.strictAntiOn_cos
        ⟨hphiPos.le, by linarith⟩
        ⟨by linarith, by linarith⟩ hphiThird
      simpa [Real.cos_pi_div_three] using this
    have hfactorPos : 0 < 1 - Real.cos phi := by linarith
    have hperpPos : 0 < perpendicularDistanceFactor phi := by
      exact mul_pos hsinPos hfactorPos
    have hperpLt : perpendicularDistanceFactor phi < 1 / 2 := by
      calc
        perpendicularDistanceFactor phi =
            Real.sin phi * (1 - Real.cos phi) := rfl
        _ < 1 * (1 - Real.cos phi) :=
          mul_lt_mul_of_pos_right hsinLt hfactorPos
        _ < 1 / 2 := by nlinarith
    refine ⟨?_, ?_, ⟨hphiPos, hphiHalf⟩⟩
    · exact mul_pos hR hperpPos
    · have := mul_lt_mul_of_pos_left hperpLt hR
      change R.value * perpendicularDistanceFactor phi < R.value / 2
      calc
        R.value * perpendicularDistanceFactor phi < R.value * (1 / 2) := this
        _ = R.value / 2 := by ring

/-- The direct-shadow cutoff is a positive angle strictly below `phi`. -/
theorem directShadowCutoffDomain
    (phi : ℝ) (hphiPos : 0 < phi) (hphiLt : phi < Real.pi / 6) :
    0 < perpendicularDistanceFactor phi ∧
      perpendicularDistanceFactor phi < Real.sin phi ∧
      Real.sin phi < 1 ∧
      0 < (directShadowCutoff phi).radians ∧
      (directShadowCutoff phi).radians < phi ∧
      Real.sin (directShadowCutoff phi).radians =
        perpendicularDistanceFactor phi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hphiHalf : phi < Real.pi / 2 := by linarith
  have hphiPi : phi < Real.pi := by linarith
  have hsinPos : 0 < Real.sin phi :=
    Real.sin_pos_of_pos_of_lt_pi hphiPos hphiPi
  have hsinLt : Real.sin phi < 1 := by
    have := Real.strictMonoOn_sin
      ⟨by linarith, hphiHalf.le⟩ ⟨by linarith, le_rfl⟩ hphiHalf
    simpa [Real.sin_pi_div_two] using this
  have hcosPos : 0 < Real.cos phi :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hphiHalf⟩
  have hcosLtOne : Real.cos phi < 1 := by
    have := Real.strictAntiOn_cos
      ⟨by norm_num, by linarith⟩ ⟨hphiPos.le, by linarith⟩ hphiPos
    simpa using this
  have hfactorPos : 0 < 1 - Real.cos phi := by linarith
  have hfactorLt : 1 - Real.cos phi < 1 := by linarith
  have hperpPos : 0 < perpendicularDistanceFactor phi :=
    mul_pos hsinPos hfactorPos
  have hperpLtSin : perpendicularDistanceFactor phi < Real.sin phi := by
    calc
      perpendicularDistanceFactor phi = Real.sin phi * (1 - Real.cos phi) := rfl
      _ < Real.sin phi * 1 := mul_lt_mul_of_pos_left hfactorLt hsinPos
      _ = Real.sin phi := mul_one _
  have hperpLtOne : perpendicularDistanceFactor phi < 1 :=
    lt_trans hperpLtSin hsinLt
  have harcsinPos : 0 < (directShadowCutoff phi).radians := by
    exact Real.arcsin_pos.2 hperpPos
  have harcsinLt : (directShadowCutoff phi).radians < phi := by
    change Real.arcsin (perpendicularDistanceFactor phi) < phi
    calc
      Real.arcsin (perpendicularDistanceFactor phi) <
          Real.arcsin (Real.sin phi) :=
        Real.arcsin_lt_arcsin (by linarith) hperpLtSin hsinLt.le
      _ = phi := Real.arcsin_sin (by linarith) hphiHalf.le
  have hsinArcsin :
      Real.sin (directShadowCutoff phi).radians =
        perpendicularDistanceFactor phi := by
    exact Real.sin_arcsin (by linarith) hperpLtOne.le
  exact ⟨hperpPos, hperpLtSin, hsinLt, harcsinPos, harcsinLt, hsinArcsin⟩

/-- Exact direct-shadow versus incoming mirror-first classification. -/
theorem smallAngleIncomingContactClassification
    (R : Length) (phi t : ℝ)
    (hR : R.IsPositive) (hphiPos : 0 < phi) (hphiLt : phi < Real.pi / 6)
    (G : Shared.GeometricOptics.ConcentratorGeometry)
    (hG : Figure2fSharedGeometry G R (smallAngleRadius R phi))
    (ht : |t| < Real.pi / 2) :
    (DirectIncomingAbsorption G t ↔
        |t| ≤ (directShadowCutoff phi).radians) ∧
      (IncomingRayFirstMeetsMirror G t ↔
        (directShadowCutoff phi).radians < |t| ∧ |t| < Real.pi / 2) ∧
      ((directShadowCutoff phi).radians < |t| →
        let P := (Shared.GeometricOptics.semicirclePoint G.mirror .lower t).1
        Shared.GeometricOptics.IsFirstConcentratorContact G
            (Shared.GeometricOptics.incomingSunlightRay G P.x)
            (R.value * Real.cos t) P ∧
          Shared.GeometricOptics.OnReflectingArc G.lowerMirror P) := by
  have hcut := directShadowCutoffDomain phi hphiPos hphiLt
  let delta := (directShadowCutoff phi).radians
  have hdeltaPos : 0 < delta := hcut.2.2.2.1
  have hdeltaLtPhi : delta < phi := hcut.2.2.2.2.1
  have hphiHalf : phi < Real.pi / 2 := by linarith [Real.pi_pos]
  have hdeltaHalf : delta < Real.pi / 2 := lt_trans hdeltaLtPhi hphiHalf
  have hsinDelta : Real.sin delta = perpendicularDistanceFactor phi :=
    hcut.2.2.2.2.2
  have habsMem : |t| ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [abs_nonneg t], ht.le⟩
  have hdeltaMem : delta ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, hdeltaHalf.le⟩
  have hdirect :
      DirectIncomingAbsorption G t ↔ |t| ≤ delta := by
    rw [(incomingContactPartition G R (smallAngleRadius R phi) t hG ht).2.1]
    change R.value * Real.sin |t| ≤
        R.value * perpendicularDistanceFactor phi ↔ _
    rw [mul_le_mul_iff_of_pos_left hR, ← hsinDelta]
    exact Real.strictMonoOn_sin.le_iff_le habsMem hdeltaMem
  have hincoming :
      IncomingRayFirstMeetsMirror G t ↔ delta < |t| ∧ |t| < Real.pi / 2 := by
    constructor
    · intro hin
      have hlt :=
        (incomingContactPartition G R (smallAngleRadius R phi) t hG ht).1.1 hin
      change R.value * perpendicularDistanceFactor phi <
          R.value * Real.sin |t| at hlt
      have hsinLt : Real.sin delta < Real.sin |t| := by
        rw [hsinDelta]
        exact (mul_lt_mul_iff_of_pos_left hR).1 hlt
      exact ⟨(Real.strictMonoOn_sin.lt_iff_lt hdeltaMem habsMem).1 hsinLt, ht⟩
    · rintro ⟨hdeltaLt, _⟩
      apply (incomingContactPartition G R (smallAngleRadius R phi) t hG ht).1.2
      change R.value * perpendicularDistanceFactor phi <
        R.value * Real.sin |t|
      apply (mul_lt_mul_iff_of_pos_left hR).2
      rw [← hsinDelta]
      exact (Real.strictMonoOn_sin.lt_iff_lt hdeltaMem habsMem).2 hdeltaLt
  refine ⟨hdirect, hincoming, ?_⟩
  intro hdeltaLt
  have hin := hincoming.2 ⟨hdeltaLt, ht⟩
  rcases hin with ⟨_hdomain, sMirror, hfirst, harc⟩
  let P := (Shared.GeometricOptics.semicirclePoint G.mirror .lower t).1
  have hcenter := hG.1
  have hradius := hG.2.1
  have hcy : G.mirror.center.y = 0 := by
    exact congrArg Shared.GeometricOptics.Point2.y hcenter
  have hPy : P.y = -R.value * Real.cos t := by
    simp [P, Shared.GeometricOptics.semicirclePoint,
      Shared.GeometricOptics.orientationSign, hcy, hradius]
  have hrayY :
      ((Shared.GeometricOptics.incomingSunlightRay G P.x).pointAt sMirror).y =
        -sMirror := by
    simp [Shared.GeometricOptics.incomingSunlightRay,
      Shared.GeometricOptics.ForwardRay.pointAt,
      Shared.GeometricOptics.translate,
      Shared.GeometricOptics.directionDisplacement,
      Shared.GeometricOptics.axisDirection,
      Shared.GeometricOptics.orientationSign, hcy]
  have hsMirror : sMirror = R.value * Real.cos t := by
    have hy := congrArg Shared.GeometricOptics.Point2.y hfirst.2.1
    rw [hPy, hrayY] at hy
    linarith
  subst sMirror
  exact ⟨hfirst, harc⟩

/-- Exact first absorber contact of the geometrically launched small-family ray. -/
theorem smallAngleFirstContainerContact
    (R : Length) (phi t : ℝ)
    (hR : R.IsPositive) (hphiPos : 0 < phi) (hphiLt : phi < Real.pi / 6)
    (ht : |t| < Real.pi / 2) :
    ((∃ s : ℝ,
      IsFirstContainerContact R (smallAngleRadius R phi)
        (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s) ↔ |t| ≤ phi) ∧
      (|t| ≤ phi →
        0 ≤ smallAngleDiscriminant phi t ∧
          0 < smallAngleFirstHitParameter R phi t ∧
          OnContainerBoundary R (smallAngleRadius R phi)
            (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t)
              (smallAngleFirstHitParameter R phi t)) ∧
          OnContainerBoundary R (smallAngleRadius R phi)
            (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t)
              (smallAngleSecondHitParameter R phi t)) ∧
          IsFirstContainerContact R (smallAngleRadius R phi)
            (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t)
            (smallAngleFirstHitParameter R phi t) ∧
          ∀ s : ℝ,
            IsFirstContainerContact R (smallAngleRadius R phi)
              (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s →
                s = smallAngleFirstHitParameter R phi t) ∧
      ∀ G : Shared.GeometricOptics.ConcentratorGeometry,
        Figure2fSharedGeometry G R (smallAngleRadius R phi) →
          (|t| ≤ phi →
            let ray := Shared.GeometricOptics.axialReflectedRay G.mirror .lower t
            Shared.GeometricOptics.IsFirstContainerContact G ray
              (smallAngleFirstHitParameter R phi t)
              (ray.pointAt (smallAngleFirstHitParameter R phi t))) ∧
          (|t| ≤ (directShadowCutoff phi).radians →
            ¬ Shared.GeometricOptics.AcceptedReflectedRay G t) := by
  have hdomains := smallAngleRadiusDomain
  rcases hdomains.2 R phi hR hphiPos hphiLt with
    ⟨haPos, haLt, _hangle⟩
  have hcut := directShadowCutoffDomain phi hphiPos hphiLt
  have hperpPhiPos : 0 < perpendicularDistanceFactor phi := hcut.1
  have hperpPhiLtHalf : perpendicularDistanceFactor phi < 1 / 2 := by
    have h := haLt
    change R.value * perpendicularDistanceFactor phi < R.value / 2 at h
    have := (mul_lt_mul_iff_of_pos_left hR).1
      (show R.value * perpendicularDistanceFactor phi < R.value * (1 / 2) by
        simpa [div_eq_mul_inv] using h)
    exact this
  have hperpAbsNonneg : 0 ≤ perpendicularDistanceFactor |t| := by
    have hsin : 0 ≤ Real.sin |t| :=
      Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg t)
        (by linarith [ht, Real.pi_pos])
    exact mul_nonneg hsin (sub_nonneg.mpr (Real.cos_le_one _))
  have hhitIff :
      perpendicularDistanceFactor |t| ≤ perpendicularDistanceFactor phi ↔
        |t| ≤ phi :=
    perpendicularDistanceStrictMono.2 phi t hphiPos hphiLt ht
  have hsignedSq :
      reflectedRaySignedDistance R t ^ 2 =
        R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2 := by
    rcases le_total 0 t with htNonneg | htNonpos
    · rw [abs_of_nonneg htNonneg]
      dsimp only [reflectedRaySignedDistance, perpendicularDistanceFactor]
      ring
    · rw [abs_of_nonpos htNonpos]
      change
        (R.value * Real.sin t * (Real.cos t - 1)) ^ 2 =
          R.value ^ 2 * (Real.sin (-t) * (1 - Real.cos (-t))) ^ 2
      rw [Real.sin_neg, Real.cos_neg]
      ring
  have hDeltaEq :
      reflectedRayDiscriminant R (smallAngleRadius R phi) t =
        R.value ^ 2 * smallAngleDiscriminant phi t := by
    dsimp only [reflectedRayDiscriminant, smallAngleRadius,
      smallAngleDiscriminant]
    rw [hsignedSq]
    ring
  have hdetails (htPhi : |t| ≤ phi) :
      0 ≤ smallAngleDiscriminant phi t ∧
        0 < smallAngleFirstHitParameter R phi t ∧
        OnContainerBoundary R (smallAngleRadius R phi)
          (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t)
            (smallAngleFirstHitParameter R phi t)) ∧
        OnContainerBoundary R (smallAngleRadius R phi)
          (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t)
            (smallAngleSecondHitParameter R phi t)) ∧
        IsFirstContainerContact R (smallAngleRadius R phi)
          (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t)
          (smallAngleFirstHitParameter R phi t) ∧
        ∀ s : ℝ,
          IsFirstContainerContact R (smallAngleRadius R phi)
            (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s →
              s = smallAngleFirstHitParameter R phi t := by
    have hperpLe := hhitIff.2 htPhi
    have hsmallD : 0 ≤ smallAngleDiscriminant phi t := by
      dsimp only [smallAngleDiscriminant]
      exact sub_nonneg.mpr
        ((sq_le_sq₀ hperpAbsNonneg hperpPhiPos.le).2 hperpLe)
    have hsmallDLt : smallAngleDiscriminant phi t < (1 / 2 : ℝ) ^ 2 := by
      dsimp only [smallAngleDiscriminant]
      have hphiSq : perpendicularDistanceFactor phi ^ 2 < (1 / 2 : ℝ) ^ 2 :=
        (sq_lt_sq₀ hperpPhiPos.le (by norm_num)).2 hperpPhiLtHalf
      nlinarith [sq_nonneg (perpendicularDistanceFactor |t|)]
    have hsqrtLt : Real.sqrt (smallAngleDiscriminant phi t) < 1 / 2 :=
      (Real.sqrt_lt' (by norm_num)).2 hsmallDLt
    have hcosPos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo (abs_lt.mp ht)
    have hprojectionHalf :
        1 / 2 ≤ reflectedRayProjectionFactor t := by
      have hcProd : 0 ≤ Real.cos t * (1 - Real.cos t) :=
        mul_nonneg hcosPos.le (sub_nonneg.mpr (Real.cos_le_one t))
      dsimp only [reflectedRayProjectionFactor]
      nlinarith
    have hfirstPos : 0 < smallAngleFirstHitParameter R phi t := by
      dsimp only [smallAngleFirstHitParameter]
      exact mul_pos hR (by linarith)
    have hsqrtScale :
        Real.sqrt (R.value ^ 2 * smallAngleDiscriminant phi t) =
          R.value * Real.sqrt (smallAngleDiscriminant phi t) := by
      rw [Real.sqrt_mul (sq_nonneg R.value), Real.sqrt_sq hR.le]
    have hfirstEq :
        reflectedRayFirstRoot R (smallAngleRadius R phi) t =
          smallAngleFirstHitParameter R phi t := by
      dsimp only [reflectedRayFirstRoot, smallAngleFirstHitParameter]
      rw [hDeltaEq, hsqrtScale]
      dsimp only [reflectedRayProjection]
      ring
    have hsecondEq :
        reflectedRaySecondRoot R (smallAngleRadius R phi) t =
          smallAngleSecondHitParameter R phi t := by
      dsimp only [reflectedRaySecondRoot, smallAngleSecondHitParameter]
      rw [hDeltaEq, hsqrtScale]
      dsimp only [reflectedRayProjection]
      ring
    have hgeneralD :
        0 ≤ (smallAngleRadius R phi).value ^ 2 -
          R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2 := by
      rw [show
        (smallAngleRadius R phi).value ^ 2 -
            R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2 =
          R.value ^ 2 * smallAngleDiscriminant phi t by
            change
              (R.value * perpendicularDistanceFactor phi) ^ 2 -
                  R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2 =
                R.value ^ 2 *
                  (perpendicularDistanceFactor phi ^ 2 -
                    perpendicularDistanceFactor |t| ^ 2)
            ring]
      exact mul_nonneg (sq_nonneg R.value) hsmallD
    have hroots :=
      (reflectedRayCircleQuadratics R t hR ht).2.1
        (smallAngleRadius R phi) hgeneralD
    have hfirstBoundary :
        OnContainerBoundary R (smallAngleRadius R phi)
          (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t)
            (smallAngleFirstHitParameter R phi t)) := by
      apply (hroots _).2
      left
      calc
        smallAngleFirstHitParameter R phi t =
            reflectedRayFirstRoot R (smallAngleRadius R phi) t := hfirstEq.symm
        _ = reflectedRayProjection R t -
            Real.sqrt ((smallAngleRadius R phi).value ^ 2 -
              R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2) := by
          dsimp only [reflectedRayFirstRoot, reflectedRayDiscriminant]
          rw [hsignedSq]
    have hsecondBoundary :
        OnContainerBoundary R (smallAngleRadius R phi)
          (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t)
            (smallAngleSecondHitParameter R phi t)) := by
      apply (hroots _).2
      right
      calc
        smallAngleSecondHitParameter R phi t =
            reflectedRaySecondRoot R (smallAngleRadius R phi) t := hsecondEq.symm
        _ = reflectedRayProjection R t +
            Real.sqrt ((smallAngleRadius R phi).value ^ 2 -
              R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2) := by
          dsimp only [reflectedRaySecondRoot, reflectedRayDiscriminant]
          rw [hsignedSq]
    rcases (figure2fSharedGeometry_existsUnique R (smallAngleRadius R phi)).2
      ⟨hR, haPos, haLt⟩ with ⟨G₀, hG₀, _hunique⟩
    have hdomain : |t| < Real.pi / 2 := ht
    rcases reflectedRayDiscriminantCriterion G₀ R (smallAngleRadius R phi) t
        hG₀ hdomain with
      ⟨_hfactor, _hmiss, htransverse, htangent, _haccepted⟩
    have hDeltaNonneg :
        0 ≤ reflectedRayDiscriminant R (smallAngleRadius R phi) t := by
      rw [hDeltaEq]
      exact mul_nonneg (sq_nonneg R.value) hsmallD
    have hsharedFirst :
        Shared.GeometricOptics.IsFirstContainerContact G₀
          (Shared.GeometricOptics.axialReflectedRay G₀.mirror .lower t)
          (smallAngleFirstHitParameter R phi t)
          ((Shared.GeometricOptics.axialReflectedRay G₀.mirror .lower t).pointAt
            (smallAngleFirstHitParameter R phi t)) := by
      by_cases hzero : smallAngleDiscriminant phi t = 0
      · have hDeltaZero :
            reflectedRayDiscriminant R (smallAngleRadius R phi) t = 0 := by
          rw [hDeltaEq, hzero, mul_zero]
        have hmPos : 0 < reflectedRayProjection R t :=
          mul_pos hR (by linarith)
        have hcontact := (htangent hDeltaZero hmPos).2.1
        have hparameter :
            reflectedRayProjection R t = smallAngleFirstHitParameter R phi t := by
          dsimp only [smallAngleFirstHitParameter]
          rw [hzero, Real.sqrt_zero]
          dsimp only [reflectedRayProjection]
          ring
        simpa [hparameter] using hcontact
      · have hsmallDPos : 0 < smallAngleDiscriminant phi t :=
          lt_of_le_of_ne hsmallD (Ne.symm hzero)
        have hDeltaPos :
            0 < reflectedRayDiscriminant R (smallAngleRadius R phi) t := by
          rw [hDeltaEq]
          exact mul_pos (sq_pos_of_pos hR) hsmallDPos
        have hcontact := (htransverse hDeltaPos).2 (by simpa [hfirstEq])
        simpa [hfirstEq] using hcontact
    have hrayData := (reflectedDirectionFormula R t hR ht).2
      (smallAngleRadius R phi) G₀ hG₀
    have hrayPoint (u : ℝ) :
        (Shared.GeometricOptics.axialReflectedRay G₀.mirror .lower t).pointAt u =
          toSharedPoint
            (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) u) := by
      change
        Shared.GeometricOptics.translate
            (Shared.GeometricOptics.axialReflectedRay G₀.mirror .lower t).origin
            (Shared.GeometricOptics.directionDisplacement u
              (Shared.GeometricOptics.axialReflectedRay G₀.mirror .lower t).direction.1) =
          toSharedPoint
            (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) u)
      rw [hrayData.1, hrayData.2]
      rfl
    have hlocalFirst :
        IsFirstContainerContact R (smallAngleRadius R phi)
          (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t)
          (smallAngleFirstHitParameter R phi t) := by
      refine ⟨hfirstPos, hfirstBoundary, ?_⟩
      intro u huNonneg huLt hin
      have hsharedIn :
          Shared.GeometricOptics.InClosedDisk G₀.absorber
            ((Shared.GeometricOptics.axialReflectedRay G₀.mirror .lower t).pointAt
              u) := by
        rw [hrayPoint]
        exact ((figure2fSharedBoundaryBridge G₀ R (smallAngleRadius R phi)
          hG₀).2 _).2.1.2 hin
      have hbefore := hsharedFirst.2.2.2 u huNonneg huLt
      exact (not_lt_of_ge hsharedIn) hbefore
    have huniqueFirst : ∀ s : ℝ,
        IsFirstContainerContact R (smallAngleRadius R phi)
          (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s →
            s = smallAngleFirstHitParameter R phi t := by
      intro s hs
      rcases lt_trichotomy s (smallAngleFirstHitParameter R phi t) with
        hsLt | hsEq | hsGt
      · have hout := hlocalFirst.2.2 s hs.1.le hsLt
        exact False.elim (hout (by
          dsimp only [InContainer]
          exact le_of_eq hs.2.1))
      · exact hsEq
      · have hout := hs.2.2 (smallAngleFirstHitParameter R phi t)
          hfirstPos.le hsGt
        exact False.elim (hout (by
          dsimp only [InContainer]
          exact le_of_eq hfirstBoundary))
    exact ⟨hsmallD, hfirstPos, hfirstBoundary, hsecondBoundary,
      hlocalFirst, huniqueFirst⟩
  have hexistenceIff :
      (∃ s : ℝ,
        IsFirstContainerContact R (smallAngleRadius R phi)
          (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s) ↔ |t| ≤ phi := by
    constructor
    · rintro ⟨s, hs⟩
      have hquad := (reflectedRayCircleQuadratics R t hR ht).1 s |>.1
      have hboundary := hs.2.1
      dsimp only [OnContainerBoundary] at hboundary
      change
        displacementNormSq
            (displacement
              (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) s)
              (containerCenter R)) =
          (smallAngleRadius R phi).value ^ 2 at hboundary
      have hsq :
          perpendicularDistanceFactor |t| ^ 2 ≤
            perpendicularDistanceFactor phi ^ 2 := by
        have hscaled :
            R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2 ≤
              R.value ^ 2 * perpendicularDistanceFactor phi ^ 2 := by
          have hrhoSq :
              (smallAngleRadius R phi).value ^ 2 =
                (R.value * perpendicularDistanceFactor phi) ^ 2 := by
            rfl
          rw [hrhoSq] at hboundary
          nlinarith [sq_nonneg (s - reflectedRayProjection R t)]
        exact (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hR)).1 hscaled
      exact hhitIff.1 ((sq_le_sq₀ hperpAbsNonneg hperpPhiPos.le).1 hsq)
    · intro htPhi
      exact ⟨smallAngleFirstHitParameter R phi t, (hdetails htPhi).2.2.2.2.1⟩
  refine ⟨hexistenceIff, ?_, ?_⟩
  · exact hdetails
  · intro G hG
    constructor
    · intro htPhi
      have hd := hdetails htPhi
      have hsmallD := hd.1
      have hDeltaNonneg :
          0 ≤ reflectedRayDiscriminant R (smallAngleRadius R phi) t := by
        rw [hDeltaEq]
        exact mul_nonneg (sq_nonneg R.value) hsmallD
      have hsqrtScale :
          Real.sqrt (R.value ^ 2 * smallAngleDiscriminant phi t) =
            R.value * Real.sqrt (smallAngleDiscriminant phi t) := by
        rw [Real.sqrt_mul (sq_nonneg R.value), Real.sqrt_sq hR.le]
      have hfirstEq :
          reflectedRayFirstRoot R (smallAngleRadius R phi) t =
            smallAngleFirstHitParameter R phi t := by
        dsimp only [reflectedRayFirstRoot, smallAngleFirstHitParameter]
        rw [hDeltaEq, hsqrtScale]
        dsimp only [reflectedRayProjection]
        ring
      rcases reflectedRayDiscriminantCriterion G R (smallAngleRadius R phi) t
          hG ht with ⟨_hfactor, _hmiss, htransverse, htangent, _haccepted⟩
      by_cases hzero : reflectedRayDiscriminant R (smallAngleRadius R phi) t = 0
      · have hrootProj :
            reflectedRayFirstRoot R (smallAngleRadius R phi) t =
              reflectedRayProjection R t := by
          dsimp only [reflectedRayFirstRoot]
          rw [hzero, Real.sqrt_zero]
          ring
        have hmPos : 0 < reflectedRayProjection R t := by
          rw [← hrootProj, hfirstEq]
          exact hd.2.1
        have hparameter :
            reflectedRayProjection R t = smallAngleFirstHitParameter R phi t :=
          hrootProj.symm.trans hfirstEq
        simpa [hparameter] using (htangent hzero hmPos).2.1
      · have hpos : 0 < reflectedRayDiscriminant R (smallAngleRadius R phi) t :=
          lt_of_le_of_ne hDeltaNonneg (Ne.symm hzero)
        simpa [hfirstEq] using (htransverse hpos).2 (by simpa [hfirstEq] using hd.2.1)
    · intro htShadow hAccepted
      have hclassification := smallAngleIncomingContactClassification R phi t hR
        hphiPos hphiLt G hG ht
      have hdirect := hclassification.1.2 htShadow
      have hincoming : IncomingRayFirstMeetsMirror G t := by
        rcases hAccepted with
          ⟨_hregime, hdomain, sMirror, hfirst, hmirror, _sHit, _QHit,
            _hHit, _hNoSecond⟩
        exact ⟨hdomain, sMirror, hfirst, hmirror⟩
      exact (incomingContactPartition G R (smallAngleRadius R phi) t hG ht).2.2.2
        ⟨hincoming, hdirect⟩

/-- Every small-family first absorber contact precedes the second mirror contact. -/
theorem smallAngleOneReflectionDomain
    (R : Length) (phi : ℝ)
    (hR : R.IsPositive) (hphiPos : 0 < phi) (hphiLt : phi < Real.pi / 6) :
    InOneReflectionDomain R (smallAngleRadius R phi) ∧
      ∀ G : Shared.GeometricOptics.ConcentratorGeometry,
        Figure2fSharedGeometry G R (smallAngleRadius R phi) →
          ∀ (t s : ℝ) (Q : Shared.GeometricOptics.Point2),
            |t| < Real.pi / 2 →
            Shared.GeometricOptics.IsFirstContainerContact G
                (Shared.GeometricOptics.axialReflectedRay G.mirror .lower t) s Q →
              |t| ≤ phi ∧
                0 < s ∧
                s ≤ reflectedRayProjection R t ∧
                reflectedRayProjection R t < 2 * R.value * Real.cos t ∧
                Shared.GeometricOptics.HasNoSecondMirrorContact G
                  (Shared.GeometricOptics.axialReflectedRay G.mirror .lower t) s := by
  have hdomains := smallAngleRadiusDomain.2 R phi hR hphiPos hphiLt
  rcases hdomains with ⟨haPos, haLt, _hangle⟩
  have hcut := directShadowCutoffDomain phi hphiPos hphiLt
  have hperpPhiPos : 0 < perpendicularDistanceFactor phi := hcut.1
  have hproperty :
      ∀ G : Shared.GeometricOptics.ConcentratorGeometry,
        Figure2fSharedGeometry G R (smallAngleRadius R phi) →
          ∀ (t s : ℝ) (Q : Shared.GeometricOptics.Point2),
            |t| < Real.pi / 2 →
            Shared.GeometricOptics.IsFirstContainerContact G
                (Shared.GeometricOptics.axialReflectedRay G.mirror .lower t) s Q →
              |t| ≤ phi ∧
                0 < s ∧
                s ≤ reflectedRayProjection R t ∧
                reflectedRayProjection R t < 2 * R.value * Real.cos t ∧
                Shared.GeometricOptics.HasNoSecondMirrorContact G
                  (Shared.GeometricOptics.axialReflectedRay G.mirror .lower t) s := by
    intro G hG t s Q ht hcontact
    let ray := Shared.GeometricOptics.axialReflectedRay G.mirror .lower t
    have hcircle : Shared.GeometricOptics.OnCircle G.absorber (ray.pointAt s) := by
      simpa [ray, hcontact.2.1] using hcontact.2.2.1
    rcases reflectedRayDiscriminantCriterion G R (smallAngleRadius R phi) t
        hG ht with ⟨_hfactor, hmiss, _htransverse, _htangent, _haccepted⟩
    have hDeltaNonneg :
        0 ≤ reflectedRayDiscriminant R (smallAngleRadius R phi) t := by
      by_contra hnot
      exact (hmiss.1 (lt_of_not_ge hnot) s) hcircle
    have hsignedSq :
        reflectedRaySignedDistance R t ^ 2 =
          R.value ^ 2 * perpendicularDistanceFactor |t| ^ 2 := by
      rcases le_total 0 t with htNonneg | htNonpos
      · rw [abs_of_nonneg htNonneg]
        dsimp only [reflectedRaySignedDistance, perpendicularDistanceFactor]
        ring
      · rw [abs_of_nonpos htNonpos]
        change
          (R.value * Real.sin t * (Real.cos t - 1)) ^ 2 =
            R.value ^ 2 * (Real.sin (-t) * (1 - Real.cos (-t))) ^ 2
        rw [Real.sin_neg, Real.cos_neg]
        ring
    have hDeltaEq :
        reflectedRayDiscriminant R (smallAngleRadius R phi) t =
          R.value ^ 2 * smallAngleDiscriminant phi t := by
      dsimp only [reflectedRayDiscriminant, smallAngleRadius,
        smallAngleDiscriminant]
      rw [hsignedSq]
      ring
    have hsmallD : 0 ≤ smallAngleDiscriminant phi t := by
      rw [hDeltaEq] at hDeltaNonneg
      nlinarith [sq_pos_of_pos hR]
    have hperpAbsNonneg : 0 ≤ perpendicularDistanceFactor |t| := by
      have hsin : 0 ≤ Real.sin |t| :=
        Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg t)
          (by linarith [ht, Real.pi_pos])
      exact mul_nonneg hsin (sub_nonneg.mpr (Real.cos_le_one _))
    have hperpLe :
        perpendicularDistanceFactor |t| ≤ perpendicularDistanceFactor phi := by
      apply (sq_le_sq₀ hperpAbsNonneg hperpPhiPos.le).1
      dsimp only [smallAngleDiscriminant] at hsmallD
      linarith
    have htPhi : |t| ≤ phi :=
      (perpendicularDistanceStrictMono.2 phi t hphiPos hphiLt ht).1 hperpLe
    have hcanonical :=
      ((smallAngleFirstContainerContact R phi t hR hphiPos hphiLt ht).2.2 G hG).1
        htPhi
    have hsEq : s = smallAngleFirstHitParameter R phi t :=
      (Shared.GeometricOptics.firstContainerContact_unique G ray
        (by simpa [ray] using hcontact) (by simpa [ray] using hcanonical)).1
    have hsLeProjection : s ≤ reflectedRayProjection R t := by
      rw [hsEq]
      dsimp only [smallAngleFirstHitParameter, reflectedRayProjection]
      have hsqrtNonneg : 0 ≤ Real.sqrt (smallAngleDiscriminant phi t) :=
        Real.sqrt_nonneg _
      nlinarith [mul_nonneg hR.le hsqrtNonneg]
    have habsThird : |t| < Real.pi / 3 := by
      linarith
    have hcosHalf : 1 / 2 < Real.cos t := by
      have hanti := Real.strictAntiOn_cos
        (show |t| ∈ Set.Icc (0 : ℝ) Real.pi by
          constructor
          · exact abs_nonneg t
          · linarith [Real.pi_pos])
        (show Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi by
          constructor <;> linarith [Real.pi_pos])
        habsThird
      simpa [Real.cos_pi_div_three, Real.cos_abs] using hanti
    have hfactorLt : reflectedRayProjectionFactor t < 2 * Real.cos t := by
      dsimp only [reflectedRayProjectionFactor]
      nlinarith [sq_nonneg (Real.cos t - 1 / 2)]
    have hprojectionLt :
        reflectedRayProjection R t < 2 * R.value * Real.cos t := by
      dsimp only [reflectedRayProjection]
      have := mul_lt_mul_of_pos_left hfactorLt hR
      nlinarith
    have hrayData := (reflectedDirectionFormula R t hR ht).2
      (smallAngleRadius R phi) G hG
    have hrayPoint (u : ℝ) :
        ray.pointAt u =
          toSharedPoint
            (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) u) := by
      change
        Shared.GeometricOptics.translate ray.origin
            (Shared.GeometricOptics.directionDisplacement u ray.direction.1) =
          toSharedPoint
            (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) u)
      rw [hrayData.1, hrayData.2]
      rfl
    have hnoSecond : Shared.GeometricOptics.HasNoSecondMirrorContact G ray s := by
      intro u huPos huLe hmirrorShared
      have huLt : u < 2 * R.value * Real.cos t :=
        lt_of_le_of_lt (le_trans huLe hsLeProjection) hprojectionLt
      rw [hrayPoint] at hmirrorShared
      have hmirrorLocal :
          OnMirror R
            (rayPoint (mirrorPoint R ⟨t⟩) (reflectedDirectionAt t) u) :=
        ((figure2fSharedBoundaryBridge G R (smallAngleRadius R phi) hG).2 _).2.2.1
          hmirrorShared
      have hroots := ((reflectedRayCircleQuadratics R t hR ht).2.2 u).1
        hmirrorLocal.1
      rcases hroots with huZero | huReturn
      · linarith
      · linarith
    exact ⟨htPhi, hcontact.1, hsLeProjection, hprojectionLt,
      by simpa [ray] using hnoSecond⟩
  rcases (figure2fSharedGeometry_existsUnique R (smallAngleRadius R phi)).2
      ⟨hR, haPos, haLt⟩ with ⟨G₀, hG₀, _hunique⟩
  refine ⟨⟨G₀, hG₀, ?_⟩, hproperty⟩
  intro t ht s Q hcontact
  exact (hproperty G₀ hG₀ t s Q ht hcontact).2.2.2.2

/-- The endpoint ray has a positive tangent first contact and no mirror return. -/
theorem smallAngleLimitingRayTangent
    (R : Length) (phi : ℝ)
    (hR : R.IsPositive) (hphiPos : 0 < phi) (hphiLt : phi < Real.pi / 6) :
    IsLimitingRayTangent R (smallAngleRadius R phi) ⟨phi⟩ ∧
      ∀ G : Shared.GeometricOptics.ConcentratorGeometry,
        Figure2fSharedGeometry G R (smallAngleRadius R phi) →
          let ray := Shared.GeometricOptics.axialReflectedRay G.mirror .lower phi
          let sPhi := reflectedRayProjection R phi
          IncomingRayFirstMeetsMirror G phi ∧
            Shared.GeometricOptics.AcceptedReflectedRay G phi ∧
            ray.origin = toSharedPoint (mirrorPoint R ⟨phi⟩) ∧
            ray.direction.1 = toSharedDirection (reflectedDirectionAt phi) ∧
            Shared.GeometricOptics.IsTangentContainerContact G ray sPhi
              (ray.pointAt sPhi) ∧
            Shared.GeometricOptics.HasNoSecondMirrorContact G ray sPhi := by
  have hphiHalf : |phi| < Real.pi / 2 := by
    rw [abs_of_pos hphiPos]
    linarith [Real.pi_pos]
  have hcut := directShadowCutoffDomain phi hphiPos hphiLt
  have hcutLtPhi : (directShadowCutoff phi).radians < phi := hcut.2.2.2.2.1
  have hone := smallAngleOneReflectionDomain R phi hR hphiPos hphiLt
  have hparameter :
      smallAngleFirstHitParameter R phi phi = reflectedRayProjection R phi := by
    change
      R.value *
          (reflectedRayProjectionFactor phi -
            Real.sqrt
              (perpendicularDistanceFactor phi ^ 2 -
                perpendicularDistanceFactor |phi| ^ 2)) =
        R.value * reflectedRayProjectionFactor phi
    rw [abs_of_pos hphiPos, sub_self, Real.sqrt_zero]
    ring
  have hpackage :
      ∀ G : Shared.GeometricOptics.ConcentratorGeometry,
        Figure2fSharedGeometry G R (smallAngleRadius R phi) →
          let ray := Shared.GeometricOptics.axialReflectedRay G.mirror .lower phi
          let sPhi := reflectedRayProjection R phi
          IncomingRayFirstMeetsMirror G phi ∧
            Shared.GeometricOptics.AcceptedReflectedRay G phi ∧
            ray.origin = toSharedPoint (mirrorPoint R ⟨phi⟩) ∧
            ray.direction.1 = toSharedDirection (reflectedDirectionAt phi) ∧
            Shared.GeometricOptics.IsTangentContainerContact G ray sPhi
              (ray.pointAt sPhi) ∧
            Shared.GeometricOptics.HasNoSecondMirrorContact G ray sPhi := by
    intro G hG
    dsimp
    let ray := Shared.GeometricOptics.axialReflectedRay G.mirror .lower phi
    let sPhi := reflectedRayProjection R phi
    have hincoming : IncomingRayFirstMeetsMirror G phi :=
      ((smallAngleIncomingContactClassification R phi phi hR hphiPos hphiLt
        G hG hphiHalf).2.1).2 ⟨by simpa [abs_of_pos hphiPos], hphiHalf⟩
    have hfirstRaw :=
      ((smallAngleFirstContainerContact R phi phi hR hphiPos hphiLt
        hphiHalf).2.2 G hG).1 (by simp [abs_of_pos hphiPos])
    have hfirst :
        Shared.GeometricOptics.IsFirstContainerContact G ray sPhi
          (ray.pointAt sPhi) := by
      simpa [ray, sPhi, hparameter] using hfirstRaw
    have hregime : Shared.GeometricOptics.InOneReflectionRegime G := by
      intro t ht s Q hcontact
      exact (hone.2 G hG t s Q ht hcontact).2.2.2.2
    have hordered := hone.2 G hG phi sPhi (ray.pointAt sPhi) hphiHalf
      (by simpa [ray] using hfirst)
    have hnoSecond : Shared.GeometricOptics.HasNoSecondMirrorContact G ray sPhi :=
      by simpa [ray] using hordered.2.2.2.2
    rcases hincoming with ⟨hdomain, sMirror, hfirstMirror, hmirror⟩
    have haccepted : Shared.GeometricOptics.AcceptedReflectedRay G phi := by
      exact ⟨hregime, hdomain, sMirror, hfirstMirror, hmirror,
        sPhi, ray.pointAt sPhi, by simpa [ray] using hfirst,
        by simpa [ray] using hnoSecond⟩
    have hDeltaZero :
        reflectedRayDiscriminant R (smallAngleRadius R phi) phi = 0 := by
      dsimp only [reflectedRayDiscriminant, smallAngleRadius,
        reflectedRaySignedDistance, perpendicularDistanceFactor]
      ring
    have hsPhiPos : 0 < sPhi := by
      simpa [sPhi] using hordered.2.1
    rcases reflectedRayDiscriminantCriterion G R (smallAngleRadius R phi) phi
        hG hphiHalf with ⟨_hfactor, _hmiss, _htransverse, htangent, _haccepted⟩
    have htangentContact :
        Shared.GeometricOptics.IsTangentContainerContact G ray sPhi
          (ray.pointAt sPhi) := by
      simpa [ray, sPhi] using (htangent hDeltaZero hsPhiPos).2
    have hrayData := (reflectedDirectionFormula R phi hR hphiHalf).2
      (smallAngleRadius R phi) G hG
    exact ⟨⟨hdomain, sMirror, hfirstMirror, hmirror⟩, haccepted,
      by simpa [ray] using hrayData.1, by simpa [ray] using hrayData.2,
      htangentContact, hnoSecond⟩
  have hphysical := smallAngleRadiusDomain.2 R phi hR hphiPos hphiLt
  rcases (figure2fSharedGeometry_existsUnique R (smallAngleRadius R phi)).2
      ⟨hR, hphysical.1, hphysical.2.1⟩ with ⟨G₀, hG₀, _hunique⟩
  have hp := hpackage G₀ hG₀
  refine ⟨?_, hpackage⟩
  exact ⟨G₀, hG₀, hp.2.1, reflectedRayProjection R phi,
    (Shared.GeometricOptics.axialReflectedRay G₀.mirror .lower phi).pointAt
      (reflectedRayProjection R phi), hp.2.2.2.2.1⟩

/-- The accepted reflected parameters are exactly the shadow-free hit interval. -/
theorem smallAngleStrikingInterval
    (R : Length) (phi : ℝ)
    (hR : R.IsPositive) (hphiPos : 0 < phi) (hphiLt : phi < Real.pi / 6) :
    (∀ t : ℝ,
      ReflectedRayStrikesContainer R (smallAngleRadius R phi) ⟨t⟩ ↔
        (directShadowCutoff phi).radians < |t| ∧ |t| ≤ phi) ∧
      (∀ (G : Shared.GeometricOptics.ConcentratorGeometry) (t : ℝ),
        Figure2fSharedGeometry G R (smallAngleRadius R phi) →
          |t| ≤ (directShadowCutoff phi).radians →
            DirectIncomingAbsorption G t ∧
              ¬ Shared.GeometricOptics.AcceptedReflectedRay G t) ∧
      IsLargestStrikingIncidenceAngle R (smallAngleRadius R phi) ⟨phi⟩ := by
  have hphiHalf : phi < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcut := directShadowCutoffDomain phi hphiPos hphiLt
  have hcutLtPhi : (directShadowCutoff phi).radians < phi := hcut.2.2.2.2.1
  have hone := smallAngleOneReflectionDomain R phi hR hphiPos hphiLt
  have hphysical := smallAngleRadiusDomain.2 R phi hR hphiPos hphiLt
  rcases (figure2fSharedGeometry_existsUnique R (smallAngleRadius R phi)).2
      ⟨hR, hphysical.1, hphysical.2.1⟩ with ⟨G₀, hG₀, _hunique⟩
  have hstrikes : ∀ t : ℝ,
      ReflectedRayStrikesContainer R (smallAngleRadius R phi) ⟨t⟩ ↔
        (directShadowCutoff phi).radians < |t| ∧ |t| ≤ phi := by
    intro t
    constructor
    · rintro ⟨G, hG, hAccepted⟩
      rcases hAccepted with
        ⟨_hregime, hdomain, sMirror, hfirstMirror, hmirror,
          sHit, QHit, hHit, _hNoSecond⟩
      have hincoming : IncomingRayFirstMeetsMirror G t :=
        ⟨hdomain, sMirror, hfirstMirror, hmirror⟩
      have hclassification := smallAngleIncomingContactClassification R phi t
        hR hphiPos hphiLt G hG hdomain
      have hcutLt : (directShadowCutoff phi).radians < |t| :=
        (hclassification.2.1.1 hincoming).1
      have htPhi := (hone.2 G hG t sHit QHit hdomain hHit).1
      exact ⟨hcutLt, htPhi⟩
    · rintro ⟨hcutLt, htPhi⟩
      have hdomain : |t| < Real.pi / 2 := lt_of_le_of_lt htPhi hphiHalf
      have hincoming : IncomingRayFirstMeetsMirror G₀ t :=
        ((smallAngleIncomingContactClassification R phi t hR hphiPos hphiLt
          G₀ hG₀ hdomain).2.1).2 ⟨hcutLt, hdomain⟩
      let ray := Shared.GeometricOptics.axialReflectedRay G₀.mirror .lower t
      let sHit := smallAngleFirstHitParameter R phi t
      have hHit :
          Shared.GeometricOptics.IsFirstContainerContact G₀ ray sHit
            (ray.pointAt sHit) := by
        simpa [ray, sHit] using
          (((smallAngleFirstContainerContact R phi t hR hphiPos hphiLt
            hdomain).2.2 G₀ hG₀).1 htPhi)
      have hregime : Shared.GeometricOptics.InOneReflectionRegime G₀ := by
        intro u hu s Q hcontact
        exact (hone.2 G₀ hG₀ u s Q hu hcontact).2.2.2.2
      have hnoSecond :
          Shared.GeometricOptics.HasNoSecondMirrorContact G₀ ray sHit := by
        simpa [ray] using
          (hone.2 G₀ hG₀ t sHit (ray.pointAt sHit) hdomain
            (by simpa [ray] using hHit)).2.2.2.2
      rcases hincoming with ⟨hdomain', sMirror, hfirstMirror, hmirror⟩
      refine ⟨G₀, hG₀, ?_⟩
      exact ⟨hregime, hdomain', sMirror, hfirstMirror, hmirror,
        sHit, ray.pointAt sHit, by simpa [ray] using hHit,
        by simpa [ray] using hnoSecond⟩
  have hdirect :
      ∀ (G : Shared.GeometricOptics.ConcentratorGeometry) (t : ℝ),
        Figure2fSharedGeometry G R (smallAngleRadius R phi) →
          |t| ≤ (directShadowCutoff phi).radians →
            DirectIncomingAbsorption G t ∧
              ¬ Shared.GeometricOptics.AcceptedReflectedRay G t := by
    intro G t hG htShadow
    have hdomain : |t| < Real.pi / 2 := by
      exact lt_of_le_of_lt htShadow (lt_trans hcutLtPhi hphiHalf)
    have hclassification := smallAngleIncomingContactClassification R phi t
      hR hphiPos hphiLt G hG hdomain
    exact ⟨hclassification.1.2 htShadow,
      ((smallAngleFirstContainerContact R phi t hR hphiPos hphiLt hdomain).2.2
        G hG).2 htShadow⟩
  have hlargest :
      IsLargestStrikingIncidenceAngle R (smallAngleRadius R phi) ⟨phi⟩ := by
    constructor
    · apply (hstrikes phi).2
      simpa [abs_of_pos hphiPos] using And.intro hcutLtPhi (le_refl phi)
    · intro theta htheta
      exact (hstrikes theta.radians).1 htheta |>.2
  exact ⟨hstrikes, hdirect, hlargest⟩

/-- Every angle in the small open interval gives a valid fixed-radius configuration. -/
theorem smallAngleFigure2fConfiguration
    (R : Length) (phi : ℝ)
    (hR : R.IsPositive) (hphiPos : 0 < phi) (hphiLt : phi < Real.pi / 6) :
    Figure2fConfiguration R (smallAngleRadius R phi) ⟨phi⟩ := by
  have hphysical := smallAngleRadiusDomain.2 R phi hR hphiPos hphiLt
  have hone := smallAngleOneReflectionDomain R phi hR hphiPos hphiLt
  have hstriking := smallAngleStrikingInterval R phi hR hphiPos hphiLt
  exact ⟨hR, hphysical.1, hphysical.2.1, hphysical.2.2,
    hone.1, hstriking.2.2⟩

/-! ## Target -/

/--
Answer-free B.1 contract: valid Figure 2f geometry uniquely characterizes one
family-wide coefficient pair, which also satisfies the displayed relation for
the particular valid cooker.
-/
theorem problem_IPhO_2026_2_B_1
    (R a : Length) (thetaMax : Angle)
    (hFigure : Figure2fConfiguration R a thetaMax) :
    ∃! coefficients : CoefficientPair,
      CoefficientSolution R coefficients ∧
        SatisfiesDisplayedRelation a thetaMax coefficients := by
  have hradiusFormula :
      ∀ (A : Length) (theta : Angle),
        Figure2fConfiguration R A theta →
          A.value = R.value * Real.sin theta.radians *
            (1 - Real.cos theta.radians) := by
    intro A theta hConfig
    have hsq := figure2fConfiguration_tangentDistance R A theta hConfig
    have hangle := hConfig.2.2.2.1
    have hsinPos : 0 < Real.sin theta.radians :=
      Real.sin_pos_of_pos_of_lt_pi hangle.1
        (lt_trans hangle.2 (by linarith [Real.pi_pos]))
    have hcosLtOne : Real.cos theta.radians < 1 := by
      have hanti := Real.strictAntiOn_cos
        (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi by
          constructor <;> linarith [Real.pi_pos])
        (show theta.radians ∈ Set.Icc (0 : ℝ) Real.pi by
          constructor
          · exact hangle.1.le
          · linarith [hangle.2, Real.pi_pos])
        hangle.1
      simpa using hanti
    have htargetPos :
        0 < R.value * Real.sin theta.radians *
          (1 - Real.cos theta.radians) :=
      mul_pos (mul_pos hConfig.1 hsinPos) (by linarith)
    have hsinSq :
        Real.sin theta.radians ^ 2 = 1 - Real.cos theta.radians ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq theta.radians]
    have hdet :
        displacementDetDirection
            (displacement (mirrorPoint R theta) (containerCenter R))
            (reflectedDirectionAt theta.radians) =
          -(R.value * Real.sin theta.radians *
            (1 - Real.cos theta.radians)) := by
      change
        (R.value * Real.sin theta.radians - 0) *
              Real.cos (2 * theta.radians) -
            (-R.value * Real.cos theta.radians - (-(R.value / 2))) *
              (-Real.sin (2 * theta.radians)) =
          -(R.value * Real.sin theta.radians *
            (1 - Real.cos theta.radians))
      rw [Real.sin_two_mul, Real.cos_two_mul]
      ring_nf
    rw [hdet] at hsq
    have hAPos : 0 < A.value := hConfig.2.1
    apply (sq_eq_sq₀ hAPos.le htargetPos.le).1
    nlinarith [hsq]
  let canonical : CoefficientPair :=
    { alpha := ⟨R.value⟩
      beta := ⟨-(R.value / 2)⟩ }
  have hcanonical : CoefficientSolution R canonical := by
    intro A theta hConfig
    unfold SatisfiesDisplayedRelation
    change A.value =
      R.value * Real.sin theta.radians +
        (-(R.value / 2)) * Real.sin (2 * theta.radians)
    rw [hradiusFormula A theta hConfig, Real.sin_two_mul]
    ring
  refine ⟨canonical, ⟨hcanonical, hcanonical a thetaMax hFigure⟩, ?_⟩
  intro coefficients hcoefficients
  have hpi : 0 < Real.pi := Real.pi_pos
  let phi₁ : ℝ := Real.pi / 12
  let phi₂ : ℝ := Real.pi / 8
  have hphi₁Pos : 0 < phi₁ := by dsimp [phi₁]; linarith
  have hphi₁Lt : phi₁ < Real.pi / 6 := by dsimp [phi₁]; linarith
  have hphi₂Pos : 0 < phi₂ := by dsimp [phi₂]; linarith
  have hphi₂Lt : phi₂ < Real.pi / 6 := by dsimp [phi₂]; linarith
  have hequation (x : ℝ) (hxPos : 0 < x) (hxLt : x < Real.pi / 6) :
      (coefficients.alpha.value - R.value) +
          2 * (coefficients.beta.value + R.value / 2) * Real.cos x = 0 := by
    have hConfig := smallAngleFigure2fConfiguration R x hFigure.1 hxPos hxLt
    have hgiven := hcoefficients.1 (smallAngleRadius R x) ⟨x⟩ hConfig
    have hcanon := hcanonical (smallAngleRadius R x) ⟨x⟩ hConfig
    unfold SatisfiesDisplayedRelation at hgiven hcanon
    rw [Real.sin_two_mul] at hgiven hcanon
    have hsinPos : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hxPos (by linarith [hxLt, hpi])
    have hproduct :
        Real.sin x * ((coefficients.alpha.value - R.value) +
          2 * (coefficients.beta.value + R.value / 2) * Real.cos x) = 0 := by
      change (smallAngleRadius R x).value =
        coefficients.alpha.value * Real.sin x +
          coefficients.beta.value * (2 * Real.sin x * Real.cos x) at hgiven
      change (smallAngleRadius R x).value =
        R.value * Real.sin x +
          (-(R.value / 2)) * (2 * Real.sin x * Real.cos x) at hcanon
      nlinarith
    exact (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt hsinPos)
  have heq₁ := hequation phi₁ hphi₁Pos hphi₁Lt
  have heq₂ := hequation phi₂ hphi₂Pos hphi₂Lt
  have hphiLt : phi₁ < phi₂ := by dsimp [phi₁, phi₂]; linarith
  have hcosLt : Real.cos phi₂ < Real.cos phi₁ := by
    exact Real.strictAntiOn_cos
      (show phi₁ ∈ Set.Icc (0 : ℝ) Real.pi by
        constructor <;> linarith [hphi₁Pos, hphi₁Lt, hpi])
      (show phi₂ ∈ Set.Icc (0 : ℝ) Real.pi by
        constructor <;> linarith [hphi₂Pos, hphi₂Lt, hpi])
      hphiLt
  have hbetaProduct :
      (coefficients.beta.value + R.value / 2) *
        (Real.cos phi₁ - Real.cos phi₂) = 0 := by
    nlinarith [heq₁, heq₂]
  have hcosDiffNe : Real.cos phi₁ - Real.cos phi₂ ≠ 0 := by
    nlinarith
  have hbetaZero : coefficients.beta.value + R.value / 2 = 0 :=
    (mul_eq_zero.mp hbetaProduct).resolve_right hcosDiffNe
  have hbeta : coefficients.beta.value = -(R.value / 2) := by linarith
  have halpha : coefficients.alpha.value = R.value := by
    rw [hbeta] at heq₁
    nlinarith [heq₁]
  apply CoefficientPair.ext
  · apply Length.ext
    simpa [canonical] using halpha
  · apply Length.ext
    simpa [canonical] using hbeta

end
end ProblemIPhO2026_2_B_1
end Ipho2026Gpt56solBlind
