import Ipho2026Gpt56solBlind.Shared.ISQDimensions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic

/-!
# Shared geometric optics

The analytic kernel in this file uses real coherent-SI coordinates.  Physical
lengths and powers cross the explicitly unit-indexed ISQ boundary supplied by
`Shared.ISQDimensions`; no scalar kernel coordinate is treated as an ISQ
quantity without that conversion.
-/

noncomputable section

namespace Ipho2026Gpt56solBlind.Shared.GeometricOptics

/-! ## Scalar coordinates and the typed boundary -/

/-- A signed coherent-SI real coordinate used in a length role. -/
abbrev Length := ℝ

/-- Strict positivity for a scalar length coordinate. -/
def IsPositiveLength (L : Length) : Prop := 0 < L

/-- A point in the scalar planar kernel. -/
structure Point2 where
  x : Length
  y : Length
deriving DecidableEq

/-- A displacement in the scalar planar kernel. -/
structure Displacement2 where
  x : Length
  y : Length
deriving DecidableEq

/-- Reconstruct an ISQ quantity from its coherent-SI real coordinate. -/
def quantityFromSICoordinate (u : SIUnitChoices)
    (d : Dimension ISQDimensionBase) (x : ℝ) : ISQDimensions.Quantity d :=
  ⟨x / (↑(SIUnitChoices.dimScale u SIUnitChoices.SI d) : ℝ)⟩

/-- Reconstruction and conversion are inverse at each fixed ISQ dimension. -/
theorem quantityFromSICoordinate_roundtrip (u : SIUnitChoices)
    (d : Dimension ISQDimensionBase) (x : ℝ) (q : ISQDimensions.Quantity d) :
    ISQDimensions.coordinateInSI u (quantityFromSICoordinate u d x) = x ∧
      quantityFromSICoordinate u d (ISQDimensions.coordinateInSI u q) = q ∧
      ISQDimensions.quantityInSI u (quantityFromSICoordinate u d x) =
        (⟨x⟩ : ISQDimensions.Quantity d) := by
  let scale : ℝ := ↑(SIUnitChoices.dimScale u SIUnitChoices.SI d)
  have hscale_pos : 0 < scale := by
    exact_mod_cast ISQDimensions.dimScaleToSI_pos u d
  have hscale : scale ≠ 0 := ne_of_gt hscale_pos
  refine ⟨?_, ?_, ?_⟩
  · change scale * (x / scale) = x
    exact mul_div_cancel₀ x hscale
  · apply WithDim.ext
    change (scale * q.val) / scale = q.val
    exact mul_div_cancel_left₀ q.val hscale
  · apply WithDim.ext
    change scale * (x / scale) = x
    exact mul_div_cancel₀ x hscale

/-- Send a typed length to the scalar coherent-SI kernel. -/
def lengthCoordinateInSI (u : SIUnitChoices) (ℓ : ISQDimensions.Length) : Length :=
  ISQDimensions.coordinateInSI u ℓ

/-- Lift a scalar coherent-SI length coordinate to a typed length. -/
def lengthFromSICoordinate (u : SIUnitChoices) (x : Length) : ISQDimensions.Length :=
  quantityFromSICoordinate u ISQDimensions.lengthDimension x

/-- Equality, positivity, and reconstruction are faithful at the length boundary. -/
theorem lengthCoordinateInSI_faithful (u : SIUnitChoices)
    (ℓ₁ ℓ₂ ℓ : ISQDimensions.Length) (x : Length) :
    (lengthCoordinateInSI u ℓ₁ = lengthCoordinateInSI u ℓ₂ ↔ ℓ₁ = ℓ₂) ∧
      (IsPositiveLength (lengthCoordinateInSI u ℓ) ↔ 0 < ℓ.val) ∧
      lengthCoordinateInSI u (lengthFromSICoordinate u x) = x := by
  let scale : ℝ :=
    ↑(SIUnitChoices.dimScale u SIUnitChoices.SI ISQDimensions.lengthDimension)
  have hscale_pos : 0 < scale := by
    exact_mod_cast
      ISQDimensions.dimScaleToSI_pos u ISQDimensions.lengthDimension
  refine ⟨?_, ?_, ?_⟩
  · simpa only [lengthCoordinateInSI] using
      ISQDimensions.coordinateInSI_eq_iff u ℓ₁ ℓ₂
  · change (0 < scale * ℓ.val ↔ 0 < ℓ.val)
    exact mul_pos_iff_of_pos_left hscale_pos
  · exact (quantityFromSICoordinate_roundtrip u
      ISQDimensions.lengthDimension x (⟨0⟩ : ISQDimensions.Length)).1

/-- An ISQ-typed planar point.  Components are signed coordinates. -/
structure PhysicalPoint2 where
  x : ISQDimensions.Length
  y : ISQDimensions.Length

/-- An ISQ-typed planar displacement. -/
structure PhysicalDisplacement2 where
  x : ISQDimensions.Length
  y : ISQDimensions.Length

/-- Componentwise coherent-SI representation of a physical point. -/
def physicalPointCoordinateInSI (u : SIUnitChoices) (P : PhysicalPoint2) : Point2 :=
  { x := lengthCoordinateInSI u P.x
    y := lengthCoordinateInSI u P.y }

/-- Componentwise coherent-SI representation of a physical displacement. -/
def physicalDisplacementCoordinateInSI (u : SIUnitChoices)
    (w : PhysicalDisplacement2) : Displacement2 :=
  { x := lengthCoordinateInSI u w.x
    y := lengthCoordinateInSI u w.y }

/-- Lift a scalar point componentwise through the inverse length boundary. -/
def physicalPointFromKernel (u : SIUnitChoices) (P : Point2) : PhysicalPoint2 :=
  { x := lengthFromSICoordinate u P.x
    y := lengthFromSICoordinate u P.y }

/-- Lift a scalar displacement componentwise through the inverse length boundary. -/
def physicalDisplacementFromKernel (u : SIUnitChoices)
    (w : Displacement2) : PhysicalDisplacement2 :=
  { x := lengthFromSICoordinate u w.x
    y := lengthFromSICoordinate u w.y }

/-- The physical-point wrapper is injective and inverse in both directions. -/
theorem physicalPointCoordinateInSI_faithful (u : SIUnitChoices) :
    Function.Injective (physicalPointCoordinateInSI u) ∧
      (∀ P, physicalPointFromKernel u (physicalPointCoordinateInSI u P) = P) ∧
      (∀ P, physicalPointCoordinateInSI u (physicalPointFromKernel u P) = P) := by
  have hfrom (q : ISQDimensions.Length) :
      lengthFromSICoordinate u (lengthCoordinateInSI u q) = q := by
    exact (quantityFromSICoordinate_roundtrip u ISQDimensions.lengthDimension
      (ISQDimensions.coordinateInSI u q) q).2.1
  have hto (x : Length) :
      lengthCoordinateInSI u (lengthFromSICoordinate u x) = x := by
    exact (quantityFromSICoordinate_roundtrip u ISQDimensions.lengthDimension x
      (⟨0⟩ : ISQDimensions.Length)).1
  refine ⟨?_, ?_, ?_⟩
  · intro P Q hPQ
    have hx : P.x = Q.x :=
      (ISQDimensions.coordinateInSI_eq_iff u P.x Q.x).mp
        (congrArg Point2.x hPQ)
    have hy : P.y = Q.y :=
      (ISQDimensions.coordinateInSI_eq_iff u P.y Q.y).mp
        (congrArg Point2.y hPQ)
    cases P
    cases Q
    simp_all
  · intro P
    cases P
    simp [physicalPointFromKernel, physicalPointCoordinateInSI, hfrom]
  · intro P
    cases P
    simp [physicalPointFromKernel, physicalPointCoordinateInSI, hto]

/-- The physical-displacement wrapper is injective and inverse in both directions. -/
theorem physicalDisplacementCoordinateInSI_faithful (u : SIUnitChoices) :
    Function.Injective (physicalDisplacementCoordinateInSI u) ∧
      (∀ w, physicalDisplacementFromKernel u
          (physicalDisplacementCoordinateInSI u w) = w) ∧
      (∀ w, physicalDisplacementCoordinateInSI u
          (physicalDisplacementFromKernel u w) = w) := by
  have hfrom (q : ISQDimensions.Length) :
      lengthFromSICoordinate u (lengthCoordinateInSI u q) = q := by
    exact (quantityFromSICoordinate_roundtrip u ISQDimensions.lengthDimension
      (ISQDimensions.coordinateInSI u q) q).2.1
  have hto (x : Length) :
      lengthCoordinateInSI u (lengthFromSICoordinate u x) = x := by
    exact (quantityFromSICoordinate_roundtrip u ISQDimensions.lengthDimension x
      (⟨0⟩ : ISQDimensions.Length)).1
  refine ⟨?_, ?_, ?_⟩
  · intro w z hwz
    have hx : w.x = z.x :=
      (ISQDimensions.coordinateInSI_eq_iff u w.x z.x).mp
        (congrArg Displacement2.x hwz)
    have hy : w.y = z.y :=
      (ISQDimensions.coordinateInSI_eq_iff u w.y z.y).mp
        (congrArg Displacement2.y hwz)
    cases w
    cases z
    simp_all
  · intro w
    cases w
    simp [physicalDisplacementFromKernel, physicalDisplacementCoordinateInSI,
      hfrom]
  · intro w
    cases w
    simp [physicalDisplacementFromKernel, physicalDisplacementCoordinateInSI,
      hto]

/-! ## Directions, rays, and lines -/

/-- A dimensionless planar direction. -/
structure Direction2 where
  x : ℝ
  y : ℝ
deriving DecidableEq

/-- The scalar displacement from `P` to `Q`. -/
def displacement (P Q : Point2) : Displacement2 :=
  { x := Q.x - P.x, y := Q.y - P.y }

/-- Translate a scalar point by a scalar displacement. -/
def translate (P : Point2) (w : Displacement2) : Point2 :=
  { x := P.x + w.x, y := P.y + w.y }

/-- Turn a direction into a displacement by a scalar path length. -/
def directionDisplacement (s : Length) (d : Direction2) : Displacement2 :=
  { x := s * d.x, y := s * d.y }

/-- Coherent-SI conversion respects the affine operations used by the kernel. -/
theorem physicalCoordinates_affine (u : SIUnitChoices)
    (P Q : PhysicalPoint2) (w : PhysicalDisplacement2)
    (ℓ : ISQDimensions.Length) (d : Direction2) :
    let pq : PhysicalDisplacement2 :=
      { x := ⟨Q.x.val - P.x.val⟩, y := ⟨Q.y.val - P.y.val⟩ }
    let pw : PhysicalPoint2 :=
      { x := ⟨P.x.val + w.x.val⟩, y := ⟨P.y.val + w.y.val⟩ }
    let ℓd : PhysicalDisplacement2 :=
      { x := ⟨ℓ.val * d.x⟩, y := ⟨ℓ.val * d.y⟩ }
    physicalDisplacementCoordinateInSI u pq =
        displacement (physicalPointCoordinateInSI u P)
          (physicalPointCoordinateInSI u Q) ∧
      physicalPointCoordinateInSI u pw =
        translate (physicalPointCoordinateInSI u P)
          (physicalDisplacementCoordinateInSI u w) ∧
      physicalDisplacementCoordinateInSI u ℓd =
        directionDisplacement (lengthCoordinateInSI u ℓ) d := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · congr 1 <;>
      simp [physicalDisplacementCoordinateInSI, physicalPointCoordinateInSI,
        lengthCoordinateInSI, ISQDimensions.coordinateInSI, displacement] <;>
      ring_nf <;> simp
  · congr 1 <;>
      simp [physicalPointCoordinateInSI, physicalDisplacementCoordinateInSI,
        lengthCoordinateInSI, ISQDimensions.coordinateInSI, translate] <;>
      ring_nf <;> simp
  · congr 1 <;>
      simp [physicalDisplacementCoordinateInSI, lengthCoordinateInSI,
        ISQDimensions.coordinateInSI, directionDisplacement] <;>
      ring_nf <;> simp

/-- Scale a direction by a dimensionless scalar. -/
def scaleDirection (c : ℝ) (d : Direction2) : Direction2 :=
  { x := c * d.x, y := c * d.y }

/-- Componentwise direction subtraction. -/
def subtractDirection (u v : Direction2) : Direction2 :=
  { x := u.x - v.x, y := u.y - v.y }

/-- Euclidean dot product of dimensionless directions. -/
def directionDot (u v : Direction2) : ℝ := u.x * v.x + u.y * v.y

/-- Oriented determinant of two dimensionless directions. -/
def directionDet (u v : Direction2) : ℝ := u.x * v.y - u.y * v.x

/-- Dot product of a scalar displacement with a dimensionless direction. -/
def displacementDirectionDot (w : Displacement2) (d : Direction2) : Length :=
  w.x * d.x + w.y * d.y

/-- Oriented determinant of a displacement and a direction. -/
def displacementDirectionDet (w : Displacement2) (d : Direction2) : Length :=
  w.x * d.y - w.y * d.x

/-- Squared norm of a direction. -/
def directionNormSq (d : Direction2) : ℝ := directionDot d d

/-- Squared scalar length of a displacement. -/
def displacementNormSq (w : Displacement2) : ℝ := w.x ^ 2 + w.y ^ 2

/-- A direction normalized to squared norm one. -/
def UnitDirection := {d : Direction2 // directionNormSq d = 1}

namespace UnitDirection

/-- A unit direction cannot have both components zero. -/
theorem ne_zero (d : UnitDirection) : d.1 ≠ ({ x := 0, y := 0 } : Direction2) := by
  intro hd
  have hnorm := d.2
  rw [hd] at hnorm
  norm_num [directionNormSq, directionDot] at hnorm

end UnitDirection

/-- Positive quarter-turn of a planar direction. -/
def quarterTurn (n : Direction2) : Direction2 := { x := -n.y, y := n.x }

/-- A unit normal and its quarter-turn form an orthonormal pair. -/
theorem quarterTurn_orthonormal (n : UnitDirection) :
    directionNormSq (quarterTurn n.1) = 1 ∧
      directionDot n.1 (quarterTurn n.1) = 0 := by
  rcases n with ⟨⟨nx, ny⟩, hn⟩
  change nx * nx + ny * ny = 1 at hn
  constructor
  · change (-ny) * (-ny) + nx * nx = 1
    ring_nf
    nlinarith [hn]
  · change nx * (-ny) + ny * nx = 0
    ring

/-- A ray with a point origin and unit forward direction. -/
structure ForwardRay where
  origin : Point2
  direction : UnitDirection

namespace ForwardRay

/-- Algebraic ray evaluation at a signed path coordinate. -/
def pointAt (r : ForwardRay) (s : Length) : Point2 :=
  translate r.origin (directionDisplacement s r.direction.1)

end ForwardRay

/-- Membership in the nonnegative propagation half of a ray. -/
def OnForwardRay (r : ForwardRay) (Q : Point2) : Prop :=
  ∃ s : Length, 0 ≤ s ∧ Q = r.pointAt s

/-- A supporting line with an anchor and a unit orientation. -/
structure OrientedLine where
  anchor : Point2
  direction : UnitDirection

/-- Membership in an oriented supporting line, with signed path coordinate. -/
def OnOrientedLine (line : OrientedLine) (Q : Point2) : Prop :=
  ∃ s : Length, Q = translate line.anchor (directionDisplacement s line.direction.1)

/-- Slope and vertical-intercept coordinates for a nonvertical line. -/
structure LineCoefficients where
  slope : ℝ
  intercept : Length
deriving DecidableEq

/-- The component equations saying that coefficients describe a line. -/
def DescribesNonverticalLine (P : Point2) (d : Direction2)
    (c : LineCoefficients) : Prop :=
  d.x ≠ 0 ∧ d.y = c.slope * d.x ∧ P.y = c.slope * P.x + c.intercept

/-- Canonical slope and intercept for the line through `P` in direction `d`. -/
def nonverticalLineCoefficients (P : Point2) (d : Direction2) : LineCoefficients :=
  { slope := d.y / d.x
    intercept := P.y - (d.y / d.x) * P.x }

/-- A nonvertical point-direction line has exactly one coefficient pair. -/
theorem existsUnique_lineCoefficients (P : Point2) (d : Direction2)
    (hd : d.x ≠ 0) :
    ∃! c : LineCoefficients, DescribesNonverticalLine P d c := by
  refine ⟨nonverticalLineCoefficients P d, ?_, ?_⟩
  · refine ⟨hd, ?_, ?_⟩
    · exact (div_mul_cancel₀ d.y hd).symm
    · simp [nonverticalLineCoefficients]
  · intro c hc
    rcases hc with ⟨_, hdir, hpoint⟩
    have hslope : c.slope = d.y / d.x := by
      apply (eq_div_iff hd).2
      exact hdir.symm
    cases c with
    | mk slope intercept =>
        simp only [nonverticalLineCoefficients, LineCoefficients.mk.injEq]
        refine ⟨hslope, ?_⟩
        dsimp at hpoint hslope ⊢
        rw [← hslope]
        linarith

/-! ## Circles, oriented semicircles, and ordered first contact -/

/-- A scalar circle with strictly positive radius. -/
structure Circle where
  center : Point2
  radius : Length
  radius_pos : IsPositiveLength radius

/-- A typed circle represented relative to one source unit choice. -/
structure PhysicalCircle (u : SIUnitChoices) where
  center : PhysicalPoint2
  radius : ISQDimensions.Length
  radius_pos : 0 < ISQDimensions.coordinateInSI u radius

/-- Scalar coherent-SI representation of a typed circle. -/
def physicalCircleCoordinateInSI (u : SIUnitChoices) (c : PhysicalCircle u) : Circle :=
  { center := physicalPointCoordinateInSI u c.center
    radius := lengthCoordinateInSI u c.radius
    radius_pos := c.radius_pos }

/-- Circle scalarization is injective and every kernel circle has one typed lift. -/
theorem physicalCircleCoordinateInSI_injective (u : SIUnitChoices) :
    Function.Injective (physicalCircleCoordinateInSI u) ∧
      ∀ c : Circle, ∃! pc : PhysicalCircle u,
        physicalCircleCoordinateInSI u pc = c := by
  have hpoint_inj := (physicalPointCoordinateInSI_faithful u).1
  have hpoint_from := (physicalPointCoordinateInSI_faithful u).2.2
  have hradius (x : Length) :
      lengthCoordinateInSI u (lengthFromSICoordinate u x) = x := by
    exact (quantityFromSICoordinate_roundtrip u ISQDimensions.lengthDimension x
      (⟨0⟩ : ISQDimensions.Length)).1
  have hinj : Function.Injective (physicalCircleCoordinateInSI u) := by
    intro c₁ c₂ h
    have hcenter : c₁.center = c₂.center := by
      apply hpoint_inj
      exact congrArg Circle.center h
    have hradius : c₁.radius = c₂.radius :=
      (ISQDimensions.coordinateInSI_eq_iff u c₁.radius c₂.radius).mp
        (congrArg Circle.radius h)
    cases c₁
    cases c₂
    simpa only [PhysicalCircle.mk.injEq] using And.intro hcenter hradius
  refine ⟨hinj, ?_⟩
  intro c
  let pc : PhysicalCircle u :=
    { center := physicalPointFromKernel u c.center
      radius := lengthFromSICoordinate u c.radius
      radius_pos := by
        change 0 < lengthCoordinateInSI u (lengthFromSICoordinate u c.radius)
        rw [hradius]
        exact c.radius_pos }
  have hpc : physicalCircleCoordinateInSI u pc = c := by
    cases c with
    | mk center radius radius_pos =>
        simp only [physicalCircleCoordinateInSI, pc, Circle.mk.injEq]
        exact ⟨hpoint_from center, hradius radius⟩
  refine ⟨pc, hpc, ?_⟩
  intro pc' hpc'
  apply hinj
  rw [hpc', hpc]

/-- A point lies on a circle boundary. -/
def OnCircle (c : Circle) (P : Point2) : Prop :=
  displacementNormSq (displacement c.center P) = c.radius ^ 2

/-- A point lies in a circle's closed disk. -/
def InClosedDisk (c : Circle) (P : Point2) : Prop :=
  displacementNormSq (displacement c.center P) ≤ c.radius ^ 2

/-- Choice of upper or lower vertical orientation. -/
inductive VerticalOrientation
  | upper
  | lower
deriving DecidableEq

/-- Sign attached to a vertical orientation. -/
def orientationSign : VerticalOrientation → ℝ
  | .upper => 1
  | .lower => -1

/-- Unit axial direction selected by the vertical orientation. -/
def axisDirection (o : VerticalOrientation) : UnitDirection :=
  ⟨{ x := 0, y := orientationSign o }, by
    cases o <;> norm_num [directionNormSq, directionDot, orientationSign]⟩

/-- The orientation sign is nonzero, squares to one, and gives a unit axis. -/
theorem orientationSign_sq (o : VerticalOrientation) :
    orientationSign o ≠ 0 ∧ orientationSign o ^ 2 = 1 ∧
      directionNormSq (axisDirection o).1 = 1 := by
  cases o <;>
    norm_num [orientationSign, axisDirection, directionNormSq, directionDot]

/-- Which optical component owns the two diameter rims. -/
inductive RimConvention
  | aperture
  | mirror
deriving DecidableEq

/-- An oriented semicircle with an independent rim convention. -/
structure Semicircle where
  circle : Circle
  orientation : VerticalOrientation
  rims : RimConvention

/-- Open half-disk interior. -/
def InSemicircleInterior (s : Semicircle) (P : Point2) : Prop :=
  orientationSign s.orientation * (P.y - s.circle.center.y) > 0 ∧
    displacementNormSq (displacement s.circle.center P) < s.circle.radius ^ 2

/-- Reflecting circular arc, with strictness determined by rim ownership. -/
def OnReflectingArc (s : Semicircle) (P : Point2) : Prop :=
  OnCircle s.circle P ∧
    match s.rims with
    | .aperture => orientationSign s.orientation * (P.y - s.circle.center.y) > 0
    | .mirror => orientationSign s.orientation * (P.y - s.circle.center.y) ≥ 0

/-- Diameter aperture, with strictness determined by rim ownership. -/
def OnAperture (s : Semicircle) (P : Point2) : Prop :=
  P.y = s.circle.center.y ∧
    match s.rims with
    | .aperture => |P.x - s.circle.center.x| ≤ s.circle.radius
    | .mirror => |P.x - s.circle.center.x| < s.circle.radius

/-- Union of the reflecting arc and diameter aperture. -/
def OnSemicircleBoundary (s : Semicircle) (P : Point2) : Prop :=
  OnReflectingArc s P ∨ OnAperture s P

/-- The two optical boundary pieces are disjoint and cover the geometric boundary. -/
theorem boundary_partition (s : Semicircle) (P : Point2) :
    ¬(OnReflectingArc s P ∧ OnAperture s P) ∧
      (OnSemicircleBoundary s P ↔
        (OnCircle s.circle P ∧
            orientationSign s.orientation * (P.y - s.circle.center.y) ≥ 0) ∨
          (P.y = s.circle.center.y ∧
            |P.x - s.circle.center.x| ≤ s.circle.radius)) := by
  have circle_abs (hcircle : OnCircle s.circle P)
      (hy : P.y = s.circle.center.y) :
      |P.x - s.circle.center.x| = s.circle.radius := by
    have hsquare :
        (P.x - s.circle.center.x) ^ 2 = s.circle.radius ^ 2 := by
      simpa [OnCircle, displacementNormSq, displacement, hy] using hcircle
    apply (sq_eq_sq₀ (abs_nonneg (P.x - s.circle.center.x))
      (le_of_lt s.circle.radius_pos)).mp
    simpa only [sq_abs] using hsquare
  have abs_circle (hy : P.y = s.circle.center.y)
      (habs : |P.x - s.circle.center.x| = s.circle.radius) :
      OnCircle s.circle P := by
    have hsquare := congrArg (fun z : ℝ => z ^ 2) habs
    simp only [sq_abs] at hsquare
    simpa [OnCircle, displacementNormSq, displacement, hy] using hsquare
  cases hrims : s.rims
  · simp only [OnReflectingArc, OnAperture, OnSemicircleBoundary, hrims]
    constructor
    · rintro ⟨⟨_, hside⟩, ⟨hy, _⟩⟩
      rw [hy, sub_self, mul_zero] at hside
      linarith
    · constructor
      · rintro (hcurve | hdiameter)
        · exact Or.inl ⟨hcurve.1, le_of_lt hcurve.2⟩
        · exact Or.inr hdiameter
      · rintro (hcurve | hdiameter)
        · by_cases hside :
              0 < orientationSign s.orientation *
                (P.y - s.circle.center.y)
          · exact Or.inl ⟨hcurve.1, hside⟩
          · have hzero :
                orientationSign s.orientation *
                    (P.y - s.circle.center.y) = 0 :=
              le_antisymm (le_of_not_gt hside) hcurve.2
            have hdiff : P.y - s.circle.center.y = 0 :=
              (mul_eq_zero.mp hzero).resolve_left
                (orientationSign_sq s.orientation).1
            have hy : P.y = s.circle.center.y := sub_eq_zero.mp hdiff
            exact Or.inr ⟨hy, (circle_abs hcurve.1 hy).le⟩
        · exact Or.inr hdiameter
  · simp only [OnReflectingArc, OnAperture, OnSemicircleBoundary, hrims]
    constructor
    · rintro ⟨⟨hcircle, _⟩, ⟨hy, habs⟩⟩
      have heq := circle_abs hcircle hy
      linarith
    · constructor
      · rintro (hcurve | hdiameter)
        · exact Or.inl hcurve
        · exact Or.inr ⟨hdiameter.1, le_of_lt hdiameter.2⟩
      · rintro (hcurve | hdiameter)
        · exact Or.inl hcurve
        · by_cases hstrict :
              |P.x - s.circle.center.x| < s.circle.radius
          · exact Or.inr ⟨hdiameter.1, hstrict⟩
          · have habs :
                |P.x - s.circle.center.x| = s.circle.radius :=
              le_antisymm hdiameter.2 (le_of_not_gt hstrict)
            refine Or.inl ⟨abs_circle hdiameter.1 habs, ?_⟩
            rw [hdiameter.1, sub_self, mul_zero]

/-- The open half-disk interior and optical boundary are disjoint. -/
theorem interior_disjoint_boundary (s : Semicircle) (P : Point2) :
    ¬(InSemicircleInterior s P ∧ OnSemicircleBoundary s P) := by
  rintro ⟨hinterior, hboundary⟩
  rcases hinterior with ⟨hside, hdisk⟩
  rcases hboundary with hcurve | hdiameter
  · have hcircle := hcurve.1
    unfold OnCircle at hcircle
    linarith
  · have hy := hdiameter.1
    rw [hy, sub_self, mul_zero] at hside
    linarith

/-- A positive, ordered first contact of a ray with a boundary. -/
def IsFirstForwardBoundaryContact (U B : Point2 → Prop) (r : ForwardRay)
    (s : Length) (Q : Point2) : Prop :=
  0 < s ∧ Q = r.pointAt s ∧ B Q ∧
    ∀ u : Length, 0 < u → u < s → U (r.pointAt u)

/-- Disjoint propagation region and boundary make an ordered first contact unique. -/
theorem firstForwardBoundaryContact_unique (U B : Point2 → Prop)
    (hdisjoint : ∀ P, U P → ¬ B P) (r : ForwardRay)
    {s₁ s₂ : Length} {Q₁ Q₂ : Point2}
    (h₁ : IsFirstForwardBoundaryContact U B r s₁ Q₁)
    (h₂ : IsFirstForwardBoundaryContact U B r s₂ Q₂) :
    s₁ = s₂ ∧ Q₁ = Q₂ := by
  rcases h₁ with ⟨hs₁, hQ₁, hB₁, hbefore₁⟩
  rcases h₂ with ⟨hs₂, hQ₂, hB₂, hbefore₂⟩
  have h₁₂ : s₁ ≤ s₂ := by
    by_contra hnot
    have hlt : s₂ < s₁ := lt_of_not_ge hnot
    have hU := hbefore₁ s₂ hs₂ hlt
    have hB : B (r.pointAt s₂) := by simpa only [hQ₂] using hB₂
    exact (hdisjoint _ hU) hB
  have h₂₁ : s₂ ≤ s₁ := by
    by_contra hnot
    have hlt : s₁ < s₂ := lt_of_not_ge hnot
    have hU := hbefore₂ s₁ hs₁ hlt
    have hB : B (r.pointAt s₁) := by simpa only [hQ₁] using hB₁
    exact (hdisjoint _ hU) hB
  have hs : s₁ = s₂ := le_antisymm h₁₂ h₂₁
  refine ⟨hs, ?_⟩
  rw [hQ₁, hQ₂, hs]

/-! ## Specular reflection -/

/-- Specular reflection expressed by tangential and normal components. -/
def IsSpecularReflection (i n o : UnitDirection) : Prop :=
  directionDot o.1 (quarterTurn n.1) = directionDot i.1 (quarterTurn n.1) ∧
    directionDot o.1 n.1 = -directionDot i.1 n.1

/-- Vector formula for reflection in a unit normal. -/
def reflectedDirection (i : Direction2) (n : UnitDirection) : Direction2 :=
  subtractDirection i (scaleDirection (2 * directionDot i n.1) n.1)

/-- The vector formula preserves the tangent component and reverses the normal one. -/
theorem reflectedDirection_components (i : Direction2) (n : UnitDirection) :
    directionDot (reflectedDirection i n) (quarterTurn n.1) =
        directionDot i (quarterTurn n.1) ∧
      directionDot (reflectedDirection i n) n.1 = -directionDot i n.1 := by
  have horthogonal : directionDot n.1 (quarterTurn n.1) = 0 :=
    (quarterTurn_orthonormal n).2
  have hunit : directionDot n.1 n.1 = 1 := n.2
  constructor
  · calc
      directionDot (reflectedDirection i n) (quarterTurn n.1) =
          directionDot i (quarterTurn n.1) -
            (2 * directionDot i n.1) *
              directionDot n.1 (quarterTurn n.1) := by
                simp [reflectedDirection, subtractDirection, scaleDirection,
                  directionDot]
                ring
      _ = directionDot i (quarterTurn n.1) := by
        rw [horthogonal]
        ring
  · calc
      directionDot (reflectedDirection i n) n.1 =
          directionDot i n.1 -
            (2 * directionDot i n.1) * directionDot n.1 n.1 := by
                simp [reflectedDirection, subtractDirection, scaleDirection,
                  directionDot]
                ring
      _ = -directionDot i n.1 := by
        rw [hunit]
        ring

/-- Reflection in a unit normal preserves squared norm. -/
theorem reflectedDirection_normSq (i : Direction2) (n : UnitDirection) :
    directionNormSq (reflectedDirection i n) = directionNormSq i := by
  have hunit : directionNormSq n.1 = 1 := n.2
  calc
    directionNormSq (reflectedDirection i n) =
        directionNormSq i - 4 * (directionDot i n.1) ^ 2 +
          4 * (directionDot i n.1) ^ 2 * directionNormSq n.1 := by
            simp [reflectedDirection, subtractDirection, scaleDirection,
              directionNormSq, directionDot]
            ring
    _ = directionNormSq i := by
      rw [hunit]
      ring

/-- Specular reflection of unit data exists and is unique. -/
theorem existsUnique_specularReflection (i n : UnitDirection) :
    ∃! o : UnitDirection, IsSpecularReflection i n o := by
  let o₀ : UnitDirection :=
    ⟨reflectedDirection i.1 n, by
      rw [reflectedDirection_normSq i.1 n]
      exact i.2⟩
  have ho₀ : IsSpecularReflection i n o₀ := by
    simpa only [IsSpecularReflection, o₀] using
      reflectedDirection_components i.1 n
  have recover_x (d : Direction2) :
      d.x = directionDot d n.1 * n.1.x -
        directionDot d (quarterTurn n.1) * n.1.y := by
    calc
      d.x = d.x * directionNormSq n.1 := by rw [n.2]; ring
      _ = directionDot d n.1 * n.1.x -
          directionDot d (quarterTurn n.1) * n.1.y := by
            simp [directionNormSq, directionDot, quarterTurn]
            ring
  have recover_y (d : Direction2) :
      d.y = directionDot d n.1 * n.1.y +
        directionDot d (quarterTurn n.1) * n.1.x := by
    calc
      d.y = d.y * directionNormSq n.1 := by rw [n.2]; ring
      _ = directionDot d n.1 * n.1.y +
          directionDot d (quarterTurn n.1) * n.1.x := by
            simp [directionNormSq, directionDot, quarterTurn]
            ring
  have direction_ext (a b : Direction2) (hx : a.x = b.x) (hy : a.y = b.y) :
      a = b := by
    rcases a with ⟨ax, ay⟩
    rcases b with ⟨bx, by'⟩
    dsimp at hx hy
    subst bx
    subst by'
    rfl
  refine ⟨o₀, ho₀, ?_⟩
  intro o ho
  apply Subtype.ext
  apply direction_ext
  · rw [recover_x o.1, recover_x o₀.1, ho.2, ho₀.2, ho.1, ho₀.1]
  · rw [recover_y o.1, recover_y o₀.1, ho.2, ho₀.2, ho.1, ho₀.1]

/-- The reflected vector equipped with its preserved unit-norm certificate. -/
def reflectedUnitDirection (i n : UnitDirection) : UnitDirection :=
  ⟨reflectedDirection i.1 n, by
    rw [reflectedDirection_normSq i.1 n]
    exact i.2⟩

/-! ## Radial and axial reflected-ray primitives -/

/-- Outward radial unit normal at a certified circle point. -/
def radialUnitNormal (c : Circle) (Q : Point2) (hQ : OnCircle c Q) : UnitDirection :=
  ⟨{ x := (Q.x - c.center.x) / c.radius
     y := (Q.y - c.center.y) / c.radius }, by
    have hradius : c.radius ≠ 0 := ne_of_gt c.radius_pos
    have hcircle :
        (Q.x - c.center.x) ^ 2 + (Q.y - c.center.y) ^ 2 =
          c.radius ^ 2 := by
      simpa [OnCircle, displacementNormSq, displacement] using hQ
    change
      ((Q.x - c.center.x) / c.radius) *
          ((Q.x - c.center.x) / c.radius) +
        ((Q.y - c.center.y) / c.radius) *
          ((Q.y - c.center.y) / c.radius) = 1
    field_simp [hradius] <;> nlinarith [hcircle]⟩

/-- The radial normal at a circle point is unit and nonzero. -/
theorem radialUnitNormal_isUnit (c : Circle) (Q : Point2) (hQ : OnCircle c Q) :
    directionNormSq (radialUnitNormal c Q hQ).1 = 1 ∧
      (radialUnitNormal c Q hQ).1 ≠ ({ x := 0, y := 0 } : Direction2) := by
  exact ⟨(radialUnitNormal c Q hQ).2,
    UnitDirection.ne_zero (radialUnitNormal c Q hQ)⟩

/-- Forward ray produced by specular reflection at a circular mirror point. -/
def rayAfterReflection (c : Circle) (r : ForwardRay) (Q : Point2)
    (hQ : OnCircle c Q) : ForwardRay :=
  { origin := Q
    direction := reflectedUnitDirection r.direction (radialUnitNormal c Q hQ) }

/-- Incidence point and radial direction on an oriented circle. -/
def semicirclePoint (c : Circle) (o : VerticalOrientation) (θ : ℝ) :
    Point2 × Direction2 :=
  ({ x := c.center.x + c.radius * Real.sin θ
     y := c.center.y + orientationSign o * c.radius * Real.cos θ },
   { x := Real.sin θ, y := orientationSign o * Real.cos θ })

/-- Strict signed angular domain excluding the two rims. -/
def InAxialIncidenceDomain (θ : ℝ) : Prop := |θ| < Real.pi / 2

/-- The parameterized point, radial normal, and axial dot product have the expected invariants. -/
theorem semicirclePoint_invariants (c : Circle) (o : VerticalOrientation)
    (rims : RimConvention) (θ : ℝ) (hθ : InAxialIncidenceDomain θ) :
    OnReflectingArc { circle := c, orientation := o, rims := rims }
        (semicirclePoint c o θ).1 ∧
      directionNormSq (semicirclePoint c o θ).2 = 1 ∧
      directionDot (axisDirection o).1 (semicirclePoint c o θ).2 = Real.cos θ := by
  change |θ| < Real.pi / 2 at hθ
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hsign : orientationSign o ^ 2 = 1 := (orientationSign_sq o).2.1
  have hcircle : OnCircle c (semicirclePoint c o θ).1 := by
    unfold OnCircle
    calc
      displacementNormSq (displacement c.center (semicirclePoint c o θ).1) =
          c.radius ^ 2 *
            (Real.sin θ ^ 2 + orientationSign o ^ 2 * Real.cos θ ^ 2) := by
              simp [displacementNormSq, displacement, semicirclePoint]
              ring
      _ = c.radius ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by
        rw [hsign]
        ring
      _ = c.radius ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]
  have hside_eq :
      orientationSign o *
          ((semicirclePoint c o θ).1.y - c.center.y) =
        c.radius * Real.cos θ := by
    calc
      orientationSign o *
          ((semicirclePoint c o θ).1.y - c.center.y) =
          orientationSign o ^ 2 * (c.radius * Real.cos θ) := by
            simp [semicirclePoint]
            ring
      _ = c.radius * Real.cos θ := by rw [hsign, one_mul]
  have hside :
      0 < orientationSign o *
        ((semicirclePoint c o θ).1.y - c.center.y) := by
    rw [hside_eq]
    exact mul_pos c.radius_pos hcos
  have harc :
      OnReflectingArc { circle := c, orientation := o, rims := rims }
        (semicirclePoint c o θ).1 := by
    refine ⟨hcircle, ?_⟩
    cases rims
    · exact hside
    · exact le_of_lt hside
  have hnorm : directionNormSq (semicirclePoint c o θ).2 = 1 := by
    calc
      directionNormSq (semicirclePoint c o θ).2 =
          Real.sin θ ^ 2 + orientationSign o ^ 2 * Real.cos θ ^ 2 := by
            simp [directionNormSq, directionDot, semicirclePoint]
            ring
      _ = Real.sin θ ^ 2 + Real.cos θ ^ 2 := by rw [hsign, one_mul]
      _ = 1 := Real.sin_sq_add_cos_sq θ
  have hdot :
      directionDot (axisDirection o).1 (semicirclePoint c o θ).2 =
        Real.cos θ := by
    calc
      directionDot (axisDirection o).1 (semicirclePoint c o θ).2 =
          orientationSign o ^ 2 * Real.cos θ := by
            simp [directionDot, axisDirection, semicirclePoint]
            ring
      _ = Real.cos θ := by rw [hsign, one_mul]
  exact ⟨harc, hnorm, hdot⟩

/-- Specularly reflected axial ray at an oriented-circle parameter. -/
def axialReflectedRay (c : Circle) (o : VerticalOrientation) (θ : ℝ) : ForwardRay :=
  let data := semicirclePoint c o θ
  let normal : UnitDirection := ⟨data.2, by
    have hsign : orientationSign o ^ 2 = 1 := (orientationSign_sq o).2.1
    calc
      directionNormSq data.2 =
          Real.sin θ ^ 2 + orientationSign o ^ 2 * Real.cos θ ^ 2 := by
            simp [data, directionNormSq, directionDot, semicirclePoint]
            ring
      _ = Real.sin θ ^ 2 + Real.cos θ ^ 2 := by rw [hsign, one_mul]
      _ = 1 := Real.sin_sq_add_cos_sq θ⟩
  { origin := data.1
    direction := reflectedUnitDirection (axisDirection o) normal }

end Ipho2026Gpt56solBlind.Shared.GeometricOptics
