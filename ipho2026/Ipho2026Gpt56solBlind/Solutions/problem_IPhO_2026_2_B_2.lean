import Ipho2026Gpt56solBlind.Shared.ConcentratorOptics

/-!
# IPhO 2026 problem 2, part B.2: solar-cooker power ratio

This answer-blind specification keeps the requested ratio as an unknown real
number.  It characterizes that number through the ray geometry and the common
irradiance/axial-extent power laws, without evaluating either aperture.
-/

noncomputable section

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_2_B_2

open Ipho2026Gpt56solBlind.Shared.GeometricOptics

/-- A typed physical realization of the half-cylindrical solar cooker.

The typed concentrator geometry fixes the parallel-axis transverse model, the
absorber displacement by half the mirror radius, and `0 < a < R / 2`.  The
same strictly positive irradiance and axial extent are used for both powers.
-/
structure SolarCookerRealization where
  sourceUnits : SIUnitChoices
  geometry : PhysicalConcentratorGeometry sourceUnits
  irradiance : Irradiance
  axialExtent : Ipho2026Gpt56solBlind.Shared.ISQDimensions.Length
  power : Ipho2026Gpt56solBlind.Shared.ISQDimensions.HeatRate
  referencePower : Ipho2026Gpt56solBlind.Shared.ISQDimensions.HeatRate
  oneReflection :
    InOneReflectionRegime
      (physicalConcentratorGeometryCoordinateInSI sourceUnits geometry)
  illuminatedMeasurable :
    HasMeasurableIlluminatedAperture
      (physicalConcentratorGeometryCoordinateInSI sourceUnits geometry)
  referenceMeasurable :
    HasMeasurableReferenceAperture
      (physicalConcentratorGeometryCoordinateInSI sourceUnits geometry)
  uniformIrradiance : UniformIrradiance sourceUnits irradiance
  irradiance_pos :
    0 < Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
      sourceUnits irradiance
  positiveAxialExtent : IsPositiveAxialExtent sourceUnits axialExtent
  uniformPowerPair :
    IsUniformPowerPair sourceUnits geometry oneReflection
      illuminatedMeasurable referenceMeasurable irradiance uniformIrradiance
      axialExtent positiveAxialExtent power referencePower

/-- The coherent-SI scalar geometry on which all ray predicates are evaluated. -/
def SolarCookerRealization.scalarGeometry (X : SolarCookerRealization) :
    ConcentratorGeometry :=
  physicalConcentratorGeometryCoordinateInSI X.sourceUnits X.geometry

/-- The accepted, nondegenerate power-ratio predicate for one realization. -/
def SolarCookerRealization.HasPowerRatio (X : SolarCookerRealization)
    (ρ : ℝ) : Prop :=
  IsPowerRatio X.sourceUnits X.geometry X.oneReflection
    X.illuminatedMeasurable X.referenceMeasurable X.irradiance
    X.uniformIrradiance X.axialExtent X.positiveAxialExtent X.power
    X.referencePower ρ

/-- The typed unmirrored transverse measure is strictly positive. -/
lemma referenceTransverseMeasure_pos (u : SIUnitChoices)
    (PG : PhysicalConcentratorGeometry u)
    (hRef : HasMeasurableReferenceAperture
      (physicalConcentratorGeometryCoordinateInSI u PG)) :
    0 < Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI u
      (referenceTransverseMeasure u
        (physicalConcentratorGeometryCoordinateInSI u PG) hRef) := by
  let G := physicalConcentratorGeometryCoordinateInSI u PG
  have ha_lt : G.absorber.radius < G.mirror.radius / 2 := by
    simpa [ConcentratorGeometry.absorber] using G.absorberRadius_lt_half
  have hsubset :
      Set.Ioo (G.absorber.center.x - G.absorber.radius / 2)
          (G.absorber.center.x + G.absorber.radius / 2) ⊆
        unmirroredReferenceAperture G := by
    intro x hx
    let δ : ℝ := x - G.mirror.center.x
    let t : ℝ := Real.sqrt (G.absorber.radius ^ 2 - δ ^ 2)
    let s : ℝ := G.mirror.radius / 2 - t
    let Q : Point2 := { x := x, y := G.absorber.center.y + t }
    have hδlower : -G.absorber.radius / 2 < δ := by
      dsimp [δ]
      simp only [ConcentratorGeometry.absorber] at hx
      change -G.absorberRadius / 2 < x - G.mirror.center.x
      linarith [hx.1]
    have hδupper : δ < G.absorber.radius / 2 := by
      dsimp [δ]
      simp only [ConcentratorGeometry.absorber] at hx
      change x - G.mirror.center.x < G.absorberRadius / 2
      linarith [hx.2]
    have hproduct :
        0 < (δ + G.absorber.radius / 2) *
          (G.absorber.radius / 2 - δ) :=
      mul_pos (by linarith) (by linarith)
    have hrad : 0 < G.absorber.radius ^ 2 - δ ^ 2 := by
      nlinarith
    have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
    have ht_sq : t ^ 2 = G.absorber.radius ^ 2 - δ ^ 2 := by
      exact Real.sq_sqrt hrad.le
    have ht_le : t ≤ G.absorber.radius := by
      nlinarith [G.absorber.radius_pos, sq_nonneg δ]
    change ∃ s : Length, ∃ Q : Point2,
      IsFirstContainerContact G (incomingSunlightRay G x) s Q
    refine ⟨s, Q, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [s]
      linarith
    · simp [Q, s, ForwardRay.pointAt, incomingSunlightRay, translate,
        directionDisplacement, axisDirection, orientationSign,
        ConcentratorGeometry.absorber] <;> try ring
    · simpa [OnCircle, displacementNormSq, displacement, Q, δ, t,
        ConcentratorGeometry.absorber] using
        (show δ ^ 2 + t ^ 2 = G.absorber.radius ^ 2 by linarith)
    · intro v hv hvs
      have ht_lt : t < G.mirror.radius / 2 - v := by
        dsimp [s] at hvs
        linarith
      have hsq_lt : t ^ 2 < (G.mirror.radius / 2 - v) ^ 2 := by
        nlinarith [sq_nonneg (G.mirror.radius / 2 - v - t)]
      simp only [ForwardRay.pointAt, incomingSunlightRay, translate,
        directionDisplacement, axisDirection, orientationSign,
        displacementNormSq, displacement, ConcentratorGeometry.absorber]
      dsimp [δ] at ht_sq
      simp only [ConcentratorGeometry.absorber] at ht_sq ⊢
      nlinarith
  have hinterval_pos :
      0 < MeasureTheory.volume
        (Set.Ioo (G.absorber.center.x - G.absorber.radius / 2)
          (G.absorber.center.x + G.absorber.radius / 2)) := by
    rw [Real.volume_Ioo]
    apply ENNReal.ofReal_pos.mpr
    simp only [ConcentratorGeometry.absorber]
    linarith [G.absorberRadius_pos]
  have hmeasure_pos :
      0 < MeasureTheory.volume (unmirroredReferenceAperture G) :=
    lt_of_lt_of_le hinterval_pos (MeasureTheory.measure_mono hsubset)
  have hmeasure_ne_top :
      MeasureTheory.volume (unmirroredReferenceAperture G) ≠ ⊤ :=
    (transverseApertures_bounded G).2.2.2
  have hcoord :
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI u
          (referenceTransverseMeasure u G hRef) =
        (MeasureTheory.volume (unmirroredReferenceAperture G)).toReal :=
    (quantityFromSICoordinate_roundtrip u
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.lengthDimension
      (MeasureTheory.volume (unmirroredReferenceAperture G)).toReal
      (referenceTransverseMeasure u G hRef)).1
  change 0 < Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI u
    (referenceTransverseMeasure u G hRef)
  rw [hcoord]
  exact ENNReal.toReal_pos hmeasure_pos.ne' hmeasure_ne_top

/-- The unmirrored reference power of every realization is strictly positive. -/
lemma SolarCookerRealization.referencePower_pos (X : SolarCookerRealization) :
    0 < Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
      X.sourceUnits X.referencePower := by
  have hμ := referenceTransverseMeasure_pos X.sourceUnits X.geometry
    X.referenceMeasurable
  have harea := collectingArea_coordinate X.sourceUnits
    (referenceTransverseMeasure X.sourceUnits X.scalarGeometry
      X.referenceMeasurable)
    X.axialExtent hμ.le X.positiveAxialExtent
  have harea_pos := harea.2.2 hμ
  have href := X.uniformPowerPair.2
  change Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
      X.sourceUnits X.referencePower =
    Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
        X.sourceUnits X.irradiance *
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI X.sourceUnits
        (collectingArea X.sourceUnits
          (referenceTransverseMeasure X.sourceUnits X.scalarGeometry
            X.referenceMeasurable) X.axialExtent) at href
  rw [href]
  exact mul_pos X.irradiance_pos harea_pos

/-- Every physical realization has exactly one accepted power ratio. -/
theorem SolarCookerRealization.existsUnique_powerRatio
    (X : SolarCookerRealization) :
    ∃! ρ : ℝ, X.HasPowerRatio ρ := by
  exact Ipho2026Gpt56solBlind.Shared.GeometricOptics.existsUnique_powerRatio
    X.sourceUnits X.geometry X.oneReflection
    X.illuminatedMeasurable X.referenceMeasurable X.irradiance
    X.uniformIrradiance X.axialExtent X.positiveAxialExtent X.power
    X.referencePower X.uniformPowerPair X.referencePower_pos

/-- Acceptance of reflected rays is invariant under reflection in the
concentrator's symmetry line. -/
def HasSignedIncidenceSymmetry (G : ConcentratorGeometry) : Prop :=
  ∀ θ : ℝ, AcceptedReflectedRay G θ ↔ AcceptedReflectedRay G (-θ)

/-- The two signed incidence branches of every concentrator are symmetric. -/
lemma acceptedReflectedRay_signedSymmetry (G : ConcentratorGeometry) :
    HasSignedIncidenceSymmetry G := by
  let reflectPoint (P : Point2) : Point2 :=
    { x := 2 * G.mirror.center.x - P.x, y := P.y }
  have point_ext (P Q : Point2) (hx : P.x = Q.x) (hy : P.y = Q.y) :
      P = Q := by
    cases P
    cases Q
    cases hx
    cases hy
    rfl
  have direction_ext (d e : Direction2) (hx : d.x = e.x) (hy : d.y = e.y) :
      d = e := by
    cases d
    cases e
    cases hx
    cases hy
    rfl
  have ray_ext (r q : ForwardRay) (ho : r.origin = q.origin)
      (hd : r.direction.1 = q.direction.1) : r = q := by
    cases r with
    | mk ro rd =>
        cases q with
        | mk qo qd =>
            dsimp at ho hd
            subst qo
            have hsub : rd = qd := Subtype.ext hd
            subst qd
            rfl
  let reflectDirection (d : Direction2) : Direction2 :=
    { x := -d.x, y := d.y }
  have reflectDirection_norm (d : Direction2) :
      directionNormSq (reflectDirection d) = directionNormSq d := by
    simp [reflectDirection, directionNormSq, directionDot]
  let reflectRay (r : ForwardRay) : ForwardRay :=
    { origin := reflectPoint r.origin
      direction := ⟨reflectDirection r.direction.1, by
        rw [reflectDirection_norm]
        exact r.direction.2⟩ }
  have reflectRay_pointAt (r : ForwardRay) (s : Length) :
      (reflectRay r).pointAt s = reflectPoint (r.pointAt s) := by
    apply point_ext
    · simp [reflectRay, reflectPoint, reflectDirection, ForwardRay.pointAt,
        translate, directionDisplacement]
      ring
    · simp [reflectRay, reflectPoint, reflectDirection, ForwardRay.pointAt,
        translate, directionDisplacement]
  have mirror_distance (P : Point2) :
      displacementNormSq (displacement G.mirror.center (reflectPoint P)) =
        displacementNormSq (displacement G.mirror.center P) := by
    simp [reflectPoint, displacementNormSq, displacement]
    ring
  have absorber_distance (P : Point2) :
      displacementNormSq (displacement G.absorber.center (reflectPoint P)) =
        displacementNormSq (displacement G.absorber.center P) := by
    simp [reflectPoint, ConcentratorGeometry.absorber, displacementNormSq,
      displacement]
    ring
  have onMirror (P : Point2) :
      OnCircle G.mirror (reflectPoint P) ↔ OnCircle G.mirror P := by
    simp only [OnCircle, mirror_distance]
  have onAbsorber (P : Point2) :
      OnCircle G.absorber (reflectPoint P) ↔ OnCircle G.absorber P := by
    simp only [OnCircle, absorber_distance]
  have inAbsorber (P : Point2) :
      InClosedDisk G.absorber (reflectPoint P) ↔ InClosedDisk G.absorber P := by
    dsimp only [InClosedDisk]
    rw [absorber_distance]
  have inLowerInterior (P : Point2) :
      InSemicircleInterior G.lowerMirror (reflectPoint P) ↔
        InSemicircleInterior G.lowerMirror P := by
    dsimp only [InSemicircleInterior, ConcentratorGeometry.lowerMirror,
      reflectPoint, orientationSign]
    rw [mirror_distance]
  have onLowerMirror (P : Point2) :
      OnReflectingArc G.lowerMirror (reflectPoint P) ↔
        OnReflectingArc G.lowerMirror P := by
    simp only [OnReflectingArc, ConcentratorGeometry.lowerMirror, onMirror,
      reflectPoint, orientationSign]
  have inFree (P : Point2) :
      InConcentratorFreeRegion G (reflectPoint P) ↔
        InConcentratorFreeRegion G P := by
    dsimp only [InConcentratorFreeRegion]
    rw [inLowerInterior, inAbsorber]
  have onBoundary (P : Point2) :
      OnConcentratorBoundary G (reflectPoint P) ↔
        OnConcentratorBoundary G P := by
    dsimp only [OnConcentratorBoundary]
    rw [onLowerMirror, onAbsorber]
  have firstConcentratorContact (r : ForwardRay) (s : Length) (Q : Point2)
      (h : IsFirstConcentratorContact G r s Q) :
      IsFirstConcentratorContact G (reflectRay r) s (reflectPoint Q) := by
    rcases h with ⟨hs, hQ, hboundary, hbefore⟩
    refine ⟨hs, ?_, (onBoundary Q).2 hboundary, ?_⟩
    · calc
        reflectPoint Q = reflectPoint (r.pointAt s) := congrArg reflectPoint hQ
        _ = (reflectRay r).pointAt s := (reflectRay_pointAt r s).symm
    · intro v hv hvs
      rw [reflectRay_pointAt]
      exact (inFree (r.pointAt v)).2 (hbefore v hv hvs)
  have firstContainerContact (r : ForwardRay) (s : Length) (Q : Point2)
      (h : IsFirstContainerContact G r s Q) :
      IsFirstContainerContact G (reflectRay r) s (reflectPoint Q) := by
    rcases h with ⟨hs, hQ, hcircle, hbefore⟩
    refine ⟨hs, ?_, (onAbsorber Q).2 hcircle, ?_⟩
    · calc
        reflectPoint Q = reflectPoint (r.pointAt s) := congrArg reflectPoint hQ
        _ = (reflectRay r).pointAt s := (reflectRay_pointAt r s).symm
    · intro v hv hvs
      rw [reflectRay_pointAt, absorber_distance]
      exact hbefore v hv hvs
  have noSecondMirrorContact (r : ForwardRay) (s : Length)
      (h : HasNoSecondMirrorContact G r s) :
      HasNoSecondMirrorContact G (reflectRay r) s := by
    intro v hv hvs hreflected
    rw [reflectRay_pointAt] at hreflected
    exact h v hv hvs ((onLowerMirror (r.pointAt v)).1 hreflected)
  have reflectIncoming (x : Length) :
      reflectRay (incomingSunlightRay G x) =
        incomingSunlightRay G (2 * G.mirror.center.x - x) := by
    apply ray_ext
    · apply point_ext <;>
        simp [reflectRay, reflectPoint, incomingSunlightRay]
    · apply direction_ext <;>
        simp [reflectRay, reflectDirection, incomingSunlightRay, axisDirection,
          orientationSign]
  have reflectSemicirclePoint (theta : ℝ) :
      reflectPoint (semicirclePoint G.mirror .lower theta).1 =
        (semicirclePoint G.mirror .lower (-theta)).1 := by
    apply point_ext
    · simp [reflectPoint, semicirclePoint, orientationSign, Real.sin_neg,
        Real.cos_neg]
      ring
    · simp [reflectPoint, semicirclePoint, orientationSign, Real.sin_neg,
        Real.cos_neg]
  have reflectAxialRay (theta : ℝ) :
      reflectRay (axialReflectedRay G.mirror .lower theta) =
        axialReflectedRay G.mirror .lower (-theta) := by
    apply ray_ext
    · exact reflectSemicirclePoint theta
    · apply direction_ext <;>
        dsimp only [reflectRay, reflectDirection, axialReflectedRay,
          semicirclePoint, reflectedUnitDirection, reflectedDirection,
          subtractDirection, scaleDirection, directionDot, axisDirection,
          orientationSign] <;>
        rw [Real.sin_neg, Real.cos_neg] <;>
        ring
  have forward (theta : ℝ) : AcceptedReflectedRay G theta →
      AcceptedReflectedRay G (-theta) := by
    rintro ⟨hregime, hdomain, sMirror, hfirst, harc,
      sHit, QHit, hhit, hnosecond⟩
    have hpoint := reflectSemicirclePoint theta
    have hpointX :
        2 * G.mirror.center.x -
            (semicirclePoint G.mirror .lower theta).1.x =
          (semicirclePoint G.mirror .lower (-theta)).1.x := by
      simpa [reflectPoint] using congrArg Point2.x hpoint
    have hfirst' := firstConcentratorContact
      (incomingSunlightRay G (semicirclePoint G.mirror .lower theta).1.x)
      sMirror (semicirclePoint G.mirror .lower theta).1 hfirst
    rw [reflectIncoming, hpoint, hpointX] at hfirst'
    have harc' :
        OnReflectingArc G.lowerMirror
          (semicirclePoint G.mirror .lower (-theta)).1 := by
      rw [← hpoint]
      exact (onLowerMirror _).2 harc
    have hhit' := firstContainerContact
      (axialReflectedRay G.mirror .lower theta) sHit QHit hhit
    rw [reflectAxialRay] at hhit'
    have hnosecond' := noSecondMirrorContact
      (axialReflectedRay G.mirror .lower theta) sHit hnosecond
    rw [reflectAxialRay] at hnosecond'
    refine ⟨hregime, ?_, sMirror, hfirst', harc',
      sHit, reflectPoint QHit, hhit', hnosecond'⟩
    change |-theta| < Real.pi / 2
    rw [abs_neg]
    exact hdomain
  intro theta
  constructor
  · exact forward theta
  · intro h
    simpa only [neg_neg] using (forward (-theta) h)

/-- Every accepted incoming coordinate belongs to exactly one of the direct
and one-reflection absorption branches. -/
def HasDirectOneReflectionPartition (G : ConcentratorGeometry) : Prop :=
  ∀ x : Length, AcceptedIncomingCoordinate G x →
    (IsDirectlyAbsorbed G x ∨ IsAbsorbedAfterOneReflection G x) ∧
      ¬(IsDirectlyAbsorbed G x ∧ IsAbsorbedAfterOneReflection G x)

/-- Accepted incoming coordinates obey the direct/one-reflection partition. -/
lemma acceptedIncomingCoordinate_directOneReflectionPartition
    (G : ConcentratorGeometry) :
    HasDirectOneReflectionPartition G := by
  intro x hx
  exact acceptedIncomingCoordinate_ordering G x hx

/-- A realization is compatible with `θmax` when that signed local-normal
incidence parameter is the positive attained tangent limit and the complete
accepted-ray family has the required symmetry and branch partition. -/
def SolarCookerRealization.CompatibleAtLimitingAngle
    (X : SolarCookerRealization) (θmax : ℝ) : Prop :=
  IsLimitingTangentAngle X.scalarGeometry θmax ∧
    HasSignedIncidenceSymmetry X.scalarGeometry ∧
    HasDirectOneReflectionPartition X.scalarGeometry

/-- A limiting angle lies on the physical acute branch and is attained by at
least one compatible realization. -/
def IsRealizableLimitingAngle (θmax : ℝ) : Prop :=
  0 < θmax ∧ θmax < Real.pi / 2 ∧
    ∃ X : SolarCookerRealization, X.CompatibleAtLimitingAngle θmax

/-- At a fixed compatible limiting angle, the absorber-to-mirror radius ratio
is invariant.  This relational statement does not evaluate that ratio. -/
lemma compatibleGeometry_scaleRelation (X Y : SolarCookerRealization)
    (θmax : ℝ) (hX : X.CompatibleAtLimitingAngle θmax)
    (hY : Y.CompatibleAtLimitingAngle θmax) :
    X.scalarGeometry.absorberRadius * Y.scalarGeometry.mirror.radius =
      Y.scalarGeometry.absorberRadius * X.scalarGeometry.mirror.radius := by
  have radius_formula (G : ConcentratorGeometry)
      (h : IsLimitingTangentAngle G θmax) :
      G.absorberRadius =
        G.mirror.radius * Real.sin θmax * (1 - Real.cos θmax) := by
    rcases h.2.2.2.1 with ⟨s, Q, htangent⟩
    have hdistance :=
      (tangentContact_distanceSq G
        (axialReflectedRay G.mirror .lower θmax) htangent).2
    have hdet :
        displacementDirectionDet
            (displacement G.absorber.center
              (axialReflectedRay G.mirror .lower θmax).origin)
            (axialReflectedRay G.mirror .lower θmax).direction.1 =
          G.mirror.radius * Real.sin θmax * (Real.cos θmax - 1) := by
      dsimp only [ConcentratorGeometry.absorber, axialReflectedRay,
        semicirclePoint, reflectedUnitDirection, reflectedDirection,
        subtractDirection, scaleDirection, directionDot, axisDirection,
        orientationSign, displacementDirectionDet, displacement]
      ring_nf
    rw [hdet] at hdistance
    have hsquared :
        G.absorberRadius ^ 2 =
          (G.mirror.radius * Real.sin θmax *
            (1 - Real.cos θmax)) ^ 2 := by
      calc
        G.absorberRadius ^ 2 =
            (G.mirror.radius * Real.sin θmax *
              (Real.cos θmax - 1)) ^ 2 := by
                simpa [ConcentratorGeometry.absorber] using hdistance
        _ = (G.mirror.radius * Real.sin θmax *
              (1 - Real.cos θmax)) ^ 2 := by ring
    have hsin : 0 < Real.sin θmax :=
      Real.sin_pos_of_pos_of_lt_pi h.1 (by linarith [h.2.1, Real.pi_pos])
    have hcos : 0 < Real.cos θmax :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1, Real.pi_pos], h.2.1⟩
    have hcos_lt : Real.cos θmax < 1 := by
      nlinarith [Real.sin_sq_add_cos_sq θmax]
    have hR : 0 < G.mirror.radius := G.mirror.radius_pos
    have hrhs :
        0 < G.mirror.radius * Real.sin θmax *
          (1 - Real.cos θmax) :=
      mul_pos (mul_pos hR hsin) (sub_pos.mpr hcos_lt)
    nlinarith [G.absorberRadius_pos]
  have hformulaX := radius_formula X.scalarGeometry hX.1
  have hformulaY := radius_formula Y.scalarGeometry hY.1
  rw [hformulaX, hformulaY]
  ring

/-- The illuminated and unmirrored transverse apertures of compatible
realizations scale by their mirror radii.  Neither aperture is evaluated. -/
lemma compatibleApertures_scale (X Y : SolarCookerRealization)
    (θmax : ℝ) (hX : X.CompatibleAtLimitingAngle θmax)
    (hY : Y.CompatibleAtLimitingAngle θmax) :
    let μX :=
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI X.sourceUnits
        (transverseFluxMeasure X.sourceUnits X.scalarGeometry
          X.illuminatedMeasurable)
    let μY :=
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Y.sourceUnits
        (transverseFluxMeasure Y.sourceUnits Y.scalarGeometry
          Y.illuminatedMeasurable)
    let μ0X :=
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI X.sourceUnits
        (referenceTransverseMeasure X.sourceUnits X.scalarGeometry
          X.referenceMeasurable)
    let μ0Y :=
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Y.sourceUnits
        (referenceTransverseMeasure Y.sourceUnits Y.scalarGeometry
          Y.referenceMeasurable)
    μX * Y.scalarGeometry.mirror.radius =
        μY * X.scalarGeometry.mirror.radius ∧
      μ0X * Y.scalarGeometry.mirror.radius =
        μ0Y * X.scalarGeometry.mirror.radius := by
  have point_ext (P Q : Point2) (hx : P.x = Q.x) (hy : P.y = Q.y) :
      P = Q := by
    cases P
    cases Q
    cases hx
    cases hy
    rfl
  have direction_ext (d e : Direction2) (hx : d.x = e.x) (hy : d.y = e.y) :
      d = e := by
    cases d
    cases e
    cases hx
    cases hy
    rfl
  have ray_ext (r q : ForwardRay) (ho : r.origin = q.origin)
      (hd : r.direction.1 = q.direction.1) : r = q := by
    cases r with
    | mk ro rd =>
        cases q with
        | mk qo qd =>
            dsimp at ho hd
            subst qo
            have hsub : rd = qd := Subtype.ext hd
            subst qd
            rfl
  have mapApertures (A B : ConcentratorGeometry) (k : ℝ) (hk : 0 < k)
      (hR : k * A.mirror.radius = B.mirror.radius)
      (ha : k * A.absorberRadius = B.absorberRadius) :
      (∀ x : Length, AcceptedIncomingCoordinate A x →
        AcceptedIncomingCoordinate B
          (B.mirror.center.x + k * (x - A.mirror.center.x))) ∧
      (∀ x : Length, x ∈ unmirroredReferenceAperture A →
        B.mirror.center.x + k * (x - A.mirror.center.x) ∈
          unmirroredReferenceAperture B) := by
    let T (P : Point2) : Point2 :=
      { x := B.mirror.center.x + k * (P.x - A.mirror.center.x)
        y := B.mirror.center.y + k * (P.y - A.mirror.center.y) }
    let TR (r : ForwardRay) : ForwardRay :=
      { origin := T r.origin, direction := r.direction }
    have hkne : k ≠ 0 := ne_of_gt hk
    have hk_sq : 0 < k ^ 2 := sq_pos_of_pos hk
    have pointAt (r : ForwardRay) (s : Length) :
        (TR r).pointAt (k * s) = T (r.pointAt s) := by
      apply point_ext
      · simp [TR, T, ForwardRay.pointAt, translate, directionDisplacement]
        ring
      · simp [TR, T, ForwardRay.pointAt, translate, directionDisplacement]
        ring
    have mirrorDistance (P : Point2) :
        displacementNormSq (displacement B.mirror.center (T P)) =
          k ^ 2 * displacementNormSq (displacement A.mirror.center P) := by
      simp [T, displacementNormSq, displacement]
      ring
    have absorberDistance (P : Point2) :
        displacementNormSq (displacement B.absorber.center (T P)) =
          k ^ 2 * displacementNormSq (displacement A.absorber.center P) := by
      simp [T, ConcentratorGeometry.absorber, displacementNormSq, displacement,
        ← hR]
      ring
    have onMirror (P : Point2) :
        OnCircle B.mirror (T P) ↔ OnCircle A.mirror P := by
      simp only [OnCircle, mirrorDistance]
      rw [← hR]
      constructor
      · intro h
        have h' :
            k ^ 2 * displacementNormSq (displacement A.mirror.center P) =
              k ^ 2 * A.mirror.radius ^ 2 := by
          calc
            k ^ 2 * displacementNormSq (displacement A.mirror.center P) =
                (k * A.mirror.radius) ^ 2 := h
            _ = k ^ 2 * A.mirror.radius ^ 2 := by ring
        exact mul_left_cancel₀ (ne_of_gt hk_sq) h'
      · intro h
        calc
          k ^ 2 * displacementNormSq (displacement A.mirror.center P) =
              k ^ 2 * A.mirror.radius ^ 2 := congrArg (k ^ 2 * ·) h
          _ = (k * A.mirror.radius) ^ 2 := by ring
    have onAbsorber (P : Point2) :
        OnCircle B.absorber (T P) ↔ OnCircle A.absorber P := by
      rw [OnCircle, absorberDistance]
      change k ^ 2 * displacementNormSq (displacement A.absorber.center P) =
          B.absorberRadius ^ 2 ↔
        displacementNormSq (displacement A.absorber.center P) =
          A.absorberRadius ^ 2
      rw [← ha]
      constructor <;> intro h <;> nlinarith
    have inAbsorber (P : Point2) :
        InClosedDisk B.absorber (T P) ↔ InClosedDisk A.absorber P := by
      dsimp only [InClosedDisk]
      rw [absorberDistance]
      change k ^ 2 * displacementNormSq (displacement A.absorber.center P) ≤
          B.absorberRadius ^ 2 ↔
        displacementNormSq (displacement A.absorber.center P) ≤
          A.absorberRadius ^ 2
      rw [← ha]
      constructor <;> intro h <;> nlinarith
    have insideMirror (P : Point2) :
        displacementNormSq (displacement B.mirror.center (T P)) <
            B.mirror.radius ^ 2 ↔
          displacementNormSq (displacement A.mirror.center P) <
            A.mirror.radius ^ 2 := by
      rw [mirrorDistance, ← hR]
      constructor <;> intro h <;> nlinarith
    have lowerSide (P : Point2) :
        orientationSign VerticalOrientation.lower *
              ((T P).y - B.mirror.center.y) > 0 ↔
          orientationSign VerticalOrientation.lower *
              (P.y - A.mirror.center.y) > 0 := by
      simp [T, orientationSign]
      constructor <;> intro h <;> nlinarith
    have lowerSide_nonneg (P : Point2) :
        orientationSign VerticalOrientation.lower *
              ((T P).y - B.mirror.center.y) ≥ 0 ↔
          orientationSign VerticalOrientation.lower *
              (P.y - A.mirror.center.y) ≥ 0 := by
      simp [T, orientationSign]
      constructor <;> intro h <;> nlinarith
    have inLowerInterior (P : Point2) :
        InSemicircleInterior B.lowerMirror (T P) ↔
          InSemicircleInterior A.lowerMirror P := by
      dsimp only [InSemicircleInterior, ConcentratorGeometry.lowerMirror]
      rw [lowerSide, insideMirror]
    have onLowerMirror (P : Point2) :
        OnReflectingArc B.lowerMirror (T P) ↔
          OnReflectingArc A.lowerMirror P := by
      simp only [OnReflectingArc, ConcentratorGeometry.lowerMirror, onMirror,
        lowerSide_nonneg]
    have inFree (P : Point2) :
        InConcentratorFreeRegion B (T P) ↔
          InConcentratorFreeRegion A P := by
      dsimp only [InConcentratorFreeRegion]
      rw [inLowerInterior, inAbsorber]
    have onBoundary (P : Point2) :
        OnConcentratorBoundary B (T P) ↔
          OnConcentratorBoundary A P := by
      dsimp only [OnConcentratorBoundary]
      rw [onLowerMirror, onAbsorber]
    have firstConcentratorContact (r : ForwardRay) (s : Length) (Q : Point2)
        (h : IsFirstConcentratorContact A r s Q) :
        IsFirstConcentratorContact B (TR r) (k * s) (T Q) := by
      rcases h with ⟨hs, hQ, hboundary, hbefore⟩
      refine ⟨mul_pos hk hs, ?_, (onBoundary Q).2 hboundary, ?_⟩
      · calc
          T Q = T (r.pointAt s) := congrArg T hQ
          _ = (TR r).pointAt (k * s) := (pointAt r s).symm
      · intro v hv hvs
        let w : ℝ := v / k
        have hw : 0 < w := div_pos hv hk
        have hwlt : w < s :=
          (div_lt_iff₀ hk).2 (by simpa [w, mul_comm] using hvs)
        have hmapped := (inFree (r.pointAt w)).2 (hbefore w hw hwlt)
        have hv_eq : k * w = v := by
          dsimp [w]
          calc
            k * (v / k) = k * v / k := by ring
            _ = v := mul_div_cancel_left₀ v hkne
        rw [← hv_eq, pointAt]
        exact hmapped
    have firstContainerContact (r : ForwardRay) (s : Length) (Q : Point2)
        (h : IsFirstContainerContact A r s Q) :
        IsFirstContainerContact B (TR r) (k * s) (T Q) := by
      rcases h with ⟨hs, hQ, hcircle, hbefore⟩
      refine ⟨mul_pos hk hs, ?_, (onAbsorber Q).2 hcircle, ?_⟩
      · calc
          T Q = T (r.pointAt s) := congrArg T hQ
          _ = (TR r).pointAt (k * s) := (pointAt r s).symm
      · intro v hv hvs
        let w : ℝ := v / k
        have hw : 0 ≤ w := div_nonneg hv hk.le
        have hwlt : w < s :=
          (div_lt_iff₀ hk).2 (by simpa [w, mul_comm] using hvs)
        have hmapped := hbefore w hw hwlt
        have hv_eq : k * w = v := by
          dsimp [w]
          calc
            k * (v / k) = k * v / k := by ring
            _ = v := mul_div_cancel_left₀ v hkne
        rw [← hv_eq, pointAt, absorberDistance]
        change k ^ 2 *
            displacementNormSq (displacement A.absorber.center (r.pointAt w)) >
          B.absorberRadius ^ 2
        rw [← ha]
        change displacementNormSq
            (displacement A.absorber.center (r.pointAt w)) >
          A.absorberRadius ^ 2 at hmapped
        nlinarith
    have noSecondMirrorContact (r : ForwardRay) (s : Length)
        (h : HasNoSecondMirrorContact A r s) :
        HasNoSecondMirrorContact B (TR r) (k * s) := by
      intro v hv hvs hmirror
      let w : ℝ := v / k
      have hw : 0 < w := div_pos hv hk
      have hwle : w ≤ s :=
        (div_le_iff₀ hk).2 (by simpa [w, mul_comm] using hvs)
      have hv_eq : k * w = v := by
        dsimp [w]
        calc
          k * (v / k) = k * v / k := by ring
          _ = v := mul_div_cancel_left₀ v hkne
      rw [← hv_eq, pointAt] at hmirror
      exact h w hw hwle ((onLowerMirror (r.pointAt w)).1 hmirror)
    have incoming (x : Length) :
        TR (incomingSunlightRay A x) =
          incomingSunlightRay B
            (B.mirror.center.x + k * (x - A.mirror.center.x)) := by
      apply ray_ext
      · apply point_ext
        · simp [TR, T, incomingSunlightRay]
        · simp [TR, T, incomingSunlightRay]
      · rfl
    have rayAfter (r : ForwardRay) (Q : Point2) (hQ : OnCircle A.mirror Q) :
        TR (rayAfterReflection A.mirror r Q hQ) =
          rayAfterReflection B.mirror (TR r) (T Q) ((onMirror Q).2 hQ) := by
      have normal :
          (radialUnitNormal B.mirror (T Q) ((onMirror Q).2 hQ)).1 =
            (radialUnitNormal A.mirror Q hQ).1 := by
        apply direction_ext
        · change ((T Q).x - B.mirror.center.x) / B.mirror.radius =
            (Q.x - A.mirror.center.x) / A.mirror.radius
          rw [← hR]
          dsimp [T]
          rw [show B.mirror.center.x + k * (Q.x - A.mirror.center.x) -
              B.mirror.center.x = k * (Q.x - A.mirror.center.x) by ring]
          exact mul_div_mul_left _ _ hkne
        · change ((T Q).y - B.mirror.center.y) / B.mirror.radius =
            (Q.y - A.mirror.center.y) / A.mirror.radius
          rw [← hR]
          dsimp [T]
          rw [show B.mirror.center.y + k * (Q.y - A.mirror.center.y) -
              B.mirror.center.y = k * (Q.y - A.mirror.center.y) by ring]
          exact mul_div_mul_left _ _ hkne
      apply ray_ext
      · rfl
      · dsimp only [TR, rayAfterReflection]
        have normal_sub :
            radialUnitNormal B.mirror (T Q) ((onMirror Q).2 hQ) =
              radialUnitNormal A.mirror Q hQ := Subtype.ext normal
        rw [normal_sub]
    have direct (x : Length) (h : IsDirectlyAbsorbed A x) :
        IsDirectlyAbsorbed B
          (B.mirror.center.x + k * (x - A.mirror.center.x)) := by
      rcases h with ⟨s, Q, hfirst, hcircle⟩
      have hfirst' := firstConcentratorContact (incomingSunlightRay A x) s Q hfirst
      rw [incoming] at hfirst'
      exact ⟨k * s, T Q, hfirst', (onAbsorber Q).2 hcircle⟩
    have reflected (x : Length) (h : IsAbsorbedAfterOneReflection A x) :
        IsAbsorbedAfterOneReflection B
          (B.mirror.center.x + k * (x - A.mirror.center.x)) := by
      rcases h with ⟨sMirror, QMirror, hfirst, hMirror,
        sHit, QHit, hhit, hnosecond⟩
      have hfirst' := firstConcentratorContact
        (incomingSunlightRay A x) sMirror QMirror hfirst
      rw [incoming] at hfirst'
      have hMirror' := (onLowerMirror QMirror).2 hMirror
      have hhit' := firstContainerContact
        (rayAfterReflection A.mirror (incomingSunlightRay A x) QMirror hMirror.1)
        sHit QHit hhit
      rw [rayAfter, incoming] at hhit'
      have hnosecond' := noSecondMirrorContact
        (rayAfterReflection A.mirror (incomingSunlightRay A x) QMirror hMirror.1)
        sHit hnosecond
      rw [rayAfter, incoming] at hnosecond'
      exact ⟨k * sMirror, T QMirror, hfirst', hMirror',
        k * sHit, T QHit, hhit', hnosecond'⟩
    constructor
    · intro x hx
      refine ⟨?_, ?_⟩
      · rw [← hR]
        have habs :
            |B.mirror.center.x + k * (x - A.mirror.center.x) -
                B.mirror.center.x| = k * |x - A.mirror.center.x| := by
          rw [show B.mirror.center.x + k * (x - A.mirror.center.x) -
              B.mirror.center.x = k * (x - A.mirror.center.x) by ring,
            abs_mul, abs_of_pos hk]
        rw [habs]
        exact mul_lt_mul_of_pos_left hx.1 hk
      · rcases hx.2 with hdirect | hreflected
        · exact Or.inl (direct x hdirect)
        · exact Or.inr (reflected x hreflected)
    · intro x hx
      change ∃ s : Length, ∃ Q : Point2,
        IsFirstContainerContact A (incomingSunlightRay A x) s Q at hx
      rcases hx with ⟨s, Q, hcontact⟩
      change ∃ s : Length, ∃ Q : Point2,
        IsFirstContainerContact B
          (incomingSunlightRay B
            (B.mirror.center.x + k * (x - A.mirror.center.x))) s Q
      have hcontact' := firstContainerContact
        (incomingSunlightRay A x) s Q hcontact
      rw [incoming] at hcontact'
      exact ⟨k * s, T Q, hcontact'⟩
  let A := X.scalarGeometry
  let B := Y.scalarGeometry
  have hApos : 0 < A.mirror.radius := A.mirror.radius_pos
  have hBpos : 0 < B.mirror.radius := B.mirror.radius_pos
  let k : ℝ := B.mirror.radius / A.mirror.radius
  have hk : 0 < k := div_pos hBpos hApos
  have hR : k * A.mirror.radius = B.mirror.radius := by
    dsimp [k]
    exact div_mul_cancel₀ B.mirror.radius (ne_of_gt hApos)
  have hgeometry : A.absorberRadius * B.mirror.radius =
      B.absorberRadius * A.mirror.radius := by
    simpa [A, B] using compatibleGeometry_scaleRelation X Y θmax hX hY
  have ha : k * A.absorberRadius = B.absorberRadius := by
    dsimp [k]
    rw [div_mul_eq_mul_div, mul_comm B.mirror.radius A.absorberRadius]
    exact (div_eq_iff (ne_of_gt hApos)).2 hgeometry
  have hmapAB := mapApertures A B k hk hR ha
  have hkinv : 0 < k⁻¹ := inv_pos.mpr hk
  have hRinv : k⁻¹ * B.mirror.radius = A.mirror.radius := by
    rw [← hR]
    calc
      k⁻¹ * (k * A.mirror.radius) =
          (k⁻¹ * k) * A.mirror.radius := by ring
      _ = A.mirror.radius := by rw [inv_mul_cancel₀ (ne_of_gt hk), one_mul]
  have hainv : k⁻¹ * B.absorberRadius = A.absorberRadius := by
    rw [← ha]
    calc
      k⁻¹ * (k * A.absorberRadius) =
          (k⁻¹ * k) * A.absorberRadius := by ring
      _ = A.absorberRadius := by rw [inv_mul_cancel₀ (ne_of_gt hk), one_mul]
  have hmapBA := mapApertures B A k⁻¹ hkinv hRinv hainv
  let f (x : ℝ) : ℝ := B.mirror.center.x + k * (x - A.mirror.center.x)
  have hinverse (x : ℝ) :
      A.mirror.center.x + k⁻¹ * (f x - B.mirror.center.x) = x := by
    dsimp [f]
    rw [show B.mirror.center.x + k * (x - A.mirror.center.x) -
        B.mirror.center.x = k * (x - A.mirror.center.x) by ring]
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hk), one_mul]
    ring
  have hIllSet : illuminatedAperture A = f ⁻¹' illuminatedAperture B := by
    ext x
    change AcceptedIncomingCoordinate A x ↔ AcceptedIncomingCoordinate B (f x)
    constructor
    · exact hmapAB.1 x
    · intro hx
      have hback := hmapBA.1 (f x) hx
      rw [hinverse] at hback
      exact hback
  have hRefSet :
      unmirroredReferenceAperture A =
        f ⁻¹' unmirroredReferenceAperture B := by
    ext x
    constructor
    · exact hmapAB.2 x
    · intro hx
      have hback := hmapBA.2 (f x) hx
      rw [hinverse] at hback
      exact hback
  let b : ℝ := B.mirror.center.x - k * A.mirror.center.x
  have hpreimage (S : Set ℝ) :
      f ⁻¹' S =
        (fun x : ℝ => k * x) ⁻¹' ((fun y : ℝ => b + y) ⁻¹' S) := by
    ext x
    change f x ∈ S ↔ b + k * x ∈ S
    have hargument : f x = b + k * x := by
      dsimp [f, b]
      ring
    rw [hargument]
  have hvolume (S : Set ℝ) :
      MeasureTheory.volume (f ⁻¹' S) =
        ENNReal.ofReal |k⁻¹| * MeasureTheory.volume S := by
    rw [hpreimage, Real.volume_preimage_mul_left (ne_of_gt hk),
      MeasureTheory.measure_preimage_add]
  have hIllVolume :
      MeasureTheory.volume (illuminatedAperture A) =
        ENNReal.ofReal |k⁻¹| * MeasureTheory.volume (illuminatedAperture B) := by
    rw [hIllSet]
    exact hvolume (illuminatedAperture B)
  have hRefVolume :
      MeasureTheory.volume (unmirroredReferenceAperture A) =
        ENNReal.ofReal |k⁻¹| *
          MeasureTheory.volume (unmirroredReferenceAperture B) := by
    rw [hRefSet]
    exact hvolume (unmirroredReferenceAperture B)
  have hIllReal :
      (MeasureTheory.volume (illuminatedAperture A)).toReal =
        k⁻¹ * (MeasureTheory.volume (illuminatedAperture B)).toReal := by
    rw [hIllVolume, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg k⁻¹)]
    rw [abs_of_pos hkinv]
  have hRefReal :
      (MeasureTheory.volume (unmirroredReferenceAperture A)).toReal =
        k⁻¹ *
          (MeasureTheory.volume (unmirroredReferenceAperture B)).toReal := by
    rw [hRefVolume, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg k⁻¹)]
    rw [abs_of_pos hkinv]
  have hIllCoordX :
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI X.sourceUnits
          (transverseFluxMeasure X.sourceUnits A X.illuminatedMeasurable) =
        (MeasureTheory.volume (illuminatedAperture A)).toReal :=
    (quantityFromSICoordinate_roundtrip X.sourceUnits
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.lengthDimension
      (MeasureTheory.volume (illuminatedAperture A)).toReal
      (transverseFluxMeasure X.sourceUnits A X.illuminatedMeasurable)).1
  have hIllCoordY :
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Y.sourceUnits
          (transverseFluxMeasure Y.sourceUnits B Y.illuminatedMeasurable) =
        (MeasureTheory.volume (illuminatedAperture B)).toReal :=
    (quantityFromSICoordinate_roundtrip Y.sourceUnits
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.lengthDimension
      (MeasureTheory.volume (illuminatedAperture B)).toReal
      (transverseFluxMeasure Y.sourceUnits B Y.illuminatedMeasurable)).1
  have hRefCoordX :
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI X.sourceUnits
          (referenceTransverseMeasure X.sourceUnits A X.referenceMeasurable) =
        (MeasureTheory.volume (unmirroredReferenceAperture A)).toReal :=
    (quantityFromSICoordinate_roundtrip X.sourceUnits
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.lengthDimension
      (MeasureTheory.volume (unmirroredReferenceAperture A)).toReal
      (referenceTransverseMeasure X.sourceUnits A X.referenceMeasurable)).1
  have hRefCoordY :
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Y.sourceUnits
          (referenceTransverseMeasure Y.sourceUnits B Y.referenceMeasurable) =
        (MeasureTheory.volume (unmirroredReferenceAperture B)).toReal :=
    (quantityFromSICoordinate_roundtrip Y.sourceUnits
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.lengthDimension
      (MeasureTheory.volume (unmirroredReferenceAperture B)).toReal
      (referenceTransverseMeasure Y.sourceUnits B Y.referenceMeasurable)).1
  dsimp only
  change
    Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI X.sourceUnits
          (transverseFluxMeasure X.sourceUnits A X.illuminatedMeasurable) *
        B.mirror.radius =
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Y.sourceUnits
          (transverseFluxMeasure Y.sourceUnits B Y.illuminatedMeasurable) *
        A.mirror.radius ∧
    Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI X.sourceUnits
          (referenceTransverseMeasure X.sourceUnits A X.referenceMeasurable) *
        B.mirror.radius =
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Y.sourceUnits
          (referenceTransverseMeasure Y.sourceUnits B Y.referenceMeasurable) *
        A.mirror.radius
  rw [hIllCoordX, hIllCoordY, hRefCoordX, hRefCoordY, hIllReal, hRefReal,
    ← hR]
  have hcancel (z r : ℝ) : k⁻¹ * z * (k * r) = z * r := by
    calc
      k⁻¹ * z * (k * r) = (k⁻¹ * k) * (z * r) := by ring
      _ = z * r := by rw [inv_mul_cancel₀ (ne_of_gt hk), one_mul]
  exact ⟨hcancel _ _, hcancel _ _⟩

/-- The illuminated/reference transverse-measure ratio is invariant between
compatible realizations, expressed without division. -/
lemma compatibleTransverseRatio_cross_eq (X Y : SolarCookerRealization)
    (θmax : ℝ) (hX : X.CompatibleAtLimitingAngle θmax)
    (hY : Y.CompatibleAtLimitingAngle θmax) :
    let μX :=
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI X.sourceUnits
        (transverseFluxMeasure X.sourceUnits X.scalarGeometry
          X.illuminatedMeasurable)
    let μY :=
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Y.sourceUnits
        (transverseFluxMeasure Y.sourceUnits Y.scalarGeometry
          Y.illuminatedMeasurable)
    let μ0X :=
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI X.sourceUnits
        (referenceTransverseMeasure X.sourceUnits X.scalarGeometry
          X.referenceMeasurable)
    let μ0Y :=
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Y.sourceUnits
        (referenceTransverseMeasure Y.sourceUnits Y.scalarGeometry
          Y.referenceMeasurable)
    μX * μ0Y = μY * μ0X := by
  have hscale := compatibleApertures_scale X Y θmax hX hY
  dsimp only at hscale ⊢
  rcases hscale with ⟨hill, href⟩
  let μX : ℝ :=
    Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI X.sourceUnits
      (transverseFluxMeasure X.sourceUnits X.scalarGeometry
        X.illuminatedMeasurable)
  let μY : ℝ :=
    Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Y.sourceUnits
      (transverseFluxMeasure Y.sourceUnits Y.scalarGeometry
        Y.illuminatedMeasurable)
  let μ0X : ℝ :=
    Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI X.sourceUnits
      (referenceTransverseMeasure X.sourceUnits X.scalarGeometry
        X.referenceMeasurable)
  let μ0Y : ℝ :=
    Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Y.sourceUnits
      (referenceTransverseMeasure Y.sourceUnits Y.scalarGeometry
        Y.referenceMeasurable)
  change μX * Y.scalarGeometry.mirror.radius =
    μY * X.scalarGeometry.mirror.radius at hill
  change μ0X * Y.scalarGeometry.mirror.radius =
    μ0Y * X.scalarGeometry.mirror.radius at href
  change μX * μ0Y = μY * μ0X
  apply mul_right_cancel₀ (ne_of_gt Y.scalarGeometry.mirror.radius_pos)
  calc
    (μX * μ0Y) * Y.scalarGeometry.mirror.radius =
        (μX * Y.scalarGeometry.mirror.radius) * μ0Y := by ring
    _ = (μY * X.scalarGeometry.mirror.radius) * μ0Y := by rw [hill]
    _ = μY * (μ0Y * X.scalarGeometry.mirror.radius) := by ring
    _ = μY * (μ0X * Y.scalarGeometry.mirror.radius) := by rw [← href]
    _ = (μY * μ0X) * Y.scalarGeometry.mirror.radius := by ring

/-- Compatible realizations at one limiting angle have the same accepted
power-ratio witness. -/
theorem compatiblePowerRatios_eq (X Y : SolarCookerRealization)
    (θmax ρX ρY : ℝ) (hX : X.CompatibleAtLimitingAngle θmax)
    (hY : Y.CompatibleAtLimitingAngle θmax)
    (hρX : X.HasPowerRatio ρX) (hρY : Y.HasPowerRatio ρY) :
    ρX = ρY := by
  have transverse_ratio (Z : SolarCookerRealization) (ρ : ℝ)
      (hρ : Z.HasPowerRatio ρ) :
      Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Z.sourceUnits
          (transverseFluxMeasure Z.sourceUnits Z.scalarGeometry
            Z.illuminatedMeasurable) =
        ρ * Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
          Z.sourceUnits
          (referenceTransverseMeasure Z.sourceUnits Z.scalarGeometry
            Z.referenceMeasurable) := by
    change IsPowerRatio Z.sourceUnits Z.geometry Z.oneReflection
      Z.illuminatedMeasurable Z.referenceMeasurable Z.irradiance
      Z.uniformIrradiance Z.axialExtent Z.positiveAxialExtent Z.power
      Z.referencePower ρ at hρ
    rcases hρ with ⟨⟨habsorbed, hreference⟩, _hP0pos, hratio⟩
    have hmeasures := transverseMeasures_coordinate Z.sourceUnits Z.scalarGeometry
      Z.illuminatedMeasurable Z.referenceMeasurable
    have harea := collectingArea_coordinate Z.sourceUnits
      (transverseFluxMeasure Z.sourceUnits Z.scalarGeometry
        Z.illuminatedMeasurable)
      Z.axialExtent hmeasures.2.2.1 Z.positiveAxialExtent
    have harea0 := collectingArea_coordinate Z.sourceUnits
      (referenceTransverseMeasure Z.sourceUnits Z.scalarGeometry
        Z.referenceMeasurable)
      Z.axialExtent hmeasures.2.2.2.1 Z.positiveAxialExtent
    have habsorbed_scalar :
        Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
            Z.sourceUnits Z.power =
          Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
              Z.sourceUnits Z.irradiance *
            (Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
                Z.sourceUnits
                (transverseFluxMeasure Z.sourceUnits Z.scalarGeometry
                  Z.illuminatedMeasurable) *
              Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
                Z.sourceUnits Z.axialExtent) := by
      change Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
          Z.sourceUnits Z.power =
        Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
            Z.sourceUnits Z.irradiance *
          Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Z.sourceUnits
            (collectingArea Z.sourceUnits
              (transverseFluxMeasure Z.sourceUnits Z.scalarGeometry
                Z.illuminatedMeasurable) Z.axialExtent) at habsorbed
      rw [habsorbed, harea.1]
    have hreference_scalar :
        Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
            Z.sourceUnits Z.referencePower =
          Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
              Z.sourceUnits Z.irradiance *
            (Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
                Z.sourceUnits
                (referenceTransverseMeasure Z.sourceUnits Z.scalarGeometry
                  Z.referenceMeasurable) *
              Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
                Z.sourceUnits Z.axialExtent) := by
      change Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
          Z.sourceUnits Z.referencePower =
        Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
            Z.sourceUnits Z.irradiance *
          Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Z.sourceUnits
            (collectingArea Z.sourceUnits
              (referenceTransverseMeasure Z.sourceUnits Z.scalarGeometry
                Z.referenceMeasurable) Z.axialExtent) at hreference
      rw [hreference, harea0.1]
    have hL :
        0 < Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
          Z.sourceUnits Z.axialExtent := Z.positiveAxialExtent
    have hfactor :
        Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
              Z.sourceUnits Z.irradiance *
            Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
              Z.sourceUnits Z.axialExtent ≠ 0 :=
      ne_of_gt (mul_pos Z.irradiance_pos hL)
    apply mul_left_cancel₀ hfactor
    calc
      (_ * _) * _ =
          Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
              Z.sourceUnits Z.irradiance *
            (Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
                Z.sourceUnits
                (transverseFluxMeasure Z.sourceUnits Z.scalarGeometry
                  Z.illuminatedMeasurable) *
              Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
                Z.sourceUnits Z.axialExtent) := by ring
      _ = Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
            Z.sourceUnits Z.power := habsorbed_scalar.symm
      _ = ρ * Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
            Z.sourceUnits Z.referencePower := hratio
      _ = ρ *
          (Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
              Z.sourceUnits Z.irradiance *
            (Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
                Z.sourceUnits
                (referenceTransverseMeasure Z.sourceUnits Z.scalarGeometry
                  Z.referenceMeasurable) *
              Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI
                Z.sourceUnits Z.axialExtent)) := by rw [hreference_scalar]
      _ = (_ * _) * (ρ * _) := by ring
  have htransverseX := transverse_ratio X ρX hρX
  have htransverseY := transverse_ratio Y ρY hρY
  have hcross := compatibleTransverseRatio_cross_eq X Y θmax hX hY
  dsimp only at hcross
  have hrefX := referenceTransverseMeasure_pos X.sourceUnits X.geometry
    X.referenceMeasurable
  have hRefY := referenceTransverseMeasure_pos Y.sourceUnits Y.geometry
    Y.referenceMeasurable
  let μX : ℝ :=
    Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI X.sourceUnits
      (transverseFluxMeasure X.sourceUnits X.scalarGeometry
        X.illuminatedMeasurable)
  let μY : ℝ :=
    Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Y.sourceUnits
      (transverseFluxMeasure Y.sourceUnits Y.scalarGeometry
        Y.illuminatedMeasurable)
  let μ0X : ℝ :=
    Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI X.sourceUnits
      (referenceTransverseMeasure X.sourceUnits X.scalarGeometry
        X.referenceMeasurable)
  let μ0Y : ℝ :=
    Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI Y.sourceUnits
      (referenceTransverseMeasure Y.sourceUnits Y.scalarGeometry
        Y.referenceMeasurable)
  change μX = ρX * μ0X at htransverseX
  change μY = ρY * μ0Y at htransverseY
  change μX * μ0Y = μY * μ0X at hcross
  change 0 < μ0X at hrefX
  change 0 < μ0Y at hRefY
  apply mul_right_cancel₀ (mul_ne_zero (ne_of_gt hrefX) (ne_of_gt hRefY))
  calc
    ρX * (μ0X * μ0Y) = μX * μ0Y := by rw [htransverseX]; ring
    _ = μY * μ0X := hcross
    _ = ρY * (μ0X * μ0Y) := by rw [htransverseY]; ring

/-- `ρ` is the ratio determined by `θmax` when compatible realizations exist
and every such realization has accepted power ratio `ρ`. -/
def IsPowerRatioAtLimitingAngle (θmax ρ : ℝ) : Prop :=
  (∃ X : SolarCookerRealization, X.CompatibleAtLimitingAngle θmax) ∧
    ∀ X : SolarCookerRealization,
      X.CompatibleAtLimitingAngle θmax → X.HasPowerRatio ρ

/-- Every physically realizable limiting angle determines one and only one
power ratio, without exposing its evaluated value in the theorem signature. -/
theorem existsUnique_powerRatioAtLimitingAngle (θmax : ℝ)
    (hθ : IsRealizableLimitingAngle θmax) :
    ∃! ρ : ℝ, IsPowerRatioAtLimitingAngle θmax ρ := by
  rcases hθ.2.2 with ⟨X, hX⟩
  rcases X.existsUnique_powerRatio with ⟨ρ, hρ, hρunique⟩
  refine ⟨ρ, ⟨⟨X, hX⟩, ?_⟩, ?_⟩
  · intro Y hY
    rcases Y.existsUnique_powerRatio with ⟨ρY, hρY, _hρYunique⟩
    have heq := compatiblePowerRatios_eq X Y θmax ρ ρY hX hY hρ hρY
    rw [heq]
    exact hρY
  · intro ρ' hρ'
    exact hρunique ρ' (hρ'.2 X hX)

end Ipho2026Gpt56solBlind.ProblemIPhO2026_2_B_2
