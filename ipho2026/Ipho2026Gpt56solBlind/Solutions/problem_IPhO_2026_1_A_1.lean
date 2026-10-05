import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic
import Ipho2026Gpt56solBlind.Shared.ISQDimensions

/-!
# IPhO 2026 Problem 1A.1: hydrostatic cube gate

This file gives an answer-free model of the cube gate in Figure 1a.  All
dimensioned quantities are retained as ISQ-indexed `WithDim` values.  The
surface-load calculation is performed only after explicitly taking coherent-SI
coordinates.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_1_A_1

open scoped Interval
open Ipho2026Gpt56solBlind.Shared.ISQDimensions

noncomputable section

/-! ## Dimensioned source data -/

/-- Acceleration has dimension length per time squared. -/
def accelerationDimension : Dimension ISQDimensionBase :=
  lengthDimension * (timeDimension ^ (2 : ℕ))⁻¹

/-- Force has dimension mass times acceleration. -/
def forceDimension : Dimension ISQDimensionBase :=
  massDimension * accelerationDimension

/-- Torque has dimension force times length. -/
def torqueDimension : Dimension ISQDimensionBase :=
  forceDimension * lengthDimension

/-- Acceleration quantities expressed in the shared ISQ basis. -/
abbrev Acceleration := Quantity accelerationDimension

/-- Force quantities expressed in the shared ISQ basis. -/
abbrev Force := Quantity forceDimension

/-- Signed torque quantities expressed in the shared ISQ basis. -/
abbrev Torque := Quantity torqueDimension

/-- The coherent-SI real coordinate of a dimensioned quantity. -/
def coherentSICoordinate {d : Dimension ISQDimensionBase}
    (q : Quantity d) : ℝ :=
  coordinateInSI SIUnitChoices.SI q

/-- The dimensional source data stated in the problem.  Gravity is represented
by its positive magnitude; its spatial direction is fixed to be downward in
the force definitions below. -/
structure HydrostaticData where
  waterDensity : MassDensity
  gravityMagnitude : Acceleration
  maximumLevelDifference : Length

/-- Positivity of the material data and the exact stated value `1.41 m` for
the maximum permitted difference. -/
def HydrostaticData.IsSourceData (D : HydrostaticData) : Prop :=
  0 < coherentSICoordinate D.waterDensity ∧
    0 < coherentSICoordinate D.gravityMagnitude ∧
    coherentSICoordinate D.maximumLevelDifference = (141 : ℝ) / 100

/-- The block has exactly three times the density of water. -/
def blockDensity (D : HydrostaticData) : MassDensity :=
  ⟨3 * coherentSICoordinate D.waterDensity⟩

/-! ## Figure 1a geometry -/

/-- A point in the plane of Figure 1a, using coherent-SI metre coordinates.
The `x` direction points from the left reservoir to the right reservoir and
`z` points vertically upward. -/
structure PlanarPointSI where
  x : ℝ
  z : ℝ

/-- The reservoir supplying the pressure on a wetted patch. -/
inductive ReservoirSide where
  | left
  | right
  deriving DecidableEq, Fintype

/-- The six torque-carrying pieces of the four lateral cube faces.  The two
faces normal to the hinge axis have zero moment about that axis and are not
included. -/
inductive WettedPatch where
  | leftUpper
  | leftLower
  | rightUpper
  | rightTop
  | rightBottom
  | rightLower
  deriving DecidableEq, Fintype

/-- A candidate gate configuration.  The left free-surface coordinate is the
right coordinate plus `levelDifference`; all three stored lengths remain
dimensioned quantities.  The fixed vertices, face parameterizations, normals,
and patch divisions from Figure 1a are used explicitly in the traction and
moment definitions below. -/
structure CubeGateGeometry where
  sideLength : Length
  levelDifference : Length
  rightFreeSurfaceHeight : Length

/-- The cube side is positive, the left-minus-right level difference is
nonnegative, and the right free surface lies strictly above the top vertex
`T`, whose height above the hinge is `a / (2 * sqrt 2)`.  Hence the whole cube
is submerged on both sides. -/
def CubeGateGeometry.IsPhysical (G : CubeGateGeometry) : Prop :=
  0 < coherentSICoordinate G.sideLength ∧
    0 ≤ coherentSICoordinate G.levelDifference ∧
    coherentSICoordinate G.sideLength /
        (2 * Real.sqrt 2) <
      coherentSICoordinate G.rightFreeSurfaceHeight

/-! ## Hydrostatic loads and their moments about the hinge -/

/-- Gauge pressure at a planar point.  It vanishes at the selected reservoir's
free surface and grows linearly with depth. -/
def hydrostaticPressure (D : HydrostaticData) (G : CubeGateGeometry)
    (side : ReservoirSide) (point : PlanarPointSI) : Pressure :=
  let freeSurfaceHeight :=
    match side with
    | .left =>
        coherentSICoordinate G.rightFreeSurfaceHeight +
          coherentSICoordinate G.levelDifference
    | .right => coherentSICoordinate G.rightFreeSurfaceHeight
  ⟨coherentSICoordinate D.waterDensity *
      coherentSICoordinate D.gravityMagnitude *
      (freeSurfaceHeight - point.z)⟩

/-- Coherent-SI pressure-traction coordinates on a wetted patch at arclength
`s`.  The four face directions are based on
`e = (1,1)/sqrt 2` and `f = (1,-1)/sqrt 2`; the traction is opposite the
outward cube normal. -/
def pressureTractionSI (D : HydrostaticData) (G : CubeGateGeometry)
    (patch : WettedPatch) (s : ℝ) : ℝ × ℝ :=
  let c : ℝ := 1 / Real.sqrt 2
  let a := coherentSICoordinate G.sideLength
  let point : PlanarPointSI :=
    match patch with
    | .leftUpper | .rightUpper =>
        ⟨s * c, s * c⟩
    | .rightTop =>
        ⟨a / 2 * c + s * c, a / 2 * c - s * c⟩
    | .rightBottom =>
        ⟨a / 2 * c + a * c - s * c,
          a / 2 * c - a * c - s * c⟩
    | .leftLower | .rightLower =>
        ⟨-(a / 2) * c + s * c, -(a / 2) * c - s * c⟩
  let outwardNormal : ℝ × ℝ :=
    match patch with
    | .leftUpper | .rightUpper => (-c, c)
    | .rightTop => (c, c)
    | .rightBottom => (c, -c)
    | .leftLower | .rightLower => (-c, -c)
  let side : ReservoirSide :=
    match patch with
    | .leftUpper | .leftLower => .left
    | .rightUpper | .rightTop | .rightBottom | .rightLower => .right
  let pressure := coherentSICoordinate (hydrostaticPressure D G side point)
  (-pressure * outwardNormal.1, -pressure * outwardNormal.2)

/-- Signed opening torque from one wetted patch.  The outer integral follows
the appropriate face-centerline interval, while the inner integral traverses
the full transverse cube width `[-a/2,a/2]`.  Positive scalar moment is
`x F_z - z F_x`, i.e. counterclockwise in the figure. -/
def patchOpeningTorque (D : HydrostaticData) (G : CubeGateGeometry)
    (patch : WettedPatch) : Torque :=
  let c : ℝ := 1 / Real.sqrt 2
  let a := coherentSICoordinate G.sideLength
  let lower : ℝ :=
    match patch with
    | .leftUpper => -a / 2
    | .leftLower | .rightUpper | .rightTop | .rightBottom => 0
    | .rightLower => a / 2
  let upper : ℝ :=
    match patch with
    | .leftUpper => 0
    | .leftLower | .rightUpper => a / 2
    | .rightTop | .rightBottom | .rightLower => a
  let point : ℝ → PlanarPointSI := fun s =>
    match patch with
    | .leftUpper | .rightUpper =>
        ⟨s * c, s * c⟩
    | .rightTop =>
        ⟨a / 2 * c + s * c, a / 2 * c - s * c⟩
    | .rightBottom =>
        ⟨a / 2 * c + a * c - s * c,
          a / 2 * c - a * c - s * c⟩
    | .leftLower | .rightLower =>
        ⟨-(a / 2) * c + s * c, -(a / 2) * c - s * c⟩
  ⟨∫ s in lower..upper,
      ∫ _y in -a / 2..a / 2,
        (point s).x * (pressureTractionSI D G patch s).2 -
          (point s).z * (pressureTractionSI D G patch s).1⟩

/-- Total moment of the complete piecewise left/right hydrostatic pressure
field on the six wetted lateral patches. -/
def surfaceOpeningTorque (D : HydrostaticData) (G : CubeGateGeometry) : Torque :=
  ⟨∑ patch : WettedPatch,
      coherentSICoordinate (patchOpeningTorque D G patch)⟩

/-- The displaced volume of the fully submerged cube. -/
def cubeVolume (G : CubeGateGeometry) : Volume :=
  ⟨(coherentSICoordinate G.sideLength) ^ (3 : ℕ)⟩

/-- Magnitude of the block's weight, using the stated block density. -/
def weightMagnitude (D : HydrostaticData) (G : CubeGateGeometry) : Force :=
  ⟨coherentSICoordinate (blockDensity D) *
      coherentSICoordinate D.gravityMagnitude *
      coherentSICoordinate (cubeVolume G)⟩

/-- Opening moment of the downward weight applied at the cube center
`C = (a/(2 sqrt 2), -a/(2 sqrt 2))`. -/
def weightOpeningTorque (D : HydrostaticData) (G : CubeGateGeometry) : Torque :=
  let centerX := coherentSICoordinate G.sideLength / (2 * Real.sqrt 2)
  let centerZ := -coherentSICoordinate G.sideLength / (2 * Real.sqrt 2)
  ⟨centerX * (-coherentSICoordinate (weightMagnitude D G)) - centerZ * 0⟩

/-- Magnitude of the upward buoyant force on the fully submerged cube. -/
def buoyantForceMagnitude (D : HydrostaticData) (G : CubeGateGeometry) : Force :=
  ⟨coherentSICoordinate D.waterDensity *
      coherentSICoordinate D.gravityMagnitude *
      coherentSICoordinate (cubeVolume G)⟩

/-- Opening moment of buoyancy, applied upward through the center of displaced
volume, which is the cube center `C`. -/
def buoyancyOpeningTorque (D : HydrostaticData) (G : CubeGateGeometry) : Torque :=
  let centerX := coherentSICoordinate G.sideLength / (2 * Real.sqrt 2)
  let centerZ := -coherentSICoordinate G.sideLength / (2 * Real.sqrt 2)
  ⟨centerX * coherentSICoordinate (buoyantForceMagnitude D G) - centerZ * 0⟩

/-- The pressure-imbalance part of the surface moment.  This is a decomposition
of the integrated surface load, not an additional force: buoyancy is already
contained in `surfaceOpeningTorque`. -/
def differentialPressureOpeningTorque (D : HydrostaticData)
    (G : CubeGateGeometry) : Torque :=
  surfaceOpeningTorque D G - buoyancyOpeningTorque D G

/-- Net signed moment about the frictionless hinge.  A positive value tends to
open the gate; a nonpositive value does not. -/
def netOpeningTorque (D : HydrostaticData) (G : CubeGateGeometry) : Torque :=
  weightOpeningTorque D G + buoyancyOpeningTorque D G +
    differentialPressureOpeningTorque D G

/-! ## Answer-free threshold characterization -/

/-- A nonnegative level difference is admissible when there exists at least
one fully submerged common depth and the gate has nonpositive opening moment
at every fully submerged common depth.  The existential conjunct prevents the
universal condition from becoming vacuous. -/
def AdmissibleLevelDifference (D : HydrostaticData) (a delta : Length) : Prop :=
  0 < coherentSICoordinate a ∧
    0 ≤ coherentSICoordinate delta ∧
    (∃ hR : Length,
      (CubeGateGeometry.mk a delta hR).IsPhysical) ∧
    ∀ hR : Length,
      (CubeGateGeometry.mk a delta hR).IsPhysical →
        coherentSICoordinate
            (netOpeningTorque D (CubeGateGeometry.mk a delta hR)) ≤ 0

/-- The nonvacuous zero-net-moment condition at a specified level difference.
This governing equality alone does not assert that the difference is maximal. -/
def ZeroNetTorqueBoundary (D : HydrostaticData) (a delta : Length) : Prop :=
  0 < coherentSICoordinate a ∧
    0 ≤ coherentSICoordinate delta ∧
    (∃ hR : Length,
      (CubeGateGeometry.mk a delta hR).IsPhysical) ∧
    ∀ hR : Length,
      (CubeGateGeometry.mk a delta hR).IsPhysical →
        coherentSICoordinate
            (netOpeningTorque D (CubeGateGeometry.mk a delta hR)) = 0

/-- `a` solves the requested design problem: the stated level difference is
admissible and is a zero-moment boundary, all smaller nonnegative differences
remain admissible, and every larger difference is inadmissible.  No value of
`a` is built into this predicate. -/
def MaximumPermissibleSide (D : HydrostaticData) (a : Length) : Prop :=
  0 < coherentSICoordinate a ∧
    AdmissibleLevelDifference D a D.maximumLevelDifference ∧
    ZeroNetTorqueBoundary D a D.maximumLevelDifference ∧
    (∀ delta : Length,
      0 ≤ coherentSICoordinate delta ∧
          coherentSICoordinate delta <
            coherentSICoordinate D.maximumLevelDifference →
        AdmissibleLevelDifference D a delta) ∧
    ∀ delta : Length,
      coherentSICoordinate D.maximumLevelDifference <
          coherentSICoordinate delta →
        ¬AdmissibleLevelDifference D a delta

/-- For valid source data, exactly one dimensioned cube side realizes the
prescribed maximum permissible level difference. -/
theorem existsUnique_maximumPermissibleSide (D : HydrostaticData)
    (hD : D.IsSourceData) :
    ∃! a : Length, MaximumPermissibleSide D a := by
  have integral_id_basic (p q : ℝ) :
      (∫ x in p..q, x) = (q ^ 2 - p ^ 2) / 2 := by
    have hconst :
        IntervalIntegrable (fun _ : ℝ => p + q) MeasureTheory.volume p q :=
      intervalIntegrable_const
    have hid :
        IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume p q :=
      continuous_id.intervalIntegrable p q
    have hreflect :=
      intervalIntegral.integral_comp_sub_left (fun x : ℝ => x) (p + q)
        (a := p) (b := q)
    rw [intervalIntegral.integral_sub hconst hid,
      intervalIntegral.integral_const] at hreflect
    rw [smul_eq_mul] at hreflect
    ring_nf at hreflect ⊢
    linarith
  have integral_sq_basic (p q : ℝ) :
      (∫ x in p..q, x ^ 2) = (q ^ 3 - p ^ 3) / 3 := by
    have integral_sq_zero (t : ℝ) :
        (∫ x in (0 : ℝ)..t, x ^ 2) = t ^ 3 / 3 := by
      let K : ℝ := ∫ x in (0 : ℝ)..t, x ^ 2
      let Kh : ℝ := ∫ x in (0 : ℝ)..t / 2, x ^ 2
      have hcont0h :
          IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume
            0 (t / 2) :=
        (continuous_id.pow 2).intervalIntegrable 0 (t / 2)
      have hcontht :
          IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume
            (t / 2) t :=
        (continuous_id.pow 2).intervalIntegrable (t / 2) t
      have hadd :=
        intervalIntegral.integral_add_adjacent_intervals hcont0h hcontht
      have hreflect_raw :=
        intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 2) t
          (a := 0) (b := t / 2)
      have hreflect :
          (∫ x in (0 : ℝ)..t / 2, (t - x) ^ 2) =
            ∫ x in t / 2..t, x ^ 2 := by
        convert hreflect_raw using 1
        all_goals ring_nf
      have hscale_raw :=
        intervalIntegral.integral_comp_mul_left (fun x : ℝ => x ^ 2)
          (show (2 : ℝ) ≠ 0 from two_ne_zero) (a := 0) (b := t / 2)
      have hscale : 4 * Kh = K / 2 := by
        dsimp [K, Kh]
        calc
          4 * (∫ x in (0 : ℝ)..t / 2, x ^ 2) =
              ∫ x in (0 : ℝ)..t / 2, (2 * x) ^ 2 := by
                rw [show (fun x : ℝ => (2 * x) ^ 2) =
                    fun x => 4 * x ^ 2 by
                      funext x
                      ring,
                  intervalIntegral.integral_const_mul]
          _ = (2 : ℝ)⁻¹ • ∫ x in 2 * 0..2 * (t / 2), x ^ 2 :=
            hscale_raw
          _ = (∫ x in (0 : ℝ)..t, x ^ 2) / 2 := by
            rw [smul_eq_mul, mul_zero]
            rw [show 2 * (t / 2) = t by ring]
            ring
      have hreflect_eval :
          (∫ x in (0 : ℝ)..t / 2, (t - x) ^ 2) =
            Kh - 2 * t * ((t / 2) ^ 2 / 2) + (t / 2) * t ^ 2 := by
        dsimp [Kh]
        calc
          (∫ x in (0 : ℝ)..t / 2, (t - x) ^ 2) =
              ∫ x in (0 : ℝ)..t / 2,
                x ^ 2 + ((-2 * t) * x + t ^ 2) := by
                  apply intervalIntegral.integral_congr
                  intro x hx
                  ring
          _ = (∫ x in (0 : ℝ)..t / 2, x ^ 2) +
                ∫ x in (0 : ℝ)..t / 2, ((-2 * t) * x + t ^ 2) := by
                  rw [intervalIntegral.integral_add
                    (by
                      apply Continuous.intervalIntegrable
                      fun_prop)
                    (by
                      apply Continuous.intervalIntegrable
                      fun_prop)]
          _ = (∫ x in (0 : ℝ)..t / 2, x ^ 2) +
                ((-2 * t) * (∫ x in (0 : ℝ)..t / 2, x) +
                  ∫ _x in (0 : ℝ)..t / 2, t ^ 2) := by
                    rw [intervalIntegral.integral_add
                      (by
                        apply Continuous.intervalIntegrable
                        fun_prop)
                      (by
                        apply Continuous.intervalIntegrable
                        fun_prop),
                      intervalIntegral.integral_const_mul]
          _ = _ := by
            rw [integral_id_basic, intervalIntegral.integral_const]
            rw [smul_eq_mul, sub_zero]
            ring
      rw [← hreflect] at hadd
      rw [hreflect_eval] at hadd
      dsimp [K, Kh] at hadd hscale ⊢
      ring_nf at hadd hscale ⊢
      linarith
    have hshift_raw :=
      intervalIntegral.integral_comp_add_right (fun x : ℝ => x ^ 2) p
        (a := 0) (b := q - p)
    have hshift :
        (∫ x in (0 : ℝ)..q - p, (x + p) ^ 2) =
          ∫ x in p..q, x ^ 2 := by
      convert hshift_raw using 1
      all_goals ring_nf
    have hshift_eval :
        (∫ x in (0 : ℝ)..q - p, (x + p) ^ 2) =
          (q - p) ^ 3 / 3 +
            2 * p * ((q - p) ^ 2 / 2) + (q - p) * p ^ 2 := by
      calc
        (∫ x in (0 : ℝ)..q - p, (x + p) ^ 2) =
            ∫ x in (0 : ℝ)..q - p,
              x ^ 2 + (2 * p * x + p ^ 2) := by
                apply intervalIntegral.integral_congr
                intro x hx
                ring
        _ = (∫ x in (0 : ℝ)..q - p, x ^ 2) +
              ∫ x in (0 : ℝ)..q - p, (2 * p * x + p ^ 2) := by
                rw [intervalIntegral.integral_add
                  (by
                    apply Continuous.intervalIntegrable
                    fun_prop)
                  (by
                    apply Continuous.intervalIntegrable
                    fun_prop)]
        _ = (∫ x in (0 : ℝ)..q - p, x ^ 2) +
              (2 * p * (∫ x in (0 : ℝ)..q - p, x) +
                ∫ _x in (0 : ℝ)..q - p, p ^ 2) := by
                  rw [intervalIntegral.integral_add
                    (by
                      apply Continuous.intervalIntegrable
                      fun_prop)
                    (by
                      apply Continuous.intervalIntegrable
                      fun_prop),
                    intervalIntegral.integral_const_mul]
        _ = _ := by
          rw [integral_sq_zero, integral_id_basic,
            intervalIntegral.integral_const]
          rw [smul_eq_mul, sub_zero]
          ring
    rw [← hshift]
    rw [hshift_eval]
    ring
  have integral_quadratic (A B C p q : ℝ) :
      (∫ x in p..q, A * x ^ 2 + B * x + C) =
        A * (q ^ 3 - p ^ 3) / 3 +
          B * (q ^ 2 - p ^ 2) / 2 + C * (q - p) := by
    rw [intervalIntegral.integral_add
        (by
          apply Continuous.intervalIntegrable
          fun_prop)
        (by
          apply Continuous.intervalIntegrable
          fun_prop),
      intervalIntegral.integral_add
        (by
          apply Continuous.intervalIntegrable
          fun_prop)
        (by
          apply Continuous.intervalIntegrable
          fun_prop),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_sq_basic, integral_id_basic,
      intervalIntegral.integral_const]
    rw [smul_eq_mul]
    ring
  let qa : (ℝ → ℝ) → ℝ := fun f => (f 1 + f (-1) - 2 * f 0) / 2
  let qb : (ℝ → ℝ) → ℝ := fun f => (f 1 - f (-1)) / 2
  let qc : (ℝ → ℝ) → ℝ := fun f => f 0
  have integrate_quadratic (f : ℝ → ℝ) (p q : ℝ)
      (hf : ∀ x, f x = qa f * x ^ 2 + qb f * x + qc f) :
      (∫ x in p..q, f x) =
        qa f * (q ^ 3 - p ^ 3) / 3 +
          qb f * (q ^ 2 - p ^ 2) / 2 + qc f * (q - p) := by
    rw [intervalIntegral.integral_congr (fun x hx => hf x)]
    exact integral_quadratic (qa f) (qb f) (qc f) p q
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by positivity)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by positivity)
  have hsqrt_cube : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
    calc
      (Real.sqrt 2) ^ 3 = Real.sqrt 2 * (Real.sqrt 2) ^ 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrt_sq]; ring
  have hsqrt_inv_sq : (Real.sqrt 2)⁻¹ ^ 2 = (1 : ℝ) / 2 := by
    rw [inv_pow, hsqrt_sq, one_div]
  have hsqrt_inv_cube : (Real.sqrt 2)⁻¹ ^ 3 = (Real.sqrt 2)⁻¹ / 2 := by
    calc
      (Real.sqrt 2)⁻¹ ^ 3 = (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ ^ 2 := by ring
      _ = (Real.sqrt 2)⁻¹ * ((1 : ℝ) / 2) := by rw [hsqrt_inv_sq]
      _ = (Real.sqrt 2)⁻¹ / 2 := by ring
  have hcoordinate {d : Dimension ISQDimensionBase} (q : Quantity d) :
      coherentSICoordinate q = q.val := by
    exact coordinateInSI_self q
  have hnet (a delta hR : Length) :
      coherentSICoordinate
          (netOpeningTorque D (CubeGateGeometry.mk a delta hR)) =
        coherentSICoordinate D.waterDensity *
          coherentSICoordinate D.gravityMagnitude *
          (coherentSICoordinate a) ^ 3 *
          (coherentSICoordinate delta / 4 -
            coherentSICoordinate a / Real.sqrt 2) := by
    unfold netOpeningTorque differentialPressureOpeningTorque
      weightOpeningTorque weightMagnitude blockDensity cubeVolume
      buoyancyOpeningTorque buoyantForceMagnitude surfaceOpeningTorque
      patchOpeningTorque
    rw [show (Finset.univ : Finset WettedPatch) =
      {.leftUpper, .leftLower, .rightUpper, .rightTop, .rightBottom,
        .rightLower} from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    unfold pressureTractionSI hydrostaticPressure
    repeat' rw [hcoordinate]
    rw [WithDim.val_add, WithDim.val_sub]
    dsimp
    repeat' rw [intervalIntegral.integral_const]
    repeat' rw [smul_eq_mul]
    ring_nf
    repeat' rw [integrate_quadratic]
    all_goals dsimp [qa, qb, qc]
    all_goals try (intro x)
    all_goals repeat' rw [hcoordinate]
    all_goals repeat' rw [intervalIntegral.integral_const]
    all_goals repeat' rw [smul_eq_mul]
    all_goals try ring
    rw [hsqrt_inv_sq, hsqrt_inv_cube]
    ring
  rcases hD with ⟨hρ, hg, hH⟩
  let H : ℝ := coherentSICoordinate D.maximumLevelDifference
  let a₀ : Length := ⟨H * Real.sqrt 2 / 4⟩
  have hH_pos : 0 < H := by
    dsimp [H]
    rw [hH]
    positivity
  have ha₀_pos : 0 < coherentSICoordinate a₀ := by
    rw [hcoordinate]
    dsimp only [a₀]
    positivity
  have hboundary :
      H / 4 - coherentSICoordinate a₀ / Real.sqrt 2 = 0 := by
    rw [hcoordinate]
    dsimp only [a₀]
    calc
      H / 4 - (H * Real.sqrt 2 / 4) / Real.sqrt 2 =
          H / 4 - (H / 4) * (Real.sqrt 2 / Real.sqrt 2) := by ring
      _ = H / 4 - (H / 4) * 1 := by rw [div_self hsqrt_ne]
      _ = 0 := by ring
  have physical_exists (a delta : Length)
      (ha : 0 < coherentSICoordinate a)
      (hdelta : 0 ≤ coherentSICoordinate delta) :
      ∃ hR : Length, (CubeGateGeometry.mk a delta hR).IsPhysical := by
    refine ⟨⟨coherentSICoordinate a / (2 * Real.sqrt 2) + 1⟩, ?_⟩
    refine ⟨ha, hdelta, ?_⟩
    repeat' rw [hcoordinate]
    dsimp only
    linarith
  have admissible_of_le (delta : Length)
      (hdelta_nonneg : 0 ≤ coherentSICoordinate delta)
      (hdelta_le : coherentSICoordinate delta ≤ H) :
      AdmissibleLevelDifference D a₀ delta := by
    refine ⟨ha₀_pos, hdelta_nonneg,
      physical_exists a₀ delta ha₀_pos hdelta_nonneg, ?_⟩
    intro hR hphysical
    rw [hnet]
    have hcoef :
        0 < coherentSICoordinate D.waterDensity *
          coherentSICoordinate D.gravityMagnitude *
          (coherentSICoordinate a₀) ^ 3 := by
      positivity
    have hbracket :
        coherentSICoordinate delta / 4 -
            coherentSICoordinate a₀ / Real.sqrt 2 ≤ 0 := by
      linarith [hboundary]
    exact mul_nonpos_of_nonneg_of_nonpos hcoef.le hbracket
  have zero_boundary :
      ZeroNetTorqueBoundary D a₀ D.maximumLevelDifference := by
    refine ⟨ha₀_pos, hH_pos.le,
      physical_exists a₀ D.maximumLevelDifference ha₀_pos hH_pos.le, ?_⟩
    intro hR hphysical
    rw [hnet]
    change coherentSICoordinate D.waterDensity *
          coherentSICoordinate D.gravityMagnitude *
          coherentSICoordinate a₀ ^ 3 *
        (H / 4 - coherentSICoordinate a₀ / Real.sqrt 2) = 0
    rw [hboundary, mul_zero]
  refine ⟨a₀, ?_, ?_⟩
  · refine ⟨ha₀_pos,
      admissible_of_le D.maximumLevelDifference hH_pos.le le_rfl,
      zero_boundary, ?_, ?_⟩
    · intro delta hdelta
      exact admissible_of_le delta hdelta.1 (le_of_lt hdelta.2)
    · intro delta hdelta_gt hadmissible
      rcases hadmissible with
        ⟨ha, hdelta_nonneg, ⟨hR, hphysical⟩, hall⟩
      have htorque_nonpos := hall hR hphysical
      rw [hnet] at htorque_nonpos
      have hcoef :
          0 < coherentSICoordinate D.waterDensity *
            coherentSICoordinate D.gravityMagnitude *
            (coherentSICoordinate a₀) ^ 3 := by
        positivity
      have hbracket :
          0 < coherentSICoordinate delta / 4 -
            coherentSICoordinate a₀ / Real.sqrt 2 := by
        change H < coherentSICoordinate delta at hdelta_gt
        linarith [hboundary]
      exact (not_le_of_gt (mul_pos hcoef hbracket)) htorque_nonpos
  · intro a ha
    rcases ha with ⟨ha_pos, hadmissible, hzero, hbelow, habove⟩
    rcases hzero with
      ⟨ha_pos', hH_nonneg, ⟨hR, hphysical⟩, hall⟩
    have htorque_zero := hall hR hphysical
    rw [hnet] at htorque_zero
    have hcoef :
        0 < coherentSICoordinate D.waterDensity *
          coherentSICoordinate D.gravityMagnitude *
          (coherentSICoordinate a) ^ 3 := by
      positivity
    have hbracket :
        coherentSICoordinate D.maximumLevelDifference / 4 -
          coherentSICoordinate a / Real.sqrt 2 = 0 :=
      (mul_eq_zero.mp htorque_zero).resolve_left (ne_of_gt hcoef)
    apply WithDim.ext
    dsimp only [a₀, H]
    rw [hcoordinate D.maximumLevelDifference, hcoordinate a] at hbracket
    rw [hcoordinate D.maximumLevelDifference]
    have hdiv :
        D.maximumLevelDifference.val / 4 = a.val / Real.sqrt 2 :=
      sub_eq_zero.mp hbracket
    have hmul := congrArg (fun x : ℝ ↦ x * Real.sqrt 2) hdiv
    rw [div_mul_cancel₀ a.val hsqrt_ne] at hmul
    calc
      a.val = (D.maximumLevelDifference.val / 4) * Real.sqrt 2 := hmul.symm
      _ = D.maximumLevelDifference.val * Real.sqrt 2 / 4 := by ring

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_1_A_1
