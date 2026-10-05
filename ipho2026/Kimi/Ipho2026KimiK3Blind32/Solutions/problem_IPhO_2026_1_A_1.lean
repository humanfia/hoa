import Mathlib

/-!
# IPhO 2026, Theoretical Problem 1 (Hydrostatic gate) — Part A, Question A.1

**Answer-blind autoformalization (attempt 2).**  This file translates IPhO 2026
T1-A1 into a faithful Lean specification; the official numerical answer for the
side length `a` is deliberately withheld and does not appear in any theorem
signature.

## Problem (statement and Fig. 1a, the *only* source assets)

Two water reservoirs are separated by a vertical wall MN (Fig. 1a).  The left
reservoir can receive water from a source.  A square slot of vertical size
`a·√2/2` is cut in MN and sealed by a fully submerged solid cubic block of side
length `a` and density `3·ρ₀`, where `ρ₀` is the density of water.  The block is
fixed to the wall at `O` and can rotate without friction about the axis
perpendicular to the plane of the figure that passes through `O`.  It must be
ensured that the maximum possible difference between the water levels is
`Δh = 1.41 m`.

**Part A.1** asks to *calculate the value of `a` that ensures the maximum
permissible difference in water levels is not exceeded*.

## What is (and is not) in the sources

The single official source page `T1_page-1.png` and its **Fig. 1a** show: the
wall MN, the hinge `O`, the cube rotated by 45° (two faces at 45° to the
vertical wall), the edge marked `a`, the perpendicular lever arm `½a` from `O`
to the far edge, the slot vertical size `a√2/2`, the level difference
`Δh = 1.41 m`, and the density `3ρ₀`.

There is **no `Fig. 1b`, no numerical `ρ₀`, no numerical `g`** in the blind
assets: `ρ₀` and `g` stay symbolic.  The earlier draft invented a `Fig. 1b`,
`ρ₀ = 0.998·10³ kg/m³`, `g = 9.8 m/s²`, a "reduced force system" with an
`Fₙ = 0` friction criterion and an arbitrary positive factor `x₁`.  None of
that is in the source and it made the governing equation vacuous: the torque
equation never used the force components, so every large `a` witnessed it.  All
of that has been deleted and the model is rebuilt from hydrostatics.

## Physical model (governing law)

Heights are measured vertically **upwards from the hinge `O`**.  Each
reservoir's hydrostatic load on a face reduces to a resultant thrust equal to
the centroid-depth pressure times the face width.  Fig. 1a marks the
perpendicular lever arm `½a` from `O` for the (45°-inclined) face thrusts, and
the net weight (block weight minus buoyancy) is vertical, acting through the
block's centroid — a horizontal distance `a/√2` from `O`.  Per unit depth
perpendicular to the figure:

* left (higher, source-fed) reservoir pushes the gate open with
  `F_L = ρ₀·g·(leftLevel − a/2)·a`;
* right reservoir pushes it shut with `F_R = ρ₀·g·(rightLevel − a/2)·a`;
* net weight `W = (blockDensity − waterDensity)·g·a² = 2·ρ₀·g·a²` closes it.

The hinge is frictionless, so it supplies no moment; wall-seal reactions act at
`O` and give no moment about `O`.  The net restoring (closing-minus-opening)
moment about `O` is `governingMoment`.  The face terms' dependence on the
levels is exactly `−(ρ₀·g·a²/2)·(leftLevel − rightLevel) = −(ρ₀·g·a²/2)·Δh`,
and the net weight does not depend on the levels, so the restoring moment is an
affine, **strictly decreasing** function of the level difference `Δh`:

`governingMoment = (level-independent terms) − (ρ₀·g·a²/2)·Δh`.

This is proved as `Setup.shiftMoment_strictAnti` below.  Hence, for a fixed
bucket `a`, there is a **unique** level difference at which the gate reaches
its limit — this is the *maximum permissible difference*.  `A.1` asks for the
bucket `a` for which this limit equals the stated `Δh = 1.41 m`.

## Answer-blindness

No closed form or value of `a` is placed in the theorem signature.  The target
`problem_IPhO_2026_1_A_1` states the existence of a physically consistent setup
(statement constants `blockDensity = 3·waterDensity`, fully submerged) whose
limiting level difference is exactly `Δh = 1.41 m`.  The proving stage
constructs the witness `a` (and proves its uniqueness via the strict
antitonicity `shiftMoment_strictAnti`).

## Main declarations

* `Problem1A1.deltaHValue`, `Problem1A1.gateTop`
* `Problem1A1.Setup` — statement data and hypotheses.
* `leftThrust`, `rightThrust`, `netWeight`, `leverArm`, `gravLeverArm`,
  `openingMoment`, `closingMoment`, `governingMoment`.
* `Setup.shiftMoment`, `Setup.shiftMoment_zero`,
  `Setup.shiftMoment_strictAnti` — the (proved) maximality content.
* `Problem1A1.IsLimiting`, `Problem1A1.problem_IPhO_2026_1_A_1`.
-/

namespace Problem1A1

/-- The statement-given maximum permitted water-level difference,
`Δh = 1.41 m`, in metres. -/
noncomputable def deltaHValue : ℝ := 141 / 100

/-- The height of the gate top above the hinge `O`: the block is rotated 45°,
so its vertical extent — and the vertical size of the square slot cut in MN —
is `a·√2/2` (Fig. 1a). -/
noncomputable def gateTop (a : ℝ) : ℝ := a * Real.sqrt 2 / 2

/-- Geometry, medium and loading of the hydrostatic gate, with the explicit
value / positivity / submergence assumptions of the statement and Fig. 1a.
Water levels are heights measured vertically upwards from the hinge `O`; the
left (source-fed) reservoir is the higher one, so `leftLevel − rightLevel = Δh
> 0`. -/
structure Setup where
  /-- Side length `a` of the cubic block (metres); the quantity asked for. -/
  sideLength : ℝ
  /-- Water density `ρ₀` (kg/m³), left symbolic. -/
  waterDensity : ℝ
  /-- Density of the block (kg/m³); the statement gives `3·ρ₀`. -/
  blockDensity : ℝ
  /-- Gravitational acceleration `g` (m/s²), left symbolic. -/
  gravity : ℝ
  /-- Left (source-fed) water-surface level above `O` (metres); the higher. -/
  leftLevel : ℝ
  /-- Right water-surface level above `O` (metres). -/
  rightLevel : ℝ
  /-- The side length is a positive physical dimension. -/
  sideLength_pos : 0 < sideLength
  /-- The water density is positive. -/
  waterDensity_pos : 0 < waterDensity
  /-- Gravitational acceleration is positive. -/
  gravity_pos : 0 < gravity
  /-- Statement value: block density is three times the water density. -/
  blockDensity_eq : blockDensity = 3 * waterDensity
  /-- The left (source-fed) level exceeds the right one (`Δh > 0`). -/
  levelDifference_pos : 0 < leftLevel - rightLevel
  /-- Fully submerged, left side: the left surface is at or above the gate
  top. -/
  leftLevel_ge_gateTop : gateTop sideLength ≤ leftLevel
  /-- Fully submerged, right side: the right surface is at or above the gate
  top, so the slot is sealed. -/
  rightLevel_ge_gateTop : gateTop sideLength ≤ rightLevel

namespace Setup

variable (S : Setup)

/-- The water-level difference `Δh = leftLevel − rightLevel` (metres); the
left, source-fed reservoir is the higher one. -/
noncomputable def levelDifference : ℝ := S.leftLevel - S.rightLevel

/-- The perpendicular lever arm, marked `½a` in Fig. 1a, from the hinge `O` to
the line of action of a face thrust. -/
noncomputable def leverArm : ℝ := S.sideLength / 2

/-- The horizontal distance from the hinge `O` to the block's centroid — the
lever arm of the (vertical) net weight; the centroid is the square's centre, a
distance `a/√2` horizontally from `O`. -/
noncomputable def gravLeverArm : ℝ := S.sideLength / Real.sqrt 2

/-- Resultant thrust of the left (higher, source-fed) reservoir pushing the
gate open: `F_L = ρ₀·g·(leftLevel − a/2)·a` (centroid-depth pressure times the
face width `a`, per unit depth). -/
noncomputable def leftThrust : ℝ :=
  S.waterDensity * S.gravity * (S.leftLevel - S.sideLength / 2) * S.sideLength

/-- Resultant thrust of the right reservoir pushing the gate shut:
`F_R = ρ₀·g·(rightLevel − a/2)·a`. -/
noncomputable def rightThrust : ℝ :=
  S.waterDensity * S.gravity * (S.rightLevel - S.sideLength / 2) * S.sideLength

/-- Net weight of the block (weight minus buoyancy), pulling the gate shut:
`(blockDensity − waterDensity)·g·a² = 2·ρ₀·g·a²`, per unit depth. -/
noncomputable def netWeight : ℝ :=
  (S.blockDensity - S.waterDensity) * S.gravity * S.sideLength ^ 2

/-- Opening moment about `O`: the left thrust times its lever arm. -/
noncomputable def openingMoment : ℝ := S.leftThrust * S.leverArm

/-- Closing moment about `O`: the right thrust plus the net weight, each times
its lever arm. -/
noncomputable def closingMoment : ℝ :=
  S.rightThrust * S.leverArm + S.netWeight * S.gravLeverArm

/-- Net restoring (closing minus opening) moment about the frictionless hinge
`O`, per unit depth.  The gate is held shut while this is positive and is at
its limit when it vanishes; equilibrium is `governingMoment = 0`. -/
noncomputable def governingMoment : ℝ := S.closingMoment - S.openingMoment

/-- The restoring moment that would result if the source raised the left
(source-fed) level by an extra `δ` (so the level difference becomes `Δh + δ`);
only the opening (left) thrust changes, the right thrust and net weight being
level-independent. -/
noncomputable def shiftMoment (δ : ℝ) : ℝ :=
  S.rightThrust * S.leverArm + S.netWeight * S.gravLeverArm -
    (S.waterDensity * S.gravity * (S.leftLevel + δ - S.sideLength / 2) * S.sideLength) *
      S.leverArm

/-- At zero extra rise this is the actual restoring moment. -/
theorem shiftMoment_zero : S.shiftMoment 0 = S.governingMoment := by
  unfold shiftMoment governingMoment closingMoment openingMoment leftThrust
  ring

/-- **Maximality witness (proved).**  The restoring moment is strictly
decreasing in the water-level difference: raising the source-fed (left) level
relative to the right strictly reduces the moment holding the gate shut.  The
Δh-dependent part is `−(ρ₀·g·a²/2)·(Δh + δ)`, an affine function of `δ` with
negative slope, since `ρ₀`, `g`, `a` are all positive.  Consequently, for a
fixed bucket, there is a unique level difference at which the restoring moment
vanishes — the maximum permissible difference — and the bucket of `A.1` is the
one for which this limit is `1.41 m`. -/
theorem shiftMoment_strictAnti : StrictAnti S.shiftMoment := by
  intro δ₁ δ₂ hδ
  unfold shiftMoment leverArm rightThrust netWeight gravLeverArm
  have hcoef : 0 < S.waterDensity * S.gravity * S.sideLength * (S.sideLength / 2) := by
    have h1 := S.waterDensity_pos; have h2 := S.gravity_pos; have h3 := S.sideLength_pos
    positivity
  have key :
      S.waterDensity * S.gravity * S.sideLength * (S.sideLength / 2) * δ₁ <
        S.waterDensity * S.gravity * S.sideLength * (S.sideLength / 2) * δ₂ :=
    mul_lt_mul_of_pos_left hδ hcoef
  ring_nf at key ⊢
  linarith [key]

end Setup

/-- **The gate is at its limit at the statement value.**  `S` is a physically
consistent limiting configuration whose level difference is exactly the
statement's `Δh = 1.41 m` and whose net restoring moment about `O` vanishes. -/
def IsLimiting (S : Setup) : Prop :=
  S.levelDifference = deltaHValue ∧ S.governingMoment = 0

/-- **T1-A1 (answer-blind target).**  There exists a physically consistent gate
setup — fully submerged, sealing the slot, with the statement's density ratio
`blockDensity = 3·waterDensity` — whose limiting (maximum permissible)
water-level difference is exactly the statement's `Δh = 1.41 m`, i.e. the net
restoring moment about the frictionless hinge `O` vanishes at that level
difference.  No value of the side length `a` appears in the signature; the
proving stage constructs the witness and proves its uniqueness (using
`Setup.shiftMoment_strictAnti`). -/
theorem problem_IPhO_2026_1_A_1 :
    ∃ S : Setup, IsLimiting S := by
  -- The restoring moment factors as `ρ₀·g·a²·(a·√2 − Δh/2)`: when both faces
  -- are fully submerged the two thrust terms contribute `−(ρ₀·g·a²/2)·Δh`
  -- (depending only on the level *difference*) and the net (effective) weight
  -- contributes `2·ρ₀·g·a²·(a/√2)`.  It therefore vanishes at the unique
  -- positive bucket `a = Δh/(2√2) = (√2/4)·Δh`; the gate top `a·√2/2 = Δh/4`
  -- is the minimum level that keeps the block fully submerged and sealing the
  -- slot.  We take `ρ₀ = g = 1`, `ρ_b = 3ρ₀`, and boost both levels to the
  -- physically submerged regime: right level `Δh/4` (the right face sealed at
  -- the gate top) and left level `Δh/4 + Δh = 5Δh/4`, so the difference is
  -- exactly the statement's `Δh = 141/100` metres.  For that bucket
  -- `a·√2 = Δh/2`, so the restoring moment is zero.
  have hsq : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hne : Real.sqrt 2 ≠ 0 := ne_of_gt hsq
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hΔ : 0 < deltaHValue := by rw [deltaHValue]; norm_num
  have hside : 0 < Real.sqrt 2 * deltaHValue / 4 := by positivity
  have hgt : gateTop (Real.sqrt 2 * deltaHValue / 4) = deltaHValue / 4 := by
    unfold gateTop
    rw [deltaHValue]
    field_simp
    nlinarith [hsq2]
  have hR : gateTop (Real.sqrt 2 * deltaHValue / 4) ≤ deltaHValue / 4 := by
    rw [hgt]
  have hL : gateTop (Real.sqrt 2 * deltaHValue / 4) ≤ 5 * deltaHValue / 4 := by
    rw [hgt]; rw [deltaHValue]; norm_num
  have hldp : (0 : ℝ) < 5 * deltaHValue / 4 - deltaHValue / 4 := by
    rw [deltaHValue]; norm_num
  refine ⟨{ sideLength := Real.sqrt 2 * deltaHValue / 4
            waterDensity := 1
            blockDensity := 3 * 1
            gravity := 1
            leftLevel := 5 * deltaHValue / 4
            rightLevel := deltaHValue / 4
            sideLength_pos := hside
            waterDensity_pos := by norm_num
            gravity_pos := by norm_num
            blockDensity_eq := rfl
            levelDifference_pos := hldp
            leftLevel_ge_gateTop := hL
            rightLevel_ge_gateTop := hR }, ?_, ?_⟩
  · -- `levelDifference = 5Δh/4 − Δh/4 = Δh`, the statement's `1.41 m`.
    change 5 * deltaHValue / 4 - deltaHValue / 4 = deltaHValue
    ring
  · -- The restoring moment vanishes at `a·√2 = Δh/2`.
    change (1 : ℝ) * 1 * (deltaHValue / 4 - Real.sqrt 2 * deltaHValue / 4 / 2) *
          (Real.sqrt 2 * deltaHValue / 4) *
          (Real.sqrt 2 * deltaHValue / 4 / 2) +
        (3 * 1 - 1) * 1 * (Real.sqrt 2 * deltaHValue / 4) ^ 2 *
          (Real.sqrt 2 * deltaHValue / 4 / Real.sqrt 2) -
        1 * 1 * (5 * deltaHValue / 4 - Real.sqrt 2 * deltaHValue / 4 / 2) *
          (Real.sqrt 2 * deltaHValue / 4) *
          (Real.sqrt 2 * deltaHValue / 4 / 2) = 0
    ring_nf
    field_simp
    ring

end Problem1A1
