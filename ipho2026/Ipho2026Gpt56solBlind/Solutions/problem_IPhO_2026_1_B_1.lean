import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, Problem 1 B.1: bound electron--positron orbit

This file formalizes the source data, the Newton--Coulomb development, and the two conic
relations printed with the problem.  Physical quantities use `WithDim`; their `.val` fields
are numerical coordinates in one fixed coherent system of units.

The requested maximum is not stored in the parameters, initial state, or governing laws.
It is characterized both as the larger positive root of the conserved radial equation and
as the attained global maximum along every admissible complete conic development.
-/

namespace Ipho2026Gpt56solBlind
namespace ProblemIPhO2026_1_B_1

open Dimension
open scoped BigOperators

noncomputable section

/-! ## Dimensioned parameters and source initial data -/

/-- The Euclidean orbital plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

abbrev LengthQuantity := WithDim L𝓭 ℝ
abbrev TimeQuantity := WithDim T𝓭 ℝ
abbrev MassQuantity := WithDim M𝓭 ℝ
abbrev ChargeQuantity := WithDim C𝓭 ℝ

/-- Action and angular momentum have dimension `M L² T⁻¹`. -/
abbrev AngularMomentumQuantity :=
  WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹) ℝ

/-- Mechanical energy has dimension `M L² T⁻²`. -/
abbrev EnergyQuantity :=
  WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ

/-- Vacuum permittivity has dimension `M⁻¹ L⁻³ T² C²`. -/
abbrev PermittivityQuantity :=
  WithDim
    (M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * T𝓭 * T𝓭 * C𝓭 * C𝓭) ℝ

/-- Coulomb's constant has dimension `M L³ T⁻² C⁻²`. -/
abbrev CoulombConstantQuantity :=
  WithDim
    (M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹) ℝ

/-- The attractive Coulomb strength `κ = k e²` has dimension energy times length. -/
abbrev CoulombStrengthQuantity :=
  WithDim (M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ

abbrev PositionQuantity := WithDim L𝓭 Plane
abbrev VelocityQuantity := WithDim (L𝓭 * T𝓭⁻¹) Plane
abbrev AccelerationQuantity := WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) Plane

/-- Constants common to the electron and positron. -/
structure Parameters where
  mass : MassQuantity
  elementaryCharge : ChargeQuantity
  vacuumPermittivity : PermittivityQuantity
  reducedPlanckConstant : AngularMomentumQuantity
  bohrRadius : LengthQuantity
  coulombConstant : CoulombConstantQuantity

/-- Positivity and the two defining relations printed in the problem statement. -/
def Parameters.IsPhysical (p : Parameters) : Prop :=
  0 < p.mass.val ∧
  0 < p.elementaryCharge.val ∧
  0 < p.vacuumPermittivity.val ∧
  0 < p.reducedPlanckConstant.val ∧
  0 < p.bohrRadius.val ∧
  0 < p.coulombConstant.val ∧
  p.coulombConstant.val = 1 / (4 * Real.pi * p.vacuumPermittivity.val) ∧
  p.bohrRadius.val =
    4 * Real.pi * p.vacuumPermittivity.val * p.reducedPlanckConstant.val ^ 2 /
      (p.mass.val * p.elementaryCharge.val ^ 2)

/-- The positron charge `q₊ = e`. -/
def positronCharge (p : Parameters) : ChargeQuantity :=
  ⟨p.elementaryCharge.val⟩

/-- The electron charge `q₋ = -e`. -/
def electronCharge (p : Parameters) : ChargeQuantity :=
  ⟨-p.elementaryCharge.val⟩

/-- The instantaneous data supplied by the source. -/
structure InitialState where
  initialTime : TimeQuantity
  mu : ℝ
  positronPosition : PositionQuantity
  electronPosition : PositionQuantity
  positronVelocity : VelocityQuantity
  electronVelocity : VelocityQuantity

/-- The Euclidean dot product in coordinate form. -/
def dot (u v : Plane) : ℝ :=
  ∑ i, u i * v i

/-- The oriented scalar cross product in the orbital plane. -/
def crossZ (u v : Plane) : ℝ :=
  u 0 * v 1 - u 1 * v 0

/-- Relative and center-of-mass quantities computed from the source instant. -/
structure InitialReducedData where
  relativePosition : PositionQuantity
  separation : LengthQuantity
  relativeVelocity : VelocityQuantity
  centerVelocity : VelocityQuantity
  centerPosition : PositionQuantity

/-- Compute the relative and center-of-mass data from an initial state. -/
def initialReducedData (s : InitialState) : InitialReducedData :=
  let relativePositionValue := s.positronPosition.val - s.electronPosition.val
  { relativePosition := ⟨relativePositionValue⟩
    separation := ⟨‖relativePositionValue‖⟩
    relativeVelocity := ⟨s.positronVelocity.val - s.electronVelocity.val⟩
    centerVelocity :=
      ⟨(1 / 2 : ℝ) • (s.positronVelocity.val + s.electronVelocity.val)⟩
    centerPosition :=
      ⟨(1 / 2 : ℝ) • (s.positronPosition.val + s.electronPosition.val)⟩ }

/-- Signed angular momentum of one particle about a specified center. -/
def particleAngularMomentumValue
    (p : Parameters) (position : PositionQuantity) (velocity : VelocityQuantity)
    (center : PositionQuantity) : AngularMomentumQuantity :=
  ⟨p.mass.val * crossZ (position.val - center.val) velocity.val⟩

/-- The source separation, transverse antiparallel velocities, and per-particle angular
momentum magnitudes.  These are initial data, not the requested maximum. -/
def HasSourceInitialConditions (p : Parameters) (s : InitialState) : Prop :=
  let d := initialReducedData s
  s.mu = 4 ∧
  d.separation.val = 100 * p.bohrRadius.val ∧
  (∃ speedRatio : ℝ,
    0 < speedRatio ∧
    s.positronVelocity.val = (-speedRatio) • s.electronVelocity.val) ∧
  dot d.relativePosition.val s.positronVelocity.val = 0 ∧
  dot d.relativePosition.val s.electronVelocity.val = 0 ∧
  abs
      (particleAngularMomentumValue p s.positronPosition s.positronVelocity
        d.centerPosition).val =
    s.mu * p.reducedPlanckConstant.val ∧
  abs
      (particleAngularMomentumValue p s.electronPosition s.electronVelocity
        d.centerPosition).val =
    s.mu * p.reducedPlanckConstant.val

/-! ## Reduced invariants fixed by the source data -/

/-- The reduced mass of two particles of common mass `m`. -/
def reducedMass (p : Parameters) : MassQuantity :=
  ⟨p.mass.val / 2⟩

/-- Positive strength of the attractive potential, `κ = -k q₊ q₋ = k e²`. -/
def coulombStrength (p : Parameters) : CoulombStrengthQuantity :=
  ⟨-(p.coulombConstant.val * (positronCharge p).val * (electronCharge p).val)⟩

/-- Magnitude of the relative angular momentum computed from the initial data. -/
def initialAngularMomentumMagnitude
    (p : Parameters) (s : InitialState) : AngularMomentumQuantity :=
  let d := initialReducedData s
  ⟨(reducedMass p).val * abs (crossZ d.relativePosition.val d.relativeVelocity.val)⟩

/-- Relative mechanical energy computed from the initial data. -/
def initialEnergy (p : Parameters) (s : InitialState) : EnergyQuantity :=
  let d := initialReducedData s
  ⟨(reducedMass p).val / 2 * ‖d.relativeVelocity.val‖ ^ 2 -
    (coulombStrength p).val / d.separation.val⟩

/-- The negative-energy regime stated to be bound in the source. -/
def IsBoundInitialRegime (p : Parameters) (s : InitialState) : Prop :=
  (initialEnergy p s).val < 0

/-- Exactly the physical parameters, source initial conditions, and stated bound regime. -/
def SourceProblemSetup (p : Parameters) (s : InitialState) : Prop :=
  p.IsPhysical ∧
  HasSourceInitialConditions p s ∧
  IsBoundInitialRegime p s

/-! ## Newton--Coulomb developments -/

/-- Position, velocity, and acceleration histories for the two particles. -/
structure PairMotion where
  positronPosition : ℝ → PositionQuantity
  electronPosition : ℝ → PositionQuantity
  positronVelocity : ℝ → VelocityQuantity
  electronVelocity : ℝ → VelocityQuantity
  positronAcceleration : ℝ → AccelerationQuantity
  electronAcceleration : ℝ → AccelerationQuantity

/-- Relative and center-of-mass observables at one time. -/
structure MotionObservables where
  relativePosition : PositionQuantity
  separation : LengthQuantity
  relativeVelocity : VelocityQuantity
  relativeAcceleration : AccelerationQuantity
  centerPosition : PositionQuantity

/-- Compute all motion observables at time `t`. -/
def motionObservables (motion : PairMotion) (t : ℝ) : MotionObservables :=
  let relativePositionValue :=
    (motion.positronPosition t).val - (motion.electronPosition t).val
  { relativePosition := ⟨relativePositionValue⟩
    separation := ⟨‖relativePositionValue‖⟩
    relativeVelocity :=
      ⟨(motion.positronVelocity t).val - (motion.electronVelocity t).val⟩
    relativeAcceleration :=
      ⟨(motion.positronAcceleration t).val - (motion.electronAcceleration t).val⟩
    centerPosition :=
      ⟨(1 / 2 : ℝ) •
        ((motion.positronPosition t).val + (motion.electronPosition t).val)⟩ }

/-- Coordinatewise first- and second-order kinematics. -/
def HasKinematics (motion : PairMotion) : Prop :=
  ∀ (t : ℝ) (i : Fin 2),
    HasDerivAt (fun u ↦ (motion.positronPosition u).val i)
        ((motion.positronVelocity t).val i) t ∧
    HasDerivAt (fun u ↦ (motion.electronPosition u).val i)
        ((motion.electronVelocity t).val i) t ∧
    HasDerivAt (fun u ↦ (motion.positronVelocity u).val i)
        ((motion.positronAcceleration t).val i) t ∧
    HasDerivAt (fun u ↦ (motion.electronVelocity u).val i)
        ((motion.electronAcceleration t).val i) t

/-- Collision-free Newton equations with the sole force given by attractive Coulomb
interaction.  The relative position points from the electron to the positron. -/
def SatisfiesNewtonCoulomb (p : Parameters) (motion : PairMotion) : Prop :=
  ∀ t : ℝ,
    let o := motionObservables motion t
    0 < o.separation.val ∧
    p.mass.val • (motion.positronAcceleration t).val =
      (-(coulombStrength p).val / o.separation.val ^ 3) • o.relativePosition.val ∧
    p.mass.val • (motion.electronAcceleration t).val =
      ((coulombStrength p).val / o.separation.val ^ 3) • o.relativePosition.val

/-- The motion agrees with all four supplied position/velocity values at the source time. -/
def ExtendsInitialState (s : InitialState) (motion : PairMotion) : Prop :=
  motion.positronPosition s.initialTime.val = s.positronPosition ∧
  motion.electronPosition s.initialTime.val = s.electronPosition ∧
  motion.positronVelocity s.initialTime.val = s.positronVelocity ∧
  motion.electronVelocity s.initialTime.val = s.electronVelocity

/-- The unit vector with polar angle `angle` in the fixed orbital coordinates. -/
def polarUnitVector (angle : ℝ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![Real.cos angle, Real.sin angle]

/-- The printed eccentricity and polar-conic relations, grounded in the actual relative
position, together with a continuous complete traversal in either orientation. -/
def SourceBoundConicGoverningRelations
    (p : Parameters) (s : InitialState) (motion : PairMotion)
    (scale : LengthQuantity) (eccentricity : ℝ) (period : TimeQuantity)
    (orientation phaseOffset : ℝ) (phase : ℝ → ℝ) : Prop :=
  0 < scale.val ∧
  0 < period.val ∧
  0 < eccentricity ∧
  eccentricity < 1 ∧
  (orientation = -1 ∨ orientation = 1) ∧
  Continuous phase ∧
  eccentricity =
    Real.sqrt
      (1 +
        4 * (initialAngularMomentumMagnitude p s).val ^ 2 * (initialEnergy p s).val /
          (p.coulombConstant.val ^ 2 * p.elementaryCharge.val ^ 4 * p.mass.val)) ∧
  ∀ t : ℝ,
    let o := motionObservables motion t
    o.relativePosition.val =
        o.separation.val • polarUnitVector (phase t + phaseOffset) ∧
    o.separation.val = scale.val / (1 - eccentricity * Real.cos (phase t)) ∧
    phase (t + period.val) = phase t + 2 * Real.pi * orientation

/-- A motion obeys the source bound-conic law when it has witnesses for all governing
parameters. -/
def SatisfiesSourceBoundConicLaw
    (p : Parameters) (s : InitialState) (motion : PairMotion) : Prop :=
  ∃ (scale : LengthQuantity) (eccentricity : ℝ) (period : TimeQuantity)
      (orientation phaseOffset : ℝ) (phase : ℝ → ℝ),
    SourceBoundConicGoverningRelations p s motion scale eccentricity period
      orientation phaseOffset phase

/-- A global collision-free Newton--Coulomb development of the source state which also
performs a complete traversal of the source conic. -/
def IsAdmissibleBoundOrbit
    (p : Parameters) (s : InitialState) (motion : PairMotion) : Prop :=
  SourceProblemSetup p s ∧
  ExtendsInitialState s motion ∧
  HasKinematics motion ∧
  SatisfiesNewtonCoulomb p motion ∧
  SatisfiesSourceBoundConicLaw p s motion

/-- The source statement that the `mu = 4` case is bound is represented by nonemptiness of
the class of complete admissible developments. -/
def HasSourceStatedBoundedness (p : Parameters) (s : InitialState) : Prop :=
  ∃ motion : PairMotion, IsAdmissibleBoundOrbit p s motion

/-- Signed relative angular momentum along a motion. -/
def relativeAngularMomentumValue
    (p : Parameters) (motion : PairMotion) (t : ℝ) : AngularMomentumQuantity :=
  let o := motionObservables motion t
  ⟨(reducedMass p).val * crossZ o.relativePosition.val o.relativeVelocity.val⟩

/-- Relative mechanical energy along a motion. -/
def relativeEnergyValue
    (p : Parameters) (motion : PairMotion) (t : ℝ) : EnergyQuantity :=
  let o := motionObservables motion t
  ⟨(reducedMass p).val / 2 * ‖o.relativeVelocity.val‖ ^ 2 -
    (coulombStrength p).val / o.separation.val⟩

/-- Vanishing radial velocity, expressed without selecting polar coordinates. -/
def IsRadialTurningTime (motion : PairMotion) (t : ℝ) : Prop :=
  let o := motionObservables motion t
  dot o.relativePosition.val o.relativeVelocity.val = 0

/-! ## The radial conservation equation and its roots -/

/-- Dimension of the radial turning polynomial: energy times length squared. -/
abbrev RadialTurningQuantity :=
  WithDim
    (M𝓭 * L𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ

/-- The radial turning polynomial evaluated at a dimensionless Bohr-radius count. -/
def radialTurningPolynomial
    (p : Parameters) (s : InitialState) (x : ℝ) : RadialTurningQuantity :=
  ⟨(initialEnergy p s).val * (p.bohrRadius.val * x) ^ 2 +
    (coulombStrength p).val * (p.bohrRadius.val * x) -
    (initialAngularMomentumMagnitude p s).val ^ 2 / (2 * (reducedMass p).val)⟩

/-- A positive dimensionless root of the source turning polynomial. -/
def IsPositiveTurningPointInBohrRadii
    (p : Parameters) (s : InitialState) (x : ℝ) : Prop :=
  0 < x ∧ (radialTurningPolynomial p s x).val = 0

/-- The ordered pair containing all positive roots of the source turning polynomial. -/
def AreOrderedPositiveTurningPoints
    (p : Parameters) (s : InitialState) (xMinus xPlus : ℝ) : Prop :=
  0 < xMinus ∧
  xMinus < xPlus ∧
  IsPositiveTurningPointInBohrRadii p s xMinus ∧
  IsPositiveTurningPointInBohrRadii p s xPlus ∧
  ∀ x : ℝ,
    IsPositiveTurningPointInBohrRadii p s x → x = xMinus ∨ x = xPlus

/-- The largest positive root, characterized without naming its value. -/
def IsLargerPositiveTurningPoint
    (p : Parameters) (s : InitialState) (answer : ℝ) : Prop :=
  IsPositiveTurningPointInBohrRadii p s answer ∧
  ∀ x : ℝ, IsPositiveTurningPointInBohrRadii p s x → x ≤ answer

/-- `answer` is an attained positive global maximum of this motion, in Bohr radii. -/
def IsAttainedMaximumInBohrRadii
    (p : Parameters) (motion : PairMotion) (answer : ℝ) : Prop :=
  0 < answer ∧
  ∃ tMax : ℝ,
    IsRadialTurningTime motion tMax ∧
    (motionObservables motion tMax).separation.val = answer * p.bohrRadius.val ∧
    ∀ t : ℝ,
      (motionObservables motion t).separation.val ≤
        (motionObservables motion tMax).separation.val

/-- A source-data root which is realized as the same maximum by every admissible motion. -/
def MaximumSeparationSolution
    (p : Parameters) (s : InitialState) (answer : ℝ) : Prop :=
  IsLargerPositiveTurningPoint p s answer ∧
  HasSourceStatedBoundedness p s ∧
  ∀ motion : PairMotion,
    IsAdmissibleBoundOrbit p s motion →
      IsAttainedMaximumInBohrRadii p motion answer

/-! ## Derivation from the source data -/

/-- The two source positions lie at `±r₀/2` from their midpoint. -/
lemma initial_midpoint_geometry (s : InitialState) :
    let d := initialReducedData s
    s.positronPosition.val - d.centerPosition.val =
        (1 / 2 : ℝ) • d.relativePosition.val ∧
      s.electronPosition.val - d.centerPosition.val =
        (-1 / 2 : ℝ) • d.relativePosition.val := by
  dsimp [initialReducedData]
  constructor <;> ext i <;> simp [Pi.sub_apply, Pi.add_apply] <;> ring

/-- Equal prescribed angular-momentum magnitudes force the antiparallel initial velocities
to be equal and opposite, so the center-of-mass velocity vanishes. -/
lemma initial_velocities_eq_neg
    (p : Parameters) (s : InitialState) (hPhysical : p.IsPhysical)
    (hSource : HasSourceInitialConditions p s) :
    s.positronVelocity.val = -s.electronVelocity.val ∧
      (initialReducedData s).centerVelocity.val = 0 := by
  rcases hPhysical with ⟨hm, he, hε, hℏ, ha, hk, hk_def, ha_def⟩
  dsimp only [HasSourceInitialConditions] at hSource
  rcases hSource with
    ⟨hμ, hR, ⟨speedRatio, hspeedRatio, hanti⟩, hperpPos, hperpElec,
      hangularPos, hangularElec⟩
  have hgeom := initial_midpoint_geometry s
  dsimp only at hgeom
  have hcross :
      crossZ
          (s.positronPosition.val - (initialReducedData s).centerPosition.val)
          s.positronVelocity.val =
        speedRatio *
          crossZ
            (s.electronPosition.val - (initialReducedData s).centerPosition.val)
            s.electronVelocity.val := by
    rw [hgeom.1, hgeom.2, hanti]
    unfold crossZ
    simp
    ring
  have hmomentum :
      (particleAngularMomentumValue p s.positronPosition s.positronVelocity
          (initialReducedData s).centerPosition).val =
        speedRatio *
          (particleAngularMomentumValue p s.electronPosition s.electronVelocity
            (initialReducedData s).centerPosition).val := by
    change
      p.mass.val *
          crossZ
            (s.positronPosition.val - (initialReducedData s).centerPosition.val)
            s.positronVelocity.val =
        speedRatio *
          (p.mass.val *
            crossZ
              (s.electronPosition.val - (initialReducedData s).centerPosition.val)
              s.electronVelocity.val)
    rw [hcross]
    ring
  have hscale_pos : 0 < s.mu * p.reducedPlanckConstant.val := by
    rw [hμ]
    positivity
  have hratio : speedRatio = 1 := by
    rw [hmomentum, abs_mul, abs_of_pos hspeedRatio, hangularElec] at hangularPos
    nlinarith
  subst speedRatio
  constructor
  · simpa using hanti
  · dsimp [initialReducedData]
    rw [hanti]
    simp

/-- The common initial speed fixed by one-particle angular momentum. -/
lemma initial_speed_eq
    (p : Parameters) (s : InitialState) (hPhysical : p.IsPhysical)
    (hSource : HasSourceInitialConditions p s) :
    let speed :=
      2 * s.mu * p.reducedPlanckConstant.val /
        (p.mass.val * (initialReducedData s).separation.val)
    ‖s.positronVelocity.val‖ = speed ∧ ‖s.electronVelocity.val‖ = speed := by
  have hvel := initial_velocities_eq_neg p s hPhysical hSource
  rcases hPhysical with ⟨hm, he, hε, hℏ, ha, hk, hk_def, ha_def⟩
  dsimp only [HasSourceInitialConditions] at hSource
  rcases hSource with
    ⟨hμ, hR, hanti, hperpPos, hperpElec, hangularPos, hangularElec⟩
  have hcross_abs_of_dot_zero (u v : Plane) (huv : dot u v = 0) :
      abs (crossZ u v) = ‖u‖ * ‖v‖ := by
    apply (sq_eq_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [sq_abs, mul_pow]
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    unfold dot at huv
    unfold crossZ
    rw [Fin.sum_univ_two] at huv
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    calc
      (u 0 * v 1 - u 1 * v 0) ^ 2 =
          (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) -
            (u 0 * v 0 + u 1 * v 1) ^ 2 := by ring
      _ = (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by rw [huv]; ring
  have hgeom := initial_midpoint_geometry s
  dsimp only at hgeom
  have hlever :
      crossZ ((1 / 2 : ℝ) • (initialReducedData s).relativePosition.val)
          s.positronVelocity.val =
        (1 / 2 : ℝ) *
          crossZ (initialReducedData s).relativePosition.val s.positronVelocity.val := by
    unfold crossZ
    simp
    ring
  have hcross_abs := hcross_abs_of_dot_zero _ _ hperpPos
  have hsep_norm :
      (initialReducedData s).separation.val =
        ‖(initialReducedData s).relativePosition.val‖ := by
    rfl
  change
    abs
        (p.mass.val *
          crossZ
            (s.positronPosition.val - (initialReducedData s).centerPosition.val)
            s.positronVelocity.val) =
      s.mu * p.reducedPlanckConstant.val at hangularPos
  rw [hgeom.1, hlever, abs_mul, abs_of_pos hm, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), hcross_abs, ← hsep_norm]
    at hangularPos
  have hsep_pos : 0 < (initialReducedData s).separation.val := by
    rw [hR]
    positivity
  have hspeedPos :
      ‖s.positronVelocity.val‖ =
        2 * s.mu * p.reducedPlanckConstant.val /
          (p.mass.val * (initialReducedData s).separation.val) := by
    apply (eq_div_iff (mul_ne_zero (ne_of_gt hm) (ne_of_gt hsep_pos))).2
    nlinarith
  dsimp only
  constructor
  · exact hspeedPos
  · rw [← hspeedPos, hvel.1, norm_neg]

/-- The two printed constant definitions imply `κ a₀ = ℏ² / m`. -/
lemma coulombStrength_mul_bohrRadius
    (p : Parameters) (hPhysical : p.IsPhysical) :
    (coulombStrength p).val * p.bohrRadius.val =
      p.reducedPlanckConstant.val ^ 2 / p.mass.val := by
  rcases hPhysical with ⟨hm, he, hε, hℏ, ha, hk, hk_def, ha_def⟩
  change
    (-(p.coulombConstant.val * p.elementaryCharge.val *
        -p.elementaryCharge.val)) * p.bohrRadius.val =
      p.reducedPlanckConstant.val ^ 2 / p.mass.val
  rw [hk_def, ha_def]
  have hdenom : 4 * Real.pi * p.vacuumPermittivity.val ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hε.ne'
  have he_sq : p.elementaryCharge.val ^ 2 ≠ 0 :=
    pow_ne_zero 2 he.ne'
  calc
    (-(1 / (4 * Real.pi * p.vacuumPermittivity.val) *
          p.elementaryCharge.val * -p.elementaryCharge.val)) *
        (4 * Real.pi * p.vacuumPermittivity.val *
            p.reducedPlanckConstant.val ^ 2 /
          (p.mass.val * p.elementaryCharge.val ^ 2)) =
      ((4 * Real.pi * p.vacuumPermittivity.val)⁻¹ *
          (4 * Real.pi * p.vacuumPermittivity.val)) *
        (p.elementaryCharge.val ^ 2 *
          (p.elementaryCharge.val ^ 2)⁻¹) *
        p.reducedPlanckConstant.val ^ 2 * p.mass.val⁻¹ := by
      rw [one_div, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = p.reducedPlanckConstant.val ^ 2 / p.mass.val := by
      rw [inv_mul_cancel₀ hdenom, mul_inv_cancel₀ he_sq,
        div_eq_mul_inv]
      ring

/-- The initial relative angular momentum is twice either particle's magnitude. -/
lemma initialAngularMomentumMagnitude_eq
    (p : Parameters) (s : InitialState) (hPhysical : p.IsPhysical)
    (hSource : HasSourceInitialConditions p s) :
    (initialAngularMomentumMagnitude p s).val =
      2 * s.mu * p.reducedPlanckConstant.val := by
  have hvel := (initial_velocities_eq_neg p s hPhysical hSource).1
  have hgeom := initial_midpoint_geometry s
  dsimp only at hgeom
  rcases hPhysical with ⟨hm, he, hε, hℏ, ha, hk, hk_def, ha_def⟩
  dsimp only [HasSourceInitialConditions] at hSource
  rcases hSource with
    ⟨hμ, hR, hanti, hperpPos, hperpElec, hangularPos, hangularElec⟩
  have hcross :
      crossZ (initialReducedData s).relativePosition.val
          (initialReducedData s).relativeVelocity.val =
        4 *
          crossZ
            (s.positronPosition.val - (initialReducedData s).centerPosition.val)
            s.positronVelocity.val := by
    change
      crossZ (initialReducedData s).relativePosition.val
          (s.positronVelocity.val - s.electronVelocity.val) =
        4 *
          crossZ
            (s.positronPosition.val - (initialReducedData s).centerPosition.val)
            s.positronVelocity.val
    rw [hvel, hgeom.1]
    unfold crossZ
    simp
    ring
  change
    p.mass.val / 2 *
        abs
          (crossZ (initialReducedData s).relativePosition.val
            (initialReducedData s).relativeVelocity.val) =
      2 * s.mu * p.reducedPlanckConstant.val
  rw [hcross, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  change
    abs
        (p.mass.val *
          crossZ
            (s.positronPosition.val - (initialReducedData s).centerPosition.val)
            s.positronVelocity.val) =
      s.mu * p.reducedPlanckConstant.val at hangularPos
  rw [abs_mul, abs_of_pos hm] at hangularPos
  nlinarith

/-- Energy expressed entirely through the source radius and one-particle angular momentum. -/
lemma initialEnergy_eq
    (p : Parameters) (s : InitialState) (hPhysical : p.IsPhysical)
    (hSource : HasSourceInitialConditions p s) :
    (initialEnergy p s).val =
      4 * s.mu ^ 2 * p.reducedPlanckConstant.val ^ 2 /
          (p.mass.val * (initialReducedData s).separation.val ^ 2) -
        (coulombStrength p).val / (initialReducedData s).separation.val := by
  have hvel := (initial_velocities_eq_neg p s hPhysical hSource).1
  have hspeed := (initial_speed_eq p s hPhysical hSource).1
  rcases hPhysical with ⟨hm, he, hε, hℏ, ha, hk, hk_def, ha_def⟩
  dsimp only [HasSourceInitialConditions] at hSource
  rcases hSource with
    ⟨hμ, hR, hanti, hperpPos, hperpElec, hangularPos, hangularElec⟩
  have hvel' : s.electronVelocity.val = -s.positronVelocity.val := by
    simpa using (congrArg Neg.neg hvel).symm
  have hrelative_norm :
      ‖(initialReducedData s).relativeVelocity.val‖ =
        2 * ‖s.positronVelocity.val‖ := by
    change
      ‖s.positronVelocity.val - s.electronVelocity.val‖ =
        2 * ‖s.positronVelocity.val‖
    rw [hvel']
    rw [sub_neg_eq_add, ← two_smul ℝ, norm_smul]
    norm_num
  have hsep_pos : 0 < (initialReducedData s).separation.val := by
    rw [hR]
    positivity
  change
    (p.mass.val / 2) / 2 *
          ‖(initialReducedData s).relativeVelocity.val‖ ^ 2 -
        (coulombStrength p).val / (initialReducedData s).separation.val =
      4 * s.mu ^ 2 * p.reducedPlanckConstant.val ^ 2 /
          (p.mass.val * (initialReducedData s).separation.val ^ 2) -
        (coulombStrength p).val / (initialReducedData s).separation.val
  rw [hrelative_norm, hspeed]
  field_simp [ne_of_gt hm, ne_of_gt hsep_pos]
  <;> ring

/-- For the printed values `mu = 4` and `R₀ = 100 a₀`, the source energy is negative. -/
lemma source_initialEnergy_neg
    (p : Parameters) (s : InitialState) (hPhysical : p.IsPhysical)
    (hSource : HasSourceInitialConditions p s) :
    (initialEnergy p s).val < 0 := by
  have hEnergy := initialEnergy_eq p s hPhysical hSource
  have hCoulomb := coulombStrength_mul_bohrRadius p hPhysical
  rcases hPhysical with ⟨hm, he, hε, hℏ, ha, hk, hk_def, ha_def⟩
  dsimp only [HasSourceInitialConditions] at hSource
  rcases hSource with
    ⟨hμ, hR, hanti, hperpPos, hperpElec, hangularPos, hangularElec⟩
  rw [hμ, hR] at hEnergy
  have hCoulomb' :
      (coulombStrength p).val * p.bohrRadius.val * p.mass.val =
        p.reducedPlanckConstant.val ^ 2 := by
    rw [hCoulomb]
    field_simp [ne_of_gt hm]
  have hformula :
      4 * (4 : ℝ) ^ 2 * p.reducedPlanckConstant.val ^ 2 /
            (p.mass.val * (100 * p.bohrRadius.val) ^ 2) -
          (coulombStrength p).val / (100 * p.bohrRadius.val) =
        (-9 / 2500 : ℝ) *
          (p.reducedPlanckConstant.val ^ 2 /
            (p.mass.val * p.bohrRadius.val ^ 2)) := by
    field_simp [ne_of_gt hm, ne_of_gt ha]
    nlinarith
  rw [hEnergy, hformula]
  have hscale_pos :
      0 < p.reducedPlanckConstant.val ^ 2 /
        (p.mass.val * p.bohrRadius.val ^ 2) := by positivity
  nlinarith

/-- The source radial polynomial has a unique ordered pair of positive roots. -/
lemma existsUnique_orderedPositiveTurningPoints
    (p : Parameters) (s : InitialState) (hSetup : SourceProblemSetup p s) :
    ∃! roots : ℝ × ℝ,
      AreOrderedPositiveTurningPoints p s roots.1 roots.2 := by
  rcases hSetup with ⟨hPhysical, hSource, hBound⟩
  have hEnergy := initialEnergy_eq p s hPhysical hSource
  have hAngular := initialAngularMomentumMagnitude_eq p s hPhysical hSource
  have hCoulomb := coulombStrength_mul_bohrRadius p hPhysical
  rcases hPhysical with ⟨hm, he, hε, hℏ, ha, hk, hk_def, ha_def⟩
  dsimp only [HasSourceInitialConditions] at hSource
  rcases hSource with
    ⟨hμ, hR, hanti, hperpPos, hperpElec, hangularPos, hangularElec⟩
  have hCoulomb' :
      (coulombStrength p).val * p.bohrRadius.val * p.mass.val =
        p.reducedPlanckConstant.val ^ 2 := by
    rw [hCoulomb]
    field_simp [ne_of_gt hm]
  have hEnergyExplicit :
      (initialEnergy p s).val =
        (-9 / 2500 : ℝ) *
          (p.reducedPlanckConstant.val ^ 2 /
            (p.mass.val * p.bohrRadius.val ^ 2)) := by
    rw [hEnergy, hμ, hR]
    field_simp [ne_of_gt hm, ne_of_gt ha]
    nlinarith
  have hPolynomial (x : ℝ) :
      (radialTurningPolynomial p s x).val =
        (p.reducedPlanckConstant.val ^ 2 / p.mass.val) *
          ((-9 / 2500 : ℝ) * (x - 100) * (x - 1600 / 9)) := by
    change
      (initialEnergy p s).val * (p.bohrRadius.val * x) ^ 2 +
            (coulombStrength p).val * (p.bohrRadius.val * x) -
          (initialAngularMomentumMagnitude p s).val ^ 2 /
            (2 * (p.mass.val / 2)) =
        (p.reducedPlanckConstant.val ^ 2 / p.mass.val) *
          ((-9 / 2500 : ℝ) * (x - 100) * (x - 1600 / 9))
    rw [hEnergyExplicit, hAngular, hμ]
    rw [show
      (coulombStrength p).val * (p.bohrRadius.val * x) =
        ((coulombStrength p).val * p.bohrRadius.val) * x by ring,
      hCoulomb]
    field_simp [ne_of_gt hm, ne_of_gt ha]
    ring
  have hscale_pos :
      0 < p.reducedPlanckConstant.val ^ 2 / p.mass.val := by positivity
  have hrootMinus : IsPositiveTurningPointInBohrRadii p s 100 := by
    constructor
    · norm_num
    · rw [hPolynomial]
      norm_num
  have hrootPlus : IsPositiveTurningPointInBohrRadii p s (1600 / 9) := by
    constructor
    · norm_num
    · rw [hPolynomial]
      norm_num
  have hclass (x : ℝ) (hx : IsPositiveTurningPointInBohrRadii p s x) :
      x = 100 ∨ x = 1600 / 9 := by
    change 0 < x ∧ (radialTurningPolynomial p s x).val = 0 at hx
    rw [hPolynomial] at hx
    have hfac0 : (x - 100) * (x - 1600 / 9) = 0 := by
      have hrest : (-9 / 2500 : ℝ) * (x - 100) * (x - 1600 / 9) = 0 :=
        (mul_eq_zero.mp hx.2).resolve_left (ne_of_gt hscale_pos)
      apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (-9 / 2500 : ℝ) ≠ 0)
      simpa [mul_assoc] using hrest
    rcases mul_eq_zero.mp hfac0 with hminus | hplus
    · left
      exact sub_eq_zero.mp hminus
    · right
      exact sub_eq_zero.mp hplus
  have hOrdered :
      AreOrderedPositiveTurningPoints p s 100 (1600 / 9) := by
    exact ⟨by norm_num, by norm_num, hrootMinus, hrootPlus, hclass⟩
  refine ⟨(100, 1600 / 9), hOrdered, ?_⟩
  intro roots hRoots
  rcases hRoots with ⟨hfirst_pos, horder, hfirst, hsecond, hall⟩
  have hfirst_cases := hclass roots.1 hfirst
  have hsecond_cases := hclass roots.2 hsecond
  have hfirst_eq : roots.1 = 100 := by
    rcases hfirst_cases with h | h
    · exact h
    · rcases hsecond_cases with h' | h'
      · exfalso
        rw [h, h'] at horder
        norm_num at horder
      · exfalso
        rw [h, h'] at horder
        exact (lt_irrefl _ horder)
  have hsecond_eq : roots.2 = 1600 / 9 := by
    rcases hsecond_cases with h | h
    · exfalso
      rw [hfirst_eq, h] at horder
      exact (lt_irrefl _ horder)
    · exact h
  apply Prod.ext
  · simpa using hfirst_eq
  · simpa using hsecond_eq

/-- The source separation is the smaller of the two positive turning radii. -/
lemma initialRadius_eq_smallerTurningPoint
    (p : Parameters) (s : InitialState) (hSetup : SourceProblemSetup p s)
    {xMinus xPlus : ℝ}
    (hRoots : AreOrderedPositiveTurningPoints p s xMinus xPlus) :
    (initialReducedData s).separation.val = xMinus * p.bohrRadius.val := by
  rcases hSetup with ⟨hPhysical, hSource, hBound⟩
  have hEnergy := initialEnergy_eq p s hPhysical hSource
  have hAngular := initialAngularMomentumMagnitude_eq p s hPhysical hSource
  have hCoulomb := coulombStrength_mul_bohrRadius p hPhysical
  rcases hPhysical with ⟨hm, he, hε, hℏ, ha, hk, hk_def, ha_def⟩
  dsimp only [HasSourceInitialConditions] at hSource
  rcases hSource with
    ⟨hμ, hR, hanti, hperpPos, hperpElec, hangularPos, hangularElec⟩
  have hCoulomb' :
      (coulombStrength p).val * p.bohrRadius.val * p.mass.val =
        p.reducedPlanckConstant.val ^ 2 := by
    rw [hCoulomb]
    field_simp [ne_of_gt hm]
  have hEnergyExplicit :
      (initialEnergy p s).val =
        (-9 / 2500 : ℝ) *
          (p.reducedPlanckConstant.val ^ 2 /
            (p.mass.val * p.bohrRadius.val ^ 2)) := by
    rw [hEnergy, hμ, hR]
    field_simp [ne_of_gt hm, ne_of_gt ha]
    nlinarith
  have hPolynomial (x : ℝ) :
      (radialTurningPolynomial p s x).val =
        (p.reducedPlanckConstant.val ^ 2 / p.mass.val) *
          ((-9 / 2500 : ℝ) * (x - 100) * (x - 1600 / 9)) := by
    change
      (initialEnergy p s).val * (p.bohrRadius.val * x) ^ 2 +
            (coulombStrength p).val * (p.bohrRadius.val * x) -
          (initialAngularMomentumMagnitude p s).val ^ 2 /
            (2 * (p.mass.val / 2)) =
        (p.reducedPlanckConstant.val ^ 2 / p.mass.val) *
          ((-9 / 2500 : ℝ) * (x - 100) * (x - 1600 / 9))
    rw [hEnergyExplicit, hAngular, hμ]
    rw [show
      (coulombStrength p).val * (p.bohrRadius.val * x) =
        ((coulombStrength p).val * p.bohrRadius.val) * x by ring,
      hCoulomb]
    field_simp [ne_of_gt hm, ne_of_gt ha]
    ring
  have hscale_pos :
      0 < p.reducedPlanckConstant.val ^ 2 / p.mass.val := by positivity
  have hclass (x : ℝ) (hx : IsPositiveTurningPointInBohrRadii p s x) :
      x = 100 ∨ x = 1600 / 9 := by
    change 0 < x ∧ (radialTurningPolynomial p s x).val = 0 at hx
    rw [hPolynomial] at hx
    have hrest : (-9 / 2500 : ℝ) * (x - 100) * (x - 1600 / 9) = 0 :=
      (mul_eq_zero.mp hx.2).resolve_left (ne_of_gt hscale_pos)
    have hfac : (x - 100) * (x - 1600 / 9) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (-9 / 2500 : ℝ) ≠ 0)
      simpa [mul_assoc] using hrest
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hRoots with ⟨hxMinus, horder, hrootMinus, hrootPlus, hall⟩
  have hminus_cases := hclass xMinus hrootMinus
  have hplus_cases := hclass xPlus hrootPlus
  have hminus : xMinus = 100 := by
    rcases hminus_cases with h | h
    · exact h
    · rcases hplus_cases with h' | h'
      · exfalso
        rw [h, h'] at horder
        norm_num at horder
      · exfalso
        rw [h, h'] at horder
        exact lt_irrefl _ horder
  rw [hR, hminus]

/-! ## Conservation and attainment for every admissible motion -/

/-- Internal forces preserve the initial center of mass and equal-and-opposite velocities. -/
lemma centerOfMass_eq_initial
    (p : Parameters) (s : InitialState) (motion : PairMotion)
    (hAdmissible : IsAdmissibleBoundOrbit p s motion) :
    ∀ t : ℝ,
      let o := motionObservables motion t
      let d := initialReducedData s
      o.centerPosition.val = d.centerPosition.val ∧
      (motion.positronVelocity t).val = -(motion.electronVelocity t).val ∧
      (motion.positronPosition t).val - d.centerPosition.val =
          (1 / 2 : ℝ) • o.relativePosition.val ∧
      (motion.electronPosition t).val - d.centerPosition.val =
          (-1 / 2 : ℝ) • o.relativePosition.val := by
  rcases hAdmissible with ⟨hSetup, hExtends, hKinematics, hNewton, hConic⟩
  have hm : 0 < p.mass.val := hSetup.1.1
  have hInitialVelocity :=
    (initial_velocities_eq_neg p s hSetup.1 hSetup.2.1).1
  have hasDerivAt_add
      {f g : ℝ → ℝ} {f' g' x : ℝ}
      (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
      HasDerivAt (fun y ↦ f y + g y) (f' + g') x := by
    apply hasDerivAtFilter_iff_isLittleO.mpr
    refine
      ((hasDerivAtFilter_iff_isLittleO.mp hf).add
        (hasDerivAtFilter_iff_isLittleO.mp hg)).congr_left ?_
    intro z
    dsimp
    ring
  have isLocalMax_hasDerivAt_eq_zero
      {f : ℝ → ℝ} {f' a : ℝ} (h : IsLocalMax f a)
      (hf : HasDerivAt f f' a) : f' = 0 := by
    have hnonpos (y : ℝ) :
        (ContinuousLinearMap.toSpanSingleton ℝ f') y ≤ 0 := by
      have hy : y ∈ posTangentConeAt (Set.univ : Set ℝ) a := by
        change y ∈ tangentConeAt NNReal (Set.univ : Set ℝ) a
        rw [tangentConeAt_univ]
        exact Set.mem_univ y
      rcases exists_fun_of_mem_tangentConeAt hy with
        ⟨ι, l, hl, c, d, hd0, hd, hcd⟩
      have hfF :
          HasFDerivWithinAt f (ContinuousLinearMap.toSpanSingleton ℝ f')
            Set.univ a :=
        (hasDerivAt_iff_hasFDerivAt.mp hf).hasFDerivWithinAt
      suffices ∀ᶠ n in l, c n • (f (a + d n) - f a) ≤ 0 from
        le_of_tendsto (hfF.lim hd0 hd hcd) this
      have hd' :
          Filter.Tendsto (fun n ↦ a + d n) l
            (nhdsWithin (a + 0) Set.univ) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨tendsto_const_nhds.add hd0, hd⟩
      rw [add_zero] at hd'
      refine (hd'.eventually (h.on Set.univ)).mono ?_
      intro n hn
      exact
        mul_nonpos_of_nonneg_of_nonpos (c n).coe_nonneg
          (sub_nonpos.mpr hn)
    apply le_antisymm
    · have h := hnonpos 1
      rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
      exact h
    · have hneg := hnonpos (-1)
      rw [ContinuousLinearMap.toSpanSingleton_apply, neg_one_smul] at hneg
      linarith
  have isLocalMin_hasDerivAt_eq_zero
      {f : ℝ → ℝ} {f' a : ℝ} (h : IsLocalMin f a)
      (hf : HasDerivAt f f' a) : f' = 0 := by
    have hnonneg (y : ℝ) :
        0 ≤ (ContinuousLinearMap.toSpanSingleton ℝ f') y := by
      have hy : y ∈ posTangentConeAt (Set.univ : Set ℝ) a := by
        change y ∈ tangentConeAt NNReal (Set.univ : Set ℝ) a
        rw [tangentConeAt_univ]
        exact Set.mem_univ y
      rcases exists_fun_of_mem_tangentConeAt hy with
        ⟨ι, l, hl, c, d, hd0, hd, hcd⟩
      have hfF :
          HasFDerivWithinAt f (ContinuousLinearMap.toSpanSingleton ℝ f')
            Set.univ a :=
        (hasDerivAt_iff_hasFDerivAt.mp hf).hasFDerivWithinAt
      suffices ∀ᶠ n in l, 0 ≤ c n • (f (a + d n) - f a) from
        ge_of_tendsto (hfF.lim hd0 hd hcd) this
      have hd' :
          Filter.Tendsto (fun n ↦ a + d n) l
            (nhdsWithin (a + 0) Set.univ) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨tendsto_const_nhds.add hd0, hd⟩
      rw [add_zero] at hd'
      refine (hd'.eventually (h.on Set.univ)).mono ?_
      intro n hn
      exact
        mul_nonneg (c n).coe_nonneg (sub_nonneg.mpr hn)
    apply le_antisymm
    · have hneg := hnonneg (-1)
      rw [ContinuousLinearMap.toSpanSingleton_apply, neg_one_smul] at hneg
      linarith
    · have h := hnonneg 1
      rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
      exact h
  have isLocalExtr_hasDerivAt_eq_zero
      {f : ℝ → ℝ} {f' a : ℝ} (h : IsLocalExtr f a)
      (hf : HasDerivAt f f' a) : f' = 0 := by
    rcases h with h | h
    · exact isLocalMin_hasDerivAt_eq_zero h hf
    · exact isLocalMax_hasDerivAt_eq_zero h hf
  have exists_isLocalExtr_Ioo_local
      {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
      (hfc : ContinuousOn f (Set.Icc a b)) (hfI : f a = f b) :
      ∃ c ∈ Set.Ioo a b, IsLocalExtr f c := by
    have ne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab.le
    obtain ⟨c, cmem, cle⟩ :
        ∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f c ≤ f x :=
      isCompact_Icc.exists_isMinOn ne hfc
    obtain ⟨C, Cmem, Cge⟩ :
        ∃ C ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f C :=
      isCompact_Icc.exists_isMaxOn ne hfc
    have hExtr : ∃ z ∈ Set.Ioo a b, IsExtrOn f (Set.Icc a b) z := by
      by_cases hc : f c = f a
      · by_cases hC : f C = f a
        · have hconst : ∀ x ∈ Set.Icc a b, f x = f a := by
            intro x hx
            exact le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx)
          rcases Set.nonempty_Ioo.mpr hab with ⟨z, hz⟩
          refine ⟨z, hz, Or.inl ?_⟩
          intro x hx
          change f z ≤ f x
          rw [hconst x hx, hconst z (Set.Ioo_subset_Icc_self hz)]
        · refine
            ⟨C,
              ⟨lt_of_le_of_ne Cmem.1 (mt ?_ hC),
                lt_of_le_of_ne Cmem.2 (mt ?_ hC)⟩,
              Or.inr Cge⟩
          · intro h
            rw [h]
          · intro h
            rw [h, hfI]
      · refine
          ⟨c,
            ⟨lt_of_le_of_ne cmem.1 (mt ?_ hc),
              lt_of_le_of_ne cmem.2 (mt ?_ hc)⟩,
            Or.inl cle⟩
        · intro h
          rw [h]
        · intro h
          rw [h, hfI]
    rcases hExtr with ⟨z, hz, hzExtr⟩
    exact
      ⟨z, hz, hzExtr.isLocalExtr (Icc_mem_nhds hz.1 hz.2)⟩
  have zeroDerivative_constant
      {f : ℝ → ℝ} (hf : ∀ x : ℝ, HasDerivAt f 0 x) :
      ∀ x y : ℝ, f x = f y := by
    have ordered {a b : ℝ} (hab : a < b) : f a = f b := by
      let g : ℝ → ℝ := fun z ↦
        (b - a) * f z - (f b - f a) * z
      have hfcont : Continuous f :=
        continuous_iff_continuousAt.mpr fun z ↦ (hf z).continuousAt
      have hgcont : ContinuousOn g (Set.Icc a b) := by
        dsimp only [g]
        exact
          ((continuous_const.mul hfcont).sub
            (continuous_const.mul continuous_id)).continuousOn
      have hgEnds : g a = g b := by
        dsimp only [g]
        ring
      have hgDeriv (z : ℝ) : HasDerivAt g (-(f b - f a)) z := by
        apply hasDerivAtFilter_iff_isLittleO.mpr
        refine
          ((hasDerivAtFilter_iff_isLittleO.mp (hf z)).const_mul_left
            (b - a)).congr_left ?_
        intro w
        dsimp only [g]
        ring
      rcases exists_isLocalExtr_Ioo_local hab hgcont hgEnds with
        ⟨z, hz, hzExtr⟩
      have hzDeriv :=
        isLocalExtr_hasDerivAt_eq_zero hzExtr (hgDeriv z)
      linarith
    intro x y
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · exact ordered hxy
    · rw [hxy]
    · exact (ordered hyx).symm
  have hAccelerationSum (t : ℝ) :
      (motion.positronAcceleration t).val +
          (motion.electronAcceleration t).val = 0 := by
    have hn := hNewton t
    dsimp only at hn
    have hscaled :
        p.mass.val •
            ((motion.positronAcceleration t).val +
              (motion.electronAcceleration t).val) = 0 := by
      rw [smul_add, hn.2.1, hn.2.2]
      module
    ext i
    have hi := congrArg (fun v : Plane ↦ v i) hscaled
    change
      p.mass.val *
          ((motion.positronAcceleration t).val i +
            (motion.electronAcceleration t).val i) = 0 at hi
    change
      (motion.positronAcceleration t).val i +
          (motion.electronAcceleration t).val i = 0
    nlinarith
  have hVelocityDerivative (i : Fin 2) (t : ℝ) :
      HasDerivAt
        (fun u ↦
          (motion.positronVelocity u).val i +
            (motion.electronVelocity u).val i) 0 t := by
    have hk := hKinematics t i
    have hd := hasDerivAt_add hk.2.2.1 hk.2.2.2
    have hsum_i := congrArg (fun v : Plane ↦ v i) (hAccelerationSum t)
    change
      (motion.positronAcceleration t).val i +
        (motion.electronAcceleration t).val i = 0 at hsum_i
    rw [hsum_i] at hd
    exact hd
  have hVelocityConstant (i : Fin 2) (t : ℝ) :
      (motion.positronVelocity t).val i +
          (motion.electronVelocity t).val i =
        (motion.positronVelocity s.initialTime.val).val i +
          (motion.electronVelocity s.initialTime.val).val i := by
    exact zeroDerivative_constant (hVelocityDerivative i) t s.initialTime.val
  have hVelocitySum (t : ℝ) :
      (motion.positronVelocity t).val +
          (motion.electronVelocity t).val = 0 := by
    ext i
    have hc := hVelocityConstant i t
    have hp := congrArg (fun q : VelocityQuantity ↦ q.val i) hExtends.2.2.1
    have he := congrArg (fun q : VelocityQuantity ↦ q.val i) hExtends.2.2.2
    have hi := congrArg (fun v : Plane ↦ v i) hInitialVelocity
    change s.positronVelocity.val i = -s.electronVelocity.val i at hi
    change
      (motion.positronVelocity t).val i +
        (motion.electronVelocity t).val i = 0
    rw [hp, he] at hc
    linarith
  have hVelocityNeg (t : ℝ) :
      (motion.positronVelocity t).val =
        -(motion.electronVelocity t).val := by
    ext i
    have hsum := congrArg (fun v : Plane ↦ v i) (hVelocitySum t)
    change
      (motion.positronVelocity t).val i +
        (motion.electronVelocity t).val i = 0 at hsum
    change
      (motion.positronVelocity t).val i =
        -(motion.electronVelocity t).val i
    linarith
  have hPositionDerivative (i : Fin 2) (t : ℝ) :
      HasDerivAt
        (fun u ↦
          (motion.positronPosition u).val i +
            (motion.electronPosition u).val i) 0 t := by
    have hk := hKinematics t i
    have hd := hasDerivAt_add hk.1 hk.2.1
    have hsum_i := congrArg (fun v : Plane ↦ v i) (hVelocitySum t)
    change
      (motion.positronVelocity t).val i +
        (motion.electronVelocity t).val i = 0 at hsum_i
    rw [hsum_i] at hd
    exact hd
  have hPositionConstant (i : Fin 2) (t : ℝ) :
      (motion.positronPosition t).val i +
          (motion.electronPosition t).val i =
        (motion.positronPosition s.initialTime.val).val i +
          (motion.electronPosition s.initialTime.val).val i := by
    exact zeroDerivative_constant (hPositionDerivative i) t s.initialTime.val
  have hPositionSum (t : ℝ) :
      (motion.positronPosition t).val +
          (motion.electronPosition t).val =
        s.positronPosition.val + s.electronPosition.val := by
    ext i
    have hc := hPositionConstant i t
    have hp := congrArg (fun q : PositionQuantity ↦ q.val i) hExtends.1
    have he := congrArg (fun q : PositionQuantity ↦ q.val i) hExtends.2.1
    change
      (motion.positronPosition t).val i +
          (motion.electronPosition t).val i =
        s.positronPosition.val i + s.electronPosition.val i
    rw [hp, he] at hc
    exact hc
  intro t
  dsimp only
  have hcenter :
      (1 / 2 : ℝ) •
          ((motion.positronPosition t).val + (motion.electronPosition t).val) =
        (initialReducedData s).centerPosition.val := by
    rw [hPositionSum]
    rfl
  refine ⟨hcenter, hVelocityNeg t, ?_, ?_⟩
  · change
      (motion.positronPosition t).val - (initialReducedData s).centerPosition.val =
        (1 / 2 : ℝ) •
          ((motion.positronPosition t).val - (motion.electronPosition t).val)
    rw [← hcenter]
    ext i
    change
      (motion.positronPosition t).val i -
          (1 / 2 : ℝ) *
            ((motion.positronPosition t).val i +
              (motion.electronPosition t).val i) =
        (1 / 2 : ℝ) *
          ((motion.positronPosition t).val i -
            (motion.electronPosition t).val i)
    ring
  · change
      (motion.electronPosition t).val - (initialReducedData s).centerPosition.val =
        (-1 / 2 : ℝ) •
          ((motion.positronPosition t).val - (motion.electronPosition t).val)
    rw [← hcenter]
    ext i
    change
      (motion.electronPosition t).val i -
          (1 / 2 : ℝ) *
            ((motion.positronPosition t).val i +
              (motion.electronPosition t).val i) =
        (-1 / 2 : ℝ) *
          ((motion.positronPosition t).val i -
            (motion.electronPosition t).val i)
    ring

/-- Subtracting the two particle equations gives the reduced central-force equation. -/
lemma relative_newton_equation
    (p : Parameters) (s : InitialState) (motion : PairMotion)
    (hAdmissible : IsAdmissibleBoundOrbit p s motion) :
    ∀ t : ℝ,
      let o := motionObservables motion t
      (reducedMass p).val • o.relativeAcceleration.val =
        (-(coulombStrength p).val / o.separation.val ^ 3) •
          o.relativePosition.val := by
  rcases hAdmissible with ⟨hSetup, hExtends, hKinematics, hNewton, hConic⟩
  intro t
  have hNewton_t := hNewton t
  dsimp only at hNewton_t ⊢
  rcases hNewton_t with ⟨hsep, hpositron, helectron⟩
  change
    p.mass.val • (motion.positronAcceleration t).val =
      (-(coulombStrength p).val /
          ‖(motion.positronPosition t).val - (motion.electronPosition t).val‖ ^ 3) •
        ((motion.positronPosition t).val - (motion.electronPosition t).val)
    at hpositron
  change
    p.mass.val • (motion.electronAcceleration t).val =
      ((coulombStrength p).val /
          ‖(motion.positronPosition t).val - (motion.electronPosition t).val‖ ^ 3) •
        ((motion.positronPosition t).val - (motion.electronPosition t).val)
    at helectron
  calc
    (p.mass.val / 2) •
          ((motion.positronAcceleration t).val -
            (motion.electronAcceleration t).val) =
        (1 / 2 : ℝ) •
          (p.mass.val • (motion.positronAcceleration t).val -
            p.mass.val • (motion.electronAcceleration t).val) := by module
    _ = (-(coulombStrength p).val /
          ‖(motion.positronPosition t).val - (motion.electronPosition t).val‖ ^ 3) •
        ((motion.positronPosition t).val - (motion.electronPosition t).val) := by
      rw [hpositron, helectron]
      ext i
      simp
      ring

/-- Relative angular momentum and energy retain their initial values; the same values are
the total angular momentum and total mechanical energy in the center-of-mass frame. -/
lemma relative_invariants_conserved
    (p : Parameters) (s : InitialState) (motion : PairMotion)
    (hAdmissible : IsAdmissibleBoundOrbit p s motion) :
    ∀ t : ℝ,
      let o := motionObservables motion t
      let d := initialReducedData s
      (relativeAngularMomentumValue p motion t).val =
          (relativeAngularMomentumValue p motion s.initialTime.val).val ∧
      abs (relativeAngularMomentumValue p motion t).val =
          (initialAngularMomentumMagnitude p s).val ∧
      (relativeEnergyValue p motion t).val = (initialEnergy p s).val ∧
      abs
          ((particleAngularMomentumValue p (motion.positronPosition t)
              (motion.positronVelocity t) d.centerPosition).val +
            (particleAngularMomentumValue p (motion.electronPosition t)
              (motion.electronVelocity t) d.centerPosition).val) =
        (initialAngularMomentumMagnitude p s).val ∧
      p.mass.val / 2 *
            (‖(motion.positronVelocity t).val‖ ^ 2 +
              ‖(motion.electronVelocity t).val‖ ^ 2) -
          (coulombStrength p).val / o.separation.val =
        (initialEnergy p s).val := by
  have hmass : 0 < p.mass.val := hAdmissible.1.1.1
  have hreducedMass : 0 < (reducedMass p).val := by
    change 0 < p.mass.val / 2
    exact half_pos hmass
  have hasDerivAt_add
      {f g : ℝ → ℝ} {f' g' x : ℝ}
      (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
      HasDerivAt (fun y ↦ f y + g y) (f' + g') x := by
    apply hasDerivAtFilter_iff_isLittleO.mpr
    refine
      ((hasDerivAtFilter_iff_isLittleO.mp hf).add
        (hasDerivAtFilter_iff_isLittleO.mp hg)).congr_left ?_
    intro z
    dsimp
    ring
  have hasDerivAt_sub
      {f g : ℝ → ℝ} {f' g' x : ℝ}
      (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
      HasDerivAt (fun y ↦ f y - g y) (f' - g') x := by
    apply hasDerivAtFilter_iff_isLittleO.mpr
    refine
      ((hasDerivAtFilter_iff_isLittleO.mp hf).sub
        (hasDerivAtFilter_iff_isLittleO.mp hg)).congr_left ?_
    intro z
    dsimp
    ring
  have fderivFilter_comp
      {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {u : ℝ → F} {v : F → ℝ} {u' : ℝ →L[ℝ] F}
      {v' : F →L[ℝ] ℝ} {L : Filter (ℝ × ℝ)} {L' : Filter (F × F)}
      (hv : HasFDerivAtFilter v v' L')
      (hu : HasFDerivAtFilter u u' L)
      (hL : Filter.Tendsto (Prod.map u u) L L') :
      HasFDerivAtFilter (v ∘ u) (v'.comp u') L := by
    apply HasFDerivAtFilter.of_isLittleOTVS
    calc
      (fun q ↦
          (v ∘ u) q.1 - (v ∘ u) q.2 -
            (v'.comp u') (q.1 - q.2)) =
          fun q ↦
            (v (u q.1) - v (u q.2) - v' (u q.1 - u q.2)) +
              v' (u q.1 - u q.2 - u' (q.1 - q.2)) := by
        ext q
        repeat' rw [Function.comp_apply]
        rw [ContinuousLinearMap.comp_apply]
        repeat' rw [map_sub]
        ring
      _ =o[ℝ; L] (fun q ↦ q.1 - q.2) := by
        apply Asymptotics.IsLittleOTVS.add
        · exact
            (hv.isLittleOTVS.comp_tendsto hL).trans_isBigOTVS
              hu.isBigOTVS_sub
        · exact
            v'.isBigOTVS_comp.trans_isLittleOTVS hu.isLittleOTVS
  have fderiv_comp
      {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {u : ℝ → F} {v : F → ℝ} {u' : ℝ →L[ℝ] F}
      {v' : F →L[ℝ] ℝ} {z : ℝ}
      (hv : HasFDerivAt v v' (u z)) (hu : HasFDerivAt u u' z) :
      HasFDerivAt (v ∘ u) (v'.comp u') z := by
    exact
      fderivFilter_comp hv hu
        (hu.continuousAt.tendsto.prodMap (Filter.tendsto_pure_pure u z))
  have fderivFilter_prodMk
      {u v : ℝ → ℝ} {u' v' : ℝ →L[ℝ] ℝ}
      {L : Filter (ℝ × ℝ)}
      (hu : HasFDerivAtFilter u u' L)
      (hv : HasFDerivAtFilter v v' L) :
      HasFDerivAtFilter (fun y ↦ (u y, v y)) (u'.prod v') L := by
    exact
      HasFDerivAtFilter.of_isLittleO
        (hu.isLittleO.prod_left hv.isLittleO)
  have fderiv_prodMk
      {u v : ℝ → ℝ} {u' v' : ℝ →L[ℝ] ℝ} {z : ℝ}
      (hu : HasFDerivAt u u' z) (hv : HasFDerivAt v v' z) :
      HasFDerivAt (fun y ↦ (u y, v y)) (u'.prod v') z := by
    exact fderivFilter_prodMk hu hv
  let multiplication : ℝ × ℝ → ℝ := fun q ↦ q.1 * q.2
  have hMultiplication : IsBoundedBilinearMap ℝ multiplication :=
    (ContinuousLinearMap.mul ℝ ℝ).isBoundedBilinearMap
  have multiplication_hasStrictFDerivAt (q : ℝ × ℝ) :
      HasStrictFDerivAt multiplication (hMultiplication.deriv q) q := by
    rw [hasStrictFDerivAt_iff_isLittleO]
    rw [← map_add_left_nhds_zero (q, q),
      Asymptotics.isLittleO_map]
    set ProductT := (ℝ × ℝ) × ℝ × ℝ
    calc
      _ = fun z ↦
          hMultiplication.deriv (z.1 - z.2) (z.2.1, z.1.2) := by
        ext z
        rcases q with ⟨a, c⟩
        repeat' rw [map_sub]
        repeat' rw [IsBoundedBilinearMap.deriv_apply]
        repeat' rw [Function.comp_apply]
        repeat' rw [Prod.mk_add_mk]
        repeat' rw [hMultiplication.add_right]
        repeat' rw [hMultiplication.add_left]
        repeat' rw [Prod.mk_sub_mk]
        repeat' rw [hMultiplication.map_sub_left]
        repeat' rw [hMultiplication.map_sub_right]
        repeat' rw [sub_add_sub_cancel]
        rw [IsBoundedBilinearMap.deriv_apply]
        dsimp only [multiplication]
        ring
      _ =o[nhds (0 : ProductT)] fun z ↦ z.1 - z.2 := by
        refine
          hMultiplication.toContinuousLinearMap.deriv₂.isBoundedBilinearMap.isBigO_comp
            |>.trans_isLittleO ?_
        suffices
            (fun z : ProductT ↦
                ‖z.1 - z.2‖ * ‖(z.2.1, z.1.2)‖) =o[nhds 0]
              fun z ↦ ‖z.1 - z.2‖ * 1 by
          have hnorm := this.congr'
            (Filter.Eventually.of_forall fun _ ↦ rfl)
            (Filter.Eventually.of_forall fun z ↦ by
              change ‖z.1 - z.2‖ * 1 = ‖z.1 - z.2‖
              rw [mul_one])
          exact hnorm.of_norm_right
        refine
          (Asymptotics.isBigO_refl _ _).mul_isLittleO
            ((Asymptotics.isLittleO_one_iff _).2 ?_)
        exact
          (continuous_snd.fst.prodMk continuous_fst.snd).norm.tendsto'
            _ _ (by
              change ‖((0, 0) : ℝ × ℝ)‖ = 0
              rw [Prod.norm_def, norm_zero, max_self])
      _ = _ := by
        funext z
        change z.1 - z.2 = (q + z.1) - (q + z.2)
        ext <;> ring
  have hasDerivAt_mul
      {f g : ℝ → ℝ} {f' g' x : ℝ}
      (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
      HasDerivAt (fun y ↦ f y * g y) (f' * g x + f x * g') x := by
    have hp :=
      fderiv_prodMk (hasDerivAt_iff_hasFDerivAt.mp hf)
        (hasDerivAt_iff_hasFDerivAt.mp hg)
    have hc :=
      fderiv_comp (u := fun y ↦ (f y, g y)) (v := multiplication)
        (multiplication_hasStrictFDerivAt (f x, g x)).hasFDerivAt hp
    have hmap :
        ContinuousLinearMap.toSpanSingleton ℝ
            (f' * g x + f x * g') =
          (hMultiplication.deriv (f x, g x)).comp
            ((ContinuousLinearMap.toSpanSingleton ℝ f').prod
              (ContinuousLinearMap.toSpanSingleton ℝ g')) := by
      apply ContinuousLinearMap.ext
      intro y
      rw [ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.toSpanSingleton_apply,
        IsBoundedBilinearMap.deriv_apply]
      dsimp only [multiplication]
      repeat' rw [smul_eq_mul]
      ring
    rw [hasDerivAt_iff_hasFDerivAt, hmap]
    exact hc
  have isLocalMax_hasDerivAt_eq_zero
      {f : ℝ → ℝ} {f' a : ℝ} (h : IsLocalMax f a)
      (hf : HasDerivAt f f' a) : f' = 0 := by
    have hnonpos (y : ℝ) :
        (ContinuousLinearMap.toSpanSingleton ℝ f') y ≤ 0 := by
      have hy : y ∈ posTangentConeAt (Set.univ : Set ℝ) a := by
        change y ∈ tangentConeAt NNReal (Set.univ : Set ℝ) a
        rw [tangentConeAt_univ]
        exact Set.mem_univ y
      rcases exists_fun_of_mem_tangentConeAt hy with
        ⟨ι, l, hl, c, d, hd0, hd, hcd⟩
      have hfF :
          HasFDerivWithinAt f (ContinuousLinearMap.toSpanSingleton ℝ f')
            Set.univ a :=
        (hasDerivAt_iff_hasFDerivAt.mp hf).hasFDerivWithinAt
      suffices ∀ᶠ n in l, c n • (f (a + d n) - f a) ≤ 0 from
        le_of_tendsto (hfF.lim hd0 hd hcd) this
      have hd' :
          Filter.Tendsto (fun n ↦ a + d n) l
            (nhdsWithin (a + 0) Set.univ) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨tendsto_const_nhds.add hd0, hd⟩
      rw [add_zero] at hd'
      refine (hd'.eventually (h.on Set.univ)).mono ?_
      intro n hn
      exact
        mul_nonpos_of_nonneg_of_nonpos (c n).coe_nonneg
          (sub_nonpos.mpr hn)
    apply le_antisymm
    · have h := hnonpos 1
      rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
      exact h
    · have hneg := hnonpos (-1)
      rw [ContinuousLinearMap.toSpanSingleton_apply, neg_one_smul] at hneg
      linarith
  have isLocalMin_hasDerivAt_eq_zero
      {f : ℝ → ℝ} {f' a : ℝ} (h : IsLocalMin f a)
      (hf : HasDerivAt f f' a) : f' = 0 := by
    have hnonneg (y : ℝ) :
        0 ≤ (ContinuousLinearMap.toSpanSingleton ℝ f') y := by
      have hy : y ∈ posTangentConeAt (Set.univ : Set ℝ) a := by
        change y ∈ tangentConeAt NNReal (Set.univ : Set ℝ) a
        rw [tangentConeAt_univ]
        exact Set.mem_univ y
      rcases exists_fun_of_mem_tangentConeAt hy with
        ⟨ι, l, hl, c, d, hd0, hd, hcd⟩
      have hfF :
          HasFDerivWithinAt f (ContinuousLinearMap.toSpanSingleton ℝ f')
            Set.univ a :=
        (hasDerivAt_iff_hasFDerivAt.mp hf).hasFDerivWithinAt
      suffices ∀ᶠ n in l, 0 ≤ c n • (f (a + d n) - f a) from
        ge_of_tendsto (hfF.lim hd0 hd hcd) this
      have hd' :
          Filter.Tendsto (fun n ↦ a + d n) l
            (nhdsWithin (a + 0) Set.univ) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨tendsto_const_nhds.add hd0, hd⟩
      rw [add_zero] at hd'
      refine (hd'.eventually (h.on Set.univ)).mono ?_
      intro n hn
      exact mul_nonneg (c n).coe_nonneg (sub_nonneg.mpr hn)
    apply le_antisymm
    · have hneg := hnonneg (-1)
      rw [ContinuousLinearMap.toSpanSingleton_apply, neg_one_smul] at hneg
      linarith
    · have h := hnonneg 1
      rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
      exact h
  have isLocalExtr_hasDerivAt_eq_zero
      {f : ℝ → ℝ} {f' a : ℝ} (h : IsLocalExtr f a)
      (hf : HasDerivAt f f' a) : f' = 0 := by
    rcases h with h | h
    · exact isLocalMin_hasDerivAt_eq_zero h hf
    · exact isLocalMax_hasDerivAt_eq_zero h hf
  have exists_isLocalExtr_Ioo_local
      {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
      (hfc : ContinuousOn f (Set.Icc a b)) (hfI : f a = f b) :
      ∃ c ∈ Set.Ioo a b, IsLocalExtr f c := by
    have ne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab.le
    obtain ⟨c, cmem, cle⟩ :
        ∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f c ≤ f x :=
      isCompact_Icc.exists_isMinOn ne hfc
    obtain ⟨C, Cmem, Cge⟩ :
        ∃ C ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f C :=
      isCompact_Icc.exists_isMaxOn ne hfc
    have hExtr : ∃ z ∈ Set.Ioo a b, IsExtrOn f (Set.Icc a b) z := by
      by_cases hc : f c = f a
      · by_cases hC : f C = f a
        · have hconst : ∀ x ∈ Set.Icc a b, f x = f a := by
            intro x hx
            exact le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx)
          rcases Set.nonempty_Ioo.mpr hab with ⟨z, hz⟩
          refine ⟨z, hz, Or.inl ?_⟩
          intro x hx
          change f z ≤ f x
          rw [hconst x hx, hconst z (Set.Ioo_subset_Icc_self hz)]
        · refine
            ⟨C,
              ⟨lt_of_le_of_ne Cmem.1 (mt ?_ hC),
                lt_of_le_of_ne Cmem.2 (mt ?_ hC)⟩,
              Or.inr Cge⟩
          · intro h
            rw [h]
          · intro h
            rw [h, hfI]
      · refine
          ⟨c,
            ⟨lt_of_le_of_ne cmem.1 (mt ?_ hc),
              lt_of_le_of_ne cmem.2 (mt ?_ hc)⟩,
            Or.inl cle⟩
        · intro h
          rw [h]
        · intro h
          rw [h, hfI]
    rcases hExtr with ⟨z, hz, hzExtr⟩
    exact ⟨z, hz, hzExtr.isLocalExtr (Icc_mem_nhds hz.1 hz.2)⟩
  have zeroDerivative_constant
      {f : ℝ → ℝ} (hf : ∀ x : ℝ, HasDerivAt f 0 x) :
      ∀ x y : ℝ, f x = f y := by
    have ordered {a b : ℝ} (hab : a < b) : f a = f b := by
      let g : ℝ → ℝ := fun z ↦
        (b - a) * f z - (f b - f a) * z
      have hfcont : Continuous f :=
        continuous_iff_continuousAt.mpr fun z ↦ (hf z).continuousAt
      have hgcont : ContinuousOn g (Set.Icc a b) := by
        dsimp only [g]
        exact
          ((continuous_const.mul hfcont).sub
            (continuous_const.mul continuous_id)).continuousOn
      have hgEnds : g a = g b := by
        dsimp only [g]
        ring
      have hgDeriv (z : ℝ) : HasDerivAt g (-(f b - f a)) z := by
        apply hasDerivAtFilter_iff_isLittleO.mpr
        refine
          ((hasDerivAtFilter_iff_isLittleO.mp (hf z)).const_mul_left
            (b - a)).congr_left ?_
        intro w
        dsimp only [g]
        ring
      rcases exists_isLocalExtr_Ioo_local hab hgcont hgEnds with
        ⟨z, hz, hzExtr⟩
      have hzDeriv :=
        isLocalExtr_hasDerivAt_eq_zero hzExtr (hgDeriv z)
      linarith
    intro x y
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · exact ordered hxy
    · rw [hxy]
    · exact (ordered hyx).symm
  have hAngularConserved :
      ∀ t : ℝ,
        (relativeAngularMomentumValue p motion t).val =
          (relativeAngularMomentumValue p motion s.initialTime.val).val := by
    have hCentralForce := relative_newton_equation p s motion hAdmissible
    have hKinematics := hAdmissible.2.2.1
    let r0 : ℝ → ℝ := fun t ↦
      (motion.positronPosition t).val 0 -
        (motion.electronPosition t).val 0
    let r1 : ℝ → ℝ := fun t ↦
      (motion.positronPosition t).val 1 -
        (motion.electronPosition t).val 1
    let w0 : ℝ → ℝ := fun t ↦
      (motion.positronVelocity t).val 0 -
        (motion.electronVelocity t).val 0
    let w1 : ℝ → ℝ := fun t ↦
      (motion.positronVelocity t).val 1 -
        (motion.electronVelocity t).val 1
    let a0 : ℝ → ℝ := fun t ↦
      (motion.positronAcceleration t).val 0 -
        (motion.electronAcceleration t).val 0
    let a1 : ℝ → ℝ := fun t ↦
      (motion.positronAcceleration t).val 1 -
        (motion.electronAcceleration t).val 1
    let forceCoefficient : ℝ → ℝ := fun t ↦
      -(coulombStrength p).val /
        ‖(motion.positronPosition t).val -
            (motion.electronPosition t).val‖ ^ 3
    have hr0 (t : ℝ) : HasDerivAt r0 (w0 t) t := by
      exact
        hasDerivAt_sub (hKinematics t 0).1 (hKinematics t 0).2.1
    have hr1 (t : ℝ) : HasDerivAt r1 (w1 t) t := by
      exact
        hasDerivAt_sub (hKinematics t 1).1 (hKinematics t 1).2.1
    have hw0 (t : ℝ) : HasDerivAt w0 (a0 t) t := by
      exact
        hasDerivAt_sub (hKinematics t 0).2.2.1
          (hKinematics t 0).2.2.2
    have hw1 (t : ℝ) : HasDerivAt w1 (a1 t) t := by
      exact
        hasDerivAt_sub (hKinematics t 1).2.2.1
          (hKinematics t 1).2.2.2
    have hForceCoordinate (t : ℝ) (i : Fin 2) :
        (reducedMass p).val *
            ((motion.positronAcceleration t).val i -
              (motion.electronAcceleration t).val i) =
          forceCoefficient t *
            ((motion.positronPosition t).val i -
              (motion.electronPosition t).val i) := by
      have hforce := hCentralForce t
      change
        (reducedMass p).val •
            ((motion.positronAcceleration t).val -
              (motion.electronAcceleration t).val) =
          (-(coulombStrength p).val /
              ‖(motion.positronPosition t).val -
                (motion.electronPosition t).val‖ ^ 3) •
            ((motion.positronPosition t).val -
              (motion.electronPosition t).val)
        at hforce
      have hi := congrArg (fun v : Plane ↦ v i) hforce
      change
        (reducedMass p).val *
            ((motion.positronAcceleration t).val i -
              (motion.electronAcceleration t).val i) =
          forceCoefficient t *
            ((motion.positronPosition t).val i -
              (motion.electronPosition t).val i) at hi
      exact hi
    have hAngularDerivative (t : ℝ) :
        HasDerivAt
          (fun u ↦ (relativeAngularMomentumValue p motion u).val) 0 t := by
      have hFirst := hasDerivAt_mul (hr0 t) (hw1 t)
      have hSecond := hasDerivAt_mul (hr1 t) (hw0 t)
      have hCross := hasDerivAt_sub hFirst hSecond
      have hScaled :=
        hasDerivAt_mul
          (hasDerivAt_const (x := t) (reducedMass p).val) hCross
      have hForce0 :
          (reducedMass p).val * a0 t = forceCoefficient t * r0 t := by
        change
          (reducedMass p).val *
              ((motion.positronAcceleration t).val 0 -
                (motion.electronAcceleration t).val 0) =
            forceCoefficient t *
              ((motion.positronPosition t).val 0 -
                (motion.electronPosition t).val 0)
        exact hForceCoordinate t 0
      have hForce1 :
          (reducedMass p).val * a1 t = forceCoefficient t * r1 t := by
        change
          (reducedMass p).val *
              ((motion.positronAcceleration t).val 1 -
                (motion.electronAcceleration t).val 1) =
            forceCoefficient t *
              ((motion.positronPosition t).val 1 -
                (motion.electronPosition t).val 1)
        exact hForceCoordinate t 1
      have hTorque :
          (reducedMass p).val *
              ((w0 t * w1 t + r0 t * a1 t) -
                (w1 t * w0 t + r1 t * a0 t)) = 0 := by
        calc
          (reducedMass p).val *
                ((w0 t * w1 t + r0 t * a1 t) -
                  (w1 t * w0 t + r1 t * a0 t)) =
              r0 t * ((reducedMass p).val * a1 t) -
                r1 t * ((reducedMass p).val * a0 t) := by ring
          _ = r0 t * (forceCoefficient t * r1 t) -
                r1 t * (forceCoefficient t * r0 t) := by
              rw [hForce0, hForce1]
          _ = 0 := by ring
      have hfun :
          (fun u ↦ (relativeAngularMomentumValue p motion u).val) =
            fun u ↦ (reducedMass p).val *
              (r0 u * w1 u - r1 u * w0 u) := by
        funext u
        rfl
      have hderiv :
          0 * (r0 t * w1 t - r1 t * w0 t) +
              (reducedMass p).val *
                ((w0 t * w1 t + r0 t * a1 t) -
                  (w1 t * w0 t + r1 t * a0 t)) = 0 := by
        rw [zero_mul, zero_add, hTorque]
      rw [hfun, ← hderiv]
      exact hScaled
    intro t
    exact
      zeroDerivative_constant hAngularDerivative t s.initialTime.val
  have hEnergyConserved :
      ∀ t : ℝ,
        (relativeEnergyValue p motion t).val = (initialEnergy p s).val := by
    have hCentralForce := relative_newton_equation p s motion hAdmissible
    have hKinematics := hAdmissible.2.2.1
    have hasDerivAt_comp_scalar
        {u v : ℝ → ℝ} {u' v' z : ℝ}
        (hv : HasDerivAt v v' (u z)) (hu : HasDerivAt u u' z) :
        HasDerivAt (fun y ↦ v (u y)) (v' * u') z := by
      have hc :=
        fderiv_comp (F := ℝ)
          (hasDerivAt_iff_hasFDerivAt.mp hv)
          (hasDerivAt_iff_hasFDerivAt.mp hu)
      have hmap :
          ContinuousLinearMap.toSpanSingleton ℝ (v' * u') =
            (ContinuousLinearMap.toSpanSingleton ℝ v').comp
              (ContinuousLinearMap.toSpanSingleton ℝ u') := by
        apply ContinuousLinearMap.ext
        intro y
        change y * (v' * u') = (y * u') * v'
        ring
      rw [hasDerivAt_iff_hasFDerivAt, hmap]
      exact hc
    have hasStrictDerivAt_inv_local {x : ℝ} (hx : x ≠ 0) :
        HasStrictDerivAt (fun y : ℝ ↦ y⁻¹) (-(x ^ 2)⁻¹) x := by
      suffices
          (fun q : ℝ × ℝ ↦
              (q.1 - q.2) * ((x * x)⁻¹ - (q.1 * q.2)⁻¹)) =o[nhds (x, x)]
            fun q ↦ (q.1 - q.2) * 1 by
        refine
          HasFDerivAtFilter.of_isLittleO
            (this.congr' ?_
              (Filter.Eventually.of_forall fun _ ↦ mul_one _))
        refine
          Filter.Eventually.mono
            ((isOpen_ne.prod isOpen_ne).mem_nhds ⟨hx, hx⟩) ?_
        rintro ⟨y, z⟩ ⟨hy, hz⟩
        change y ≠ 0 at hy
        change z ≠ 0 at hz
        change
          (y - z) * ((x * x)⁻¹ - (y * z)⁻¹) =
            y⁻¹ - z⁻¹ -
              (ContinuousLinearMap.toSpanSingleton ℝ (-(x ^ 2)⁻¹)) (y - z)
        rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
        change
          (y - z) * ((x * x)⁻¹ - (y * z)⁻¹) =
            y⁻¹ - z⁻¹ - (y - z) * (-(x ^ 2)⁻¹)
        rw [inv_sub_inv hy hz, div_eq_mul_inv]
        ring
      refine
        (Asymptotics.isBigO_refl (fun q : ℝ × ℝ ↦ q.1 - q.2) _).mul_isLittleO
          ((Asymptotics.isLittleO_one_iff ℝ).2 ?_)
      rw [← sub_self (x * x)⁻¹]
      exact
        tendsto_const_nhds.sub
          ((continuous_mul.tendsto (x, x)).inv₀ (mul_ne_zero hx hx))
    have hasDerivAt_inv_comp
        {u : ℝ → ℝ} {u' z : ℝ} (hu : HasDerivAt u u' z)
        (hu_ne : u z ≠ 0) :
        HasDerivAt (fun y ↦ (u y)⁻¹) (-(u z ^ 2)⁻¹ * u') z := by
      exact
        hasDerivAt_comp_scalar
          (hasStrictDerivAt_inv_local hu_ne).hasDerivAt hu
    have hasDerivAt_of_sq
        {r q : ℝ → ℝ} {q' t : ℝ}
        (hr : ContinuousAt r t) (hrt : 0 < r t)
        (hq : HasDerivAt q q' t) (hsq : ∀ u, q u = r u ^ 2) :
        HasDerivAt r (q' / (2 * r t)) t := by
      let D : ℝ → ℝ := fun u ↦ r u + r t
      have hDlim :
          Filter.Tendsto D (nhds t) (nhds (2 * r t)) := by
        have hc :
            Filter.Tendsto (fun _ : ℝ ↦ r t) (nhds t) (nhds (r t)) :=
          tendsto_const_nhds
        convert hr.tendsto.add hc using 1 <;> ring
      have hTwoR : 2 * r t ≠ 0 :=
        mul_ne_zero two_ne_zero (ne_of_gt hrt)
      have hDne : ∀ᶠ u in nhds t, D u ≠ 0 :=
        hDlim.eventually_ne hTwoR
      have hInvLim :
          Filter.Tendsto (fun u ↦ (D u)⁻¹) (nhds t)
            (nhds ((2 * r t)⁻¹)) :=
        hDlim.inv₀ hTwoR
      have hInvBig :
          (fun u ↦ (D u)⁻¹) =O[nhds t]
            (fun _ : ℝ ↦ (1 : ℝ)) :=
        hInvLim.isBigO_one ℝ
      have hFirst :
          (fun u ↦
              (q u - q t - (u - t) * q') * (D u)⁻¹) =o[nhds t]
            fun u ↦ u - t := by
        have h := hq.isLittleO.mul_isBigO hInvBig
        exact h.congr'
          (Filter.Eventually.of_forall fun u ↦ by
            change
              (q u - q t - (u - t) • q') * (D u)⁻¹ =
                (q u - q t - (u - t) * q') * (D u)⁻¹
            rw [smul_eq_mul])
          (Filter.Eventually.of_forall fun u ↦ by
            change (u - t) * 1 = u - t
            rw [mul_one])
      have hDeltaLim :
          Filter.Tendsto
              (fun u ↦ (D u)⁻¹ - (2 * r t)⁻¹) (nhds t) (nhds 0) := by
        have hc :
            Filter.Tendsto (fun _ : ℝ ↦ (2 * r t)⁻¹) (nhds t)
              (nhds ((2 * r t)⁻¹)) :=
          tendsto_const_nhds
        have h := hInvLim.sub hc
        rw [sub_self] at h
        exact h
      have hDeltaLittle :
          (fun u ↦ (D u)⁻¹ - (2 * r t)⁻¹) =o[nhds t]
            (fun _ : ℝ ↦ (1 : ℝ)) :=
        (Asymptotics.isLittleO_one_iff ℝ).2 hDeltaLim
      have hLinearBig :
          (fun u ↦ (u - t) * q') =O[nhds t] fun u ↦ u - t := by
        have h :=
          (Asymptotics.isBigO_refl (fun u : ℝ ↦ u - t) (nhds t)).const_mul_left q'
        exact h.congr'
          (Filter.Eventually.of_forall fun u ↦ by ring)
          (Filter.Eventually.of_forall fun _ ↦ rfl)
      have hSecond :
          (fun u ↦
              ((u - t) * q') * ((D u)⁻¹ - (2 * r t)⁻¹)) =o[nhds t]
            fun u ↦ u - t := by
        have h := hLinearBig.mul_isLittleO hDeltaLittle
        exact h.congr'
          (Filter.Eventually.of_forall fun _ ↦ rfl)
          (Filter.Eventually.of_forall fun u ↦ by
            change (u - t) * 1 = u - t
            rw [mul_one])
      apply HasDerivAt.of_isLittleO
      refine
        (hFirst.add hSecond).congr' ?_
          (Filter.Eventually.of_forall fun _ ↦ rfl)
      filter_upwards [hDne] with u hDu
      calc
        (q u - q t - (u - t) * q') * (D u)⁻¹ +
              (u - t) * q' * ((D u)⁻¹ - (2 * r t)⁻¹) =
            (q u - q t) * (D u)⁻¹ -
              (u - t) * q' * (2 * r t)⁻¹ := by ring
        _ = (r u ^ 2 - r t ^ 2) * (D u)⁻¹ -
              (u - t) * q' * (2 * r t)⁻¹ := by
                rw [hsq u, hsq t]
        _ = ((r u - r t) * (r u + r t)) * (D u)⁻¹ -
              (u - t) * q' * (2 * r t)⁻¹ := by
                ring
        _ = (r u - r t) -
              (u - t) * q' * (2 * r t)⁻¹ := by
                dsimp only [D]
                rw [mul_inv_cancel_right₀ hDu]
        _ = r u - r t - (u - t) • (q' / (2 * r t)) := by
                rw [smul_eq_mul, div_eq_mul_inv]
                ring
    let r0 : ℝ → ℝ := fun t ↦
      (motion.positronPosition t).val 0 -
        (motion.electronPosition t).val 0
    let r1 : ℝ → ℝ := fun t ↦
      (motion.positronPosition t).val 1 -
        (motion.electronPosition t).val 1
    let w0 : ℝ → ℝ := fun t ↦
      (motion.positronVelocity t).val 0 -
        (motion.electronVelocity t).val 0
    let w1 : ℝ → ℝ := fun t ↦
      (motion.positronVelocity t).val 1 -
        (motion.electronVelocity t).val 1
    let a0 : ℝ → ℝ := fun t ↦
      (motion.positronAcceleration t).val 0 -
        (motion.electronAcceleration t).val 0
    let a1 : ℝ → ℝ := fun t ↦
      (motion.positronAcceleration t).val 1 -
        (motion.electronAcceleration t).val 1
    let radius : ℝ → ℝ := fun t ↦
      ‖(motion.positronPosition t).val -
          (motion.electronPosition t).val‖
    let radialSquare : ℝ → ℝ := fun t ↦
      r0 t * r0 t + r1 t * r1 t
    let radialDot : ℝ → ℝ := fun t ↦
      r0 t * w0 t + r1 t * w1 t
    let forceCoefficient : ℝ → ℝ := fun t ↦
      -(coulombStrength p).val / radius t ^ 3
    let kinetic : ℝ → ℝ := fun t ↦
      (reducedMass p).val / 2 *
        (w0 t * w0 t + w1 t * w1 t)
    let potential : ℝ → ℝ := fun t ↦
      (coulombStrength p).val * (radius t)⁻¹
    have hr0 (t : ℝ) : HasDerivAt r0 (w0 t) t := by
      exact
        hasDerivAt_sub (hKinematics t 0).1 (hKinematics t 0).2.1
    have hr1 (t : ℝ) : HasDerivAt r1 (w1 t) t := by
      exact
        hasDerivAt_sub (hKinematics t 1).1 (hKinematics t 1).2.1
    have hw0 (t : ℝ) : HasDerivAt w0 (a0 t) t := by
      exact
        hasDerivAt_sub (hKinematics t 0).2.2.1
          (hKinematics t 0).2.2.2
    have hw1 (t : ℝ) : HasDerivAt w1 (a1 t) t := by
      exact
        hasDerivAt_sub (hKinematics t 1).2.2.1
          (hKinematics t 1).2.2.2
    have hRadiusContinuous (t : ℝ) : ContinuousAt radius t := by
      have h0 := hasDerivAt_mul (hr0 t) (hr0 t)
      have h1 := hasDerivAt_mul (hr1 t) (hr1 t)
      have hqcont : ContinuousAt radialSquare t :=
        (hasDerivAt_add h0 h1).continuousAt
      have hfun : radius = fun u ↦ Real.sqrt (radialSquare u) := by
        funext u
        have hsq : radialSquare u = radius u ^ 2 := by
          dsimp only [radialSquare, radius, r0, r1]
          rw [EuclideanSpace.real_norm_sq_eq]
          rw [Fin.sum_univ_two]
          change
            ((motion.positronPosition u).val 0 -
                  (motion.electronPosition u).val 0) *
                ((motion.positronPosition u).val 0 -
                  (motion.electronPosition u).val 0) +
              ((motion.positronPosition u).val 1 -
                  (motion.electronPosition u).val 1) *
                ((motion.positronPosition u).val 1 -
                  (motion.electronPosition u).val 1) =
            ((motion.positronPosition u).val 0 -
                  (motion.electronPosition u).val 0) ^ 2 +
              ((motion.positronPosition u).val 1 -
                  (motion.electronPosition u).val 1) ^ 2
          ring
        rw [hsq, Real.sqrt_sq (norm_nonneg _)]
      rw [hfun]
      exact Real.continuous_sqrt.continuousAt.comp hqcont
    have hRadiusPos (t : ℝ) : 0 < radius t := by
      have hn := hAdmissible.2.2.2.1 t
      dsimp only at hn
      have hsep := hn.1
      change
        0 < ‖(motion.positronPosition t).val -
          (motion.electronPosition t).val‖ at hsep
      change
        0 < ‖(motion.positronPosition t).val -
          (motion.electronPosition t).val‖
      exact hsep
    have hRadialSquare (t : ℝ) :
        HasDerivAt radialSquare (2 * radialDot t) t := by
      have h0 := hasDerivAt_mul (hr0 t) (hr0 t)
      have h1 := hasDerivAt_mul (hr1 t) (hr1 t)
      convert hasDerivAt_add h0 h1 using 1 <;>
        dsimp only [radialSquare, radialDot] <;> ring
    have hRadialSquare_eq (t : ℝ) :
        radialSquare t = radius t ^ 2 := by
      dsimp only [radialSquare, radius, r0, r1]
      rw [EuclideanSpace.real_norm_sq_eq]
      rw [Fin.sum_univ_two]
      change
        ((motion.positronPosition t).val 0 -
              (motion.electronPosition t).val 0) *
            ((motion.positronPosition t).val 0 -
              (motion.electronPosition t).val 0) +
          ((motion.positronPosition t).val 1 -
              (motion.electronPosition t).val 1) *
            ((motion.positronPosition t).val 1 -
              (motion.electronPosition t).val 1) =
        ((motion.positronPosition t).val 0 -
              (motion.electronPosition t).val 0) ^ 2 +
          ((motion.positronPosition t).val 1 -
              (motion.electronPosition t).val 1) ^ 2
      ring
    have hRadiusDeriv (t : ℝ) :
        HasDerivAt radius (radialDot t / radius t) t := by
      have h :=
        hasDerivAt_of_sq (hRadiusContinuous t) (hRadiusPos t)
          (hRadialSquare t) hRadialSquare_eq
      convert h using 1
      exact (mul_div_mul_left (radialDot t) (radius t)
        (show (2 : ℝ) ≠ 0 from two_ne_zero)).symm
    have hForceCoordinate (t : ℝ) (i : Fin 2) :
        (reducedMass p).val *
            ((motion.positronAcceleration t).val i -
              (motion.electronAcceleration t).val i) =
          forceCoefficient t *
            ((motion.positronPosition t).val i -
              (motion.electronPosition t).val i) := by
      have hforce := hCentralForce t
      change
        (reducedMass p).val •
            ((motion.positronAcceleration t).val -
              (motion.electronAcceleration t).val) =
          (-(coulombStrength p).val /
              ‖(motion.positronPosition t).val -
                (motion.electronPosition t).val‖ ^ 3) •
            ((motion.positronPosition t).val -
              (motion.electronPosition t).val)
        at hforce
      have hi := congrArg (fun v : Plane ↦ v i) hforce
      change
        (reducedMass p).val *
            ((motion.positronAcceleration t).val i -
              (motion.electronAcceleration t).val i) =
          forceCoefficient t *
            ((motion.positronPosition t).val i -
              (motion.electronPosition t).val i) at hi
      exact hi
    have hKineticDeriv (t : ℝ) :
        HasDerivAt kinetic
          ((reducedMass p).val *
            (w0 t * a0 t + w1 t * a1 t)) t := by
      have h0 := hasDerivAt_mul (hw0 t) (hw0 t)
      have h1 := hasDerivAt_mul (hw1 t) (hw1 t)
      have hsum := hasDerivAt_add h0 h1
      have hscaled :=
        hasDerivAt_mul
          (hasDerivAt_const (x := t) ((reducedMass p).val / 2)) hsum
      convert hscaled using 1 <;> (try dsimp only [kinetic]) <;> ring
    have hPotentialDeriv (t : ℝ) :
        HasDerivAt potential (forceCoefficient t * radialDot t) t := by
      have hinv :=
        hasDerivAt_inv_comp (hRadiusDeriv t)
          (ne_of_gt (hRadiusPos t))
      have hscaled :=
        hasDerivAt_mul
          (hasDerivAt_const (x := t) (coulombStrength p).val) hinv
      change
        HasDerivAt potential
          (0 * (radius t)⁻¹ +
            (coulombStrength p).val *
              (-(radius t ^ 2)⁻¹ * (radialDot t / radius t))) t
        at hscaled
      have hderiv :
          0 * (radius t)⁻¹ +
              (coulombStrength p).val *
                (-(radius t ^ 2)⁻¹ * (radialDot t / radius t)) =
            forceCoefficient t * radialDot t := by
        dsimp only [forceCoefficient]
        rw [zero_mul, zero_add]
        repeat' rw [div_eq_mul_inv]
        repeat' rw [inv_pow]
        ring
      rw [hderiv] at hscaled
      exact hscaled
    have hEnergyDerivative (t : ℝ) :
        HasDerivAt (fun u ↦ kinetic u - potential u) 0 t := by
      have hForce0 :
          (reducedMass p).val * a0 t = forceCoefficient t * r0 t := by
        change
          (reducedMass p).val *
              ((motion.positronAcceleration t).val 0 -
                (motion.electronAcceleration t).val 0) =
            forceCoefficient t *
              ((motion.positronPosition t).val 0 -
                (motion.electronPosition t).val 0)
        exact hForceCoordinate t 0
      have hForce1 :
          (reducedMass p).val * a1 t = forceCoefficient t * r1 t := by
        change
          (reducedMass p).val *
              ((motion.positronAcceleration t).val 1 -
                (motion.electronAcceleration t).val 1) =
            forceCoefficient t *
              ((motion.positronPosition t).val 1 -
                (motion.electronPosition t).val 1)
        exact hForceCoordinate t 1
      have hKineticForce :
          (reducedMass p).val *
              (w0 t * a0 t + w1 t * a1 t) =
            forceCoefficient t * radialDot t := by
        dsimp only [radialDot]
        calc
          (reducedMass p).val *
                (w0 t * a0 t + w1 t * a1 t) =
              w0 t * ((reducedMass p).val * a0 t) +
                w1 t * ((reducedMass p).val * a1 t) := by ring
          _ = w0 t * (forceCoefficient t * r0 t) +
                w1 t * (forceCoefficient t * r1 t) := by
              rw [hForce0, hForce1]
          _ = forceCoefficient t *
                (r0 t * w0 t + r1 t * w1 t) := by ring
      have h := hasDerivAt_sub (hKineticDeriv t) (hPotentialDeriv t)
      rw [hKineticForce] at h
      rw [sub_self] at h
      exact h
    have hEnergyFunction (t : ℝ) :
        (relativeEnergyValue p motion t).val = kinetic t - potential t := by
      change
        (reducedMass p).val / 2 *
              ‖(motion.positronVelocity t).val -
                  (motion.electronVelocity t).val‖ ^ 2 -
            (coulombStrength p).val /
              ‖(motion.positronPosition t).val -
                  (motion.electronPosition t).val‖ =
          kinetic t - potential t
      have hnorm :
          ‖(motion.positronVelocity t).val -
              (motion.electronVelocity t).val‖ ^ 2 =
            w0 t * w0 t + w1 t * w1 t := by
        rw [EuclideanSpace.real_norm_sq_eq]
        rw [Fin.sum_univ_two]
        change
          ((motion.positronVelocity t).val 0 -
                (motion.electronVelocity t).val 0) ^ 2 +
              ((motion.positronVelocity t).val 1 -
                (motion.electronVelocity t).val 1) ^ 2 =
            ((motion.positronVelocity t).val 0 -
                  (motion.electronVelocity t).val 0) *
                ((motion.positronVelocity t).val 0 -
                  (motion.electronVelocity t).val 0) +
              ((motion.positronVelocity t).val 1 -
                  (motion.electronVelocity t).val 1) *
                ((motion.positronVelocity t).val 1 -
                  (motion.electronVelocity t).val 1)
        ring
      rw [hnorm]
      dsimp only [kinetic, potential, radius]
      rw [div_eq_mul_inv, div_eq_mul_inv]
    have hRelativeEnergyDerivative (t : ℝ) :
        HasDerivAt
          (fun u ↦ (relativeEnergyValue p motion u).val) 0 t := by
      have hfun :
          (fun u ↦ (relativeEnergyValue p motion u).val) =
            fun u ↦ kinetic u - potential u :=
        funext hEnergyFunction
      rw [hfun]
      exact hEnergyDerivative t
    have hAtInitial :
        (relativeEnergyValue p motion s.initialTime.val).val =
          (initialEnergy p s).val := by
      change
        (reducedMass p).val / 2 *
              ‖(motion.positronVelocity s.initialTime.val).val -
                  (motion.electronVelocity s.initialTime.val).val‖ ^ 2 -
            (coulombStrength p).val /
              ‖(motion.positronPosition s.initialTime.val).val -
                  (motion.electronPosition s.initialTime.val).val‖ =
          (reducedMass p).val / 2 *
              ‖(initialReducedData s).relativeVelocity.val‖ ^ 2 -
            (coulombStrength p).val /
              (initialReducedData s).separation.val
      rw [hAdmissible.2.1.1, hAdmissible.2.1.2.1,
        hAdmissible.2.1.2.2.1, hAdmissible.2.1.2.2.2]
      rfl
    intro t
    exact
      (zeroDerivative_constant hRelativeEnergyDerivative t
        s.initialTime.val).trans hAtInitial
  have hInitialAngularAbs :
      abs (relativeAngularMomentumValue p motion s.initialTime.val).val =
        (initialAngularMomentumMagnitude p s).val := by
    change
      abs
          ((reducedMass p).val *
            crossZ
              ((motion.positronPosition s.initialTime.val).val -
                (motion.electronPosition s.initialTime.val).val)
              ((motion.positronVelocity s.initialTime.val).val -
                (motion.electronVelocity s.initialTime.val).val)) =
        (reducedMass p).val *
          abs
            (crossZ (initialReducedData s).relativePosition.val
              (initialReducedData s).relativeVelocity.val)
    rw [hAdmissible.2.1.1, hAdmissible.2.1.2.1,
      hAdmissible.2.1.2.2.1, hAdmissible.2.1.2.2.2]
    change
      abs
          ((reducedMass p).val *
            crossZ (initialReducedData s).relativePosition.val
              (initialReducedData s).relativeVelocity.val) =
        (reducedMass p).val *
          abs
            (crossZ (initialReducedData s).relativePosition.val
              (initialReducedData s).relativeVelocity.val)
    rw [abs_mul, abs_of_pos hreducedMass]
  intro t
  have hCenter := centerOfMass_eq_initial p s motion hAdmissible t
  dsimp only at hCenter ⊢
  have hAngularAbs :
      abs (relativeAngularMomentumValue p motion t).val =
        (initialAngularMomentumMagnitude p s).val := by
    rw [hAngularConserved t]
    exact hInitialAngularAbs
  have hElectronVelocity :
      (motion.electronVelocity t).val = -(motion.positronVelocity t).val := by
    have hneg := congrArg Neg.neg hCenter.2.1
    rw [neg_neg] at hneg
    exact hneg.symm
  have hPosCenter := hCenter.2.2.1
  change
    (motion.positronPosition t).val -
        (initialReducedData s).centerPosition.val =
      (1 / 2 : ℝ) •
        ((motion.positronPosition t).val -
          (motion.electronPosition t).val) at hPosCenter
  have hElectronCenter := hCenter.2.2.2
  change
    (motion.electronPosition t).val -
        (initialReducedData s).centerPosition.val =
      (-1 / 2 : ℝ) •
        ((motion.positronPosition t).val -
          (motion.electronPosition t).val) at hElectronCenter
  have hParticleSigned :
      (particleAngularMomentumValue p (motion.positronPosition t)
            (motion.positronVelocity t) (initialReducedData s).centerPosition).val +
          (particleAngularMomentumValue p (motion.electronPosition t)
            (motion.electronVelocity t) (initialReducedData s).centerPosition).val =
        (relativeAngularMomentumValue p motion t).val := by
    change
      p.mass.val *
            crossZ
              ((motion.positronPosition t).val -
                (initialReducedData s).centerPosition.val)
              (motion.positronVelocity t).val +
          p.mass.val *
            crossZ
              ((motion.electronPosition t).val -
                (initialReducedData s).centerPosition.val)
              (motion.electronVelocity t).val =
        (p.mass.val / 2) *
          crossZ
            ((motion.positronPosition t).val - (motion.electronPosition t).val)
            ((motion.positronVelocity t).val - (motion.electronVelocity t).val)
    rw [hPosCenter, hElectronCenter, hElectronVelocity]
    unfold crossZ
    change
      p.mass.val *
            ((1 / 2 : ℝ) *
                ((motion.positronPosition t).val 0 -
                  (motion.electronPosition t).val 0) *
                (motion.positronVelocity t).val 1 -
              (1 / 2 : ℝ) *
                ((motion.positronPosition t).val 1 -
                  (motion.electronPosition t).val 1) *
                (motion.positronVelocity t).val 0) +
          p.mass.val *
            ((-1 / 2 : ℝ) *
                ((motion.positronPosition t).val 0 -
                  (motion.electronPosition t).val 0) *
                (-(motion.positronVelocity t).val 1) -
              (-1 / 2 : ℝ) *
                ((motion.positronPosition t).val 1 -
                  (motion.electronPosition t).val 1) *
                (-(motion.positronVelocity t).val 0)) =
        (p.mass.val / 2) *
          (((motion.positronPosition t).val 0 -
                (motion.electronPosition t).val 0) *
              ((motion.positronVelocity t).val 1 -
                (-(motion.positronVelocity t).val 1)) -
            ((motion.positronPosition t).val 1 -
                (motion.electronPosition t).val 1) *
              ((motion.positronVelocity t).val 0 -
                (-(motion.positronVelocity t).val 0)))
    ring
  have hTotalEnergy :
      p.mass.val / 2 *
            (‖(motion.positronVelocity t).val‖ ^ 2 +
              ‖(motion.electronVelocity t).val‖ ^ 2) -
          (coulombStrength p).val / (motionObservables motion t).separation.val =
        (initialEnergy p s).val := by
    have hRelativeEnergy := hEnergyConserved t
    change
      (p.mass.val / 2) / 2 *
            ‖(motion.positronVelocity t).val -
                (motion.electronVelocity t).val‖ ^ 2 -
          (coulombStrength p).val / (motionObservables motion t).separation.val =
        (initialEnergy p s).val at hRelativeEnergy
    rw [hElectronVelocity] at hRelativeEnergy ⊢
    have hnorm :
        ‖(motion.positronVelocity t).val - -(motion.positronVelocity t).val‖ =
          2 * ‖(motion.positronVelocity t).val‖ := by
      rw [sub_neg_eq_add, ← two_smul ℝ, norm_smul]
      rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
    rw [hnorm] at hRelativeEnergy
    rw [norm_neg]
    convert hRelativeEnergy using 1 <;> ring
  exact
    ⟨hAngularConserved t, hAngularAbs, hEnergyConserved t,
      hParticleSigned ▸ hAngularAbs, hTotalEnergy⟩

/-- The conserved energy split into radial kinetic, angular, and potential terms. -/
lemma effective_radial_energy
    (p : Parameters) (s : InitialState) (motion : PairMotion)
    (hAdmissible : IsAdmissibleBoundOrbit p s motion) :
    ∀ t : ℝ,
      let o := motionObservables motion t
      (initialEnergy p s).val =
        (reducedMass p).val / 2 *
            (dot o.relativePosition.val o.relativeVelocity.val / o.separation.val) ^ 2 +
          (initialAngularMomentumMagnitude p s).val ^ 2 /
            (2 * (reducedMass p).val * o.separation.val ^ 2) -
          (coulombStrength p).val / o.separation.val := by
  have hmass : 0 < (reducedMass p).val := by
    change 0 < p.mass.val / 2
    exact half_pos hAdmissible.1.1.1
  intro t
  have hInvariants := relative_invariants_conserved p s motion hAdmissible t
  have hNewton := hAdmissible.2.2.2.1 t
  dsimp only at hInvariants hNewton ⊢
  have hsep :
      0 < ‖(motion.positronPosition t).val - (motion.electronPosition t).val‖ :=
    hNewton.1
  let r : Plane :=
    (motion.positronPosition t).val - (motion.electronPosition t).val
  let w : Plane :=
    (motion.positronVelocity t).val - (motion.electronVelocity t).val
  have hLagrange : ‖r‖ ^ 2 * ‖w‖ ^ 2 = dot r w ^ 2 + crossZ r w ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    unfold dot crossZ
    repeat' rw [Fin.sum_univ_two]
    ring
  have hAngularAbs :
      abs ((reducedMass p).val * crossZ r w) =
        (initialAngularMomentumMagnitude p s).val := by
    exact hInvariants.2.1
  have hAngularSq :
      ((reducedMass p).val * crossZ r w) ^ 2 =
        (initialAngularMomentumMagnitude p s).val ^ 2 := by
    calc
      ((reducedMass p).val * crossZ r w) ^ 2 =
          abs ((reducedMass p).val * crossZ r w) ^ 2 := by rw [sq_abs]
      _ = (initialAngularMomentumMagnitude p s).val ^ 2 :=
        congrArg (fun x : ℝ ↦ x ^ 2) hAngularAbs
  have hEnergy :
      (reducedMass p).val / 2 * ‖w‖ ^ 2 -
          (coulombStrength p).val / ‖r‖ =
        (initialEnergy p s).val := by
    exact hInvariants.2.2.1
  have hr_ne : ‖r‖ ≠ 0 := ne_of_gt hsep
  have hr_sq_ne : ‖r‖ ^ 2 ≠ 0 := pow_ne_zero 2 hr_ne
  have hNormDecomp :
      ‖w‖ ^ 2 = dot r w ^ 2 / ‖r‖ ^ 2 + crossZ r w ^ 2 / ‖r‖ ^ 2 := by
    calc
      ‖w‖ ^ 2 = ‖r‖ ^ 2 * ‖w‖ ^ 2 / ‖r‖ ^ 2 :=
        (mul_div_cancel_left₀ _ hr_sq_ne).symm
      _ = (dot r w ^ 2 + crossZ r w ^ 2) / ‖r‖ ^ 2 := by rw [hLagrange]
      _ = dot r w ^ 2 / ‖r‖ ^ 2 + crossZ r w ^ 2 / ‖r‖ ^ 2 :=
        add_div _ _ _
  change
    (initialEnergy p s).val =
      (reducedMass p).val / 2 * (dot r w / ‖r‖) ^ 2 +
          (initialAngularMomentumMagnitude p s).val ^ 2 /
            (2 * (reducedMass p).val * ‖r‖ ^ 2) -
        (coulombStrength p).val / ‖r‖
  rw [← hEnergy]
  rw [hNormDecomp, ← hAngularSq]
  have hdot :
      (dot r w / ‖r‖) ^ 2 = dot r w ^ 2 / ‖r‖ ^ 2 :=
    div_pow (dot r w) ‖r‖ 2
  have hm_ne : (reducedMass p).val ≠ 0 := ne_of_gt hmass
  have hcross :
      ((reducedMass p).val * crossZ r w) ^ 2 /
            (2 * (reducedMass p).val * ‖r‖ ^ 2) =
          (reducedMass p).val / 2 * (crossZ r w ^ 2 / ‖r‖ ^ 2) := by
    rw [mul_pow]
    calc
      ((reducedMass p).val ^ 2 * crossZ r w ^ 2) /
            (2 * (reducedMass p).val * ‖r‖ ^ 2) =
          ((reducedMass p).val *
              ((reducedMass p).val * crossZ r w ^ 2)) /
            ((reducedMass p).val * (2 * ‖r‖ ^ 2)) := by
              congr 1 <;> ring
      _ = ((reducedMass p).val * crossZ r w ^ 2) /
            (2 * ‖r‖ ^ 2) :=
        mul_div_mul_left _ _ hm_ne
      _ = (reducedMass p).val / 2 * (crossZ r w ^ 2 / ‖r‖ ^ 2) :=
        mul_div_mul_comm _ _ _ _
  rw [hdot, hcross]
  ring

/-- Dynamical radial turning is equivalent to the source polynomial vanishing at the
dimensionless instantaneous radius. -/
lemma turningTime_iff_positiveTurningPoint
    (p : Parameters) (s : InitialState) (motion : PairMotion)
    (hAdmissible : IsAdmissibleBoundOrbit p s motion) (t : ℝ) :
    IsRadialTurningTime motion t ↔
      IsPositiveTurningPointInBohrRadii p s
        ((motionObservables motion t).separation.val / p.bohrRadius.val) := by
  have hEffective := effective_radial_energy p s motion hAdmissible t
  have hsep := (hAdmissible.2.2.2.1 t).1
  have ha : 0 < p.bohrRadius.val := hAdmissible.1.1.2.2.2.2.1
  have hmass : 0 < (reducedMass p).val := by
    change 0 < p.mass.val / 2
    exact half_pos hAdmissible.1.1.1
  let o := motionObservables motion t
  have hscale : p.bohrRadius.val * (o.separation.val / p.bohrRadius.val) =
      o.separation.val := by
    calc
      p.bohrRadius.val * (o.separation.val / p.bohrRadius.val) =
          o.separation.val * p.bohrRadius.val / p.bohrRadius.val := by ring
      _ = o.separation.val :=
        mul_div_cancel_right₀ _ (ne_of_gt ha)
  have hPolynomial :
      (radialTurningPolynomial p s (o.separation.val / p.bohrRadius.val)).val =
        (reducedMass p).val / 2 *
          dot o.relativePosition.val o.relativeVelocity.val ^ 2 := by
    change
      (initialEnergy p s).val *
            (p.bohrRadius.val * (o.separation.val / p.bohrRadius.val)) ^ 2 +
          (coulombStrength p).val *
            (p.bohrRadius.val * (o.separation.val / p.bohrRadius.val)) -
        (initialAngularMomentumMagnitude p s).val ^ 2 /
          (2 * (reducedMass p).val) =
        (reducedMass p).val / 2 *
          dot o.relativePosition.val o.relativeVelocity.val ^ 2
    have hr_ne : o.separation.val ≠ 0 := ne_of_gt hsep
    have hr_sq_ne : o.separation.val ^ 2 ≠ 0 := pow_ne_zero 2 hr_ne
    have hradial :
        (dot o.relativePosition.val o.relativeVelocity.val /
              o.separation.val) ^ 2 * o.separation.val ^ 2 =
            dot o.relativePosition.val o.relativeVelocity.val ^ 2 := by
      rw [div_pow, div_mul_cancel₀ _ hr_sq_ne]
    have hangular :
        (initialAngularMomentumMagnitude p s).val ^ 2 /
              (2 * (reducedMass p).val * o.separation.val ^ 2) *
            o.separation.val ^ 2 =
          (initialAngularMomentumMagnitude p s).val ^ 2 /
            (2 * (reducedMass p).val) := by
      rw [div_mul_eq_mul_div]
      exact mul_div_mul_right _ _ hr_sq_ne
    have hpotential :
        (coulombStrength p).val / o.separation.val * o.separation.val ^ 2 =
          (coulombStrength p).val * o.separation.val := by
      calc
        (coulombStrength p).val / o.separation.val * o.separation.val ^ 2 =
            ((coulombStrength p).val / o.separation.val * o.separation.val) *
              o.separation.val := by ring
        _ = (coulombStrength p).val * o.separation.val := by
          rw [div_mul_cancel₀ _ hr_ne]
    rw [hscale, hEffective]
    calc
      ((reducedMass p).val / 2 *
              (dot o.relativePosition.val o.relativeVelocity.val /
                o.separation.val) ^ 2 +
            (initialAngularMomentumMagnitude p s).val ^ 2 /
              (2 * (reducedMass p).val * o.separation.val ^ 2) -
            (coulombStrength p).val / o.separation.val) * o.separation.val ^ 2 +
          (coulombStrength p).val * o.separation.val -
          (initialAngularMomentumMagnitude p s).val ^ 2 /
            (2 * (reducedMass p).val) =
        (reducedMass p).val / 2 *
              ((dot o.relativePosition.val o.relativeVelocity.val /
                o.separation.val) ^ 2 * o.separation.val ^ 2) +
            ((initialAngularMomentumMagnitude p s).val ^ 2 /
                (2 * (reducedMass p).val * o.separation.val ^ 2) *
              o.separation.val ^ 2) -
            ((coulombStrength p).val / o.separation.val *
              o.separation.val ^ 2) +
          (coulombStrength p).val * o.separation.val -
          (initialAngularMomentumMagnitude p s).val ^ 2 /
            (2 * (reducedMass p).val) := by ring
      _ = (reducedMass p).val / 2 *
          dot o.relativePosition.val o.relativeVelocity.val ^ 2 := by
        rw [hradial, hangular, hpotential]
        ring
  constructor
  · intro hTurning
    refine ⟨div_pos hsep ha, ?_⟩
    rw [hPolynomial]
    change dot o.relativePosition.val o.relativeVelocity.val = 0 at hTurning
    rw [hTurning]
    ring
  · intro hRoot
    change dot o.relativePosition.val o.relativeVelocity.val = 0
    have hzero := hRoot.2
    rw [hPolynomial] at hzero
    have hsquare : dot o.relativePosition.val o.relativeVelocity.val ^ 2 = 0 :=
      (mul_eq_zero.mp hzero).resolve_left (by positivity)
    exact sq_eq_zero_iff.mp hsquare

/-- Energy conservation confines every instantaneous separation between the two roots. -/
lemma separation_between_orderedTurningPoints
    (p : Parameters) (s : InitialState) (motion : PairMotion)
    (hAdmissible : IsAdmissibleBoundOrbit p s motion)
    {xMinus xPlus : ℝ}
    (hRoots : AreOrderedPositiveTurningPoints p s xMinus xPlus) :
    ∀ t : ℝ,
      xMinus * p.bohrRadius.val ≤ (motionObservables motion t).separation.val ∧
      (motionObservables motion t).separation.val ≤ xPlus * p.bohrRadius.val := by
  rcases hRoots with ⟨hxMinusPos, hrootOrder, hrootMinus, hrootPlus, hrootClass⟩
  have ha : 0 < p.bohrRadius.val := hAdmissible.1.1.2.2.2.2.1
  have henergyNeg : (initialEnergy p s).val < 0 := hAdmissible.1.2.2
  have hmass : 0 < (reducedMass p).val := by
    change 0 < p.mass.val / 2
    exact half_pos hAdmissible.1.1.1
  let A : ℝ := (initialEnergy p s).val * p.bohrRadius.val ^ 2
  let B : ℝ := (coulombStrength p).val * p.bohrRadius.val
  let C : ℝ :=
    -(initialAngularMomentumMagnitude p s).val ^ 2 / (2 * (reducedMass p).val)
  have hPolynomialForm (x : ℝ) :
      (radialTurningPolynomial p s x).val = A * x ^ 2 + B * x + C := by
    dsimp [radialTurningPolynomial, A, B, C]
    ring
  have hminusZero : A * xMinus ^ 2 + B * xMinus + C = 0 := by
    rw [← hPolynomialForm]
    exact hrootMinus.2
  have hplusZero : A * xPlus ^ 2 + B * xPlus + C = 0 := by
    rw [← hPolynomialForm]
    exact hrootPlus.2
  have hfactorDifference :
      (xPlus - xMinus) * (A * (xPlus + xMinus) + B) = 0 := by
    calc
      (xPlus - xMinus) * (A * (xPlus + xMinus) + B) =
          (A * xPlus ^ 2 + B * xPlus + C) -
            (A * xMinus ^ 2 + B * xMinus + C) := by ring
      _ = 0 := by rw [hplusZero, hminusZero]; ring
  have hsumCoefficient : A * (xPlus + xMinus) + B = 0 :=
    (mul_eq_zero.mp hfactorDifference).resolve_left (sub_ne_zero.mpr hrootOrder.ne')
  have hB : B = -A * (xPlus + xMinus) := by linarith
  have hC : C = A * xMinus * xPlus := by
    calc
      C = -(A * xMinus ^ 2 + B * xMinus) := by linarith
      _ = A * xMinus * xPlus := by rw [hB]; ring
  have hFactorization (x : ℝ) :
      (radialTurningPolynomial p s x).val =
        A * (x - xMinus) * (x - xPlus) := by
    rw [hPolynomialForm, hB, hC]
    ring
  have hAneg : A < 0 := by
    dsimp only [A]
    exact mul_neg_of_neg_of_pos henergyNeg (sq_pos_of_pos ha)
  intro t
  let o := motionObservables motion t
  let x := o.separation.val / p.bohrRadius.val
  have hsep : 0 < o.separation.val := (hAdmissible.2.2.2.1 t).1
  have hEffective := effective_radial_energy p s motion hAdmissible t
  change
    (initialEnergy p s).val =
      (reducedMass p).val / 2 *
          (dot o.relativePosition.val o.relativeVelocity.val / o.separation.val) ^ 2 +
        (initialAngularMomentumMagnitude p s).val ^ 2 /
          (2 * (reducedMass p).val * o.separation.val ^ 2) -
        (coulombStrength p).val / o.separation.val at hEffective
  have hscale : p.bohrRadius.val * x = o.separation.val := by
    dsimp only [x]
    calc
      p.bohrRadius.val * (o.separation.val / p.bohrRadius.val) =
          o.separation.val * p.bohrRadius.val / p.bohrRadius.val := by ring
      _ = o.separation.val :=
        mul_div_cancel_right₀ _ (ne_of_gt ha)
  have hCurrentPolynomial :
      (radialTurningPolynomial p s x).val =
        (reducedMass p).val / 2 *
          dot o.relativePosition.val o.relativeVelocity.val ^ 2 := by
    change
      (initialEnergy p s).val * (p.bohrRadius.val * x) ^ 2 +
            (coulombStrength p).val * (p.bohrRadius.val * x) -
          (initialAngularMomentumMagnitude p s).val ^ 2 /
            (2 * (reducedMass p).val) =
        (reducedMass p).val / 2 *
          dot o.relativePosition.val o.relativeVelocity.val ^ 2
    have hr_ne : o.separation.val ≠ 0 := ne_of_gt hsep
    have hr_sq_ne : o.separation.val ^ 2 ≠ 0 := pow_ne_zero 2 hr_ne
    have hradial :
        (dot o.relativePosition.val o.relativeVelocity.val /
              o.separation.val) ^ 2 * o.separation.val ^ 2 =
            dot o.relativePosition.val o.relativeVelocity.val ^ 2 := by
      rw [div_pow, div_mul_cancel₀ _ hr_sq_ne]
    have hangular :
        (initialAngularMomentumMagnitude p s).val ^ 2 /
              (2 * (reducedMass p).val * o.separation.val ^ 2) *
            o.separation.val ^ 2 =
          (initialAngularMomentumMagnitude p s).val ^ 2 /
            (2 * (reducedMass p).val) := by
      rw [div_mul_eq_mul_div]
      exact mul_div_mul_right _ _ hr_sq_ne
    have hpotential :
        (coulombStrength p).val / o.separation.val * o.separation.val ^ 2 =
          (coulombStrength p).val * o.separation.val := by
      calc
        (coulombStrength p).val / o.separation.val * o.separation.val ^ 2 =
            ((coulombStrength p).val / o.separation.val * o.separation.val) *
              o.separation.val := by ring
        _ = (coulombStrength p).val * o.separation.val := by
          rw [div_mul_cancel₀ _ hr_ne]
    rw [hscale, hEffective]
    calc
      ((reducedMass p).val / 2 *
              (dot o.relativePosition.val o.relativeVelocity.val /
                o.separation.val) ^ 2 +
            (initialAngularMomentumMagnitude p s).val ^ 2 /
              (2 * (reducedMass p).val * o.separation.val ^ 2) -
            (coulombStrength p).val / o.separation.val) * o.separation.val ^ 2 +
          (coulombStrength p).val * o.separation.val -
          (initialAngularMomentumMagnitude p s).val ^ 2 /
            (2 * (reducedMass p).val) =
        (reducedMass p).val / 2 *
              ((dot o.relativePosition.val o.relativeVelocity.val /
                o.separation.val) ^ 2 * o.separation.val ^ 2) +
            ((initialAngularMomentumMagnitude p s).val ^ 2 /
                (2 * (reducedMass p).val * o.separation.val ^ 2) *
              o.separation.val ^ 2) -
            ((coulombStrength p).val / o.separation.val *
              o.separation.val ^ 2) +
          (coulombStrength p).val * o.separation.val -
          (initialAngularMomentumMagnitude p s).val ^ 2 /
            (2 * (reducedMass p).val) := by ring
      _ = (reducedMass p).val / 2 *
          dot o.relativePosition.val o.relativeVelocity.val ^ 2 := by
        rw [hradial, hangular, hpotential]
        ring
  have hPolynomialNonneg : 0 ≤ (radialTurningPolynomial p s x).val := by
    rw [hCurrentPolynomial]
    positivity
  have hxLower : xMinus ≤ x := by
    by_contra h
    have hxm : x - xMinus < 0 := sub_neg.mpr (lt_of_not_ge h)
    have hxp : x - xPlus < 0 := by linarith
    have hprod : 0 < (x - xMinus) * (x - xPlus) := mul_pos_of_neg_of_neg hxm hxp
    rw [hFactorization] at hPolynomialNonneg
    have hnegative : A * (x - xMinus) * (x - xPlus) < 0 := by
      rw [mul_assoc]
      exact mul_neg_of_neg_of_pos hAneg hprod
    exact (not_lt_of_ge hPolynomialNonneg) hnegative
  have hxUpper : x ≤ xPlus := by
    by_contra h
    have hxp : 0 < x - xPlus := sub_pos.mpr (lt_of_not_ge h)
    have hxm : 0 < x - xMinus := by linarith
    have hprod : 0 < (x - xMinus) * (x - xPlus) := mul_pos hxm hxp
    rw [hFactorization] at hPolynomialNonneg
    have hnegative : A * (x - xMinus) * (x - xPlus) < 0 := by
      rw [mul_assoc]
      exact mul_neg_of_neg_of_pos hAneg hprod
    exact (not_lt_of_ge hPolynomialNonneg) hnegative
  exact ⟨(le_div_iff₀ ha).mp hxLower, (div_le_iff₀ ha).mp hxUpper⟩

/-- The source time realizes the smaller radial turning point. -/
lemma initialTime_is_smallerTurningPoint
    (p : Parameters) (s : InitialState) (motion : PairMotion)
    (hAdmissible : IsAdmissibleBoundOrbit p s motion)
    {xMinus xPlus : ℝ}
    (hRoots : AreOrderedPositiveTurningPoints p s xMinus xPlus) :
    IsRadialTurningTime motion s.initialTime.val ∧
      (motionObservables motion s.initialTime.val).separation.val =
        xMinus * p.bohrRadius.val := by
  rcases hAdmissible with ⟨hSetup, hExtends, hKinematics, hNewton, hConic⟩
  have hRadius := initialRadius_eq_smallerTurningPoint p s hSetup hRoots
  rcases hSetup with ⟨hPhysical, hSource, hBound⟩
  dsimp only [HasSourceInitialConditions] at hSource
  rcases hSource with
    ⟨hμ, hR, hanti, hperpPos, hperpElec, hangularPos, hangularElec⟩
  constructor
  · change
      dot
        ((motion.positronPosition s.initialTime.val).val -
          (motion.electronPosition s.initialTime.val).val)
        ((motion.positronVelocity s.initialTime.val).val -
          (motion.electronVelocity s.initialTime.val).val) = 0
    rw [hExtends.1, hExtends.2.1, hExtends.2.2.1, hExtends.2.2.2]
    change
      dot (initialReducedData s).relativePosition.val
          (s.positronVelocity.val - s.electronVelocity.val) = 0
    unfold dot at hperpPos hperpElec ⊢
    rw [Fin.sum_univ_two] at hperpPos hperpElec ⊢
    change
      (initialReducedData s).relativePosition.val.ofLp 0 *
            (s.positronVelocity.val.ofLp 0 - s.electronVelocity.val.ofLp 0) +
          (initialReducedData s).relativePosition.val.ofLp 1 *
            (s.positronVelocity.val.ofLp 1 - s.electronVelocity.val.ofLp 1) =
        0
    linarith
  · change
      ‖(motion.positronPosition s.initialTime.val).val -
          (motion.electronPosition s.initialTime.val).val‖ =
        xMinus * p.bohrRadius.val
    rw [hExtends.1, hExtends.2.1]
    change
      ‖s.positronPosition.val - s.electronPosition.val‖ =
        xMinus * p.bohrRadius.val at hRadius
    exact hRadius

/-- Elementary cosine bounds make the conic denominator positive and bound its radius. -/
lemma sourceConic_denominator_pos_and_radial_bounds
    (p : Parameters) (s : InitialState) (motion : PairMotion)
    (scale : LengthQuantity) (eccentricity : ℝ) (period : TimeQuantity)
    (orientation phaseOffset : ℝ) (phase : ℝ → ℝ)
    (hConic : SourceBoundConicGoverningRelations p s motion scale eccentricity period
      orientation phaseOffset phase) :
    ∀ t : ℝ,
      0 < 1 - eccentricity * Real.cos (phase t) ∧
      0 < scale.val / (1 + eccentricity) ∧
      scale.val / (1 + eccentricity) ≤
          (motionObservables motion t).separation.val ∧
      (motionObservables motion t).separation.val ≤
        scale.val / (1 - eccentricity) := by
  rcases hConic with
    ⟨hscale, hperiod, heccentricity, heccentricity_lt, horientation,
      hcontinuous, heccentricity_formula, hrelations⟩
  intro t
  have hrelation := hrelations t
  dsimp only at hrelation
  have hcos_le :
      eccentricity * Real.cos (phase t) ≤ eccentricity :=
    by
      calc
        eccentricity * Real.cos (phase t) ≤ eccentricity * 1 :=
          mul_le_mul_of_nonneg_left (Real.cos_le_one (phase t)) heccentricity.le
        _ = eccentricity := by ring
  have hneg_le_cos :
      -eccentricity ≤ eccentricity * Real.cos (phase t) := by
    have h := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (phase t))
      heccentricity.le
    nlinarith
  have hden_lower :
      1 - eccentricity ≤ 1 - eccentricity * Real.cos (phase t) := by
    linarith
  have hden_upper :
      1 - eccentricity * Real.cos (phase t) ≤ 1 + eccentricity := by
    linarith
  have hden_pos : 0 < 1 - eccentricity * Real.cos (phase t) := by
    linarith
  have hone_add_pos : 0 < 1 + eccentricity := by linarith
  have hone_sub_pos : 0 < 1 - eccentricity := by linarith
  refine ⟨hden_pos, by positivity, ?_, ?_⟩
  · rw [hrelation.2.1]
    exact div_le_div_of_nonneg_left hscale.le hden_pos hden_upper
  · rw [hrelation.2.1]
    exact div_le_div_of_nonneg_left hscale.le hone_sub_pos hden_lower

/-- A continuous phase which changes by one signed turn attains both conic apsides during
every period. -/
lemma sourceConic_fullTraversal_attains_apsides
    (p : Parameters) (s : InitialState) (motion : PairMotion)
    (scale : LengthQuantity) (eccentricity : ℝ) (period : TimeQuantity)
    (orientation phaseOffset : ℝ) (phase : ℝ → ℝ)
    (hConic : SourceBoundConicGoverningRelations p s motion scale eccentricity period
      orientation phaseOffset phase) :
    ∀ u : ℝ,
      ∃ tMinus tPlus : ℝ,
        tMinus ∈ Set.Icc u (u + period.val) ∧
        tPlus ∈ Set.Icc u (u + period.val) ∧
        Real.cos (phase tMinus) = -1 ∧
        (motionObservables motion tMinus).separation.val =
          scale.val / (1 + eccentricity) ∧
        Real.cos (phase tPlus) = 1 ∧
        (motionObservables motion tPlus).separation.val =
          scale.val / (1 - eccentricity) ∧
        scale.val / (1 + eccentricity) < scale.val / (1 - eccentricity) := by
  rcases hConic with
    ⟨hscale, hperiod, heccentricity, heccentricity_lt, horientation,
      hcontinuous, heccentricity_formula, hrelations⟩
  have htwoPi : 0 < 2 * Real.pi := by positivity
  have phaseInterval_contains_apsides (a : ℝ) :
      ∃ yMinus yPlus : ℝ,
        yMinus ∈ Set.Icc a (a + 2 * Real.pi) ∧
        yPlus ∈ Set.Icc a (a + 2 * Real.pi) ∧
        Real.cos yMinus = -1 ∧ Real.cos yPlus = 1 := by
    let nPlus : ℤ := ⌈a / (2 * Real.pi)⌉
    let nMinus : ℤ := ⌈(a - Real.pi) / (2 * Real.pi)⌉
    have hnPlus_lower : a ≤ (nPlus : ℝ) * (2 * Real.pi) := by
      apply (div_le_iff₀ htwoPi).mp
      change a / (2 * Real.pi) ≤ (nPlus : ℝ)
      dsimp only [nPlus]
      exact Int.le_ceil (a / (2 * Real.pi))
    have hnPlus_upper : (nPlus : ℝ) * (2 * Real.pi) < a + 2 * Real.pi := by
      calc
        (nPlus : ℝ) * (2 * Real.pi) <
            (a / (2 * Real.pi) + 1) * (2 * Real.pi) :=
          mul_lt_mul_of_pos_right (by
            change (nPlus : ℝ) < a / (2 * Real.pi) + 1
            dsimp only [nPlus]
            exact Int.ceil_lt_add_one (a / (2 * Real.pi))) htwoPi
        _ = a + 2 * Real.pi := by
          rw [add_mul, div_mul_cancel₀ a (ne_of_gt htwoPi)]
          ring
    have hnMinus_base_lower :
        a - Real.pi ≤ (nMinus : ℝ) * (2 * Real.pi) := by
      apply (div_le_iff₀ htwoPi).mp
      change (a - Real.pi) / (2 * Real.pi) ≤ (nMinus : ℝ)
      dsimp only [nMinus]
      exact Int.le_ceil ((a - Real.pi) / (2 * Real.pi))
    have hnMinus_base_upper :
        (nMinus : ℝ) * (2 * Real.pi) < a - Real.pi + 2 * Real.pi := by
      calc
        (nMinus : ℝ) * (2 * Real.pi) <
            ((a - Real.pi) / (2 * Real.pi) + 1) * (2 * Real.pi) :=
          mul_lt_mul_of_pos_right (by
            change (nMinus : ℝ) < (a - Real.pi) / (2 * Real.pi) + 1
            dsimp only [nMinus]
            exact Int.ceil_lt_add_one ((a - Real.pi) / (2 * Real.pi))) htwoPi
        _ = a - Real.pi + 2 * Real.pi := by
          rw [add_mul,
            div_mul_cancel₀ (a - Real.pi) (ne_of_gt htwoPi)]
          ring
    refine
      ⟨(nMinus : ℝ) * (2 * Real.pi) + Real.pi,
        (nPlus : ℝ) * (2 * Real.pi), ?_, ?_, ?_, ?_⟩
    · constructor <;> linarith
    · exact ⟨hnPlus_lower, hnPlus_upper.le⟩
    · exact Real.cos_int_mul_two_pi_add_pi nMinus
    · exact Real.cos_int_mul_two_pi nPlus
  have buildConclusion
      (u tMinus tPlus : ℝ)
      (htMinus : tMinus ∈ Set.Icc u (u + period.val))
      (htPlus : tPlus ∈ Set.Icc u (u + period.val))
      (hcosMinus : Real.cos (phase tMinus) = -1)
      (hcosPlus : Real.cos (phase tPlus) = 1) :
      ∃ tMinus tPlus : ℝ,
        tMinus ∈ Set.Icc u (u + period.val) ∧
        tPlus ∈ Set.Icc u (u + period.val) ∧
        Real.cos (phase tMinus) = -1 ∧
        (motionObservables motion tMinus).separation.val =
          scale.val / (1 + eccentricity) ∧
        Real.cos (phase tPlus) = 1 ∧
        (motionObservables motion tPlus).separation.val =
          scale.val / (1 - eccentricity) ∧
        scale.val / (1 + eccentricity) < scale.val / (1 - eccentricity) := by
    have hminusRelation := (hrelations tMinus).2.1
    have hplusRelation := (hrelations tPlus).2.1
    have hsepMinus :
        (motionObservables motion tMinus).separation.val =
          scale.val / (1 + eccentricity) := by
      rw [hcosMinus] at hminusRelation
      rw [show 1 - eccentricity * (-1) = 1 + eccentricity by ring]
        at hminusRelation
      exact hminusRelation
    have hsepPlus :
        (motionObservables motion tPlus).separation.val =
          scale.val / (1 - eccentricity) := by
      rw [hcosPlus] at hplusRelation
      rw [show 1 - eccentricity * 1 = 1 - eccentricity by ring]
        at hplusRelation
      exact hplusRelation
    have hone_sub_pos : 0 < 1 - eccentricity := by linarith
    have hstrict :
        scale.val / (1 + eccentricity) < scale.val / (1 - eccentricity) := by
      apply div_lt_div_of_pos_left hscale hone_sub_pos
      linarith
    exact
      ⟨tMinus, tPlus, htMinus, htPlus, hcosMinus, hsepMinus,
        hcosPlus, hsepPlus, hstrict⟩
  intro u
  have huPeriod : u ≤ u + period.val := by linarith
  rcases horientation with horientation | horientation
  · have hend := (hrelations u).2.2
    have hend' :
        phase (u + period.val) = phase u - 2 * Real.pi := by
      calc
        phase (u + period.val) = phase u + 2 * Real.pi * orientation := hend
        _ = phase u - 2 * Real.pi := by rw [horientation]; ring
    rcases phaseInterval_contains_apsides (phase u - 2 * Real.pi) with
      ⟨yMinus, yPlus, hyMinus, hyPlus, hcosMinus, hcosPlus⟩
    have hyMinus' : yMinus ∈ Set.Icc (phase (u + period.val)) (phase u) := by
      rw [hend']
      exact ⟨hyMinus.1, by linarith [hyMinus.2]⟩
    have hyPlus' : yPlus ∈ Set.Icc (phase (u + period.val)) (phase u) := by
      rw [hend']
      exact ⟨hyPlus.1, by linarith [hyPlus.2]⟩
    rcases intermediate_value_Icc' huPeriod hcontinuous.continuousOn hyMinus' with
      ⟨tMinus, htMinus, hphaseMinus⟩
    rcases intermediate_value_Icc' huPeriod hcontinuous.continuousOn hyPlus' with
      ⟨tPlus, htPlus, hphasePlus⟩
    apply buildConclusion u tMinus tPlus htMinus htPlus
    · rw [hphaseMinus]
      exact hcosMinus
    · rw [hphasePlus]
      exact hcosPlus
  · have hend := (hrelations u).2.2
    have hend' :
        phase (u + period.val) = phase u + 2 * Real.pi := by
      calc
        phase (u + period.val) = phase u + 2 * Real.pi * orientation := hend
        _ = phase u + 2 * Real.pi := by rw [horientation]; ring
    rcases phaseInterval_contains_apsides (phase u) with
      ⟨yMinus, yPlus, hyMinus, hyPlus, hcosMinus, hcosPlus⟩
    have hyMinus' : yMinus ∈ Set.Icc (phase u) (phase (u + period.val)) := by
      rw [hend']
      exact hyMinus
    have hyPlus' : yPlus ∈ Set.Icc (phase u) (phase (u + period.val)) := by
      rw [hend']
      exact hyPlus
    rcases intermediate_value_Icc huPeriod hcontinuous.continuousOn hyMinus' with
      ⟨tMinus, htMinus, hphaseMinus⟩
    rcases intermediate_value_Icc huPeriod hcontinuous.continuousOn hyPlus' with
      ⟨tPlus, htPlus, hphasePlus⟩
    apply buildConclusion u tMinus tPlus htMinus htPlus
    · rw [hphaseMinus]
      exact hcosMinus
    · rw [hphasePlus]
      exact hcosPlus

/-- The printed eccentricity formula gives the ratio of the two conservation roots. -/
lemma sourceConic_eccentricity_eq_turningRootRatio
    (p : Parameters) (s : InitialState) (motion : PairMotion)
    (hSetup : SourceProblemSetup p s)
    {xMinus xPlus : ℝ}
    (hRoots : AreOrderedPositiveTurningPoints p s xMinus xPlus)
    (scale : LengthQuantity) (eccentricity : ℝ) (period : TimeQuantity)
    (orientation phaseOffset : ℝ) (phase : ℝ → ℝ)
    (hConic : SourceBoundConicGoverningRelations p s motion scale eccentricity period
      orientation phaseOffset phase) :
    eccentricity = (xPlus - xMinus) / (xPlus + xMinus) ∧
      xPlus / xMinus = (1 + eccentricity) / (1 - eccentricity) := by
  have hRadius := initialRadius_eq_smallerTurningPoint p s hSetup hRoots
  rcases hSetup with ⟨hPhysical, hSource, hBound⟩
  have hEnergy := initialEnergy_eq p s hPhysical hSource
  have hAngular := initialAngularMomentumMagnitude_eq p s hPhysical hSource
  have hCoulomb := coulombStrength_mul_bohrRadius p hPhysical
  rcases hPhysical with ⟨hm, he, hε, hℏ, ha, hk, hk_def, ha_def⟩
  dsimp only [HasSourceInitialConditions] at hSource
  rcases hSource with
    ⟨hμ, hR, hanti, hperpPos, hperpElec, hangularPos, hangularElec⟩
  rcases hRoots with ⟨hxMinusPos, hrootOrder, hrootMinus, hrootPlus, hrootClass⟩
  rcases hConic with
    ⟨hscale, hperiod, heccentricity, heccentricity_lt, horientation,
      hcontinuous, heccentricity_formula, hrelations⟩
  have hxMinus : xMinus = 100 := by
    have hmul : xMinus * p.bohrRadius.val = 100 * p.bohrRadius.val := by
      rw [← hRadius, ← hR]
    exact mul_right_cancel₀ (ne_of_gt ha) hmul
  have hCoulomb' :
      (coulombStrength p).val =
        p.reducedPlanckConstant.val ^ 2 /
          (p.mass.val * p.bohrRadius.val) := by
    apply (eq_div_iff (mul_ne_zero (ne_of_gt hm) (ne_of_gt ha))).2
    calc
      (coulombStrength p).val * (p.mass.val * p.bohrRadius.val) =
          ((coulombStrength p).val * p.bohrRadius.val) * p.mass.val := by ring
      _ = (p.reducedPlanckConstant.val ^ 2 / p.mass.val) * p.mass.val := by
        rw [hCoulomb]
      _ = p.reducedPlanckConstant.val ^ 2 :=
        div_mul_cancel₀ _ (ne_of_gt hm)
  have hEnergyExplicit :
      (initialEnergy p s).val =
        (-9 / 2500 : ℝ) *
          (p.reducedPlanckConstant.val ^ 2 /
            (p.mass.val * p.bohrRadius.val ^ 2)) := by
    rw [hEnergy, hμ, hR, hCoulomb']
    ring
  have hPolynomial (x : ℝ) :
      (radialTurningPolynomial p s x).val =
        (p.reducedPlanckConstant.val ^ 2 / p.mass.val) *
          ((-9 / 2500 : ℝ) * (x - 100) * (x - 1600 / 9)) := by
    change
      (initialEnergy p s).val * (p.bohrRadius.val * x) ^ 2 +
            (coulombStrength p).val * (p.bohrRadius.val * x) -
          (initialAngularMomentumMagnitude p s).val ^ 2 /
            (2 * (p.mass.val / 2)) =
        (p.reducedPlanckConstant.val ^ 2 / p.mass.val) *
          ((-9 / 2500 : ℝ) * (x - 100) * (x - 1600 / 9))
    have hlinear :
        (p.reducedPlanckConstant.val ^ 2 /
              (p.mass.val * p.bohrRadius.val)) *
            (p.bohrRadius.val * x) =
          (p.reducedPlanckConstant.val ^ 2 / p.mass.val) * x := by
      calc
        (p.reducedPlanckConstant.val ^ 2 /
                (p.mass.val * p.bohrRadius.val)) *
              (p.bohrRadius.val * x) =
            (p.reducedPlanckConstant.val ^ 2 * p.bohrRadius.val) /
                (p.mass.val * p.bohrRadius.val) * x := by ring
        _ = (p.reducedPlanckConstant.val ^ 2 / p.mass.val) * x := by
          rw [mul_div_mul_right _ _ (ne_of_gt ha)]
    have hquadratic :
        (p.reducedPlanckConstant.val ^ 2 /
              (p.mass.val * p.bohrRadius.val ^ 2)) *
            (p.bohrRadius.val * x) ^ 2 =
          (p.reducedPlanckConstant.val ^ 2 / p.mass.val) * x ^ 2 := by
      calc
        (p.reducedPlanckConstant.val ^ 2 /
                (p.mass.val * p.bohrRadius.val ^ 2)) *
              (p.bohrRadius.val * x) ^ 2 =
            (p.reducedPlanckConstant.val ^ 2 * p.bohrRadius.val ^ 2) /
                (p.mass.val * p.bohrRadius.val ^ 2) * x ^ 2 := by ring
        _ = (p.reducedPlanckConstant.val ^ 2 / p.mass.val) * x ^ 2 := by
          rw [mul_div_mul_right _ _ (pow_ne_zero 2 (ne_of_gt ha))]
    rw [hEnergyExplicit, hCoulomb', hAngular, hμ]
    calc
      (-9 / 2500 : ℝ) *
              (p.reducedPlanckConstant.val ^ 2 /
                (p.mass.val * p.bohrRadius.val ^ 2)) *
              (p.bohrRadius.val * x) ^ 2 +
            (p.reducedPlanckConstant.val ^ 2 /
                (p.mass.val * p.bohrRadius.val)) *
              (p.bohrRadius.val * x) -
            (2 * 4 * p.reducedPlanckConstant.val) ^ 2 /
              (2 * (p.mass.val / 2)) =
          (-9 / 2500 : ℝ) *
              ((p.reducedPlanckConstant.val ^ 2 /
                  (p.mass.val * p.bohrRadius.val ^ 2)) *
                (p.bohrRadius.val * x) ^ 2) +
            ((p.reducedPlanckConstant.val ^ 2 /
                (p.mass.val * p.bohrRadius.val)) *
              (p.bohrRadius.val * x)) -
            (p.reducedPlanckConstant.val ^ 2 / p.mass.val) * 64 := by ring
      _ = (-9 / 2500 : ℝ) *
              ((p.reducedPlanckConstant.val ^ 2 / p.mass.val) * x ^ 2) +
            (p.reducedPlanckConstant.val ^ 2 / p.mass.val) * x -
            (p.reducedPlanckConstant.val ^ 2 / p.mass.val) * 64 := by
        rw [hquadratic, hlinear]
      _ = (p.reducedPlanckConstant.val ^ 2 / p.mass.val) *
          ((-9 / 2500 : ℝ) * (x - 100) * (x - 1600 / 9)) := by ring
  have hxPlus : xPlus = 1600 / 9 := by
    have hzero := hrootPlus.2
    rw [hPolynomial] at hzero
    have hscale_ne :
        p.reducedPlanckConstant.val ^ 2 / p.mass.val ≠ 0 := by positivity
    have hrest : (-9 / 2500 : ℝ) * (xPlus - 100) * (xPlus - 1600 / 9) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hscale_ne
    have hfac : (xPlus - 100) * (xPlus - 1600 / 9) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (by positivity : (-9 / 2500 : ℝ) ≠ 0)
      rw [← mul_assoc]
      exact hrest
    rcases mul_eq_zero.mp hfac with hfirst | hsecond
    · have : xPlus = 100 := sub_eq_zero.mp hfirst
      rw [hxMinus, this] at hrootOrder
      exact False.elim (lt_irrefl _ hrootOrder)
    · exact sub_eq_zero.mp hsecond
  have hstrength :
      (coulombStrength p).val =
        p.coulombConstant.val * p.elementaryCharge.val ^ 2 := by
    change
      -(p.coulombConstant.val * p.elementaryCharge.val * -p.elementaryCharge.val) =
        p.coulombConstant.val * p.elementaryCharge.val ^ 2
    ring
  let Q : ℝ :=
    1 +
      4 * (initialAngularMomentumMagnitude p s).val ^ 2 * (initialEnergy p s).val /
        (p.coulombConstant.val ^ 2 * p.elementaryCharge.val ^ 4 * p.mass.val)
  have hdenominator :
      p.coulombConstant.val ^ 2 * p.elementaryCharge.val ^ 4 * p.mass.val =
        (coulombStrength p).val ^ 2 * p.mass.val := by
    rw [hstrength]
    ring
  have hQ : Q = 49 / 625 := by
    have hcommon_ne :
        p.reducedPlanckConstant.val ^ 4 /
            (p.mass.val * p.bohrRadius.val ^ 2) ≠ 0 := by
      positivity
    have hdenReduced :
        (p.reducedPlanckConstant.val ^ 2 /
              (p.mass.val * p.bohrRadius.val)) ^ 2 * p.mass.val =
          p.reducedPlanckConstant.val ^ 4 /
            (p.mass.val * p.bohrRadius.val ^ 2) := by
      rw [div_pow, div_mul_eq_mul_div]
      calc
        (p.reducedPlanckConstant.val ^ 2) ^ 2 * p.mass.val /
              (p.mass.val * p.bohrRadius.val) ^ 2 =
            (p.mass.val * p.reducedPlanckConstant.val ^ 4) /
              (p.mass.val * (p.mass.val * p.bohrRadius.val ^ 2)) := by
                congr 1 <;> ring
        _ = p.reducedPlanckConstant.val ^ 4 /
              (p.mass.val * p.bohrRadius.val ^ 2) :=
          mul_div_mul_left _ _ (ne_of_gt hm)
    have hnumReduced :
        4 * (2 * 4 * p.reducedPlanckConstant.val) ^ 2 *
              ((-9 / 2500 : ℝ) *
                (p.reducedPlanckConstant.val ^ 2 /
                  (p.mass.val * p.bohrRadius.val ^ 2))) =
            (-576 / 625 : ℝ) *
              (p.reducedPlanckConstant.val ^ 4 /
                (p.mass.val * p.bohrRadius.val ^ 2)) := by
      ring
    dsimp only [Q]
    rw [hdenominator, hCoulomb', hAngular, hμ, hEnergyExplicit]
    rw [hnumReduced, hdenReduced]
    rw [mul_div_cancel_right₀ _ hcommon_ne]
    ring
  have heccentricity_sqrt : eccentricity = Real.sqrt Q := by
    dsimp only [Q]
    exact heccentricity_formula
  have hQpos : 0 < Q := by
    apply (Real.sqrt_pos).mp
    rw [← heccentricity_sqrt]
    exact heccentricity
  have heccentricity_sq : eccentricity ^ 2 = 49 / 625 := by
    rw [heccentricity_sqrt, Real.sq_sqrt hQpos.le, hQ]
  have heccentricity_value : eccentricity = 7 / 25 := by
    apply (sq_eq_sq₀ heccentricity.le (by positivity : (0 : ℝ) ≤ 7 / 25)).mp
    rw [heccentricity_sq]
    ring
  constructor
  · rw [hxMinus, hxPlus, heccentricity_value]
    ring
  · rw [hxMinus, hxPlus, heccentricity_value]
    ring

/-- The lower and upper conic apsides are exactly the two ordered turning roots. -/
lemma sourceConic_apsides_eq_orderedTurningPoints
    (p : Parameters) (s : InitialState) (motion : PairMotion)
    (hAdmissible : IsAdmissibleBoundOrbit p s motion)
    {xMinus xPlus : ℝ}
    (hRoots : AreOrderedPositiveTurningPoints p s xMinus xPlus)
    (scale : LengthQuantity) (eccentricity : ℝ) (period : TimeQuantity)
    (orientation phaseOffset : ℝ) (phase : ℝ → ℝ)
    (hConic : SourceBoundConicGoverningRelations p s motion scale eccentricity period
      orientation phaseOffset phase) :
    scale.val / (p.bohrRadius.val * (1 + eccentricity)) = xMinus ∧
    scale.val / (p.bohrRadius.val * (1 - eccentricity)) = xPlus ∧
    ∀ x : ℝ,
      IsPositiveTurningPointInBohrRadii p s x ↔
        x = scale.val / (p.bohrRadius.val * (1 + eccentricity)) ∨
        x = scale.val / (p.bohrRadius.val * (1 - eccentricity)) := by
  have hSetup := hAdmissible.1
  have ha : 0 < p.bohrRadius.val := hSetup.1.2.2.2.2.1
  have hConicBounds :=
    sourceConic_denominator_pos_and_radial_bounds p s motion scale eccentricity period
      orientation phaseOffset phase hConic
  have hTraversal :=
    sourceConic_fullTraversal_attains_apsides p s motion scale eccentricity period
      orientation phaseOffset phase hConic 0
  have hMotionBounds :=
    separation_between_orderedTurningPoints p s motion hAdmissible hRoots
  have hInitial := initialTime_is_smallerTurningPoint p s motion hAdmissible hRoots
  have hRatio :=
    sourceConic_eccentricity_eq_turningRootRatio p s motion hSetup hRoots scale
      eccentricity period orientation phaseOffset phase hConic
  rcases hConic with
    ⟨hscale, hperiod, heccentricity, heccentricity_lt, horientation,
      hcontinuous, heccentricity_formula, hrelations⟩
  rcases hTraversal with
    ⟨tMinus, tPlus, htMinus, htPlus, hcosMinus, hsepMinus,
      hcosPlus, hsepPlus, hapsisOrder⟩
  rcases hRoots with
    ⟨hxMinusPos, hrootOrder, hrootMinus, hrootPlus, hrootClass⟩
  have honeAdd : 0 < 1 + eccentricity := by linarith
  have honeSub : 0 < 1 - eccentricity := by linarith
  have hlower_le :
      xMinus * p.bohrRadius.val ≤ scale.val / (1 + eccentricity) := by
    rw [← hsepMinus]
    exact (hMotionBounds tMinus).1
  have hle_lower :
      scale.val / (1 + eccentricity) ≤ xMinus * p.bohrRadius.val := by
    calc
      scale.val / (1 + eccentricity) ≤
          (motionObservables motion s.initialTime.val).separation.val :=
        (hConicBounds s.initialTime.val).2.2.1
      _ = xMinus * p.bohrRadius.val := hInitial.2
  have hlower :
      scale.val / (1 + eccentricity) = xMinus * p.bohrRadius.val :=
    le_antisymm hle_lower hlower_le
  have hratioCross :
      xPlus * (1 - eccentricity) = xMinus * (1 + eccentricity) := by
    have hcross :=
      (div_eq_div_iff (ne_of_gt hxMinusPos) (ne_of_gt honeSub)).mp hRatio.2
    calc
      xPlus * (1 - eccentricity) = (1 + eccentricity) * xMinus := hcross
      _ = xMinus * (1 + eccentricity) := by ring
  have hupper :
      scale.val / (1 - eccentricity) = xPlus * p.bohrRadius.val := by
    apply (div_eq_iff (ne_of_gt honeSub)).2
    have hscaleEq := (div_eq_iff (ne_of_gt honeAdd)).mp hlower
    calc
      scale.val = xMinus * p.bohrRadius.val * (1 + eccentricity) := hscaleEq
      _ = p.bohrRadius.val * (xMinus * (1 + eccentricity)) := by ring
      _ = p.bohrRadius.val * (xPlus * (1 - eccentricity)) := by rw [← hratioCross]
      _ = xPlus * p.bohrRadius.val * (1 - eccentricity) := by ring
  have hlowerNormalized :
      scale.val / (p.bohrRadius.val * (1 + eccentricity)) = xMinus := by
    apply (div_eq_iff (mul_ne_zero (ne_of_gt ha) (ne_of_gt honeAdd))).2
    have hscaleEq := (div_eq_iff (ne_of_gt honeAdd)).mp hlower
    calc
      scale.val = xMinus * p.bohrRadius.val * (1 + eccentricity) := hscaleEq
      _ = xMinus * (p.bohrRadius.val * (1 + eccentricity)) := by ring
  have hupperNormalized :
      scale.val / (p.bohrRadius.val * (1 - eccentricity)) = xPlus := by
    apply (div_eq_iff (mul_ne_zero (ne_of_gt ha) (ne_of_gt honeSub))).2
    have hscaleEq := (div_eq_iff (ne_of_gt honeSub)).mp hupper
    calc
      scale.val = xPlus * p.bohrRadius.val * (1 - eccentricity) := hscaleEq
      _ = xPlus * (p.bohrRadius.val * (1 - eccentricity)) := by ring
  refine ⟨hlowerNormalized, hupperNormalized, ?_⟩
  intro x
  constructor
  · intro hx
    rcases hrootClass x hx with h | h
    · left
      rw [hlowerNormalized]
      exact h
    · right
      rw [hupperNormalized]
      exact h
  · intro hx
    rw [hlowerNormalized, hupperNormalized] at hx
    rcases hx with rfl | rfl
    · exact hrootMinus
    · exact hrootPlus

/-- For every admissible source development, the larger root is precisely the unique
attained global-maximum value (without asserting uniqueness of the maximizing time). -/
lemma largerTurningPoint_is_unique_attainedMaximum
    (p : Parameters) (s : InitialState) (motion : PairMotion)
    (hAdmissible : IsAdmissibleBoundOrbit p s motion)
    {xMinus xPlus : ℝ}
    (hRoots : AreOrderedPositiveTurningPoints p s xMinus xPlus) :
    ∀ answer : ℝ,
      IsAttainedMaximumInBohrRadii p motion answer ↔ answer = xPlus := by
  have ha : 0 < p.bohrRadius.val := hAdmissible.1.1.2.2.2.2.1
  rcases hAdmissible.2.2.2.2 with
    ⟨scale, eccentricity, period, orientation, phaseOffset, phase, hConic⟩
  have hBounds :=
    sourceConic_denominator_pos_and_radial_bounds p s motion scale eccentricity period
      orientation phaseOffset phase hConic
  have hTraversal :=
    sourceConic_fullTraversal_attains_apsides p s motion scale eccentricity period
      orientation phaseOffset phase hConic 0
  have hApsides :=
    sourceConic_apsides_eq_orderedTurningPoints p s motion hAdmissible hRoots scale
      eccentricity period orientation phaseOffset phase hConic
  rcases hConic with
    ⟨hscale, hperiod, heccentricity, heccentricity_lt, horientation,
      hcontinuous, heccentricity_formula, hrelations⟩
  rcases hTraversal with
    ⟨tMinus, tPlus, htMinus, htPlus, hcosMinus, hsepMinus,
      hcosPlus, hsepPlus, hapsisOrder⟩
  rcases hRoots with
    ⟨hxMinusPos, hrootOrder, hrootMinus, hrootPlus, hrootClass⟩
  have honeSub : 0 < 1 - eccentricity := by linarith
  have hUpperDimensional :
      scale.val / (1 - eccentricity) = xPlus * p.bohrRadius.val := by
    have hscaleEq :=
      (div_eq_iff (mul_ne_zero (ne_of_gt ha) (ne_of_gt honeSub))).mp hApsides.2.1
    apply (div_eq_iff (ne_of_gt honeSub)).2
    calc
      scale.val = xPlus * (p.bohrRadius.val * (1 - eccentricity)) := hscaleEq
      _ = xPlus * p.bohrRadius.val * (1 - eccentricity) := by ring
  have hAtPlus :
      (motionObservables motion tPlus).separation.val =
        xPlus * p.bohrRadius.val := by
    rw [hsepPlus, hUpperDimensional]
  intro answer
  constructor
  · intro hMaximum
    rcases hMaximum with ⟨hanswerPos, tAnswer, hturning, hsepAnswer, hglobal⟩
    have hlower : xPlus ≤ answer := by
      apply le_of_mul_le_mul_right (a := p.bohrRadius.val) (b := xPlus) (c := answer)
      · calc
        xPlus * p.bohrRadius.val =
            (motionObservables motion tPlus).separation.val := hAtPlus.symm
        _ ≤ (motionObservables motion tAnswer).separation.val := hglobal tPlus
        _ = answer * p.bohrRadius.val := hsepAnswer
      · exact ha
    have hupper : answer ≤ xPlus := by
      apply le_of_mul_le_mul_right (a := p.bohrRadius.val) (b := answer) (c := xPlus)
      · calc
        answer * p.bohrRadius.val =
            (motionObservables motion tAnswer).separation.val := hsepAnswer.symm
        _ ≤ scale.val / (1 - eccentricity) := (hBounds tAnswer).2.2.2
        _ = xPlus * p.bohrRadius.val := hUpperDimensional
      · exact ha
    exact le_antisymm hupper hlower
  · intro hanswer
    subst answer
    refine ⟨lt_trans hxMinusPos hrootOrder, tPlus, ?_, hAtPlus, ?_⟩
    · apply (turningTime_iff_positiveTurningPoint p s motion hAdmissible tPlus).2
      have hratio :
          (motionObservables motion tPlus).separation.val / p.bohrRadius.val = xPlus := by
        rw [hAtPlus]
        exact mul_div_cancel_right₀ _ (ne_of_gt ha)
      rw [hratio]
      exact hrootPlus
    · intro t
      calc
        (motionObservables motion t).separation.val ≤
            scale.val / (1 - eccentricity) := (hBounds t).2.2.2
        _ = xPlus * p.bohrRadius.val := hUpperDimensional
        _ = (motionObservables motion tPlus).separation.val := hAtPlus.symm

end
end ProblemIPhO2026_1_B_1

open ProblemIPhO2026_1_B_1

/-- The source setup and its stated boundedness determine a unique maximum separation in
Bohr-radius units.  The value is intentionally absent from the theorem signature. -/
theorem problem_IPhO_2026_1_B_1
    (p : Parameters) (s : InitialState) (hSetup : SourceProblemSetup p s)
    (hBounded : HasSourceStatedBoundedness p s) :
    ∃! answer : ℝ, MaximumSeparationSolution p s answer := by
  rcases existsUnique_orderedPositiveTurningPoints p s hSetup with
    ⟨roots, hRoots, hRootsUnique⟩
  rcases hRoots with
    ⟨hxMinusPos, hrootOrder, hrootMinus, hrootPlus, hrootClass⟩
  have hLarger : IsLargerPositiveTurningPoint p s roots.2 := by
    refine ⟨hrootPlus, ?_⟩
    intro x hx
    rcases hrootClass x hx with h | h
    · rw [h]
      exact hrootOrder.le
    · rw [h]
  have hRootsRebuilt :
      AreOrderedPositiveTurningPoints p s roots.1 roots.2 :=
    ⟨hxMinusPos, hrootOrder, hrootMinus, hrootPlus, hrootClass⟩
  have hSolution : MaximumSeparationSolution p s roots.2 := by
    refine ⟨hLarger, hBounded, ?_⟩
    intro motion hAdmissible
    exact
      (largerTurningPoint_is_unique_attainedMaximum p s motion hAdmissible
        hRootsRebuilt roots.2).2 rfl
  refine ⟨roots.2, hSolution, ?_⟩
  intro answer hAnswer
  apply le_antisymm
  · exact hLarger.2 answer hAnswer.1.1
  · exact hAnswer.1.2 roots.2 hrootPlus

end Ipho2026Gpt56solBlind
