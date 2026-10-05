import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Basic
import Physlib.Units.ISQDimensionBase
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, problem 3, part A.1

This file gives an answer-blind model of the magnetic field-strength magnitude in a
thin, densely wound paramagnetic torus.  The requested magnitude is characterized by
the torus geometry, the uniform-field approximation, and Ampère's law; no closed-form
value for it is part of the statement.
-/

namespace Ipho2026Gpt56solBlind
namespace ProblemIPhO2026_3_A_1

open Dimension

/-! ## Dimensioned scalar quantities -/

/-- Length in the seven-base International System of Quantities (ISQ). -/
def lengthDimension : Dimension ISQDimensionBase := single .length

/-- Time in the seven-base International System of Quantities (ISQ). -/
def timeDimension : Dimension ISQDimensionBase := single .time

/-- Mass in the seven-base International System of Quantities (ISQ). -/
def massDimension : Dimension ISQDimensionBase := single .mass

/-- Electric current in the seven-base International System of Quantities (ISQ). -/
def currentDimension : Dimension ISQDimensionBase := single .current

/-- Cross-sectional area has dimension `length²`. -/
def areaDimension : Dimension ISQDimensionBase := lengthDimension ^ 2

/-- Volume has dimension `length³`. -/
def volumeDimension : Dimension ISQDimensionBase := lengthDimension ^ 3

/-- The magnetic field strength `H` and magnetization `M` have dimension current/length. -/
def magneticFieldStrengthDimension : Dimension ISQDimensionBase :=
  currentDimension * lengthDimension⁻¹

/-- Magnetic flux density `B` has SI dimension mass/(current·time²). -/
def magneticFluxDensityDimension : Dimension ISQDimensionBase :=
  massDimension * currentDimension⁻¹ * timeDimension⁻¹ * timeDimension⁻¹

/-- Vacuum permeability has the dimension needed to send `H` to `B`. -/
def permeabilityDimension : Dimension ISQDimensionBase :=
  magneticFluxDensityDimension * magneticFieldStrengthDimension⁻¹

abbrev Length := WithDim lengthDimension ℝ
abbrev Area := WithDim areaDimension ℝ
abbrev Volume := WithDim volumeDimension ℝ
abbrev ElectricCurrent := WithDim currentDimension ℝ
abbrev MagneticFieldStrength := WithDim magneticFieldStrengthDimension ℝ
abbrev Magnetization := WithDim magneticFieldStrengthDimension ℝ
abbrev MagneticFluxDensity := WithDim magneticFluxDensityDimension ℝ
abbrev Permeability := WithDim permeabilityDimension ℝ

/-! ## Thin-torus geometry and the winding -/

/--
Geometry of the torus in the thin-torus regime.  `meanRadiusR`, `innerRadiusr`,
`crossSectionAreaA`, and `volumeV` are the source quantities `R`, `r`, `A`, and `V`.

The caller supplies a positive smallness bound `thinnessBound`; the inequality involving
it is the formal version of `r ≪ R`.  The mean Ampère loop `C` has length `2πR`, and
the torus volume is its length times the cross-sectional area.
-/
structure ThinTorusGeometry where
  meanRadiusR : Length
  innerRadiusr : Length
  crossSectionAreaA : Area
  volumeV : Volume
  meanAmpereLoopLength : Length
  thinnessBound : ℝ
  meanRadius_pos : 0 < meanRadiusR.val
  innerRadius_pos : 0 < innerRadiusr.val
  crossSectionArea_pos : 0 < crossSectionAreaA.val
  volume_pos : 0 < volumeV.val
  meanAmpereLoopLength_pos : 0 < meanAmpereLoopLength.val
  thinnessBound_pos : 0 < thinnessBound
  thinnessBound_lt_one : thinnessBound < 1
  thin_torus_regime : innerRadiusr.val ≤ thinnessBound * meanRadiusR.val
  mean_loop_geometry : meanAmpereLoopLength.val = 2 * Real.pi * meanRadiusR.val
  volume_geometry : volumeV.val = crossSectionAreaA.val * meanAmpereLoopLength.val

/--
A homogeneous, isotropic paramagnetic material model.  Homogeneity is represented by
one response map throughout the core; isotropy by its dependence only on the scalar
field-strength magnitude.  The positivity condition records alignment of the
paramagnetic response with a nonnegative applied field.
-/
structure HomogeneousIsotropicParamagnet where
  vacuumPermeabilityMu0 : Permeability
  vacuumPermeability_pos : 0 < vacuumPermeabilityMu0.val
  magnetizationResponse : MagneticFieldStrength → Magnetization
  response_zero : magnetizationResponse 0 = 0
  response_nonnegative :
    ∀ H, 0 ≤ H.val → 0 ≤ (magnetizationResponse H).val

/-- The torus core is nonempty and carries the same homogeneous material everywhere. -/
structure ParamagneticTorus where
  geometry : ThinTorusGeometry
  CorePoint : Type
  core_nonempty : Nonempty CorePoint
  material : HomogeneousIsotropicParamagnet

/--
The densely wound insulated wire.  Every one of the `N` turns carries the same
instantaneous current `I` and links the chosen Ampère surface once with the same
orientation.  These are the topological/current consequences of the dense toroidal
winding needed in part A.1.
-/
structure DenseToroidalWinding where
  turnsN : ℕ
  turns_pos : 0 < turnsN
  instantaneousCurrentI : ElectricCurrent
  current_nonnegative : 0 ≤ instantaneousCurrentI.val
  turnCurrent : Fin turnsN → ElectricCurrent
  eachTurnSameCurrent : ∀ k, turnCurrent k = instantaneousCurrentI
  linkingNumber : Fin turnsN → ℤ
  eachTurnLinksOnce : ∀ k, linkingNumber k = 1

/-- Net free current through a surface bounded by the mean loop `C`. -/
def linkedFreeCurrent (winding : DenseToroidalWinding) : ElectricCurrent :=
  ⟨∑ k, (winding.linkingNumber k : ℝ) * (winding.turnCurrent k).val⟩

/-! ## Uniform magnetic state and governing laws -/

/-- The material relation `B = μ₀ H + μ₀ M`, written with dimensioned arguments. -/
def ConstitutiveLaw (mu0 : Permeability) (H : MagneticFieldStrength)
    (M : Magnetization) (B : MagneticFluxDensity) : Prop :=
  B.val = mu0.val * H.val + mu0.val * M.val

/--
Within the stated uniform-field approximation, the line integral around the mean
toroidal loop is its length times the nonnegative field-strength magnitude.
-/
def uniformMeanLoopCirculation (loopLength : Length) (H : MagneticFieldStrength) :
    ElectricCurrent :=
  ⟨H.val * loopLength.val⟩

/-- Ampère's law `∮_C H · dℓ = I_C` on the mean toroidal loop. -/
def SatisfiesAmpereLaw (geometry : ThinTorusGeometry)
    (winding : DenseToroidalWinding) (H : MagneticFieldStrength) : Prop :=
  uniformMeanLoopCirculation geometry.meanAmpereLoopLength H = linkedFreeCurrent winding

/--
The idealized uniform state used by the problem: the spatial fields `H`, `M`, and `B`
are constant throughout the core, the homogeneous material response supplies `M`, and
the constitutive relation holds pointwise.  Exact constancy here is the mathematical
model adopted after invoking the source's thin-torus/uniform-field approximation.
-/
def IsUniformMagneticState (torus : ParamagneticTorus)
    (H : MagneticFieldStrength) : Prop :=
  ∃ (M : Magnetization) (B : MagneticFluxDensity)
      (hField : torus.CorePoint → MagneticFieldStrength)
      (mField : torus.CorePoint → Magnetization)
      (bField : torus.CorePoint → MagneticFluxDensity),
    0 ≤ H.val ∧
    M = torus.material.magnetizationResponse H ∧
    0 ≤ M.val ∧
    0 ≤ B.val ∧
    (∀ p, hField p = H) ∧
    (∀ p, mField p = M) ∧
    (∀ p, bField p = B) ∧
    ∀ p, ConstitutiveLaw torus.material.vacuumPermeabilityMu0
      (hField p) (mField p) (bField p)

/--
Answer-free solution predicate for the requested magnitude.  Its geometric clause
retains the requested `A` and `V`, while its last clause is Ampère's law for the `N`
linked turns carrying instantaneous current `I`.
-/
def FieldMagnitudeSolution (torus : ParamagneticTorus)
    (winding : DenseToroidalWinding) (H : MagneticFieldStrength) : Prop :=
  IsUniformMagneticState torus H ∧
  torus.geometry.volumeV.val =
    torus.geometry.crossSectionAreaA.val * torus.geometry.meanAmpereLoopLength.val ∧
  SatisfiesAmpereLaw torus.geometry winding H

/--
IPhO 2026 T3-A1: in the thin, uniformly magnetized toroidal approximation with a
dense `N`-turn winding carrying current `I`, there is a unique admissible magnitude
of `H`.  The witness (and hence its closed form in `N`, `I`, `A`, and `V`) is
deliberately absent from the theorem signature.
-/
theorem problem_IPhO_2026_3_A_1 (torus : ParamagneticTorus)
    (winding : DenseToroidalWinding) :
    ∃! H : MagneticFieldStrength, FieldMagnitudeSolution torus winding H := by
  have hlinked_nonnegative : 0 ≤ (linkedFreeCurrent winding).val := by
    change 0 ≤ ∑ k : Fin winding.turnsN,
      (winding.linkingNumber k : ℝ) * (winding.turnCurrent k).val
    apply Finset.sum_nonneg
    intro k _
    rw [winding.eachTurnLinksOnce k, winding.eachTurnSameCurrent k]
    simpa using winding.current_nonnegative
  let H : MagneticFieldStrength :=
    ⟨(linkedFreeCurrent winding).val / torus.geometry.meanAmpereLoopLength.val⟩
  have hH_nonnegative : 0 ≤ H.val := by
    dsimp [H]
    exact div_nonneg hlinked_nonnegative
      (le_of_lt torus.geometry.meanAmpereLoopLength_pos)
  let M : Magnetization := torus.material.magnetizationResponse H
  have hM_nonnegative : 0 ≤ M.val := by
    dsimp [M]
    exact torus.material.response_nonnegative H hH_nonnegative
  let B : MagneticFluxDensity :=
    ⟨torus.material.vacuumPermeabilityMu0.val * H.val +
      torus.material.vacuumPermeabilityMu0.val * M.val⟩
  have hB_nonnegative : 0 ≤ B.val := by
    dsimp [B]
    exact add_nonneg
      (mul_nonneg (le_of_lt torus.material.vacuumPermeability_pos) hH_nonnegative)
      (mul_nonneg (le_of_lt torus.material.vacuumPermeability_pos) hM_nonnegative)
  have hAmpere : SatisfiesAmpereLaw torus.geometry winding H := by
    apply WithDim.ext
    change
      (linkedFreeCurrent winding).val / torus.geometry.meanAmpereLoopLength.val *
          torus.geometry.meanAmpereLoopLength.val =
        (linkedFreeCurrent winding).val
    exact div_mul_cancel₀ _ (ne_of_gt torus.geometry.meanAmpereLoopLength_pos)
  refine ⟨H, ?_, ?_⟩
  · refine ⟨?_, torus.geometry.volume_geometry, hAmpere⟩
    refine ⟨M, B, (fun _ => H), (fun _ => M), (fun _ => B), ?_⟩
    refine ⟨hH_nonnegative, rfl, hM_nonnegative, hB_nonnegative, ?_⟩
    refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
    intro p
    rfl
  · intro H' hH'
    have hAmpere' : SatisfiesAmpereLaw torus.geometry winding H' := hH'.2.2
    have hscalar :
        H'.val * torus.geometry.meanAmpereLoopLength.val =
          (linkedFreeCurrent winding).val := by
      exact congrArg WithDim.val hAmpere'
    apply WithDim.ext
    change
      H'.val =
        (linkedFreeCurrent winding).val / torus.geometry.meanAmpereLoopLength.val
    rw [eq_div_iff (ne_of_gt torus.geometry.meanAmpereLoopLength_pos)]
    exact hscalar

end ProblemIPhO2026_3_A_1
end Ipho2026Gpt56solBlind
