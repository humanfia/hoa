import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, problem 1 C.1: photodissociation threshold

This file gives an answer-blind specification of the minimum photon angular
frequency needed to dissociate an initially stationary ozone molecule into an
oxygen molecule and an oxygen atom.  No closed form for that frequency is part
of the specification.

All physical scalars are genuine Physlib `WithDim` quantities over the LTMCT
dimension basis.  Their `.val` fields are numerical coordinates in one fixed
coherent system of units; the dimensions remain present in their Lean types.
-/

namespace Ipho2026Gpt56solBlind

namespace Problem1C1

noncomputable section

/-- Physlib's rational-exponent dimensions over the length, time, mass, charge,
and temperature basis. -/
abbrev Dimension : Type := _root_.Dimension LTMCTDimensionBase

namespace Dimension

/-- Mass dimension. -/
def mass : Problem1C1.Dimension := _root_.Dimension.M𝓭

/-- Speed dimension `L T⁻¹`. -/
def speed : Problem1C1.Dimension :=
  _root_.Dimension.L𝓭 * _root_.Dimension.T𝓭⁻¹

/-- Angular-frequency dimension `T⁻¹`; plane angle is dimensionless. -/
def angularFrequency : Problem1C1.Dimension :=
  _root_.Dimension.T𝓭⁻¹

/-- Energy dimension `M L² T⁻²`. -/
def energy : Problem1C1.Dimension :=
  _root_.Dimension.M𝓭 * _root_.Dimension.L𝓭 * _root_.Dimension.L𝓭 *
    _root_.Dimension.T𝓭⁻¹ * _root_.Dimension.T𝓭⁻¹

/-- Action dimension `M L² T⁻¹`. -/
def action : Problem1C1.Dimension :=
  _root_.Dimension.M𝓭 * _root_.Dimension.L𝓭 * _root_.Dimension.L𝓭 *
    _root_.Dimension.T𝓭⁻¹

/-- Momentum dimension `M L T⁻¹`. -/
def momentum : Problem1C1.Dimension :=
  _root_.Dimension.M𝓭 * _root_.Dimension.L𝓭 * _root_.Dimension.T𝓭⁻¹

/-- Plane angles measured in radians are dimensionless. -/
def planeAngle : Problem1C1.Dimension := 1

end Dimension

/-- A real Physlib quantity carrying the fixed physical dimension `dimension`.
The underlying real is its coordinate in one fixed coherent unit system. -/
abbrev Quantity (dimension : Dimension) : Type := WithDim dimension ℝ

abbrev Energy := Quantity Dimension.energy
abbrev Mass := Quantity Dimension.mass
abbrev Speed := Quantity Dimension.speed
abbrev Action := Quantity Dimension.action
abbrev AngularFrequency := Quantity Dimension.angularFrequency
abbrev Momentum := Quantity Dimension.momentum
abbrev PlaneAngle := Quantity Dimension.planeAngle

/-- Strict positivity of a dimensioned scalar in the fixed coherent units. -/
def IsStrictlyPositive {dimension : Dimension} (q : Quantity dimension) : Prop :=
  0 < q.val

/-- Addition of energies. -/
def addEnergy (a b : Energy) : Energy :=
  a + b

/-- Difference of energies. -/
def subEnergy (a b : Energy) : Energy :=
  a - b

/-- Multiplication of a mass by a dimensionless real scalar. -/
def scaleMass (a : ℝ) (massValue : Mass) : Mass :=
  ⟨a * massValue.val⟩

/-- A planar momentum, with the incident photon direction used as the positive
`x`-axis and the `y`-axis in the scattering plane. -/
structure PlanarMomentum where
  x : Momentum
  y : Momentum

/-- Vector addition of planar momenta. -/
def addMomentum (p q : PlanarMomentum) : PlanarMomentum :=
  ⟨p.x + q.x, p.y + q.y⟩

/-- Squared Euclidean norm, retaining the squared-momentum dimension. -/
def momentumNormSq (p : PlanarMomentum) :
    Quantity (Dimension.momentum * Dimension.momentum) :=
  ⟨p.x.val ^ 2 + p.y.val ^ 2⟩

/-- Euclidean norm of a planar momentum. -/
def momentumNorm (p : PlanarMomentum) : Momentum :=
  ⟨Real.sqrt (momentumNormSq p).val⟩

/-- Euclidean dot product, retaining the squared-momentum dimension. -/
def momentumDot (p q : PlanarMomentum) :
    Quantity (Dimension.momentum * Dimension.momentum) :=
  ⟨p.x.val * q.x.val + p.y.val * q.y.val⟩

/-- Non-relativistic kinetic energy `|p|²/(2 M)`.  The use of this law records
the classical approximation regime stated in the problem. -/
def classicalKineticEnergy (p : PlanarMomentum) (massValue : Mass) : Energy :=
  ⟨(momentumNormSq p).val / (2 * massValue.val)⟩

/-- The dimensional parameters and named ground-state quantities of the
photodissociation experiment. -/
structure PhotodissociationSetup where
  reducedPlanckConstant : Action
  speedOfLight : Speed
  oxygenAtomMass : Mass
  ozoneGroundEnergy : Energy
  oxygenMoleculeGroundEnergy : Energy
  /-- `ΔU = U_f - U_i`. -/
  energyGap : Energy
  /-- The unsigned angle from the incident photon momentum to the outgoing
  oxygen-molecule momentum, in radians. -/
  outgoingAngle : PlaneAngle

/-- Physical-domain assumptions for the classical model.  The angle spans the
full unsigned domain `[0, π]`; no acute-angle or threshold-attainment
assumption is imposed. -/
def PhotodissociationSetup.IsPhysical (setup : PhotodissociationSetup) : Prop :=
  IsStrictlyPositive setup.reducedPlanckConstant ∧
    IsStrictlyPositive setup.speedOfLight ∧
    IsStrictlyPositive setup.oxygenAtomMass ∧
    setup.energyGap =
      subEnergy setup.oxygenMoleculeGroundEnergy setup.ozoneGroundEnergy ∧
    IsStrictlyPositive setup.energyGap ∧
    0 ≤ setup.outgoingAngle.val ∧
    setup.outgoingAngle.val ≤ Real.pi

/-- The energy `ℏ ω` of the completely absorbed photon. -/
def photonEnergy (setup : PhotodissociationSetup)
    (omega : AngularFrequency) : Energy :=
  ⟨setup.reducedPlanckConstant.val * omega.val⟩

/-- The photon momentum magnitude `Eγ/c = ℏ ω/c`. -/
def photonMomentumMagnitude (setup : PhotodissociationSetup)
    (omega : AngularFrequency) : Momentum :=
  ⟨(photonEnergy setup omega).val / setup.speedOfLight.val⟩

/-- The incident photon momentum in the chosen planar chart. -/
def incidentPhotonMomentum (setup : PhotodissociationSetup)
    (omega : AngularFrequency) : PlanarMomentum :=
  ⟨photonMomentumMagnitude setup omega, 0⟩

/-- The outgoing oxygen-molecule and oxygen-atom momenta. -/
structure FragmentMomenta where
  oxygenMolecule : PlanarMomentum
  oxygenAtom : PlanarMomentum

/-- In the stated classical model the oxygen molecule has inertial mass `2m`;
the atomic fragment has mass `m`. -/
def oxygenMoleculeMass (setup : PhotodissociationSetup) : Mass :=
  scaleMass 2 setup.oxygenAtomMass

/-- Total final non-relativistic kinetic energy of O₂ and O. -/
def finalKineticEnergy (setup : PhotodissociationSetup)
    (momenta : FragmentMomenta) : Energy :=
  addEnergy
    (classicalKineticEnergy momenta.oxygenMolecule
      (oxygenMoleculeMass setup))
    (classicalKineticEnergy momenta.oxygenAtom setup.oxygenAtomMass)

/-- Momentum conservation for an initially stationary ozone molecule after
complete photon absorption. -/
def ConservesMomentum (setup : PhotodissociationSetup)
    (omega : AngularFrequency) (momenta : FragmentMomenta) : Prop :=
  addMomentum momenta.oxygenMolecule momenta.oxygenAtom =
    incidentPhotonMomentum setup omega

/-- Energy conservation after cancelling the initial ozone ground-state
energy and using `ΔU = U_f - U_i`. -/
def ConservesEnergy (setup : PhotodissociationSetup)
    (omega : AngularFrequency) (momenta : FragmentMomenta) : Prop :=
  photonEnergy setup omega =
    addEnergy setup.energyGap (finalKineticEnergy setup momenta)

/-- Two nonzero planar momenta make the unsigned angle `theta` when their dot
product is `|p| |q| cos theta`.  Combined with the setup domain
`0 ≤ theta ≤ π`, this covers acute, right, and obtuse angles. -/
def MomentaMakeAngle (p q : PlanarMomentum) (theta : PlaneAngle) : Prop :=
  IsStrictlyPositive (momentumNormSq p) ∧
    IsStrictlyPositive (momentumNormSq q) ∧
    momentumDot p q =
      ⟨(momentumNorm p).val * (momentumNorm q).val * Real.cos theta.val⟩

/-- A physically admissible dissociation outcome at a proposed positive photon
angular frequency, combining the angular geometry with both conservation
laws. -/
def IsDissociationOutcome (setup : PhotodissociationSetup)
    (omega : AngularFrequency) (momenta : FragmentMomenta) : Prop :=
  IsStrictlyPositive omega ∧
    MomentaMakeAngle (incidentPhotonMomentum setup omega)
      momenta.oxygenMolecule setup.outgoingAngle ∧
    ConservesMomentum setup omega momenta ∧
    ConservesEnergy setup omega momenta

/-- Dissociation is feasible at `omega` exactly when fragment momenta obeying
all governing equations exist. -/
def DissociationFeasible (setup : PhotodissociationSetup)
    (omega : AngularFrequency) : Prop :=
  ∃ momenta : FragmentMomenta, IsDissociationOutcome setup omega momenta

/-- The prescribed outgoing angle is acute. -/
def IsAcuteAngle (setup : PhotodissociationSetup) : Prop :=
  0 < Real.cos setup.outgoingAngle.val

/-- The prescribed outgoing angle is right or obtuse.  On the physical
unsigned-angle domain this is the complement of `IsAcuteAngle`. -/
def IsRightOrObtuseAngle (setup : PhotodissociationSetup) : Prop :=
  Real.cos setup.outgoingAngle.val ≤ 0

/-- The outgoing oxygen-molecule momentum with magnitude `r`, using the
positive-`y` representative of the prescribed unsigned angle. -/
def outgoingMoleculeMomentumAtAngle (setup : PhotodissociationSetup)
    (r : Momentum) : PlanarMomentum :=
  ⟨⟨r.val * Real.cos setup.outgoingAngle.val⟩,
    ⟨r.val * Real.sin setup.outgoingAngle.val⟩⟩

/-- The atomic-fragment momentum obtained by eliminating it from vector
momentum conservation. -/
def eliminatedAtomicMomentum (setup : PhotodissociationSetup)
    (omega : AngularFrequency) (r : Momentum) : PlanarMomentum :=
  ⟨⟨(photonMomentumMagnitude setup omega).val -
      r.val * Real.cos setup.outgoingAngle.val⟩,
    ⟨-(r.val * Real.sin setup.outgoingAngle.val)⟩⟩

/-- Final kinetic-energy cost after momentum conservation has eliminated the
atomic momentum and the molecular momentum has been parametrized by its
positive magnitude at the prescribed angle. -/
def reducedKineticCost (setup : PhotodissociationSetup)
    (omega : AngularFrequency) (r : Momentum) : Energy :=
  finalKineticEnergy setup
    { oxygenMolecule := outgoingMoleculeMomentumAtAngle setup r
      oxygenAtom := eliminatedAtomicMomentum setup omega r }

/-- Exact scalar reduction of the angle condition and both conservation laws.
The physical molecular momentum magnitude remains an existential variable; no
threshold value is inserted into this contract. -/
lemma dissociationFeasible_iff_reducedKineticCost
    (setup : PhotodissociationSetup) (hsetup : setup.IsPhysical)
    (omega : AngularFrequency) :
    DissociationFeasible setup omega ↔
      ∃ r : Momentum,
        IsStrictlyPositive r ∧
          photonEnergy setup omega =
            addEnergy setup.energyGap (reducedKineticCost setup omega r) := by
  have hhbar := hsetup.1
  have hc := hsetup.2.1
  have hm := hsetup.2.2.1
  have hgapPos := hsetup.2.2.2.2.1
  change 0 < setup.reducedPlanckConstant.val at hhbar
  change 0 < setup.speedOfLight.val at hc
  change 0 < setup.oxygenAtomMass.val at hm
  change 0 < setup.energyGap.val at hgapPos
  constructor
  · rintro ⟨momenta, homega, hangle, hm_conservation, he_conservation⟩
    change 0 < omega.val at homega
    have hq : 0 < (photonMomentumMagnitude setup omega).val := by
      change
        0 < setup.reducedPlanckConstant.val * omega.val /
          setup.speedOfLight.val
      exact div_pos (mul_pos hhbar homega) hc
    let r : Momentum := momentumNorm momenta.oxygenMolecule
    have hp2sq : 0 < (momentumNormSq momenta.oxygenMolecule).val := hangle.2.1
    have hrpos : IsStrictlyPositive r := by
      change 0 < Real.sqrt (momentumNormSq momenta.oxygenMolecule).val
      exact Real.sqrt_pos.2 hp2sq
    refine ⟨r, hrpos, ?_⟩
    have hnormIncident :
        (momentumNorm (incidentPhotonMomentum setup omega)).val =
          (photonMomentumMagnitude setup omega).val := by
      change Real.sqrt
          ((photonMomentumMagnitude setup omega).val ^ 2 + 0 ^ 2) =
        (photonMomentumMagnitude setup omega).val
      rw [zero_pow (show (2 : ℕ) ≠ 0 from Nat.succ_ne_zero 1), add_zero]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]
    have hdot := congrArg WithDim.val hangle.2.2
    change
      (photonMomentumMagnitude setup omega).val *
          momenta.oxygenMolecule.x.val + 0 * momenta.oxygenMolecule.y.val =
        (momentumNorm (incidentPhotonMomentum setup omega)).val * r.val *
          Real.cos setup.outgoingAngle.val at hdot
    rw [zero_mul, add_zero, hnormIncident] at hdot
    have hp2x : momenta.oxygenMolecule.x.val =
        r.val * Real.cos setup.outgoingAngle.val := by
      nlinarith
    have hrsq : r.val ^ 2 =
        momenta.oxygenMolecule.x.val ^ 2 +
          momenta.oxygenMolecule.y.val ^ 2 := by
      dsimp [r, momentumNorm]
      rw [Real.sq_sqrt (le_of_lt hp2sq)]
      rfl
    have hp2ysq : momenta.oxygenMolecule.y.val ^ 2 =
        r.val ^ 2 * Real.sin setup.outgoingAngle.val ^ 2 := by
      have hp2xsq := congrArg (fun x : ℝ => x ^ 2) hp2x
      nlinarith [Real.sin_sq_add_cos_sq setup.outgoingAngle.val]
    change addMomentum momenta.oxygenMolecule momenta.oxygenAtom =
      incidentPhotonMomentum setup omega at hm_conservation
    have hp1x := congrArg (fun p : PlanarMomentum => p.x.val) hm_conservation
    have hp1y := congrArg (fun p : PlanarMomentum => p.y.val) hm_conservation
    change momenta.oxygenMolecule.x.val + momenta.oxygenAtom.x.val =
      (photonMomentumMagnitude setup omega).val at hp1x
    change momenta.oxygenMolecule.y.val + momenta.oxygenAtom.y.val = 0 at hp1y
    have hp1x' : momenta.oxygenAtom.x.val =
        (photonMomentumMagnitude setup omega).val -
          r.val * Real.cos setup.outgoingAngle.val := by linarith
    have hp1y' : momenta.oxygenAtom.y.val =
        -momenta.oxygenMolecule.y.val := by linarith
    have hcost : reducedKineticCost setup omega r =
        finalKineticEnergy setup momenta := by
      apply WithDim.ext
      change
        ((r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
              (r.val * Real.sin setup.outgoingAngle.val) ^ 2) /
            (2 * (2 * setup.oxygenAtomMass.val)) +
          (((photonMomentumMagnitude setup omega).val -
                r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
              (-(r.val * Real.sin setup.outgoingAngle.val)) ^ 2) /
            (2 * setup.oxygenAtomMass.val) =
        (momenta.oxygenMolecule.x.val ^ 2 +
              momenta.oxygenMolecule.y.val ^ 2) /
            (2 * (2 * setup.oxygenAtomMass.val)) +
          (momenta.oxygenAtom.x.val ^ 2 +
              momenta.oxygenAtom.y.val ^ 2) /
            (2 * setup.oxygenAtomMass.val)
      have hmol :
          (r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
              (r.val * Real.sin setup.outgoingAngle.val) ^ 2 =
            momenta.oxygenMolecule.x.val ^ 2 +
              momenta.oxygenMolecule.y.val ^ 2 := by
        calc
          (r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
                (r.val * Real.sin setup.outgoingAngle.val) ^ 2 =
              r.val ^ 2 := by
                nlinarith [Real.sin_sq_add_cos_sq setup.outgoingAngle.val]
          _ = _ := hrsq
      have hatom :
          ((photonMomentumMagnitude setup omega).val -
                r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
              (-(r.val * Real.sin setup.outgoingAngle.val)) ^ 2 =
            momenta.oxygenAtom.x.val ^ 2 +
              momenta.oxygenAtom.y.val ^ 2 := by
        rw [hp1x', hp1y']
        nlinarith [hp2ysq]
      rw [hmol, hatom]
    change photonEnergy setup omega =
      addEnergy setup.energyGap (finalKineticEnergy setup momenta) at he_conservation
    rw [← hcost] at he_conservation
    exact he_conservation
  · rintro ⟨r, hrpos, henergy⟩
    change 0 < r.val at hrpos
    have hcost_nonneg : 0 ≤ (reducedKineticCost setup omega r).val := by
      change
        0 ≤
          ((r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
                (r.val * Real.sin setup.outgoingAngle.val) ^ 2) /
              (2 * (2 * setup.oxygenAtomMass.val)) +
            (((photonMomentumMagnitude setup omega).val -
                  r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
                (-(r.val * Real.sin setup.outgoingAngle.val)) ^ 2) /
              (2 * setup.oxygenAtomMass.val)
      have hm4 : 0 < 2 * (2 * setup.oxygenAtomMass.val) := by positivity
      have hm2 : 0 < 2 * setup.oxygenAtomMass.val := by positivity
      exact add_nonneg
        (div_nonneg (by positivity) (le_of_lt hm4))
        (div_nonneg (by positivity) (le_of_lt hm2))
    have henergyVal := congrArg WithDim.val henergy
    change (photonEnergy setup omega).val =
      setup.energyGap.val + (reducedKineticCost setup omega r).val at henergyVal
    have hphotonPos : 0 < (photonEnergy setup omega).val := by linarith
    have homega : IsStrictlyPositive omega := by
      change 0 < omega.val
      change 0 < setup.reducedPlanckConstant.val * omega.val at hphotonPos
      nlinarith
    have hq : 0 < (photonMomentumMagnitude setup omega).val := by
      change
        0 < (photonEnergy setup omega).val / setup.speedOfLight.val
      exact div_pos hphotonPos hc
    let momenta : FragmentMomenta :=
      { oxygenMolecule := outgoingMoleculeMomentumAtAngle setup r
        oxygenAtom := eliminatedAtomicMomentum setup omega r }
    refine ⟨momenta, homega, ?_, ?_, ?_⟩
    · have hnormIncident :
          (momentumNorm (incidentPhotonMomentum setup omega)).val =
            (photonMomentumMagnitude setup omega).val := by
        change Real.sqrt
            ((photonMomentumMagnitude setup omega).val ^ 2 + 0 ^ 2) =
          (photonMomentumMagnitude setup omega).val
        rw [zero_pow (show (2 : ℕ) ≠ 0 from Nat.succ_ne_zero 1), add_zero]
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]
      have hnormOutgoing :
          (momentumNorm (outgoingMoleculeMomentumAtAngle setup r)).val = r.val := by
        change Real.sqrt
            ((r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
              (r.val * Real.sin setup.outgoingAngle.val) ^ 2) = r.val
        rw [show
          (r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
              (r.val * Real.sin setup.outgoingAngle.val) ^ 2 = r.val ^ 2 by
          nlinarith [Real.sin_sq_add_cos_sq setup.outgoingAngle.val]]
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hrpos]
      refine ⟨?_, ?_, ?_⟩
      · change 0 < (photonMomentumMagnitude setup omega).val ^ 2 + 0 ^ 2
        positivity
      · change 0 <
          (r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
            (r.val * Real.sin setup.outgoingAngle.val) ^ 2
        nlinarith [Real.sin_sq_add_cos_sq setup.outgoingAngle.val,
          sq_pos_of_pos hrpos]
      · apply WithDim.ext
        change
          (photonMomentumMagnitude setup omega).val *
              (r.val * Real.cos setup.outgoingAngle.val) + 0 *
                (r.val * Real.sin setup.outgoingAngle.val) =
            (momentumNorm (incidentPhotonMomentum setup omega)).val *
              (momentumNorm (outgoingMoleculeMomentumAtAngle setup r)).val *
                Real.cos setup.outgoingAngle.val
        rw [hnormIncident, hnormOutgoing]
        ring
    · change addMomentum (outgoingMoleculeMomentumAtAngle setup r)
          (eliminatedAtomicMomentum setup omega r) =
        incidentPhotonMomentum setup omega
      apply congrArg₂ PlanarMomentum.mk
      · apply WithDim.ext
        change r.val * Real.cos setup.outgoingAngle.val +
            ((photonMomentumMagnitude setup omega).val -
              r.val * Real.cos setup.outgoingAngle.val) =
          (photonMomentumMagnitude setup omega).val
        ring
      · apply WithDim.ext
        change r.val * Real.sin setup.outgoingAngle.val +
            -(r.val * Real.sin setup.outgoingAngle.val) = 0
        ring
    · change photonEnergy setup omega =
        addEnergy setup.energyGap (reducedKineticCost setup omega r)
      exact henergy

/-- The angular factor for minimization on the closed relaxation `r ≥ 0`.
The positive part of the cosine distinguishes the acute and nonacute
branches. -/
def relaxedAngularFactor (setup : PhotodissociationSetup) : ℝ :=
  3 - 2 * (max (Real.cos setup.outgoingAngle.val) 0) ^ 2

/-- The molecular momentum magnitude minimizing the kinetic cost on the
closed relaxation `r ≥ 0`. -/
def relaxedMinimizingMomentum (setup : PhotodissociationSetup)
    (omega : AngularFrequency) : Momentum :=
  ⟨(2 * (photonMomentumMagnitude setup omega).val / 3) *
    max (Real.cos setup.outgoingAngle.val) 0⟩

/-- The relaxed minimum kinetic energy.  For a right or obtuse angle this is
the non-attained infimum on the physical domain `r > 0`. -/
def relaxedMinimumKineticEnergy (setup : PhotodissociationSetup)
    (omega : AngularFrequency) : Energy :=
  reducedKineticCost setup omega (relaxedMinimizingMomentum setup omega)

/-- The relaxed angular factor lies between one and three. -/
lemma relaxedAngularFactor_bounds (setup : PhotodissociationSetup)
    (hsetup : setup.IsPhysical) :
    1 ≤ relaxedAngularFactor setup ∧ relaxedAngularFactor setup ≤ 3 := by
  have hnonneg : 0 ≤ max (Real.cos setup.outgoingAngle.val) 0 :=
    le_max_right _ _
  have hle : max (Real.cos setup.outgoingAngle.val) 0 ≤ 1 :=
    max_le (Real.cos_le_one _) (by norm_num)
  unfold relaxedAngularFactor
  constructor <;> nlinarith [sq_nonneg (max (Real.cos setup.outgoingAngle.val) 0)]

/-- The reduced kinetic cost in quadratic and completed-square forms. -/
lemma reducedKineticCost_quadratic
    (setup : PhotodissociationSetup) (hsetup : setup.IsPhysical)
    (omega : AngularFrequency) (r : Momentum) :
    let q := (photonMomentumMagnitude setup omega).val
    let mu := Real.cos setup.outgoingAngle.val
    (reducedKineticCost setup omega r).val =
        (3 * r.val ^ 2 - 4 * q * mu * r.val + 2 * q ^ 2) /
          (4 * setup.oxygenAtomMass.val) ∧
      (reducedKineticCost setup omega r).val =
        (3 / (4 * setup.oxygenAtomMass.val)) *
            (r.val - 2 * q * mu / 3) ^ 2 +
          (q ^ 2 / (6 * setup.oxygenAtomMass.val)) * (3 - 2 * mu ^ 2) := by
  dsimp
  rcases hsetup with ⟨_, _, hm, _⟩
  have hm0 : setup.oxygenAtomMass.val ≠ 0 := ne_of_gt hm
  change
    (((r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
              (r.val * Real.sin setup.outgoingAngle.val) ^ 2) /
            (2 * (2 * setup.oxygenAtomMass.val)) +
          (((photonMomentumMagnitude setup omega).val -
                r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
              (-(r.val * Real.sin setup.outgoingAngle.val)) ^ 2) /
            (2 * setup.oxygenAtomMass.val) =
        (3 * r.val ^ 2 -
              4 * (photonMomentumMagnitude setup omega).val *
                Real.cos setup.outgoingAngle.val * r.val +
              2 * (photonMomentumMagnitude setup omega).val ^ 2) /
          (4 * setup.oxygenAtomMass.val)) ∧
      (((r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
              (r.val * Real.sin setup.outgoingAngle.val) ^ 2) /
            (2 * (2 * setup.oxygenAtomMass.val)) +
          (((photonMomentumMagnitude setup omega).val -
                r.val * Real.cos setup.outgoingAngle.val) ^ 2 +
              (-(r.val * Real.sin setup.outgoingAngle.val)) ^ 2) /
            (2 * setup.oxygenAtomMass.val) =
        (3 / (4 * setup.oxygenAtomMass.val)) *
            (r.val -
              2 * (photonMomentumMagnitude setup omega).val *
                Real.cos setup.outgoingAngle.val / 3) ^ 2 +
          ((photonMomentumMagnitude setup omega).val ^ 2 /
              (6 * setup.oxygenAtomMass.val)) *
            (3 - 2 * Real.cos setup.outgoingAngle.val ^ 2))
  have hinv2 :
      (2 * setup.oxygenAtomMass.val)⁻¹ =
        (1 / 2 : ℝ) * setup.oxygenAtomMass.val⁻¹ := by
    rw [mul_inv_rev]
    norm_num
    ring
  have hinv4 :
      (4 * setup.oxygenAtomMass.val)⁻¹ =
        (1 / 4 : ℝ) * setup.oxygenAtomMass.val⁻¹ := by
    rw [mul_inv_rev]
    norm_num
    ring
  have hinv6 :
      (6 * setup.oxygenAtomMass.val)⁻¹ =
        (1 / 6 : ℝ) * setup.oxygenAtomMass.val⁻¹ := by
    rw [mul_inv_rev]
    norm_num
    ring
  have hinv22 :
      (2 * (2 * setup.oxygenAtomMass.val))⁻¹ =
        (1 / 4 : ℝ) * setup.oxygenAtomMass.val⁻¹ := by
    rw [show 2 * (2 * setup.oxygenAtomMass.val) =
        4 * setup.oxygenAtomMass.val by ring, hinv4]
  have hsin_sq :
      Real.sin setup.outgoingAngle.val ^ 2 =
        1 - Real.cos setup.outgoingAngle.val ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq setup.outgoingAngle.val]
  have hrsin_sq :
      (r.val * Real.sin setup.outgoingAngle.val) ^ 2 =
        r.val ^ 2 * (1 - Real.cos setup.outgoingAngle.val ^ 2) := by
    rw [mul_pow, hsin_sq]
  have hneg_rsin_sq :
      (-(r.val * Real.sin setup.outgoingAngle.val)) ^ 2 =
        r.val ^ 2 * (1 - Real.cos setup.outgoingAngle.val ^ 2) := by
    rw [neg_sq, hrsin_sq]
  constructor
  · repeat' rw [div_eq_mul_inv]
    repeat' rw [hinv2]
    repeat' rw [hinv4]
    repeat' rw [hinv22]
    rw [hrsin_sq, hneg_rsin_sq]
    ring
  · repeat' rw [div_eq_mul_inv]
    repeat' rw [hinv2]
    repeat' rw [hinv4]
    repeat' rw [hinv6]
    repeat' rw [hinv22]
    rw [hrsin_sq, hneg_rsin_sq]
    ring

/-- At an acute angle the relaxed minimizer is positive and is the unique
minimizer of the kinetic cost on `r ≥ 0`. -/
lemma reducedKineticCost_minimum_acute
    (setup : PhotodissociationSetup) (hsetup : setup.IsPhysical)
    (omega : AngularFrequency) (homega : IsStrictlyPositive omega)
    (hacute : IsAcuteAngle setup) :
    IsStrictlyPositive (relaxedMinimizingMomentum setup omega) ∧
      (∀ r : Momentum, 0 ≤ r.val →
        (relaxedMinimumKineticEnergy setup omega).val ≤
          (reducedKineticCost setup omega r).val) ∧
      (∀ r : Momentum, 0 ≤ r.val →
        ((reducedKineticCost setup omega r).val =
            (relaxedMinimumKineticEnergy setup omega).val ↔
          r = relaxedMinimizingMomentum setup omega)) := by
  have hhbar := hsetup.1
  have hc := hsetup.2.1
  have hm := hsetup.2.2.1
  change 0 < setup.reducedPlanckConstant.val at hhbar
  change 0 < setup.speedOfLight.val at hc
  change 0 < setup.oxygenAtomMass.val at hm
  change 0 < omega.val at homega
  change 0 < Real.cos setup.outgoingAngle.val at hacute
  have hq : 0 < (photonMomentumMagnitude setup omega).val := by
    change
      0 < setup.reducedPlanckConstant.val * omega.val /
        setup.speedOfLight.val
    exact div_pos (mul_pos hhbar homega) hc
  have hmax : max (Real.cos setup.outgoingAngle.val) 0 =
      Real.cos setup.outgoingAngle.val := max_eq_left (le_of_lt hacute)
  have hr0val : (relaxedMinimizingMomentum setup omega).val =
      2 * (photonMomentumMagnitude setup omega).val *
        Real.cos setup.outgoingAngle.val / 3 := by
    change
      (2 * (photonMomentumMagnitude setup omega).val / 3) *
          max (Real.cos setup.outgoingAngle.val) 0 =
        2 * (photonMomentumMagnitude setup omega).val *
          Real.cos setup.outgoingAngle.val / 3
    rw [hmax]
    ring
  have hr0pos : IsStrictlyPositive (relaxedMinimizingMomentum setup omega) := by
    change 0 < (relaxedMinimizingMomentum setup omega).val
    rw [hr0val]
    positivity
  have hcoef : 0 < 3 / (4 * setup.oxygenAtomMass.val) := by positivity
  refine ⟨hr0pos, ?_, ?_⟩
  · intro r _
    have hr := (reducedKineticCost_quadratic setup hsetup omega r).2
    have hr0 := (reducedKineticCost_quadratic setup hsetup omega
        (relaxedMinimizingMomentum setup omega)).2
    rw [hr0val] at hr0
    have hcenter :
        (2 * (photonMomentumMagnitude setup omega).val *
              Real.cos setup.outgoingAngle.val / 3 -
            2 * (photonMomentumMagnitude setup omega).val *
              Real.cos setup.outgoingAngle.val / 3) ^ 2 = 0 := by ring
    rw [hcenter, mul_zero, zero_add] at hr0
    change (reducedKineticCost setup omega
        (relaxedMinimizingMomentum setup omega)).val ≤
      (reducedKineticCost setup omega r).val
    have hsquare : 0 ≤ 3 / (4 * setup.oxygenAtomMass.val) *
        (r.val - 2 * (photonMomentumMagnitude setup omega).val *
          Real.cos setup.outgoingAngle.val / 3) ^ 2 :=
      mul_nonneg (le_of_lt hcoef) (sq_nonneg _)
    linarith
  · intro r _
    constructor
    · intro heq
      have hr := (reducedKineticCost_quadratic setup hsetup omega r).2
      have hr0 := (reducedKineticCost_quadratic setup hsetup omega
          (relaxedMinimizingMomentum setup omega)).2
      rw [hr0val] at hr0
      have hcenter :
          (2 * (photonMomentumMagnitude setup omega).val *
                Real.cos setup.outgoingAngle.val / 3 -
              2 * (photonMomentumMagnitude setup omega).val *
                Real.cos setup.outgoingAngle.val / 3) ^ 2 = 0 := by ring
      rw [hcenter, mul_zero, zero_add] at hr0
      change (reducedKineticCost setup omega r).val =
        (reducedKineticCost setup omega
          (relaxedMinimizingMomentum setup omega)).val at heq
      apply WithDim.ext
      have hprod : 3 / (4 * setup.oxygenAtomMass.val) *
          (r.val - 2 * (photonMomentumMagnitude setup omega).val *
            Real.cos setup.outgoingAngle.val / 3) ^ 2 = 0 := by
        linarith
      have hsquare :
          (r.val - 2 * (photonMomentumMagnitude setup omega).val *
            Real.cos setup.outgoingAngle.val / 3) ^ 2 = 0 :=
        (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hcoef)
      rw [hr0val]
      nlinarith
    · rintro rfl
      rfl

/-- At a right or obtuse angle the relaxed minimizer is zero.  Its cost is
the strict, non-attained infimum over physical momenta `r > 0`, and positive
momenta approach it arbitrarily closely. -/
lemma reducedKineticCost_infimum_nonacute
    (setup : PhotodissociationSetup) (hsetup : setup.IsPhysical)
    (omega : AngularFrequency) (homega : IsStrictlyPositive omega)
    (hnonacute : IsRightOrObtuseAngle setup) :
    relaxedMinimizingMomentum setup omega = (0 : Momentum) ∧
      (relaxedMinimumKineticEnergy setup omega).val =
        (photonMomentumMagnitude setup omega).val ^ 2 /
          (2 * setup.oxygenAtomMass.val) ∧
      (∀ r : Momentum, IsStrictlyPositive r →
        (relaxedMinimumKineticEnergy setup omega).val <
          (reducedKineticCost setup omega r).val) ∧
      (∀ epsilon : ℝ, 0 < epsilon →
        ∃ r : Momentum,
          IsStrictlyPositive r ∧
            (relaxedMinimumKineticEnergy setup omega).val <
              (reducedKineticCost setup omega r).val ∧
            (reducedKineticCost setup omega r).val <
              (relaxedMinimumKineticEnergy setup omega).val + epsilon) := by
  have hhbar := hsetup.1
  have hc := hsetup.2.1
  have hm := hsetup.2.2.1
  change 0 < setup.reducedPlanckConstant.val at hhbar
  change 0 < setup.speedOfLight.val at hc
  change 0 < setup.oxygenAtomMass.val at hm
  change 0 < omega.val at homega
  change Real.cos setup.outgoingAngle.val ≤ 0 at hnonacute
  have hq : 0 < (photonMomentumMagnitude setup omega).val := by
    change
      0 < setup.reducedPlanckConstant.val * omega.val /
        setup.speedOfLight.val
    exact div_pos (mul_pos hhbar homega) hc
  have hmax : max (Real.cos setup.outgoingAngle.val) 0 = 0 :=
    max_eq_right hnonacute
  have hr0 : relaxedMinimizingMomentum setup omega = (0 : Momentum) := by
    apply WithDim.ext
    change
      (2 * (photonMomentumMagnitude setup omega).val / 3) *
          max (Real.cos setup.outgoingAngle.val) 0 = 0
    rw [hmax]
    ring
  have hden : 0 < 4 * setup.oxygenAtomMass.val := mul_pos (by norm_num) hm
  have hinv2m :
      (2 * setup.oxygenAtomMass.val)⁻¹ =
        (1 / 2 : ℝ) * setup.oxygenAtomMass.val⁻¹ := by
    rw [mul_inv_rev]
    norm_num
    ring
  have hinv4m :
      (4 * setup.oxygenAtomMass.val)⁻¹ =
        (1 / 4 : ℝ) * setup.oxygenAtomMass.val⁻¹ := by
    rw [mul_inv_rev]
    norm_num
    ring
  have hzero := (reducedKineticCost_quadratic setup hsetup omega (0 : Momentum)).1
  rw [WithDim.val_zero,
    zero_pow (show (2 : ℕ) ≠ 0 from Nat.succ_ne_zero 1),
    mul_zero, mul_zero, sub_zero, zero_add] at hzero
  have hminval : (relaxedMinimumKineticEnergy setup omega).val =
      (photonMomentumMagnitude setup omega).val ^ 2 /
        (2 * setup.oxygenAtomMass.val) := by
    change (reducedKineticCost setup omega
      (relaxedMinimizingMomentum setup omega)).val = _
    rw [hr0]
    rw [hzero]
    repeat' rw [div_eq_mul_inv]
    repeat' rw [hinv2m]
    repeat' rw [hinv4m]
    ring
  have hstrict : ∀ r : Momentum, IsStrictlyPositive r →
      (relaxedMinimumKineticEnergy setup omega).val <
        (reducedKineticCost setup omega r).val := by
    intro r hrpos
    change 0 < r.val at hrpos
    have hr := (reducedKineticCost_quadratic setup hsetup omega r).1
    have hnum : 0 <
        3 * r.val ^ 2 -
          4 * (photonMomentumMagnitude setup omega).val *
            Real.cos setup.outgoingAngle.val * r.val := by
      have hqmu :
          (photonMomentumMagnitude setup omega).val *
            Real.cos setup.outgoingAngle.val ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hq) hnonacute
      nlinarith [sq_pos_of_pos hrpos]
    rw [hminval, hr]
    rw [show (photonMomentumMagnitude setup omega).val ^ 2 /
          (2 * setup.oxygenAtomMass.val) =
        (2 * (photonMomentumMagnitude setup omega).val ^ 2) /
          (4 * setup.oxygenAtomMass.val) by
      repeat' rw [div_eq_mul_inv]
      repeat' rw [hinv2m]
      repeat' rw [hinv4m]
      ring]
    apply (div_lt_div_iff_of_pos_right hden).2
    nlinarith
  refine ⟨hr0, hminval, hstrict, ?_⟩
  intro epsilon hepsilon
  let C : ℝ :=
    (3 - 4 * (photonMomentumMagnitude setup omega).val *
      Real.cos setup.outgoingAngle.val) /
        (4 * setup.oxygenAtomMass.val)
  have hC : 0 < C := by
    dsimp [C]
    apply div_pos
    · have hqmu :
          (photonMomentumMagnitude setup omega).val *
            Real.cos setup.outgoingAngle.val ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hq) hnonacute
      nlinarith
    · exact hden
  let x : ℝ := min 1 (epsilon / (2 * C))
  have hxpos : 0 < x := by
    dsimp [x]
    exact lt_min (by norm_num) (div_pos hepsilon (mul_pos (by norm_num) hC))
  have hxle1 : x ≤ 1 := by
    dsimp [x]
    exact min_le_left _ _
  have hxlediv : x ≤ epsilon / (2 * C) := by
    dsimp [x]
    exact min_le_right _ _
  have hxsq : x ^ 2 ≤ x := by nlinarith [sq_nonneg x]
  have hpoly_le :
      (3 * x ^ 2 - 4 * (photonMomentumMagnitude setup omega).val *
          Real.cos setup.outgoingAngle.val * x) /
          (4 * setup.oxygenAtomMass.val) ≤ C * x := by
    have hnumle :
        3 * x ^ 2 - 4 * (photonMomentumMagnitude setup omega).val *
            Real.cos setup.outgoingAngle.val * x ≤
          (3 - 4 * (photonMomentumMagnitude setup omega).val *
            Real.cos setup.outgoingAngle.val) * x := by
      nlinarith
    rw [show C * x =
        ((3 - 4 * (photonMomentumMagnitude setup omega).val *
          Real.cos setup.outgoingAngle.val) * x) /
            (4 * setup.oxygenAtomMass.val) by
      dsimp [C]
      ring]
    exact (div_le_div_iff_of_pos_right hden).2 hnumle
  have hCx : C * x ≤ epsilon / 2 := by
    calc
      C * x ≤ C * (epsilon / (2 * C)) :=
        mul_le_mul_of_nonneg_left hxlediv (le_of_lt hC)
      _ = epsilon / 2 := by
        rw [div_eq_mul_inv, mul_inv_rev]
        rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
        calc
          C * (epsilon * (C⁻¹ * (1 / 2))) =
              (C * C⁻¹) * (epsilon / 2) := by ring
          _ = epsilon / 2 := by rw [mul_inv_cancel₀ hC.ne', one_mul]
  have hpoly :
      (3 * x ^ 2 - 4 * (photonMomentumMagnitude setup omega).val *
          Real.cos setup.outgoingAngle.val * x) /
          (4 * setup.oxygenAtomMass.val) < epsilon := by
    nlinarith
  refine ⟨⟨x⟩, ?_, hstrict ⟨x⟩ ?_, ?_⟩
  · exact hxpos
  · exact hxpos
  · have hxcost :=
      (reducedKineticCost_quadratic setup hsetup omega (⟨x⟩ : Momentum)).1
    change (reducedKineticCost setup omega (⟨x⟩ : Momentum)).val <
      (relaxedMinimumKineticEnergy setup omega).val + epsilon
    rw [hminval, hminval] at *
    rw [hxcost]
    have hsplit :
        (3 * x ^ 2 - 4 * (photonMomentumMagnitude setup omega).val *
              Real.cos setup.outgoingAngle.val * x +
            2 * (photonMomentumMagnitude setup omega).val ^ 2) /
            (4 * setup.oxygenAtomMass.val) =
          (photonMomentumMagnitude setup omega).val ^ 2 /
              (2 * setup.oxygenAtomMass.val) +
            (3 * x ^ 2 - 4 * (photonMomentumMagnitude setup omega).val *
              Real.cos setup.outgoingAngle.val * x) /
                (4 * setup.oxygenAtomMass.val) := by
      repeat' rw [div_eq_mul_inv]
      repeat' rw [hinv2m]
      repeat' rw [hinv4m]
      ring
    rw [hsplit]
    linarith

/-- Exact range of the reduced kinetic cost on positive molecular momentum
magnitudes, with the correct weak/strict endpoint for the two angle branches.
-/
lemma reducedKineticCost_positive_range
    (setup : PhotodissociationSetup) (hsetup : setup.IsPhysical)
    (omega : AngularFrequency) (homega : IsStrictlyPositive omega)
    (energyValue : Energy) :
    (IsAcuteAngle setup →
      ((∃ r : Momentum,
          IsStrictlyPositive r ∧
            reducedKineticCost setup omega r = energyValue) ↔
        (relaxedMinimumKineticEnergy setup omega).val ≤ energyValue.val)) ∧
      (IsRightOrObtuseAngle setup →
        ((∃ r : Momentum,
            IsStrictlyPositive r ∧
              reducedKineticCost setup omega r = energyValue) ↔
          (relaxedMinimumKineticEnergy setup omega).val < energyValue.val)) := by
  have hm := hsetup.2.2.1
  change 0 < setup.oxygenAtomMass.val at hm
  have hhbar := hsetup.1
  have hc := hsetup.2.1
  change 0 < setup.reducedPlanckConstant.val at hhbar
  change 0 < setup.speedOfLight.val at hc
  change 0 < omega.val at homega
  have h4m : 4 * setup.oxygenAtomMass.val ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) hm)
  have hinv2m :
      (2 * setup.oxygenAtomMass.val)⁻¹ =
        (1 / 2 : ℝ) * setup.oxygenAtomMass.val⁻¹ := by
    rw [mul_inv_rev]
    norm_num
    ring
  have hinv4m :
      (4 * setup.oxygenAtomMass.val)⁻¹ =
        (1 / 4 : ℝ) * setup.oxygenAtomMass.val⁻¹ := by
    rw [mul_inv_rev]
    norm_num
    ring
  have hq : 0 < (photonMomentumMagnitude setup omega).val := by
    change
      0 < setup.reducedPlanckConstant.val * omega.val /
        setup.speedOfLight.val
    exact div_pos (mul_pos hhbar homega) hc
  constructor
  · intro hacute
    have hacuteData :=
      reducedKineticCost_minimum_acute setup hsetup omega homega hacute
    constructor
    · rintro ⟨r, hrpos, hcost⟩
      have hle := hacuteData.2.1 r (le_of_lt hrpos)
      have hval := congrArg WithDim.val hcost
      linarith
    · intro hle
      change 0 < Real.cos setup.outgoingAngle.val at hacute
      have hmax : max (Real.cos setup.outgoingAngle.val) 0 =
          Real.cos setup.outgoingAngle.val := max_eq_left (le_of_lt hacute)
      have hr0val : (relaxedMinimizingMomentum setup omega).val =
          2 * (photonMomentumMagnitude setup omega).val *
            Real.cos setup.outgoingAngle.val / 3 := by
        change
          (2 * (photonMomentumMagnitude setup omega).val / 3) *
              max (Real.cos setup.outgoingAngle.val) 0 =
            2 * (photonMomentumMagnitude setup omega).val *
              Real.cos setup.outgoingAngle.val / 3
        rw [hmax]
        ring
      let d : ℝ := energyValue.val -
        (relaxedMinimumKineticEnergy setup omega).val
      have hd : 0 ≤ d := by dsimp [d]; linarith
      let z : ℝ := 4 * setup.oxygenAtomMass.val * d / 3
      have hz : 0 ≤ z := by dsimp [z]; positivity
      have hsq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz
      let r : Momentum :=
        ⟨(relaxedMinimizingMomentum setup omega).val + Real.sqrt z⟩
      have hrpos : IsStrictlyPositive r := by
        change 0 < (relaxedMinimizingMomentum setup omega).val + Real.sqrt z
        have hr0pos := hacuteData.1
        change 0 < (relaxedMinimizingMomentum setup omega).val at hr0pos
        nlinarith [Real.sqrt_nonneg z]
      refine ⟨r, hrpos, ?_⟩
      apply WithDim.ext
      have hr := (reducedKineticCost_quadratic setup hsetup omega r).2
      have hr0 := (reducedKineticCost_quadratic setup hsetup omega
        (relaxedMinimizingMomentum setup omega)).2
      change (relaxedMinimumKineticEnergy setup omega).val = _ at hr0
      rw [hr0val] at hr0
      have hcenter :
          (2 * (photonMomentumMagnitude setup omega).val *
                Real.cos setup.outgoingAngle.val / 3 -
              2 * (photonMomentumMagnitude setup omega).val *
                Real.cos setup.outgoingAngle.val / 3) ^ 2 = 0 := by ring
      rw [hcenter, mul_zero, zero_add] at hr0
      dsimp [r] at hr
      rw [hr0val] at hr
      have hcoef :
          3 / (4 * setup.oxygenAtomMass.val) * z = d := by
        dsimp [z]
        repeat' rw [div_eq_mul_inv]
        calc
          3 * (4 * setup.oxygenAtomMass.val)⁻¹ *
                (4 * setup.oxygenAtomMass.val * d * 3⁻¹) =
              ((4 * setup.oxygenAtomMass.val)⁻¹ *
                  (4 * setup.oxygenAtomMass.val)) *
                (3 * 3⁻¹) * d := by ring
          _ = d := by
            rw [inv_mul_cancel₀ h4m, mul_inv_cancel₀ (by norm_num : (3 : ℝ) ≠ 0)]
            ring
      have hshift :
          (2 * (photonMomentumMagnitude setup omega).val *
                Real.cos setup.outgoingAngle.val / 3 + Real.sqrt z -
              2 * (photonMomentumMagnitude setup omega).val *
                Real.cos setup.outgoingAngle.val / 3) ^ 2 = z := by
        rw [show
          2 * (photonMomentumMagnitude setup omega).val *
                Real.cos setup.outgoingAngle.val / 3 + Real.sqrt z -
              2 * (photonMomentumMagnitude setup omega).val *
                Real.cos setup.outgoingAngle.val / 3 = Real.sqrt z by ring]
        exact hsq
      rw [hshift] at hr
      have hcostval :
          (reducedKineticCost setup omega r).val =
            (relaxedMinimumKineticEnergy setup omega).val + d := by
        dsimp [r]
        rw [hr0val]
        nlinarith
      dsimp [d] at hcostval
      linarith
  · intro hnonacute
    have hnonacuteData :=
      reducedKineticCost_infimum_nonacute setup hsetup omega homega hnonacute
    constructor
    · rintro ⟨r, hrpos, hcost⟩
      have hlt := hnonacuteData.2.2.1 r hrpos
      have hval := congrArg WithDim.val hcost
      linarith
    · intro hlt
      change Real.cos setup.outgoingAngle.val ≤ 0 at hnonacute
      let d : ℝ := energyValue.val -
        (relaxedMinimumKineticEnergy setup omega).val
      have hd : 0 < d := by dsimp [d]; linarith
      let a : ℝ := 2 * (photonMomentumMagnitude setup omega).val *
        Real.cos setup.outgoingAngle.val / 3
      have ha : a ≤ 0 := by
        dsimp [a]
        have hqmu :
            (photonMomentumMagnitude setup omega).val *
              Real.cos setup.outgoingAngle.val ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hq) hnonacute
        nlinarith
      let z : ℝ := a ^ 2 + 4 * setup.oxygenAtomMass.val * d / 3
      have hz : 0 ≤ z := by
        dsimp [z]
        positivity
      have hsq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz
      have hzgt : a ^ 2 < z := by
        have hterm : 0 < 4 * setup.oxygenAtomMass.val * d / 3 := by
          positivity
        dsimp [z]
        linarith
      have hroot : -a < Real.sqrt z := by
        have hsnonneg := Real.sqrt_nonneg z
        nlinarith [sq_nonneg (Real.sqrt z + (-a))]
      let r : Momentum := ⟨a + Real.sqrt z⟩
      have hrpos : IsStrictlyPositive r := by
        change 0 < a + Real.sqrt z
        linarith
      refine ⟨r, hrpos, ?_⟩
      apply WithDim.ext
      have hr := (reducedKineticCost_quadratic setup hsetup omega r).1
      have hdiff :
          (3 * r.val ^ 2 -
              4 * (photonMomentumMagnitude setup omega).val *
                Real.cos setup.outgoingAngle.val * r.val) /
              (4 * setup.oxygenAtomMass.val) = d := by
        dsimp [r]
        rw [show 4 * (photonMomentumMagnitude setup omega).val *
              Real.cos setup.outgoingAngle.val = 6 * a by
          dsimp [a]
          ring]
        rw [show (a + Real.sqrt z) ^ 2 =
            a ^ 2 + 2 * a * Real.sqrt z + (Real.sqrt z) ^ 2 by ring]
        rw [hsq]
        dsimp [z]
        apply (div_eq_iff h4m).2
        ring
      have hsplit :
          (3 * r.val ^ 2 -
                4 * (photonMomentumMagnitude setup omega).val *
                  Real.cos setup.outgoingAngle.val * r.val +
              2 * (photonMomentumMagnitude setup omega).val ^ 2) /
              (4 * setup.oxygenAtomMass.val) =
            (photonMomentumMagnitude setup omega).val ^ 2 /
                (2 * setup.oxygenAtomMass.val) + d := by
        rw [← hdiff]
        repeat' rw [div_eq_mul_inv]
        repeat' rw [hinv2m]
        repeat' rw [hinv4m]
        ring
      rw [hr, hsplit]
      dsimp [d]
      linarith [hnonacuteData.2.1]

/-- The conservation boundary obtained by setting the fragment kinetic cost
to its constrained minimum or infimum. -/
def ConservationBoundary (setup : PhotodissociationSetup)
    (omega : AngularFrequency) : Prop :=
  photonEnergy setup omega =
    addEnergy setup.energyGap (relaxedMinimumKineticEnergy setup omega)

/-- The increasing, lower physical branch of the concave available-energy
margin. -/
def OnLowerPhysicalBranch (setup : PhotodissociationSetup)
    (omega : AngularFrequency) : Prop :=
  0 < (photonEnergy setup omega).val ∧
    relaxedAngularFactor setup * (photonEnergy setup omega).val <
      3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2

/-- Parameter-only domain in which the relaxed conservation boundary has two
distinct roots and hence a unique lower physical branch. -/
def SubcriticalParameters (setup : PhotodissociationSetup) : Prop :=
  2 * relaxedAngularFactor setup * setup.energyGap.val <
    3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2

/-- Answer-free threshold predicate.  It records the lower conservation
boundary intrinsically and requires it to bound every exact feasible event.
It does not require boundary attainment, which fails for nonacute angles. -/
def MinimumFrequencySolution (setup : PhotodissociationSetup)
    (omegaMin : AngularFrequency) : Prop :=
  ConservationBoundary setup omegaMin ∧
    OnLowerPhysicalBranch setup omegaMin ∧
    ∀ nu : AngularFrequency,
      DissociationFeasible setup nu → omegaMin.val ≤ nu.val

/-- Feasibility is exactly the appropriate side of the relaxed boundary:
weak at an acute angle and strict at a right or obtuse angle. -/
lemma dissociationFeasible_iff_relaxedMinimum
    (setup : PhotodissociationSetup) (hsetup : setup.IsPhysical)
    (omega : AngularFrequency) :
    (IsAcuteAngle setup →
      (DissociationFeasible setup omega ↔
        IsStrictlyPositive omega ∧
          (addEnergy setup.energyGap
              (relaxedMinimumKineticEnergy setup omega)).val ≤
            (photonEnergy setup omega).val)) ∧
      (IsRightOrObtuseAngle setup →
        (DissociationFeasible setup omega ↔
          IsStrictlyPositive omega ∧
            (addEnergy setup.energyGap
                (relaxedMinimumKineticEnergy setup omega)).val <
              (photonEnergy setup omega).val)) := by
  let available : Energy :=
    subEnergy (photonEnergy setup omega) setup.energyGap
  have hscalar :=
    dissociationFeasible_iff_reducedKineticCost setup hsetup omega
  constructor
  · intro hacute
    constructor
    · intro hfeasible
      have homega : IsStrictlyPositive omega := by
        rcases hfeasible with ⟨momenta, houtcome⟩
        exact houtcome.1
      rcases hscalar.mp hfeasible with ⟨r, hrpos, henergy⟩
      have henergyVal := congrArg WithDim.val henergy
      change (photonEnergy setup omega).val = setup.energyGap.val +
        (reducedKineticCost setup omega r).val at henergyVal
      have hcostAvailable : reducedKineticCost setup omega r = available := by
        apply WithDim.ext
        dsimp [available, subEnergy]
        linarith
      have hrange := (reducedKineticCost_positive_range setup hsetup omega
        homega available).1 hacute
      have hminimum := hrange.mp ⟨r, hrpos, hcostAvailable⟩
      refine ⟨homega, ?_⟩
      dsimp [available, subEnergy] at hminimum
      change setup.energyGap.val +
          (relaxedMinimumKineticEnergy setup omega).val ≤
        (photonEnergy setup omega).val
      linarith
    · rintro ⟨homega, hminimum⟩
      have hrange := (reducedKineticCost_positive_range setup hsetup omega
        homega available).1 hacute
      have havailable :
          (relaxedMinimumKineticEnergy setup omega).val ≤ available.val := by
        dsimp [available, subEnergy]
        change setup.energyGap.val +
            (relaxedMinimumKineticEnergy setup omega).val ≤
          (photonEnergy setup omega).val at hminimum
        linarith
      rcases hrange.mpr havailable with ⟨r, hrpos, hcost⟩
      apply hscalar.mpr
      refine ⟨r, hrpos, ?_⟩
      apply WithDim.ext
      have hcostVal := congrArg WithDim.val hcost
      dsimp [available, subEnergy] at hcostVal
      change (photonEnergy setup omega).val = setup.energyGap.val +
        (reducedKineticCost setup omega r).val
      linarith
  · intro hnonacute
    constructor
    · intro hfeasible
      have homega : IsStrictlyPositive omega := by
        rcases hfeasible with ⟨momenta, houtcome⟩
        exact houtcome.1
      rcases hscalar.mp hfeasible with ⟨r, hrpos, henergy⟩
      have henergyVal := congrArg WithDim.val henergy
      change (photonEnergy setup omega).val = setup.energyGap.val +
        (reducedKineticCost setup omega r).val at henergyVal
      have hcostAvailable : reducedKineticCost setup omega r = available := by
        apply WithDim.ext
        dsimp [available, subEnergy]
        linarith
      have hrange := (reducedKineticCost_positive_range setup hsetup omega
        homega available).2 hnonacute
      have hminimum := hrange.mp ⟨r, hrpos, hcostAvailable⟩
      refine ⟨homega, ?_⟩
      dsimp [available, subEnergy] at hminimum
      change setup.energyGap.val +
          (relaxedMinimumKineticEnergy setup omega).val <
        (photonEnergy setup omega).val
      linarith
    · rintro ⟨homega, hminimum⟩
      have hrange := (reducedKineticCost_positive_range setup hsetup omega
        homega available).2 hnonacute
      have havailable :
          (relaxedMinimumKineticEnergy setup omega).val < available.val := by
        dsimp [available, subEnergy]
        change setup.energyGap.val +
            (relaxedMinimumKineticEnergy setup omega).val <
          (photonEnergy setup omega).val at hminimum
        linarith
      rcases hrange.mpr havailable with ⟨r, hrpos, hcost⟩
      apply hscalar.mpr
      refine ⟨r, hrpos, ?_⟩
      apply WithDim.ext
      have hcostVal := congrArg WithDim.val hcost
      dsimp [available, subEnergy] at hcostVal
      change (photonEnergy setup omega).val = setup.energyGap.val +
        (reducedKineticCost setup omega r).val
      linarith

/-- A physical subcritical setup has exactly one conservation-boundary
frequency on the lower physical branch. -/
lemma existsUnique_lowerBoundary
    (setup : PhotodissociationSetup) (hsetup : setup.IsPhysical)
    (hsubcritical : SubcriticalParameters setup) :
    ∃! omega0 : AngularFrequency,
      ConservationBoundary setup omega0 ∧ OnLowerPhysicalBranch setup omega0 := by
  have hhbar := hsetup.1
  have hc := hsetup.2.1
  have hm := hsetup.2.2.1
  have hgap := hsetup.2.2.2.2.1
  change 0 < setup.reducedPlanckConstant.val at hhbar
  change 0 < setup.speedOfLight.val at hc
  change 0 < setup.oxygenAtomMass.val at hm
  change 0 < setup.energyGap.val at hgap
  have hA := (relaxedAngularFactor_bounds setup hsetup).1
  have hApos : 0 < relaxedAngularFactor setup := lt_of_lt_of_le (by norm_num) hA
  have hinv4m :
      (4 * setup.oxygenAtomMass.val)⁻¹ =
        (1 / 4 : ℝ) * setup.oxygenAtomMass.val⁻¹ := by
    rw [mul_inv_rev]
    norm_num
    ring
  have hinv6m :
      (6 * setup.oxygenAtomMass.val)⁻¹ =
        (1 / 6 : ℝ) * setup.oxygenAtomMass.val⁻¹ := by
    rw [mul_inv_rev]
    norm_num
    ring
  have hinv3mc2 :
      (3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2)⁻¹ =
        (1 / 3 : ℝ) * setup.oxygenAtomMass.val⁻¹ *
          setup.speedOfLight.val⁻¹ ^ 2 := by
    rw [mul_inv_rev, ← inv_pow, mul_inv_rev]
    norm_num
    ring
  have hinv6mc2 :
      (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2)⁻¹ =
        (1 / 6 : ℝ) * setup.oxygenAtomMass.val⁻¹ *
          setup.speedOfLight.val⁻¹ ^ 2 := by
    rw [mul_inv_rev, ← inv_pow, mul_inv_rev]
    norm_num
    ring
  have hKformula (w : AngularFrequency) :
      (relaxedMinimumKineticEnergy setup w).val =
        relaxedAngularFactor setup * (photonEnergy setup w).val ^ 2 /
          (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) := by
    by_cases hmu : Real.cos setup.outgoingAngle.val ≤ 0
    · have hmax : max (Real.cos setup.outgoingAngle.val) 0 = 0 :=
        max_eq_right hmu
      have hr0 : relaxedMinimizingMomentum setup w = (0 : Momentum) := by
        apply WithDim.ext
        change
          (2 * (photonMomentumMagnitude setup w).val / 3) *
              max (Real.cos setup.outgoingAngle.val) 0 = 0
        rw [hmax]
        ring
      have hquad :=
        (reducedKineticCost_quadratic setup hsetup w (0 : Momentum)).1
      rw [WithDim.val_zero,
        zero_pow (show (2 : ℕ) ≠ 0 from Nat.succ_ne_zero 1),
        mul_zero, mul_zero, sub_zero, zero_add] at hquad
      change (reducedKineticCost setup w
        (relaxedMinimizingMomentum setup w)).val = _
      rw [hr0, hquad]
      rw [show relaxedAngularFactor setup = 3 by
        change
          3 - 2 * max (Real.cos setup.outgoingAngle.val) 0 ^ 2 = 3
        rw [hmax]
        ring]
      change
        2 * ((photonEnergy setup w).val / setup.speedOfLight.val) ^ 2 /
              (4 * setup.oxygenAtomMass.val) = _
      repeat' rw [div_eq_mul_inv]
      repeat' rw [hinv4m]
      repeat' rw [hinv6mc2]
      ring
    · have hmu0 : 0 ≤ Real.cos setup.outgoingAngle.val := le_of_not_ge hmu
      have hmax : max (Real.cos setup.outgoingAngle.val) 0 =
          Real.cos setup.outgoingAngle.val := max_eq_left hmu0
      have hr0val : (relaxedMinimizingMomentum setup w).val =
          2 * (photonMomentumMagnitude setup w).val *
            Real.cos setup.outgoingAngle.val / 3 := by
        change
          (2 * (photonMomentumMagnitude setup w).val / 3) *
              max (Real.cos setup.outgoingAngle.val) 0 =
            2 * (photonMomentumMagnitude setup w).val *
              Real.cos setup.outgoingAngle.val / 3
        rw [hmax]
        ring
      have hquad := (reducedKineticCost_quadratic setup hsetup w
        (relaxedMinimizingMomentum setup w)).2
      change (relaxedMinimumKineticEnergy setup w).val = _ at hquad
      rw [hr0val] at hquad
      have hcenter :
          (2 * (photonMomentumMagnitude setup w).val *
                Real.cos setup.outgoingAngle.val / 3 -
              2 * (photonMomentumMagnitude setup w).val *
                Real.cos setup.outgoingAngle.val / 3) ^ 2 = 0 := by ring
      rw [hcenter, mul_zero, zero_add] at hquad
      rw [hquad]
      rw [show relaxedAngularFactor setup =
          3 - 2 * Real.cos setup.outgoingAngle.val ^ 2 by
        change
          3 - 2 * max (Real.cos setup.outgoingAngle.val) 0 ^ 2 =
            3 - 2 * Real.cos setup.outgoingAngle.val ^ 2
        rw [hmax]]
      change
        ((photonEnergy setup w).val / setup.speedOfLight.val) ^ 2 /
              (6 * setup.oxygenAtomMass.val) *
            (3 - 2 * Real.cos setup.outgoingAngle.val ^ 2) =
          (3 - 2 * Real.cos setup.outgoingAngle.val ^ 2) *
              (photonEnergy setup w).val ^ 2 /
            (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2)
      repeat' rw [div_eq_mul_inv]
      repeat' rw [hinv6m]
      repeat' rw [hinv6mc2]
      ring
  let k : ℝ := relaxedAngularFactor setup /
    (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2)
  have hk : 0 < k := by dsimp [k]; positivity
  have hden : 0 < 6 * setup.oxygenAtomMass.val *
      setup.speedOfLight.val ^ 2 := by positivity
  have hsub : 2 * relaxedAngularFactor setup * setup.energyGap.val <
      3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2 :=
    hsubcritical
  have hfour : 4 * k * setup.energyGap.val < 1 := by
    rw [show 4 * k * setup.energyGap.val =
        (2 * relaxedAngularFactor setup * setup.energyGap.val) /
          (3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) by
      dsimp [k]
      repeat' rw [div_eq_mul_inv]
      repeat' rw [hinv3mc2]
      repeat' rw [hinv6mc2]
      ring]
    exact (div_lt_one (by positivity)).2 hsub
  let D : ℝ := 1 - 4 * k * setup.energyGap.val
  have hD : 0 < D := by dsimp [D]; linarith
  have hDlt : D < 1 := by
    have : 0 < 4 * k * setup.energyGap.val := by positivity
    dsimp [D]
    linarith
  have hsqrtPos : 0 < Real.sqrt D := Real.sqrt_pos.2 hD
  have hsqrtLt : Real.sqrt D < 1 := by
    nlinarith [Real.sq_sqrt (le_of_lt hD)]
  let x0 : ℝ := (1 - Real.sqrt D) / (2 * k)
  have hx0 : 0 < x0 := by dsimp [x0]; positivity
  have hx0vertex : x0 < 1 / (2 * k) := by
    dsimp [x0]
    apply (div_lt_div_iff_of_pos_right (mul_pos (by norm_num) hk)).2
    linarith
  have hx0root : x0 = setup.energyGap.val + k * x0 ^ 2 := by
    have hsqD := Real.sq_sqrt (le_of_lt hD)
    have hxlin :
        2 * k * x0 = 1 - Real.sqrt D := by
      dsimp [x0]
      exact
        mul_div_cancel₀ (b := 2 * k) (1 - Real.sqrt D)
          (mul_ne_zero (by norm_num) hk.ne')
    have hxlin_sq := congrArg (fun y : ℝ ↦ y ^ 2) hxlin
    dsimp [D] at hsqD
    apply mul_left_cancel₀ (a := k) hk.ne'
    nlinarith only [hxlin, hxlin_sq, hsqD]
  let omega0 : AngularFrequency := ⟨x0 / setup.reducedPlanckConstant.val⟩
  have henergy0 : (photonEnergy setup omega0).val = x0 := by
    change
      setup.reducedPlanckConstant.val *
          (x0 / setup.reducedPlanckConstant.val) = x0
    exact mul_div_cancel₀ x0 hhbar.ne'
  have hbranchUpper0 : relaxedAngularFactor setup * x0 <
      3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2 := by
    have hkx : k * x0 < 1 / 2 := by
      have := mul_lt_mul_of_pos_left hx0vertex hk
      have hhalf : k * (1 / (2 * k)) = 1 / 2 := by
        rw [div_eq_mul_inv, mul_inv_rev]
        calc
          k * (1 * (k⁻¹ * 2⁻¹)) =
              (k * k⁻¹) * (1 / 2) := by ring
          _ = 1 / 2 := by rw [mul_inv_cancel₀ hk.ne', one_mul]
      rw [hhalf] at this
      exact this
    rw [show relaxedAngularFactor setup * x0 =
        (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) *
          (k * x0) by
      dsimp [k]
      symm
      calc
        (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) *
              ((relaxedAngularFactor setup /
                  (6 * setup.oxygenAtomMass.val *
                    setup.speedOfLight.val ^ 2)) * x0) =
            ((6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) *
                (relaxedAngularFactor setup /
                  (6 * setup.oxygenAtomMass.val *
                    setup.speedOfLight.val ^ 2))) * x0 := by ring
        _ = relaxedAngularFactor setup * x0 := by
          rw [mul_div_cancel₀ (relaxedAngularFactor setup) hden.ne']]
    nlinarith [show 0 < setup.oxygenAtomMass.val *
      setup.speedOfLight.val ^ 2 by positivity]
  refine ⟨omega0, ⟨?_, ?_⟩, ?_⟩
  · apply WithDim.ext
    change (photonEnergy setup omega0).val = setup.energyGap.val +
      (relaxedMinimumKineticEnergy setup omega0).val
    rw [hKformula, henergy0]
    rw [show relaxedAngularFactor setup * x0 ^ 2 /
          (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) =
        k * x0 ^ 2 by
      dsimp [k]
      ring]
    exact hx0root
  · exact ⟨henergy0 ▸ hx0, henergy0 ▸ hbranchUpper0⟩
  · intro w hw
    have hboundaryVal := congrArg WithDim.val hw.1
    change (photonEnergy setup w).val = setup.energyGap.val +
      (relaxedMinimumKineticEnergy setup w).val at hboundaryVal
    rw [hKformula] at hboundaryVal
    rw [show relaxedAngularFactor setup * (photonEnergy setup w).val ^ 2 /
          (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) =
        k * (photonEnergy setup w).val ^ 2 by
      dsimp [k]
      ring] at hboundaryVal
    have hsum : relaxedAngularFactor setup *
          ((photonEnergy setup w).val + x0) <
        6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2 := by
      nlinarith [hw.2.2, hbranchUpper0]
    have hksum : k * ((photonEnergy setup w).val + x0) < 1 := by
      rw [show k * ((photonEnergy setup w).val + x0) =
          (relaxedAngularFactor setup *
            ((photonEnergy setup w).val + x0)) /
              (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) by
        dsimp [k]
        ring]
      exact (div_lt_one hden).2 hsum
    have hfactor :
        ((photonEnergy setup w).val - x0) *
          (1 - k * ((photonEnergy setup w).val + x0)) = 0 := by
      nlinarith only [hboundaryVal, hx0root]
    have henergyEq : (photonEnergy setup w).val = x0 := by
      rcases mul_eq_zero.mp hfactor with h | h
      · linarith only [h]
      · exfalso
        nlinarith only [h, hksum]
    apply WithDim.ext
    have hwEnergy : (photonEnergy setup w).val =
        setup.reducedPlanckConstant.val * w.val := rfl
    dsimp [omega0]
    rw [hwEnergy] at henergyEq
    apply (eq_div_iff (ne_of_gt hhbar)).2
    nlinarith only [henergyEq]

/-- A lower-branch conservation-boundary frequency bounds every exact
feasible frequency. -/
lemma lowerBoundary_le_feasible
    (setup : PhotodissociationSetup) (hsetup : setup.IsPhysical)
    (omega0 : AngularFrequency)
    (hboundary : ConservationBoundary setup omega0)
    (hbranch : OnLowerPhysicalBranch setup omega0) :
    ∀ {nu : AngularFrequency},
      DissociationFeasible setup nu → omega0.val ≤ nu.val := by
  have hhbar := hsetup.1
  have hc := hsetup.2.1
  have hm := hsetup.2.2.1
  change 0 < setup.reducedPlanckConstant.val at hhbar
  change 0 < setup.speedOfLight.val at hc
  change 0 < setup.oxygenAtomMass.val at hm
  have hApos : 0 < relaxedAngularFactor setup :=
    lt_of_lt_of_le (by norm_num) (relaxedAngularFactor_bounds setup hsetup).1
  have hKformula (w : AngularFrequency) :
      (relaxedMinimumKineticEnergy setup w).val =
        relaxedAngularFactor setup * (photonEnergy setup w).val ^ 2 /
          (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) := by
    have hp : Real.cos setup.outgoingAngle.val *
          max (Real.cos setup.outgoingAngle.val) 0 =
        (max (Real.cos setup.outgoingAngle.val) 0) ^ 2 := by
      by_cases hmu : Real.cos setup.outgoingAngle.val ≤ 0
      · rw [max_eq_right hmu]
        ring
      · rw [max_eq_left (le_of_not_ge hmu)]
        ring
    have hr0val : (relaxedMinimizingMomentum setup w).val =
        2 * (photonMomentumMagnitude setup w).val / 3 *
          max (Real.cos setup.outgoingAngle.val) 0 := by
      rfl
    have hquad := (reducedKineticCost_quadratic setup hsetup w
      (relaxedMinimizingMomentum setup w)).1
    change (relaxedMinimumKineticEnergy setup w).val = _ at hquad
    rw [hr0val] at hquad
    rw [hquad]
    change
      (3 * (2 * ((photonEnergy setup w).val / setup.speedOfLight.val) / 3 *
              max (Real.cos setup.outgoingAngle.val) 0) ^ 2 -
            4 * ((photonEnergy setup w).val / setup.speedOfLight.val) *
              Real.cos setup.outgoingAngle.val *
              (2 * ((photonEnergy setup w).val / setup.speedOfLight.val) / 3 *
                max (Real.cos setup.outgoingAngle.val) 0) +
            2 * ((photonEnergy setup w).val / setup.speedOfLight.val) ^ 2) /
          (4 * setup.oxygenAtomMass.val) =
        (3 - 2 * (max (Real.cos setup.outgoingAngle.val) 0) ^ 2) *
            (photonEnergy setup w).val ^ 2 /
          (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2)
    have hcross :
        ((photonEnergy setup w).val / setup.speedOfLight.val) *
              Real.cos setup.outgoingAngle.val *
              (2 * ((photonEnergy setup w).val /
                    setup.speedOfLight.val) / 3 *
                max (Real.cos setup.outgoingAngle.val) 0) =
          (2 / 3 : ℝ) *
              ((photonEnergy setup w).val /
                setup.speedOfLight.val) ^ 2 *
            max (Real.cos setup.outgoingAngle.val) 0 ^ 2 := by
      calc
        _ = (2 / 3 : ℝ) *
              ((photonEnergy setup w).val /
                setup.speedOfLight.val) ^ 2 *
              (Real.cos setup.outgoingAngle.val *
                max (Real.cos setup.outgoingAngle.val) 0) := by ring
        _ = _ := by rw [hp]
    have hinv4m :
        (4 * setup.oxygenAtomMass.val)⁻¹ =
          (1 / 4 : ℝ) * setup.oxygenAtomMass.val⁻¹ := by
      rw [mul_inv_rev]
      norm_num
      ring
    have hcross4 :
        4 * ((photonEnergy setup w).val / setup.speedOfLight.val) *
              Real.cos setup.outgoingAngle.val *
              (2 * ((photonEnergy setup w).val /
                    setup.speedOfLight.val) / 3 *
                max (Real.cos setup.outgoingAngle.val) 0) =
          4 * ((2 / 3 : ℝ) *
              ((photonEnergy setup w).val /
                setup.speedOfLight.val) ^ 2 *
            max (Real.cos setup.outgoingAngle.val) 0 ^ 2) := by
      calc
        _ = 4 *
            (((photonEnergy setup w).val / setup.speedOfLight.val) *
              Real.cos setup.outgoingAngle.val *
              (2 * ((photonEnergy setup w).val /
                    setup.speedOfLight.val) / 3 *
                max (Real.cos setup.outgoingAngle.val) 0)) := by ring
        _ = _ := by rw [hcross]
    have hinv6mc2 :
        (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2)⁻¹ =
          (1 / 6 : ℝ) * setup.oxygenAtomMass.val⁻¹ *
            setup.speedOfLight.val⁻¹ ^ 2 := by
      rw [mul_inv_rev, ← inv_pow, mul_inv_rev]
      norm_num
      ring
    rw [hcross4]
    repeat' rw [div_eq_mul_inv]
    repeat' rw [hinv4m]
    repeat' rw [hinv6mc2]
    ring
  let k : ℝ := relaxedAngularFactor setup /
    (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2)
  have hk : 0 < k := by dsimp [k]; positivity
  have hden : 0 < 6 * setup.oxygenAtomMass.val *
      setup.speedOfLight.val ^ 2 := by positivity
  change 0 < (photonEnergy setup omega0).val ∧
      relaxedAngularFactor setup * (photonEnergy setup omega0).val <
        3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2 at hbranch
  have hboundaryVal := congrArg WithDim.val hboundary
  change (photonEnergy setup omega0).val = setup.energyGap.val +
    (relaxedMinimumKineticEnergy setup omega0).val at hboundaryVal
  rw [hKformula] at hboundaryVal
  rw [show relaxedAngularFactor setup * (photonEnergy setup omega0).val ^ 2 /
        (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) =
      k * (photonEnergy setup omega0).val ^ 2 by
    dsimp [k]
    ring] at hboundaryVal
  intro nu hfeasible
  have homega : IsStrictlyPositive nu := by
    rcases hfeasible with ⟨momenta, houtcome⟩
    exact houtcome.1
  have hmargin : setup.energyGap.val +
      k * (photonEnergy setup nu).val ^ 2 ≤
        (photonEnergy setup nu).val := by
    by_cases hacute : 0 < Real.cos setup.outgoingAngle.val
    · have hchar :=
        (dissociationFeasible_iff_relaxedMinimum setup hsetup nu).1 hacute
      have hineq := (hchar.mp hfeasible).2
      change setup.energyGap.val +
          (relaxedMinimumKineticEnergy setup nu).val ≤
        (photonEnergy setup nu).val at hineq
      rw [hKformula] at hineq
      rw [show relaxedAngularFactor setup * (photonEnergy setup nu).val ^ 2 /
            (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) =
          k * (photonEnergy setup nu).val ^ 2 by
        dsimp [k]
        ring] at hineq
      exact hineq
    · have hnonacute : IsRightOrObtuseAngle setup := le_of_not_gt hacute
      have hchar :=
        (dissociationFeasible_iff_relaxedMinimum setup hsetup nu).2 hnonacute
      have hineq := (hchar.mp hfeasible).2
      change setup.energyGap.val +
          (relaxedMinimumKineticEnergy setup nu).val <
        (photonEnergy setup nu).val at hineq
      rw [hKformula] at hineq
      rw [show relaxedAngularFactor setup * (photonEnergy setup nu).val ^ 2 /
            (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) =
          k * (photonEnergy setup nu).val ^ 2 by
        dsimp [k]
        ring] at hineq
      exact le_of_lt hineq
  by_contra hnot
  have hnuLt : nu.val < omega0.val := lt_of_not_ge hnot
  have henergyLt : (photonEnergy setup nu).val <
      (photonEnergy setup omega0).val := by
    change setup.reducedPlanckConstant.val * nu.val <
      setup.reducedPlanckConstant.val * omega0.val
    nlinarith
  have hsum : relaxedAngularFactor setup *
        ((photonEnergy setup nu).val + (photonEnergy setup omega0).val) <
      6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2 := by
    nlinarith
  have hksum : k *
        ((photonEnergy setup nu).val + (photonEnergy setup omega0).val) < 1 := by
    rw [show k *
          ((photonEnergy setup nu).val + (photonEnergy setup omega0).val) =
        (relaxedAngularFactor setup *
          ((photonEnergy setup nu).val + (photonEnergy setup omega0).val)) /
            (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) by
      dsimp [k]
      ring]
    exact (div_lt_one hden).2 hsum
  have hdiff :
      ((photonEnergy setup nu).val - setup.energyGap.val -
          k * (photonEnergy setup nu).val ^ 2) -
        ((photonEnergy setup omega0).val - setup.energyGap.val -
          k * (photonEnergy setup omega0).val ^ 2) < 0 := by
    rw [show
      ((photonEnergy setup nu).val - setup.energyGap.val -
          k * (photonEnergy setup nu).val ^ 2) -
        ((photonEnergy setup omega0).val - setup.energyGap.val -
          k * (photonEnergy setup omega0).val ^ 2) =
        ((photonEnergy setup nu).val - (photonEnergy setup omega0).val) *
          (1 - k * ((photonEnergy setup nu).val +
            (photonEnergy setup omega0).val)) by ring]
    exact mul_neg_of_neg_of_pos (sub_neg.2 henergyLt) (sub_pos.2 hksum)
  nlinarith

/-- The two boundary clauses plus the lower-bound theorem produce the full
minimum-frequency solution predicate. -/
lemma lowerBoundary_isMinimumFrequencySolution
    (setup : PhotodissociationSetup) (hsetup : setup.IsPhysical)
    (omega0 : AngularFrequency)
    (hboundary : ConservationBoundary setup omega0)
    (hbranch : OnLowerPhysicalBranch setup omega0) :
    MinimumFrequencySolution setup omega0 := by
  exact ⟨hboundary, hbranch,
    fun nu hnu => lowerBoundary_le_feasible setup hsetup omega0
      hboundary hbranch hnu⟩

/-- Numerical values of positive angular frequencies for which the complete
angle and conservation-law model has an outcome. -/
def feasibleFrequencyValues (setup : PhotodissociationSetup) : Set ℝ :=
  {w | ∃ omega : AngularFrequency,
    w = omega.val ∧
      IsStrictlyPositive omega ∧
      DissociationFeasible setup omega}

/-- Physical subcritical parameters imply that exact feasible frequencies
exist; their positive numerical values are bounded below by zero. -/
lemma feasibleFrequencyValues_nonempty_bddBelow
    (setup : PhotodissociationSetup) (hsetup : setup.IsPhysical)
    (hsubcritical : SubcriticalParameters setup) :
    (feasibleFrequencyValues setup).Nonempty ∧
      BddBelow (feasibleFrequencyValues setup) := by
  have hhbar := hsetup.1
  have hc := hsetup.2.1
  have hm := hsetup.2.2.1
  change 0 < setup.reducedPlanckConstant.val at hhbar
  change 0 < setup.speedOfLight.val at hc
  change 0 < setup.oxygenAtomMass.val at hm
  have hApos : 0 < relaxedAngularFactor setup :=
    lt_of_lt_of_le (by norm_num) (relaxedAngularFactor_bounds setup hsetup).1
  have hKformula (w : AngularFrequency) :
      (relaxedMinimumKineticEnergy setup w).val =
        relaxedAngularFactor setup * (photonEnergy setup w).val ^ 2 /
          (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) := by
    have hp : Real.cos setup.outgoingAngle.val *
          max (Real.cos setup.outgoingAngle.val) 0 =
        (max (Real.cos setup.outgoingAngle.val) 0) ^ 2 := by
      by_cases hmu : Real.cos setup.outgoingAngle.val ≤ 0
      · rw [max_eq_right hmu]
        ring
      · rw [max_eq_left (le_of_not_ge hmu)]
        ring
    have hr0val : (relaxedMinimizingMomentum setup w).val =
        2 * (photonMomentumMagnitude setup w).val / 3 *
          max (Real.cos setup.outgoingAngle.val) 0 := by
      rfl
    have hquad := (reducedKineticCost_quadratic setup hsetup w
      (relaxedMinimizingMomentum setup w)).1
    change (relaxedMinimumKineticEnergy setup w).val = _ at hquad
    rw [hr0val] at hquad
    rw [hquad]
    change
      (3 * (2 * ((photonEnergy setup w).val / setup.speedOfLight.val) / 3 *
              max (Real.cos setup.outgoingAngle.val) 0) ^ 2 -
            4 * ((photonEnergy setup w).val / setup.speedOfLight.val) *
              Real.cos setup.outgoingAngle.val *
              (2 * ((photonEnergy setup w).val / setup.speedOfLight.val) / 3 *
                max (Real.cos setup.outgoingAngle.val) 0) +
            2 * ((photonEnergy setup w).val / setup.speedOfLight.val) ^ 2) /
          (4 * setup.oxygenAtomMass.val) =
        (3 - 2 * (max (Real.cos setup.outgoingAngle.val) 0) ^ 2) *
            (photonEnergy setup w).val ^ 2 /
          (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2)
    have hcross :
        ((photonEnergy setup w).val / setup.speedOfLight.val) *
              Real.cos setup.outgoingAngle.val *
              (2 * ((photonEnergy setup w).val /
                    setup.speedOfLight.val) / 3 *
                max (Real.cos setup.outgoingAngle.val) 0) =
          (2 / 3 : ℝ) *
              ((photonEnergy setup w).val /
                setup.speedOfLight.val) ^ 2 *
            max (Real.cos setup.outgoingAngle.val) 0 ^ 2 := by
      calc
        _ = (2 / 3 : ℝ) *
              ((photonEnergy setup w).val /
                setup.speedOfLight.val) ^ 2 *
              (Real.cos setup.outgoingAngle.val *
                max (Real.cos setup.outgoingAngle.val) 0) := by ring
        _ = _ := by rw [hp]
    have hinv4m :
        (4 * setup.oxygenAtomMass.val)⁻¹ =
          (1 / 4 : ℝ) * setup.oxygenAtomMass.val⁻¹ := by
      rw [mul_inv_rev]
      norm_num
      ring
    have hcross4 :
        4 * ((photonEnergy setup w).val / setup.speedOfLight.val) *
              Real.cos setup.outgoingAngle.val *
              (2 * ((photonEnergy setup w).val /
                    setup.speedOfLight.val) / 3 *
                max (Real.cos setup.outgoingAngle.val) 0) =
          4 * ((2 / 3 : ℝ) *
              ((photonEnergy setup w).val /
                setup.speedOfLight.val) ^ 2 *
            max (Real.cos setup.outgoingAngle.val) 0 ^ 2) := by
      calc
        _ = 4 *
            (((photonEnergy setup w).val / setup.speedOfLight.val) *
              Real.cos setup.outgoingAngle.val *
              (2 * ((photonEnergy setup w).val /
                    setup.speedOfLight.val) / 3 *
                max (Real.cos setup.outgoingAngle.val) 0)) := by ring
        _ = _ := by rw [hcross]
    have hinv6mc2 :
        (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2)⁻¹ =
          (1 / 6 : ℝ) * setup.oxygenAtomMass.val⁻¹ *
            setup.speedOfLight.val⁻¹ ^ 2 := by
      rw [mul_inv_rev, ← inv_pow, mul_inv_rev]
      norm_num
      ring
    rw [hcross4]
    repeat' rw [div_eq_mul_inv]
    repeat' rw [hinv4m]
    repeat' rw [hinv6mc2]
    ring
  let xVertex : ℝ :=
    3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2 /
      relaxedAngularFactor setup
  have hxVertex : 0 < xVertex := by dsimp [xVertex]; positivity
  let omegaVertex : AngularFrequency :=
    ⟨xVertex / setup.reducedPlanckConstant.val⟩
  have homegaVertex : IsStrictlyPositive omegaVertex := by
    change 0 < xVertex / setup.reducedPlanckConstant.val
    positivity
  have henergyVertex : (photonEnergy setup omegaVertex).val = xVertex := by
    change
      setup.reducedPlanckConstant.val *
          (xVertex / setup.reducedPlanckConstant.val) = xVertex
    exact mul_div_cancel₀ xVertex hhbar.ne'
  have hKVertex : (relaxedMinimumKineticEnergy setup omegaVertex).val =
      xVertex / 2 := by
    rw [hKformula, henergyVertex]
    have hAx :
        relaxedAngularFactor setup * xVertex =
          3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2 := by
      dsimp [xVertex]
      exact
        mul_div_cancel₀
          (3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2)
          hApos.ne'
    apply
      (div_eq_iff
        (ne_of_gt (show
          0 < 6 * setup.oxygenAtomMass.val *
            setup.speedOfLight.val ^ 2 by positivity))).2
    rw [show relaxedAngularFactor setup * xVertex ^ 2 =
        (relaxedAngularFactor setup * xVertex) * xVertex by ring, hAx]
    ring
  have hmargin : setup.energyGap.val +
      (relaxedMinimumKineticEnergy setup omegaVertex).val <
        (photonEnergy setup omegaVertex).val := by
    rw [hKVertex, henergyVertex]
    have hsub : 2 * relaxedAngularFactor setup * setup.energyGap.val <
        3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2 :=
      hsubcritical
    have hgapVertex : setup.energyGap.val < xVertex / 2 := by
      dsimp [xVertex]
      rw [show
        3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2 /
              relaxedAngularFactor setup / 2 =
            (3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) /
              (2 * relaxedAngularFactor setup) by ring]
      apply (lt_div_iff₀ (mul_pos (by norm_num) hApos)).2
      nlinarith
    linarith
  have hfeasible : DissociationFeasible setup omegaVertex := by
    by_cases hacute : 0 < Real.cos setup.outgoingAngle.val
    · apply ((dissociationFeasible_iff_relaxedMinimum setup hsetup
        omegaVertex).1 hacute).2
      exact ⟨homegaVertex, le_of_lt hmargin⟩
    · have hnonacute : IsRightOrObtuseAngle setup := le_of_not_gt hacute
      apply ((dissociationFeasible_iff_relaxedMinimum setup hsetup
        omegaVertex).2 hnonacute).2
      exact ⟨homegaVertex, hmargin⟩
  constructor
  · refine ⟨omegaVertex.val, ?_⟩
    exact ⟨omegaVertex, rfl, homegaVertex, hfeasible⟩
  · refine ⟨0, ?_⟩
    intro w hw
    rcases hw with ⟨omega, rfl, homega, _⟩
    exact le_of_lt homega

/-- At an acute angle, a minimum-frequency solution is feasible, and the
explicit relaxed minimizer realizes the required fragment momenta. -/
lemma minimumFrequency_feasible_of_acute
    (setup : PhotodissociationSetup) (hsetup : setup.IsPhysical)
    (hacute : IsAcuteAngle setup) (omegaMin : AngularFrequency)
    (hminimum : MinimumFrequencySolution setup omegaMin) :
    DissociationFeasible setup omegaMin ∧
      IsDissociationOutcome setup omegaMin
        { oxygenMolecule :=
            outgoingMoleculeMomentumAtAngle setup
              (relaxedMinimizingMomentum setup omegaMin)
          oxygenAtom :=
            eliminatedAtomicMomentum setup omegaMin
              (relaxedMinimizingMomentum setup omegaMin) } := by
  have hhbar := hsetup.1
  have hc := hsetup.2.1
  change 0 < setup.reducedPlanckConstant.val at hhbar
  change 0 < setup.speedOfLight.val at hc
  have hboundary := hminimum.1
  have hbranch := hminimum.2.1
  have hphotonPos : 0 < (photonEnergy setup omegaMin).val := hbranch.1
  have homega : IsStrictlyPositive omegaMin := by
    change 0 < omegaMin.val
    change 0 < setup.reducedPlanckConstant.val * omegaMin.val at hphotonPos
    nlinarith
  have hq : 0 < (photonMomentumMagnitude setup omegaMin).val := by
    change
      0 < (photonEnergy setup omegaMin).val / setup.speedOfLight.val
    exact div_pos hphotonPos hc
  let r0 : Momentum := relaxedMinimizingMomentum setup omegaMin
  have hr0pos : IsStrictlyPositive r0 :=
    (reducedKineticCost_minimum_acute setup hsetup omegaMin homega hacute).1
  have hfeasible : DissociationFeasible setup omegaMin := by
    apply (dissociationFeasible_iff_reducedKineticCost setup hsetup omegaMin).2
    exact ⟨r0, hr0pos, hboundary⟩
  refine ⟨hfeasible, homega, ?_, ?_, ?_⟩
  · have hnormIncident :
        (momentumNorm (incidentPhotonMomentum setup omegaMin)).val =
          (photonMomentumMagnitude setup omegaMin).val := by
      change Real.sqrt
          ((photonMomentumMagnitude setup omegaMin).val ^ 2 + 0 ^ 2) =
        (photonMomentumMagnitude setup omegaMin).val
      rw [zero_pow (show (2 : ℕ) ≠ 0 from Nat.succ_ne_zero 1), add_zero]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]
    have hnormOutgoing :
        (momentumNorm (outgoingMoleculeMomentumAtAngle setup r0)).val = r0.val := by
      change Real.sqrt
          ((r0.val * Real.cos setup.outgoingAngle.val) ^ 2 +
            (r0.val * Real.sin setup.outgoingAngle.val) ^ 2) = r0.val
      rw [show
        (r0.val * Real.cos setup.outgoingAngle.val) ^ 2 +
            (r0.val * Real.sin setup.outgoingAngle.val) ^ 2 = r0.val ^ 2 by
        nlinarith [Real.sin_sq_add_cos_sq setup.outgoingAngle.val]]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hr0pos]
    refine ⟨?_, ?_, ?_⟩
    · change 0 < (photonMomentumMagnitude setup omegaMin).val ^ 2 + 0 ^ 2
      positivity
    · change 0 <
        (r0.val * Real.cos setup.outgoingAngle.val) ^ 2 +
          (r0.val * Real.sin setup.outgoingAngle.val) ^ 2
      nlinarith [Real.sin_sq_add_cos_sq setup.outgoingAngle.val,
        sq_pos_of_pos hr0pos]
    · apply WithDim.ext
      change
        (photonMomentumMagnitude setup omegaMin).val *
            (r0.val * Real.cos setup.outgoingAngle.val) +
              0 * (r0.val * Real.sin setup.outgoingAngle.val) =
          (momentumNorm (incidentPhotonMomentum setup omegaMin)).val *
            (momentumNorm (outgoingMoleculeMomentumAtAngle setup r0)).val *
              Real.cos setup.outgoingAngle.val
      rw [hnormIncident, hnormOutgoing]
      ring
  · change addMomentum (outgoingMoleculeMomentumAtAngle setup r0)
        (eliminatedAtomicMomentum setup omegaMin r0) =
      incidentPhotonMomentum setup omegaMin
    unfold addMomentum outgoingMoleculeMomentumAtAngle
      eliminatedAtomicMomentum incidentPhotonMomentum
    congr 1 <;> apply WithDim.ext
    · change r0.val * Real.cos setup.outgoingAngle.val +
          ((photonMomentumMagnitude setup omegaMin).val -
            r0.val * Real.cos setup.outgoingAngle.val) =
        (photonMomentumMagnitude setup omegaMin).val
      ring
    · change r0.val * Real.sin setup.outgoingAngle.val +
          -(r0.val * Real.sin setup.outgoingAngle.val) = 0
      ring
  · change photonEnergy setup omegaMin =
      addEnergy setup.energyGap (reducedKineticCost setup omegaMin r0)
    exact hboundary

/-- At a right or obtuse angle, the lower boundary is not attained, but exact
feasible frequencies approach it arbitrarily closely from above. -/
lemma minimumFrequency_approached_of_nonacute
    (setup : PhotodissociationSetup) (hsetup : setup.IsPhysical)
    (hnonacute : IsRightOrObtuseAngle setup)
    (omegaMin : AngularFrequency)
    (hminimum : MinimumFrequencySolution setup omegaMin) :
    ¬ DissociationFeasible setup omegaMin ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ nu : AngularFrequency,
          DissociationFeasible setup nu ∧
            omegaMin.val < nu.val ∧
            nu.val < omegaMin.val + epsilon := by
  have hhbar := hsetup.1
  have hc := hsetup.2.1
  have hm := hsetup.2.2.1
  change 0 < setup.reducedPlanckConstant.val at hhbar
  change 0 < setup.speedOfLight.val at hc
  change 0 < setup.oxygenAtomMass.val at hm
  have hApos : 0 < relaxedAngularFactor setup :=
    lt_of_lt_of_le (by norm_num) (relaxedAngularFactor_bounds setup hsetup).1
  have hboundary := hminimum.1
  have hbranch := hminimum.2.1
  change 0 < (photonEnergy setup omegaMin).val ∧
      relaxedAngularFactor setup * (photonEnergy setup omegaMin).val <
        3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2 at hbranch
  have hnotfeasible : ¬ DissociationFeasible setup omegaMin := by
    intro hfeasible
    have hchar :=
      (dissociationFeasible_iff_relaxedMinimum setup hsetup omegaMin).2 hnonacute
    have hstrict := (hchar.mp hfeasible).2
    have hboundaryVal := congrArg WithDim.val hboundary
    change (photonEnergy setup omegaMin).val = setup.energyGap.val +
      (relaxedMinimumKineticEnergy setup omegaMin).val at hboundaryVal
    change setup.energyGap.val +
        (relaxedMinimumKineticEnergy setup omegaMin).val <
      (photonEnergy setup omegaMin).val at hstrict
    linarith
  refine ⟨hnotfeasible, ?_⟩
  have hKformula (w : AngularFrequency) :
      (relaxedMinimumKineticEnergy setup w).val =
        relaxedAngularFactor setup * (photonEnergy setup w).val ^ 2 /
          (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) := by
    have hp : Real.cos setup.outgoingAngle.val *
          max (Real.cos setup.outgoingAngle.val) 0 =
        (max (Real.cos setup.outgoingAngle.val) 0) ^ 2 := by
      by_cases hmu : Real.cos setup.outgoingAngle.val ≤ 0
      · rw [max_eq_right hmu]
        ring
      · rw [max_eq_left (le_of_not_ge hmu)]
        ring
    have hr0val : (relaxedMinimizingMomentum setup w).val =
        2 * (photonMomentumMagnitude setup w).val / 3 *
          max (Real.cos setup.outgoingAngle.val) 0 := by
      rfl
    have hquad := (reducedKineticCost_quadratic setup hsetup w
      (relaxedMinimizingMomentum setup w)).1
    change (relaxedMinimumKineticEnergy setup w).val = _ at hquad
    rw [hr0val] at hquad
    rw [hquad]
    change
      (3 * (2 * ((photonEnergy setup w).val / setup.speedOfLight.val) / 3 *
              max (Real.cos setup.outgoingAngle.val) 0) ^ 2 -
            4 * ((photonEnergy setup w).val / setup.speedOfLight.val) *
              Real.cos setup.outgoingAngle.val *
              (2 * ((photonEnergy setup w).val / setup.speedOfLight.val) / 3 *
                max (Real.cos setup.outgoingAngle.val) 0) +
            2 * ((photonEnergy setup w).val / setup.speedOfLight.val) ^ 2) /
          (4 * setup.oxygenAtomMass.val) =
        (3 - 2 * (max (Real.cos setup.outgoingAngle.val) 0) ^ 2) *
            (photonEnergy setup w).val ^ 2 /
          (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2)
    have hcross :
        ((photonEnergy setup w).val / setup.speedOfLight.val) *
              Real.cos setup.outgoingAngle.val *
              (2 * ((photonEnergy setup w).val /
                    setup.speedOfLight.val) / 3 *
                max (Real.cos setup.outgoingAngle.val) 0) =
          (2 / 3 : ℝ) *
              ((photonEnergy setup w).val /
                setup.speedOfLight.val) ^ 2 *
            max (Real.cos setup.outgoingAngle.val) 0 ^ 2 := by
      calc
        _ = (2 / 3 : ℝ) *
              ((photonEnergy setup w).val /
                setup.speedOfLight.val) ^ 2 *
              (Real.cos setup.outgoingAngle.val *
                max (Real.cos setup.outgoingAngle.val) 0) := by ring
        _ = _ := by rw [hp]
    have hinv4m :
        (4 * setup.oxygenAtomMass.val)⁻¹ =
          (1 / 4 : ℝ) * setup.oxygenAtomMass.val⁻¹ := by
      rw [mul_inv_rev]
      norm_num
      ring
    have hcross4 :
        4 * ((photonEnergy setup w).val / setup.speedOfLight.val) *
              Real.cos setup.outgoingAngle.val *
              (2 * ((photonEnergy setup w).val /
                    setup.speedOfLight.val) / 3 *
                max (Real.cos setup.outgoingAngle.val) 0) =
          4 * ((2 / 3 : ℝ) *
              ((photonEnergy setup w).val /
                setup.speedOfLight.val) ^ 2 *
            max (Real.cos setup.outgoingAngle.val) 0 ^ 2) := by
      calc
        _ = 4 *
            (((photonEnergy setup w).val / setup.speedOfLight.val) *
              Real.cos setup.outgoingAngle.val *
              (2 * ((photonEnergy setup w).val /
                    setup.speedOfLight.val) / 3 *
                max (Real.cos setup.outgoingAngle.val) 0)) := by ring
        _ = _ := by rw [hcross]
    have hinv6mc2 :
        (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2)⁻¹ =
          (1 / 6 : ℝ) * setup.oxygenAtomMass.val⁻¹ *
            setup.speedOfLight.val⁻¹ ^ 2 := by
      rw [mul_inv_rev, ← inv_pow, mul_inv_rev]
      norm_num
      ring
    rw [hcross4]
    repeat' rw [div_eq_mul_inv]
    repeat' rw [hinv4m]
    repeat' rw [hinv6mc2]
    ring
  let k : ℝ := relaxedAngularFactor setup /
    (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2)
  have hk : 0 < k := by dsimp [k]; positivity
  have hden : 0 < 6 * setup.oxygenAtomMass.val *
      setup.speedOfLight.val ^ 2 := by positivity
  have hboundaryVal := congrArg WithDim.val hboundary
  change (photonEnergy setup omegaMin).val = setup.energyGap.val +
    (relaxedMinimumKineticEnergy setup omegaMin).val at hboundaryVal
  rw [hKformula] at hboundaryVal
  rw [show relaxedAngularFactor setup * (photonEnergy setup omegaMin).val ^ 2 /
        (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) =
      k * (photonEnergy setup omegaMin).val ^ 2 by
    dsimp [k]
    ring] at hboundaryVal
  let headroom : ℝ :=
    3 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2 -
      relaxedAngularFactor setup * (photonEnergy setup omegaMin).val
  have hheadroom : 0 < headroom := by dsimp [headroom]; linarith [hbranch.2]
  intro epsilon hepsilon
  let t : ℝ := min (epsilon / 2)
    (headroom /
      (relaxedAngularFactor setup * setup.reducedPlanckConstant.val))
  have htpos : 0 < t := by
    dsimp [t]
    exact lt_min (by linarith)
      (div_pos hheadroom (mul_pos hApos hhbar))
  have htlepsilon : t ≤ epsilon / 2 := by
    dsimp [t]
    exact min_le_left _ _
  have htheadroom :
      t ≤ headroom /
        (relaxedAngularFactor setup * setup.reducedPlanckConstant.val) := by
    dsimp [t]
    exact min_le_right _ _
  have hproduct : relaxedAngularFactor setup *
      setup.reducedPlanckConstant.val * t ≤ headroom := by
    have := (le_div_iff₀ (mul_pos hApos hhbar)).mp htheadroom
    nlinarith
  let nu : AngularFrequency := ⟨omegaMin.val + t⟩
  have henergyNu : (photonEnergy setup nu).val =
      (photonEnergy setup omegaMin).val +
        setup.reducedPlanckConstant.val * t := by
    dsimp [nu, photonEnergy]
    ring
  have homegaMin : 0 < omegaMin.val := by
    have hpos := hbranch.1
    change 0 < setup.reducedPlanckConstant.val * omegaMin.val at hpos
    nlinarith
  have homegaNu : IsStrictlyPositive nu := by
    change 0 < omegaMin.val + t
    linarith
  have hsum : relaxedAngularFactor setup *
        ((photonEnergy setup nu).val + (photonEnergy setup omegaMin).val) <
      6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2 := by
    rw [henergyNu]
    dsimp [headroom] at hproduct
    nlinarith [hbranch.2]
  have hksum : k *
        ((photonEnergy setup nu).val + (photonEnergy setup omegaMin).val) < 1 := by
    rw [show k *
          ((photonEnergy setup nu).val + (photonEnergy setup omegaMin).val) =
        (relaxedAngularFactor setup *
          ((photonEnergy setup nu).val + (photonEnergy setup omegaMin).val)) /
            (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) by
      dsimp [k]
      ring]
    exact (div_lt_one hden).2 hsum
  have henergyIncrease : (photonEnergy setup omegaMin).val <
      (photonEnergy setup nu).val := by
    rw [henergyNu]
    nlinarith [mul_pos hhbar htpos]
  have hmarginDiff :
      0 < ((photonEnergy setup nu).val - setup.energyGap.val -
          k * (photonEnergy setup nu).val ^ 2) -
        ((photonEnergy setup omegaMin).val - setup.energyGap.val -
          k * (photonEnergy setup omegaMin).val ^ 2) := by
    rw [show
      ((photonEnergy setup nu).val - setup.energyGap.val -
          k * (photonEnergy setup nu).val ^ 2) -
        ((photonEnergy setup omegaMin).val - setup.energyGap.val -
          k * (photonEnergy setup omegaMin).val ^ 2) =
        ((photonEnergy setup nu).val - (photonEnergy setup omegaMin).val) *
          (1 - k * ((photonEnergy setup nu).val +
            (photonEnergy setup omegaMin).val)) by ring]
    exact mul_pos (sub_pos.2 henergyIncrease) (sub_pos.2 hksum)
  have hmargin : setup.energyGap.val +
      (relaxedMinimumKineticEnergy setup nu).val <
        (photonEnergy setup nu).val := by
    rw [hKformula]
    rw [show relaxedAngularFactor setup * (photonEnergy setup nu).val ^ 2 /
          (6 * setup.oxygenAtomMass.val * setup.speedOfLight.val ^ 2) =
        k * (photonEnergy setup nu).val ^ 2 by
      dsimp [k]
      ring]
    nlinarith
  have hfeasible : DissociationFeasible setup nu := by
    apply ((dissociationFeasible_iff_relaxedMinimum setup hsetup nu).2
      hnonacute).2
    exact ⟨homegaNu, hmargin⟩
  refine ⟨nu, hfeasible, ?_, ?_⟩
  · dsimp [nu]
    linarith
  · dsimp [nu]
    linarith

end

end Problem1C1

open Problem1C1

/-- Every physical subcritical setup has a unique dimensioned threshold
frequency.  The value is deliberately absent from the theorem signature: it
is characterized by the governing conservation boundary, its lower physical
branch, and its order relation to all exact feasible events. -/
theorem problem_IPhO_2026_1_C_1
    (setup : PhotodissociationSetup)
    (hsetup : setup.IsPhysical)
    (hsubcritical : SubcriticalParameters setup) :
    ∃! omegaMin : AngularFrequency,
      MinimumFrequencySolution setup omegaMin := by
  rcases existsUnique_lowerBoundary setup hsetup hsubcritical with
    ⟨omega0, hboundaryBranch, hunique⟩
  refine ⟨omega0,
    lowerBoundary_isMinimumFrequencySolution setup hsetup omega0
      hboundaryBranch.1 hboundaryBranch.2, ?_⟩
  intro omega hsolution
  exact hunique omega ⟨hsolution.1, hsolution.2.1⟩

end Ipho2026Gpt56solBlind
