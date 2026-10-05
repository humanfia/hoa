import Ipho2026Gpt56solBlind.Shared.PhotodissociationKinematics

/-!
# IPhO 2026 problem 1, part C.2

This file specializes the shared two-fragment photodissociation model to
ozone dissociation.  All scalar quantities use one coherent coordinate chart:
energy in electronvolts, time in seconds, and length in metres.  Thus masses
have coordinate unit `eV s² / m²`; in particular, a tabulated atomic-mass
energy equivalent is divided by the square of the speed of light.

The parenthesized source precision of the atomic-mass entry is retained as an
absolute-deviation datum.  The requested threshold-energy excess and the
tight enclosure induced by that source precision are characterized solely by
the conservation laws; no derived value or enclosure endpoint appears in a
target signature.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_1_C_2

noncomputable section

open Ipho2026Gpt56solBlind.Shared.PhotodissociationKinematics

/-- A positive reduced Planck constant in `eV s` coordinates.  The source
table gives only an ellipsized decimal, so its value remains a parameter. -/
structure PositiveReducedPlanckConstantEVS where
  reducedPlanckConstantEVS : ℝ
  positive : 0 < reducedPlanckConstantEVS

/-- Exact speed-of-light coordinate in metres per second. -/
def speedOfLightMS : ℝ :=
  299792458

/-- Central atomic-mass energy-equivalent coordinate encoded by the displayed
source digits, in electronvolts.  This is not an assertion that the physical
quantity is known exactly. -/
def atomicMassEnergyEquivalentEV : ℝ :=
  93149410372 / 100

/-- Radius in electronvolts encoded by the parenthesized final source digits. -/
def atomicMassEnergyEquivalentRadiusEV : ℝ :=
  29 / 100

/-- An atomic-mass energy-equivalent coordinate admitted by the precision of
the displayed source datum. -/
structure AtomicMassEnergyDatumEV where
  energyEquivalentEV : ℝ
  deviation_le_radius :
    |energyEquivalentEV - atomicMassEnergyEquivalentEV| ≤
      atomicMassEnergyEquivalentRadiusEV

/-- The lower endpoint of the source interval is strictly positive. -/
lemma atomicMassEnergyEquivalentEV_sub_radius_pos :
    0 < atomicMassEnergyEquivalentEV - atomicMassEnergyEquivalentRadiusEV := by
  change 0 < (93149410372 : ℝ) / 100 - 29 / 100
  norm_num

namespace AtomicMassEnergyDatumEV

/-- Every admitted atomic-mass coordinate lies above the lower source
endpoint. -/
lemma lower_bound (D : AtomicMassEnergyDatumEV) :
    atomicMassEnergyEquivalentEV - atomicMassEnergyEquivalentRadiusEV ≤
      D.energyEquivalentEV := by
  have hlower := (abs_le.mp D.deviation_le_radius).1
  linarith

/-- Every admitted atomic-mass coordinate lies below the upper source
endpoint. -/
lemma upper_bound (D : AtomicMassEnergyDatumEV) :
    D.energyEquivalentEV ≤
      atomicMassEnergyEquivalentEV + atomicMassEnergyEquivalentRadiusEV := by
  have hupper := (abs_le.mp D.deviation_le_radius).2
  linarith

/-- Every admitted atomic-mass energy-equivalent coordinate is positive. -/
lemma coordinate_pos (D : AtomicMassEnergyDatumEV) :
    0 < D.energyEquivalentEV := by
  exact lt_of_lt_of_le atomicMassEnergyEquivalentEV_sub_radius_pos
    D.lower_bound

end AtomicMassEnergyDatumEV

/-- The displayed central coordinate, regarded as an admissible source datum. -/
def centralAtomicMassEnergyDatumEV : AtomicMassEnergyDatumEV where
  energyEquivalentEV := atomicMassEnergyEquivalentEV
  deviation_le_radius := by
    norm_num [atomicMassEnergyEquivalentRadiusEV]

/-- One atomic mass unit in the coherent `eV s² / m²` mass coordinate, for a
particular energy-equivalent datum admitted by the source. -/
def atomicMassUnitEVS2PerM2 (D : AtomicMassEnergyDatumEV) : ℝ :=
  D.energyEquivalentEV / speedOfLightMS ^ 2

/-- Prescribed oxygen-atom mass coordinate, corresponding to `16.0 amu`. -/
def oxygenAtomMassEVS2PerM2 (D : AtomicMassEnergyDatumEV) : ℝ :=
  16 * atomicMassUnitEVS2PerM2 D

/-- Oxygen-molecule mass coordinate in the classical fragment model. -/
def oxygenMoleculeMassEVS2PerM2 (D : AtomicMassEnergyDatumEV) : ℝ :=
  2 * oxygenAtomMassEVS2PerM2 D

/-- Prescribed molecular ground-state energy gap in electronvolts. -/
def dissociationEnergyGapEV : ℝ :=
  11 / 10

/-- Prescribed unsigned angle of the outgoing oxygen-molecule momentum. -/
def outgoingAngle : ℝ :=
  Real.pi / 6

/-- The reduced Planck coordinate carried by a positive datum is positive. -/
lemma reducedPlanckConstantEVS_pos
    (H : PositiveReducedPlanckConstantEVS) :
    0 < H.reducedPlanckConstantEVS := by
  exact H.positive

/-- The exact speed-of-light coordinate is positive. -/
lemma speedOfLightMS_pos :
    0 < speedOfLightMS := by
  change 0 < (299792458 : ℝ)
  norm_num

/-- The coherent mass coordinate of one atomic mass unit is positive for
every source-admissible datum. -/
lemma atomicMassUnitEVS2PerM2_pos (D : AtomicMassEnergyDatumEV) :
    0 < atomicMassUnitEVS2PerM2 D := by
  exact div_pos D.coordinate_pos (sq_pos_of_pos speedOfLightMS_pos)

/-- The prescribed oxygen-atom mass coordinate is positive for every
source-admissible datum. -/
lemma oxygenAtomMassEVS2PerM2_pos (D : AtomicMassEnergyDatumEV) :
    0 < oxygenAtomMassEVS2PerM2 D := by
  exact mul_pos (by norm_num) (atomicMassUnitEVS2PerM2_pos D)

/-- The oxygen-molecule fragment mass coordinate is positive for every
source-admissible datum. -/
lemma oxygenMoleculeMassEVS2PerM2_pos (D : AtomicMassEnergyDatumEV) :
    0 < oxygenMoleculeMassEVS2PerM2 D := by
  exact mul_pos (by norm_num) (oxygenAtomMassEVS2PerM2_pos D)

/-- The prescribed dissociation gap is positive. -/
lemma dissociationEnergyGapEV_pos :
    0 < dissociationEnergyGapEV := by
  change 0 < (11 : ℝ) / 10
  norm_num

/-- The prescribed unsigned angle is nonnegative. -/
lemma outgoingAngle_nonneg :
    0 ≤ outgoingAngle := by
  exact div_nonneg Real.pi_pos.le (by norm_num)

/-- The prescribed unsigned angle lies at most at `π`. -/
lemma outgoingAngle_le_pi :
    outgoingAngle ≤ Real.pi := by
  change Real.pi / 6 ≤ Real.pi
  nlinarith [Real.pi_pos]

/-- The prescribed angle is acute. -/
lemma outgoingAngle_acute :
    0 < Real.cos outgoingAngle := by
  change 0 < Real.cos (Real.pi / 6)
  rw [Real.cos_pi_div_six]
  exact div_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num)

/-- The shared conservation-law setup specialized to ozone dissociation and
one atomic-mass coordinate admitted by the source.  Fragment one is the
outgoing oxygen molecule of mass `2m`; fragment two is the oxygen atom of
mass `m`. -/
def specializedSetup
    (H : PositiveReducedPlanckConstantEVS)
    (D : AtomicMassEnergyDatumEV) : Setup where
  fragmentOneMass := oxygenMoleculeMassEVS2PerM2 D
  fragmentTwoMass := oxygenAtomMassEVS2PerM2 D
  propagationSpeed := speedOfLightMS
  reducedAction := H.reducedPlanckConstantEVS
  energyGap := dissociationEnergyGapEV
  angle := outgoingAngle
  fragmentOneMass_pos := oxygenMoleculeMassEVS2PerM2_pos D
  fragmentTwoMass_pos := oxygenAtomMassEVS2PerM2_pos D
  propagationSpeed_pos := speedOfLightMS_pos
  reducedAction_pos := reducedPlanckConstantEVS_pos H
  energyGap_pos := dissociationEnergyGapEV_pos
  angle_nonneg := outgoingAngle_nonneg
  angle_le_pi := outgoingAngle_le_pi

/-- Every setup admitted by the displayed atomic-mass precision lies in the
regime where the relaxed conservation boundary has a lower physical root. -/
lemma specializedSetup_subcritical
    (H : PositiveReducedPlanckConstantEVS)
    (D : AtomicMassEnergyDatumEV) :
    SubcriticalParameters (specializedSetup H D) := by
  let s := specializedSetup H D
  have hfactor_le : relaxedAngularFactor s ≤ 1 :=
    (relaxedAngularFactor_bounds s).2.2
  have hmass_times_c_sq :
      oxygenAtomMassEVS2PerM2 D * speedOfLightMS ^ 2 =
        16 * D.energyEquivalentEV := by
    unfold oxygenAtomMassEVS2PerM2 atomicMassUnitEVS2PerM2
    rw [mul_assoc,
      div_mul_cancel₀ D.energyEquivalentEV
        (pow_ne_zero 2 speedOfLightMS_pos.ne')]
  have hdenominator :
      2 * oxygenAtomMassEVS2PerM2 D * speedOfLightMS ^ 2 =
        32 * D.energyEquivalentEV := by
    nlinarith [hmass_times_c_sq]
  have hdenominator_pos :
      0 < 2 * oxygenAtomMassEVS2PerM2 D * speedOfLightMS ^ 2 :=
    mul_pos (mul_pos (by norm_num) (oxygenAtomMassEVS2PerM2_pos D))
      (sq_pos_of_pos speedOfLightMS_pos)
  have hleft_le :
      4 * relaxedAngularFactor s * dissociationEnergyGapEV ≤ 22 / 5 := by
    unfold dissociationEnergyGapEV
    norm_num
    nlinarith
  have hsource_large : 22 / 5 < 32 * D.energyEquivalentEV := by
    have hD := D.lower_bound
    unfold atomicMassEnergyEquivalentEV
      atomicMassEnergyEquivalentRadiusEV at hD
    norm_num at hD ⊢
    linarith
  have hnumerator_lt :
      4 * relaxedAngularFactor s * dissociationEnergyGapEV <
        2 * oxygenAtomMassEVS2PerM2 D * speedOfLightMS ^ 2 := by
    rw [hdenominator]
    exact lt_of_le_of_lt hleft_le hsource_large
  unfold SubcriticalParameters boundaryCoefficient
  change
    4 * (relaxedAngularFactor s /
      (2 * oxygenAtomMassEVS2PerM2 D * speedOfLightMS ^ 2)) *
        dissociationEnergyGapEV < 1
  calc
    4 * (relaxedAngularFactor s /
        (2 * oxygenAtomMassEVS2PerM2 D * speedOfLightMS ^ 2)) *
          dissociationEnergyGapEV =
        (4 * relaxedAngularFactor s * dissociationEnergyGapEV) /
          (2 * oxygenAtomMassEVS2PerM2 D * speedOfLightMS ^ 2) := by ring
    _ < 1 := (div_lt_one hdenominator_pos).2 hnumerator_lt

/-- At the prescribed acute angle, every feasibility threshold lies on the
lower physical branch and is attained by physical outgoing momenta. -/
lemma specializedThreshold_attained
    (H : PositiveReducedPlanckConstantEVS)
    (D : AtomicMassEnergyDatumEV)
    (omega0 : ℝ)
    (hThreshold : FeasibilityThreshold (specializedSetup H D) omega0) :
    OnLowerPhysicalBranch (specializedSetup H D) omega0 ∧
      Feasible (specializedSetup H D) omega0 := by
  have hacute :
      0 < Real.cos (specializedSetup H D).angle := by
    change 0 < Real.cos outgoingAngle
    exact outgoingAngle_acute
  exact ⟨hThreshold.2.1, hThreshold.2.2.2.2.1 hacute⟩

/-- `x` is the requested threshold photon-energy excess, in electronvolt
coordinates, for exact admissible data `H` and `D`.  Its witness is constrained
by the full conservation-law threshold, the lower physical branch, and
threshold attainment. -/
def IsThresholdEnergyExcessEV
    (H : PositiveReducedPlanckConstantEVS)
    (D : AtomicMassEnergyDatumEV)
    (x : ℝ) : Prop :=
  ∃ omega0 : ℝ,
    FeasibilityThreshold (specializedSetup H D) omega0 ∧
      OnLowerPhysicalBranch (specializedSetup H D) omega0 ∧
      Feasible (specializedSetup H D) omega0 ∧
      x = photonEnergy (specializedSetup H D) omega0 - dissociationEnergyGapEV

/-- The governing conservation laws determine exactly one threshold-energy
excess for every positive reduced-Planck datum and source-admissible atomic
mass datum, without placing its derived value in the theorem statement. -/
theorem existsUnique_thresholdEnergyExcessEV
    (H : PositiveReducedPlanckConstantEVS)
    (D : AtomicMassEnergyDatumEV) :
    ∃! x : ℝ, IsThresholdEnergyExcessEV H D x := by
  rcases existsUnique_feasibilityThreshold (specializedSetup H D)
      (specializedSetup_subcritical H D) with
    ⟨omega0, hThreshold, hThreshold_unique⟩
  rcases specializedThreshold_attained H D omega0 hThreshold with
    ⟨hLower, hFeasible⟩
  refine ⟨photonEnergy (specializedSetup H D) omega0 -
      dissociationEnergyGapEV, ?_, ?_⟩
  · exact ⟨omega0, hThreshold, hLower, hFeasible, rfl⟩
  · intro x hx
    rcases hx with
      ⟨omega, hThreshold', hLower', hFeasible', hx⟩
    have homega : omega = omega0 :=
      hThreshold_unique omega hThreshold'
    subst omega
    exact hx

/-- A threshold-energy excess is source-consistent when it is produced by
some positive reduced-Planck datum and some atomic-mass coordinate admitted by
the displayed source precision. -/
def IsSourceConsistentThresholdEnergyExcessEV (x : ℝ) : Prop :=
  ∃ H : PositiveReducedPlanckConstantEVS,
    ∃ D : AtomicMassEnergyDatumEV,
      IsThresholdEnergyExcessEV H D x

/-- `[L,U]` is a tight enclosure of all source-consistent output coordinates:
it contains every such output and both endpoints are themselves attained
source-consistent outputs. -/
def IsTightSourceConsistentOutputEnclosureEV (L U : ℝ) : Prop :=
  L ≤ U ∧
    (∀ x : ℝ,
      IsSourceConsistentThresholdEnergyExcessEV x → L ≤ x ∧ x ≤ U) ∧
    IsSourceConsistentThresholdEnergyExcessEV L ∧
    IsSourceConsistentThresholdEnergyExcessEV U

/-- There is exactly one attained tight enclosure induced by the displayed
source precision.  Its endpoints remain characterized rather than evaluated. -/
theorem existsUnique_tightSourceConsistentOutputEnclosureEV :
    ∃! bounds : ℝ × ℝ,
      IsTightSourceConsistentOutputEnclosureEV bounds.1 bounds.2 := by
  have hmass_times_c_sq (D : AtomicMassEnergyDatumEV) :
      oxygenAtomMassEVS2PerM2 D * speedOfLightMS ^ 2 =
        16 * D.energyEquivalentEV := by
    unfold oxygenAtomMassEVS2PerM2 atomicMassUnitEVS2PerM2
    rw [mul_assoc,
      div_mul_cancel₀ D.energyEquivalentEV
        (pow_ne_zero 2 speedOfLightMS_pos.ne')]
  have hangular_factor
      (H : PositiveReducedPlanckConstantEVS)
      (D : AtomicMassEnergyDatumEV) :
      relaxedAngularFactor (specializedSetup H D) =
        1 - (2 / 3 : ℝ) * max (Real.cos outgoingAngle) 0 ^ 2 := by
    change
      1 - (2 * oxygenAtomMassEVS2PerM2 D) /
          (2 * oxygenAtomMassEVS2PerM2 D +
            oxygenAtomMassEVS2PerM2 D) *
            max (Real.cos outgoingAngle) 0 ^ 2 =
        1 - (2 / 3 : ℝ) * max (Real.cos outgoingAngle) 0 ^ 2
    have hmass : 0 < oxygenAtomMassEVS2PerM2 D :=
      oxygenAtomMassEVS2PerM2_pos D
    have hratio :
        (2 * oxygenAtomMassEVS2PerM2 D) /
            (2 * oxygenAtomMassEVS2PerM2 D +
              oxygenAtomMassEVS2PerM2 D) =
          (2 / 3 : ℝ) := by
      apply (div_eq_iff (by nlinarith)).2
      ring
    rw [hratio]
  have hcoefficient
      (H : PositiveReducedPlanckConstantEVS)
      (D : AtomicMassEnergyDatumEV) :
      boundaryCoefficient (specializedSetup H D) =
        (1 - (2 / 3 : ℝ) * max (Real.cos outgoingAngle) 0 ^ 2) /
          (32 * D.energyEquivalentEV) := by
    have hdenominator :
        2 * oxygenAtomMassEVS2PerM2 D * speedOfLightMS ^ 2 =
          32 * D.energyEquivalentEV := by
      nlinarith [hmass_times_c_sq D]
    unfold boundaryCoefficient
    change
      relaxedAngularFactor (specializedSetup H D) /
          (2 * oxygenAtomMassEVS2PerM2 D * speedOfLightMS ^ 2) =
        (1 - (2 / 3 : ℝ) * max (Real.cos outgoingAngle) 0 ^ 2) /
          (32 * D.energyEquivalentEV)
    rw [hangular_factor H D, hdenominator]
  have excess_antitone
      (H₁ H₂ : PositiveReducedPlanckConstantEVS)
      (D₁ D₂ : AtomicMassEnergyDatumEV)
      (x₁ x₂ : ℝ)
      (hD : D₁.energyEquivalentEV ≤ D₂.energyEquivalentEV)
      (hx₁ : IsThresholdEnergyExcessEV H₁ D₁ x₁)
      (hx₂ : IsThresholdEnergyExcessEV H₂ D₂ x₂) :
      x₂ ≤ x₁ := by
    rcases hx₁ with
      ⟨omega₁, hThreshold₁, hLower₁, hFeasible₁, hx₁eq⟩
    rcases hx₂ with
      ⟨omega₂, hThreshold₂, hLower₂, hFeasible₂, hx₂eq⟩
    have hangular_pos :
        0 < 1 - (2 / 3 : ℝ) * max (Real.cos outgoingAngle) 0 ^ 2 := by
      have hbounds :=
        relaxedAngularFactor_bounds (specializedSetup H₁ D₁)
      have hpositive :
          0 < relaxedAngularFactor (specializedSetup H₁ D₁) :=
        lt_of_lt_of_le hbounds.1 hbounds.2.1
      rwa [hangular_factor H₁ D₁] at hpositive
    have hdenominator₁ : 0 < 32 * D₁.energyEquivalentEV :=
      mul_pos (by norm_num) D₁.coordinate_pos
    have hdenominator₂ : 0 < 32 * D₂.energyEquivalentEV :=
      mul_pos (by norm_num) D₂.coordinate_pos
    have hcoefficient_le :
        boundaryCoefficient (specializedSetup H₂ D₂) ≤
          boundaryCoefficient (specializedSetup H₁ D₁) := by
      rw [hcoefficient H₂ D₂, hcoefficient H₁ D₁]
      apply (div_le_div_iff₀ hdenominator₂ hdenominator₁).2
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hD (by norm_num)) hangular_pos.le
    have hacute₁ :
        0 < Real.cos (specializedSetup H₁ D₁).angle := by
      change 0 < Real.cos outgoingAngle
      exact outgoingAngle_acute
    have hmargin₁ :
        0 ≤ boundaryMargin (specializedSetup H₁ D₁)
          (photonEnergy (specializedSetup H₁ D₁) omega₁) :=
      (((feasible_iff_boundaryMargin (specializedSetup H₁ D₁) omega₁).1
        hacute₁).1 hFeasible₁).2
    have hquadratic_le :
        boundaryCoefficient (specializedSetup H₂ D₂) *
            photonEnergy (specializedSetup H₁ D₁) omega₁ ^ 2 ≤
          boundaryCoefficient (specializedSetup H₁ D₁) *
            photonEnergy (specializedSetup H₁ D₁) omega₁ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoefficient_le (sq_nonneg _)
    have hmargin₂ :
        0 ≤ boundaryMargin (specializedSetup H₂ D₂)
          (photonEnergy (specializedSetup H₁ D₁) omega₁) := by
      unfold boundaryMargin at hmargin₁ ⊢
      dsimp [specializedSetup] at hmargin₁ hquadratic_le ⊢
      linarith
    let nu := photonEnergy (specializedSetup H₁ D₁) omega₁ /
      H₂.reducedPlanckConstantEVS
    have hnu_pos : 0 < nu :=
      div_pos hLower₁.1 H₂.positive
    have henergy_nu :
        photonEnergy (specializedSetup H₂ D₂) nu =
          photonEnergy (specializedSetup H₁ D₁) omega₁ := by
      change
        H₂.reducedPlanckConstantEVS *
            ((H₁.reducedPlanckConstantEVS * omega₁) /
              H₂.reducedPlanckConstantEVS) =
          H₁.reducedPlanckConstantEVS * omega₁
      exact
        mul_div_cancel₀ (H₁.reducedPlanckConstantEVS * omega₁)
          H₂.positive.ne'
    have hacute₂ :
        0 < Real.cos (specializedSetup H₂ D₂).angle := by
      change 0 < Real.cos outgoingAngle
      exact outgoingAngle_acute
    have hnu_feasible : Feasible (specializedSetup H₂ D₂) nu := by
      apply ((feasible_iff_boundaryMargin (specializedSetup H₂ D₂) nu).1
        hacute₂).2
      refine ⟨hnu_pos, ?_⟩
      rw [henergy_nu]
      exact hmargin₂
    have homega_le : omega₂ ≤ nu :=
      hThreshold₂.2.2.2.1 nu hnu_feasible
    have henergy_le :
        photonEnergy (specializedSetup H₂ D₂) omega₂ ≤
          photonEnergy (specializedSetup H₁ D₁) omega₁ := by
      calc
        photonEnergy (specializedSetup H₂ D₂) omega₂ ≤
            photonEnergy (specializedSetup H₂ D₂) nu := by
          unfold photonEnergy
          exact mul_le_mul_of_nonneg_left homega_le H₂.positive.le
        _ = photonEnergy (specializedSetup H₁ D₁) omega₁ :=
          henergy_nu
    calc
      x₂ = photonEnergy (specializedSetup H₂ D₂) omega₂ -
          dissociationEnergyGapEV := hx₂eq
      _ ≤ photonEnergy (specializedSetup H₁ D₁) omega₁ -
          dissociationEnergyGapEV := sub_le_sub_right henergy_le _
      _ = x₁ := hx₁eq.symm
  let H0 : PositiveReducedPlanckConstantEVS :=
    ⟨1, by norm_num⟩
  let Dlower : AtomicMassEnergyDatumEV :=
    { energyEquivalentEV :=
        atomicMassEnergyEquivalentEV - atomicMassEnergyEquivalentRadiusEV
      deviation_le_radius := by
        change
          |((93149410372 : ℝ) / 100 - 29 / 100) -
              93149410372 / 100| ≤
            29 / 100
        norm_num }
  let Dupper : AtomicMassEnergyDatumEV :=
    { energyEquivalentEV :=
        atomicMassEnergyEquivalentEV + atomicMassEnergyEquivalentRadiusEV
      deviation_le_radius := by
        change
          |((93149410372 : ℝ) / 100 + 29 / 100) -
              93149410372 / 100| ≤
            29 / 100
        norm_num }
  rcases existsUnique_thresholdEnergyExcessEV H0 Dupper with
    ⟨L, hL, hL_unique⟩
  rcases existsUnique_thresholdEnergyExcessEV H0 Dlower with
    ⟨U, hU, hU_unique⟩
  have hDlower_upper :
      Dlower.energyEquivalentEV ≤ Dupper.energyEquivalentEV := by
    change
      (93149410372 : ℝ) / 100 - 29 / 100 ≤
        93149410372 / 100 + 29 / 100
    norm_num
  have hLU : L ≤ U :=
    excess_antitone H0 H0 Dlower Dupper U L hDlower_upper hU hL
  have hL_source : IsSourceConsistentThresholdEnergyExcessEV L :=
    ⟨H0, Dupper, hL⟩
  have hU_source : IsSourceConsistentThresholdEnergyExcessEV U :=
    ⟨H0, Dlower, hU⟩
  have hcontains :
      ∀ x : ℝ, IsSourceConsistentThresholdEnergyExcessEV x →
        L ≤ x ∧ x ≤ U := by
    intro x hx
    rcases hx with ⟨H, D, hx⟩
    constructor
    · apply excess_antitone H H0 D Dupper x L
      · simpa [Dupper] using D.upper_bound
      · exact hx
      · exact hL
    · apply excess_antitone H0 H Dlower D U x
      · simpa [Dlower] using D.lower_bound
      · exact hU
      · exact hx
  have htight : IsTightSourceConsistentOutputEnclosureEV L U :=
    ⟨hLU, hcontains, hL_source, hU_source⟩
  refine ⟨(L, U), ?_, ?_⟩
  · exact htight
  · intro bounds hbounds
    rcases hbounds with
      ⟨hbounds_order, hbounds_contains, hbounds_lower, hbounds_upper⟩
    have hlower_eq : bounds.1 = L := by
      apply le_antisymm
      · exact (hbounds_contains L hL_source).1
      · exact (hcontains bounds.1 hbounds_lower).1
    have hupper_eq : bounds.2 = U := by
      apply le_antisymm
      · exact (hcontains bounds.2 hbounds_upper).2
      · exact (hbounds_contains U hU_source).2
    apply Prod.ext
    · exact hlower_eq
    · exact hupper_eq

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_1_C_2
