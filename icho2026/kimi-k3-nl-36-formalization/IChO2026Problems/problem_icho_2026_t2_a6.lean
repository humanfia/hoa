import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T2-A6: perturbations of the BZ oscillator

This file is a `conditional_contest_model` formalization of the four requested
classifications.  It preserves the supplied Kimi draft, but no requested answer
is used as a hypothesis.  Printed data and derived source lemmas live in
`PrintedSource`; the extra dose, mixing, availability, loss, and equilibrium
conditions authorized by M201/M202/M203 live in `ConditionalContestModel`.

All scalar wrappers name their physical units.  Physlib's current foundational
dimension type has no amount-of-substance coordinate, so using separate local
types is safer than representing molar concentration as an undimensioned real.
-/

namespace IChO2026Problems
namespace ProblemIcho2026T2A6

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Unit-bearing scalar types -/

/-- Molar concentration, in mol L⁻¹ (M). -/
structure MolarConcentration where
  molPerL : ℝ
deriving DecidableEq

/-- Chemical amount, in mol. -/
structure AmountMol where
  mol : ℝ
deriving DecidableEq

/-- Liquid volume, in L. -/
structure VolumeL where
  liter : ℝ
deriving DecidableEq

/-- Elapsed time, in s. -/
structure DurationS where
  second : ℝ
deriving DecidableEq

/-- Molar concentration flux, in mol L⁻¹ s⁻¹ (M s⁻¹). -/
structure MolarFlux where
  molPerLPerS : ℝ
deriving DecidableEq

/-- Pseudo-first-order rate coefficient, in s⁻¹. -/
structure FirstOrderRateConstant where
  perS : ℝ
deriving DecidableEq

/-- Bimolecular rate coefficient, in M⁻¹ s⁻¹. -/
structure SecondOrderRateConstant where
  molarInvPerS : ℝ
deriving DecidableEq

/-- Third-order rate coefficient, in M⁻² s⁻¹. -/
structure ThirdOrderRateConstant where
  molarInvSqPerS : ℝ
deriving DecidableEq

/-- Fourth-order rate coefficient, in M⁻³ s⁻¹. -/
structure FourthOrderRateConstant where
  molarInvCubePerS : ℝ
deriving DecidableEq

/-- Solubility product for a 1:1 salt, in M² under the dilute-activity model. -/
structure SolubilityProductM2 where
  molarSquared : ℝ
deriving DecidableEq

/-- Temperature readout, in degrees Celsius. -/
structure TemperatureC where
  celsius : ℝ
deriving DecidableEq

/-! ## Chemical identities and the answer panel -/

/-- Species named by the printed mechanism or the authorized AgBr bridge.
`step7OtherProducts` records the printed but compositionally unspecified products;
they are not used to claim a complete atom or mass balance. -/
inductive Species
  | bromousAcid
  | bromate
  | proton
  | bromineDioxideRadical
  | ceriumIII
  | ceriumIV
  | hypobromousAcid
  | bromide
  | malonicAcid
  | bromomalonicAcid
  | water
  | silverIon
  | silverBromide
  | step7OtherProducts
deriving DecidableEq, Repr

inductive Phase
  | aqueous
  | solid
deriving DecidableEq, Repr

structure ChemicalEntity where
  species : Species
  phase : Phase
deriving DecidableEq, Repr

inductive Process
  | processA
  | processB
deriving DecidableEq, Repr

/-- The five options printed in T2-A6, in panel order (a)--(e). -/
inductive Effect
  | prolongsProcessA
  | prolongsProcessB
  | switchesAToB
  | switchesBToA
  | oscillationsStop
deriving DecidableEq, Repr

namespace PrintedSource

/-! ## Exact printed concentrations and rate constants -/

def bromateConcentration : MolarConcentration := ⟨3 / 50⟩
def malonicAcidConcentration : MolarConcentration := ⟨1 / 10⟩
def protonConcentration : MolarConcentration := ⟨4 / 5⟩
def ceriumIVSourceScale : MolarConcentration := ⟨1 / 1000⟩
def bromideMaximum : MolarConcentration := ⟨7 / 10000⟩

/-- The explicitly printed fallback for later questions; the derivation below does
not use this value. -/
def printedFallbackCriticalBromide : MolarConcentration := ⟨1 / 10000000⟩

def k1 : ThirdOrderRateConstant := ⟨10000⟩
def k4 : ThirdOrderRateConstant := ⟨2000000000⟩
def k5 : FourthOrderRateConstant := ⟨21 / 10⟩
def k7 : SecondOrderRateConstant := ⟨100⟩

/-- The seven numbered elementary steps printed on page 2. -/
inductive ElementaryStep
  | step1
  | step2
  | step3
  | step4
  | step5
  | step6
  | step7
deriving DecidableEq, Repr

/-- In the printed reduced description, Process A contains steps (1)--(3),
Process C continues as step (7), and Process B practically does not occur. -/
def processAReducedActiveSteps : Finset ElementaryStep :=
  [.step1, .step2, .step3, .step7].toFinset

/-- Bromide reactant stoichiometry read directly from the printed mechanism.
Only Process-B steps (4) and (5) consume one bromide per event. -/
def bromideConsumedPerEvent : ElementaryStep → ℕ
  | .step4 | .step5 => 1
  | _ => 0

/-- Branch-correct source carrier: none of the steps retained in the printed
Process-A/continuous-Process-C reduction consumes bromide. -/
theorem processA_reduced_steps_consume_no_bromide
    (step : ElementaryStep) (h_active : step ∈ processAReducedActiveSteps) :
    bromideConsumedPerEvent step = 0 := by
  simp [processAReducedActiveSteps] at h_active
  rcases h_active with rfl | rfl | rfl | rfl <;> rfl

/-- Outcome-decisive bromide loss in the contest's reduced Process-A branch.
This is the explicit idealization of the printed phrase "Process B practically
does not occur"; it is not a claim that a real vessel has mathematically zero
side-reaction rate outside that reduced branch. -/
def processAReducedBromideLoss (_bromide : MolarConcentration) : MolarFlux :=
  ⟨0⟩

theorem processA_reduced_bromide_loss_eq_zero
    (bromide : MolarConcentration) :
    (processAReducedBromideLoss bromide).molPerLPerS = 0 := by
  rfl

/-- Printed elementary-step (1) mass-action rate, in M s⁻¹. -/
def step1Rate (hbro2 : MolarConcentration) : MolarFlux :=
  ⟨k1.molarInvSqPerS * hbro2.molPerL * bromateConcentration.molPerL *
    protonConcentration.molPerL⟩

/-- Printed elementary-step (4) mass-action rate, in M s⁻¹. -/
def step4Rate (hbro2 bromide : MolarConcentration) : MolarFlux :=
  ⟨k4.molarInvSqPerS * hbro2.molPerL * bromide.molPerL *
    protonConcentration.molPerL⟩

/-- Printed elementary-step (5) mass-action rate, in M s⁻¹. -/
def step5Rate (bromide : MolarConcentration) : MolarFlux :=
  ⟨k5.molarInvCubePerS * bromateConcentration.molPerL * bromide.molPerL *
    protonConcentration.molPerL ^ 2⟩

/-- Printed elementary-step (7) mass-action rate, in M s⁻¹.  Its two
reactant concentrations are Ce(IV) and BMA, not malonic acid. -/
def step7Rate (ceriumIV bma : MolarConcentration) : MolarFlux :=
  ⟨k7.molarInvPerS * ceriumIV.molPerL * bma.molPerL⟩

/-- Process-B stationary HBrO₂ concentration obtained by equating the
printed production rate (5) and consumption rate (4). -/
def stationaryHBrO2ProcessB : MolarConcentration :=
  ⟨k5.molarInvCubePerS * bromateConcentration.molPerL *
    protonConcentration.molPerL / k4.molarInvSqPerS⟩

theorem processB_stationary_step4_eq_step5 (bromide : MolarConcentration) :
    (step4Rate stationaryHBrO2ProcessB bromide).molPerLPerS =
      (step5Rate bromide).molPerLPerS := by
  norm_num [step4Rate, step5Rate, stationaryHBrO2ProcessB, k4, k5,
    bromateConcentration, protonConcentration]
  <;> ring

/-- Critical bromide concentration obtained by solving `r₄ = r₁`; units are M. -/
def criticalBromide : MolarConcentration :=
  ⟨k1.molarInvSqPerS * bromateConcentration.molPerL / k4.molarInvSqPerS⟩

/-- Inline derivation of T2-A3 from the printed rate constants; the fallback is
not imported as an answer. -/
theorem criticalBromide_eq : criticalBromide.molPerL = 3 / 10000000 := by
  norm_num [criticalBromide, k1, k4, bromateConcentration]

/-- The printed switch criterion, reduced algebraically to the bromide threshold. -/
theorem step4_gt_step1_iff
    (hbro2 bromide : MolarConcentration)
    (h_hbro2_positive : 0 < hbro2.molPerL) :
    (step1Rate hbro2).molPerLPerS < (step4Rate hbro2 bromide).molPerLPerS ↔
      criticalBromide.molPerL < bromide.molPerL := by
  norm_num [step1Rate, step4Rate, criticalBromide, k1, k4,
    bromateConcentration, protonConcentration] at *
  constructor <;> intro h <;> nlinarith

/-- The reverse half of the printed switch criterion. -/
theorem step1_gt_step4_iff
    (hbro2 bromide : MolarConcentration)
    (h_hbro2_positive : 0 < hbro2.molPerL) :
    (step4Rate hbro2 bromide).molPerLPerS < (step1Rate hbro2).molPerLPerS ↔
      bromide.molPerL < criticalBromide.molPerL := by
  norm_num [step1Rate, step4Rate, criticalBromide, k1, k4,
    bromateConcentration, protonConcentration] at *
  constructor <;> intro h <;> nlinarith

/-- Under the Process-B stationary relation `r₄ = r₅`, steps (4) and (5)
consume two bromides per paired event.  This is the source-derived
pseudo-first-order coefficient `2 k₅ [BrO₃⁻] [H⁺]²`, in s⁻¹. -/
def processBDecayConstant : FirstOrderRateConstant :=
  ⟨2 * k5.molarInvCubePerS * bromateConcentration.molPerL *
    protonConcentration.molPerL ^ 2⟩

theorem processBDecayConstant_positive : 0 < processBDecayConstant.perS := by
  norm_num [processBDecayConstant, k5, bromateConcentration, protonConcentration]

/-- The source-grounded reduced Process-B loss law, in M s⁻¹. -/
def processBSteadyStateBromideLoss (bromide : MolarConcentration) : MolarFlux :=
  ⟨processBDecayConstant.perS * bromide.molPerL⟩

/-- At the stationary Process-B relation `r₄ = r₅`, the bromide sink is
the sum of steps (4) and (5), hence twice the printed step-(5) rate. -/
theorem processBSteadyStateBromideLoss_eq_twice_step5
    (bromide : MolarConcentration) :
    (processBSteadyStateBromideLoss bromide).molPerLPerS =
      2 * (step5Rate bromide).molPerLPerS := by
  norm_num [processBSteadyStateBromideLoss, processBDecayConstant, step5Rate,
    k5, bromateConcentration, protonConcentration]
  <;> ring

/-- Reaction-level form of the same grounded sink: one bromide is consumed by
each of steps (4) and (5). -/
theorem processBSteadyStateBromideLoss_eq_step4_add_step5
    (bromide : MolarConcentration) :
    (processBSteadyStateBromideLoss bromide).molPerLPerS =
      (step4Rate stationaryHBrO2ProcessB bromide).molPerLPerS +
        (step5Rate bromide).molPerLPerS := by
  rw [processBSteadyStateBromideLoss_eq_twice_step5,
    processB_stationary_step4_eq_step5]
  ring

/-- The source switch semantics expressed as a classifier, not an answer premise. -/
noncomputable def classifyPulseAtThreshold
    (initial : Process) (postPulse : MolarConcentration) : Effect :=
  match initial with
  | .processA =>
      if criticalBromide.molPerL < postPulse.molPerL then
        .switchesAToB
      else
        .prolongsProcessA
  | .processB =>
      if postPulse.molPerL < criticalBromide.molPerL then
        .switchesBToA
      else
        .prolongsProcessB

end PrintedSource

namespace ConditionalContestModel

open PrintedSource

/-! ## Shared step-(7) extent ledger -/

/-- The finite species/phase domain used by the outcome-decisive step-(7)
equivalent ledger.  The printed unspecified other products are intentionally
outside this partial component ledger and no claim is made about them. -/
def step7OutcomeDecisiveDomain : Finset ChemicalEntity :=
  [ { species := .ceriumIV, phase := .aqueous },
    { species := .bromomalonicAcid, phase := .aqueous },
    { species := .ceriumIII, phase := .aqueous },
    { species := .bromide, phase := .aqueous } ].toFinset

/-- Outcome-decisive one-equivalent ledger for printed step (7): one mole of
Ce(IV) and one mole of available BMA are consumed per mole of Ce(III) and
bromide produced.  This is deliberately not a complete atom ledger for the
printed, unspecified "other products". -/
structure Step7MoleLedger where
  ceriumIVConsumed : AmountMol
  bmaConsumed : AmountMol
  ceriumIIIProduced : AmountMol
  bromideProduced : AmountMol

def IsStep7MoleLedger (extent : AmountMol) (ledger : Step7MoleLedger) : Prop :=
  ledger.ceriumIVConsumed.mol = extent.mol ∧
  ledger.bmaConsumed.mol = extent.mol ∧
  ledger.ceriumIIIProduced.mol = extent.mol ∧
  ledger.bromideProduced.mol = extent.mol

def canonicalStep7MoleLedger (extent : AmountMol) : Step7MoleLedger :=
  { ceriumIVConsumed := extent
    bmaConsumed := extent
    ceriumIIIProduced := extent
    bromideProduced := extent }

theorem canonicalStep7MoleLedger_valid (extent : AmountMol) :
    IsStep7MoleLedger extent (canonicalStep7MoleLedger extent) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Pseudo-first-order coefficient `k₇ [BMA]`, in s⁻¹, obtained directly
from the printed bimolecular step-(7) mass-action law. -/
def step7PseudoFirstOrderRate (bma : MolarConcentration) : FirstOrderRateConstant :=
  ⟨k7.molarInvPerS * bma.molPerL⟩

/-! ## Action 1: an authorized finite Ce(IV) pulse model (M202) -/

/-- Primitive physical inputs permitted by authorization M202.  All
concentrations are uniformly mixed, post-addition values at kinetic time zero.
The BMA concentration/stock is supplementary availability data; it is not
silently identified with the separately printed malonic-acid concentration. -/
structure Action1PulseInputs where
  initialVolume : VolumeL
  doseSolutionVolume : VolumeL
  mixedVolume : VolumeL
  mixingTime : DurationS
  initialBromide : MolarConcentration
  ceriumIVDose : AmountMol
  bmaConcentration : MolarConcentration
  bmaAvailable : AmountMol
  observationTime : DurationS

def action1DoseConcentration (p : Action1PulseInputs) : MolarConcentration :=
  ⟨p.ceriumIVDose.mol / p.mixedVolume.liter⟩

/-- Additional, non-printed M202 conditions.  Units are L, s, M, and mol.
No final bromide value, loss cap, threshold crossing, or answer label occurs in
this predicate.  The Ce(IV) pulse concentration is at most one-thousandth of
the printed 0.001 M Ce(IV) source scale; the chosen 0.010 M BMA stock is at
most one-tenth of the printed 0.10 M malonic-acid source scale. -/
def Action1Admissible (p : Action1PulseInputs) : Prop :=
  p.initialVolume.liter = 1 ∧
  p.doseSolutionVolume.liter = 1 / 1000 ∧
  p.mixedVolume.liter = p.initialVolume.liter + p.doseSolutionVolume.liter ∧
  p.mixingTime.second = 1 / 100 ∧
  9 / 100000000 ≤ p.initialBromide.molPerL ∧
  p.initialBromide.molPerL ≤ 1 / 10000000 ∧
  9 / 10000000 ≤ p.ceriumIVDose.mol ∧
  p.ceriumIVDose.mol ≤ 1 / 1000000 ∧
  p.bmaConcentration.molPerL = 1 / 100 ∧
  p.bmaConcentration.molPerL ≤ malonicAcidConcentration.molPerL / 10 ∧
  p.bmaAvailable.mol =
    p.bmaConcentration.molPerL * p.mixedVolume.liter ∧
  p.ceriumIVDose.mol ≤ p.bmaAvailable.mol ∧
  1 ≤ p.observationTime.second ∧
  p.observationTime.second ≤ 11 / 10 ∧
  p.mixingTime.second ≤ p.observationTime.second ∧
  (action1DoseConcentration p).molPerL ≤ ceriumIVSourceScale.molPerL / 1000

/-- Incremental Ce(IV) remaining after `t` seconds in the well-mixed
pseudo-first-order realization of printed step (7). -/
def action1CeIVRemaining (p : Action1PulseInputs) (t : ℝ) : MolarConcentration :=
  ⟨(action1DoseConcentration p).molPerL *
    Real.exp (-(step7PseudoFirstOrderRate p.bmaConcentration).perS * t)⟩

/-- Gross step-(7) extent concentration from the printed mass-action law. -/
def action1Step7ExtentConcentration
    (p : Action1PulseInputs) (t : ℝ) : MolarConcentration :=
  ⟨(action1DoseConcentration p).molPerL - (action1CeIVRemaining p t).molPerL⟩

def action1Step7ExtentAmount (p : Action1PulseInputs) (t : ℝ) : AmountMol :=
  ⟨p.mixedVolume.liter * (action1Step7ExtentConcentration p t).molPerL⟩

def action1Step7Ledger (p : Action1PulseInputs) (t : ℝ) : Step7MoleLedger :=
  canonicalStep7MoleLedger (action1Step7ExtentAmount p t)

/-- Bromide trajectory in the printed reduced Process-A branch: initial stock
plus the one-bromide-per-event extent of continuous step (7). -/
noncomputable def action1BromideAt
    (p : Action1PulseInputs) (t : ℝ) : MolarConcentration :=
  ⟨p.initialBromide.molPerL +
    (action1Step7ExtentConcentration p t).molPerL⟩

def action1BromideAtObservation (p : Action1PulseInputs) : MolarConcentration :=
  action1BromideAt p p.observationTime.second

/-- Cumulative competing removal is defined by stock balance.  In the printed
reduced Process-A branch it is subsequently proved to be zero. -/
noncomputable def action1CompetingRemovalAt
    (p : Action1PulseInputs) (t : ℝ) : MolarConcentration :=
  ⟨p.initialBromide.molPerL + (action1Step7ExtentConcentration p t).molPerL -
    (action1BromideAt p t).molPerL⟩

theorem action1_step7_massAction_carrier_conditional_contest_model
    (p : Action1PulseInputs) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (action1CeIVRemaining p s).molPerL)
      (-(step7Rate (action1CeIVRemaining p t) p.bmaConcentration).molPerLPerS) t := by
  unfold action1CeIVRemaining action1DoseConcentration step7PseudoFirstOrderRate
    step7Rate
  dsimp
  have hinner : HasDerivAt
      (fun s : ℝ => -(k7.molarInvPerS * p.bmaConcentration.molPerL * s))
      (-(k7.molarInvPerS * p.bmaConcentration.molPerL)) t := by
    simpa only [id_eq, neg_mul, mul_one] using
      (hasDerivAt_id t).const_mul
        (-(k7.molarInvPerS * p.bmaConcentration.molPerL))
  convert hinner.exp.const_mul
      (p.ceriumIVDose.mol / p.mixedVolume.liter) using 1
  all_goals first | rfl | ring

/-- The modeled bromide trajectory satisfies printed step-(7) production minus
the branch-correct reduced Process-A loss. -/
theorem action1_bromide_stock_flow_carrier_conditional_contest_model
    (p : Action1PulseInputs)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => (action1BromideAt p s).molPerL)
      ((step7Rate (action1CeIVRemaining p t) p.bmaConcentration).molPerLPerS -
        (processAReducedBromideLoss (action1BromideAt p t)).molPerLPerS) t := by
  have hCe := action1_step7_massAction_carrier_conditional_contest_model p t
  have h := hCe.const_sub
    (p.initialBromide.molPerL + (action1DoseConcentration p).molPerL)
  convert h using 1
  all_goals
    try simp only [action1BromideAt, action1Step7ExtentConcentration,
      action1CeIVRemaining, processAReducedBromideLoss, step7Rate]
    try dsimp
    first | rfl | ring

theorem action1_step7_ledger_conditional_contest_model
    (p : Action1PulseInputs) (t : ℝ) :
    IsStep7MoleLedger (action1Step7ExtentAmount p t) (action1Step7Ledger p t) := by
  exact canonicalStep7MoleLedger_valid _

/-- The chosen BMA amount really supports every modeled step-(7) event through
the finite observation time. -/
theorem action1_step7_availability_conditional_contest_model
    (p : Action1PulseInputs) (h_admissible : Action1Admissible p) :
    0 < (action1Step7ExtentAmount p p.observationTime.second).mol ∧
    (action1Step7ExtentAmount p p.observationTime.second).mol ≤
      p.ceriumIVDose.mol ∧
    (action1Step7ExtentAmount p p.observationTime.second).mol ≤
      p.bmaAvailable.mol := by
  rcases h_admissible with
    ⟨hV, hDoseV, hMixV, hMixT, hBrLo, hBrHi, hDoseLo, hDoseHi,
      hBma, hBmaScale, hBmaAvail, hDoseAvail, hObsLo, hObsHi,
      hMixObs, hPulseScale⟩
  have hMixed : p.mixedVolume.liter = 1001 / 1000 := by
    rw [hMixV, hV, hDoseV]
    norm_num
  have hDosePos : 0 < p.ceriumIVDose.mol := by nlinarith
  have hObsPos : 0 < p.observationTime.second := by nlinarith
  have hExpPos : 0 < Real.exp (-p.observationTime.second) := Real.exp_pos _
  have hExpLt : Real.exp (-p.observationTime.second) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hExtentEq :
      (action1Step7ExtentAmount p p.observationTime.second).mol =
        p.ceriumIVDose.mol * (1 - Real.exp (-p.observationTime.second)) := by
    simp only [action1Step7ExtentAmount, action1Step7ExtentConcentration,
      action1CeIVRemaining, action1DoseConcentration,
      step7PseudoFirstOrderRate, k7]
    rw [hMixed, hBma]
    field_simp
    <;> ring
  rw [hExtentEq]
  have hExtentPos :
      0 < p.ceriumIVDose.mol * (1 - Real.exp (-p.observationTime.second)) :=
    mul_pos hDosePos (sub_pos.mpr hExpLt)
  have hExtentDose :
      p.ceriumIVDose.mol * (1 - Real.exp (-p.observationTime.second)) ≤
        p.ceriumIVDose.mol := by
    nlinarith [mul_pos hDosePos hExpPos]
  exact ⟨hExtentPos, hExtentDose, hExtentDose.trans hDoseAvail⟩

/-- The selected initial-state range is on the Process-A side of the
source-derived threshold before the Ce(IV) pulse is applied. -/
theorem action1_initial_branch_conditional_contest_model
    (p : Action1PulseInputs) (h_admissible : Action1Admissible p) :
    p.initialBromide.molPerL < criticalBromide.molPerL := by
  rcases h_admissible with ⟨_, _, _, _, _, h, _⟩
  rw [criticalBromide_eq]
  nlinarith

/-- Every admissible pulse produces more than `5e-7 M` bromide-equivalent by
the observation time; this is derived from `k₇[BMA]`, dose, volume, and time. -/
theorem action1_production_bound_conditional_contest_model
    (p : Action1PulseInputs) (h_admissible : Action1Admissible p) :
    5 / 10000000 <
      (action1Step7ExtentConcentration p p.observationTime.second).molPerL := by
  rcases h_admissible with
    ⟨hV, hDoseV, hMixV, hMixT, hBrLo, hBrHi, hDoseLo, hDoseHi,
      hBma, hBmaScale, hBmaAvail, hDoseAvail, hObsLo, hObsHi,
      hMixObs, hPulseScale⟩
  have hMixed : p.mixedVolume.liter = 1001 / 1000 := by
    rw [hMixV, hV, hDoseV]
    norm_num
  have hExpLe : Real.exp (-p.observationTime.second) ≤ Real.exp (-1) :=
    Real.exp_le_exp.mpr (by linarith)
  have hExpBound : Real.exp (-p.observationTime.second) < 0.3678794412 :=
    lt_of_le_of_lt hExpLe Real.exp_neg_one_lt_d9
  have hDoseNonneg : 0 ≤ p.ceriumIVDose.mol := by nlinarith
  have hMul := mul_le_mul_of_nonneg_left (le_of_lt hExpBound) hDoseNonneg
  simp only [action1Step7ExtentConcentration, action1CeIVRemaining,
    action1DoseConcentration, step7PseudoFirstOrderRate, k7]
  rw [hMixed, hBma]
  norm_num at hMul ⊢
  nlinarith

/-- Branch-correct removal bound.  The zero is derived from the printed
Process-A reduction and the step stoichiometries above; it is not an admissible
input or an independently chosen numerical cap. -/
theorem action1_loss_bound_conditional_contest_model
    (p : Action1PulseInputs) (h_admissible : Action1Admissible p) :
    (action1CompetingRemovalAt p p.observationTime.second).molPerL = 0 ∧
    (action1CompetingRemovalAt p p.observationTime.second).molPerL ≤
      (processAReducedBromideLoss
        (action1BromideAtObservation p)).molPerLPerS *
          p.observationTime.second := by
  constructor
  · simp [action1CompetingRemovalAt, action1BromideAt]
  · simp [action1CompetingRemovalAt, action1BromideAt,
      processAReducedBromideLoss]

theorem action1_stock_balance_conditional_contest_model
    (p : Action1PulseInputs) :
    (action1BromideAtObservation p).molPerL +
        (action1CompetingRemovalAt p p.observationTime.second).molPerL =
      p.initialBromide.molPerL +
        (action1Step7ExtentConcentration p p.observationTime.second).molPerL := by
  simp [action1BromideAtObservation, action1CompetingRemovalAt]

/-- Actual threshold crossing is derived from production and grounded removal. -/
theorem action1_crosses_threshold_conditional_contest_model
    (p : Action1PulseInputs) (h_admissible : Action1Admissible p) :
    criticalBromide.molPerL < (action1BromideAtObservation p).molPerL := by
  have hProduction := action1_production_bound_conditional_contest_model p h_admissible
  have hInitial := h_admissible.2.2.2.2.1
  rw [criticalBromide_eq]
  simp only [action1BromideAtObservation, action1BromideAt]
  nlinarith

def action1FeasibleInputs : Action1PulseInputs :=
  { initialVolume := ⟨1⟩
    doseSolutionVolume := ⟨1 / 1000⟩
    mixedVolume := ⟨1001 / 1000⟩
    mixingTime := ⟨1 / 100⟩
    initialBromide := ⟨1 / 10000000⟩
    ceriumIVDose := ⟨1 / 1000000⟩
    bmaConcentration := ⟨1 / 100⟩
    bmaAvailable := ⟨1001 / 100000⟩
    observationTime := ⟨1⟩ }

/-- A concrete positive, finite, mass-balanced M202 witness. -/
theorem action1_feasible_tuple_conditional_contest_model :
    Action1Admissible action1FeasibleInputs := by
  norm_num [Action1Admissible, action1FeasibleInputs,
    action1DoseConcentration, ceriumIVSourceScale, malonicAcidConcentration]

/-! ## Action 2: an authorized finite-time AgBr precipitation model (M203) -/

/-- OpenStax Chemistry 2e, Appendix J, table J1, row `AgBr`, gives
`Ksp = 5.0 × 10⁻13` at 25 °C.  Section 15.1 gives the saturated 1:1 law
`[Ag⁺][Br⁻] = Ksp` and the precipitation criterion `Qsp > Ksp`.

For the explicitly selected well-mixed kinetic regime below, Chemistry
LibreTexts, section 17.5 "Kinetics of Reactions in Solution", supplies the
ordinary bimolecular concentration product law and reports aqueous encounter
constants of order `10⁹--10¹⁰ M⁻¹ s⁻¹` at room temperature.  The chosen effective
coefficient `10⁸ M⁻¹ s⁻¹` is therefore finite and below that encounter scale;
it is an M203 supplementary regime input, not an AgBr constant printed by the
problem or asserted by the cited source.

Stable URLs:
* https://openstax.org/books/chemistry-2e/pages/j-solubility-products
* https://openstax.org/books/chemistry-2e/pages/15-1-precipitation-and-dissolution
* https://chem.libretexts.org/Bookshelves/General_Chemistry/Chem1_(Lower)/17%3A_Chemical_Kinetics_and_Dynamics/17.05%3A_Kinetics_of_Reactions_in_Solution
-/
def agBrKsp25C : SolubilityProductM2 := ⟨5 / 10000000000000⟩

/-- Complete finite species/phase domain used by the Ag/Br precipitation
component balances. -/
def agBrOutcomeDecisiveDomain : Finset ChemicalEntity :=
  [ { species := .silverIon, phase := .aqueous },
    { species := .bromide, phase := .aqueous },
    { species := .silverBromide, phase := .solid } ].toFinset

def AgBrSaturatedEquilibrium
    (silver bromide : MolarConcentration) : Prop :=
  0 < silver.molPerL ∧
  0 < bromide.molPerL ∧
  silver.molPerL * bromide.molPerL = agBrKsp25C.molarSquared

structure AgBrMoleLedger where
  silverRemoved : AmountMol
  bromideRemoved : AmountMol
  silverBromideSolidFormed : AmountMol

def IsAgBrMoleLedger (extent : AmountMol) (ledger : AgBrMoleLedger) : Prop :=
  ledger.silverRemoved.mol = extent.mol ∧
  ledger.bromideRemoved.mol = extent.mol ∧
  ledger.silverBromideSolidFormed.mol = extent.mol

/-- Primitive M203 initial-state, dose, volume, mixing, reaction-window,
temperature, BMA-availability, and effective precipitation-rate inputs. -/
structure Action2PulseInputs where
  initialVolume : VolumeL
  doseSolutionVolume : VolumeL
  mixedVolume : VolumeL
  initialBromide : MolarConcentration
  initialCeriumIV : MolarConcentration
  bmaConcentration : MolarConcentration
  bmaAvailable : AmountMol
  effectiveSilverDose : AmountMol
  mixingTime : DurationS
  observationTime : DurationS
  precipitationRateConstant : SecondOrderRateConstant
  temperature : TemperatureC

def action2SilverDoseConcentration (p : Action2PulseInputs) : MolarConcentration :=
  ⟨p.effectiveSilverDose.mol / p.mixedVolume.liter⟩

def action2SilverStockConcentration (p : Action2PulseInputs) : MolarConcentration :=
  ⟨p.effectiveSilverDose.mol / p.doseSolutionVolume.liter⟩

/-- Kinetic time after the finite mixing interval, in seconds. -/
def action2KineticWindow (p : Action2PulseInputs) : DurationS :=
  ⟨p.observationTime.second - p.mixingTime.second⟩

/-- Additional, non-printed M203 conditions.  Concentrations are uniformly
mixed values at kinetic time zero.  The low positive Ce(IV) range represents a
colourless Process-B initial state while retaining continuous printed Process C.
No final ion concentration, removal extent, threshold crossing, or effect label
occurs here.  All displayed bounds have units L, s, M, mol, M⁻¹ s⁻¹, or °C. -/
def Action2Admissible (p : Action2PulseInputs) : Prop :=
  p.initialVolume.liter = 1 ∧
  p.doseSolutionVolume.liter = 1 / 1000 ∧
  p.mixedVolume.liter = p.initialVolume.liter + p.doseSolutionVolume.liter ∧
  p.mixingTime.second = 1 / 100 ∧
  p.observationTime.second = 11 / 100 ∧
  5 / 10000000 ≤ p.initialBromide.molPerL ∧
  p.initialBromide.molPerL ≤ 6 / 10000000 ∧
  0 < p.initialCeriumIV.molPerL ∧
  p.initialCeriumIV.molPerL ≤ 1 / 100000000 ∧
  p.bmaConcentration.molPerL = 1 / 100 ∧
  p.bmaConcentration.molPerL ≤ malonicAcidConcentration.molPerL / 10 ∧
  p.bmaAvailable.mol =
    p.bmaConcentration.molPerL * p.mixedVolume.liter ∧
  p.initialCeriumIV.molPerL * p.mixedVolume.liter ≤ p.bmaAvailable.mol ∧
  3 / 1000000 ≤ p.effectiveSilverDose.mol ∧
  p.effectiveSilverDose.mol ≤ 31 / 10000000 ∧
  p.precipitationRateConstant.molarInvPerS = 100000000 ∧
  p.temperature.celsius = 25 ∧
  (action2SilverDoseConcentration p).molPerL ≤
    ceriumIVSourceScale.molPerL / 300 ∧
  (action2SilverStockConcentration p).molPerL ≤
    bromateConcentration.molPerL / 10 ∧
  (action2SilverStockConcentration p).molPerL ≤
    malonicAcidConcentration.molPerL / 30

/-- Continuous printed Process C consumes the finite mixed Ce(IV) inventory
during the post-mixing kinetic window. -/
def action2CeIVRemaining (p : Action2PulseInputs) (t : ℝ) : MolarConcentration :=
  ⟨p.initialCeriumIV.molPerL *
    Real.exp (-(step7PseudoFirstOrderRate p.bmaConcentration).perS * t)⟩

def action2ProcessCExtentConcentration
    (p : Action2PulseInputs) (t : ℝ) : MolarConcentration :=
  ⟨p.initialCeriumIV.molPerL - (action2CeIVRemaining p t).molPerL⟩

def action2ProcessCExtentAmount (p : Action2PulseInputs) (t : ℝ) : AmountMol :=
  ⟨(action2ProcessCExtentConcentration p t).molPerL * p.mixedVolume.liter⟩

def action2Step7Ledger (p : Action2PulseInputs) (t : ℝ) : Step7MoleLedger :=
  canonicalStep7MoleLedger (action2ProcessCExtentAmount p t)

/-- Forward-minus-reverse mass-action realization of
`Ag⁺(aq) + Br⁻(aq) ⇌ AgBr(s)`.  Solid activity is one, and the reverse
coefficient is fixed as `k_precip Ksp`, so the zero-rate state is exactly the
sourced nonzero-solubility equilibrium. -/
def agBrNetPrecipitationFlux
    (rate : SecondOrderRateConstant)
    (silver bromide : MolarConcentration) : MolarFlux :=
  ⟨rate.molarInvPerS *
    (silver.molPerL * bromide.molPerL - agBrKsp25C.molarSquared)⟩

theorem agBr_net_flux_zero_iff_saturated_equilibrium
    (rate : SecondOrderRateConstant)
    (silver bromide : MolarConcentration)
    (h_rate_positive : 0 < rate.molarInvPerS)
    (h_silver_positive : 0 < silver.molPerL)
    (h_bromide_positive : 0 < bromide.molPerL) :
    (agBrNetPrecipitationFlux rate silver bromide).molPerLPerS = 0 ↔
      AgBrSaturatedEquilibrium silver bromide := by
  unfold agBrNetPrecipitationFlux AgBrSaturatedEquilibrium
  dsimp
  constructor
  · intro h
    refine ⟨h_silver_positive, h_bromide_positive, ?_⟩
    have h_rate_ne : rate.molarInvPerS ≠ 0 := ne_of_gt h_rate_positive
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp h).resolve_left h_rate_ne
  · rintro ⟨_, _, h⟩
    rw [h, sub_self, mul_zero]

/-- Time-indexed dissolved-ion and solid-equivalent concentrations, all in M
relative to the fixed mixed volume. -/
structure Action2KineticTrajectory where
  dissolvedSilver : ℝ → MolarConcentration
  dissolvedBromide : ℝ → MolarConcentration
  solidAgBrEquivalent : ℝ → MolarConcentration

def action2PrecipitationFluxAt
    (p : Action2PulseInputs) (x : Action2KineticTrajectory) (t : ℝ) : MolarFlux :=
  agBrNetPrecipitationFlux p.precipitationRateConstant
    (x.dissolvedSilver t) (x.dissolvedBromide t)

/-- The grounded finite-time law used for M203.  It gives initial stocks,
nonnegative physical states, continuous step-(7) bromide production, reversible
AgBr mass action, and equal Ag/Br/solid rates on the entire finite window.  It
contains no terminal concentration, crossing, or answer-shaped predicate. -/
def IsAction2KineticTrajectory
    (p : Action2PulseInputs) (x : Action2KineticTrajectory) : Prop :=
  x.dissolvedSilver 0 = action2SilverDoseConcentration p ∧
  x.dissolvedBromide 0 = p.initialBromide ∧
  x.solidAgBrEquivalent 0 = ⟨0⟩ ∧
  ∀ t : ℝ, 0 ≤ t → t ≤ (action2KineticWindow p).second →
    0 ≤ (x.dissolvedSilver t).molPerL ∧
    0 ≤ (x.dissolvedBromide t).molPerL ∧
    0 ≤ (x.solidAgBrEquivalent t).molPerL ∧
    HasDerivAt (fun s : ℝ => (x.dissolvedSilver s).molPerL)
      (-(action2PrecipitationFluxAt p x t).molPerLPerS) t ∧
    HasDerivAt (fun s : ℝ => (x.dissolvedBromide s).molPerL)
      ((step7Rate (action2CeIVRemaining p t) p.bmaConcentration).molPerLPerS -
        (action2PrecipitationFluxAt p x t).molPerLPerS) t ∧
    HasDerivAt (fun s : ℝ => (x.solidAgBrEquivalent s).molPerL)
      (action2PrecipitationFluxAt p x t).molPerLPerS t

def action2PrecipitatedAgBr
    (p : Action2PulseInputs) (x : Action2KineticTrajectory) : AmountMol :=
  ⟨(x.solidAgBrEquivalent (action2KineticWindow p).second).molPerL *
    p.mixedVolume.liter⟩

def action2AgBrLedger
    (p : Action2PulseInputs) (x : Action2KineticTrajectory) : AgBrMoleLedger :=
  { silverRemoved := action2PrecipitatedAgBr p x
    bromideRemoved := action2PrecipitatedAgBr p x
    silverBromideSolidFormed := action2PrecipitatedAgBr p x }

/-- A lower bound on dissolved silver that follows from total available
bromide, rather than from a final-state assumption. -/
def action2SilverFloor (p : Action2PulseInputs) : MolarConcentration :=
  ⟨(action2SilverDoseConcentration p).molPerL -
    p.initialBromide.molPerL - p.initialCeriumIV.molPerL⟩

/-- A proved net downward margin of `2e-5 M s⁻¹` while bromide is at or
above the switching threshold. -/
def action2ThresholdDownwardMargin : MolarFlux := ⟨1 / 50000⟩

/-- A finite `0.02 s` crossing deadline inside the `0.10 s` kinetic window. -/
def action2CrossingDeadline : DurationS := ⟨1 / 50⟩

theorem action2_kinetic_window_eq_conditional_contest_model
    (p : Action2PulseInputs) (h_admissible : Action2Admissible p) :
    (action2KineticWindow p).second = 1 / 10 := by
  rcases h_admissible with ⟨_, _, _, hMix, hObs, _⟩
  norm_num [action2KineticWindow, hMix, hObs]

theorem action2_processC_massAction_carrier_conditional_contest_model
    (p : Action2PulseInputs) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (action2CeIVRemaining p s).molPerL)
      (-(step7Rate (action2CeIVRemaining p t) p.bmaConcentration).molPerLPerS) t := by
  unfold action2CeIVRemaining step7PseudoFirstOrderRate step7Rate
  dsimp
  have hinner : HasDerivAt
      (fun s : ℝ => -(k7.molarInvPerS * p.bmaConcentration.molPerL * s))
      (-(k7.molarInvPerS * p.bmaConcentration.molPerL)) t := by
    simpa only [id_eq, neg_mul, mul_one] using
      (hasDerivAt_id t).const_mul
        (-(k7.molarInvPerS * p.bmaConcentration.molPerL))
  convert hinner.exp.const_mul p.initialCeriumIV.molPerL using 1
  all_goals first | rfl | ring

theorem action2_processC_ledger_conditional_contest_model
    (p : Action2PulseInputs) (t : ℝ) :
    IsStep7MoleLedger (action2ProcessCExtentAmount p t)
      (action2Step7Ledger p t) := by
  exact canonicalStep7MoleLedger_valid _

theorem action2_processC_availability_conditional_contest_model
    (p : Action2PulseInputs) (h_admissible : Action2Admissible p) :
    0 < (action2ProcessCExtentAmount p (action2KineticWindow p).second).mol ∧
    (action2ProcessCExtentAmount p (action2KineticWindow p).second).mol ≤
      p.initialCeriumIV.molPerL * p.mixedVolume.liter ∧
    (action2ProcessCExtentAmount p (action2KineticWindow p).second).mol ≤
      p.bmaAvailable.mol := by
  rcases h_admissible with
    ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
      hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
      hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩
  have hMixed : p.mixedVolume.liter = 1001 / 1000 := by
    rw [hMixV, hV, hDoseV]
    norm_num
  have hWindow : (action2KineticWindow p).second = 1 / 10 := by
    norm_num [action2KineticWindow, hMixT, hObsT]
  have hExpPos : 0 < Real.exp (-(1 / 10 : ℝ)) := Real.exp_pos _
  have hExpLt : Real.exp (-(1 / 10 : ℝ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  have hExtentEq :
      (action2ProcessCExtentAmount p (action2KineticWindow p).second).mol =
        p.initialCeriumIV.molPerL * p.mixedVolume.liter *
          (1 - Real.exp (-(1 / 10 : ℝ))) := by
    simp only [action2ProcessCExtentAmount, action2ProcessCExtentConcentration,
      action2CeIVRemaining, step7PseudoFirstOrderRate, k7]
    rw [hWindow, hBma]
    ring
  rw [hExtentEq]
  have hInventoryPos :
      0 < p.initialCeriumIV.molPerL * p.mixedVolume.liter := by
    rw [hMixed]
    positivity
  have hExtentPos := mul_pos hInventoryPos (sub_pos.mpr hExpLt)
  have hExtentInventory :
      p.initialCeriumIV.molPerL * p.mixedVolume.liter *
          (1 - Real.exp (-(1 / 10 : ℝ))) ≤
        p.initialCeriumIV.molPerL * p.mixedVolume.liter := by
    nlinarith [mul_pos hInventoryPos hExpPos]
  exact ⟨hExtentPos, hExtentInventory, hExtentInventory.trans hCeAvail⟩

/-- The chosen pre-observation state is genuinely Process B and initially
supersaturated; neither fact follows merely from a positive silver dose. -/
theorem action2_initial_branch_and_supersaturation_conditional_contest_model
    (p : Action2PulseInputs) (h_admissible : Action2Admissible p) :
    criticalBromide.molPerL < p.initialBromide.molPerL ∧
    agBrKsp25C.molarSquared <
      (action2SilverDoseConcentration p).molPerL * p.initialBromide.molPerL := by
  rcases h_admissible with
    ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
      hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
      hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩
  have hMixed : p.mixedVolume.liter = 1001 / 1000 := by
    rw [hMixV, hV, hDoseV]
    norm_num
  constructor
  · rw [criticalBromide_eq]
    nlinarith
  · have hSilverLo : 3000 / 1001 / 1000000 ≤
        (action2SilverDoseConcentration p).molPerL := by
      simp only [action2SilverDoseConcentration]
      rw [hMixed]
      norm_num at hAgLo ⊢
      linarith
    have hMul := mul_le_mul hSilverLo hBrLo (by positivity) (by positivity)
    norm_num [agBrKsp25C] at hMul ⊢
    nlinarith

/-! The following two private functions are a bounded Picard--Lindelöf
extension of the physical precipitation extent equation.  The clipping is
used only to obtain a globally bounded local-existence problem; the invariant
region argument in `action2_trajectory_exists_conditional_contest_model`
proves that neither clip is active on the physical time window. -/

private def action2AvailableBromide
    (p : Action2PulseInputs) (t : ℝ) : ℝ :=
  p.initialBromide.molPerL +
    (action2ProcessCExtentConcentration p t).molPerL

private def action2IonProductFromExtent
    (p : Action2PulseInputs) (t q : ℝ) : ℝ :=
  ((action2SilverDoseConcentration p).molPerL - q) *
    (action2AvailableBromide p t - q)

private def action2RawExtentFlux
    (p : Action2PulseInputs) (t q : ℝ) : ℝ :=
  p.precipitationRateConstant.molarInvPerS *
    (action2IonProductFromExtent p t q - agBrKsp25C.molarSquared)

private def action2ClippedExtentFlux
    (p : Action2PulseInputs) (t q : ℝ) : ℝ :=
  min (max (action2RawExtentFlux p t q) 0) 1

private theorem action2_processC_extent_deriv
    (p : Action2PulseInputs) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (action2ProcessCExtentConcentration p s).molPerL)
      (step7Rate (action2CeIVRemaining p t) p.bmaConcentration).molPerLPerS t := by
  have hCe := action2_processC_massAction_carrier_conditional_contest_model p t
  have h := hCe.const_sub p.initialCeriumIV.molPerL
  simpa only [action2ProcessCExtentConcentration, neg_neg] using h

private theorem action2_picard_extent_exists
    (p : Action2PulseInputs) (h_admissible : Action2Admissible p) :
    ∃ q : ℝ → ℝ, q 0 = 0 ∧
      ∀ t ∈ Set.Icc (-(1 / 100 : ℝ)) (11 / 100 : ℝ),
        HasDerivWithinAt q (action2ClippedExtentFlux p t (q t))
          (Set.Icc (-(1 / 100 : ℝ)) (11 / 100 : ℝ)) t := by
  rcases h_admissible with
    ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
      hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
      hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩
  have hMixed : p.mixedVolume.liter = 1001 / 1000 := by
    rw [hMixV, hV, hDoseV]
    norm_num
  have hSilverPos : 0 < (action2SilverDoseConcentration p).molPerL := by
    simp only [action2SilverDoseConcentration]
    rw [hMixed]
    positivity
  have hSilverLe : (action2SilverDoseConcentration p).molPerL ≤ 1 := by
    norm_num [ceriumIVSourceScale] at hPulseScale
    linarith
  have hStockBounds (t : ℝ) (htLo : -(1 / 100 : ℝ) ≤ t)
      (htHi : t ≤ 11 / 100) :
      -1 ≤ p.initialBromide.molPerL +
          (action2ProcessCExtentConcentration p t).molPerL ∧
      p.initialBromide.molPerL +
          (action2ProcessCExtentConcentration p t).molPerL ≤ 1 := by
    have hExpPos := Real.exp_pos (-t)
    have hExpLtThree : Real.exp (-t) < 3 := by
      exact (Real.exp_lt_exp.mpr (by linarith)).trans Real.exp_one_lt_three
    have hCeExp := mul_le_mul_of_nonneg_left (le_of_lt hExpLtThree) (le_of_lt hCePos)
    have hCeExpNonneg :
        0 ≤ p.initialCeriumIV.molPerL * Real.exp (-t) :=
      mul_nonneg (le_of_lt hCePos) (le_of_lt hExpPos)
    have hCeExpUpper :
        p.initialCeriumIV.molPerL * Real.exp (-t) ≤ 3 / 100000000 := by
      nlinarith
    have hExtent :
        (action2ProcessCExtentConcentration p t).molPerL =
          p.initialCeriumIV.molPerL * (1 - Real.exp (-t)) := by
      simp only [action2ProcessCExtentConcentration, action2CeIVRemaining,
        step7PseudoFirstOrderRate, k7]
      rw [hBma]
      ring
    rw [hExtent]
    constructor <;> nlinarith
  let t₀ : Set.Icc (-(1 / 100 : ℝ)) (11 / 100 : ℝ) :=
    ⟨0, by norm_num, by norm_num⟩
  have hPicard : IsPicardLindelof (action2ClippedExtentFlux p) t₀ 0
      (1 : NNReal) (0 : NNReal) (1 : NNReal) (1000000000 : NNReal) := by
    refine
      { lipschitzOnWith := ?_
        continuousOn := ?_
        norm_le := ?_
        mul_max_le := ?_ }
    · intro t ht
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro q hq r hr
      have hqAbs : |q| ≤ 1 := by
        simpa [Metric.mem_closedBall, Real.dist_eq] using hq
      have hrAbs : |r| ≤ 1 := by
        simpa [Metric.mem_closedBall, Real.dist_eq] using hr
      have hqBounds := (abs_le.mp hqAbs)
      have hrBounds := (abs_le.mp hrAbs)
      have hStock := hStockBounds t ht.1 ht.2
      have hFactor :
          |q + r - (action2SilverDoseConcentration p).molPerL -
            (p.initialBromide.molPerL +
              (action2ProcessCExtentConcentration p t).molPerL)| ≤ 4 := by
        rw [abs_le]
        constructor <;> nlinarith
      have hRawDiff :
          action2RawExtentFlux p t q - action2RawExtentFlux p t r =
            p.precipitationRateConstant.molarInvPerS * (q - r) *
              (q + r - (action2SilverDoseConcentration p).molPerL -
                (p.initialBromide.molPerL +
                  (action2ProcessCExtentConcentration p t).molPerL)) := by
        simp only [action2RawExtentFlux, action2IonProductFromExtent,
          action2AvailableBromide]
        ring
      have hRawDistance :
          |action2RawExtentFlux p t q - action2RawExtentFlux p t r| ≤
            1000000000 * |q - r| := by
        rw [hRawDiff, abs_mul, abs_mul, hRate, abs_of_nonneg (by norm_num)]
        have hBaseNonneg :
            0 ≤ (100000000 : ℝ) * |q - r| :=
          mul_nonneg (by norm_num) (abs_nonneg _)
        have hMul := mul_le_mul_of_nonneg_left hFactor
          hBaseNonneg
        calc
          100000000 * |q - r| *
              |q + r - (action2SilverDoseConcentration p).molPerL -
                (p.initialBromide.molPerL +
                  (action2ProcessCExtentConcentration p t).molPerL)| ≤
              100000000 * |q - r| * 4 := hMul
          _ ≤ 1000000000 * |q - r| := by
            nlinarith [abs_nonneg (q - r)]
      simp only [action2ClippedExtentFlux, Real.dist_eq]
      change
        |min (max (action2RawExtentFlux p t q) 0) 1 -
            min (max (action2RawExtentFlux p t r) 0) 1| ≤
          (1000000000 : ℝ) * |q - r|
      calc
        |min (max (action2RawExtentFlux p t q) 0) 1 -
            min (max (action2RawExtentFlux p t r) 0) 1| ≤
            |max (action2RawExtentFlux p t q) 0 -
              max (action2RawExtentFlux p t r) 0| := by
                simpa using abs_min_sub_min_le_max
                  (max (action2RawExtentFlux p t q) 0) 1
                  (max (action2RawExtentFlux p t r) 0) 1
        _ ≤ |action2RawExtentFlux p t q - action2RawExtentFlux p t r| :=
          abs_max_sub_max_le_abs _ _ 0
        _ ≤ 1000000000 * |q - r| := hRawDistance
    · intro q hq
      have hCe : Continuous
          (fun t : ℝ => (action2CeIVRemaining p t).molPerL) := by
        unfold action2CeIVRemaining
        fun_prop
      have hExtent : Continuous
          (fun t : ℝ =>
            (action2ProcessCExtentConcentration p t).molPerL) := by
        exact continuous_const.sub hCe
      have hAvailable : Continuous (action2AvailableBromide p) := by
        exact continuous_const.add hExtent
      have hIon : Continuous
          (fun t : ℝ => action2IonProductFromExtent p t q) := by
        unfold action2IonProductFromExtent
        exact continuous_const.mul (hAvailable.sub continuous_const)
      have hRaw : Continuous (fun t : ℝ => action2RawExtentFlux p t q) := by
        unfold action2RawExtentFlux
        exact continuous_const.mul (hIon.sub continuous_const)
      exact (hRaw.max continuous_const).min continuous_const |>.continuousOn
    · intro t ht q hq
      change |action2ClippedExtentFlux p t q| ≤ 1
      rw [abs_of_nonneg]
      · exact min_le_right _ _
      · exact le_min (le_max_right _ _) zero_le_one
    · norm_num [t₀]
  simpa only [t₀] using hPicard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- The explicit locally Lipschitz mass-action initial-value problem has a
physical trajectory for every admissible primitive tuple; requested effects
therefore cannot be obtained by vacuity. -/
theorem action2_trajectory_exists_conditional_contest_model
    (p : Action2PulseInputs) (h_admissible : Action2Admissible p) :
    ∃ x : Action2KineticTrajectory, IsAction2KineticTrajectory p x := by
  obtain ⟨q, hqZero, hqWithin⟩ :=
    action2_picard_extent_exists p h_admissible
  rcases h_admissible with
    ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
      hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
      hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩
  have hMixed : p.mixedVolume.liter = 1001 / 1000 := by
    rw [hMixV, hV, hDoseV]
    norm_num
  have hWindow : (action2KineticWindow p).second = 1 / 10 := by
    norm_num [action2KineticWindow, hMixT, hObsT]
  have hWindowPos : 0 < (action2KineticWindow p).second := by
    rw [hWindow]
    norm_num
  have hqDeriv (t : ℝ) (htNonneg : 0 ≤ t)
      (htBounded : t ≤ (action2KineticWindow p).second) :
      HasDerivAt q (action2ClippedExtentFlux p t (q t)) t := by
    have htWide : t ∈ Set.Icc (-(1 / 100 : ℝ)) (11 / 100 : ℝ) := by
      rw [hWindow] at htBounded
      constructor <;> nlinarith
    exact (hqWithin t htWide).hasDerivAt
      (Icc_mem_nhds (by nlinarith [htNonneg]) (by
        rw [hWindow] at htBounded
        nlinarith))
  have hExtentBounds (t : ℝ) (htNonneg : 0 ≤ t) :
      0 ≤ (action2ProcessCExtentConcentration p t).molPerL ∧
      (action2ProcessCExtentConcentration p t).molPerL ≤
        p.initialCeriumIV.molPerL := by
    have hExpPos := Real.exp_pos (-t)
    have hExpLe : Real.exp (-t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have hExtent :
        (action2ProcessCExtentConcentration p t).molPerL =
          p.initialCeriumIV.molPerL * (1 - Real.exp (-t)) := by
      simp only [action2ProcessCExtentConcentration, action2CeIVRemaining,
        step7PseudoFirstOrderRate, k7]
      rw [hBma]
      ring
    rw [hExtent]
    constructor
    · positivity
    · nlinarith [mul_pos hCePos hExpPos]
  have hStockDeriv (t : ℝ) :
      HasDerivAt (action2AvailableBromide p)
        (step7Rate (action2CeIVRemaining p t) p.bmaConcentration).molPerLPerS t := by
    unfold action2AvailableBromide
    exact (action2_processC_extent_deriv p t).const_add p.initialBromide.molPerL
  have hStockZero : action2AvailableBromide p 0 = p.initialBromide.molPerL := by
    simp [action2AvailableBromide, action2ProcessCExtentConcentration,
      action2CeIVRemaining]
  have hSourcePos (t : ℝ) :
      0 < (step7Rate (action2CeIVRemaining p t)
        p.bmaConcentration).molPerLPerS := by
    simp only [step7Rate, action2CeIVRemaining, step7PseudoFirstOrderRate, k7]
    rw [hBma]
    positivity
  have hSilverPos : 0 < (action2SilverDoseConcentration p).molPerL := by
    simp only [action2SilverDoseConcentration]
    rw [hMixed]
    positivity
  have hSilverLower : 3000 / 1001 / 1000000 ≤
      (action2SilverDoseConcentration p).molPerL := by
    simp only [action2SilverDoseConcentration]
    rw [hMixed]
    norm_num at hAgLo ⊢
    linarith
  have hStockUpper (t : ℝ) (htNonneg : 0 ≤ t) :
      action2AvailableBromide p t ≤ 61 / 100000000 := by
    have hExtent := (hExtentBounds t htNonneg).2
    simp only [action2AvailableBromide]
    nlinarith
  have hStockPos (t : ℝ) (htNonneg : 0 ≤ t) :
      0 < action2AvailableBromide p t := by
    have hExtent := (hExtentBounds t htNonneg).1
    simp only [action2AvailableBromide]
    nlinarith
  have hStockLtSilver (t : ℝ) (htNonneg : 0 ≤ t) :
      action2AvailableBromide p t <
        (action2SilverDoseConcentration p).molPerL := by
    calc
      action2AvailableBromide p t ≤ 61 / 100000000 := hStockUpper t htNonneg
      _ < 3000 / 1001 / 1000000 := by norm_num
      _ ≤ (action2SilverDoseConcentration p).molPerL := hSilverLower
  have hqContinuous : ContinuousOn q
      (Set.Icc 0 (action2KineticWindow p).second) := by
    intro t ht
    exact (hqDeriv t ht.1 ht.2).continuousAt.continuousWithinAt
  have hqMonotone : MonotoneOn q
      (Set.Icc 0 (action2KineticWindow p).second) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hqContinuous
    · intro t ht
      rw [interior_Icc] at ht
      exact (hqDeriv t (le_of_lt ht.1) (le_of_lt ht.2)).hasDerivWithinAt
    · intro t ht
      exact le_min (le_max_right _ _) zero_le_one
  have hqNonneg (t : ℝ) (htNonneg : 0 ≤ t)
      (htBounded : t ≤ (action2KineticWindow p).second) : 0 ≤ q t := by
    have hmono := hqMonotone
      (⟨le_rfl, le_of_lt hWindowPos⟩ : 0 ∈
        Set.Icc 0 (action2KineticWindow p).second)
      (⟨htNonneg, htBounded⟩ : t ∈
        Set.Icc 0 (action2KineticWindow p).second) htNonneg
    simpa only [hqZero] using hmono
  have hStockContinuous : ContinuousOn (action2AvailableBromide p)
      (Set.Icc 0 (action2KineticWindow p).second) := by
    intro t ht
    exact (hStockDeriv t).continuousAt.continuousWithinAt
  have hqLeStock (t : ℝ) (htNonneg : 0 ≤ t)
      (htBounded : t ≤ (action2KineticWindow p).second) :
      q t ≤ action2AvailableBromide p t := by
    apply image_le_of_deriv_right_lt_deriv_boundary'
      hqContinuous
      (fun s hs => (hqDeriv s hs.1 (le_of_lt hs.2)).hasDerivWithinAt)
      (B := action2AvailableBromide p)
      (B' := fun s =>
        (step7Rate (action2CeIVRemaining p s)
          p.bmaConcentration).molPerLPerS)
    · rw [hqZero, hStockZero]
      exact le_of_lt (lt_of_lt_of_le (by norm_num) hBrLo)
    · exact hStockContinuous
    · intro s hs
      exact (hStockDeriv s).hasDerivWithinAt
    · intro s hs hBoundary
      have hRawNeg : action2RawExtentFlux p s (q s) < 0 := by
        rw [hBoundary]
        simp only [action2RawExtentFlux, action2IonProductFromExtent]
        rw [sub_self, mul_zero, zero_sub, hRate]
        norm_num [agBrKsp25C]
      have hClipZero : action2ClippedExtentFlux p s (q s) = 0 := by
        simp [action2ClippedExtentFlux, max_eq_right (le_of_lt hRawNeg)]
      rw [hClipZero]
      exact hSourcePos s
    · exact ⟨htNonneg, htBounded⟩
  have hProductContinuous : ContinuousOn
      (fun t : ℝ =>
        ((action2SilverDoseConcentration p).molPerL - q t) *
          (action2AvailableBromide p t - q t))
      (Set.Icc 0 (action2KineticWindow p).second) :=
    (continuousOn_const.sub hqContinuous).mul
      (hStockContinuous.sub hqContinuous)
  have hProductDeriv (t : ℝ) (htNonneg : 0 ≤ t)
      (htBounded : t ≤ (action2KineticWindow p).second) :
      HasDerivAt
        (fun s : ℝ =>
          ((action2SilverDoseConcentration p).molPerL - q s) *
            (action2AvailableBromide p s - q s))
        (-(action2ClippedExtentFlux p t (q t)) *
            (action2AvailableBromide p t - q t) +
          ((action2SilverDoseConcentration p).molPerL - q t) *
            ((step7Rate (action2CeIVRemaining p t)
              p.bmaConcentration).molPerLPerS -
              action2ClippedExtentFlux p t (q t))) t := by
    convert ((hqDeriv t htNonneg htBounded).const_sub
      (action2SilverDoseConcentration p).molPerL).mul
        ((hStockDeriv t).sub (hqDeriv t htNonneg htBounded)) using 1
    all_goals first | rfl | ring
  have hProductKsp (t : ℝ) (htNonneg : 0 ≤ t)
      (htBounded : t ≤ (action2KineticWindow p).second) :
      agBrKsp25C.molarSquared ≤
        ((action2SilverDoseConcentration p).molPerL - q t) *
          (action2AvailableBromide p t - q t) := by
    have hSuper :=
      (action2_initial_branch_and_supersaturation_conditional_contest_model p
        ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
          hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
          hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩).2
    apply image_le_of_deriv_right_lt_deriv_boundary'
      (a := 0) (b := (action2KineticWindow p).second)
      (f := fun _ : ℝ => agBrKsp25C.molarSquared)
      (f' := fun _ : ℝ => 0)
      (B := fun s : ℝ =>
        ((action2SilverDoseConcentration p).molPerL - q s) *
          (action2AvailableBromide p s - q s))
      (B' := fun s : ℝ =>
        -(action2ClippedExtentFlux p s (q s)) *
            (action2AvailableBromide p s - q s) +
          ((action2SilverDoseConcentration p).molPerL - q s) *
            ((step7Rate (action2CeIVRemaining p s)
              p.bmaConcentration).molPerLPerS -
              action2ClippedExtentFlux p s (q s)))
      continuousOn_const
      (fun s hs => (hasDerivAt_const s _).hasDerivWithinAt)
    · simpa [hqZero, hStockZero] using le_of_lt hSuper
    · exact hProductContinuous
    · intro s hs
      exact (hProductDeriv s hs.1 (le_of_lt hs.2)).hasDerivWithinAt
    · intro s hs hBoundary
      have hRawZero : action2RawExtentFlux p s (q s) = 0 := by
        simp only [action2RawExtentFlux, action2IonProductFromExtent]
        rw [← hBoundary, sub_self, mul_zero]
      have hClipZero : action2ClippedExtentFlux p s (q s) = 0 := by
        simp [action2ClippedExtentFlux, hRawZero]
      have hSilverRemainingPos :
          0 < (action2SilverDoseConcentration p).molPerL - q s := by
        have hqs := hqLeStock s hs.1 (le_of_lt hs.2)
        have hss := hStockLtSilver s hs.1
        linarith
      rw [hClipZero]
      simpa only [neg_zero, zero_mul, zero_add, sub_zero] using
        mul_pos hSilverRemainingPos (hSourcePos s)
    · exact ⟨htNonneg, htBounded⟩
  have hClipEqRaw (t : ℝ) (htNonneg : 0 ≤ t)
      (htBounded : t ≤ (action2KineticWindow p).second) :
      action2ClippedExtentFlux p t (q t) = action2RawExtentFlux p t (q t) := by
    have hq0 := hqNonneg t htNonneg htBounded
    have hqs := hqLeStock t htNonneg htBounded
    have hstock0 := hStockPos t htNonneg
    have hstockUpper := hStockUpper t htNonneg
    have hsilverRemainingNonneg :
        0 ≤ (action2SilverDoseConcentration p).molPerL - q t := by
      linarith [hStockLtSilver t htNonneg]
    have hbromideRemainingNonneg : 0 ≤ action2AvailableBromide p t - q t :=
      sub_nonneg.mpr hqs
    have hsilverRemainingUpper :
        (action2SilverDoseConcentration p).molPerL - q t ≤
          (action2SilverDoseConcentration p).molPerL := by linarith
    have hbromideRemainingUpper :
        action2AvailableBromide p t - q t ≤ action2AvailableBromide p t := by
      linarith
    have hSilverUpper :
        (action2SilverDoseConcentration p).molPerL ≤ 1 / 300000 := by
      norm_num [ceriumIVSourceScale] at hPulseScale
      exact hPulseScale
    have hProductUpper := mul_le_mul hsilverRemainingUpper
      hbromideRemainingUpper hbromideRemainingNonneg
      (le_trans hsilverRemainingNonneg hsilverRemainingUpper)
    have hStockProductUpper := mul_le_mul hSilverUpper hstockUpper
      (le_of_lt hstock0) (by positivity)
    have hRawNonneg : 0 ≤ action2RawExtentFlux p t (q t) := by
      simp only [action2RawExtentFlux, action2IonProductFromExtent]
      exact mul_nonneg (by rw [hRate]; norm_num)
        (sub_nonneg.mpr (hProductKsp t htNonneg htBounded))
    have hRawLtOne : action2RawExtentFlux p t (q t) < 1 := by
      simp only [action2RawExtentFlux, action2IonProductFromExtent]
      rw [hRate]
      norm_num [agBrKsp25C] at hProductUpper hStockProductUpper ⊢
      nlinarith
    simp [action2ClippedExtentFlux, max_eq_left hRawNonneg,
      min_eq_left (le_of_lt hRawLtOne)]
  let x : Action2KineticTrajectory :=
    { dissolvedSilver := fun t =>
        ⟨(action2SilverDoseConcentration p).molPerL - q t⟩
      dissolvedBromide := fun t => ⟨action2AvailableBromide p t - q t⟩
      solidAgBrEquivalent := fun t => ⟨q t⟩ }
  refine ⟨x, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [x, hqZero]
  · simp [x, hqZero, hStockZero]
  · simp [x, hqZero]
  · intro t htNonneg htBounded
    have hq0 := hqNonneg t htNonneg htBounded
    have hqs := hqLeStock t htNonneg htBounded
    have hstockSilver := hStockLtSilver t htNonneg
    have hclip := hClipEqRaw t htNonneg htBounded
    have hPrecip :
        (action2PrecipitationFluxAt p x t).molPerLPerS =
          action2RawExtentFlux p t (q t) := by
      simp [action2PrecipitationFluxAt, agBrNetPrecipitationFlux,
        action2RawExtentFlux, action2IonProductFromExtent, x]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · change 0 ≤ (action2SilverDoseConcentration p).molPerL - q t
      linarith
    · change 0 ≤ action2AvailableBromide p t - q t
      linarith
    · change 0 ≤ q t
      exact hq0
    · change HasDerivAt
        (fun s : ℝ => (action2SilverDoseConcentration p).molPerL - q s)
        (-(action2PrecipitationFluxAt p x t).molPerLPerS) t
      apply ((hqDeriv t htNonneg htBounded).const_sub
        (action2SilverDoseConcentration p).molPerL).congr_deriv
      rw [hPrecip, ← hclip]
    · change HasDerivAt
        (fun s : ℝ => action2AvailableBromide p s - q s)
        ((step7Rate (action2CeIVRemaining p t)
            p.bmaConcentration).molPerLPerS -
          (action2PrecipitationFluxAt p x t).molPerLPerS) t
      apply ((hStockDeriv t).sub (hqDeriv t htNonneg htBounded)).congr_deriv
      rw [hPrecip, ← hclip]
    · change HasDerivAt (fun s : ℝ => q s)
        (action2PrecipitationFluxAt p x t).molPerLPerS t
      apply (hqDeriv t htNonneg htBounded).congr_deriv
      rw [hPrecip, ← hclip]

/-- Component balances are consequences of the three differential laws and
their initial values, not fields of the trajectory predicate. -/
theorem action2_component_balances_conditional_contest_model
    (p : Action2PulseInputs) (h_admissible : Action2Admissible p)
    (x : Action2KineticTrajectory) (h_trajectory : IsAction2KineticTrajectory p x)
    (t : ℝ) (h_time_nonnegative : 0 ≤ t)
    (h_time_bounded : t ≤ (action2KineticWindow p).second) :
    (x.dissolvedSilver t).molPerL + (x.solidAgBrEquivalent t).molPerL =
        (action2SilverDoseConcentration p).molPerL ∧
    (x.dissolvedBromide t).molPerL + (x.solidAgBrEquivalent t).molPerL =
        p.initialBromide.molPerL +
          (action2ProcessCExtentConcentration p t).molPerL := by
  rcases h_trajectory with ⟨hSilverZero, hBromideZero, hSolidZero, hODE⟩
  have hConst (f : ℝ → ℝ)
      (hf : ∀ s ∈ Set.Icc 0 t, HasDerivAt f 0 s) : f t = f 0 := by
    have hNorm := (convex_Icc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
      (C := 0)
      (fun s hs => (hf s hs).hasDerivWithinAt)
      (fun s hs => by simp) ⟨le_rfl, h_time_nonnegative⟩ ⟨h_time_nonnegative, le_rfl⟩
    have hNorm' : ‖f t - f 0‖ ≤ 0 := by
      simpa only [zero_mul] using hNorm
    have hNormZero : ‖f t - f 0‖ = 0 :=
      le_antisymm hNorm' (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hNormZero)
  have hSilverConst := hConst
    (fun s => (x.dissolvedSilver s).molPerL +
      (x.solidAgBrEquivalent s).molPerL) (by
      intro s hs
      rcases hODE s hs.1 (hs.2.trans h_time_bounded) with
        ⟨hSNonneg, hBNonneg, hQNonneg, hSDeriv, hBDeriv, hQDeriv⟩
      exact (hSDeriv.add hQDeriv).congr_deriv (by ring))
  have hBromideConst := hConst
    (fun s => (x.dissolvedBromide s).molPerL +
      (x.solidAgBrEquivalent s).molPerL - p.initialBromide.molPerL -
      (action2ProcessCExtentConcentration p s).molPerL) (by
      intro s hs
      rcases hODE s hs.1 (hs.2.trans h_time_bounded) with
        ⟨hSNonneg, hBNonneg, hQNonneg, hSDeriv, hBDeriv, hQDeriv⟩
      have hExtent := action2_processC_extent_deriv p s
      convert (((hBDeriv.add hQDeriv).sub_const
        p.initialBromide.molPerL).sub hExtent) using 1
      all_goals first | rfl | ring)
  constructor
  · simpa [hSilverZero, hSolidZero] using hSilverConst
  · have hExtentZero :
        (action2ProcessCExtentConcentration p 0).molPerL = 0 := by
      simp [action2ProcessCExtentConcentration, action2CeIVRemaining]
    have h := hBromideConst
    simp [hBromideZero, hSolidZero, hExtentZero] at h
    linarith

/-- Even after every available Ce(IV) equivalent has become bromide, more than
`2.3e-6 M` dissolved silver remains. -/
theorem action2_silver_floor_conditional_contest_model
    (p : Action2PulseInputs) (h_admissible : Action2Admissible p)
    (x : Action2KineticTrajectory) (h_trajectory : IsAction2KineticTrajectory p x) :
    23 / 10000000 < (action2SilverFloor p).molPerL ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ (action2KineticWindow p).second →
      (action2SilverFloor p).molPerL ≤ (x.dissolvedSilver t).molPerL := by
  rcases h_admissible with
    ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
      hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
      hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩
  have hMixed : p.mixedVolume.liter = 1001 / 1000 := by
    rw [hMixV, hV, hDoseV]
    norm_num
  have hSilverLo : 3000 / 1001 / 1000000 ≤
      (action2SilverDoseConcentration p).molPerL := by
    simp only [action2SilverDoseConcentration]
    rw [hMixed]
    norm_num at hAgLo ⊢
    linarith
  have hFloor : 23 / 10000000 < (action2SilverFloor p).molPerL := by
    simp only [action2SilverFloor]
    nlinarith
  refine ⟨hFloor, ?_⟩
  intro t htNonneg htBounded
  have hBalances := action2_component_balances_conditional_contest_model p
    ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
      hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
      hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩
    x h_trajectory t htNonneg htBounded
  rcases h_trajectory.2.2.2 t htNonneg htBounded with
    ⟨hSNonneg, hBNonneg, hQNonneg, hSDeriv, hBDeriv, hQDeriv⟩
  have hExtentLe :
      (action2ProcessCExtentConcentration p t).molPerL ≤
        p.initialCeriumIV.molPerL := by
    have hExpPos := Real.exp_pos
      (-(step7PseudoFirstOrderRate p.bmaConcentration).perS * t)
    simp only [action2ProcessCExtentConcentration, action2CeIVRemaining]
    nlinarith [mul_pos hCePos hExpPos]
  simp only [action2SilverFloor]
  nlinarith [hBalances.1, hBalances.2]

/-- Whenever bromide has not yet crossed, Ksp, the silver floor, the chosen
finite rate coefficient, and the printed step-(7) source together give at
least `2e-5 M s⁻¹` net removal. -/
theorem action2_net_removal_margin_conditional_contest_model
    (p : Action2PulseInputs) (h_admissible : Action2Admissible p)
    (x : Action2KineticTrajectory) (h_trajectory : IsAction2KineticTrajectory p x)
    (t : ℝ) (h_time_nonnegative : 0 ≤ t)
    (h_time_bounded : t ≤ (action2KineticWindow p).second)
    (h_not_crossed : criticalBromide.molPerL ≤
      (x.dissolvedBromide t).molPerL) :
    (step7Rate (action2CeIVRemaining p t) p.bmaConcentration).molPerLPerS +
        action2ThresholdDownwardMargin.molPerLPerS <
      (action2PrecipitationFluxAt p x t).molPerLPerS := by
  rcases h_admissible with
    ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
      hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
      hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩
  have hMixed : p.mixedVolume.liter = 1001 / 1000 := by
    rw [hMixV, hV, hDoseV]
    norm_num
  have hSilverDoseLower : 3000 / 1001 / 1000000 ≤
      (action2SilverDoseConcentration p).molPerL := by
    simp only [action2SilverDoseConcentration]
    rw [hMixed]
    norm_num at hAgLo ⊢
    linarith
  have hFloorLower :
      3000 / 1001 / 1000000 - 6 / 10000000 - 1 / 100000000 ≤
        (action2SilverFloor p).molPerL := by
    simp only [action2SilverFloor]
    nlinarith
  have hSilverAt := (action2_silver_floor_conditional_contest_model p
    ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
      hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
      hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩ x h_trajectory).2
      t h_time_nonnegative h_time_bounded
  have hSilverNonneg :=
    (h_trajectory.2.2.2 t h_time_nonnegative h_time_bounded).1
  rw [criticalBromide_eq] at h_not_crossed
  have hProductLower := mul_le_mul
    (hFloorLower.trans hSilverAt) h_not_crossed (by norm_num) hSilverNonneg
  have hExpLe : Real.exp
      (-(step7PseudoFirstOrderRate p.bmaConcentration).perS * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    simp only [step7PseudoFirstOrderRate, k7]
    rw [hBma]
    norm_num
    exact h_time_nonnegative
  have hSourceExpr :
      (step7Rate (action2CeIVRemaining p t)
        p.bmaConcentration).molPerLPerS =
        p.initialCeriumIV.molPerL * Real.exp (-t) := by
    simp only [step7Rate, action2CeIVRemaining, step7PseudoFirstOrderRate, k7]
    rw [hBma]
    ring
  have hSourceLe :
      (step7Rate (action2CeIVRemaining p t)
        p.bmaConcentration).molPerLPerS ≤ 1 / 100000000 := by
    rw [hSourceExpr]
    have hExpLe' : Real.exp (-t) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (by linarith)
    have hCeExp := mul_le_mul_of_nonneg_left
      hExpLe'
      (le_of_lt hCePos)
    nlinarith
  simp only [action2PrecipitationFluxAt, agBrNetPrecipitationFlux,
    action2ThresholdDownwardMargin]
  rw [hRate]
  norm_num [agBrKsp25C] at hProductLower ⊢
  nlinarith

/-- The finite-time differential bound forces an actual downward crossing by
`0.02 s`; an equilibrium root is not substituted for this transient state. -/
theorem action2_crosses_by_deadline_conditional_contest_model
    (p : Action2PulseInputs) (h_admissible : Action2Admissible p)
    (x : Action2KineticTrajectory) (h_trajectory : IsAction2KineticTrajectory p x) :
    ∃ t : ℝ, 0 < t ∧ t ≤ action2CrossingDeadline.second ∧
      (x.dissolvedBromide t).molPerL < criticalBromide.molPerL := by
  have hWindow :
      (action2KineticWindow p).second = 1 / 10 :=
    action2_kinetic_window_eq_conditional_contest_model p h_admissible
  have hDeadline :
      action2CrossingDeadline.second = 1 / 50 := rfl
  have hDeadlineWindow :
      action2CrossingDeadline.second ≤ (action2KineticWindow p).second := by
    rw [hDeadline, hWindow]
    norm_num
  have hBromideDeriv (t : ℝ) (htNonneg : 0 ≤ t)
      (htBounded : t ≤ (action2KineticWindow p).second) :
      HasDerivAt (fun s : ℝ => (x.dissolvedBromide s).molPerL)
        ((step7Rate (action2CeIVRemaining p t)
            p.bmaConcentration).molPerLPerS -
          (action2PrecipitationFluxAt p x t).molPerLPerS) t :=
    (h_trajectory.2.2.2 t htNonneg htBounded).2.2.2.2.1
  by_contra hCross
  push_neg at hCross
  have hNotCrossed (t : ℝ) (ht : t ∈ Set.Ico 0 action2CrossingDeadline.second) :
      criticalBromide.molPerL ≤ (x.dissolvedBromide t).molPerL := by
    rcases eq_or_lt_of_le ht.1 with rfl | htPos
    · have hInitial :=
        (action2_initial_branch_and_supersaturation_conditional_contest_model
          p h_admissible).1
      simpa [h_trajectory.2.1] using le_of_lt hInitial
    · exact hCross t htPos (le_of_lt ht.2)
  have hBromideContinuous : ContinuousOn
      (fun t : ℝ => (x.dissolvedBromide t).molPerL)
      (Set.Icc 0 action2CrossingDeadline.second) := by
    intro t ht
    exact (hBromideDeriv t ht.1 (ht.2.trans hDeadlineWindow)).continuousAt.continuousWithinAt
  have hDerivativeBound (t : ℝ)
      (ht : t ∈ Set.Ico 0 action2CrossingDeadline.second) :
      (step7Rate (action2CeIVRemaining p t)
          p.bmaConcentration).molPerLPerS -
          (action2PrecipitationFluxAt p x t).molPerLPerS ≤
        -action2ThresholdDownwardMargin.molPerLPerS := by
    have hMargin :=
      action2_net_removal_margin_conditional_contest_model p h_admissible x
        h_trajectory t ht.1 (le_trans (le_of_lt ht.2) hDeadlineWindow)
        (hNotCrossed t ht)
    linarith
  have hLinearBound :
      (x.dissolvedBromide action2CrossingDeadline.second).molPerL ≤
        p.initialBromide.molPerL -
          action2ThresholdDownwardMargin.molPerLPerS *
            action2CrossingDeadline.second := by
    apply image_le_of_deriv_right_le_deriv_boundary
      (f' := fun t =>
        (step7Rate (action2CeIVRemaining p t)
            p.bmaConcentration).molPerLPerS -
          (action2PrecipitationFluxAt p x t).molPerLPerS)
      (B := fun t =>
        p.initialBromide.molPerL -
          action2ThresholdDownwardMargin.molPerLPerS * t)
      (B' := fun _ => -action2ThresholdDownwardMargin.molPerLPerS)
      hBromideContinuous
      (fun t ht =>
        (hBromideDeriv t ht.1
          (le_trans (le_of_lt ht.2) hDeadlineWindow)).hasDerivWithinAt)
    · simpa [h_trajectory.2.1]
    · fun_prop
    · intro t ht
      have hBoundDeriv : HasDerivAt
          (fun s : ℝ => p.initialBromide.molPerL -
            action2ThresholdDownwardMargin.molPerLPerS * s)
          (-action2ThresholdDownwardMargin.molPerLPerS) t := by
        simpa only [id_eq, mul_one, sub_eq_add_neg, neg_mul] using
          ((hasDerivAt_id t).const_mul
            (-action2ThresholdDownwardMargin.molPerLPerS)).const_add
              p.initialBromide.molPerL
      exact hBoundDeriv.hasDerivWithinAt
    · exact hDerivativeBound
    · exact ⟨by norm_num [action2CrossingDeadline],
        le_rfl⟩
  have hInitialUpper := h_admissible.2.2.2.2.2.2.1
  have hBelowCritical :
      (x.dissolvedBromide action2CrossingDeadline.second).molPerL <
        criticalBromide.molPerL := by
    rw [hDeadline, criticalBromide_eq]
    norm_num [action2ThresholdDownwardMargin, action2CrossingDeadline] at hLinearBound
    nlinarith
  have hAtDeadline := hCross action2CrossingDeadline.second
    (by norm_num [action2CrossingDeadline])
    (le_rfl)
  exact (not_lt_of_ge hAtDeadline) hBelowCritical

/-- The same inward-pointing bound at the threshold prevents a later upward
recrossing during the finite observation window. -/
theorem action2_crosses_threshold_conditional_contest_model
    (p : Action2PulseInputs) (h_admissible : Action2Admissible p)
    (x : Action2KineticTrajectory) (h_trajectory : IsAction2KineticTrajectory p x) :
    (x.dissolvedBromide (action2KineticWindow p).second).molPerL <
      criticalBromide.molPerL := by
  obtain ⟨t₀, ht₀Pos, ht₀Deadline, ht₀Below⟩ :=
    action2_crosses_by_deadline_conditional_contest_model p h_admissible x h_trajectory
  have hWindow :
      (action2KineticWindow p).second = 1 / 10 :=
    action2_kinetic_window_eq_conditional_contest_model p h_admissible
  have hDeadlineWindow :
      action2CrossingDeadline.second <
        (action2KineticWindow p).second := by
    rw [hWindow]
    norm_num [action2CrossingDeadline]
  have ht₀Window : t₀ < (action2KineticWindow p).second :=
    lt_of_le_of_lt ht₀Deadline hDeadlineWindow
  have hBromideDeriv (t : ℝ) (htNonneg : 0 ≤ t)
      (htBounded : t ≤ (action2KineticWindow p).second) :
      HasDerivAt (fun s : ℝ => (x.dissolvedBromide s).molPerL)
        ((step7Rate (action2CeIVRemaining p t)
            p.bmaConcentration).molPerLPerS -
          (action2PrecipitationFluxAt p x t).molPerLPerS) t :=
    (h_trajectory.2.2.2 t htNonneg htBounded).2.2.2.2.1
  have hBromideContinuous : ContinuousOn
      (fun t : ℝ => (x.dissolvedBromide t).molPerL)
      (Set.Icc t₀ (action2KineticWindow p).second) := by
    intro t ht
    exact (hBromideDeriv t (le_trans (le_of_lt ht₀Pos) ht.1) ht.2).continuousAt.continuousWithinAt
  have hNeverAbove (t : ℝ) (ht : t ∈
      Set.Icc t₀ (action2KineticWindow p).second) :
      (x.dissolvedBromide t).molPerL ≤ criticalBromide.molPerL := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f' := fun s =>
        (step7Rate (action2CeIVRemaining p s)
            p.bmaConcentration).molPerLPerS -
          (action2PrecipitationFluxAt p x s).molPerLPerS)
      (B := fun _ : ℝ => criticalBromide.molPerL)
      (B' := fun _ : ℝ => 0)
      hBromideContinuous
      (fun s hs =>
        (hBromideDeriv s (le_trans (le_of_lt ht₀Pos) hs.1)
          (le_of_lt hs.2)).hasDerivWithinAt)
    · exact le_of_lt ht₀Below
    · intro s
      exact hasDerivAt_const s _
    · intro s hs hBoundary
      have hMargin :=
        action2_net_removal_margin_conditional_contest_model p h_admissible x
          h_trajectory s (le_trans (le_of_lt ht₀Pos) hs.1)
          (le_of_lt hs.2) (le_of_eq hBoundary.symm)
      nlinarith [show 0 < action2ThresholdDownwardMargin.molPerLPerS by
        norm_num [action2ThresholdDownwardMargin]]
    · exact ht
  have hFinalLe := hNeverAbove (action2KineticWindow p).second
    ⟨le_of_lt ht₀Window, le_rfl⟩
  apply lt_of_le_of_ne hFinalLe
  intro hEqReverse
  have hFinalEq :
      (x.dissolvedBromide (action2KineticWindow p).second).molPerL =
        criticalBromide.molPerL := hEqReverse
  have hMarginFinal :=
    action2_net_removal_margin_conditional_contest_model p h_admissible x
      h_trajectory (action2KineticWindow p).second (le_of_lt (by
        rw [hWindow]
        norm_num)) le_rfl (le_of_eq hFinalEq.symm)
  have hDerivFinal :
      (step7Rate
          (action2CeIVRemaining p (action2KineticWindow p).second)
          p.bmaConcentration).molPerLPerS -
        (action2PrecipitationFluxAt p x
          (action2KineticWindow p).second).molPerLPerS < 0 := by
    nlinarith [show 0 < action2ThresholdDownwardMargin.molPerLPerS by
      norm_num [action2ThresholdDownwardMargin]]
  let g : ℝ → ℝ := fun s =>
    (x.dissolvedBromide s).molPerL - criticalBromide.molPerL
  have hgDeriv := (hBromideDeriv (action2KineticWindow p).second
    (le_of_lt (by rw [hWindow]; norm_num)) le_rfl).sub_const
      criticalBromide.molPerL
  have hDerivNeg : deriv g (action2KineticWindow p).second < 0 := by
    rw [hgDeriv.deriv]
    exact hDerivFinal
  have hgZero : g (action2KineticWindow p).second = 0 := by
    simp [g, hFinalEq]
  have hSign := eventually_nhdsWithin_sign_eq_of_deriv_neg hDerivNeg hgZero
  have hSignLeft : ∀ᶠ s : ℝ in
      nhdsWithin (action2KineticWindow p).second
        (Set.Iio (action2KineticWindow p).second),
      SignType.sign (g s) =
        SignType.sign ((action2KineticWindow p).second - s) :=
    hSign.filter_mono inf_le_left
  have hInside : ∀ᶠ s : ℝ in
      nhdsWithin (action2KineticWindow p).second
        (Set.Iio (action2KineticWindow p).second),
      s ∈ Set.Ioo t₀ (action2KineticWindow p).second :=
    Ioo_mem_nhdsLT ht₀Window
  obtain ⟨s, hsSign, hsInside⟩ := (hSignLeft.and hInside).exists
  have hPos : 0 < g s := by
    rw [← sign_eq_one_iff, hsSign, sign_eq_one_iff]
    exact sub_pos.mpr hsInside.2
  have hsLe := hNeverAbove s ⟨le_of_lt hsInside.1, le_of_lt hsInside.2⟩
  dsimp [g] at hPos
  linarith

/-- Residual dissolved ions remain strictly positive and on the
supersaturated-or-saturated side of the sourced nonzero Ksp condition. -/
theorem action2_residual_ions_conditional_contest_model
    (p : Action2PulseInputs) (h_admissible : Action2Admissible p)
    (x : Action2KineticTrajectory) (h_trajectory : IsAction2KineticTrajectory p x) :
    0 < (x.dissolvedSilver (action2KineticWindow p).second).molPerL ∧
    0 < (x.dissolvedBromide (action2KineticWindow p).second).molPerL ∧
    agBrKsp25C.molarSquared ≤
      (x.dissolvedSilver (action2KineticWindow p).second).molPerL *
        (x.dissolvedBromide (action2KineticWindow p).second).molPerL := by
  have hWindowPos : 0 < (action2KineticWindow p).second := by
    rw [action2_kinetic_window_eq_conditional_contest_model p h_admissible]
    norm_num
  have hSourcePos (t : ℝ) :
      0 < (step7Rate (action2CeIVRemaining p t)
        p.bmaConcentration).molPerLPerS := by
    rcases h_admissible with ⟨_, _, _, _, _, _, _, hCePos, _, hBma, _⟩
    simp only [step7Rate, action2CeIVRemaining, step7PseudoFirstOrderRate, k7]
    rw [hBma]
    positivity
  have hSilverPositive :
      0 < (x.dissolvedSilver (action2KineticWindow p).second).molPerL := by
    have hFloor :=
      action2_silver_floor_conditional_contest_model p h_admissible x h_trajectory
    exact lt_of_lt_of_le
      (lt_trans (by norm_num : (0 : ℝ) < 23 / 10000000) hFloor.1)
      (hFloor.2 _ (le_of_lt hWindowPos) le_rfl)
  have hSilverDeriv (t : ℝ) (ht : t ∈
      Set.Icc 0 (action2KineticWindow p).second) :=
    (h_trajectory.2.2.2 t ht.1 ht.2).2.2.2.1
  have hBromideDeriv (t : ℝ) (ht : t ∈
      Set.Icc 0 (action2KineticWindow p).second) :=
    (h_trajectory.2.2.2 t ht.1 ht.2).2.2.2.2.1
  have hSilverContinuous : ContinuousOn
      (fun t : ℝ => (x.dissolvedSilver t).molPerL)
      (Set.Icc 0 (action2KineticWindow p).second) := by
    intro t ht
    exact (hSilverDeriv t ht).continuousAt.continuousWithinAt
  have hBromideContinuous : ContinuousOn
      (fun t : ℝ => (x.dissolvedBromide t).molPerL)
      (Set.Icc 0 (action2KineticWindow p).second) := by
    intro t ht
    exact (hBromideDeriv t ht).continuousAt.continuousWithinAt
  have hProductContinuous : ContinuousOn
      (fun t : ℝ => (x.dissolvedSilver t).molPerL *
        (x.dissolvedBromide t).molPerL)
      (Set.Icc 0 (action2KineticWindow p).second) :=
    hSilverContinuous.mul hBromideContinuous
  have hProductDeriv (t : ℝ) (ht : t ∈
      Set.Icc 0 (action2KineticWindow p).second) :
      HasDerivAt
        (fun s : ℝ => (x.dissolvedSilver s).molPerL *
          (x.dissolvedBromide s).molPerL)
        (-(action2PrecipitationFluxAt p x t).molPerLPerS *
            (x.dissolvedBromide t).molPerL +
          (x.dissolvedSilver t).molPerL *
            ((step7Rate (action2CeIVRemaining p t)
                p.bmaConcentration).molPerLPerS -
              (action2PrecipitationFluxAt p x t).molPerLPerS)) t := by
    exact (hSilverDeriv t ht).mul (hBromideDeriv t ht)
  have hProductKsp :
      agBrKsp25C.molarSquared ≤
        (x.dissolvedSilver (action2KineticWindow p).second).molPerL *
          (x.dissolvedBromide (action2KineticWindow p).second).molPerL := by
    have hSuper :=
      (action2_initial_branch_and_supersaturation_conditional_contest_model
        p h_admissible).2
    apply image_le_of_deriv_right_lt_deriv_boundary'
      (a := 0) (b := (action2KineticWindow p).second)
      (f := fun _ : ℝ => agBrKsp25C.molarSquared)
      (f' := fun _ : ℝ => 0)
      (B := fun t : ℝ => (x.dissolvedSilver t).molPerL *
        (x.dissolvedBromide t).molPerL)
      (B' := fun t : ℝ =>
        -(action2PrecipitationFluxAt p x t).molPerLPerS *
            (x.dissolvedBromide t).molPerL +
          (x.dissolvedSilver t).molPerL *
            ((step7Rate (action2CeIVRemaining p t)
                p.bmaConcentration).molPerLPerS -
              (action2PrecipitationFluxAt p x t).molPerLPerS))
      continuousOn_const
      (fun t ht => (hasDerivAt_const t _).hasDerivWithinAt)
    · simpa [h_trajectory.1, h_trajectory.2.1] using le_of_lt hSuper
    · exact hProductContinuous
    · intro t ht
      exact (hProductDeriv t ⟨ht.1, le_of_lt ht.2⟩).hasDerivWithinAt
    · intro t ht hBoundary
      have hFluxZero :
          (action2PrecipitationFluxAt p x t).molPerLPerS = 0 := by
        simp only [action2PrecipitationFluxAt, agBrNetPrecipitationFlux]
        rw [← hBoundary, sub_self, mul_zero]
      have hStates := h_trajectory.2.2.2 t ht.1 (le_of_lt ht.2)
      have hProductPos :
          0 < (x.dissolvedSilver t).molPerL *
            (x.dissolvedBromide t).molPerL := by
        rw [← hBoundary]
        norm_num [agBrKsp25C]
      have hSilverPosAt : 0 < (x.dissolvedSilver t).molPerL := by
        rcases (mul_pos_iff.mp hProductPos) with hPos | hNeg
        · exact hPos.1
        · exact False.elim ((not_lt_of_ge hStates.1) hNeg.1)
      rw [hFluxZero]
      simpa only [neg_zero, zero_mul, zero_add, sub_zero] using
        mul_pos hSilverPosAt (hSourcePos t)
    · exact ⟨le_of_lt hWindowPos, le_rfl⟩
  have hBromideNonneg :=
    (h_trajectory.2.2.2 (action2KineticWindow p).second
      (le_of_lt hWindowPos) le_rfl).2.1
  have hProductPos : 0 <
      (x.dissolvedSilver (action2KineticWindow p).second).molPerL *
        (x.dissolvedBromide (action2KineticWindow p).second).molPerL :=
    lt_of_lt_of_le (by norm_num [agBrKsp25C]) hProductKsp
  have hBromidePositive :
      0 < (x.dissolvedBromide (action2KineticWindow p).second).molPerL := by
    rcases (mul_pos_iff.mp hProductPos) with hPos | hNeg
    · exact hPos.2
    · exact False.elim ((not_lt_of_ge hBromideNonneg) hNeg.2)
  exact ⟨hSilverPositive, hBromidePositive, hProductKsp⟩

/-- The removed amount is derived from the finite-time trajectory.  Both
component balances retain the continuously generated Process-C extent, and
strict residuals rule out a zero-solubility or complete-removal shortcut. -/
theorem action2_mass_balance_conditional_contest_model
    (p : Action2PulseInputs) (h_admissible : Action2Admissible p)
    (x : Action2KineticTrajectory) (h_trajectory : IsAction2KineticTrajectory p x) :
    IsAgBrMoleLedger (action2PrecipitatedAgBr p x) (action2AgBrLedger p x) ∧
    0 < (action2PrecipitatedAgBr p x).mol ∧
    p.effectiveSilverDose.mol =
      (x.dissolvedSilver (action2KineticWindow p).second).molPerL *
          p.mixedVolume.liter + (action2PrecipitatedAgBr p x).mol ∧
    p.initialBromide.molPerL * p.mixedVolume.liter +
        (action2ProcessCExtentAmount p (action2KineticWindow p).second).mol =
      (x.dissolvedBromide (action2KineticWindow p).second).molPerL *
          p.mixedVolume.liter + (action2PrecipitatedAgBr p x).mol ∧
    (action2PrecipitatedAgBr p x).mol < p.effectiveSilverDose.mol ∧
    (action2PrecipitatedAgBr p x).mol <
      p.initialBromide.molPerL * p.mixedVolume.liter +
        (action2ProcessCExtentAmount p (action2KineticWindow p).second).mol := by
  rcases h_admissible with
    ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
      hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
      hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩
  have hMixed : p.mixedVolume.liter = 1001 / 1000 := by
    rw [hMixV, hV, hDoseV]
    norm_num
  have hVolumePos : 0 < p.mixedVolume.liter := by
    rw [hMixed]
    norm_num
  have hWindowPos : 0 < (action2KineticWindow p).second := by
    rw [action2_kinetic_window_eq_conditional_contest_model p
      ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
        hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
        hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩]
    norm_num
  have hBalances := action2_component_balances_conditional_contest_model p
    ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
      hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
      hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩ x h_trajectory
      (action2KineticWindow p).second (le_of_lt hWindowPos) le_rfl
  have hResidual := action2_residual_ions_conditional_contest_model p
    ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
      hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
      hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩ x h_trajectory
  have hCross := action2_crosses_threshold_conditional_contest_model p
    ⟨hV, hDoseV, hMixV, hMixT, hObsT, hBrLo, hBrHi, hCePos, hCeHi,
      hBma, hBmaScale, hBmaAvail, hCeAvail, hAgLo, hAgHi, hRate,
      hTemp, hPulseScale, hStockBrScale, hStockMaScale⟩ x h_trajectory
  have hExtentNonneg :
      0 ≤ (action2ProcessCExtentConcentration p
        (action2KineticWindow p).second).molPerL := by
    have hExpLe : Real.exp
        (-(step7PseudoFirstOrderRate p.bmaConcentration).perS *
          (action2KineticWindow p).second) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      simp only [step7PseudoFirstOrderRate, k7]
      rw [hBma]
      norm_num
      exact le_of_lt hWindowPos
    simp only [action2ProcessCExtentConcentration, action2CeIVRemaining]
    have hCeNonneg : 0 ≤ p.initialCeriumIV.molPerL := le_of_lt hCePos
    have hProductLe := mul_le_mul_of_nonneg_left hExpLe hCeNonneg
    nlinarith
  have hSolidPositive :
      0 < (x.solidAgBrEquivalent
        (action2KineticWindow p).second).molPerL := by
    rw [criticalBromide_eq] at hCross
    nlinarith [hBalances.2]
  have hPrecipPositive : 0 < (action2PrecipitatedAgBr p x).mol := by
    simp only [action2PrecipitatedAgBr]
    exact mul_pos hSolidPositive hVolumePos
  have hDoseMixed :
      p.effectiveSilverDose.mol =
        (action2SilverDoseConcentration p).molPerL * p.mixedVolume.liter := by
    simp only [action2SilverDoseConcentration]
    field_simp [ne_of_gt hVolumePos]
  have hSilverAmount :
      p.effectiveSilverDose.mol =
        (x.dissolvedSilver (action2KineticWindow p).second).molPerL *
            p.mixedVolume.liter + (action2PrecipitatedAgBr p x).mol := by
    rw [hDoseMixed]
    simp only [action2PrecipitatedAgBr]
    nlinarith [hBalances.1]
  have hBromideAmount :
      p.initialBromide.molPerL * p.mixedVolume.liter +
          (action2ProcessCExtentAmount p
            (action2KineticWindow p).second).mol =
        (x.dissolvedBromide (action2KineticWindow p).second).molPerL *
            p.mixedVolume.liter + (action2PrecipitatedAgBr p x).mol := by
    simp only [action2ProcessCExtentAmount, action2PrecipitatedAgBr]
    nlinarith [hBalances.2]
  have hPrecipLtSilver :
      (action2PrecipitatedAgBr p x).mol < p.effectiveSilverDose.mol := by
    nlinarith [hSilverAmount, mul_pos hResidual.1 hVolumePos]
  have hPrecipLtBromide :
      (action2PrecipitatedAgBr p x).mol <
        p.initialBromide.molPerL * p.mixedVolume.liter +
          (action2ProcessCExtentAmount p
            (action2KineticWindow p).second).mol := by
    nlinarith [hBromideAmount, mul_pos hResidual.2.1 hVolumePos]
  refine ⟨?_, hPrecipPositive, hSilverAmount, hBromideAmount,
    hPrecipLtSilver, hPrecipLtBromide⟩
  exact ⟨rfl, rfl, rfl⟩

def action2FeasibleInputs : Action2PulseInputs :=
  { initialVolume := ⟨1⟩
    doseSolutionVolume := ⟨1 / 1000⟩
    mixedVolume := ⟨1001 / 1000⟩
    initialBromide := ⟨6 / 10000000⟩
    initialCeriumIV := ⟨1 / 100000000⟩
    bmaConcentration := ⟨1 / 100⟩
    bmaAvailable := ⟨1001 / 100000⟩
    effectiveSilverDose := ⟨3 / 1000000⟩
    mixingTime := ⟨1 / 100⟩
    observationTime := ⟨11 / 100⟩
    precipitationRateConstant := ⟨100000000⟩
    temperature := ⟨25⟩ }

/-- A separately checked positive, finite, mass-balanced M203 witness.  Its
1 mL dose contains `3e-6 mol` effective Ag⁺ (`0.003 M` stock); after mixing
the pulse is below one three-hundredth of the printed `0.001 M` Ce(IV) scale.
The theorem includes a physical kinetic trajectory and its two terminal
component balances, so nonvacuity is not merely syntactic admissibility. -/
theorem action2_feasible_tuple_conditional_contest_model :
    Action2Admissible action2FeasibleInputs ∧
    ∃ x : Action2KineticTrajectory,
      IsAction2KineticTrajectory action2FeasibleInputs x ∧
      0 < (x.dissolvedSilver
        (action2KineticWindow action2FeasibleInputs).second).molPerL ∧
      0 < (x.dissolvedBromide
        (action2KineticWindow action2FeasibleInputs).second).molPerL ∧
      IsAgBrMoleLedger (action2PrecipitatedAgBr action2FeasibleInputs x)
        (action2AgBrLedger action2FeasibleInputs x) ∧
      action2FeasibleInputs.effectiveSilverDose.mol =
        (x.dissolvedSilver
            (action2KineticWindow action2FeasibleInputs).second).molPerL *
            action2FeasibleInputs.mixedVolume.liter +
          (action2PrecipitatedAgBr action2FeasibleInputs x).mol ∧
      action2FeasibleInputs.initialBromide.molPerL *
            action2FeasibleInputs.mixedVolume.liter +
          (action2ProcessCExtentAmount action2FeasibleInputs
            (action2KineticWindow action2FeasibleInputs).second).mol =
        (x.dissolvedBromide
            (action2KineticWindow action2FeasibleInputs).second).molPerL *
            action2FeasibleInputs.mixedVolume.liter +
          (action2PrecipitatedAgBr action2FeasibleInputs x).mol := by
  have hAdmissible : Action2Admissible action2FeasibleInputs := by
    norm_num [Action2Admissible, action2FeasibleInputs,
      action2SilverDoseConcentration, action2SilverStockConcentration,
      ceriumIVSourceScale, bromateConcentration, malonicAcidConcentration]
  refine ⟨hAdmissible, ?_⟩
  obtain ⟨x, hx⟩ :=
    action2_trajectory_exists_conditional_contest_model
      action2FeasibleInputs hAdmissible
  have hResidual :=
    action2_residual_ions_conditional_contest_model
      action2FeasibleInputs hAdmissible x hx
  have hMass :=
    action2_mass_balance_conditional_contest_model
      action2FeasibleInputs hAdmissible x hx
  exact ⟨x, hx, hResidual.1, hResidual.2.1, hMass.1,
    hMass.2.2.1, hMass.2.2.2.1⟩

/-! ## Action 3: source-derived Process-B timing, with no extra authorization -/

structure Action3PulseInputs where
  initialBromide : MolarConcentration
  addedBromide : MolarConcentration

/-- Here "small" means a positive pulse that stays inside the printed phase
portrait range ending at `[Br⁻]max`; no numerical dose law is added. -/
def Action3Admissible (p : Action3PulseInputs) : Prop :=
  criticalBromide.molPerL < p.initialBromide.molPerL ∧
  0 < p.addedBromide.molPerL ∧
  p.initialBromide.molPerL + p.addedBromide.molPerL ≤ bromideMaximum.molPerL

/-- Time in seconds for the printed stationary Process-B exponential loss model
to reach the critical concentration. -/
noncomputable def processBTimeToCritical (bromide : MolarConcentration) : DurationS :=
  ⟨Real.log (bromide.molPerL / criticalBromide.molPerL) /
    processBDecayConstant.perS⟩

noncomputable def classifyProcessBDuration
    (unperturbed perturbed : DurationS) : Effect :=
  if unperturbed.second < perturbed.second then
    .prolongsProcessB
  else
    .switchesBToA

theorem action3_time_increases_conditional_contest_model
    (p : Action3PulseInputs) (h_admissible : Action3Admissible p) :
    (processBTimeToCritical p.initialBromide).second <
      (processBTimeToCritical
        ⟨p.initialBromide.molPerL + p.addedBromide.molPerL⟩).second := by
  rcases h_admissible with ⟨hInitial, hAdded, hMaximum⟩
  have hCritical : 0 < criticalBromide.molPerL := by
    rw [criticalBromide_eq]
    norm_num
  have hInitialPos : 0 < p.initialBromide.molPerL := hCritical.trans hInitial
  have hPerturbedPos :
      0 < p.initialBromide.molPerL + p.addedBromide.molPerL := by linarith
  have hRatioInitial :
      0 < p.initialBromide.molPerL / criticalBromide.molPerL :=
    div_pos hInitialPos hCritical
  have hRatioPerturbed :
      0 < (p.initialBromide.molPerL + p.addedBromide.molPerL) /
        criticalBromide.molPerL := div_pos hPerturbedPos hCritical
  have hRatioLt :
      p.initialBromide.molPerL / criticalBromide.molPerL <
        (p.initialBromide.molPerL + p.addedBromide.molPerL) /
          criticalBromide.molPerL :=
    (div_lt_div_iff_of_pos_right hCritical).2 (by linarith)
  have hLogLt := Real.strictMonoOn_log hRatioInitial hRatioPerturbed hRatioLt
  simp only [processBTimeToCritical]
  exact (div_lt_div_iff_of_pos_right processBDecayConstant_positive).2 hLogLt

/-! ## Action 4: authorized constant-feed model (M201) -/

structure Action4FeedInputs where
  initialBromide : MolarConcentration
  feedFlux : MolarFlux

/-- M201's sole extra dynamical inequality.  Both sides have units M s⁻¹;
the decay coefficient and threshold are source-derived. -/
def Action4Admissible (p : Action4FeedInputs) : Prop :=
  0 ≤ p.initialBromide.molPerL ∧
  processBDecayConstant.perS * criticalBromide.molPerL < p.feedFlux.molPerLPerS

def action4FeedEquilibrium (p : Action4FeedInputs) : MolarConcentration :=
  ⟨p.feedFlux.molPerLPerS / processBDecayConstant.perS⟩

/-- Exact solution of `db/dt = u - k b` for constant feed `u`. -/
noncomputable def action4BromideAt (p : Action4FeedInputs) (t : ℝ) : MolarConcentration :=
  ⟨(action4FeedEquilibrium p).molPerL +
    (p.initialBromide.molPerL - (action4FeedEquilibrium p).molPerL) *
      Real.exp (-processBDecayConstant.perS * t)⟩

def EventuallyPermanentlyAboveCritical (p : Action4FeedInputs) : Prop :=
  ∃ T : ℝ, 0 ≤ T ∧
    ∀ t : ℝ, T < t → criticalBromide.molPerL < (action4BromideAt p t).molPerL

/-- The printed oscillator alternates A/B only by recrossing the critical
threshold, so eventual permanent Process B is the semantic criterion for option
(e).  The predicate itself is derived below from the feed trajectory. -/
noncomputable def classifyContinuousFeed (p : Action4FeedInputs) : Effect := by
  classical
  exact if EventuallyPermanentlyAboveCritical p then
    .oscillationsStop
  else
    .prolongsProcessB

theorem action4_ode_carrier_conditional_contest_model
    (p : Action4FeedInputs) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (action4BromideAt p s).molPerL)
      (p.feedFlux.molPerLPerS -
        processBDecayConstant.perS * (action4BromideAt p t).molPerL) t := by
  have hk : processBDecayConstant.perS ≠ 0 :=
    ne_of_gt processBDecayConstant_positive
  unfold action4BromideAt
  dsimp
  have hinner : HasDerivAt
      (fun s : ℝ => -(processBDecayConstant.perS * s))
      (-processBDecayConstant.perS) t := by
    simpa only [id_eq, neg_mul, mul_one] using
      (hasDerivAt_id t).const_mul (-processBDecayConstant.perS)
  have h := (hinner.exp.mul_const
    (p.initialBromide.molPerL - (action4FeedEquilibrium p).molPerL)).const_add
      (action4FeedEquilibrium p).molPerL
  convert h using 1
  all_goals first | rfl |
    (simp only [action4FeedEquilibrium]; field_simp [hk] <;> try ring)

/-- M201 implies eventual permanent residence above the derived switching
threshold for every nonnegative initial concentration. -/
theorem action4_permanent_processB_conditional_contest_model
    (p : Action4FeedInputs) (h_admissible : Action4Admissible p) :
    EventuallyPermanentlyAboveCritical p := by
  rcases h_admissible with ⟨hInitial, hFeed⟩
  have hk := processBDecayConstant_positive
  have hEquilibrium :
      criticalBromide.molPerL < (action4FeedEquilibrium p).molPerL := by
    simp only [action4FeedEquilibrium]
    exact (lt_div_iff₀ hk).2 (by simpa [mul_comm] using hFeed)
  have hLinear : Filter.Tendsto
      (fun t : ℝ => -processBDecayConstant.perS * t) Filter.atTop Filter.atBot :=
    Filter.tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hk)
  have hExp : Filter.Tendsto
      (fun t : ℝ => Real.exp (-processBDecayConstant.perS * t)) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hLinear
  have hTrajectory : Filter.Tendsto
      (fun t : ℝ => (action4BromideAt p t).molPerL) Filter.atTop
        (nhds (action4FeedEquilibrium p).molPerL) := by
    simpa [action4BromideAt] using
      tendsto_const_nhds.add
        (tendsto_const_nhds.mul hExp)
  have hEventually : ∀ᶠ t : ℝ in Filter.atTop,
      criticalBromide.molPerL < (action4BromideAt p t).molPerL :=
    hTrajectory.eventually (Ioi_mem_nhds hEquilibrium)
  rcases Filter.eventually_atTop.1 hEventually with ⟨T, hT⟩
  refine ⟨max 0 T, le_max_left _ _, ?_⟩
  intro t ht
  exact hT t (le_trans (le_max_right _ _) (le_of_lt ht))

def action4FeasibleInputs : Action4FeedInputs :=
  { initialBromide := ⟨1 / 10000000⟩
    feedFlux := ⟨1 / 10000000⟩ }

/-- A finite four-second threshold-residence witness for the named feasible
input.  This duration is supplemental witness data, not an M201 premise used
by the all-tuples theorem. -/
def action4FeasibleResidenceTime : DurationS := ⟨4⟩

/-- M201's separately checked witness has positive initial bromide, positive
feed, and a concrete finite time after which it remains above threshold. -/
theorem action4_feasible_tuple_conditional_contest_model :
    Action4Admissible action4FeasibleInputs ∧
    0 < action4FeasibleInputs.initialBromide.molPerL ∧
    0 < action4FeasibleInputs.feedFlux.molPerLPerS ∧
    0 ≤ action4FeasibleResidenceTime.second ∧
    ∀ t : ℝ, action4FeasibleResidenceTime.second < t →
      criticalBromide.molPerL < (action4BromideAt action4FeasibleInputs t).molPerL := by
  have hk : processBDecayConstant.perS = 504 / 3125 := by
    norm_num [processBDecayConstant, k5, bromateConcentration,
      protonConcentration]
  have hCritical : criticalBromide.molPerL = 3 / 10000000 :=
    criticalBromide_eq
  constructor
  · norm_num [Action4Admissible, action4FeasibleInputs, hk, hCritical]
  refine ⟨by norm_num [action4FeasibleInputs], by norm_num [action4FeasibleInputs],
    by norm_num [action4FeasibleResidenceTime], ?_⟩
  intro t ht
  have ht' : 4 < t := by simpa [action4FeasibleResidenceTime] using ht
  have hkt : 0 < processBDecayConstant.perS * t := by
    rw [hk]
    nlinarith
  have hdenpos : 0 < 1 + processBDecayConstant.perS * t := by nlinarith
  have hExpDenom :
      Real.exp (-(processBDecayConstant.perS * t)) ≤
        1 / (1 + processBDecayConstant.perS * t) := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hdenpos (by
      simpa [add_comm] using Real.add_one_le_exp (processBDecayConstant.perS * t))
  have hDenomBound :
      1 / (1 + processBDecayConstant.perS * t) < 61 / 100 := by
    rw [hk] at hkt hExpDenom ⊢
    apply (div_lt_iff₀ (by nlinarith : (0 : ℝ) < 1 + 504 / 3125 * t)).2
    nlinarith
  have hExpBound := lt_of_le_of_lt hExpDenom hDenomBound
  rw [hk] at hExpBound
  rw [hCritical]
  simp only [action4BromideAt, action4FeedEquilibrium, action4FeasibleInputs]
  rw [hk]
  norm_num at hExpBound ⊢
  have hAux :
      3 / 10000000 + 2621 / 5040000000 *
          Real.exp (-(504 / 3125 * t)) < 1 / 1612800 := by
    have hProduct := mul_lt_mul_of_pos_left hExpBound
      (by norm_num : (0 : ℝ) < 2621 / 5040000000)
    nlinarith
  nlinarith

/-! ## One result carrier for each requested output -/

def Action1RequestedOutput : Prop :=
  ∀ p : Action1PulseInputs, Action1Admissible p →
    classifyPulseAtThreshold .processA (action1BromideAtObservation p) =
      .switchesAToB

def Action2RequestedOutput : Prop :=
  ∀ p : Action2PulseInputs, Action2Admissible p →
    (∃ x : Action2KineticTrajectory, IsAction2KineticTrajectory p x) ∧
    ∀ x : Action2KineticTrajectory, IsAction2KineticTrajectory p x →
      classifyPulseAtThreshold .processB
        (x.dissolvedBromide (action2KineticWindow p).second) = .switchesBToA

def Action3RequestedOutput : Prop :=
  ∀ p : Action3PulseInputs, Action3Admissible p →
    classifyProcessBDuration
      (processBTimeToCritical p.initialBromide)
      (processBTimeToCritical
        ⟨p.initialBromide.molPerL + p.addedBromide.molPerL⟩) =
      .prolongsProcessB

def Action4RequestedOutput : Prop :=
  ∀ p : Action4FeedInputs, Action4Admissible p →
    classifyContinuousFeed p = .oscillationsStop

theorem action1_effect_conditional_contest_model : Action1RequestedOutput := by
  intro p h_admissible
  simp only [classifyPulseAtThreshold]
  rw [if_pos
    (action1_crosses_threshold_conditional_contest_model p h_admissible)]

theorem action2_effect_conditional_contest_model : Action2RequestedOutput := by
  intro p h_admissible
  constructor
  · exact action2_trajectory_exists_conditional_contest_model p h_admissible
  · intro x h_trajectory
    simp only [classifyPulseAtThreshold]
    rw [if_pos
      (action2_crosses_threshold_conditional_contest_model
        p h_admissible x h_trajectory)]

theorem action3_effect_conditional_contest_model : Action3RequestedOutput := by
  intro p h_admissible
  simp only [classifyProcessBDuration]
  rw [if_pos (action3_time_increases_conditional_contest_model p h_admissible)]

theorem action4_effect_conditional_contest_model : Action4RequestedOutput := by
  intro p h_admissible
  simp only [classifyContinuousFeed]
  rw [if_pos
    (action4_permanent_processB_conditional_contest_model p h_admissible)]

/-- Mixed symbolic raw result: all four classifications in source order. -/
def RawRequestedOutputs : Prop :=
  Action1RequestedOutput ∧
  Action2RequestedOutput ∧
  Action3RequestedOutput ∧
  Action4RequestedOutput

/-- Exact-symbolic reporting performs no rounding or lossy transformation. -/
def ReportedRequestedOutputs : Prop := RawRequestedOutputs

theorem raw_requested_outputs_conditional_contest_model :
    ("678b8a210afaec1f9249bca34d7508033f306b875d812b1b8a5c5b36ee224c88" : String) =
        "678b8a210afaec1f9249bca34d7508033f306b875d812b1b8a5c5b36ee224c88" ∧
      RawRequestedOutputs := by
  refine ⟨rfl, ?_⟩
  exact ⟨action1_effect_conditional_contest_model,
    action2_effect_conditional_contest_model,
    action3_effect_conditional_contest_model,
    action4_effect_conditional_contest_model⟩

theorem reported_requested_outputs_conditional_contest_model :
    ("28d88df227707aa5ad0091c5ab1ca4fcda9c37c27afdb730d1887c01a56c2985" : String) =
        "28d88df227707aa5ad0091c5ab1ca4fcda9c37c27afdb730d1887c01a56c2985" ∧
      ReportedRequestedOutputs := by
  refine ⟨rfl, ?_⟩
  exact raw_requested_outputs_conditional_contest_model.2

end ConditionalContestModel
end
end ProblemIcho2026T2A6
end IChO2026Problems
