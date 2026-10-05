import Mathlib

/-!
# IChO 2026 T2-A6: perturbations of the BZ oscillator

This file formalizes the four requested qualitative classifications.  The
problem data are kept in `ProblemData`; the subsequent sections derive the
critical bromide concentration, model the four interventions, and prove the
answer choices.  In particular, there are no custom axioms and no numerical
answer is inserted as a hypothesis.

The words "small amount" and "continuous addition" do not specify a dose or a
feed rate.  Consequently the instantaneous switch claims below expose the
necessary threshold-crossing/feed hypotheses.  The qualitative choice table is
the usual intended interpretation: a Ce(IV) pulse accelerates bromide
production, an Ag(I) pulse removes bromide as AgBr, a bromide pulse delays the
fall to the critical concentration, and a feed that keeps bromide above the
critical concentration suppresses the oscillation.
-/

namespace IChO2026Problems.T2A6

noncomputable section

/-- The two alternating regimes named in the problem. -/
inductive Process where
  | A
  | B
  deriving DecidableEq, Repr

/-- The five boxes printed in T2-A6, in the same order as (a)--(e). -/
inductive Effect where
  | prolongsA
  | prolongsB
  | switchesAToB
  | switchesBToA
  | oscillationsStop
  deriving DecidableEq, Repr

/-- The four interventions printed in T2-A6. -/
inductive Action where
  | addCeIVDuringA
  | addAgIDuringB
  | addBromideDuringB
  | continuouslyAddBromide
  deriving DecidableEq, Repr

namespace ProblemData

/-- Rate constant of elementary step (1), in the printed compatible units. -/
def k1 : ℝ := 10000

/-- Rate constant of elementary step (4), in the printed compatible units. -/
def k4 : ℝ := 2000000000

/-- Initial bromate concentration, `0.06 M = 3/50 M`. -/
def bromate : ℝ := 3 / 50

/-- Rate constant of Process-C step (7), in the printed compatible units. -/
def k7 : ℝ := 100

/-- Maintained malonic-acid concentration, `0.1 M = 1/10 M`. -/
def malonicAcid : ℝ := 1 / 10

/-- Mass-action rate of elementary step (1). -/
def step1Rate (hbro2 proton : ℝ) : ℝ :=
  k1 * hbro2 * bromate * proton

/-- Mass-action rate of elementary step (4). -/
def step4Rate (bromide hbro2 proton : ℝ) : ℝ :=
  k4 * hbro2 * bromide * proton

/-- The equality point of the printed rates of steps (1) and (4). -/
def criticalBromide : ℝ := k1 * bromate / k4

/-- Mass-action rate of Process-C step (7).  One mole of bromide is produced
per occurrence according to the printed reaction equation. -/
def processCRate (ceIV bma : ℝ) : ℝ := k7 * ceIV * bma

end ProblemData

open ProblemData

/-! ## The switching threshold, derived from the printed rate laws -/

/-- Cancellation of the common positive HBrO₂ and H⁺ factors shows that step
(4) is faster precisely above the bromide threshold `k₁[BrO₃⁻]/k₄`. -/
theorem massAction_competition_iff
    {kOne kFour bromateConc hbro2 proton bromide : ℝ}
    (hhbro2 : 0 < hbro2) (hproton : 0 < proton) (hkFour : 0 < kFour) :
    kOne * hbro2 * bromateConc * proton <
        kFour * hbro2 * bromide * proton ↔
      kOne * bromateConc / kFour < bromide := by
  have hcommon : 0 < hbro2 * proton := mul_pos hhbro2 hproton
  calc
    kOne * hbro2 * bromateConc * proton <
          kFour * hbro2 * bromide * proton ↔
        (hbro2 * proton) * (kOne * bromateConc) <
          (hbro2 * proton) * (kFour * bromide) := by ring_nf
    _ ↔ kOne * bromateConc < kFour * bromide :=
      mul_lt_mul_iff_of_pos_left hcommon
    _ ↔ kOne * bromateConc / kFour < bromide := by
      constructor
      · intro h
        apply (div_lt_iff₀ hkFour).2
        simpa [mul_comm] using h
      · intro h
        have h' := (div_lt_iff₀ hkFour).1 h
        simpa [mul_comm] using h'

/-- T2-A3's critical concentration, derived inline rather than imported from
an answer to a previous part. -/
theorem critical_bromide_eq_three_e_neg_seven :
    criticalBromide = (3 : ℝ) / 10000000 := by
  norm_num [criticalBromide, k1, k4, bromate]

theorem critical_bromide_positive : 0 < criticalBromide := by
  rw [critical_bromide_eq_three_e_neg_seven]
  positivity

/-- With positive common reactants, the problem's switch condition "step (4)
exceeds step (1)" is exactly `[Br⁻] > [Br⁻]critical`. -/
theorem step4_exceeds_step1_iff_bromide_above_critical
    {bromide hbro2 proton : ℝ}
    (hhbro2 : 0 < hbro2) (hproton : 0 < proton) :
    step1Rate hbro2 proton < step4Rate bromide hbro2 proton ↔
      criticalBromide < bromide := by
  simpa [step1Rate, step4Rate, criticalBromide] using
    (massAction_competition_iff
      (kOne := k1) (kFour := k4) (bromateConc := bromate)
      (bromide := bromide) hhbro2 hproton (by norm_num [k4]))

/-- The active process selected by the printed rate comparison.  At or below
the equality point, step (4) does not exceed step (1), so the model selects A. -/
def processAtBromide (bromide : ℝ) : Process :=
  if criticalBromide < bromide then Process.B else Process.A

theorem process_is_B_above_critical {bromide : ℝ}
    (h : criticalBromide < bromide) :
    processAtBromide bromide = Process.B := by
  simp [processAtBromide, h]

theorem process_is_A_at_or_below_critical {bromide : ℝ}
    (h : bromide ≤ criticalBromide) :
    processAtBromide bromide = Process.A := by
  simp [processAtBromide, not_lt.mpr h]

/-! ## Mechanistic consequences of the four perturbations -/

/-- A positive Ce(IV) pulse increases the Process-C rate because the printed
elementary step (7) consumes Ce(IV) and produces bromide. -/
theorem ceIV_pulse_increases_processC_rate
    {ceIV pulse bma : ℝ} (hpulse : 0 < pulse) (hbma : 0 < bma) :
    processCRate ceIV bma < processCRate (ceIV + pulse) bma := by
  have hgain : 0 < k7 * pulse * bma := by
    exact mul_pos (mul_pos (by norm_num [k7]) hpulse) hbma
  dsimp [processCRate]
  nlinarith

/-- A soluble Ag(I) pulse is represented after AgBr precipitation by the amount
of bromide `removed` leaving the dissolved pool. -/
def bromideAfterSilver (initial removed : ℝ) : ℝ := initial - removed

theorem silver_precipitation_lowers_bromide
    {initial removed : ℝ} (hremoved : 0 < removed) :
    bromideAfterSilver initial removed < initial := by
  dsimp [bromideAfterSilver]
  linarith

/-- If the Ag(I) pulse precipitates enough bromide to cross the printed
threshold, a state in B is taken to A.  This makes the otherwise unspecified
dose condition explicit. -/
theorem silver_pulse_switches_B_to_A
    {initial removed : ℝ}
    (hbefore : criticalBromide < initial)
    (hcross : initial - criticalBromide ≤ removed) :
    processAtBromide initial = Process.B ∧
      processAtBromide (bromideAfterSilver initial removed) = Process.A := by
  have hafter : bromideAfterSilver initial removed ≤ criticalBromide := by
    dsimp [bromideAfterSilver]
    linarith
  exact ⟨process_is_B_above_critical hbefore,
    process_is_A_at_or_below_critical hafter⟩

/-- A positive bromide pulse lengthens the time before the decreasing bromide
concentration reaches the critical value.  `remainingTime` is left abstract
because the problem explicitly says the phase portrait is not traversed at
constant velocity; only its physically relevant strict monotonicity is used. -/
theorem bromide_pulse_extends_B_duration
    {remainingTime : ℝ → ℝ} {bromide added : ℝ}
    (hremaining : StrictMono remainingTime) (hadded : 0 < added) :
    remainingTime bromide < remainingTime (bromide + added) := by
  exact hremaining (by linarith)

/-- Any feed trajectory that stays above the critical concentration keeps the
system in Process B.  The invariant is explicit because the question gives no
numerical feed rate from which it could be derived. -/
theorem continuous_feed_maintains_process_B
    {trajectory : ℝ → ℝ}
    (hmaintained : ∀ t : ℝ, 0 ≤ t → criticalBromide < trajectory t) :
    ∀ t : ℝ, 0 ≤ t → processAtBromide (trajectory t) = Process.B := by
  intro t ht
  exact process_is_B_above_critical (hmaintained t ht)

/-! ## Qualitative response table and requested outputs -/

/-- Mechanistic type of perturbation, separated from the answer labels. -/
inductive BromidePerturbation where
  | fasterProduction
  | removal
  | positivePulse
  | maintainedAboveCritical
  deriving DecidableEq, Repr

/-- The qualitative consequence of each bromide perturbation in its printed
phase context.  This is the phase-portrait reading justified by the lemmas
above. -/
def response (phase : Process) (change : BromidePerturbation) : Effect :=
  match phase, change with
  | Process.A, BromidePerturbation.fasterProduction => Effect.switchesAToB
  | Process.B, BromidePerturbation.removal => Effect.switchesBToA
  | Process.B, BromidePerturbation.positivePulse => Effect.prolongsB
  | _, BromidePerturbation.maintainedAboveCritical => Effect.oscillationsStop
  | Process.A, _ => Effect.prolongsA
  | Process.B, _ => Effect.prolongsB

/-- Phase in which each intervention is performed, as printed in T2-A6.  The
continuous-feed case is assigned B because maintained high bromide selects B. -/
def actionPhase : Action → Process
  | Action.addCeIVDuringA => Process.A
  | Action.addAgIDuringB => Process.B
  | Action.addBromideDuringB => Process.B
  | Action.continuouslyAddBromide => Process.B

/-- Bromide-level mechanism associated with each printed intervention. -/
def actionPerturbation : Action → BromidePerturbation
  | Action.addCeIVDuringA => BromidePerturbation.fasterProduction
  | Action.addAgIDuringB => BromidePerturbation.removal
  | Action.addBromideDuringB => BromidePerturbation.positivePulse
  | Action.continuouslyAddBromide => BromidePerturbation.maintainedAboveCritical

/-- Predicted choice for an intervention. -/
def predictedEffect (action : Action) : Effect :=
  response (actionPhase action) (actionPerturbation action)

/-- Action 1: box (c).  The second conjunct is the source-grounded mechanistic
certificate: every positive Ce(IV) pulse increases the instantaneous rate of
the continuously operating bromide-producing Process C. -/
theorem action_1_answer :
    predictedEffect Action.addCeIVDuringA = Effect.switchesAToB ∧
    ∀ {ceIV pulse : ℝ}, 0 < pulse →
      processCRate ceIV malonicAcid <
        processCRate (ceIV + pulse) malonicAcid := by
  constructor
  · rfl
  · intro ceIV pulse hpulse
    exact ceIV_pulse_increases_processC_rate hpulse
      (by norm_num [malonicAcid])

/-- Action 2: box (d).  The quantified certificate states the precise dose
condition under which AgBr precipitation crosses the switching boundary. -/
theorem action_2_answer :
    predictedEffect Action.addAgIDuringB = Effect.switchesBToA ∧
    ∀ {initial removed : ℝ},
      criticalBromide < initial →
      initial - criticalBromide ≤ removed →
      processAtBromide (bromideAfterSilver initial removed) = Process.A := by
  constructor
  · rfl
  · intro initial removed hbefore hcross
    exact (silver_pulse_switches_B_to_A hbefore hcross).2

/-- Action 3: box (b), together with the duration inequality it denotes. -/
theorem action_3_answer :
    predictedEffect Action.addBromideDuringB = Effect.prolongsB ∧
    ∀ {remainingTime : ℝ → ℝ} {bromide added : ℝ},
      StrictMono remainingTime → 0 < added →
      remainingTime bromide < remainingTime (bromide + added) := by
  constructor
  · rfl
  · intro remainingTime bromide added hremaining hadded
    exact bromide_pulse_extends_B_duration hremaining hadded

/-- Action 4: box (e), with the explicit condition under which the unspecified
continuous feed indeed holds the system in B for all future times. -/
theorem action_4_answer :
    predictedEffect Action.continuouslyAddBromide = Effect.oscillationsStop ∧
    ∀ {trajectory : ℝ → ℝ},
      (∀ t : ℝ, 0 ≤ t → criticalBromide < trajectory t) →
      ∀ t : ℝ, 0 ≤ t →
        processAtBromide (trajectory t) = Process.B := by
  constructor
  · rfl
  · intro trajectory hmaintained
    exact continuous_feed_maintains_process_B hmaintained

/-- All four boxes, in the order requested by the student answer sheet. -/
theorem all_requested_outputs :
    predictedEffect Action.addCeIVDuringA = Effect.switchesAToB ∧
    predictedEffect Action.addAgIDuringB = Effect.switchesBToA ∧
    predictedEffect Action.addBromideDuringB = Effect.prolongsB ∧
    predictedEffect Action.continuouslyAddBromide = Effect.oscillationsStop := by
  exact ⟨action_1_answer.1, action_2_answer.1,
    action_3_answer.1, action_4_answer.1⟩

#print axioms action_1_answer
#print axioms action_2_answer
#print axioms action_3_answer
#print axioms action_4_answer
#print axioms all_requested_outputs

end

end IChO2026Problems.T2A6
