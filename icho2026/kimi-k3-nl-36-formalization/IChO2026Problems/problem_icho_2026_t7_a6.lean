import Mathlib

/-!
# IChO 2026 T7-A6: conditional contest model

This file formalizes the page-3 ranking task under exactly the user-authorized
finite model hypotheses M701 and M702.  The four calibration yields are printed
data.  The four candidate yields remain universally quantified and are never
introduced as measurements or as hypotheses.

The model deliberately uses different structures for standard potential,
dimensionless pK_a, and an ammonia amount measured in moles.  The explicit
`MolarResponseScale` below is used only to build a mathematical consistency
witness; that witness is not experimental data.
-/

namespace IChO2026Problems.IChO2026T7A6

noncomputable section

/-- A standard reduction potential, with its scalar coordinate measured in volts. -/
structure StandardPotential where
  volts : ℝ

/-- The dimensionless pK_a value printed for an additive. -/
structure PKaValue where
  dimensionless : ℝ

/-- The response reported by the table: an amount of ammonia in moles. -/
structure AmmoniaAmount where
  moles : ℝ

/-- Metal identity in the depicted bis(cyclopentadienyl) reductant. -/
inductive ReductantIdentity
  | bisCyclopentadienylChromium
  | bisCyclopentadienylCobalt
  | bisCyclopentadienylNickel
  | bisCyclopentadienylVanadium
deriving DecidableEq, Fintype, Repr

/-- Counterions explicitly depicted on page 3. -/
inductive Counterion
  | triflate
  | chloride
deriving DecidableEq, Fintype, Repr

/-- Cation structures used to distinguish the depicted additives. -/
inductive AdditiveCation
  | dimethylPyridinium
  | methylPyridinium
  | phenanthrolinium
  | trimethylPyridinium
  | anilinium
deriving DecidableEq, Fintype, Repr

/-- The complete finite domain of the four calibrations and four candidates on
page 3.  Having exactly these constructors is the finite-scope boundary of
M701/M702. -/
inductive Page3Entry
  | calibration1
  | calibration2
  | calibration3
  | calibration4
  | candidateA
  | candidateB
  | candidateC
  | candidateD
deriving DecidableEq, Fintype, Repr

/-- All source features attached to one page-3 entry, excluding candidate
ammonia yields (which are not printed). -/
structure EntryFeatures where
  reductant : ReductantIdentity
  potential : StandardPotential
  additive : AdditiveCation
  counterion : Counterion
  pKa : PKaValue

/-- Exact transcription of the eight page-3 feature columns. -/
def entryFeatures : Page3Entry → EntryFeatures
  | .calibration1 =>
      ⟨.bisCyclopentadienylChromium, ⟨-(22 : ℝ) / 25⟩,
        .dimethylPyridinium, .triflate, ⟨(72 : ℝ) / 5⟩⟩
  | .calibration2 =>
      ⟨.bisCyclopentadienylCobalt, ⟨-(23 : ℝ) / 20⟩,
        .dimethylPyridinium, .chloride, ⟨(72 : ℝ) / 5⟩⟩
  | .calibration3 =>
      ⟨.bisCyclopentadienylCobalt, ⟨-(23 : ℝ) / 20⟩,
        .methylPyridinium, .triflate, ⟨(139 : ℝ) / 10⟩⟩
  | .calibration4 =>
      ⟨.bisCyclopentadienylCobalt, ⟨-(23 : ℝ) / 20⟩,
        .dimethylPyridinium, .triflate, ⟨(72 : ℝ) / 5⟩⟩
  | .candidateA =>
      ⟨.bisCyclopentadienylNickel, ⟨-(9 : ℝ) / 100⟩,
        .phenanthrolinium, .triflate, ⟨(137 : ℝ) / 10⟩⟩
  | .candidateB =>
      ⟨.bisCyclopentadienylVanadium, ⟨-(11 : ℝ) / 10⟩,
        .trimethylPyridinium, .triflate, ⟨15⟩⟩
  | .candidateC =>
      ⟨.bisCyclopentadienylVanadium, ⟨-(11 : ℝ) / 10⟩,
        .phenanthrolinium, .triflate, ⟨(137 : ℝ) / 10⟩⟩
  | .candidateD =>
      ⟨.bisCyclopentadienylVanadium, ⟨-(11 : ℝ) / 10⟩,
        .anilinium, .triflate, ⟨(53 : ℝ) / 5⟩⟩

/-- The finite scope named in the authorization: precisely all eight entries. -/
def page3Entries : Finset Page3Entry := Finset.univ

/-- The candidate panel printed under question 7.6. -/
def candidateEntries : Finset Page3Entry :=
  [.candidateA, .candidateB, .candidateC, .candidateD].toFinset

/-- Printed ammonia amounts exist only for calibration columns 1--4. -/
def printedCalibrationAmount : Page3Entry → Option AmmoniaAmount
  | .calibration1 => some ⟨0⟩
  | .calibration2 => some ⟨(7 : ℝ) / 10⟩
  | .calibration3 => some ⟨(91 : ℝ) / 10⟩
  | .calibration4 => some ⟨(59 : ℝ) / 5⟩
  | .candidateA | .candidateB | .candidateC | .candidateD => none

/-- A response function is compatible with the page-3 observations precisely
when it reproduces every printed calibration amount and is nonnegative on the
finite eight-entry domain.  It prescribes no candidate amount. -/
def CompatibleWithPrintedCalibration
    (response : Page3Entry → AmmoniaAmount) : Prop :=
  (∀ entry amount,
      printedCalibrationAmount entry = some amount → response entry = amount) ∧
  ∀ entry, entry ∈ page3Entries → 0 ≤ (response entry).moles

/-- Calibration 1 is the printed zero-yield reference used by M701. -/
def zeroYieldReference : Page3Entry := .calibration1

/-- The cutoff is extracted from the reference column rather than supplied as
an independent number. -/
def zeroYieldReferencePotential : StandardPotential :=
  (entryFeatures zeroYieldReference).potential

/-- The reference counterion is likewise extracted from calibration 1. -/
def zeroYieldReferenceCounterion : Counterion :=
  (entryFeatures zeroYieldReference).counterion

/-- **M701, conditional_contest_model.**  Uniformly on the eight page-3
entries, an entry at or above the printed zero-yield reference potential has
zero response; below the cutoff, an entry carrying the reference counterion
has strictly positive response.

This is the authorized finite idealization, not a source-derived electrochemical
law.  It names no candidate and contains no pairwise ranking. -/
def M701_conditional_contest_model
    (response : Page3Entry → AmmoniaAmount) : Prop :=
  ∀ entry, entry ∈ page3Entries →
    (zeroYieldReferencePotential.volts ≤ (entryFeatures entry).potential.volts →
        (response entry).moles = 0) ∧
    ((entryFeatures entry).potential.volts < zeroYieldReferencePotential.volts ∧
        (entryFeatures entry).counterion = zeroYieldReferenceCounterion →
      0 < (response entry).moles)

/-- Entries match for the three features held fixed by M702.  Additive identity
and pK_a are intentionally not among the matched fields. -/
def SameM702Conditions (first second : Page3Entry) : Prop :=
  (entryFeatures first).reductant = (entryFeatures second).reductant ∧
  (entryFeatures first).potential = (entryFeatures second).potential ∧
  (entryFeatures first).counterion = (entryFeatures second).counterion

/-- Strict positivity is the activity condition used by M702. -/
def ActiveEntry (response : Page3Entry → AmmoniaAmount)
    (entry : Page3Entry) : Prop :=
  0 < (response entry).moles

/-- Dimensionless pK_a change from one entry to another. -/
def pKaChange (fromEntry toEntry : Page3Entry) : ℝ :=
  (entryFeatures toEntry).pKa.dimensionless -
    (entryFeatures fromEntry).pKa.dimensionless

/-- Molar ammonia-response change from one entry to another. -/
def ammoniaAmountChange (response : Page3Entry → AmmoniaAmount)
    (fromEntry toEntry : Page3Entry) : ℝ :=
  (response toEntry).moles - (response fromEntry).moles

/-- The lower-pK_a member of the printed, matched, positive calibration pair. -/
def matchedCalibrationLow : Page3Entry := .calibration3

/-- The higher-pK_a member of the printed, matched, positive calibration pair. -/
def matchedCalibrationHigh : Page3Entry := .calibration4

/-- **M702, conditional_contest_model.**  Once the actual calibration-3 to
calibration-4 pK_a and molar-response changes have both been proved positive,
their sign transfers to every pair of active entries in the finite page-3
domain that shares reductant identity, potential, and counterion.

The calibration contrast occurs as an indispensable antecedent: unused table
fields cannot activate this rule.  This authorized finite comparative model
names no candidate and assumes no candidate amount or candidate comparison. -/
def M702_conditional_contest_model
    (response : Page3Entry → AmmoniaAmount) : Prop :=
  ActiveEntry response matchedCalibrationLow →
  ActiveEntry response matchedCalibrationHigh →
  SameM702Conditions matchedCalibrationLow matchedCalibrationHigh →
  0 < pKaChange matchedCalibrationLow matchedCalibrationHigh →
  0 < ammoniaAmountChange response matchedCalibrationLow matchedCalibrationHigh →
  ∀ lower higher,
    lower ∈ page3Entries →
    higher ∈ page3Entries →
    ActiveEntry response lower →
    ActiveEntry response higher →
    SameM702Conditions lower higher →
    0 < pKaChange lower higher →
    0 < ammoniaAmountChange response lower higher

/-- The source table has no measured candidate response. -/
theorem candidates_are_exactly_the_unmeasured_entries :
    ∀ entry, printedCalibrationAmount entry = none ↔ entry ∈ candidateEntries := by
  intro entry
  cases entry <;> simp [printedCalibrationAmount, candidateEntries]

/-- The two calibration columns used by M702 really match in reductant,
potential, and counterion. -/
theorem printed_M702_calibrations_match :
    SameM702Conditions matchedCalibrationLow matchedCalibrationHigh := by
  simp [SameM702Conditions, matchedCalibrationLow, matchedCalibrationHigh,
    entryFeatures]

/-- The printed pK_a values give a positive `13.9 -> 14.4` change. -/
theorem printed_M702_pKa_change_is_positive :
    0 < pKaChange matchedCalibrationLow matchedCalibrationHigh := by
  norm_num [pKaChange, matchedCalibrationLow, matchedCalibrationHigh,
    entryFeatures]

/-- Compatibility with the printed yields gives a positive `9.1 mol ->
11.8 mol` calibration change. -/
theorem printed_M702_ammonia_change_is_positive
    (response : Page3Entry → AmmoniaAmount)
    (hSource : CompatibleWithPrintedCalibration response) :
    0 < ammoniaAmountChange response matchedCalibrationLow matchedCalibrationHigh := by
  rcases hSource with ⟨hCalibration, _⟩
  have hLow := hCalibration .calibration3 ⟨(91 : ℝ) / 10⟩ (by
    simp [printedCalibrationAmount])
  have hHigh := hCalibration .calibration4 ⟨(59 : ℝ) / 5⟩ (by
    simp [printedCalibrationAmount])
  simp [ammoniaAmountChange, matchedCalibrationLow, matchedCalibrationHigh,
    hLow, hHigh]
  norm_num

/-- Both printed members of the M702 calibration pair are active. -/
theorem printed_M702_calibrations_are_active
    (response : Page3Entry → AmmoniaAmount)
    (hSource : CompatibleWithPrintedCalibration response) :
    ActiveEntry response matchedCalibrationLow ∧
      ActiveEntry response matchedCalibrationHigh := by
  rcases hSource with ⟨hCalibration, _⟩
  have hLow := hCalibration .calibration3 ⟨(91 : ℝ) / 10⟩ (by
    simp [printedCalibrationAmount])
  have hHigh := hCalibration .calibration4 ⟨(59 : ℝ) / 5⟩ (by
    simp [printedCalibrationAmount])
  constructor <;>
    simp [ActiveEntry, matchedCalibrationLow, matchedCalibrationHigh, hLow, hHigh]

/-- This wrapper makes the mandated use of the observed calibration contrast
explicit whenever M702 is transferred to another matched active pair. -/
theorem apply_M702_using_printed_calibration
    (response : Page3Entry → AmmoniaAmount)
    (hSource : CompatibleWithPrintedCalibration response)
    (hM702 : M702_conditional_contest_model response)
    (lower higher : Page3Entry)
    (hLowerMem : lower ∈ page3Entries)
    (hHigherMem : higher ∈ page3Entries)
    (hLowerActive : ActiveEntry response lower)
    (hHigherActive : ActiveEntry response higher)
    (hMatched : SameM702Conditions lower higher)
    (hPkaIncrease : 0 < pKaChange lower higher) :
    0 < ammoniaAmountChange response lower higher := by
  rcases printed_M702_calibrations_are_active response hSource with
    ⟨hCalibrationLowActive, hCalibrationHighActive⟩
  exact hM702 hCalibrationLowActive hCalibrationHighActive
    printed_M702_calibrations_match printed_M702_pKa_change_is_positive
    (printed_M702_ammonia_change_is_positive response hSource)
    lower higher hLowerMem hHigherMem hLowerActive hHigherActive hMatched
    hPkaIncrease

/-- Source-feature consequence: A is at or above the M701 cutoff. -/
theorem candidateA_is_at_or_above_M701_cutoff :
    zeroYieldReferencePotential.volts ≤
      (entryFeatures .candidateA).potential.volts := by
  norm_num [zeroYieldReferencePotential, zeroYieldReference,
    entryFeatures]

/-- Source-feature consequence: B, C, and D are below the M701 cutoff and use
the reference's triflate counterion. -/
theorem candidatesBCD_are_below_M701_cutoff_with_reference_counterion :
    ∀ entry ∈ ([Page3Entry.candidateB, .candidateC, .candidateD].toFinset),
      (entryFeatures entry).potential.volts < zeroYieldReferencePotential.volts ∧
      (entryFeatures entry).counterion = zeroYieldReferenceCounterion := by
  intro entry hEntry
  simp at hEntry
  rcases hEntry with rfl | rfl | rfl <;>
    norm_num [entryFeatures, zeroYieldReferencePotential, zeroYieldReference,
      zeroYieldReferenceCounterion]

/-- Source-feature consequence: D to C and C to B are matched M702 pairs with
strictly increasing pK_a. -/
theorem candidates_DCB_have_matched_conditions_and_increasing_pKa :
    SameM702Conditions .candidateD .candidateC ∧
    0 < pKaChange .candidateD .candidateC ∧
    SameM702Conditions .candidateC .candidateB ∧
    0 < pKaChange .candidateC .candidateB := by
  norm_num [SameM702Conditions, pKaChange, entryFeatures]

/-- A proposed ranking covers every candidate exactly once and decreases
strictly in molar ammonia response at every earlier/later pair. -/
def IsStrictDecreasingCandidateRanking
    (response : Page3Entry → AmmoniaAmount) (ranking : List Page3Entry) : Prop :=
  ranking.Nodup ∧
  ranking.toFinset = candidateEntries ∧
  ranking.Pairwise
    (fun earlier later => (response later).moles < (response earlier).moles)

/-- The frozen Kimi draft's proposed ranking, represented only as the output
candidate to be verified, never as a premise. -/
def kimiDraftRanking : List Page3Entry :=
  [.candidateB, .candidateC, .candidateD, .candidateA]

/-- Requested output for T7-A6.  For every response function compatible with
the printed calibration and the two authorized feature-based rules, the frozen
draft ranking is strictly decreasing.

This declaration is intentionally labelled `conditional_contest_model` under
M701/M702; neither rule is asserted as an unconditional source fact. -/
theorem yield_ranking_conditional_contest_model_M701_M702
    (response : Page3Entry → AmmoniaAmount)
    (hSource : CompatibleWithPrintedCalibration response)
    (hM701 : M701_conditional_contest_model response)
    (hM702 : M702_conditional_contest_model response) :
    IsStrictDecreasingCandidateRanking response kimiDraftRanking := by
  have hAModel := hM701 .candidateA (by simp [page3Entries])
  have hAZero : (response .candidateA).moles = 0 :=
    hAModel.1 candidateA_is_at_or_above_M701_cutoff
  have hBCD := candidatesBCD_are_below_M701_cutoff_with_reference_counterion
  have hBFeatures := hBCD .candidateB (by simp)
  have hCFeatures := hBCD .candidateC (by simp)
  have hDFeatures := hBCD .candidateD (by simp)
  have hBPositive : ActiveEntry response .candidateB :=
    (hM701 .candidateB (by simp [page3Entries])).2 hBFeatures
  have hCPositive : ActiveEntry response .candidateC :=
    (hM701 .candidateC (by simp [page3Entries])).2 hCFeatures
  have hDPositive : ActiveEntry response .candidateD :=
    (hM701 .candidateD (by simp [page3Entries])).2 hDFeatures
  rcases candidates_DCB_have_matched_conditions_and_increasing_pKa with
    ⟨hDCMatched, hDCPKa, hCBMatched, hCBPKa⟩
  have hDCChange := apply_M702_using_printed_calibration response hSource hM702
    .candidateD .candidateC (by simp [page3Entries]) (by simp [page3Entries])
    hDPositive hCPositive hDCMatched hDCPKa
  have hCBChange := apply_M702_using_printed_calibration response hSource hM702
    .candidateC .candidateB (by simp [page3Entries]) (by simp [page3Entries])
    hCPositive hBPositive hCBMatched hCBPKa
  have hDC : (response .candidateD).moles < (response .candidateC).moles := by
    simpa [ammoniaAmountChange] using hDCChange
  have hCB : (response .candidateC).moles < (response .candidateB).moles := by
    simpa [ammoniaAmountChange] using hCBChange
  have hDB : (response .candidateD).moles < (response .candidateB).moles :=
    hDC.trans hCB
  have hAB : (response .candidateA).moles < (response .candidateB).moles := by
    rw [hAZero]
    exact hBPositive
  have hAC : (response .candidateA).moles < (response .candidateC).moles := by
    rw [hAZero]
    exact hCPositive
  have hAD : (response .candidateA).moles < (response .candidateD).moles := by
    rw [hAZero]
    exact hDPositive
  refine ⟨?_, ?_, ?_⟩
  · simp [kimiDraftRanking]
  · ext entry
    cases entry <;> simp [kimiDraftRanking, candidateEntries]
  · simp [kimiDraftRanking, hCB, hDB, hAB, hDC, hAC, hAD]

/-! ## Separate nonvacuity witness

The following construction is a mathematical response model, not a set of
additional measurements.  A dimensionless score is converted to moles only by
an explicit response scale.
-/

/-- A dimensionless mathematical score used only in the consistency witness. -/
structure DimensionlessResponseScore where
  value : ℝ

/-- A dimensional conversion factor, measured in moles per dimensionless score
unit. -/
structure MolarResponseScale where
  molesPerDimensionlessUnit : ℝ

/-- Apply a declared response scale; this is the only score-to-moles bridge. -/
def MolarResponseScale.toAmmoniaAmount
    (scale : MolarResponseScale) (score : DimensionlessResponseScore) :
    AmmoniaAmount :=
  ⟨scale.molesPerDimensionlessUnit * score.value⟩

/-- One mole per response-score unit, declared solely for the consistency
witness. -/
def consistencyResponseScale : MolarResponseScale := ⟨1⟩

/-- A feature-only, monotone piecewise score anchored at the two printed M702
calibration values.  It uses pK_a as an input but does not identify pK_a with a
molar amount. -/
def activeTriflateWitnessScore (pKa : PKaValue) : DimensionlessResponseScore :=
  if pKa.dimensionless ≤ (139 : ℝ) / 10 then
    ⟨(91 : ℝ) / 10 + (pKa.dimensionless - (139 : ℝ) / 10)⟩
  else
    ⟨(91 : ℝ) / 10 + (27 : ℝ) / 5 *
      (pKa.dimensionless - (139 : ℝ) / 10)⟩

/-- Uniform mathematical score on all eight entries.  It branches only on the
source features used by M701/M702, never on a candidate label. -/
def mathematicalWitnessScore (entry : Page3Entry) : DimensionlessResponseScore :=
  if zeroYieldReferencePotential.volts ≤ (entryFeatures entry).potential.volts then
    ⟨0⟩
  else if (entryFeatures entry).counterion = .chloride then
    ⟨(7 : ℝ) / 10⟩
  else
    activeTriflateWitnessScore (entryFeatures entry).pKa

/-- A dimensionally coherent response function witnessing mathematical
consistency.  Its unmeasured entries are model values, not claimed measurements. -/
def mathematicalConsistencyWitness (entry : Page3Entry) : AmmoniaAmount :=
  consistencyResponseScale.toAmmoniaAmount (mathematicalWitnessScore entry)

/-- The explicit witness satisfies the printed calibration and both authorized
conditional contest-model rules. -/
theorem mathematicalConsistencyWitness_satisfies_M701_M702 :
    CompatibleWithPrintedCalibration mathematicalConsistencyWitness ∧
    M701_conditional_contest_model mathematicalConsistencyWitness ∧
    M702_conditional_contest_model mathematicalConsistencyWitness := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro entry amount hAmount
      cases entry <;>
        simp_all [printedCalibrationAmount, mathematicalConsistencyWitness,
          MolarResponseScale.toAmmoniaAmount, consistencyResponseScale,
          mathematicalWitnessScore, activeTriflateWitnessScore,
          zeroYieldReferencePotential, zeroYieldReference, entryFeatures] <;>
        norm_num at * <;>
        assumption
    · intro entry _
      cases entry <;>
        simp [page3Entries, mathematicalConsistencyWitness,
          MolarResponseScale.toAmmoniaAmount, consistencyResponseScale,
          mathematicalWitnessScore, activeTriflateWitnessScore,
          zeroYieldReferencePotential, zeroYieldReference, entryFeatures] <;>
        norm_num
  · intro entry _
    cases entry <;>
      simp [mathematicalConsistencyWitness,
        MolarResponseScale.toAmmoniaAmount, consistencyResponseScale,
        mathematicalWitnessScore, activeTriflateWitnessScore,
        zeroYieldReferencePotential, zeroYieldReference,
        zeroYieldReferenceCounterion, entryFeatures] <;>
      norm_num
  · intro _ _ _ _ _ lower higher _ _ hLowerActive hHigherActive hMatched
      hPkaIncrease
    cases lower <;> cases higher <;>
      norm_num [SameM702Conditions, entryFeatures] at hMatched
    all_goals norm_num [pKaChange, entryFeatures] at hPkaIncrease
    all_goals
      norm_num [ammoniaAmountChange, mathematicalConsistencyWitness,
        MolarResponseScale.toAmmoniaAmount, consistencyResponseScale,
        mathematicalWitnessScore, activeTriflateWitnessScore,
        zeroYieldReferencePotential, zeroYieldReference, entryFeatures] <;>
      simp_all <;>
      norm_num

/-- Separate nonemptiness statement for the authorized conditional model. -/
theorem conditional_contest_model_M701_M702_nonempty :
    ∃ response : Page3Entry → AmmoniaAmount,
      CompatibleWithPrintedCalibration response ∧
      M701_conditional_contest_model response ∧
      M702_conditional_contest_model response := by
  exact ⟨mathematicalConsistencyWitness,
    mathematicalConsistencyWitness_satisfies_M701_M702⟩

end

end IChO2026Problems.IChO2026T7A6
