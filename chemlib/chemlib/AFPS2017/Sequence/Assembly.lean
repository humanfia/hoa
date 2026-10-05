import AFPS2017.Sequence.Cycle
import AFPS2017.Sequence.Target

/-!
# Repeated conditional sequence assembly

This module models a finite, connected sequence of full-cycle coupling attempts
in the C-to-N order supplied by a peptide target. The trace records intended
operations only. Successful coupling, absence of deletion, and absence of
epimerization remain three explicit hypotheses for every attempt.

Source references:

* Sanitized sequence contract (`afps2017.sequence.contract:question`).
* Mijalis et al., Nature Chemical Biology (2017), DOI `10.1038/nchembio.2318`
  (`afps2017.main:DOI-10.1038/nchembio.2318`).
-/

namespace AFPS2017.Sequence

/-- A connected finite trace whose attempts follow the supplied coupling
schedule. Each step starts from the previous step's observed final state. -/
def IsCouplingTrace :
    {Identity Chirality Protection Linker : Type} →
      List (AFPS2017.Sequence.ResidueSpec Identity Chirality Protection) →
        AFPS2017.Sequence.ResinBoundState Identity Chirality Protection Linker →
          AFPS2017.Sequence.ResinBoundState Identity Chirality Protection Linker →
            List (AFPS2017.Sequence.CouplingAttempt
              Identity Chirality Protection Linker) → Prop
  | _, _, _, _, [], initial, final, [] => final = initial
  | _, _, _, _, incoming :: schedule, initial, final, attempt :: attempts =>
      ∃ next,
        attempt = AFPS2017.Sequence.fullCycle incoming initial next ∧
          AFPS2017.Sequence.IsCouplingTrace schedule next final attempts
  | _, _, _, _, _, _, _, _ => False

/-- Explicitly successful, deletion-free, and epimerization-free attempts along
a connected C-to-N trace construct the target sequence and have the expected
cycle count. -/
theorem repeated_successful_cycles_construct_target :
    {Identity Chirality Protection Linker : Type} →
      (target : AFPS2017.Sequence.PeptideTarget Identity Chirality Protection) →
        (initial final : AFPS2017.Sequence.ResinBoundState
          Identity Chirality Protection Linker) →
          (attempts : List (AFPS2017.Sequence.CouplingAttempt
            Identity Chirality Protection Linker)) →
            initial.chainNToC = [AFPS2017.Sequence.cTerminalResidue target] →
              AFPS2017.Sequence.IsCouplingTrace
                (AFPS2017.Sequence.couplingSchedule target) initial final attempts →
                (∀ attempt ∈ attempts, AFPS2017.Sequence.SuccessfulCoupling attempt) →
                  (∀ attempt ∈ attempts, AFPS2017.Sequence.NoDeletion attempt) →
                    (∀ attempt ∈ attempts,
                      AFPS2017.Sequence.NoEpimerization attempt) →
                      final.chainNToC = target.residuesNToC ∧
                        attempts.length + 1 = target.residuesNToC.length := by
  intro Identity Chirality Protection Linker target initial final attempts
    initialChain trace allSuccessful allNoDeletion allNoEpimerization
  have assemble :
      ∀ (schedule : List (ResidueSpec Identity Chirality Protection))
        (start finish : ResinBoundState Identity Chirality Protection Linker)
        (recorded : List (CouplingAttempt Identity Chirality Protection Linker)),
        IsCouplingTrace schedule start finish recorded →
          (∀ attempt ∈ recorded, SuccessfulCoupling attempt) →
            (∀ attempt ∈ recorded, NoDeletion attempt) →
              (∀ attempt ∈ recorded, NoEpimerization attempt) →
                finish.chainNToC = schedule.reverse ++ start.chainNToC ∧
                  recorded.length = schedule.length := by
    intro schedule
    induction schedule with
    | nil =>
        intro start finish recorded trace _ _ _
        cases recorded with
        | nil =>
            simp only [IsCouplingTrace] at trace
            subst finish
            simp
        | cons attempt attempts =>
            simp [IsCouplingTrace] at trace
    | cons incoming schedule inductionHypothesis =>
        intro start finish recorded trace successful noDeletion noEpimerization
        cases recorded with
        | nil =>
            simp [IsCouplingTrace] at trace
        | cons attempt attempts =>
            simp only [IsCouplingTrace] at trace
            rcases trace with ⟨next, attemptDefinition, remainingTrace⟩
            subst attempt
            have headSuccessful :
                SuccessfulCoupling (fullCycle incoming start next) :=
              successful _ (by simp)
            have headNoDeletion :
                NoDeletion (fullCycle incoming start next) :=
              noDeletion _ (by simp)
            have headNoEpimerization :
                NoEpimerization (fullCycle incoming start next) :=
              noEpimerization _ (by simp)
            have stepChain : next.chainNToC = incoming :: start.chainNToC :=
              successful_full_cycle_adds_intended incoming start next
                headSuccessful headNoDeletion headNoEpimerization
            have remainingSuccessful :
                ∀ candidate ∈ attempts, SuccessfulCoupling candidate := by
              intro candidate candidateMem
              exact successful candidate (List.mem_cons_of_mem _ candidateMem)
            have remainingNoDeletion :
                ∀ candidate ∈ attempts, NoDeletion candidate := by
              intro candidate candidateMem
              exact noDeletion candidate (List.mem_cons_of_mem _ candidateMem)
            have remainingNoEpimerization :
                ∀ candidate ∈ attempts, NoEpimerization candidate := by
              intro candidate candidateMem
              exact noEpimerization candidate (List.mem_cons_of_mem _ candidateMem)
            obtain ⟨finishChain, remainingLength⟩ :=
              inductionHypothesis next finish attempts remainingTrace
                remainingSuccessful remainingNoDeletion remainingNoEpimerization
            constructor
            · rw [finishChain, stepChain]
              simp [List.reverse_cons, List.append_assoc]
            · simp [remainingLength]
  obtain ⟨finalChain, attemptCount⟩ :=
    assemble (couplingSchedule target) initial final attempts trace
      allSuccessful allNoDeletion allNoEpimerization
  constructor
  · rw [finalChain, initialChain]
    cases residuesDefinition : target.residuesNToC with
    | nil => exact (target.nonempty residuesDefinition).elim
    | cons head tail =>
        simp only [couplingSchedule, cTerminalResidue, residuesDefinition,
          List.reverse_reverse]
        exact List.dropLast_append_getLast (by simp)
  · calc
      attempts.length + 1 = (couplingSchedule target).length + 1 := by
        rw [attemptCount]
      _ = target.residuesNToC.length := couplingSchedule_length target

end AFPS2017.Sequence
