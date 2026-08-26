import AFPS2017.Sequence.Coupling
import AFPS2017.Sequence.Deprotection
import AFPS2017.Sequence.Wash

/-!
# Abstract solid-phase synthesis cycle

This module composes the abstract deprotection and wash transitions before
recording a coupling attempt. It makes no empirical-success inference: the
coupling outcome, absence of deletion, and absence of epimerization remain
three explicit hypotheses.

Source reference: sanitized sequence contract
(`afps2017.sequence.contract:question`).
-/

namespace AFPS2017.Sequence

/-- Record coupling after the abstract deprotection and wash transitions. -/
def fullCycle :
    {Identity Chirality Protection Linker : Type} →
      AFPS2017.Sequence.ResidueSpec Identity Chirality Protection →
        AFPS2017.Sequence.ResinBoundState Identity Chirality Protection Linker →
          AFPS2017.Sequence.ResinBoundState Identity Chirality Protection Linker →
            AFPS2017.Sequence.CouplingAttempt Identity Chirality Protection Linker :=
  fun incoming before after =>
    AFPS2017.Sequence.couple incoming
      (AFPS2017.Sequence.wash (AFPS2017.Sequence.deprotect before)) after

/-- Under the three explicit outcome obligations, one full cycle prepends the
intended residue. -/
theorem successful_full_cycle_adds_intended :
    {Identity Chirality Protection Linker : Type} →
      (incoming : AFPS2017.Sequence.ResidueSpec Identity Chirality Protection) →
        (before after : AFPS2017.Sequence.ResinBoundState Identity Chirality Protection Linker) →
          AFPS2017.Sequence.SuccessfulCoupling
              (AFPS2017.Sequence.fullCycle incoming before after) →
            AFPS2017.Sequence.NoDeletion
                (AFPS2017.Sequence.fullCycle incoming before after) →
              AFPS2017.Sequence.NoEpimerization
                  (AFPS2017.Sequence.fullCycle incoming before after) →
                after.chainNToC = incoming :: before.chainNToC := by
  intro Identity Chirality Protection Linker incoming before after
    successful noDeletion noEpimerization
  have cycleResult :=
    AFPS2017.Sequence.successful_coupling_prepends
      (AFPS2017.Sequence.fullCycle incoming before after)
      successful noDeletion noEpimerization
  simpa [AFPS2017.Sequence.fullCycle, AFPS2017.Sequence.couple,
    AFPS2017.Sequence.wash, AFPS2017.Sequence.deprotect] using cycleResult

end AFPS2017.Sequence
