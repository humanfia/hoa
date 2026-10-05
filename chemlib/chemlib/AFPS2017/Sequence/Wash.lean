import AFPS2017.Sequence.State

/-!
# Abstract wash transition

This module models washing only at the sequence-state abstraction level. The
transition has no sequence-level effect and does not model solvent transport,
material removal, purification, efficiency, or empirical success.

Source reference: sanitized sequence contract
(`afps2017.sequence.contract:question`).
-/

namespace AFPS2017.Sequence

/-- The abstract wash transition has no effect on the sequence state. -/
def wash :
    {Identity Chirality Protection Linker : Type} →
      ResinBoundState Identity Chirality Protection Linker →
        ResinBoundState Identity Chirality Protection Linker :=
  fun state => state

/-- Washing preserves the growing chain stored in N-to-C order. -/
theorem wash_preserves_chain :
    {Identity Chirality Protection Linker : Type} →
      (state : ResinBoundState Identity Chirality Protection Linker) →
        (wash state).chainNToC = state.chainNToC := by
  intro Identity Chirality Protection Linker state
  rfl

end AFPS2017.Sequence
