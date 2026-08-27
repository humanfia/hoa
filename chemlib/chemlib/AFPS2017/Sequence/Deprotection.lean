import AFPS2017.Sequence.State

/-!
# Abstract deprotection transition

This module models deprotection as a structural state transition: it marks the
N terminus as deprotected while retaining the chain, linker, resin loading,
and reactive-site amount. It does not assert that an experimental
deprotection succeeded.

Source reference:

* Sanitized sequence contract (`afps2017.sequence.contract:question`).
-/

namespace AFPS2017.Sequence

/-- Mark the N terminus as deprotected without changing the remaining state. -/
def deprotect :
    {Identity Chirality Protection Linker : Type} →
      AFPS2017.Sequence.ResinBoundState Identity Chirality Protection Linker →
        AFPS2017.Sequence.ResinBoundState Identity Chirality Protection Linker :=
  fun state =>
    { state with
      nTerminalProtection := AFPS2017.Sequence.NTerminalProtection.deprotected }

/-- The abstract deprotection transition changes only the protection field. -/
theorem deprotect_changes_only_protection :
    {Identity Chirality Protection Linker : Type} →
      (state : AFPS2017.Sequence.ResinBoundState Identity Chirality Protection Linker) →
        (AFPS2017.Sequence.deprotect state).chainNToC = state.chainNToC ∧
          (AFPS2017.Sequence.deprotect state).linker = state.linker ∧
          (AFPS2017.Sequence.deprotect state).loading = state.loading ∧
          (AFPS2017.Sequence.deprotect state).reactiveSiteAmount = state.reactiveSiteAmount ∧
          (AFPS2017.Sequence.deprotect state).nTerminalProtection =
            AFPS2017.Sequence.NTerminalProtection.deprotected := by
  intro Identity Chirality Protection Linker state
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end AFPS2017.Sequence
