import AFPS2017.Sequence.State

/-!
# Conditional coupling

This module records a solid-phase coupling attempt without claiming that the
experimental operation succeeded. Successful attachment, preservation of the
existing chain, and preservation of chirality remain separate hypotheses.

Source references:

* Sanitized sequence contract (`afps2017.sequence.contract:question`).
* Public AFPS2017 article, DOI `10.1038/nchembio.2318`
  (`afps2017.main`).
-/

namespace AFPS2017.Sequence

/-- The recorded inputs and observed state of one coupling attempt. -/
structure CouplingAttempt
    (Identity Chirality Protection Linker : Type) : Type where
  after : ResinBoundState Identity Chirality Protection Linker
  before : ResinBoundState Identity Chirality Protection Linker
  incoming : ResidueSpec Identity Chirality Protection

/-- No pre-existing residue is deleted: removing the new head recovers the prior chain. -/
def NoDeletion
    {Identity Chirality Protection Linker : Type}
    (attempt : CouplingAttempt Identity Chirality Protection Linker) : Prop :=
  attempt.after.chainNToC.drop 1 = attempt.before.chainNToC

/-- The newly exposed N-terminal residue retains the incoming residue's chirality. -/
def NoEpimerization
    {Identity Chirality Protection Linker : Type}
    (attempt : CouplingAttempt Identity Chirality Protection Linker) : Prop :=
  ∀ actual,
    attempt.after.chainNToC.head? = some actual →
      actual.chirality = attempt.incoming.chirality

/-- Successful coupling attaches the intended identity/protection and preserves
non-sequence state. -/
def SuccessfulCoupling
    {Identity Chirality Protection Linker : Type}
    (attempt : CouplingAttempt Identity Chirality Protection Linker) : Prop :=
  (∃ actual,
      attempt.after.chainNToC.head? = some actual ∧
      actual.identity = attempt.incoming.identity ∧
      actual.protection = attempt.incoming.protection) ∧
    attempt.after.nTerminalProtection = .«protected» ∧
    attempt.after.linker = attempt.before.linker ∧
    attempt.after.loading = attempt.before.loading ∧
    attempt.after.reactiveSiteAmount = attempt.before.reactiveSiteAmount

/-- Record an intended residue, the state before coupling, and the observed state after it. -/
def couple
    {Identity Chirality Protection Linker : Type}
    (incoming : ResidueSpec Identity Chirality Protection)
    (before after : ResinBoundState Identity Chirality Protection Linker) :
    CouplingAttempt Identity Chirality Protection Linker :=
  { after, before, incoming }

/-- Under the three explicit outcome obligations, coupling prepends the incoming residue. -/
theorem successful_coupling_prepends
    {Identity Chirality Protection Linker : Type}
    (attempt : CouplingAttempt Identity Chirality Protection Linker)
    (successful : SuccessfulCoupling attempt)
    (noDeletion : NoDeletion attempt)
    (noEpimerization : NoEpimerization attempt) :
    attempt.after.chainNToC = attempt.incoming :: attempt.before.chainNToC := by
  rcases successful.1 with ⟨actual, hactual, hidentity, hprotection⟩
  cases hchain : attempt.after.chainNToC with
  | nil => simp [hchain] at hactual
  | cons head tail =>
      have hhead : head = actual := by simpa [hchain] using hactual
      subst head
      have htail : tail = attempt.before.chainNToC := by
        simpa [NoDeletion, hchain] using noDeletion
      have hchirality : actual.chirality = attempt.incoming.chirality :=
        noEpimerization actual hactual
      have hresidue : actual = attempt.incoming := by
        rcases actual with ⟨actualId, actualChirality, actualProtection⟩
        cases hincoming : attempt.incoming with
        | mk incomingId incomingChirality incomingProtection =>
            rw [hincoming] at hidentity hchirality hprotection
            cases hidentity
            cases hchirality
            cases hprotection
            rfl
      simp [htail, hresidue]

end AFPS2017.Sequence
