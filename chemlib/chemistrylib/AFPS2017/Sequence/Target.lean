import AFPS2017.Sequence.Residue

/-!
# Peptide targets and coupling order

A peptide target stores its residue sequence from the N-terminus to the
C-terminus together with evidence that the sequence is nonempty. Solid-phase
assembly begins with the C-terminal residue already loaded, so the subsequent
coupling schedule reverses all preceding residues into C-to-N order.

Source references:

* Sequence-orientation contract from the benchmark question
  (`afps2017.sequence.contract:question`).
* Mijalis et al., Nature Chemical Biology (2017),
  DOI `10.1038/nchembio.2318`
  (`afps2017.main:DOI-10.1038/nchembio.2318`).
-/

namespace AFPS2017.Sequence

/-- A nonempty peptide sequence stored in public N-to-C orientation. -/
structure PeptideTarget (Identity Chirality Protection : Type) : Type where
  residuesNToC : List (ResidueSpec Identity Chirality Protection)
  nonempty : residuesNToC ≠ []

/-- The C-terminal residue, which is initially loaded before coupling begins. -/
def cTerminalResidue {Identity Chirality Protection : Type}
    (target : PeptideTarget Identity Chirality Protection) :
    ResidueSpec Identity Chirality Protection :=
  target.residuesNToC.getLast target.nonempty

/-- Residues to couple after initial loading, ordered from C to N. -/
def couplingSchedule {Identity Chirality Protection : Type}
    (target : PeptideTarget Identity Chirality Protection) :
    List (ResidueSpec Identity Chirality Protection) :=
  target.residuesNToC.dropLast.reverse

/-- Initial loading plus the coupling schedule accounts for every target residue. -/
theorem couplingSchedule_length {Identity Chirality Protection : Type}
    (target : PeptideTarget Identity Chirality Protection) :
    (couplingSchedule target).length + 1 = target.residuesNToC.length := by
  cases h : target.residuesNToC with
  | nil => exact (target.nonempty h).elim
  | cons head tail => simp [couplingSchedule, h]

end AFPS2017.Sequence
