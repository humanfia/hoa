import Mathlib

/-!
# IChO 2026, theory problem 9.3

This file formalizes the two structural counts requested for compound `X`.
The problem diagram supplies seven glucopyranoside repeats.  Periodate cleavage
removes the C2--C3 bond in every repeat; borohydride reduction makes the two
ends methylene groups, and acetylation does not make a new carbon skeleton
bond.  Thus the surviving cyclic path has the five positions

`C1 - O5 - C5 - C4 - O(glycosidic)`

per repeat.  Of the five stereogenic carbon positions of the starting
glucopyranoside, C2 and C3 become methylene groups, leaving C1, C4, and C5.

The chemistry-to-combinatorics interpretation is kept explicit below.  The
numerical results are then proved by finite-cardinality arguments.
-/

namespace IChO2026Problems.T9A3

/-! ## Problem input -/

/-- The repeat label `7` printed on the beta-cyclodextrin starting-material
diagram in Q9-2. -/
def betaCDRepeatCount : ℕ := 7

theorem betaCDRepeatCount_eq : betaCDRepeatCount = 7 := rfl

/-! ## Ring-atom inventory after the reaction sequence -/

/-- The five atom positions contributed by each opened glucopyranoside repeat
to the one surviving covalent macrocycle.  `glycosidicO` joins C4 of the
current repeat to C1 of the next repeat. -/
inductive XRingSite
  | c1
  | o5
  | c5
  | c4
  | glycosidicO
  deriving DecidableEq, Fintype, Repr

/-- One traversal of the local part of the surviving ring. -/
def localRingTraversal : List XRingSite :=
  [.c1, .o5, .c5, .c4, .glycosidicO]

theorem localRingTraversal_length : localRingTraversal.length = 5 := rfl

theorem localRingTraversal_nodup : localRingTraversal.Nodup := by
  decide

theorem localRingTraversal_complete :
    localRingTraversal.toFinset = Finset.univ := by
  decide

theorem xRingSites_per_repeat : Fintype.card XRingSite = 5 := by
  decide

/-- A ring atom is determined by a repeat number and one of the five atom
positions in the surviving local path. -/
abbrev XRingAtom := Fin betaCDRepeatCount × XRingSite

/-- Ring size is the number of atoms in the surviving covalent cycle. -/
def ringSizeX : ℕ := Fintype.card XRingAtom

theorem ringSizeX_factorization :
    ringSizeX = betaCDRepeatCount * Fintype.card XRingSite := by
  simp [ringSizeX]

/-- Requested output `rs`: the macrocycle contains 35 ring atoms. -/
theorem macrocycle_X_ring_size : ringSizeX = 35 := by
  rw [ringSizeX_factorization, betaCDRepeatCount_eq, xRingSites_per_repeat]

/-! ## Stereocentre inventory after the reaction sequence -/

/-- Carbon positions that are stereogenic in an intact glucopyranoside repeat
before cleavage. -/
inductive GlucopyranosideStereoCarbon
  | c1
  | c2
  | c3
  | c4
  | c5
  deriving DecidableEq, Fintype, Repr

/-- Periodate cleaves the vicinal-diol C2--C3 bond.  After reduction, exactly
these two carbon positions are methylene groups and cannot be stereocentres. -/
def becomesMethyleneInX : GlucopyranosideStereoCarbon → Bool
  | .c2 | .c3 => true
  | .c1 | .c4 | .c5 => false

/-- The carbon positions that remain stereogenic in `X`: C1, C4, and C5. -/
def stereogenicInX : GlucopyranosideStereoCarbon → Bool
  | .c1 | .c4 | .c5 => true
  | .c2 | .c3 => false

theorem stereogenicInX_iff_not_methylene
    (carbon : GlucopyranosideStereoCarbon) :
    stereogenicInX carbon = !becomesMethyleneInX carbon := by
  cases carbon <;> rfl

/-- A stereocentre of `X` is a repeat number together with one of the retained
stereogenic carbon positions. -/
abbrev XStereocentre :=
  Fin betaCDRepeatCount ×
    {carbon : GlucopyranosideStereoCarbon // stereogenicInX carbon = true}

theorem xStereogenicCarbons_per_repeat :
    Fintype.card
        {carbon : GlucopyranosideStereoCarbon //
          stereogenicInX carbon = true} = 3 := by
  decide

/-- Total number of stereocentres in compound `X`. -/
def stereocentreCountX : ℕ := Fintype.card XStereocentre

theorem stereocentreCountX_factorization :
    stereocentreCountX =
      betaCDRepeatCount *
        Fintype.card
          {carbon : GlucopyranosideStereoCarbon //
            stereogenicInX carbon = true} := by
  simp [stereocentreCountX]

/-- Requested output `sc`: compound `X` contains 21 stereocentres. -/
theorem macrocycle_X_stereocentres : stereocentreCountX = 21 := by
  rw [stereocentreCountX_factorization, betaCDRepeatCount_eq,
    xStereogenicCarbons_per_repeat]

/-- The two requested integer outputs, packaged together. -/
theorem macrocycle_X_requested_outputs :
    ringSizeX = 35 ∧ stereocentreCountX = 21 :=
  ⟨macrocycle_X_ring_size, macrocycle_X_stereocentres⟩

#print axioms macrocycle_X_ring_size
#print axioms macrocycle_X_stereocentres
#print axioms macrocycle_X_requested_outputs

end IChO2026Problems.T9A3
