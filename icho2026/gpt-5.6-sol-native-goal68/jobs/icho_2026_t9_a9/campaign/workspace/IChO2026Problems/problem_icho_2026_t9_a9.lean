import Mathlib

/-!
# IChO 2026 T9-A9: arrangements on hexadifferentiated alpha-cyclodextrin

The problem supplies two pieces of structural data used here:

* alpha-CD has six glucopyranoside units, hence six primary `CH2OH` sites;
* "hexadifferentiated" means that the six substituent groups are pairwise
  distinct.

The directed alpha-1,4-linked ring is treated as an oriented cycle.  Choosing
one of the distinct groups as an anchor removes the arbitrary choice of a
starting unit.  The five remaining distinct groups may then be assigned
bijectively to the five sites encountered in the fixed cyclic direction.
Thus the type of chemical arrangements is represented by the permutations of
five objects.  Reflection is deliberately not quotiented out: the source
itself distinguishes clockwise and counterclockwise in the immediately
preceding subquestion, and all glucose units have the stated D stereochemistry.
-/

namespace IChO2026Problems.T9A9

/-! ## Problem-input model -/

/-- The six primary sites of alpha-CD, one on each glucopyranoside unit. -/
abbrev PrimarySite := Fin 6

/-- A cyclic coordinate for the six sites.  Addition is rotation in the fixed
direction around the glycosidic ring. -/
abbrev CyclicIndex := ZMod 6

/-- A labelled assignment before forgetting the arbitrary starting point on
the ring.  Both the sites and the six pairwise-distinct groups are numbered by
`ZMod 6`; an assignment is therefore a bijection. -/
abbrev LabelledLinearArrangement := Equiv.Perm CyclicIndex

/-- A chemical arrangement on the oriented ring.  Fix one distinct group as
the anchor.  Reading clockwise from it leaves a bijection between five
remaining groups and five remaining positions. -/
abbrev HexadifferentiatedArrangement := Equiv.Perm (Fin 5)

/-! ## Derived counting lemmas -/

/-- Change the chosen starting site by the cyclic displacement `k`. -/
def rotateReading (k : CyclicIndex) (a : LabelledLinearArrangement) :
    LabelledLinearArrangement :=
  (Equiv.addRight k).trans a

@[simp]
theorem rotateReading_apply (k i : CyclicIndex)
    (a : LabelledLinearArrangement) :
    rotateReading k a i = a (i + k) := by
  rfl

/-- Because every functional group is distinct, no two rotations give the
same labelled reading. -/
theorem rotateReading_injective (a : LabelledLinearArrangement) :
    Function.Injective (fun k : CyclicIndex => rotateReading k a) := by
  intro k l hkl
  have h_at_zero : a ((0 : CyclicIndex) + k) = a (0 + l) := by
    simpa only [rotateReading_apply] using
      congrArg (fun e : LabelledLinearArrangement => e 0) hkl
  have h_index : (0 : CyclicIndex) + k = 0 + l := a.injective h_at_zero
  simpa using h_index

/-- Consequently every rotational class has exactly six labelled readings. -/
theorem rotationalReadings_count (a : LabelledLinearArrangement) :
    Fintype.card (Set.range (fun k : CyclicIndex => rotateReading k a)) = 6 := by
  rw [Set.card_range_of_injective (rotateReading_injective a), ZMod.card]

/-- There are `6! = 720` labelled linear readings before cyclic rotations are
identified. -/
theorem labelledLinearArrangement_count :
    Fintype.card LabelledLinearArrangement = 720 := by
  rw [Fintype.card_perm, ZMod.card]
  norm_num [Nat.factorial]

/-- There are six possible choices of the starting site when the same
oriented cyclic arrangement is written linearly. -/
theorem startingSite_count : Fintype.card PrimarySite = 6 := by
  exact Fintype.card_fin 6

/-- The elementary orbit calculation gives `6! / 6 = 120`.  Distinctness of
all six groups makes the rotational action free, which is equivalently
captured by anchoring one chosen group in `HexadifferentiatedArrangement`. -/
theorem cyclic_orbit_arithmetic :
    Fintype.card LabelledLinearArrangement / Fintype.card PrimarySite = 120 := by
  rw [labelledLinearArrangement_count, startingSite_count]

/-- General factorial count for the anchored representation: five distinct
groups can be put into five directionally ordered positions in `5!` ways. -/
theorem anchored_factorial_count :
    Fintype.card HexadifferentiatedArrangement = Nat.factorial 5 := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-- Requested output for T9-A9: the number of arrangements is exactly 120. -/
theorem arrangement_count :
    Fintype.card HexadifferentiatedArrangement = 120 := by
  rw [anchored_factorial_count]
  norm_num [Nat.factorial]

/-- The anchored count agrees with the explicit division of all linear
assignments by the six rotations of the alpha-CD ring. -/
theorem anchored_count_eq_cyclic_quotient :
    Fintype.card HexadifferentiatedArrangement =
      Fintype.card LabelledLinearArrangement / Fintype.card PrimarySite := by
  rw [arrangement_count, cyclic_orbit_arithmetic]

#print axioms labelledLinearArrangement_count
#print axioms rotateReading_injective
#print axioms rotationalReadings_count
#print axioms cyclic_orbit_arithmetic
#print axioms anchored_factorial_count
#print axioms arrangement_count
#print axioms anchored_count_eq_cyclic_quotient

end IChO2026Problems.T9A9
