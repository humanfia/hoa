import IChO2026Chem

/-!
# IChO 2026 T9.6: constitutional isomers of the β-CD dimer

The problem states that β-cyclodextrin has seven (cyclically ordered)
glucopyranoside units.  On the displayed synthesis, the first primary alcohol
is called unit 1 and directs the second primary debenzylation to unit 4.  Thus
the intermediate `L` has two free primary sites.  The following alkylation
uses one of them for the tether, while the product drawing shows the other as
`CH₂OH`.

The two ends joined by metathesis and hydrogenation are identical β-CD
fragments, so exchanging the ends does not give a new constitutional isomer.
Accordingly, a dimer is represented by an unordered pair (`Sym2`) of choices
of tether site.  No chemical premise is introduced as an axiom: the finite
candidate type below is the direct combinatorial model of the statement and
scheme, and its cardinality is proved from Mathlib's symmetric-square count.
-/

namespace IChO2026Problems.ProblemIcho2026T9A6

/-- A position on the cyclic ring of seven glucopyranoside units of β-CD. -/
abbrev BetaCDUnit := Fin 7

/-- The first primary alcohol in the problem's numbering (Lean uses index 0). -/
def unit1 : BetaCDUnit := 0

/-- The directed second primary alcohol, unit 4 (Lean uses index 3). -/
def unit4 : BetaCDUnit := 3

/-- The two free primary-alcohol sites of intermediate `L` that are visible in
the synthesis: the initial site and the site selected by 1 → 4 direction. -/
def lFreePrimarySites : Finset BetaCDUnit := {unit1, unit4}

theorem unit1_ne_unit4 : unit1 ≠ unit4 := by
  decide

/-- The directing rule really supplies two distinct candidate tether sites. -/
theorem lFreePrimarySites_card : lFreePrimarySites.card = 2 := by
  simp [lFreePrimarySites, unit1_ne_unit4]

/-- A monomer regioisomer is determined by which one of the two free primary
sites of `L` is converted to the alkenyl ether.  The other site remains OH. -/
abbrev MonomerRegioisomer := {u : BetaCDUnit // u ∈ lFreePrimarySites}

theorem monomer_regioisomer_count : Fintype.card MonomerRegioisomer = 2 := by
  simpa only [Fintype.card_coe] using lFreePrimarySites_card

/-- The saturated linker has two indistinguishable ends.  `Sym2` therefore
implements the chemically necessary identification `(a,b) = (b,a)`. -/
abbrev DimerConstitutionalIsomer := Sym2 MonomerRegioisomer

theorem exchanging_dimer_ends_does_not_create_an_isomer
    (a b : MonomerRegioisomer) :
    (s(a, b) : DimerConstitutionalIsomer) = s(b, a) := by
  exact Sym2.eq_swap

/-- Every dimer candidate is an unordered pair of the two possible monomer
regioisomers, so its three possibilities are AA, AB (= BA), and BB. -/
theorem dimer_isomer_count :
    Fintype.card DimerConstitutionalIsomer = 3 := by
  rw [Sym2.card, monomer_regioisomer_count]
  decide

end IChO2026Problems.ProblemIcho2026T9A6

#print axioms IChO2026Problems.ProblemIcho2026T9A6.lFreePrimarySites_card
#print axioms IChO2026Problems.ProblemIcho2026T9A6.monomer_regioisomer_count
#print axioms IChO2026Problems.ProblemIcho2026T9A6.exchanging_dimer_ends_does_not_create_an_isomer
#print axioms IChO2026Problems.ProblemIcho2026T9A6.dimer_isomer_count
