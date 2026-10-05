import Mathlib

/-!
# IChO 2026 T8-A3: geometry of catalyst 1

The problem drawing separates naturally into three kinds of information:

* `ProblemInput` records only what is read from the printed problem and its
  blank answer sheet: ligand 8 contains four pyridyl-N donor sites, aquation of
  1 releases two chloride ions, and the seven displayed choices have the
  profiles transcribed below.
* `CoordinationModel` records the standard octahedral model for a planar
  κ⁴-N₄ quaterpyridine complex.  Its four N donors fill the equatorial sites.
  The fact that the two remaining sites are opposite is then proved, rather
  than inserted into the answer-choice table as an unexplained answer.
* The final theorems compute the resulting profile and prove that exactly the
  bottom-right (seventh) box on answer sheet A8-2 has that profile.

No official solution or marking material is used.
-/

namespace IChO2026Problems.T8A3

/-- Named idealized coordination geometries appearing among the seven boxes. -/
inductive Geometry where
  | squarePlanar
  | tetrahedral
  | squarePyramidal
  | trigonalBipyramidal
  | octahedral
  deriving DecidableEq, Repr

/-- How the two chloride donors are related when two are present. -/
inductive ChlorideRelation where
  | notApplicable
  | single
  | cis
  | trans
  deriving DecidableEq, Repr

/-- The chemically relevant features by which the printed choices differ. -/
structure ChoiceProfile where
  geometry : Geometry
  coordinationNumber : ℕ
  nitrogenDonors : ℕ
  chlorideDonors : ℕ
  chlorideRelation : ChlorideRelation
  deriving DecidableEq, Repr

/-- The seven boxes of answer sheet A8-2, in reading order. -/
inductive AnswerChoice where
  | topLeft
  | topMiddle
  | topThird
  | topRight
  | bottomLeft
  | bottomMiddle
  | bottomRight
  deriving DecidableEq, Repr

namespace ProblemInput

/-!
These are transcriptions of the official problem, not conclusions of the
formal proof.

* Q8-1 (PDF page 72) draws four pyridine N atoms in ligand 8 and also supplies
  a four-N cartoon for that ligand.
* Q8-2 (PDF page 73) labels the conversion `1 + 2 H₂O ⟶ 9` with loss of
  `2 Cl⁻`, so structure 1 contains the two replaceable coordinated chlorides.
* A8-2 (PDF page 78) contains the seven structural choices.
-/

/-- The four N donor labels visible in the ligand-8 drawing. -/
inductive Ligand8Nitrogen where
  | n₁ | n₂ | n₃ | n₄
  deriving DecidableEq, Fintype, Repr

/-- Number of pyridyl-N donors supplied by one molecule of ligand 8. -/
def ligand8NitrogenDonorCount : ℕ := 4

/-- Number of coordinated chlorides displaced from 1 in the printed aquation
step on Q8-2. -/
def coordinatedChlorideCount : ℕ := 2

theorem ligand8_has_four_nitrogen_donors :
    ligand8NitrogenDonorCount = 4 := by
  rfl

theorem complex1_has_two_coordinated_chlorides :
    coordinatedChlorideCount = 2 := by
  rfl

/-- Profiles transcribed from the seven pictures on answer sheet A8-2.  The
last three are the three octahedral N₄Cl₂ arrangements shown on its bottom
row. -/
def choiceProfile : AnswerChoice → ChoiceProfile
  | .topLeft =>
      ⟨.tetrahedral, 4, 4, 0, .notApplicable⟩
  | .topMiddle =>
      ⟨.squarePlanar, 4, 4, 0, .notApplicable⟩
  | .topThird =>
      ⟨.squarePyramidal, 5, 4, 1, .single⟩
  | .topRight =>
      ⟨.trigonalBipyramidal, 5, 4, 1, .single⟩
  | .bottomLeft =>
      ⟨.octahedral, 6, 4, 2, .cis⟩
  | .bottomMiddle =>
      ⟨.octahedral, 6, 4, 2, .cis⟩
  | .bottomRight =>
      ⟨.octahedral, 6, 4, 2, .trans⟩

end ProblemInput

namespace CoordinationModel

/-!
We model an octahedral coordination sphere by the six signed Cartesian-axis
directions.  The planar κ⁴-N₄ binding mode of the conjugated quaterpyridine
ligand occupies the four equatorial directions; this is the standard
coordination-chemistry reading of the ligand drawing.  Everything about the
two residual sites below is a finite deduction from that model.
-/

/-- Six idealized sites of an octahedral coordination sphere. -/
inductive OctahedralSite where
  | xPlus | xMinus | yPlus | yMinus | zPlus | zMinus
  deriving DecidableEq, Fintype, Repr

/-- The site diametrically opposite a given octahedral site. -/
def opposite : OctahedralSite → OctahedralSite
  | .xPlus => .xMinus
  | .xMinus => .xPlus
  | .yPlus => .yMinus
  | .yMinus => .yPlus
  | .zPlus => .zMinus
  | .zMinus => .zPlus

/-- Two octahedral ligands are trans exactly when their sites are opposite. -/
abbrev SitesAreTrans (a b : OctahedralSite) : Prop := opposite a = b

/-- Sites occupied by the planar tetradentate ligand 8. -/
def ligand8Sites : Finset OctahedralSite :=
  {.xPlus, .xMinus, .yPlus, .yMinus}

/-- Sites not occupied by ligand 8, hence available to the two chlorides. -/
def residualSites : Finset OctahedralSite :=
  Finset.univ \ ligand8Sites

theorem ligand8_occupies_four_sites : ligand8Sites.card = 4 := by
  decide

/-- A κ⁴ equatorial ligand leaves precisely the two axial sites. -/
theorem residual_sites_are_axial :
    residualSites = {.zPlus, .zMinus} := by
  ext s
  cases s <;> simp [residualSites, ligand8Sites]

/-- Consequently the two sites available to chloride are a trans pair. -/
theorem ligand8_leaves_two_trans_sites :
    residualSites.card = 2 ∧ SitesAreTrans .zPlus .zMinus := by
  constructor
  · rw [residual_sites_are_axial]
    decide
  · rfl

/-- Relation read from a pair of residual octahedral sites. -/
def relationOfSites (a b : OctahedralSite) : ChlorideRelation :=
  if SitesAreTrans a b then .trans else .cis

theorem residual_chloride_relation :
    relationOfSites .zPlus .zMinus = .trans := by
  rfl

/-- Standard geometry assignment for the six-coordinate Fe-N₄Cl₂ sphere in
this problem.  The other branch makes the dependence on coordination number
explicit and is not used to classify any lower-coordinate species. -/
def geometryForComplex1 (coordinationNumber : ℕ) : Geometry :=
  if coordinationNumber = 6 then .octahedral else .tetrahedral

end CoordinationModel

open ProblemInput CoordinationModel

/-- Coordination number obtained from the donor count and chloride count
given by the problem drawings. -/
def complex1CoordinationNumber : ℕ :=
  ligand8NitrogenDonorCount + coordinatedChlorideCount

theorem complex1_coordination_number : complex1CoordinationNumber = 6 := by
  rfl

/-- The profile derived from the source data and the octahedral site model,
without referring to the position of any answer box. -/
def derivedComplex1Profile : ChoiceProfile where
  geometry := geometryForComplex1 complex1CoordinationNumber
  coordinationNumber := complex1CoordinationNumber
  nitrogenDonors := ligand8NitrogenDonorCount
  chlorideDonors := coordinatedChlorideCount
  chlorideRelation := relationOfSites .zPlus .zMinus

theorem derived_profile_of_complex1 :
    derivedComplex1Profile =
      ⟨.octahedral, 6, 4, 2, .trans⟩ := by
  rfl

/-- A printed box fits structure 1 when all chemically relevant fields agree
with the independently derived profile. -/
def FitsComplex1 (choice : AnswerChoice) : Prop :=
  choiceProfile choice = derivedComplex1Profile

theorem bottom_right_fits_complex1 : FitsComplex1 .bottomRight := by
  rfl

theorem fitting_choice_is_bottom_right
    (choice : AnswerChoice) (h : FitsComplex1 choice) :
    choice = .bottomRight := by
  cases choice <;>
    simp [FitsComplex1, choiceProfile, derivedComplex1Profile,
      complex1CoordinationNumber, ligand8NitrogenDonorCount,
      coordinatedChlorideCount, geometryForComplex1, relationOfSites,
      SitesAreTrans, opposite] at h ⊢

/-- Requested classification: a choice fits the source-grounded structure of
1 if and only if it is the bottom-right (seventh) choice. -/
theorem geometry_1 (choice : AnswerChoice) :
    FitsComplex1 choice ↔ choice = .bottomRight := by
  constructor
  · exact fitting_choice_is_bottom_right choice
  · intro h
    subst choice
    exact bottom_right_fits_complex1

/-- Existence and uniqueness form of the requested tick-box answer. -/
theorem geometry_1_unique : ∃! choice : AnswerChoice, FitsComplex1 choice := by
  refine ⟨.bottomRight, bottom_right_fits_complex1, ?_⟩
  intro choice h
  exact fitting_choice_is_bottom_right choice h

#print axioms ligand8_leaves_two_trans_sites
#print axioms derived_profile_of_complex1
#print axioms geometry_1
#print axioms geometry_1_unique

end IChO2026Problems.T8A3
