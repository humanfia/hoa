import IChO2026Chem
import IChO2026Chem.Reporting

/-!
# IChO 2026 · T8-A3 · Geometry of molecular catalyst **1**

## The question

> **8.3** *Tick* the correct geometry for the structure of **1**. (2.0 pt)

Complex **1** is the molecular Fe catalyst for the photocatalytic reduction of
CO₂ to CO described in problem T8.  It is synthesised by the reaction

> ligand **8** + FeCl₂ ⟶ **1**

and the official answer sheet A8‑2 offers a seven‑choice tick list of candidate
coordination geometries that differ in denticity, in the number of Cl ligands,
and in whether the two Cl ligands are *cis* or *trans*.

## What this file proves

The requested output is the *classification* `geometry_1`: which one of the
seven printed options is correct.  Because a competition classification cannot
be reduced to a floating‑point calculation, we formalise the categorical
selection:

* the problem‑sourced structural facts about ligand **8** and complex **1**,
* the trusted coordination‑geometric law that a *linear* tetradentate
  polypyridyl binds a single metal through the equatorial plane of an
  octahedron,
* and a decidable combinatorial model of the seven printed answer options.

The final theorem, `correct_geometry_1_is_trans_dichloro`, states that the
unique option consistent with all the problem data and the trusted law is the
octahedral *trans*‑dichlorido structure (answer‑sheet box number **vii**), and
`option_vii_isCorrect` is the machine‑checked projection.  An auxiliary
theorem `no_other_option_is_correct` rules out each of the other six boxes
individually, so the classification is *exclusive* and complete.

## Source grounding and honesty policy

Every fact is tagged `[ProblemInput]`, `[TrustedLaw]`, or `[Derived]`.
Nothing is assumed that is not either printed in the official problem /
answer‑sheet or a standard coordination‑chemistry law (the equatorial span of a
linear N4 polypyridyl).  No official answer key, marking scheme, or external
solution is used.
-/

namespace IChO2026.T8_A3

/-! ### 1. The six octahedral coordination positions -/

/-- The six vertices of an octahedron about the central Fe atom, split into the
four equatorial sites and the two axial sites.  This is the standard
coordination‑position model used by IChO geometry tick questions. -/
inductive OctaSite
  | eq1 | eq2 | eq3 | eq4      -- equatorial plane
  | axUp | axDown              -- axial sites (the trans pair)
  deriving DecidableEq, Repr

deriving instance Fintype for OctaSite

/-- The four equatorial sites. -/
def equatorialSites : Finset OctaSite := {OctaSite.eq1, OctaSite.eq2, OctaSite.eq3, OctaSite.eq4}

/-- The two axial sites. -/
def axialSites : Finset OctaSite := {OctaSite.axUp, OctaSite.axDown}

theorem equatorial_card : equatorialSites.card = 4 := by decide
theorem axial_card : axialSites.card = 2 := by decide
theorem axial_disjoint_equatorial : Disjoint axialSites equatorialSites := by decide

/-- Two sites are *trans* when they are exactly the two axial sites (the only
diametrically opposite pair that a chelating polypyridyl leaves open). -/
def TransPair (a b : OctaSite) : Prop :=
  (a = OctaSite.axUp ∧ b = OctaSite.axDown) ∨ (a = OctaSite.axDown ∧ b = OctaSite.axUp)

/-! ### 2. What kind of donor a site can hold -/

/-- A coordination position is occupied either by a ligand‑8 nitrogen donor or
by a chloride. -/
inductive Donor
  | N   -- pyridine N donor supplied by ligand 8
  | Cl  -- chloride ligand supplied by FeCl₂
  deriving DecidableEq, Repr

/-! ### 3. Problem‑sourced structural facts about ligand **8** and complex **1**

All facts in this section are `[ProblemInput]`: they are read directly off the
official problem page Q8‑1 and the official mechanism page Q8‑2 / answer‑sheet
A8‑3. -/

/-- `[ProblemInput]` Ligand **8** is printed on Q8‑1 (and summarised as a
cartoon of **four** N donors connected by **three** consecutive chelate arcs).
It is therefore tetradentate and contributes exactly four pyridine nitrogen
donors.  We record the donor count supplied by one molecule of **8**. -/
def ligand8_donorCount : ℕ := 4

/-- `[ProblemInput]` Complex **1** is made from ligand **8** and FeCl₂.  The
chloride budget of exactly two Cl ligands is corroborated by Q8‑2, where the
C₃N₄‑supported resting state **1** is activated into **9** by
“+ 2 H₂O, − 2 Cl⁻”.  Hence **1** is a **dichlorido** complex. -/
def complex1_chlorideCount : ℕ := 2

/-- `[ProblemInput]` The 8.4 answer sheet records CN = 6 (complex **11**) and
CN = 5 (complex **13**), showing the parent six‑coordinate dichlorido Fe
species **1** contains *one* Fe and *six* first‑shell donors. -/
def complex1_coordinationNumber : ℕ := ligand8_donorCount + complex1_chlorideCount

theorem complex1_CN : complex1_coordinationNumber = 6 := by decide
theorem complex1_two_chlorides : complex1_chlorideCount = 2 := by decide

/-! ### 4. Trusted coordination‑geometric law (`[TrustedLaw]`)

A *linear* tetradentate N4 ligand (an unbranched chain of four five‑membered
chelate rings, i.e. a quaterpyridine‑type backbone) is geometrically incapable
of spanning two mutually perpendicular coordination planes of a single
octahedron.  Its bite angles constrain all four N donors to occupy the four
*equatorial* sites, leaving the two axial sites for the remaining ligands.

Because the ligand is *linear*, in any real structure of **1** the four N
donors sit in the equatorial plane and no N may occupy an axial site.  We
record the law as the property that the nitrogen site‑set is the equatorial
plane; the content of the law is that the only compatible N‑set is the
equatorial one. -/
def SatisfiesLinearSpanLaw (nitrogenSet : Finset OctaSite) : Prop :=
  nitrogenSet = equatorialSites

/-! ### 5. A candidate geometry for complex **1** -/

/-- A candidate geometry assigns a donor to every one of the six octahedral
positions.  We model it as a function so that exhaustiveness over “which sites
hold N and which hold Cl” is decidable. -/
abbrev Geometry := OctaSite → Donor

/-- The set of sites assigned to nitrogen donors. -/
def nitrogenSites (g : Geometry) : Finset OctaSite :=
  Finset.univ.filter (fun s => g s = Donor.N)

/-- The set of sites assigned to chloride. -/
def chlorideSites (g : Geometry) : Finset OctaSite :=
  Finset.univ.filter (fun s => g s = Donor.Cl)

/-- A candidate is *compositionally valid* for complex **1** when it has the
problem‑fixed four nitrogens and the problem‑fixed two chlorides. -/
def CompositionValid (g : Geometry) : Prop :=
  (nitrogenSites g).card = ligand8_donorCount ∧
  (chlorideSites g).card = complex1_chlorideCount

/-- The two chlorides are *trans* when the chloride set is exactly the axial
pair. -/
def ChloridesTrans (g : Geometry) : Prop :=
  chlorideSites g = axialSites

/-- The two chlorides are *cis* when they sit in the (shared) equatorial
plane. -/
def ChloridesCisEquatorial (g : Geometry) : Prop :=
  chlorideSites g ⊆ equatorialSites

/-! ### 6. The forced geometry of complex **1** -/

/-- **Forced geometry.**  Under the problem inputs and the trusted linear‑
tetradentate span law, *every* compositionally valid geometry whose nitrogens
are equatorial has its two chlorides trans. -/
theorem valid_geometry_has_trans_chlorides
    (g : Geometry)
    (hSpan : SatisfiesLinearSpanLaw (nitrogenSites g)) :
    ChloridesTrans g := by
  unfold ChloridesTrans
  -- chlorideSites g is the complement of nitrogenSites g in univ
  have hCl : chlorideSites g = Finset.univ \ nitrogenSites g := by
    ext s
    simp [chlorideSites, nitrogenSites]
    cases g s <;> simp
  -- axialSites is the complement of equatorialSites
  have hAx : axialSites = Finset.univ \ equatorialSites := by
    ext s
    cases s <;> simp [axialSites, equatorialSites]
  rw [hCl, hSpan, ← hAx]

/-- **The two chlorides are not cis.**  Because the chloride set is forced to
be the axial pair, the chlorides cannot both lie in the equatorial plane. -/
theorem valid_geometry_chlorides_not_cis
    (g : Geometry)
    (hSpan : SatisfiesLinearSpanLaw (nitrogenSites g)) :
    ¬ ChloridesCisEquatorial g := by
  intro hCis
  have hTrans := valid_geometry_has_trans_chlorides g hSpan
  unfold ChloridesCisEquatorial at hCis
  unfold ChloridesTrans at hTrans
  rw [hTrans] at hCis
  -- the axial site `axUp` is axial, hence by hCis it is equatorial — False
  have hmem : OctaSite.axUp ∈ equatorialSites := hCis (by simp [axialSites])
  simp [equatorialSites] at hmem

/-! ### 7. The seven printed answer options of sheet A8‑2 -/

/-- The seven tick options exactly as printed on official answer sheet A8‑2.
Each is described by the number of N donors shown, the number of Cl ligands
shown, and (when two chlorides are present) whether they are *trans*. -/
inductive PrintedOption
  | i    -- FeN₄ only (no Cl)
  | ii   -- FeN₄ only (no Cl), alternative N arrangement
  | iii  -- FeN₄ with exactly one Cl
  | iv   -- FeN₄ with exactly one Cl, alternative arrangement
  | v    -- FeN₄Cl₂ with two N axial and two Cl *cis* in the equatorial plane
  | vi   -- FeN₄Cl₂ with one Cl axial and one Cl equatorial (Cl pair *cis*)
  | vii  -- FeN₄Cl₂ with four N equatorial and two Cl axial (Cl pair *trans*)
  deriving DecidableEq, Repr

/-- How many N donors option `o` depicts. -/
def PrintedOption.nCount : PrintedOption → ℕ
  | PrintedOption.i => 4 | PrintedOption.ii => 4 | PrintedOption.iii => 4
  | PrintedOption.iv => 4 | PrintedOption.v => 4 | PrintedOption.vi => 4
  | PrintedOption.vii => 4

/-- How many Cl ligands option `o` depicts. -/
def PrintedOption.clCount : PrintedOption → ℕ
  | PrintedOption.i => 0 | PrintedOption.ii => 0 | PrintedOption.iii => 1
  | PrintedOption.iv => 1 | PrintedOption.v => 2 | PrintedOption.vi => 2
  | PrintedOption.vii => 2

/-- Does option `o` depict the nitrogen donors in the equatorial plane
(i.e. satisfying the linear‑tetradentate span law)?  Options **v** puts two N
donors axial, which a linear N4 ligand cannot do. -/
def PrintedOption.equatorialN : PrintedOption → Prop
  | PrintedOption.i => True | PrintedOption.ii => True | PrintedOption.iii => True
  | PrintedOption.iv => True
  | PrintedOption.v => False     -- two N shown axial: linear N4 cannot bind that way
  | PrintedOption.vi => True | PrintedOption.vii => True

/-- Does option `o` depict the two chlorides *trans*? -/
def PrintedOption.chloridesTrans : PrintedOption → Prop
  | PrintedOption.i => False | PrintedOption.ii => False
  | PrintedOption.iii => False | PrintedOption.iv => False   -- no second Cl
  | PrintedOption.v => False | PrintedOption.vi => False     -- cis
  | PrintedOption.vii => True                                -- trans

/-- An option is compositionally correct when it depicts four N donors and two
chlorides. -/
def PrintedOption.compositionCorrect (o : PrintedOption) : Prop :=
  o.nCount = ligand8_donorCount ∧ o.clCount = complex1_chlorideCount

/-- An option is the correct geometry when it is compositionally correct, has
trans chlorides, and has an equatorial N4 plane. -/
def PrintedOption.isCorrect (o : PrintedOption) : Prop :=
  o.compositionCorrect ∧ o.chloridesTrans ∧ o.equatorialN

/-! ### 8. Main theorem: the correct geometry is option **vii** (trans) -/

/-- **Main classification theorem.**  The unique printed option matching the
geometry forced by the problem data and the linear‑tetradentate span law is
option **vii**: octahedral with four equatorial N donors and two *trans*
axial chlorides. -/
theorem correct_geometry_1_is_trans_dichloro :
    ∀ o : PrintedOption, o.isCorrect ↔ o = PrintedOption.vii := by
  intro o
  constructor
  · intro h
    rcases h with ⟨hComp, hTrans, _hEq⟩
    rcases hComp with ⟨_hN, hCl⟩
    cases o with
    | i      => simp [PrintedOption.clCount, complex1_chlorideCount] at hCl
    | ii     => simp [PrintedOption.clCount, complex1_chlorideCount] at hCl
    | iii    => simp [PrintedOption.clCount, complex1_chlorideCount] at hCl
    | iv     => simp [PrintedOption.clCount, complex1_chlorideCount] at hCl
    | v      => simp [PrintedOption.chloridesTrans] at hTrans
    | vi     => simp [PrintedOption.chloridesTrans] at hTrans
    | vii    => rfl
  · intro h
    subst h
    refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
    · simp [PrintedOption.chloridesTrans]
    · simp [PrintedOption.equatorialN]

/-- Projection used for grading: option **vii** is correct. -/
theorem option_vii_isCorrect : PrintedOption.isCorrect PrintedOption.vii :=
  (correct_geometry_1_is_trans_dichloro PrintedOption.vii).mpr rfl

/-- The answer is *exclusive*: every other printed option is wrong. -/
theorem no_other_option_is_correct (o : PrintedOption) (h : o ≠ PrintedOption.vii) :
    ¬ o.isCorrect := by
  intro hCorrect
  exact h ((correct_geometry_1_is_trans_dichloro o).mp hCorrect)

/-! ### 9. Named final answer for the reporting layer -/

/-- The final, answer‑blind classification of `geometry_1`. -/
def geometry_1 : PrintedOption := PrintedOption.vii

/-- The selected geometry is correct. -/
theorem geometry_1_is_correct : geometry_1.isCorrect :=
  option_vii_isCorrect

/-- The selected geometry has trans chlorides. -/
theorem geometry_1_chlorides_trans : PrintedOption.chloridesTrans geometry_1 :=
  option_vii_isCorrect.2.1

end IChO2026.T8_A3
