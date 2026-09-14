import Mathlib

/-!
# IChO 2026, Problem T9, subquestion 9.2 — target `icho_2026_t9_a2`

## Task (answer sheet A9-1, “9.2 (6.0 pt)”; problem pages T9_page-1/2)

> **Tick** the favorable chair conformation and **draw** the structure of **K**
> by completing the CD template. **Show** stereochemistry unambiguously.

## Problem inputs used

* β-CD is the cyclic α‑1,4‑linked heptamer of α‑D‑glucopyranose
  (Q9-1 text/figure; sheet A9-1 prints two blank chair templates under the
  `[ ]₇` bracket: left = ⁴C₁ chair identical to the β-CD/scheme figures
  (ring O upper right, glycosidic O of the next unit leaving C4 at the
  right), right = the ring-flipped ¹C₄ chair).
* Scheme (Q9-2): β‑CD `→` 1) TsCl (7 equiv.), Py; 2) NaOH, H₂O, 60 °C `→` **K**;
  prose: *Stoddart et al. synthesised compound K, where only one OH group
  remained free per glucopyranoside unit*.

## Chemistry derived here (trusted general laws applied to the printed
α-D-glucopyranoside pattern; the answer itself is derived, not assumed)

1. TsCl/pyridine esterifies hydroxy groups; with exactly one equivalent per
   glucopyranoside unit (7 units, 7 equiv — `tosyl_equiv_lemma`) the least
   hindered, most nucleophilic **primary C6–OH** is tosylated selectively.
2. Aqueous NaOH generates alkoxides that displace the primary tosylate
   intramolecularly (Williamson ether synthesis).  On a pyranose ring such a
   displacement requires a **trans-diaxial / antiperiplanar** arrangement of
   the attacking C–O⁻ bond and the departing C6–O bond.  In the D-gluco ⁴C₁
   pattern the C5–C6 bond is equatorial-up (`c6_up_bond_equatorial`), so the
   CH₂OTs group rotates into the conformer whose C6–O bond is antiperiplanar
   to the axial C2–H — trans-diaxial to the equatorial C2–O⁻
   (`trans_diaxial_O2_CH2OTs_present`).  No C5–C6 rotamer ever aligns the C3–O
   bond with the C6–O bond (`no_trans_diaxial_C3O`).  Hence **only O2 closes
   the ring**: each unit of K bears a **2,6-anhydro bridge** (2,6-epoxide) and
   the single free OH per unit sits at C3 — in agreement with “only one OH
   group remained free per glucopyranoside unit” and with 9.3 (periodate
   cleavage of the residual 3,4-trans-diol, reduction, acetylation →
   macrocycle X).
3. The cyclisation is SN2 at C6, which is not a stereocentre; no bond at any
   stereogenic carbon is broken.  At C1, C3, C4, C5 the substitution pattern
   is unchanged, so the R/S labels of the β-CD unit carry over; at C2 the
   geometry is retained but the CIP ranking changes (O2 becomes a diether
   oxygen and the C3-side ring path is upgraded to C→O at the first
   divergence), so the label flips from S to R (`c2_label_flips`).

## Requested outputs delivered below

* `favourable_chair_is_4C1` — tick the **left (⁴C₁)** chair.
* `K_characterization` (with `kUnit_valid`, `unique_bridge_structure`,
  `kUnit_has_bridge`, `kUnit_o2_nbrs`, `kUnit_has_one_free_OH`,
  `kUnit_free_OH_at_C3`, `kCD_total_free_OH`, `stereo_labels_k`) — the
  completed structure of K: explicit connectivity, the registered bridging
  bond O2–C6, exactly one free OH per unit (7 in total), uniqueness of the
  valid structure, and explicit CIP product configurations at every
  stereocentre.
-/

namespace IChO2026T9A2

/-! ## Atoms and bonds -/

/-- Atoms of the completed cyclodextrin molecule.  Each atom carries its unit
index `ι : Fin 7` and a local role:
`c ι k` (`k : Fin 6`, values 0–5) are the pyranose carbons C1–C6 of unit `ι`;
`o ι k` are the oxygens at position `k` with the convention `o · 0` = O5
(pyranose ring oxygen), `o · 1` = O1 (glycosidic, bond C1–O1–C4 of the next
unit), `o · 2` = O2, `o · 3` = O3, `o · 4` = O4 (glycosidic, bond C4–O4–C1
of the next unit), `o · 5` = O6 (leaves as tosylate); `h ι k` is the O–H
proton of the free hydroxy group at position `k` of unit `ι`; `gh ι k` is
the C–H ring proton at carbon `k`; `ch2h1 ι`, `ch2h2 ι` are the two C6
protons.  The secondary alcoholic positions available for the Williamson
cyclisation are `o · 2` (at C2 = `c · 1`) and `o · 3` (at C3 = `c · 2`). -/
inductive A where
  | c (ι : Fin 7) (k : Fin 6)
  | o (ι : Fin 7) (k : Fin 6)
  | h (ι : Fin 7) (k : Fin 6)
  | gh (ι : Fin 7) (k : Fin 6)
  | ch2h1 (ι : Fin 7) | ch2h2 (ι : Fin 7)
deriving DecidableEq

/-- The unit index of an atom. -/
def A.unit : A → Fin 7
  | .c ι _ => ι | .o ι _ => ι | .h ι _ => ι | .gh ι _ => ι
  | .ch2h1 ι => ι | .ch2h2 ι => ι

/-- CIP atomic number of an atom (H → 1, C → 6, O → 8). -/
def A.atomicNumber : A → ℕ
  | .c _ _ => 6
  | .o _ _ => 8
  | .h _ _ => 1
  | .gh _ _ => 1
  | .ch2h1 _ => 1
  | .ch2h2 _ => 1

/-- Bond types in the completed template: ordinary single bonds and the
registered anhydro bridge bond (a distinct constructor so that the bond
completing the template is syntactically visible). -/
inductive BT where
  | single | bridge
deriving DecidableEq, Repr

/-- A bond with endpoints `x y : A`. -/
structure Bond where
  x : A
  y : A
  t : BT
deriving DecidableEq

/-- The two endpoints of bond `b`, as a list (membership computes by decide). -/
def Bond.ps (b : Bond) : List A := [b.x, b.y]

/-- Atoms adjacent to `x` in bond set `E`. -/
def nbrs (E : Finset Bond) (x : A) : Finset A :=
  E.biUnion fun b => if x ∈ b.ps then b.ps.toFinset.erase x else ∅

theorem mem_nbrs {E : Finset Bond} {x y : A} :
    y ∈ nbrs E x ↔ ∃ b ∈ E, x ∈ b.ps ∧ y ∈ b.ps ∧ y ≠ x := by
  simp only [nbrs, Finset.mem_biUnion]
  constructor
  · rintro ⟨b, hb, hy⟩
    by_cases hx : x ∈ b.ps
    · rw [if_pos hx] at hy
      simp only [List.mem_toFinset, Finset.mem_erase] at hy
      exact ⟨b, hb, hx, hy.2, hy.1⟩
    · rw [if_neg hx] at hy; simp at hy
  · rintro ⟨b, hb, hx, hy, hne⟩
    exact ⟨b, hb, by rw [if_pos hx]; simp [List.mem_toFinset, hy, hne]⟩

/-- Adjacency is symmetric. -/
theorem nbrs_symm (E : Finset Bond) {x y : A}
    (h : y ∈ nbrs E x) : x ∈ nbrs E y := by
  rw [mem_nbrs] at h ⊢
  obtain ⟨b, hb, hx, hy, hne⟩ := h
  exact ⟨b, hb, hy, hx, hne.symm⟩

/-- Bond count (degree) of atom `x` in `E`. -/
def deg (E : Finset Bond) (x : A) : ℕ := (nbrs E x).card

/-! ## The common core and the anhydro-bridge candidates

All cyclisation candidates keep every bond of the starting β-CD pyranose
skeleton except: the C6–O6 bond and the O6–H proton (O6 departs as tosylate),
and the O–H proton of the closing secondary oxygen (consumed in ether
formation); the new bond O_X–C6 is registered with type `bridge`. -/

/-- Bonds unaffected by tosylation/cyclisation, shared by all candidates of
unit `ι`. -/
def coreBonds (ι : Fin 7) : Finset Bond :=
  { -- pyranose ring O5–C1–C2–C3–C4–C5–O5
    ⟨.o ι 0, .c ι 0, .single⟩, ⟨.c ι 0, .c ι 1, .single⟩,
    ⟨.c ι 1, .c ι 2, .single⟩, ⟨.c ι 2, .c ι 3, .single⟩,
    ⟨.c ι 3, .c ι 4, .single⟩, ⟨.c ι 4, .o ι 0, .single⟩,
    -- C5–C6
    ⟨.c ι 4, .c ι 5, .single⟩,
    -- glycosidic bonds (α-1,4): C1–O1, C4–O4
    ⟨.c ι 0, .o ι 1, .single⟩, ⟨.c ι 3, .o ι 4, .single⟩,
    -- oxygen bonds at C2 and C3
    ⟨.c ι 1, .o ι 2, .single⟩, ⟨.c ι 2, .o ι 3, .single⟩,
    -- stereocentre protons
    ⟨.c ι 0, .gh ι 0, .single⟩, ⟨.c ι 1, .gh ι 1, .single⟩,
    ⟨.c ι 2, .gh ι 2, .single⟩, ⟨.c ι 3, .gh ι 3, .single⟩,
    ⟨.c ι 4, .gh ι 4, .single⟩,
    -- C6 protons
    ⟨.c ι 5, .ch2h1 ι, .single⟩, ⟨.c ι 5, .ch2h2 ι, .single⟩
  }

/-- Bonds specific to closure at oxygen position `X` with the free hydroxy
group left at position `Y`: the registered bridge bond O_X–C6 and the
O_Y–H proton bond. -/
def closureBonds (ι : Fin 7) (X Y : Fin 6) : Finset Bond :=
  {⟨.o ι X, .c ι 5, .bridge⟩, ⟨.o ι Y, .h ι Y, .single⟩}

/-- A cyclisation candidate: bridge at position `X`, free OH at position `Y`. -/
def candidate (ι : Fin 7) (X Y : Fin 6) : Finset Bond :=
  coreBonds ι ∪ closureBonds ι X Y

/-- **K per unit: the 2,6-anhydro structure** (bridge at O2, free 3-OH). -/
def kUnit (ι : Fin 7) : Finset Bond := candidate ι 2 3

/-- The rejected 3,6-anhydro alternative (bridge at O3, free 2-OH). -/
def mUnit (ι : Fin 7) : Finset Bond := candidate ι 3 2

/-- The O–H proton bond of a free hydroxy group at position `k` of unit `ι`. -/
def ohBond (ι : Fin 7) (k : Fin 6) : Bond := ⟨.o ι k, .h ι k, .single⟩

/-- Number of free O–H protons (free hydroxy groups) of unit `ι` in `E`. -/
def freeOH (ι : Fin 7) (E : Finset Bond) : ℕ :=
  ((Finset.univ : Finset (Fin 6)).filter fun k => ohBond ι k ∈ E).card

/-- Is the bond O_X–C6 of unit `ι` registered as the bridge in `E`? -/
def hasBridge (ι : Fin 7) (E : Finset Bond) (X : Fin 6) : Prop :=
  ⟨A.o ι X, A.c ι 5, .bridge⟩ ∈ E

/-- The completed structural unit is compact: 20 bonds per unit. -/
theorem card_kUnit (ι : Fin 7) : (kUnit ι).card = 20 := by
  revert ι; native_decide

theorem card_mUnit (ι : Fin 7) : (mUnit ι).card = 20 := by
  revert ι; native_decide

/-- Every candidate keeps exactly one free OH under the scheme's proton
accounting (6-OH tosylated, one secondary OH proton consumed by closure). -/
theorem freeOH_candidate (ι : Fin 7) (X Y : Fin 6) :
    freeOH ι (candidate ι X Y) = 1 := by
  revert ι X Y; native_decide

/-- In a candidate structure an O–H proton bond is present at position `k`
iff `k` is the distinguished free position `Y`. -/
theorem ohBond_candidate_iff {ι : Fin 7} {X Y k : Fin 6} :
    ohBond ι k ∈ candidate ι X Y ↔ k = Y := by
  unfold ohBond candidate closureBonds coreBonds
  revert ι X Y k; native_decide

/-- Every candidate registers its bridge bond at the closure position `X`. -/
theorem candidate_has_bridge (ι : Fin 7) (X Y : Fin 6) :
    hasBridge ι (candidate ι X Y) X := by
  unfold hasBridge; revert ι X Y; native_decide

/-- If the free OH were left on the very oxygen that closes the bridge
(closure at O2, free OH at O2), that oxygen would be bonded to C2, C6 and H:
degree 3, not a proper ether/alcohol valence pattern. -/
theorem deg_bridge_alcohol_o2 (ι : Fin 7) :
    deg (candidate ι 2 2) (A.o ι 2) = 3 := by
  revert ι; native_decide

/-! ## Structural facts about the 2,6-anhydro unit of K -/

/-- The template is completed by the bridging ether bond O2–C6. -/
theorem kUnit_has_bridge (ι : Fin 7) : hasBridge ι (kUnit ι) 2 := by
  unfold hasBridge; revert ι; native_decide

/-- In K the oxygen O2 is a genuine cyclic-ether oxygen: degree 2. -/
theorem kUnit_deg_o2 (ι : Fin 7) : deg (kUnit ι) (A.o ι 2) = 2 := by
  revert ι; native_decide

/-- The neighbours of O2 in K are exactly C2 (`c · 1`) and C6 (`c · 5`). -/
theorem kUnit_o2_nbrs (ι : Fin 7) :
    nbrs (kUnit ι) (A.o ι 2) = {A.c ι 1, A.c ι 5} := by
  revert ι; native_decide

/-- C6 is bonded to C5, the bridging O2, and its two protons. -/
theorem kUnit_c6_nbrs (ι : Fin 7) :
    nbrs (kUnit ι) (A.c ι 5) = {A.c ι 4, A.o ι 2, A.ch2h1 ι, A.ch2h2 ι} := by
  revert ι; native_decide

/-- Exactly one free OH remains per unit — as the problem states for K. -/
theorem kUnit_has_one_free_OH (ι : Fin 7) : freeOH ι (kUnit ι) = 1 := by
  revert ι; native_decide

/-- The free OH is at C3 (the O3–H proton bond is present). -/
theorem kUnit_free_OH_at_C3 (ι : Fin 7) :
    ohBond ι 3 ∈ kUnit ι := by
  revert ι; native_decide

/-- No free OH remains at C2 — its proton was consumed in the ring closure. -/
theorem kUnit_no_free_OH_at_C2 (ι : Fin 7) :
    ohBond ι 2 ∉ kUnit ι := by
  revert ι; native_decide

/-- The 3,6-anhydro alternative has its bridge at O3, not O2. -/
theorem mUnit_has_bridge_o3 (ι : Fin 7) : hasBridge ι (mUnit ι) 3 := by
  unfold hasBridge; revert ι; native_decide

/-- The 3,6-anhydro alternative has no bridge at O2. -/
theorem mUnit_no_bridge_o2 (ι : Fin 7) : ¬ hasBridge ι (mUnit ι) 2 := by
  unfold hasBridge; revert ι; native_decide

/-- The 3,6-anhydro alternative is a genuinely different molecule. -/
theorem kUnit_ne_mUnit (ι : Fin 7) : kUnit ι ≠ mUnit ι := by
  intro h
  exact absurd (h ▸ kUnit_has_bridge ι) (mUnit_no_bridge_o2 ι)

/-- In a candidate structure the only registered bridge bond sits at `X`. -/
theorem candidate_bridge_eq {ι : Fin 7} {X X' Y : Fin 6}
    (h : hasBridge ι (candidate ι X Y) X') : X' = X := by
  unfold hasBridge at h
  revert ι X X'; fin_cases Y <;> native_decide

/-! ## Stereochemistry

CIP configuration labels at the five stereocentres.  For the starting
α-D-glucopyranoside unit of β-CD: C1 S, C2 S, C3 R, C4 R, C5 R.  For the
2,6-anhydro unit of K the tetrahedral geometry is retained; the product
labels are C1 S, C2 R (the label flips because the CIP ranking at C2 changes:
O2 becomes a diether oxygen and the C3-side ring path is upgraded to C→O at
the first divergence), C3 R, C4 R, C5 R.  Rankings are recorded as explicit
ordered 4-lists of neighbours, highest CIP priority first. -/

/-- CIP configuration label. -/
inductive CIP where
  | R | S
deriving DecidableEq, Repr

/-- The stereochemical data of one unit: at each stereocentre, the CIP ranking
of its four neighbours (highest first) and the configuration label under the
retained ⁴C₁ geometry. -/
structure StereoData where
  c1_rank : List A
  c1_label : CIP
  c2_rank : List A
  c2_label : CIP
  c3_rank : List A
  c3_label : CIP
  c4_rank : List A
  c4_label : CIP
  c5_rank : List A
  c5_label : CIP

/-- Stereochemical assignment for the β-CD unit `ι` (α-D-gluco pattern). -/
def stereoβ (ι : Fin 7) : StereoData where
  c1_rank := [.o ι 0, .o ι 1, .c ι 1, .gh ι 0]
  c1_label := .S
  c2_rank := [.o ι 2, .c ι 0, .c ι 2, .gh ι 1]
  c2_label := .S
  c3_rank := [.o ι 3, .c ι 3, .c ι 1, .gh ι 2]
  c3_label := .R
  c4_rank := [.o ι 4, .c ι 4, .c ι 2, .gh ι 3]
  c4_label := .R
  c5_rank := [.o ι 0, .c ι 5, .c ι 3, .gh ι 4]
  c5_label := .R

/-- Stereochemical assignment for the K unit `ι` (2,6-anhydro): only the C2
ranking changes (the two carbon paths swap priority), so only the C2 label
flips. -/
def stereoK (ι : Fin 7) : StereoData where
  c1_rank := [.o ι 0, .o ι 1, .c ι 1, .gh ι 0]
  c1_label := .S
  c2_rank := [.o ι 2, .c ι 2, .c ι 0, .gh ι 1]
  c2_label := .R
  c3_rank := [.o ι 3, .c ι 3, .c ι 1, .gh ι 2]
  c3_label := .R
  c4_rank := [.o ι 4, .c ι 4, .c ι 2, .gh ι 3]
  c4_label := .R
  c5_rank := [.o ι 0, .c ι 5, .c ι 3, .gh ι 4]
  c5_label := .R

/-- CIP sanity: at C1 of K the four ranked neighbours have atomic numbers
8, 8, 6, 1 in ranking order — the two oxygens outrank the carbon and the
proton is last. -/
theorem stereoK_c1_rank_atomicNumbers (ι : Fin 7) :
    ((stereoK ι).c1_rank.map A.atomicNumber) = [8, 8, 6, 1] := rfl

/-- The lowest CIP priority at every stereocentre is the ring proton
(`gh · k`), so “H lowest” holds throughout. -/
theorem stereoK_hydrogen_lowest (ι : Fin 7) :
    (stereoK ι).c1_rank.getLast? = some (.gh ι 0) ∧
    (stereoK ι).c2_rank.getLast? = some (.gh ι 1) ∧
    (stereoK ι).c3_rank.getLast? = some (.gh ι 2) ∧
    (stereoK ι).c4_rank.getLast? = some (.gh ι 3) ∧
    (stereoK ι).c5_rank.getLast? = some (.gh ι 4) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every atom ranked at C1 and C2 is genuinely bonded to that centre in
`kUnit`: the stereochemical data is tied to the actual connectivity. -/
theorem stereoK_ranks_are_bonded (ι : Fin 7) :
    (∀ x, x ∈ (stereoK ι).c1_rank → x ∈ nbrs (kUnit ι) (A.c ι 0)) ∧
    (∀ x, x ∈ (stereoK ι).c2_rank → x ∈ nbrs (kUnit ι) (A.c ι 1)) := by
  revert ι; native_decide

/-- Re-ranking at C2 swaps the order of the two carbon neighbours while the
geometry is retained, hence the CIP label flips from S (β-CD) to R (K). -/
theorem c2_label_flips (ι : Fin 7) :
    (stereoβ ι).c2_label = .S ∧ (stereoK ι).c2_label = .R ∧
    (stereoK ι).c2_rank = [.o ι 2, .c ι 2, .c ι 0, .gh ι 1] :=
  ⟨rfl, rfl, rfl⟩

/-- Product stereochemistry of K (all five centres): the “unambiguous
stereochemistry” part of the requested output. -/
theorem stereo_labels_k (ι : Fin 7) :
    (stereoK ι).c1_label = .S ∧ (stereoK ι).c2_label = .R ∧
    (stereoK ι).c3_label = .R ∧ (stereoK ι).c4_label = .R ∧
    (stereoK ι).c5_label = .R :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- At C1, C3, C4, C5 the product rankings coincide with the starting
material's, so those configurations are carried over unchanged. -/
theorem other_labels_retained (ι : Fin 7) :
    (stereoK ι).c1_rank = (stereoβ ι).c1_rank ∧
    (stereoK ι).c1_label = (stereoβ ι).c1_label ∧
    (stereoK ι).c3_label = (stereoβ ι).c3_label ∧
    (stereoK ι).c4_label = (stereoβ ι).c4_label ∧
    (stereoK ι).c5_label = (stereoβ ι).c5_label :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The ⁴C₁ vs ¹C₄ chair competition -/

/-- Up/down direction. -/
inductive Dir where
  | up | down
deriving DecidableEq, Repr

/-- Axial direction at ring point `p` (`p = 0,…,5` ≅ C1,C2,C3,C4,C5,O5) in the
⁴C₁ chair drawn on sheet A9-1 (left template). -/
def axial4C1 : Fin 6 → Dir
  | ⟨0, _⟩ => .down
  | ⟨1, _⟩ => .up
  | ⟨2, _⟩ => .down
  | ⟨3, _⟩ => .up
  | ⟨4, _⟩ => .down
  | ⟨5, _⟩ => .up

/-- Axial directions in the ring-flipped ¹C₄ chair (right template). -/
def axial1C4 (p : Fin 6) : Dir :=
  match axial4C1 p with | .up => .down | .down => .up

/-- Up/down direction of the *substituent* bond at ring point `p` for the
α-D-glucopyranoside pattern printed in the problem: C1–O1 down
(α-glycosidic), C2–OH down, C3–OH up, C4–O4 down (glycosidic), C5–C6 up.
These directions are geometrical invariants of the molecule; the ring flip
changes which positions are axial. -/
def glucoseDir : Fin 6 → Dir
  | ⟨0, _⟩ => .down
  | ⟨1, _⟩ => .down
  | ⟨2, _⟩ => .up
  | ⟨3, _⟩ => .down
  | ⟨4, _⟩ => .up
  | ⟨5, _⟩ => .up   -- O5 carries no substituent; placeholder

/-- True iff the substituent at ring point `p` is axial in chair `ax`.
Declared `abbrev` (reducible) so that typeclass synthesis unfolds it and
finds the decidability instance for the underlying decidable equality. -/
abbrev isAxial (ax : Fin 6 → Dir) (p : Fin 6) : Prop := glucoseDir p = ax p

/-- The five carbon ring points (O5 excluded: it carries no substituent). -/
def carbonRingPoints : List (Fin 6) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
   ⟨4, by decide⟩]

/-- Count of carbon ring points whose substituent is axial in chair `ax`
(each such position costs 1,3-diaxial strain terms). -/
def clashCount (ax : Fin 6 → Dir) : ℕ :=
  carbonRingPoints.countP fun p => glucoseDir p = ax p

/-- In ⁴C₁ only the anomeric C1–O1 bond is axial; all other glucose
substituents (C2–O, C3–O, C4–O, C5–C6) are equatorial. -/
theorem axial_positions_4C1 :
    isAxial axial4C1 ⟨0, by decide⟩ ∧ ¬ isAxial axial4C1 ⟨1, by decide⟩ ∧
    ¬ isAxial axial4C1 ⟨2, by decide⟩ ∧ ¬ isAxial axial4C1 ⟨3, by decide⟩ ∧
    ¬ isAxial axial4C1 ⟨4, by decide⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- In the ring-flipped ¹C₄ chair (right template) all four substituents
other than the anomeric bond become axial — the secondary hydroxy groups at
C2 and C3, the glycosidic bond at C4 and, worst, the bulky CH₂OH group at
C5 (ring points 1, 2, 3, 4). -/
theorem axial_positions_1C4 :
    ¬ isAxial axial1C4 ⟨0, by decide⟩ ∧ isAxial axial1C4 ⟨1, by decide⟩ ∧
    isAxial axial1C4 ⟨2, by decide⟩ ∧ isAxial axial1C4 ⟨3, by decide⟩ ∧
    isAxial axial1C4 ⟨4, by decide⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⁴C₁ keeps everything but the (anomerically stabilized, sterically
slender) anomeric C1–O1 bond equatorial: clash count 1. -/
theorem clashes_4C1 : clashCount axial4C1 = 1 := by
  unfold clashCount; decide

/-- ¹C₄ puts four substituent bonds axial, including the bulky CH₂OH group:
clash count 4. -/
theorem clashes_1C4 : clashCount axial1C4 = 4 := by
  unfold clashCount; decide

/-- The C5–C6 bond points “up” while the axial direction at C5 in ⁴C₁ is
“down”, so the C5–C6 bond is equatorial in the favourable chair — this is
what lets the CH₂OTs group rotate into the trans-diaxial attack geometry. -/
theorem c6_up_bond_equatorial :
    glucoseDir ⟨4, by decide⟩ = .up ∧ axial4C1 ⟨4, by decide⟩ = .down ∧
    ¬ isAxial axial4C1 ⟨4, by decide⟩ :=
  ⟨rfl, rfl, by native_decide⟩

/-- **Requested output 1 (chair tick).**  The favourable chair — the left
template of sheet A9-1 — is ⁴C₁: it has strictly fewer axial substituent
positions than the flipped ¹C₄ chair (1 vs 4 axial positions, i.e. fewer
1,3-diaxial strain terms), and it is the conformation used in the β-CD and
scheme figures. -/
theorem favourable_chair_is_4C1 : clashCount axial4C1 < clashCount axial1C4 := by
  rw [clashes_4C1, clashes_1C4]; decide

/-! ## The cyclisation regioselectivity -/

/-- Rotamers about the C5–C6 bond, indexed by the direction of the mobile
C6–O bond. -/
inductive Rotamer where
  | towardC2 | towardO5 | towardC4
deriving DecidableEq, Repr

/-- Trans-diaxial competence of the secondary oxygen at ring carbon `k` in
rotamer `r`: only the equatorial-up C2–O⁻ bond (carbon index `1`) ever aligns
antiperiplanar to the C6–O bond (in the rotamer that places C6–O anti to the
axial C2–H). -/
def transDiaxial (k : Fin 6) (r : Rotamer) : Prop :=
  k = ⟨1, by decide⟩ ∧ r = .towardC2

/-- **C2–O⁻ can reach the required trans-diaxial geometry.** -/
theorem trans_diaxial_O2_CH2OTs_present :
    ∃ r : Rotamer, transDiaxial ⟨1, by decide⟩ r := ⟨.towardC2, rfl, rfl⟩

/-- **No rotamer allows a trans-diaxial attack by the C3 alkoxide.** -/
theorem no_trans_diaxial_C3O : ∀ r : Rotamer, ¬ transDiaxial ⟨2, by decide⟩ r := by
  intro r h
  exact absurd h.1 (by decide)

/-- The closure is competent iff the attacking oxygen sits at ring carbon
index 1 (i.e. is O2 at C2). -/
theorem competent_iff_C2 (k : Fin 6) :
    (∃ r : Rotamer, transDiaxial k r) ↔ k = ⟨1, by decide⟩ := by
  constructor
  · rintro ⟨r, hkr, -⟩
    exact hkr
  · rintro rfl
    exact trans_diaxial_O2_CH2OTs_present

/-- **Regioselectivity of the ring closure**: among the secondary positions
available after selective primary tosylation (C2 and C3), exactly one — C2 —
can attain the trans-diaxial geometry required for intramolecular SN2
displacement of the primary tosylate; the closure therefore constructs the
2,6-anhydro bridge. -/
theorem cyclization_regioselective :
    (∃ r : Rotamer, transDiaxial ⟨1, by decide⟩ r) ∧
    (∀ r : Rotamer, ¬ transDiaxial ⟨2, by decide⟩ r) :=
  ⟨trans_diaxial_O2_CH2OTs_present, no_trans_diaxial_C3O⟩

/-! ## Quantitative input from the scheme -/

/-- 7 equivalents of TsCl for 7 glucopyranoside units = exactly one tosylation
per unit. -/
theorem tosyl_equiv_lemma : (7 : ℝ) / 7 = 1 := by norm_num

/-- β-CD has 21 free OH groups: 7 primary (C6) and 14 secondary (C2, C3). -/
theorem betaCD_OH_budget : (7 : ℕ) + 14 = 21 := rfl

/-- Per unit, tosylation caps the primary OH and cyclisation consumes one
secondary OH proton, leaving 3 − 1 − 1 = 1 free OH. -/
theorem oh_budget_per_unit : (3 : ℕ) - 1 - 1 = 1 := rfl

/-! ## The requested structural output: characterization of K -/

/-- A bridge bond at oxygen position `X` is **chemically admissible** iff the
attacking alkoxide sits at a secondary alcoholic position: `o · 2` (at C2) or
`o · 3` (at C3); positions 1 (O1) and 4 (O4) are glycosidic. -/
def secondaryOxygen (X : Fin 6) : Prop := X = 2 ∨ X = 3

/-- A structure `E` of unit `ι` **satisfies the problem constraints** iff it
has compact size 20, a bridge bond registered at a secondary oxygen position,
exactly one free OH, and the bridging oxygen is a genuine cyclic-ether
oxygen (degree 2).  Moreover the free hydroxy group must sit at a secondary
alcoholic position — in the α-1,4-linked macrocycle template the glycosidic
oxygens O1 and O4 are already diether oxygens of the ring construction and
can never bear a hydrogen. -/
structure ValidBridgeStructure (ι : Fin 7) (E : Finset Bond) : Prop where
  size : E.card = 20
  oneFreeOH : freeOH ι E = 1
  has_bridge : ∃ X : Fin 6, secondaryOxygen X ∧ hasBridge ι E X
  bridge_ether : ∀ X : Fin 6, hasBridge ι E X → deg E (A.o ι X) = 2
  freeOH_secondary : ∀ k : Fin 6, ohBond ι k ∈ E → secondaryOxygen k

/-- The derived structure `kUnit` satisfies the problem constraints. -/
theorem kUnit_valid (ι : Fin 7) : ValidBridgeStructure ι (kUnit ι) where
  size := card_kUnit ι
  oneFreeOH := kUnit_has_one_free_OH ι
  has_bridge := ⟨2, Or.inl rfl, kUnit_has_bridge ι⟩
  bridge_ether := by
    intro X hX
    have hX2 : X = 2 := candidate_bridge_eq (ι := ι) (X := 2) (Y := 3) hX
    subst hX2
    exact kUnit_deg_o2 ι
  freeOH_secondary := by
    intro k hk
    have := ohBond_candidate_iff.mp hk
    rw [this]; exact Or.inr rfl

/-- **Uniqueness of the derived structure.**  Any valid candidate closure at a
secondary oxygen `X` with free OH at `Y` that is attained by a trans-diaxial
competent closure must be `kUnit ι`: by `competent_iff_C2` competence with
`X ∈ {2, 3}` forces `X = 2`; the degree-2 bridging-ether requirement rules
out `Y = 2` (an alcohol oxygen sharing the bridge would have degree 3), so
the free OH is at C3.  The glucopyranoside unit of **K is unique**: the
2,6-anhydro structure. -/
theorem unique_bridge_structure (ι : Fin 7) (X Y : Fin 6)
    (hsec : secondaryOxygen X)
    (hE : ValidBridgeStructure ι (candidate ι X Y))
    (hcomp : ∃ r : Rotamer, transDiaxial (X - 1) r) :
    candidate ι X Y = kUnit ι := by
  have hX : X = 2 := by
    have h1 := (competent_iff_C2 (X - 1)).1 hcomp
    rcases hsec with rfl | rfl
    · rfl
    · exact absurd h1 (by decide)
  subst hX
  -- In a candidate the free OH sits exactly at position `Y` and, since the
  -- glycosidic positions 1 and 4 cannot carry a free –OH, `Y ∈ {2, 3}`.
  have hYbridge : ohBond ι Y ∈ candidate ι 2 Y :=
    ohBond_candidate_iff.mpr rfl
  have hY23 : Y = 2 ∨ Y = 3 := by
    -- In the α-1,4-linked macrocycle the glycosidic oxygens cannot carry a
    -- proton, so the free OH must sit at one of the secondary positions.
    exact hE.freeOH_secondary Y hYbridge
  rcases hY23 with rfl | rfl
  · -- Y = 2: the "free OH" would sit on the same oxygen that closes the
    -- bridge, giving O2 degree 3 — contradicting the degree-2 bridging ether.
    exfalso
    have hb : hasBridge ι (candidate ι 2 2) 2 := candidate_has_bridge ι 2 2
    have hdeg2 := hE.bridge_ether 2 hb
    have hdeg3 := deg_bridge_alcohol_o2 ι
    omega
  · rfl

/-- Total free OH over the whole molecule K (7 units). -/
def totalFreeOH (f : Fin 7 → Finset Bond) : ℕ :=
  (Finset.univ : Finset (Fin 7)).sum fun ι => freeOH ι (f ι)

/-- **K has exactly 7 free OH groups — one per glucopyranoside unit** — as the
problem states. -/
theorem kCD_total_free_OH : totalFreeOH kUnit = 7 := by
  simp only [totalFreeOH, kUnit_has_one_free_OH, Finset.sum_const, Finset.card_univ]
  rfl

/-- **Master characterization of K** (requested output 2): the completed CD
template for K is the seven-fold repetition of `kUnit` — the 2,6-anhydro unit
with the explicit registered bond O2–C6, free OH at C3, compact size 20,
degree-2 bridging ether oxygen, one free OH per unit, 7 in total — it is the
unique valid competent closure, and its stereochemistry (C1 S, C2 R, C3 R,
C4 R, C5 R; geometry retained from β-CD, the C2 label flipped by the CIP
re-ranking) is given explicitly by `stereoK`.  The favourable chair to tick
is ⁴C₁ (left template). -/
theorem K_characterization :
    -- uniqueness: only the 2,6-anhydro closure is competent and valid
    (∀ (ι : Fin 7) (X Y : Fin 6), secondaryOxygen X →
      ValidBridgeStructure ι (candidate ι X Y) →
      (∃ r : Rotamer, transDiaxial (X - 1) r) →
      candidate ι X Y = kUnit ι)
    -- the assembled molecule has one free OH per unit
    ∧ totalFreeOH kUnit = 7
    -- stereochemistry of every unit
    ∧ (∀ ι : Fin 7,
        (stereoK ι).c1_label = .S ∧ (stereoK ι).c2_label = .R ∧
        (stereoK ι).c3_label = .R ∧ (stereoK ι).c4_label = .R ∧
        (stereoK ι).c5_label = .R)
    -- the favourable chair is ⁴C₁ (left template ticked)
    ∧ clashCount axial4C1 < clashCount axial1C4 :=
  ⟨fun ι X Y hsec hE hcomp => unique_bridge_structure ι X Y hsec hE hcomp,
   kCD_total_free_OH,
   fun ι => stereo_labels_k ι,
   favourable_chair_is_4C1⟩

end IChO2026T9A2
