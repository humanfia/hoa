import Mathlib

/-!
# IChO 2026, theory problem 9.5

This file formalizes the structure of intermediate `L` in the printed
cyclodextrin scheme.  Problem data, reaction semantics, derived template
entries, and the fully expanded molecular graph are kept in separate
namespaces.

The seven primary positions are numbered clockwise as in Q9-3, with Lean
index `0` representing printed unit 1.  The underlying cyclodextrin is made of
seven alpha-D-glucopyranoside units; the stereochemical faces below are the
standard Haworth-face meaning of that source phrase.
-/

namespace IChO2026Problems.T9A5

set_option maxRecDepth 100000

abbrev Unit := Fin 7

def unit1 : Unit := 0
def unit2 : Unit := 1
def unit3 : Unit := 2
def unit4 : Unit := 3
def unit5 : Unit := 4
def unit6 : Unit := 5
def unit7 : Unit := 6

inductive PrimaryBox where
  | hydroxymethyl
  | benzyloxymethyl
  deriving DecidableEq, Fintype, Repr

inductive SecondaryPosition where
  | c2
  | c3
  deriving DecidableEq, Fintype, Repr

inductive SecondaryBox where
  | hydroxy
  | benzyloxy
  deriving DecidableEq, Fintype, Repr

inductive StereoPosition where
  | c1
  | c2
  | c3
  | c4
  | c5
  deriving DecidableEq, Fintype, Repr

inductive Face where
  | above
  | below
  deriving DecidableEq, Fintype, Repr

/-- Standard Haworth-face encoding of an alpha-D-glucopyranoside residue:
the anomeric substituent and the C2 and C4 oxygen substituents are below;
the C3 oxygen substituent and C5 hydroxymethyl group are above. -/
def alphaDGlucopyranosideFace : StereoPosition → Face
  | .c1 => .below
  | .c2 => .below
  | .c3 => .above
  | .c4 => .below
  | .c5 => .above

structure CDState where
  primary : Unit → PrimaryBox
  secondary : Unit → SecondaryPosition → SecondaryBox
  stereo : Unit → StereoPosition → Face

namespace Source

def glucoseUnitCount : Nat := 7
def hydroxylsPerUnit : Nat := 3
def sodiumHydrideEquivalents : Nat := 30
def benzylChlorideEquivalents : Nat := 30
def dibalEquivalents : Nat := 2

theorem benzylation_reagents_cover_all_hydroxyls :
    glucoseUnitCount * hydroxylsPerUnit ≤ sodiumHydrideEquivalents ∧
    glucoseUnitCount * hydroxylsPerUnit ≤ benzylChlorideEquivalents := by
  norm_num [glucoseUnitCount, hydroxylsPerUnit, sodiumHydrideEquivalents,
    benzylChlorideEquivalents]

/-- The source drawing immediately before the reagents in Q9-3: seven
primary `CH2OH` groups and fourteen secondary hydroxyls on beta-CD. -/
def betaCD : CDState where
  primary := fun _ => .hydroxymethyl
  secondary := fun _ _ => .hydroxy
  stereo := fun _ => alphaDGlucopyranosideFace

/-- The first selectively exposed primary position may be called unit 1
because the fully benzylated starting ring is cyclically symmetric. -/
def firstDebenzylatedUnit : Unit := unit1

/-- The paragraph printed above the scheme states that a protic group at unit
1 directs the next primary reductive debenzylation to unit 4 when available. -/
def directedSecondUnit : Unit := unit4

theorem printed_dibal_count_matches_two_steps : dibalEquivalents = 2 := rfl

end Source

namespace Chemistry

/-- Exhaustive NaH/BnCl benzylation replaces every primary and secondary
hydroxyl hydrogen by benzyl and leaves the glucopyranoside stereochemistry
unchanged. -/
def exhaustiveBenzylation (s : CDState) : CDState where
  primary := fun _ => .benzyloxymethyl
  secondary := fun _ _ => .benzyloxy
  stereo := s.stereo

/-- One selective DIBAL-H debenzylation exposes the specified primary
alcohol.  The operation changes neither secondary ethers nor the CD
stereogenic backbone. -/
def primaryDebenzylation (selected : Unit) (s : CDState) : CDState where
  primary := fun u => if u = selected then .hydroxymethyl else s.primary u
  secondary := s.secondary
  stereo := s.stereo

theorem primaryDebenzylation_selected (selected : Unit) (s : CDState) :
    (primaryDebenzylation selected s).primary selected = .hydroxymethyl := by
  simp [primaryDebenzylation]

theorem primaryDebenzylation_other (selected u : Unit) (s : CDState)
    (h : u ≠ selected) :
    (primaryDebenzylation selected s).primary u = s.primary u := by
  simp [primaryDebenzylation, h]

theorem primaryDebenzylation_preserves_secondary
    (selected : Unit) (s : CDState) :
    (primaryDebenzylation selected s).secondary = s.secondary := rfl

theorem primaryDebenzylation_preserves_stereo
    (selected : Unit) (s : CDState) :
    (primaryDebenzylation selected s).stereo = s.stereo := rfl

end Chemistry

open Chemistry

/-- Product `L` obtained by exhaustive benzylation followed by the two
primary reductive debenzylations specified by the source scheme and directing
rule. -/
def L : CDState :=
  primaryDebenzylation Source.directedSecondUnit
    (primaryDebenzylation Source.firstDebenzylatedUnit
      (exhaustiveBenzylation Source.betaCD))

theorem L_primary_alcohol_iff (u : Unit) :
    L.primary u = .hydroxymethyl ↔ u = unit1 ∨ u = unit4 := by
  by_cases h4 : u = unit4
  · simp [L, Source.directedSecondUnit, Source.firstDebenzylatedUnit,
      Chemistry.primaryDebenzylation, h4]
  · by_cases h1 : u = unit1
    · simp [L, Source.directedSecondUnit, Source.firstDebenzylatedUnit,
        Chemistry.primaryDebenzylation, h1]
    · simp [L, Source.directedSecondUnit, Source.firstDebenzylatedUnit,
        Chemistry.primaryDebenzylation, Chemistry.exhaustiveBenzylation,
        h4, h1]

theorem L_primary_benzyl_iff (u : Unit) :
    L.primary u = .benzyloxymethyl ↔ u ≠ unit1 ∧ u ≠ unit4 := by
  by_cases h4 : u = unit4
  · simp [L, Source.directedSecondUnit, Chemistry.primaryDebenzylation, h4]
  · by_cases h1 : u = unit1
    · simp [L, Source.directedSecondUnit, Source.firstDebenzylatedUnit,
        Chemistry.primaryDebenzylation, h1]
    · simp [L, Source.directedSecondUnit, Source.firstDebenzylatedUnit,
        Chemistry.primaryDebenzylation, Chemistry.exhaustiveBenzylation,
        h4, h1]

theorem L_secondary_benzyl (u : Unit) (p : SecondaryPosition) :
    L.secondary u p = .benzyloxy := by
  rfl

theorem L_stereochemistry (u : Unit) (p : StereoPosition) :
    L.stereo u p = alphaDGlucopyranosideFace p := by
  rfl

/-- The seven boxes in clockwise printed order (units 1 through 7). -/
theorem structure_L_primary_boxes :
    List.ofFn L.primary =
      [.hydroxymethyl, .benzyloxymethyl, .benzyloxymethyl,
       .hydroxymethyl, .benzyloxymethyl, .benzyloxymethyl,
       .benzyloxymethyl] := by
  decide

/-- The outside template box abbreviates the two benzylated secondary
oxygens on each of seven residues, hence `(OBn)14`. -/
theorem structure_L_secondary_boxes :
    (Finset.univ.filter fun x : Unit × SecondaryPosition =>
      L.secondary x.1 x.2 = .benzyloxy).card = 14 := by
  decide

theorem structure_L_free_primary_count :
    (Finset.univ.filter fun u : Unit =>
      L.primary u = .hydroxymethyl).card = 2 := by
  decide

theorem structure_L_benzylated_primary_count :
    (Finset.univ.filter fun u : Unit =>
      L.primary u = .benzyloxymethyl).card = 5 := by
  decide

/-! ## Fully expanded molecular graph

The answer-sheet boxes use `Bn` shorthand.  The following finite graph expands
every such group, every hydrogen, all bond orders, formal charges, radical
counts, and all 35 glucopyranoside stereocentres.
-/

abbrev FreePrimary := {u : Unit // L.primary u = .hydroxymethyl}
abbrev ProtectedPrimary := {u : Unit // L.primary u = .benzyloxymethyl}
abbrev BenzylAttachment := ProtectedPrimary ⊕ (Unit × SecondaryPosition)

inductive BackboneHeavySite where
  | c1 | c2 | c3 | c4 | c5 | c6
  | ringO | glycosidicO | o2 | o3 | o6
  deriving DecidableEq, Fintype

inductive BenzylCarbonSite where
  | methylene
  | aryl0 | aryl1 | aryl2 | aryl3 | aryl4 | aryl5
  deriving DecidableEq, Fintype

inductive HeavyAtom where
  | backbone (unit : Unit) (site : BackboneHeavySite)
  | benzyl (attachment : BenzylAttachment) (site : BenzylCarbonSite)
  deriving DecidableEq, Fintype

inductive BackboneHydrogenSite where
  | c1 | c2 | c3 | c4 | c5 | c6a | c6b
  deriving DecidableEq, Fintype

inductive BenzylHydrogenSite where
  | methyleneA | methyleneB
  | aryl1 | aryl2 | aryl3 | aryl4 | aryl5
  deriving DecidableEq, Fintype

inductive HydrogenAtom where
  | backbone (unit : Unit) (site : BackboneHydrogenSite)
  | alcohol (unit : FreePrimary)
  | benzyl (attachment : BenzylAttachment) (site : BenzylHydrogenSite)
  deriving DecidableEq, Fintype

inductive Atom where
  | heavy (atom : HeavyAtom)
  | hydrogen (atom : HydrogenAtom)
  deriving DecidableEq, Fintype

inductive Element where
  | carbon | oxygen | hydrogen
  deriving DecidableEq, Fintype

def element : Atom → Element
  | .hydrogen _ => .hydrogen
  | .heavy (.benzyl _ _) => .carbon
  | .heavy (.backbone _ s) =>
      match s with
      | .c1 | .c2 | .c3 | .c4 | .c5 | .c6 => .carbon
      | .ringO | .glycosidicO | .o2 | .o3 | .o6 => .oxygen

def formalCharge (_ : Atom) : Int := 0
def radicalElectrons (_ : Atom) : Nat := 0

inductive BondOrder where
  | single
  | double
  deriving DecidableEq, Fintype

inductive BackboneHeavyEdge where
  | c1c2 | c2c3 | c3c4 | c4c5 | c5c6
  | c1RingO | c5RingO
  | c1GlycosidicO | glycosidicOToNextC4
  | c2O2 | c3O3 | c6O6
  deriving DecidableEq, Fintype

inductive BenzylRingEdge where
  | e01 | e12 | e23 | e34 | e45 | e50
  deriving DecidableEq, Fintype

inductive Bond where
  | backboneHeavy (unit : Unit) (edge : BackboneHeavyEdge)
  | backboneHydrogen (unit : Unit) (site : BackboneHydrogenSite)
  | alcoholHydrogen (unit : FreePrimary)
  | benzylAttachment (attachment : BenzylAttachment)
  | benzylMethyleneAryl (attachment : BenzylAttachment)
  | benzylRing (attachment : BenzylAttachment) (edge : BenzylRingEdge)
  | benzylHydrogen (attachment : BenzylAttachment) (site : BenzylHydrogenSite)
  deriving DecidableEq, Fintype

structure BondData where
  left : Atom
  right : Atom
  order : BondOrder
  deriving DecidableEq

private def bh (u : Unit) (s : BackboneHeavySite) : Atom :=
  .heavy (.backbone u s)

private def bc (a : BenzylAttachment) (s : BenzylCarbonSite) : Atom :=
  .heavy (.benzyl a s)

private def backboneHydrogenParent : BackboneHydrogenSite → BackboneHeavySite
  | .c1 => .c1
  | .c2 => .c2
  | .c3 => .c3
  | .c4 => .c4
  | .c5 => .c5
  | .c6a | .c6b => .c6

private def benzylHydrogenParent : BenzylHydrogenSite → BenzylCarbonSite
  | .methyleneA | .methyleneB => .methylene
  | .aryl1 => .aryl1
  | .aryl2 => .aryl2
  | .aryl3 => .aryl3
  | .aryl4 => .aryl4
  | .aryl5 => .aryl5

def attachmentOxygen : BenzylAttachment → Atom
  | .inl u => bh u.1 .o6
  | .inr (u, .c2) => bh u .o2
  | .inr (u, .c3) => bh u .o3

private def backboneHeavyEndpoints
    (u : Unit) : BackboneHeavyEdge → Atom × Atom
  | .c1c2 => (bh u .c1, bh u .c2)
  | .c2c3 => (bh u .c2, bh u .c3)
  | .c3c4 => (bh u .c3, bh u .c4)
  | .c4c5 => (bh u .c4, bh u .c5)
  | .c5c6 => (bh u .c5, bh u .c6)
  | .c1RingO => (bh u .c1, bh u .ringO)
  | .c5RingO => (bh u .c5, bh u .ringO)
  | .c1GlycosidicO => (bh u .c1, bh u .glycosidicO)
  | .glycosidicOToNextC4 =>
      (bh u .glycosidicO, bh (u + 1) .c4)
  | .c2O2 => (bh u .c2, bh u .o2)
  | .c3O3 => (bh u .c3, bh u .o3)
  | .c6O6 => (bh u .c6, bh u .o6)

private def benzylRingEndpoints
    (a : BenzylAttachment) : BenzylRingEdge → Atom × Atom
  | .e01 => (bc a .aryl0, bc a .aryl1)
  | .e12 => (bc a .aryl1, bc a .aryl2)
  | .e23 => (bc a .aryl2, bc a .aryl3)
  | .e34 => (bc a .aryl3, bc a .aryl4)
  | .e45 => (bc a .aryl4, bc a .aryl5)
  | .e50 => (bc a .aryl5, bc a .aryl0)

private def benzylRingBondOrder : BenzylRingEdge → BondOrder
  | .e01 | .e23 | .e45 => .double
  | .e12 | .e34 | .e50 => .single

/-- Complete edge interpretation of the expanded structure of `L`. -/
def bondData : Bond → BondData
  | .backboneHeavy u e =>
      { left := (backboneHeavyEndpoints u e).1
        right := (backboneHeavyEndpoints u e).2
        order := .single }
  | .backboneHydrogen u h =>
      { left := bh u (backboneHydrogenParent h)
        right := .hydrogen (.backbone u h)
        order := .single }
  | .alcoholHydrogen u =>
      { left := bh u.1 .o6
        right := .hydrogen (.alcohol u)
        order := .single }
  | .benzylAttachment a =>
      { left := attachmentOxygen a
        right := bc a .methylene
        order := .single }
  | .benzylMethyleneAryl a =>
      { left := bc a .methylene
        right := bc a .aryl0
        order := .single }
  | .benzylRing a e =>
      { left := (benzylRingEndpoints a e).1
        right := (benzylRingEndpoints a e).2
        order := benzylRingBondOrder e }
  | .benzylHydrogen a h =>
      { left := bc a (benzylHydrogenParent h)
        right := .hydrogen (.benzyl a h)
        order := .single }

def atomCount (e : Element) : Nat :=
  (Finset.univ.filter fun a : Atom => element a = e).card

def doubleBondCount : Nat :=
  (Finset.univ.filter fun b : Bond => (bondData b).order = .double).card

theorem L_free_primary_card : Fintype.card FreePrimary = 2 := by
  decide

theorem L_protected_primary_card : Fintype.card ProtectedPrimary = 5 := by
  decide

theorem L_benzyl_attachment_card : Fintype.card BenzylAttachment = 19 := by
  decide

/-- Every primary O6 is connected to an explicit benzyl carbon exactly when
its template box says `CH2OBn`. -/
theorem L_primary_has_benzyl_iff (u : Unit) :
    (∃ a : BenzylAttachment,
      attachmentOxygen a = bh u .o6) ↔
      L.primary u = .benzyloxymethyl := by
  fin_cases u <;> decide

/-- Every primary O6 is connected to an explicit hydroxyl hydrogen exactly
at the two boxes marked `CH2OH`. -/
theorem L_primary_has_hydrogen_iff (u : Unit) :
    (∃ f : FreePrimary,
      (bondData (.alcoholHydrogen f)).left = bh u .o6) ↔
      L.primary u = .hydroxymethyl := by
  fin_cases u <;> decide

/-- Every secondary O2/O3 oxygen is attached to one explicit benzyl group. -/
theorem L_secondary_has_benzyl
    (u : Unit) (p : SecondaryPosition) :
    ∃ a : BenzylAttachment,
      attachmentOxygen a =
        match p with
        | .c2 => bh u .o2
        | .c3 => bh u .o3 := by
  cases p with
  | c2 => exact ⟨.inr (u, .c2), rfl⟩
  | c3 => exact ⟨.inr (u, .c3), rfl⟩

theorem L_is_neutral_and_closed_shell (a : Atom) :
    formalCharge a = 0 ∧ radicalElectrons a = 0 := by
  simp [formalCharge, radicalElectrons]

/-- Expanded atom inventory: `L` has formula C175 H184 O35. -/
theorem structure_L_formula :
    atomCount .carbon = 175 ∧
    atomCount .hydrogen = 184 ∧
    atomCount .oxygen = 35 := by
  decide

set_option maxRecDepth 100000 in
theorem structure_L_atom_count : Fintype.card Atom = 394 := by
  decide

set_option maxRecDepth 100000 in
theorem structure_L_bond_count : Fintype.card Bond = 420 := by
  decide

/-- The only non-single bonds are the three Kekule double bonds in each of
the 19 explicitly expanded benzyl phenyl rings. -/
theorem structure_L_double_bond_count : doubleBondCount = 57 := by
  decide

theorem structure_L_no_self_bonds (b : Bond) :
    (bondData b).left ≠ (bondData b).right := by
  cases b with
  | backboneHeavy u e =>
      cases e <;>
        simp [bondData, backboneHeavyEndpoints, bh]
  | backboneHydrogen u h =>
      simp [bondData, bh]
  | alcoholHydrogen u =>
      simp [bondData, bh]
  | benzylAttachment a =>
      cases a with
      | inl u => simp [bondData, attachmentOxygen, bh, bc]
      | inr up =>
          rcases up with ⟨u, p⟩
          cases p <;> simp [bondData, attachmentOxygen, bh, bc]
  | benzylMethyleneAryl a =>
      simp [bondData, bc]
  | benzylRing a e =>
      cases e <;> simp [bondData, benzylRingEndpoints, bc]
  | benzylHydrogen a h =>
      simp [bondData, bc]

/-- There are five fixed stereocentres per glucopyranoside residue, all with
the alpha-D face assignment retained by the two reactions. -/
theorem structure_L_stereocentre_count :
    Fintype.card (Unit × StereoPosition) = 35 := by
  decide

/-- A compact certificate for the expanded graph: formula, attachment count,
edge inventory, aromatic bond orders, neutral/closed-shell state, and absence
of self-bonds. -/
theorem requested_structure_L_graph :
    Fintype.card BenzylAttachment = 19 ∧
    (atomCount .carbon = 175 ∧ atomCount .hydrogen = 184 ∧
      atomCount .oxygen = 35) ∧
    Fintype.card Atom = 394 ∧
    Fintype.card Bond = 420 ∧
    doubleBondCount = 57 ∧
    (∀ a, formalCharge a = 0 ∧ radicalElectrons a = 0) ∧
    (∀ b, (bondData b).left ≠ (bondData b).right) ∧
    Fintype.card (Unit × StereoPosition) = 35 := by
  exact ⟨L_benzyl_attachment_card, structure_L_formula,
    structure_L_atom_count, structure_L_bond_count,
    structure_L_double_bond_count, L_is_neutral_and_closed_shell,
    structure_L_no_self_bonds, structure_L_stereocentre_count⟩

/-- Combined exact statement of every answer-sheet field and the retained
stereochemistry. -/
theorem requested_structure_L :
    List.ofFn L.primary =
      [.hydroxymethyl, .benzyloxymethyl, .benzyloxymethyl,
       .hydroxymethyl, .benzyloxymethyl, .benzyloxymethyl,
       .benzyloxymethyl] ∧
    (∀ u p, L.secondary u p = .benzyloxy) ∧
    (∀ u p, L.stereo u p = alphaDGlucopyranosideFace p) := by
  exact ⟨structure_L_primary_boxes, L_secondary_benzyl, L_stereochemistry⟩

end IChO2026Problems.T9A5

#print axioms IChO2026Problems.T9A5.requested_structure_L
#print axioms IChO2026Problems.T9A5.structure_L_formula
#print axioms IChO2026Problems.T9A5.L_primary_has_benzyl_iff
#print axioms IChO2026Problems.T9A5.L_primary_has_hydrogen_iff
#print axioms IChO2026Problems.T9A5.requested_structure_L_graph
