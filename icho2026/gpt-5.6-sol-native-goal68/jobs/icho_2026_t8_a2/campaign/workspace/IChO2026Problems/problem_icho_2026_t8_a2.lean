import Mathlib

/-!
# IChO 2026, theory problem 8.2

This file formalizes the five structures requested in the printed mechanism.
The problem input is kept in `ProblemInput`; the graph rewrites in
`ChemistryRule` encode the standard tertiary-amine oxidation sequence.  The
answer structures are independent, fully explicit labelled molecular graphs,
so the main theorems check the result of each rewrite rather than defining an
answer by an assumed equality.

Hydrogens are recorded on their heavy atom.  Thus every atom of a conventional
skeletal drawing is represented: heavy atoms are vertices and attached
hydrogens are part of the vertex label.  Formal charge, unpaired electrons,
bond order, and stereochemical annotations are separate fields.
-/

namespace IChO2026T8A2

inductive Element where
  | C | N | O
  deriving DecidableEq, Repr

inductive BondOrder where
  | none | single | double
  deriving DecidableEq, Repr

inductive StereoAnnotation where
  | none | R | S | E | Z
  deriving DecidableEq, Repr

/-- The complete label on a heavy-atom vertex.  `hydrogens` records the
explicit number of H atoms attached to that vertex. -/
structure AtomLabel where
  element : Element
  hydrogens : Nat
  formalCharge : Int
  radicalElectrons : Nat
  stereo : StereoAnnotation
  deriving DecidableEq, Repr

/-- A finite labelled molecular graph. -/
structure Molecule (n : Nat) where
  atom : Fin n → AtomLabel
  bond : Fin n → Fin n → BondOrder

@[ext]
theorem molecule_ext {n : Nat} {m₁ m₂ : Molecule n}
    (hatom : m₁.atom = m₂.atom) (hbond : m₁.bond = m₂.bond) : m₁ = m₂ := by
  cases m₁
  cases m₂
  simp_all

def carbon (h r : Nat) (q : Int) : AtomLabel :=
  ⟨.C, h, q, r, .none⟩

def nitrogen (h r : Nat) (q : Int) : AtomLabel :=
  ⟨.N, h, q, r, .none⟩

def oxygen (h r : Nat) (q : Int) : AtomLabel :=
  ⟨.O, h, q, r, .none⟩

def joins {n : Nat} (a b i j : Fin n) : Prop :=
  (i = a ∧ j = b) ∨ (i = b ∧ j = a)

instance {n : Nat} (a b i j : Fin n) : Decidable (joins a b i j) :=
  by
    unfold joins
    infer_instance

/-- Bond graph of N(CH2CH2OH)3.  Vertices `1,4,7` are alpha to N;
`2,5,8` are the corresponding beta carbons; `3,6,9` are OH oxygens. -/
def triethanolamineBond (i j : Fin 10) : BondOrder :=
  if joins 0 1 i j ∨ joins 1 2 i j ∨ joins 2 3 i j ∨
      joins 0 4 i j ∨ joins 4 5 i j ∨ joins 5 6 i j ∨
      joins 0 7 i j ∨ joins 7 8 i j ∨ joins 8 9 i j then
    .single
  else
    .none

def iminiumBond (i j : Fin 10) : BondOrder :=
  if joins 0 1 i j then .double else triethanolamineBond i j

def diethanolamineBond (i j : Fin 7) : BondOrder :=
  if joins 0 1 i j ∨ joins 1 2 i j ∨ joins 2 3 i j ∨
      joins 0 4 i j ∨ joins 4 5 i j ∨ joins 5 6 i j then
    .single
  else
    .none

def glycolaldehydeBond (i j : Fin 4) : BondOrder :=
  if joins 0 3 i j then
    .double
  else if joins 0 1 i j ∨ joins 1 2 i j then
    .single
  else
    .none

namespace ProblemInput

/-- Species 2 as printed: triethanolamine, N(CH2CH2OH)3. -/
def species2 : Molecule 10 where
  atom := ![
    nitrogen 0 0 0,
    carbon 2 0 0, carbon 2 0 0, oxygen 1 0 0,
    carbon 2 0 0, carbon 2 0 0, oxygen 1 0 0,
    carbon 2 0 0, carbon 2 0 0, oxygen 1 0 0]
  bond := triethanolamineBond

/-- The four labels printed over the arrows from 2 to 6 + 7. -/
inductive PrintedStep where
  | removeElectron
  | removeProton
  | addWaterRemoveProton
  deriving DecidableEq, Repr

def printedSteps : List PrintedStep :=
  [.removeElectron, .removeProton, .removeElectron, .addWaterRemoveProton]

end ProblemInput

namespace ChemistryRule

def updateAtom {n : Nat} (m : Molecule n) (k : Fin n)
    (f : AtomLabel → AtomLabel) : Molecule n where
  atom i := if i = k then f (m.atom i) else m.atom i
  bond := m.bond

def updateBond {n : Nat} (m : Molecule n) (a b : Fin n)
    (order : BondOrder) : Molecule n where
  atom := m.atom
  bond i j := if joins a b i j then order else m.bond i j

/-- Single-electron oxidation of a neutral tertiary amine removes an electron
from the N lone pair, giving the N-centred aminium radical cation. -/
def oxidizeTertiaryAmine (m : Molecule 10) : Molecule 10 :=
  updateAtom m 0 fun a =>
    { a with
      formalCharge := a.formalCharge + 1
      radicalElectrons := a.radicalElectrons + 1 }

/-- Alpha deprotonation of an aminium radical cation.  The first arm is used as
a canonical representative of the three symmetry-equivalent arms. -/
def alphaDeprotonateAminium (m : Molecule 10) : Molecule 10 :=
  let onN := updateAtom m 0 fun a =>
    { a with
      formalCharge := a.formalCharge - 1
      radicalElectrons := a.radicalElectrons - 1 }
  updateAtom onN 1 fun a =>
    { a with
      hydrogens := a.hydrogens - 1
      radicalElectrons := a.radicalElectrons + 1 }

/-- Oxidation of the alpha-amino carbon radical gives the usual iminium Lewis
structure, with an N=C double bond and positive formal charge on N. -/
def oxidizeAlphaRadicalToIminium (m : Molecule 10) : Molecule 10 :=
  let onN := updateAtom m 0 fun a =>
    { a with formalCharge := a.formalCharge + 1 }
  let offC := updateAtom onN 1 fun a =>
    { a with radicalElectrons := a.radicalElectrons - 1 }
  updateBond offC 0 1 .double

/-- Hydrolysis of the canonical N=C iminium arm.  The old alpha carbon becomes
the aldehyde carbon, water supplies its carbonyl oxygen, and the proton left
after the printed net `+H2O, -H+` operation becomes the N-H proton. -/
def hydrolyzeFirstIminium (m : Molecule 10) : Molecule 7 × Molecule 4 :=
  let amine : Molecule 7 :=
    { atom := ![
        { m.atom 0 with
          hydrogens := (m.atom 0).hydrogens + 1
          formalCharge := (m.atom 0).formalCharge - 1 },
        m.atom 4, m.atom 5, m.atom 6,
        m.atom 7, m.atom 8, m.atom 9]
      bond := diethanolamineBond }
  let aldehyde : Molecule 4 :=
    { atom := ![m.atom 1, m.atom 2, m.atom 3, oxygen 0 0 0]
      bond := glycolaldehydeBond }
  (amine, aldehyde)

end ChemistryRule

/-! ## Derived mechanism states -/

def derived3 : Molecule 10 :=
  ChemistryRule.oxidizeTertiaryAmine ProblemInput.species2

def derived4 : Molecule 10 :=
  ChemistryRule.alphaDeprotonateAminium derived3

def derived5 : Molecule 10 :=
  ChemistryRule.oxidizeAlphaRadicalToIminium derived4

def hydrolysisProducts : Molecule 7 × Molecule 4 :=
  ChemistryRule.hydrolyzeFirstIminium derived5

def derived6 : Molecule 7 := hydrolysisProducts.1
def derived7 : Molecule 4 := hydrolysisProducts.2

/-! ## Explicit answer drawings

These definitions do not invoke the rewrite functions above.  Consequently,
the equalities below genuinely compare a derived graph with an independently
spelled-out answer graph.
-/

/-- 3 = [(HOCH2CH2)3N] radical cation, with charge and radical on N. -/
def drawing3 : Molecule 10 where
  atom := ![
    nitrogen 0 1 1,
    carbon 2 0 0, carbon 2 0 0, oxygen 1 0 0,
    carbon 2 0 0, carbon 2 0 0, oxygen 1 0 0,
    carbon 2 0 0, carbon 2 0 0, oxygen 1 0 0]
  bond := triethanolamineBond

/-- 4 = (HOCH2CH2)2N-C(H radical)-CH2OH. -/
def drawing4 : Molecule 10 where
  atom := ![
    nitrogen 0 0 0,
    carbon 1 1 0, carbon 2 0 0, oxygen 1 0 0,
    carbon 2 0 0, carbon 2 0 0, oxygen 1 0 0,
    carbon 2 0 0, carbon 2 0 0, oxygen 1 0 0]
  bond := triethanolamineBond

/-- 5 = [(HOCH2CH2)2N+=CH-CH2OH], the iminium ion. -/
def drawing5 : Molecule 10 where
  atom := ![
    nitrogen 0 0 1,
    carbon 1 0 0, carbon 2 0 0, oxygen 1 0 0,
    carbon 2 0 0, carbon 2 0 0, oxygen 1 0 0,
    carbon 2 0 0, carbon 2 0 0, oxygen 1 0 0]
  bond := iminiumBond

/-- 6 = HN(CH2CH2OH)2, diethanolamine. -/
def drawing6 : Molecule 7 where
  atom := ![
    nitrogen 1 0 0,
    carbon 2 0 0, carbon 2 0 0, oxygen 1 0 0,
    carbon 2 0 0, carbon 2 0 0, oxygen 1 0 0]
  bond := diethanolamineBond

/-- 7 = HOCH2-C(=O)H, glycolaldehyde. -/
def drawing7 : Molecule 4 where
  atom := ![
    carbon 1 0 0, carbon 2 0 0, oxygen 1 0 0, oxygen 0 0 0]
  bond := glycolaldehydeBond

/-! ## Structural checks -/

def bondWeight : BondOrder → Nat
  | .none => 0
  | .single => 1
  | .double => 2

def bondValence {n : Nat} (m : Molecule n) (i : Fin n) : Nat :=
  ∑ j, bondWeight (m.bond i j)

/-- Local main-group valence patterns used by these five Lewis structures. -/
def LocalValenceOK (a : AtomLabel) (v : Nat) : Prop :=
  match a.element with
  | .C =>
      a.formalCharge = 0 ∧ a.radicalElectrons ≤ 1 ∧
        v + a.hydrogens + a.radicalElectrons = 4
  | .O =>
      a.formalCharge = 0 ∧ a.radicalElectrons = 0 ∧
        v + a.hydrogens = 2
  | .N =>
      (a.formalCharge = 0 ∧ a.radicalElectrons = 0 ∧
        v + a.hydrogens = 3) ∨
      (a.formalCharge = 1 ∧ a.radicalElectrons = 0 ∧
        v + a.hydrogens = 4) ∨
      (a.formalCharge = 1 ∧ a.radicalElectrons = 1 ∧
        v + a.hydrogens = 3)

instance (a : AtomLabel) (v : Nat) : Decidable (LocalValenceOK a v) := by
  unfold LocalValenceOK
  cases a.element <;> infer_instance

def WellFormed {n : Nat} (m : Molecule n) : Prop :=
  (∀ i, m.bond i i = .none) ∧
  (∀ i j, m.bond i j = m.bond j i) ∧
  (∀ i, LocalValenceOK (m.atom i) (bondValence m i))

structure Formula where
  carbon : Nat
  hydrogen : Nat
  nitrogen : Nat
  oxygen : Nat
  deriving DecidableEq, Repr

def formula {n : Nat} (m : Molecule n) : Formula where
  carbon := ∑ i, if (m.atom i).element = .C then 1 else 0
  hydrogen := ∑ i, (m.atom i).hydrogens
  nitrogen := ∑ i, if (m.atom i).element = .N then 1 else 0
  oxygen := ∑ i, if (m.atom i).element = .O then 1 else 0

def netCharge {n : Nat} (m : Molecule n) : Int :=
  ∑ i, (m.atom i).formalCharge

def radicalCount {n : Nat} (m : Molecule n) : Nat :=
  ∑ i, (m.atom i).radicalElectrons

def NoStereoAnnotations {n : Nat} (m : Molecule n) : Prop :=
  ∀ i, (m.atom i).stereo = .none

/-- The graph predicate recognized by the aldehyde-selective silver-mirror clue:
a carbon bearing H and double-bonded to oxygen. -/
def HasAldehydeCarbon {n : Nat} (m : Molecule n) : Prop :=
  ∃ c o, c ≠ o ∧
    (m.atom c).element = .C ∧ 0 < (m.atom c).hydrogens ∧
    (m.atom o).element = .O ∧ m.bond c o = .double

theorem derived3_eq_drawing3 : derived3 = drawing3 := by
  apply molecule_ext
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem derived4_eq_drawing4 : derived4 = drawing4 := by
  apply molecule_ext
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem derived5_eq_drawing5 : derived5 = drawing5 := by
  apply molecule_ext
  · funext i
    fin_cases i <;> rfl
  · funext i j
    fin_cases i <;> fin_cases j <;> rfl

theorem derived6_eq_drawing6 : derived6 = drawing6 := by
  apply molecule_ext
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem derived7_eq_drawing7 : derived7 = drawing7 := by
  apply molecule_ext
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem drawing3_wellFormed : WellFormed drawing3 := by
  constructor
  · intro i
    fin_cases i <;> rfl
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i
    fin_cases i <;> decide

theorem drawing4_wellFormed : WellFormed drawing4 := by
  constructor
  · intro i
    fin_cases i <;> rfl
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i
    fin_cases i <;> decide

theorem drawing5_wellFormed : WellFormed drawing5 := by
  constructor
  · intro i
    fin_cases i <;> rfl
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i
    fin_cases i <;> decide

theorem drawing6_wellFormed : WellFormed drawing6 := by
  constructor
  · intro i
    fin_cases i <;> rfl
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i
    fin_cases i <;> decide

theorem drawing7_wellFormed : WellFormed drawing7 := by
  constructor
  · intro i
    fin_cases i <;> rfl
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i
    fin_cases i <;> decide

theorem product7_hasAldehyde : HasAldehydeCarbon drawing7 := by
  refine ⟨0, 3, ?_, rfl, by decide, rfl, rfl⟩
  decide

theorem product6_hasNoAldehyde : ¬HasAldehydeCarbon drawing6 := by
  rintro ⟨c, o, hne, hc, hh, ho, hb⟩
  fin_cases c <;> fin_cases o <;> simp_all [drawing6, diethanolamineBond, joins]

theorem drawing3_composition :
    formula drawing3 = ⟨6, 15, 1, 3⟩ ∧
    netCharge drawing3 = 1 ∧ radicalCount drawing3 = 1 := by decide

theorem drawing4_composition :
    formula drawing4 = ⟨6, 14, 1, 3⟩ ∧
    netCharge drawing4 = 0 ∧ radicalCount drawing4 = 1 := by decide

theorem drawing5_composition :
    formula drawing5 = ⟨6, 14, 1, 3⟩ ∧
    netCharge drawing5 = 1 ∧ radicalCount drawing5 = 0 := by decide

theorem drawing6_composition :
    formula drawing6 = ⟨4, 11, 1, 2⟩ ∧
    netCharge drawing6 = 0 ∧ radicalCount drawing6 = 0 := by decide

theorem drawing7_composition :
    formula drawing7 = ⟨2, 4, 0, 2⟩ ∧
    netCharge drawing7 = 0 ∧ radicalCount drawing7 = 0 := by decide

/-- Atom, charge, and radical accounting for the three printed intermediate
arrows.  In particular, only the `-H+` step changes the molecular formula. -/
theorem intermediate_arrow_accounting :
    formula derived3 = formula ProblemInput.species2 ∧
    netCharge derived3 = netCharge ProblemInput.species2 + 1 ∧
    radicalCount derived3 = radicalCount ProblemInput.species2 + 1 ∧
    formula derived4 = ⟨6, 14, 1, 3⟩ ∧
    netCharge derived4 = netCharge derived3 - 1 ∧
    radicalCount derived4 = radicalCount derived3 ∧
    formula derived5 = formula derived4 ∧
    netCharge derived5 = netCharge derived4 + 1 ∧
    radicalCount derived5 + 1 = radicalCount derived4 := by
  decide

/-- The final graph rewrite has exactly the printed net accounting
`5 + H2O - H+`: one extra O and one net extra H across 6 and 7, while C and N
are partitioned between the products and the total charge becomes zero. -/
theorem hydrolysis_arrow_accounting :
    (formula derived6).carbon + (formula derived7).carbon =
      (formula derived5).carbon ∧
    (formula derived6).hydrogen + (formula derived7).hydrogen =
      (formula derived5).hydrogen + 1 ∧
    (formula derived6).nitrogen + (formula derived7).nitrogen =
      (formula derived5).nitrogen ∧
    (formula derived6).oxygen + (formula derived7).oxygen =
      (formula derived5).oxygen + 1 ∧
    netCharge derived6 + netCharge derived7 = netCharge derived5 - 1 := by
  decide

theorem drawing3_noStereo : NoStereoAnnotations drawing3 := by
  intro i
  fin_cases i <;> rfl

theorem drawing4_noStereo : NoStereoAnnotations drawing4 := by
  intro i
  fin_cases i <;> rfl

theorem drawing5_noStereo : NoStereoAnnotations drawing5 := by
  intro i
  fin_cases i <;> rfl

theorem drawing6_noStereo : NoStereoAnnotations drawing6 := by
  intro i
  fin_cases i <;> rfl

theorem drawing7_noStereo : NoStereoAnnotations drawing7 := by
  intro i
  fin_cases i <;> rfl

/-! ## Requested outputs -/

theorem structure_3 :
    derived3 = drawing3 ∧ WellFormed drawing3 ∧
      formula drawing3 = ⟨6, 15, 1, 3⟩ ∧
      netCharge drawing3 = 1 ∧ radicalCount drawing3 = 1 ∧
      NoStereoAnnotations drawing3 := by
  exact ⟨derived3_eq_drawing3, drawing3_wellFormed,
    drawing3_composition.1, drawing3_composition.2.1,
    drawing3_composition.2.2, drawing3_noStereo⟩

theorem structure_4 :
    derived4 = drawing4 ∧ WellFormed drawing4 ∧
      formula drawing4 = ⟨6, 14, 1, 3⟩ ∧
      netCharge drawing4 = 0 ∧ radicalCount drawing4 = 1 ∧
      NoStereoAnnotations drawing4 := by
  exact ⟨derived4_eq_drawing4, drawing4_wellFormed,
    drawing4_composition.1, drawing4_composition.2.1,
    drawing4_composition.2.2, drawing4_noStereo⟩

theorem structure_5 :
    derived5 = drawing5 ∧ WellFormed drawing5 ∧
      formula drawing5 = ⟨6, 14, 1, 3⟩ ∧
      netCharge drawing5 = 1 ∧ radicalCount drawing5 = 0 ∧
      NoStereoAnnotations drawing5 := by
  exact ⟨derived5_eq_drawing5, drawing5_wellFormed,
    drawing5_composition.1, drawing5_composition.2.1,
    drawing5_composition.2.2, drawing5_noStereo⟩

theorem structure_6 :
    derived6 = drawing6 ∧ WellFormed drawing6 ∧
      formula drawing6 = ⟨4, 11, 1, 2⟩ ∧
      netCharge drawing6 = 0 ∧ radicalCount drawing6 = 0 ∧
      NoStereoAnnotations drawing6 ∧ ¬HasAldehydeCarbon drawing6 := by
  exact ⟨derived6_eq_drawing6, drawing6_wellFormed,
    drawing6_composition.1, drawing6_composition.2.1,
    drawing6_composition.2.2, drawing6_noStereo,
    product6_hasNoAldehyde⟩

theorem structure_7 :
    derived7 = drawing7 ∧ WellFormed drawing7 ∧
      formula drawing7 = ⟨2, 4, 0, 2⟩ ∧
      netCharge drawing7 = 0 ∧ radicalCount drawing7 = 0 ∧
      NoStereoAnnotations drawing7 ∧ HasAldehydeCarbon drawing7 := by
  exact ⟨derived7_eq_drawing7, drawing7_wellFormed,
    drawing7_composition.1, drawing7_composition.2.1,
    drawing7_composition.2.2, drawing7_noStereo,
    product7_hasAldehyde⟩

#print axioms structure_3
#print axioms structure_4
#print axioms structure_5
#print axioms structure_6
#print axioms structure_7

end IChO2026T8A2
