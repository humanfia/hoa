import Mathlib

inductive HClass | boronicAcid | catechol | amine | aldehyde | nitrile
  deriving DecidableEq, Repr

inductive Monomer
  | A1 | A2 | A3 | A4 | B1 | B2 | B3 | C1 | C2 | C3 | D1 | D2 | D3 | D4 | E1
  deriving DecidableEq, Repr, Fintype

def connectivity : Monomer → ℕ
  | .A1 => 3 | .A2 => 2 | .A3 => 4 | .A4 => 4
  | .B1 => 4 | .B2 => 2 | .B3 => 2
  | .C1 => 2 | .C2 => 4 | .C3 => 4
  | .D1 => 6 | .D2 => 3 | .D3 => 4 | .D4 => 2
  | .E1 => 3

def hclass : Monomer → HClass
  | .A1 | .A2 | .A3 | .A4 => .boronicAcid
  | .B1 | .B2 | .B3 => .catechol
  | .C1 | .C2 | .C3 => .amine
  | .D1 | .D2 | .D3 | .D4 => .aldehyde
  | .E1 => .nitrile

inductive Geometry | planar | tetrahedral
  deriving DecidableEq, Repr

def geometry : Monomer → Geometry
  | .A4 | .D3 => .tetrahedral
  | _ => .planar

def reactCompatible (m n : Monomer) : Prop :=
  match hclass m, hclass n with
  | .boronicAcid, .catechol | .catechol, .boronicAcid
  | .amine, .aldehyde | .aldehyde, .amine
  | .nitrile, .aldehyde | .aldehyde, .nitrile => True
  | _, _ => False

instance : Decidable (reactCompatible m n) := by
  unfold reactCompatible
  cases hclass m <;> cases hclass n <;>
    first | exact .isTrue trivial | exact .isFalse id

def chemicallyAdmissible (m n : Monomer) : Prop :=
  reactCompatible m n ∧
  ((hclass m = .nitrile ∨ hclass n = .nitrile) →
    (m = .D4 ∨ m = .E1) ∧ (n = .D4 ∨ n = .E1))

instance : Decidable (chemicallyAdmissible m n) := by
  unfold chemicallyAdmissible
  exact inferInstanceAs (Decidable (_ ∧ _))

example : reactCompatible Monomer.A2 Monomer.B3 := by decide
example : chemicallyAdmissible Monomer.A2 Monomer.B3 := by decide
example : chemicallyAdmissible Monomer.E1 Monomer.D2 := by decide
example : chemicallyAdmissible Monomer.E1 Monomer.D4 := by decide
example : ¬ chemicallyAdmissible Monomer.B2 Monomer.C2 := by decide

example : reactCompatible Monomer.E1 Monomer.D2 := by decide
example : ((hclass Monomer.E1 = .nitrile ∨ hclass Monomer.D2 = .nitrile) →
    (Monomer.E1 = .D4 ∨ Monomer.E1 = .E1) ∧ (Monomer.D2 = .D4 ∨ Monomer.D2 = .E1)) := by decide
example : True ∧ (((hclass Monomer.E1 = .nitrile ∨ hclass Monomer.D2 = .nitrile) →
    (Monomer.E1 = .D4 ∨ Monomer.E1 = .E1) ∧ (Monomer.D2 = .D4 ∨ Monomer.D2 = .E1))) := by decide
-- mimic unfold order
example : chemicallyAdmissible Monomer.E1 Monomer.D2 := by
  unfold chemicallyAdmissible
  decide

example (P : Prop) [Decidable P] : decide (Monomer.E1 = Monomer.D4) = false := by
  exact rfl
example : decide (Monomer.E1 = Monomer.D4 ∨ Monomer.E1 = Monomer.E1) = true := by
  exact rfl
example : decide ((hclass Monomer.E1 = HClass.nitrile ∨ hclass Monomer.D2 = HClass.nitrile)) = true := by
  exact rfl
example : decide ((Monomer.E1 = Monomer.D4 ∨ Monomer.E1 = Monomer.E1) ∧
     (Monomer.D2 = Monomer.D4 ∨ Monomer.D2 = Monomer.E1)) = true := by
  exact rfl
example : decide ((hclass Monomer.E1 = HClass.nitrile ∨ hclass Monomer.D2 = HClass.nitrile) →
    (Monomer.E1 = Monomer.D4 ∨ Monomer.E1 = Monomer.E1) ∧
     (Monomer.D2 = Monomer.D4 ∨ Monomer.D2 = Monomer.E1)) = true := by
  exact rfl
