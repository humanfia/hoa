import Mathlib
inductive HClass | boronicAcid | catechol | amine | aldehyde | nitrile deriving DecidableEq, Repr
inductive Monomer
  | A1 | A2 | A3 | A4 | B1 | B2 | B3 | C1 | C2 | C3 | D1 | D2 | D3 | D4 | E1
  deriving DecidableEq, Repr, Fintype
def connectivity : Monomer → ℕ
  | .A1 => 3 | .A2 => 2 | .A3 => 4 | .A4 => 4
  | .B1 => 4 | .B2 => 2 | .B3 => 3
  | .C1 => 2 | .C2 => 4 | .C3 => 4
  | .D1 => 6 | .D2 => 3 | .D3 => 4 | .D4 => 2
  | .E1 => 3
def hclass : Monomer → HClass
  | .A1 | .A2 | .A3 | .A4 => .boronicAcid
  | .B1 | .B2 | .B3 => .catechol
  | .C1 | .C2 | .C3 => .amine
  | .D1 | .D2 | .D3 | .D4 => .aldehyde
  | .E1 => .nitrile
inductive Geometry | planar | tetrahedral deriving DecidableEq, Repr
def geometry : Monomer → Geometry
  | .A4 | .D3 => .tetrahedral
  | _ => .planar
def reactCompatible (m n : Monomer) : Prop :=
  match hclass m, hclass n with
  | .boronicAcid, .catechol | .catechol, .boronicAcid
  | .amine, .aldehyde | .aldehyde, .amine
  | .nitrile, .aldehyde | .aldehyde, .nitrile => True
  | _, _ => False
instance {m n : Monomer} : Decidable (reactCompatible m n) := by
  unfold reactCompatible
  cases hclass m <;> cases hclass n <;>
    first | exact .isTrue trivial | exact .isFalse id

#eval decide (reactCompatible Monomer.E1 Monomer.D2)

structure Net where
  vertexDegree : ℕ
  planarOnly : Bool
  needsTetrahedralVertex : Bool
  deriving DecidableEq, Repr

def Realises (t : Net) (x y : Monomer) : Prop :=
  x ≠ y ∧
  reactCompatible x y ∧
  ((connectivity x = t.vertexDegree ∧ connectivity y = 2) ∨
   (connectivity y = t.vertexDegree ∧ connectivity x = 2)) ∧
  (t.planarOnly → geometry x = .planar ∧ geometry y = .planar) ∧
  (t.needsTetrahedralVertex →
    (connectivity x = t.vertexDegree → geometry x = .tetrahedral) ∧
    (connectivity y = t.vertexDegree → geometry y = .tetrahedral))

instance {t : Net} {x y : Monomer} : Decidable (Realises t x y) := by
  unfold Realises
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def hexagonal2Net  : Net := ⟨3, true, false⟩
#eval decide (Realises hexagonal2Net Monomer.E1 Monomer.D2)
#eval decide ((connectivity Monomer.E1 = 3 ∧ connectivity Monomer.D2 = 2) ∨
   (connectivity Monomer.D2 = 3 ∧ connectivity Monomer.E1 = 2))
#eval decide (geometry Monomer.E1 = .planar ∧ geometry Monomer.D2 = .planar)

#eval connectivity Monomer.D2
#eval connectivity Monomer.E1
#eval decide (connectivity Monomer.E1 = 3)
#eval decide (connectivity Monomer.D2 = 2)
