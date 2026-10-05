import Mathlib

inductive HClass | boronicAcid | catechol | amine | aldehyde | nitrile
  deriving DecidableEq, Repr

inductive Monomer
  | A1 | A2 | A3 | A4 | B1 | B2 | B3 | C1 | C2 | C3 | D1 | D2 | D3 | D4 | E1
  deriving DecidableEq, Repr, Fintype

def hclass : Monomer → HClass
  | .A1 | .A2 | .A3 | .A4 => .boronicAcid
  | .B1 | .B2 | .B3 => .catechol
  | .C1 | .C2 | .C3 => .amine
  | .D1 | .D2 | .D3 | .D4 => .aldehyde
  | .E1 => .nitrile

-- raw decidable equality probes
theorem t1 : (Monomer.E1 = Monomer.D4 ∨ Monomer.E1 = Monomer.E1) := by decide
theorem t2 : decide (Monomer.E1 = Monomer.D4 ∨ Monomer.E1 = Monomer.E1) = true := by native_decide
theorem t3 : decide (Monomer.E1 = Monomer.E1) = true := rfl
theorem t4 : decide (Monomer.E1 = Monomer.D4) = false := rfl
#print axioms t1
