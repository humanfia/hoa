import Mathlib

inductive Monomer
  | A1 | A2 | A3 | A4 | B1 | B2 | B3 | C1 | C2 | C3 | D1 | D2 | D3 | D4 | E1
  deriving DecidableEq, Repr, Fintype

@[reducible] def samePair (x y a b : Monomer) : Prop :=
  (x = a ∧ y = b) ∨ (x = b ∧ y = a)

-- exhaustive pattern: hypothesis kept in context, ground goals decided directly
example (x y : Monomer) (h : (x = Monomer.A2 ∧ y = Monomer.B1) ∨ True) :
    samePair x y Monomer.A3 Monomer.B2 ∨ samePair x y Monomer.B1 Monomer.A2 := by
  fin_cases x <;> fin_cases y <;> decide
