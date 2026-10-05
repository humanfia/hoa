import QAlgBench.Base

namespace QAlgFormalized

open QAlgBench
open QAlgBench.PureState

noncomputable section

/-- The reversible basis-label map `(x, y) ↦ (x, y ⊕ f x)` for an
`n`-bit input and an `m`-bit target register. -/
def bitOraclePerm {n m : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ m)) :
    Equiv.Perm (Fin (2 ^ n) × Fin (2 ^ m)) where
  toFun p := (p.1, p.2 ^^^ f p.1)
  invFun p := (p.1, p.2 ^^^ f p.1)
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp only [Fin.xor_val_of_two_pow]
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp only [Fin.xor_val_of_two_pow]
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- The multi-bit XOR oracle, obtained by lifting its computational-basis
permutation to the `(n + m)`-qubit Hilbert space. -/
def bitOracle {n m : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ m)) :
    Gate (Qubits (n + m)) :=
  Gate.ofPerm (prodEquiv.permCongr (bitOraclePerm f))

/-- The oracle has the specified action on every computational-basis state. -/
theorem bitOracle_apply_ket {n m : ℕ}
    (f : Fin (2 ^ n) → Fin (2 ^ m))
    (x : Fin (2 ^ n)) (y : Fin (2 ^ m)) :
    (bitOracle f).apply (ket (prodEquiv (x, y))) =
      ket (prodEquiv (x, y ^^^ f x)) := by
  rw [bitOracle, Gate.ofPerm_apply_ket]
  congr 1
  change
    prodEquiv ((bitOraclePerm f).symm
      (prodEquiv.symm (prodEquiv (x, y)))) =
        prodEquiv (x, y ^^^ f x)
  rw [Equiv.symm_apply_apply]
  rfl

/-- A multi-bit XOR oracle is both unitary and Hermitian. -/
theorem bitOracle_unitary_and_hermitian {n m : ℕ}
    (f : Fin (2 ^ n) → Fin (2 ^ m)) :
    (bitOracle f : HilbertOperator (Qubits (n + m))) ∈
        Matrix.unitaryGroup (Fin (2 ^ (n + m))) ℂ ∧
      (bitOracle f : HilbertOperator (Qubits (n + m))).conjTranspose =
        (bitOracle f : HilbertOperator (Qubits (n + m))) := by
  constructor
  · exact (bitOracle f).unitary
  · change
      ((prodEquiv.permCongr (bitOraclePerm f)).permMatrix ℂ).conjTranspose =
        (prodEquiv.permCongr (bitOraclePerm f)).permMatrix ℂ
    rw [Matrix.conjTranspose_permMatrix]
    congr 1

end

end QAlgFormalized
