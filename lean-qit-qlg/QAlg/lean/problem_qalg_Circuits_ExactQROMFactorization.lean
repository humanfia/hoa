/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

import QAlgBench.Base

/-!
# Exact QROM factorization

This file formalizes the address-controlled factorization of an exact QROM
lookup.  An `n`-bit address and an `m`-bit data word are represented by
`Fin (2 ^ n)` and `Fin (2 ^ m)`, respectively.  The joint register uses the
big-endian tensor identification supplied by `QAlgBench.prodEquiv`.
-/

namespace QAlgFormalized
namespace ExactQROMFactorization

open QAlgBench

noncomputable section

/-- Bitwise XOR on the `m`-bit computational-basis labels. -/
def bitwiseXor {m : ℕ} (y d : Fin (2 ^ m)) : Fin (2 ^ m) :=
  (BitVec.xor (BitVec.ofFin y) (BitVec.ofFin d)).toFin

/-- The `j`-th, most-significant-bit-first component `D_j(k)` of a QROM word. -/
def dataBit {n m : ℕ} (D : Fin (2 ^ n) → Fin (2 ^ m))
    (k : Fin (2 ^ n)) (j : Fin m) : Bool :=
  (BitVec.ofFin (D k)).getMsb j

/-- XOR by a fixed `m`-bit word, viewed as an involutive permutation. -/
def bitwiseXorPerm {m : ℕ} (d : Fin (2 ^ m)) : Equiv.Perm (Fin (2 ^ m)) where
  toFun y := bitwiseXor y d
  invFun y := bitwiseXor y d
  left_inv := by
    intro y
    change
      ((BitVec.ofFin ((BitVec.ofFin y ^^^ BitVec.ofFin d).toFin)) ^^^
          BitVec.ofFin d).toFin =
        y
    rw [BitVec.ofFin_toFin, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero, BitVec.toFin_ofFin]
  right_inv := by
    intro y
    change
      ((BitVec.ofFin ((BitVec.ofFin y ^^^ BitVec.ofFin d).toFin)) ^^^
          BitVec.ofFin d).toFin =
        y
    rw [BitVec.ofFin_toFin, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero, BitVec.toFin_ofFin]

/-- The Pauli-X power selected by a classical bit: `X^0 = I`, `X^1 = X`. -/
def pauliXPower (b : Bool) : Gate (Qubits 1) :=
  if b then Gate.X else 1

/-- Ordered tensor product of one-qubit Pauli-X powers.

The recursion keeps the prefix on the left and appends the final bit on the
right, so when `bits` is instantiated with `dataBit D k`, the factors occur in
most-significant-bit order.  The empty tensor is the identity gate on
`Qubits 0`. -/
def orderedPauliXTensor :
    (m : ℕ) → (Fin m → Bool) → Gate (Qubits m)
  | 0, _ => 1
  | m + 1, bits =>
      Gate.tensor
        (orderedPauliXTensor m (fun j => bits j.castSucc))
        (pauliXPower (bits (Fin.last m)))

/-- The zero-fold ordered tensor is the identity on the zero-qubit register. -/
@[simp]
theorem orderedPauliXTensor_zero (bits : Fin 0 → Bool) :
    orderedPauliXTensor 0 bits = (1 : Gate (Qubits 0)) :=
  rfl

/-- Unfolding an ordered tensor appends its least-significant factor after the
most-significant prefix. -/
@[simp]
theorem orderedPauliXTensor_succ (m : ℕ) (bits : Fin (m + 1) → Bool) :
    orderedPauliXTensor (m + 1) bits =
      Gate.tensor
        (orderedPauliXTensor m (fun j => bits j.castSucc))
        (pauliXPower (bits (Fin.last m))) :=
  rfl

/-- The source expression
`X^(D k) = ⨂_{j=1}^m X^(D_j(k))`, with factors in MSB-first order. -/
def dataXTensor {n m : ℕ} (D : Fin (2 ^ n) → Fin (2 ^ m))
    (k : Fin (2 ^ n)) : Gate (Qubits m) :=
  orderedPauliXTensor m (fun j => dataBit D k j)

/-- The data-register operator
`X^d = ⨂ⱼ X^(d_j)`, characterized as bitwise XOR by `d`. -/
def dataXPower {m : ℕ} (d : Fin (2 ^ m)) : Gate (Qubits m) :=
  Gate.ofPerm (bitwiseXorPerm d)

private theorem bitVec_ofFin_prodEquiv {m n : ℕ}
    (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    BitVec.ofFin (prodEquiv (x, y)) =
      BitVec.ofFin x ++ BitVec.ofFin y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofFin, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt y.isLt]
  simp [prodEquiv, finProdFinEquiv, Nat.shiftLeft_eq, Nat.mul_comm,
    Nat.add_comm]

private theorem bitwiseXor_prodEquiv {m n : ℕ}
    (x d : Fin (2 ^ m)) (y e : Fin (2 ^ n)) :
    bitwiseXor (prodEquiv (x, y)) (prodEquiv (d, e)) =
      prodEquiv (bitwiseXor x d, bitwiseXor y e) := by
  change
    (BitVec.ofFin (prodEquiv (x, y)) ^^^
          BitVec.ofFin (prodEquiv (d, e))).toFin =
      (BitVec.ofFin (prodEquiv
        ((BitVec.ofFin x ^^^ BitVec.ofFin d).toFin,
          (BitVec.ofFin y ^^^ BitVec.ofFin e).toFin))).toFin
  apply congrArg BitVec.toFin
  simp only [bitVec_ofFin_prodEquiv, BitVec.ofFin_toFin,
    BitVec.xor_append]

private theorem dataXPower_apply_basis' {m : ℕ}
    (d y : Fin (2 ^ m)) :
    (dataXPower d).apply (PureState.ket y) =
      PureState.ket (bitwiseXor y d) := by
  rw [dataXPower, Gate.ofPerm_apply_ket]
  rfl

private theorem dataXPower_tensor {m n : ℕ}
    (d : Fin (2 ^ m)) (e : Fin (2 ^ n)) :
    Gate.tensor (dataXPower d) (dataXPower e) =
      dataXPower (prodEquiv (d, e)) := by
  apply Gate.ext
  intro i j
  rw [← Gate.apply_ket (Gate.tensor (dataXPower d) (dataXPower e)) j i,
    ← Gate.apply_ket (dataXPower (prodEquiv (d, e))) j i]
  let xy := (prodEquiv (m := m) (n := n)).symm j
  have hj :
      (PureState.ket xy.1).tensor (PureState.ket xy.2) =
        PureState.ket j := by
    rw [PureState.tensor_ket, Equiv.apply_symm_apply]
  have hlabel :
      prodEquiv (bitwiseXor xy.1 d, bitwiseXor xy.2 e) =
        bitwiseXor j (prodEquiv (d, e)) := by
    rw [← bitwiseXor_prodEquiv]
    congr 1
    exact Equiv.apply_symm_apply prodEquiv j
  have haction :
      (Gate.tensor (dataXPower d) (dataXPower e)).apply
          (PureState.ket j) =
        (dataXPower (prodEquiv (d, e))).apply
          (PureState.ket j) := by
    calc
      _ = (Gate.tensor (dataXPower d) (dataXPower e)).apply
          ((PureState.ket xy.1).tensor (PureState.ket xy.2)) :=
        congrArg
          (Gate.apply (Gate.tensor (dataXPower d) (dataXPower e))) hj.symm
      _ = ((dataXPower d).apply (PureState.ket xy.1)).tensor
          ((dataXPower e).apply (PureState.ket xy.2)) := by
        rw [Gate.tensor_apply_tensor]
      _ = (PureState.ket (bitwiseXor xy.1 d)).tensor
          (PureState.ket (bitwiseXor xy.2 e)) := by
        rw [dataXPower_apply_basis', dataXPower_apply_basis']
      _ = PureState.ket
          (prodEquiv (bitwiseXor xy.1 d, bitwiseXor xy.2 e)) := by
        rw [PureState.tensor_ket]
      _ = PureState.ket (bitwiseXor j (prodEquiv (d, e))) :=
        congrArg PureState.ket hlabel
      _ = _ := (dataXPower_apply_basis' (prodEquiv (d, e)) j).symm
  exact congrArg (fun ψ : PureState (Qubits (m + n)) => ψ i) haction

private theorem pauliXPower_eq_dataXPower_oneBit
    (d : Fin (2 ^ 1)) :
    pauliXPower ((BitVec.ofFin d).getMsb 0) = dataXPower d := by
  apply Gate.ext
  intro i j
  rw [← Gate.apply_ket
      (pauliXPower ((BitVec.ofFin d).getMsb 0)) j i,
    ← Gate.apply_ket (dataXPower d) j i]
  fin_cases d <;> fin_cases i <;> fin_cases j <;>
    simp +decide [pauliXPower, dataXPower, bitwiseXorPerm, bitwiseXor,
      Gate.X, Gate.ofPerm_apply_ket]

private theorem bitVec_getMsb_eq_getMsbD {m : ℕ}
    (x : BitVec m) (j : Fin m) :
    x.getMsb j = x.getMsbD j.val := by
  simp [BitVec.getMsb, BitVec.getMsbD, BitVec.getLsb,
    BitVec.getLsbD, j.isLt]

private theorem dataXPower_zero (d : Fin (2 ^ 0)) :
    dataXPower d = 1 := by
  have hp : bitwiseXorPerm d = Equiv.refl _ := by
    apply Equiv.ext
    intro y
    apply Fin.ext
    omega
  rw [dataXPower, hp]
  apply Gate.ext
  intro i j
  rw [← Gate.apply_ket (Gate.ofPerm (Equiv.refl _)) j i,
    ← Gate.apply_ket (1 : Gate (Qubits 0)) j i]
  fin_cases i
  fin_cases j
  simp [Gate.ofPerm_apply_ket]

private theorem orderedPauliXTensor_eq_dataXPower :
    ∀ (m : ℕ) (d : Fin (2 ^ m)),
      orderedPauliXTensor m (fun j => (BitVec.ofFin d).getMsb j) =
        dataXPower d := by
  intro m
  induction m with
  | zero =>
      intro d
      change (1 : Gate (Qubits 0)) = dataXPower d
      exact (dataXPower_zero d).symm
  | succ m ih =>
      intro d
      let de := (prodEquiv (m := m) (n := 1)).symm d
      have hdappend :
          BitVec.ofFin d =
            BitVec.ofFin de.1 ++ BitVec.ofFin de.2 := by
        calc
          BitVec.ofFin d =
              BitVec.ofFin (prodEquiv (de.1, de.2)) :=
            congrArg BitVec.ofFin
              (Equiv.apply_symm_apply prodEquiv d).symm
          _ = _ := bitVec_ofFin_prodEquiv de.1 de.2
      have hprefix :
          (fun j : Fin m => (BitVec.ofFin d).getMsb j.castSucc) =
            (fun j : Fin m => (BitVec.ofFin de.1).getMsb j) := by
        funext j
        rw [bitVec_getMsb_eq_getMsbD, bitVec_getMsb_eq_getMsbD]
        have h := congrArg
          (fun v : BitVec (m + 1) => v.getMsbD j.val) hdappend
        simpa [BitVec.getMsbD_append,
          show ¬m ≤ j.val by omega] using h
      have hlast :
          (BitVec.ofFin d).getMsb (Fin.last m) =
            (BitVec.ofFin de.2).getMsb (0 : Fin 1) := by
        rw [bitVec_getMsb_eq_getMsbD, bitVec_getMsb_eq_getMsbD]
        have h := congrArg
          (fun v : BitVec (m + 1) => v.getMsbD m) hdappend
        simpa [BitVec.getMsbD_append] using h
      rw [orderedPauliXTensor_succ, hprefix, ih de.1, hlast,
        pauliXPower_eq_dataXPower_oneBit, dataXPower_tensor]
      congr 1
      exact Equiv.apply_symm_apply prodEquiv d

/-- The explicit MSB-first tensor of one-qubit Pauli-X powers is exactly the
bitwise-XOR permutation gate used by `dataXPower`. -/
theorem dataXTensor_eq_dataXPower {n m : ℕ}
    (D : Fin (2 ^ n) → Fin (2 ^ m)) (k : Fin (2 ^ n)) :
    dataXTensor D k = dataXPower (D k) := by
  unfold dataXTensor dataBit
  exact orderedPauliXTensor_eq_dataXPower m (D k)

/-- `dataXPower d` has the computational-basis action of the tensor product
of the single-qubit factors `X^(d_j)`. -/
theorem dataXPower_apply_basis {m : ℕ} (d y : Fin (2 ^ m)) :
    (dataXPower d).apply (PureState.ket y) =
      PureState.ket (bitwiseXor y d) := by
  rw [dataXPower, Gate.ofPerm_apply_ket]
  rfl

/-- The benchmark's Pauli-X gate is the matrix displayed in the source. -/
theorem pauliX_matrix :
    (Gate.X : HilbertOperator (Qubits 1)) =
      !![(0 : ℂ), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gate.X, Gate.ofPerm]

/-- The raw controlled factor
`I_A ⊗ I_D + |k⟩⟨k|_A ⊗ (X^(D k) - I_D)`. -/
def factorOperator {n m : ℕ} (D : Fin (2 ^ n) → Fin (2 ^ m))
    (k : Fin (2 ^ n)) : HilbertOperator (Qubits (n + m)) :=
  HilbertOperator.tensor
      (1 : HilbertOperator (Qubits n))
      (1 : HilbertOperator (Qubits m))
    +
    HilbertOperator.tensor
      (OrthogonalProjector.basisOp k)
      ((dataXPower (D k) : HilbertOperator (Qubits m)) -
        (1 : HilbertOperator (Qubits m)))

/-- The controlled factor written with the source's explicit ordered tensor
`⨂_{j=1}^m X^(D_j(k))` in place of its XOR-permutation characterization. -/
theorem factorOperator_eq_orderedPauliXTensor {n m : ℕ}
    (D : Fin (2 ^ n) → Fin (2 ^ m)) (k : Fin (2 ^ n)) :
    factorOperator D k =
      HilbertOperator.tensor
          (1 : HilbertOperator (Qubits n))
          (1 : HilbertOperator (Qubits m))
        +
        HilbertOperator.tensor
          (OrthogonalProjector.basisOp k)
          ((dataXTensor D k : HilbertOperator (Qubits m)) -
            (1 : HilbertOperator (Qubits m))) := by
  rw [factorOperator, dataXTensor_eq_dataXPower]

/-- The address-controlled factor `C_k`, bundled with its unitarity. -/
def factorGate {n m : ℕ} (D : Fin (2 ^ n) → Fin (2 ^ m))
    (k : Fin (2 ^ n)) : Gate (Qubits (n + m)) :=
  Gate.ofUnitary (factorOperator D k) (by
    let P : OrthogonalProjector n := OrthogonalProjector.basis k
    let U : HilbertOperator (Qubits m) := dataXPower (D k)
    have hfactor :
        factorOperator D k =
          HilbertOperator.tensor P.complement 1 +
            HilbertOperator.tensor P.op U := by
      ext i j
      simp only [factorOperator, P, U, OrthogonalProjector.complement,
        OrthogonalProjector.basis, HilbertOperator.tensor_apply,
        Matrix.add_apply, Matrix.sub_apply]
      ring
    have hUstar : U.conjTranspose = U := by
      change
        ((bitwiseXorPerm (D k)).permMatrix ℂ).conjTranspose =
          (bitwiseXorPerm (D k)).permMatrix ℂ
      rw [Matrix.conjTranspose_permMatrix]
      rfl
    have hUsq : U * U = 1 := by
      have h := (dataXPower (D k)).unitary
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
      change U * U.conjTranspose = 1 at h
      rw [hUstar] at h
      exact h
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hfactor,
      Matrix.conjTranspose_add, HilbertOperator.conjTranspose_tensor,
      HilbertOperator.conjTranspose_tensor, P.complement_conjTranspose,
      P.selfAdjoint, hUstar, Matrix.conjTranspose_one, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_add, HilbertOperator.tensor_mul_tensor,
      HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor,
      HilbertOperator.tensor_mul_tensor, P.complement_sq, P.complement_mul,
      P.mul_complement, P.idempotent, hUsq]
    simp only [one_mul, mul_one, HilbertOperator.zero_tensor, add_zero, zero_add]
    rw [← HilbertOperator.add_tensor]
    have hcomplement : P.complement + P.op = 1 := by
      simp [OrthogonalProjector.complement]
    rw [hcomplement, HilbertOperator.one_tensor_one])

@[simp]
theorem factorGate_operator {n m : ℕ}
    (D : Fin (2 ^ n) → Fin (2 ^ m)) (k : Fin (2 ^ n)) :
    (factorGate D k : HilbertOperator (Qubits (n + m))) =
      factorOperator D k :=
  rfl

/-- Every controlled factor `C_k` is unitary. -/
theorem factorOperator_unitary {n m : ℕ}
    (D : Fin (2 ^ n) → Fin (2 ^ m)) (k : Fin (2 ^ n)) :
    factorOperator D k ∈ Matrix.unitaryGroup (Fin (2 ^ (n + m))) ℂ :=
  (factorGate D k).unitary

/-- A controlled factor changes the data word exactly on its selected address. -/
theorem factorGate_apply_basis {n m : ℕ}
    (D : Fin (2 ^ n) → Fin (2 ^ m))
    (k x : Fin (2 ^ n)) (y : Fin (2 ^ m)) :
    (factorGate D k).apply
        ((PureState.ket x).tensor (PureState.ket y)) =
      if x = k then
        (PureState.ket k).tensor
          (PureState.ket (bitwiseXor y (D k)))
      else
        (PureState.ket x).tensor (PureState.ket y) := by
  let P : OrthogonalProjector n := OrthogonalProjector.basis k
  let U : HilbertOperator (Qubits m) := dataXPower (D k)
  have hfactor :
      factorOperator D k =
        HilbertOperator.tensor P.complement 1 +
          HilbertOperator.tensor P.op U := by
    ext i j
    simp only [factorOperator, P, U, OrthogonalProjector.complement,
      OrthogonalProjector.basis, HilbertOperator.tensor_apply,
      Matrix.add_apply, Matrix.sub_apply]
    ring
  have hprojector :
      HilbertOperator.applyVec P.op
          (PureState.ket (R := Qubits n) x).vec =
        if x = k then
          (PureState.ket (R := Qubits n) x).vec
        else 0 := by
    by_cases hx : x = k
    · subst x
      ext i
      rw [HilbertOperator.applyVec_ket]
      simp [P, OrthogonalProjector.basis, OrthogonalProjector.basisOp]
    · ext i
      rw [HilbertOperator.applyVec_ket]
      simp [P, OrthogonalProjector.basis, OrthogonalProjector.basisOp, hx]
  have hsub_applyVec (A B : HilbertOperator (Qubits n))
      (ψ : StateVector (Qubits n)) :
      HilbertOperator.applyVec (A - B) ψ =
        HilbertOperator.applyVec A ψ - HilbertOperator.applyVec B ψ := by
    unfold HilbertOperator.applyVec
    rw [Matrix.sub_mulVec]
    rfl
  have hcomplement :
      HilbertOperator.applyVec P.complement
          (PureState.ket (R := Qubits n) x).vec =
        if x = k then 0
        else (PureState.ket (R := Qubits n) x).vec := by
    rw [OrthogonalProjector.complement, hsub_applyVec,
      HilbertOperator.one_applyVec, hprojector]
    by_cases hx : x = k <;> simp [hx]
  have hU :
      HilbertOperator.applyVec U
          (PureState.ket (R := Qubits m) y).vec =
        (PureState.ket (R := Qubits m) (bitwiseXor y (D k))).vec := by
    simpa [U, Gate.applyVec] using congrArg
      (fun ψ : PureState (Qubits m) => (ψ : StateVector (Qubits m)))
      (dataXPower_apply_basis (D k) y)
  have hvec :
      HilbertOperator.applyVec (factorOperator D k)
          (StateVector.tensor
            (PureState.ket (R := Qubits n) x).vec
            (PureState.ket (R := Qubits m) y).vec) =
        if x = k then
          StateVector.tensor
            (PureState.ket (R := Qubits n) k).vec
            (PureState.ket (R := Qubits m) (bitwiseXor y (D k))).vec
        else
          StateVector.tensor
            (PureState.ket (R := Qubits n) x).vec
            (PureState.ket (R := Qubits m) y).vec := by
    rw [hfactor, HilbertOperator.add_applyVec,
      HilbertOperator.tensor_applyVec_tensor,
      HilbertOperator.tensor_applyVec_tensor, hcomplement,
      HilbertOperator.one_applyVec, hprojector, hU]
    by_cases hx : x = k
    · subst x
      simp
    · simp [hx]
  apply PureState.ext
  intro i
  by_cases hx : x = k
  · rw [if_pos hx] at hvec ⊢
    have hi := congrArg
      (fun ψ : StateVector (Qubits (n + m)) => ψ i) hvec
    simpa only [Gate.apply, Gate.applyVec, factorGate, Gate.ofUnitary,
      PureState.tensor, PureState.ofVec] using hi
  · rw [if_neg hx] at hvec ⊢
    have hi := congrArg
      (fun ψ : StateVector (Qubits (n + m)) => ψ i) hvec
    simpa only [Gate.apply, Gate.applyVec, factorGate, Gate.ofUnitary,
      PureState.tensor, PureState.ofVec] using hi

/-- The basis-label update `(x,y) ↦ (x, y ⊕ D(x))`. -/
def qromBasisUpdate {n m : ℕ} (D : Fin (2 ^ n) → Fin (2 ^ m))
    (z : Fin (2 ^ (n + m))) : Fin (2 ^ (n + m)) :=
  let xy := (prodEquiv (m := n) (n := m)).symm z
  prodEquiv (m := n) (n := m) (xy.1, bitwiseXor xy.2 (D xy.1))

/-- The ideal QROM basis update, as an involutive permutation. -/
def qromPerm {n m : ℕ} (D : Fin (2 ^ n) → Fin (2 ^ m)) :
    Equiv.Perm (Fin (2 ^ (n + m))) where
  toFun z := qromBasisUpdate D z
  invFun z := qromBasisUpdate D z
  left_inv := by
    intro z
    simp only [qromBasisUpdate, Equiv.symm_apply_apply]
    have hxor :
        bitwiseXor
            (bitwiseXor (prodEquiv.symm z).2
              (D (prodEquiv.symm z).1))
            (D (prodEquiv.symm z).1) =
          (prodEquiv.symm z).2 := by
      simpa only [bitwiseXorPerm] using
        (bitwiseXorPerm (D (prodEquiv.symm z).1)).left_inv
          (prodEquiv.symm z).2
    rw [hxor]
    exact Equiv.apply_symm_apply prodEquiv z
  right_inv := by
    intro z
    simp only [qromBasisUpdate, Equiv.symm_apply_apply]
    have hxor :
        bitwiseXor
            (bitwiseXor (prodEquiv.symm z).2
              (D (prodEquiv.symm z).1))
            (D (prodEquiv.symm z).1) =
          (prodEquiv.symm z).2 := by
      simpa only [bitwiseXorPerm] using
        (bitwiseXorPerm (D (prodEquiv.symm z).1)).right_inv
          (prodEquiv.symm z).2
    rw [hxor]
    exact Equiv.apply_symm_apply prodEquiv z

/-- The ideal QROM unitary `U_D`. -/
def idealQROM {n m : ℕ} (D : Fin (2 ^ n) → Fin (2 ^ m)) :
    Gate (Qubits (n + m)) :=
  Gate.ofPerm (qromPerm D)

/-- The ideal QROM has the required computational-basis action. -/
theorem idealQROM_apply_basis {n m : ℕ}
    (D : Fin (2 ^ n) → Fin (2 ^ m))
    (x : Fin (2 ^ n)) (y : Fin (2 ^ m)) :
    (idealQROM D).apply
        ((PureState.ket x).tensor (PureState.ket y)) =
      (PureState.ket x).tensor
        (PureState.ket (bitwiseXor y (D x))) := by
  rw [PureState.tensor_ket, PureState.tensor_ket, idealQROM,
    Gate.ofPerm_apply_ket]
  congr 1
  change qromBasisUpdate D (prodEquiv (x, y)) = _
  simp [qromBasisUpdate]

/-- Product of controlled factors in an explicit address schedule.  `foldl`
fixes the otherwise noncommutative product convention. -/
def factorProduct {n m : ℕ} (D : Fin (2 ^ n) → Fin (2 ^ m))
    (schedule : List (Fin (2 ^ n))) : Gate (Qubits (n + m)) :=
  schedule.foldl (fun product k => product * factorGate D k) 1

/-- The canonical schedule `0, 1, ..., 2^n - 1`. -/
def canonicalSchedule (n : ℕ) : List (Fin (2 ^ n)) :=
  List.ofFn fun k => k

/-- Distinct-address controlled factors commute (and the statement also
includes the tautological equal-address case). -/
theorem factorGate_comm {n m : ℕ}
    (D : Fin (2 ^ n) → Fin (2 ^ m)) (k l : Fin (2 ^ n)) :
    factorGate D k * factorGate D l =
      factorGate D l * factorGate D k := by
  by_cases hkl : k = l
  · subst l
    rfl
  apply Gate.ext
  intro i j
  rw [← Gate.apply_ket (factorGate D k * factorGate D l) j i,
    ← Gate.apply_ket (factorGate D l * factorGate D k) j i]
  let xy := (prodEquiv (m := n) (n := m)).symm j
  rw [← show
    (PureState.ket xy.1).tensor (PureState.ket xy.2) =
      PureState.ket j by
        rw [PureState.tensor_ket, Equiv.apply_symm_apply]]
  rw [Gate.mul_apply, Gate.mul_apply]
  by_cases hk : xy.1 = k
  · simp [hk, hkl, factorGate_apply_basis]
  · by_cases hl : xy.1 = l
    · have hlk : l ≠ k := fun h => hkl h.symm
      simp [hl, hlk, factorGate_apply_basis]
    · simp [hk, hl, factorGate_apply_basis]

/-- Reordering an explicit schedule does not change its factor product. -/
theorem factorProduct_eq_of_perm {n m : ℕ}
    (D : Fin (2 ^ n) → Fin (2 ^ m))
    {schedule₁ schedule₂ : List (Fin (2 ^ n))}
    (hperm : schedule₁.Perm schedule₂) :
    factorProduct D schedule₁ = factorProduct D schedule₂ := by
  unfold factorProduct
  have hfold : ∀ p : Gate (Qubits (n + m)),
      schedule₁.foldl (fun product k => product * factorGate D k) p =
        schedule₂.foldl (fun product k => product * factorGate D k) p := by
    intro p
    induction hperm generalizing p with
    | nil => rfl
    | cons a h ih =>
        simpa only [List.foldl] using ih (p * factorGate D a)
    | swap a b l =>
        simp only [List.foldl]
        congr 1
        rw [mul_assoc, factorGate_comm D b a, ← mul_assoc]
    | trans h₁ h₂ ih₁ ih₂ =>
        exact (ih₁ p).trans (ih₂ p)
  exact hfold 1

/-- Exact factorization of the ideal QROM into all address-controlled factors. -/
theorem idealQROM_eq_factorProduct {n m : ℕ}
    (D : Fin (2 ^ n) → Fin (2 ^ m)) :
    idealQROM D = factorProduct D (canonicalSchedule n) := by
  apply Gate.ext
  intro i j
  rw [← Gate.apply_ket (idealQROM D) j i,
    ← Gate.apply_ket (factorProduct D (canonicalSchedule n)) j i]
  let xy := (prodEquiv (m := n) (n := m)).symm j
  have hj :
      (PureState.ket xy.1).tensor (PureState.ket xy.2) =
        PureState.ket j := by
    rw [PureState.tensor_ket, Equiv.apply_symm_apply]
  have hxmem : xy.1 ∈ canonicalSchedule n := by
    simp [canonicalSchedule, List.mem_ofFn]
  have hnodup : (canonicalSchedule n).Nodup := by
    rw [canonicalSchedule, List.nodup_ofFn]
    exact Function.injective_id
  have hxerase : xy.1 ∉ (canonicalSchedule n).erase xy.1 :=
    hnodup.not_mem_erase
  have hfold_noop : ∀ (schedule : List (Fin (2 ^ n)))
      (p : Gate (Qubits (n + m))), xy.1 ∉ schedule →
        (schedule.foldl (fun product k => product * factorGate D k) p).apply
            ((PureState.ket xy.1).tensor (PureState.ket xy.2)) =
          p.apply ((PureState.ket xy.1).tensor (PureState.ket xy.2)) := by
    intro schedule
    induction schedule with
    | nil =>
        intro p h
        rfl
    | cons a schedule ih =>
        intro p h
        simp only [List.mem_cons, not_or] at h
        rw [List.foldl, ih (p * factorGate D a) h.2, Gate.mul_apply,
          factorGate_apply_basis, if_neg h.1]
  have hproduct :
      (factorProduct D (canonicalSchedule n)).apply
          ((PureState.ket xy.1).tensor (PureState.ket xy.2)) =
        (PureState.ket xy.1).tensor
          (PureState.ket (bitwiseXor xy.2 (D xy.1))) := by
    rw [factorProduct_eq_of_perm D (List.perm_cons_erase hxmem)]
    unfold factorProduct
    simp only [List.foldl, one_mul]
    rw [hfold_noop ((canonicalSchedule n).erase xy.1)
      (factorGate D xy.1) hxerase, factorGate_apply_basis, if_pos rfl]
  rw [← hj, idealQROM_apply_basis, hproduct]

end

end ExactQROMFactorization
end QAlgFormalized
