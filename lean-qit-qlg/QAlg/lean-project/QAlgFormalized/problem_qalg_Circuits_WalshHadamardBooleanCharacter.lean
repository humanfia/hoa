import QAlgBench.Base

/-!
# Walsh--Hadamard transform of a Boolean character

An `n`-bit string is represented by its big-endian computational-basis label
in `Fin (2 ^ n)`.  The individual bits are read with `Nat.testBit`; this only
chooses an order for the coordinates and does not change the Boolean dot
product.
-/

namespace QAlgFormalized.WalshHadamardBooleanCharacter

open QAlgBench

noncomputable section

/-- The `j`-th bit of a computational-basis label, regarded as a natural
number in `{0, 1}`. -/
def bitValue {n : ℕ} (x : Fin (2 ^ n)) (j : Fin n) : ℕ :=
  if Nat.testBit x.val j.val then 1 else 0

/-- The Boolean dot product
`s · y = (∑ j, s_j y_j) mod 2`. -/
def booleanDot {n : ℕ} (s y : Fin (2 ^ n)) : Fin 2 :=
  ⟨(∑ j : Fin n, bitValue s j * bitValue y j) % 2,
    Nat.mod_lt _ (by decide)⟩

/-- The raw Boolean-character vector
`2^{-n/2} ∑ y, (-1)^(s · y) |y⟩`.

In coordinates, the coefficient `2^{-n/2}` is written as
`PureState.invSqrt2 ^ n`. -/
def booleanCharacterVec {n : ℕ} (s : Fin (2 ^ n)) :
    StateVector (Qubits n) :=
  WithLp.toLp 2 fun y =>
    PureState.invSqrt2 ^ n * (-1 : ℂ) ^ (booleanDot s y).val

private lemma pair_val_eq_bit {n : ℕ} (x : Fin (2 ^ n)) (b : Fin 2) :
    (prodEquiv (m := n) (n := 1) (x, b)).val =
      Nat.bit (b.val == 1) x.val := by
  rw [show (prodEquiv (m := n) (n := 1) (x, b)).val =
    b.val + 2 * x.val by rfl]
  fin_cases b <;> simp [Nat.bit, add_comm]

private lemma bitValue_pair_zero {n : ℕ} (x : Fin (2 ^ n)) (b : Fin 2) :
    bitValue (prodEquiv (m := n) (n := 1) (x, b)) (0 : Fin (n + 1)) =
      b.val := by
  unfold bitValue
  rw [pair_val_eq_bit]
  change
    (if Nat.testBit (Nat.bit (b.val == 1) x.val) 0 then 1 else 0) = b.val
  rw [Nat.testBit_bit_zero]
  fin_cases b <;> simp

private lemma bitValue_pair_succ {n : ℕ} (x : Fin (2 ^ n)) (b : Fin 2)
    (j : Fin n) :
    bitValue (prodEquiv (m := n) (n := 1) (x, b)) j.succ =
      bitValue x j := by
  unfold bitValue
  rw [pair_val_eq_bit]
  change
    (if Nat.testBit (Nat.bit (b.val == 1) x.val) (Nat.succ j.val)
      then 1 else 0) = _
  rw [Nat.testBit_bit_succ]

private lemma bitValue_fin_two (b : Fin 2) (j : Fin 1) :
    bitValue b j = b.val := by
  fin_cases b <;> fin_cases j <;>
    simp [bitValue, Nat.testBit, Nat.shiftRight_eq_div_pow]

private lemma booleanDot_fin_two (b d : Fin 2) :
    (booleanDot (n := 1) b d).val = (b.val * d.val) % 2 := by
  simp [booleanDot, bitValue_fin_two]

private lemma booleanDot_pair {n : ℕ} (s y : Fin (2 ^ n)) (b d : Fin 2) :
    (booleanDot (prodEquiv (m := n) (n := 1) (s, b))
      (prodEquiv (m := n) (n := 1) (y, d))).val =
        ((booleanDot s y).val + (booleanDot (n := 1) b d).val) % 2 := by
  rw [booleanDot_fin_two]
  simp only [booleanDot, Fin.sum_univ_succ, bitValue_pair_zero,
    bitValue_pair_succ]
  omega

private lemma neg_one_pow_add_mod_two (a b : Fin 2) :
    (-1 : ℂ) ^ ((a.val + b.val) % 2) =
      (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val := by
  fin_cases a <;> fin_cases b <;> norm_num

private lemma booleanCharacterVec_pair {n : ℕ} (s : Fin (2 ^ n)) (b : Fin 2) :
    booleanCharacterVec (prodEquiv (m := n) (n := 1) (s, b)) =
      StateVector.tensor (booleanCharacterVec s)
        (booleanCharacterVec (n := 1) b) := by
  apply WithLp.ofLp_injective
  funext i
  change booleanCharacterVec (prodEquiv (s, b)) i =
    StateVector.tensor (booleanCharacterVec s) (booleanCharacterVec b) i
  rw [← prodEquiv.apply_symm_apply i, StateVector.tensor_apply_prod]
  unfold booleanCharacterVec
  simp only []
  rw [booleanDot_pair, neg_one_pow_add_mod_two]
  simp only [pow_succ]
  ring

/-- A Boolean-character vector is normalized. -/
theorem norm_booleanCharacterVec {n : ℕ} (s : Fin (2 ^ n)) :
    ‖booleanCharacterVec s‖ = 1 := by
  induction n with
  | zero =>
      rw [EuclideanSpace.norm_eq]
      simp [booleanCharacterVec, booleanDot]
  | succ n ih =>
      let p := (prodEquiv (m := n) (n := 1)).symm s
      have hs : s = prodEquiv (m := n) (n := 1) p :=
        (prodEquiv (m := n) (n := 1)).apply_symm_apply s |>.symm
      rw [hs, booleanCharacterVec_pair, StateVector.norm_tensor, ih]
      have hone : ‖booleanCharacterVec (n := 1) p.2‖ = 1 := by
        rw [EuclideanSpace.norm_eq]
        simp [booleanCharacterVec]
      rw [hone, mul_one]

/-- The normalized Boolean-character state `|χ_s⟩`. -/
def booleanCharacterState {n : ℕ} (s : Fin (2 ^ n)) :
    PureState (Qubits n) :=
  PureState.ofVec (booleanCharacterVec s) (norm_booleanCharacterVec s)

/-- The tensor power `H^{⊗ n}`, with the zero-fold tensor interpreted as the
identity gate on the zero-qubit register. -/
def walshHadamard : (n : ℕ) → Gate (Qubits n)
  | 0 => 1
  | n + 1 => (walshHadamard n).tensor Gate.H

private lemma booleanCharacterState_pair {n : ℕ}
    (s : Fin (2 ^ n)) (b : Fin 2) :
    booleanCharacterState (prodEquiv (m := n) (n := 1) (s, b)) =
      (booleanCharacterState s).tensor (booleanCharacterState (n := 1) b) := by
  apply PureState.ext
  intro i
  change booleanCharacterVec (prodEquiv (s, b)) i =
    StateVector.tensor (booleanCharacterVec s) (booleanCharacterVec b) i
  rw [booleanCharacterVec_pair]

private lemma H_apply_booleanCharacterState_one (b : Fin 2) :
    Gate.H.apply (booleanCharacterState (n := 1) b) = PureState.ket b := by
  fin_cases b <;> apply PureState.ext <;> intro i <;> fin_cases i <;>
    rw [Gate.apply_apply] <;>
    simp [Gate.H, Gate.HOp, booleanCharacterState, booleanCharacterVec,
      booleanDot, bitValue, PureState.invSqrt2_mul_self] <;>
    norm_num

/-- Applying `H^{⊗ n}` to the Boolean character indexed by `s` yields the
computational-basis ket `|s⟩`. -/
theorem walshHadamard_apply_booleanCharacter (n : ℕ) (s : Fin (2 ^ n)) :
    (walshHadamard n).apply (booleanCharacterState s) = PureState.ket s := by
  induction n with
  | zero =>
      rw [walshHadamard, Gate.one_apply]
      fin_cases s
      apply PureState.ext
      intro i
      fin_cases i
      simp [booleanCharacterState, booleanCharacterVec, booleanDot]
  | succ n ih =>
      let p := (prodEquiv (m := n) (n := 1)).symm s
      have hs : s = prodEquiv (m := n) (n := 1) p :=
        (prodEquiv (m := n) (n := 1)).apply_symm_apply s |>.symm
      rw [hs, booleanCharacterState_pair]
      change
        ((walshHadamard n).tensor Gate.H).apply
            ((booleanCharacterState p.1).tensor (booleanCharacterState p.2)) =
          PureState.ket (prodEquiv p)
      rw [Gate.tensor_apply_tensor, ih, H_apply_booleanCharacterState_one,
        PureState.tensor_ket]

end

end QAlgFormalized.WalshHadamardBooleanCharacter
