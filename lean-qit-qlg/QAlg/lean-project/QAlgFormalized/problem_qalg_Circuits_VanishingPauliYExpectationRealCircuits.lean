import QAlgBench.Base

/-!
# Vanishing Pauli-Y expectation for real circuits

This file formalizes the fact that a real unitary circuit prepares a real state
from the all-zero computational-basis state, and that purely imaginary
skew-symmetric observables have zero expectation on real normalized states.
-/

namespace QAlgFormalized
namespace VanishingPauliYExpectationRealCircuits

open QAlgBench

noncomputable section

/-- A state vector is real in the distinguished computational basis. -/
def IsRealState {R : Register} (ψ : PureState R) : Prop :=
  ∀ i, starRingEnd ℂ (ψ i) = ψ i

/-- A Hilbert operator has real entries in the distinguished computational basis. -/
def IsRealOperator {R : Register} (A : HilbertOperator R) : Prop :=
  ∀ i j, starRingEnd ℂ (A i j) = A i j

/-- Every entry of a Hilbert operator is purely imaginary. -/
def IsPurelyImaginary {R : Register} (A : HilbertOperator R) : Prop :=
  ∀ i j, starRingEnd ℂ (A i j) = -A i j

/-- A Hilbert operator is skew-symmetric with respect to the computational basis. -/
def IsSkewSymmetric {R : Register} (A : HilbertOperator R) : Prop :=
  A.transpose = -A

/-- A Hilbert operator is a quantum observable exactly when it is self-adjoint. -/
def IsObservable {R : Register} (A : HilbertOperator R) : Prop :=
  A.conjTranspose = A

/-- The full complex matrix element `⟨ψ|A|ψ⟩`. -/
def complexExpectation {R : Register} (ψ : PureState R) (A : HilbertOperator R) : ℂ :=
  inner ℂ (ψ : StateVector R)
    (HilbertOperator.applyVec A (ψ : StateVector R))

/-- The state `U |0^n⟩` produced by an `n`-qubit circuit. -/
def circuitOutput {n : ℕ} (U : Gate (Qubits n)) : PureState (Qubits n) :=
  U.apply (PureState.ket 0)

/-- Pauli `Y` on zero-indexed qubit `k`, and the identity on every other qubit. -/
def pauliYAt {n : ℕ} (k : Fin n) : HilbertOperator (Qubits n) := by
  have hdim : k.1 + (1 + (n - (k.1 + 1))) = n := by omega
  exact cast (congrArg (fun q => HilbertOperator (Qubits q)) hdim)
    (HilbertOperator.tensor (1 : HilbertOperator (Qubits k.1))
      (HilbertOperator.tensor Gate.YOp
        (1 : HilbertOperator (Qubits (n - (k.1 + 1))))))

/-- For a real matrix, transpose and conjugate transpose coincide. -/
theorem transpose_eq_conjTranspose_of_real {R : Register} (A : HilbertOperator R)
    (hA : IsRealOperator A) :
    A.transpose = A.conjTranspose := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.conjTranspose_apply]
  exact (hA j i).symm

/-- A real unitary circuit is orthogonal: its transpose is its adjoint. -/
theorem real_gate_transpose_eq_adjoint {R : Register} (U : Gate R)
    (hU : IsRealOperator (U : HilbertOperator R)) :
    (U : HilbertOperator R).transpose = (U : HilbertOperator R).conjTranspose := by
  exact transpose_eq_conjTranspose_of_real (U : HilbertOperator R) hU

/-- In particular, a real unitary circuit satisfies the orthogonality equation. -/
theorem real_gate_transpose_mul_self {R : Register} (U : Gate R)
    (hU : IsRealOperator (U : HilbertOperator R)) :
    (U : HilbertOperator R).transpose * (U : HilbertOperator R) = 1 := by
  rw [real_gate_transpose_eq_adjoint U hU, ← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp U.unitary

/-- A circuit with a real computational-basis matrix sends `|0^n⟩` to a real state. -/
theorem circuitOutput_isReal {n : ℕ} (U : Gate (Qubits n))
    (hU : IsRealOperator (U : HilbertOperator (Qubits n))) :
    IsRealState (circuitOutput U) := by
  intro i
  rw [circuitOutput, Gate.apply_ket]
  exact hU i 0

/-- Pure imaginary entries and skew symmetry make an operator self-adjoint. -/
theorem isObservable_of_purelyImaginary_of_skewSymmetric {R : Register}
    (A : HilbertOperator R) (hAImag : IsPurelyImaginary A)
    (hASkew : IsSkewSymmetric A) :
    IsObservable A := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  change starRingEnd ℂ (A j i) = A i j
  rw [hAImag j i]
  have h := congrFun (congrFun hASkew i) j
  change A j i = -A i j at h
  rw [h]
  simp

private theorem isPurelyImaginary_cast_qubits {m n : ℕ} (h : m = n)
    (A : HilbertOperator (Qubits m)) (hA : IsPurelyImaginary A) :
    IsPurelyImaginary
      (cast (congrArg (fun q => HilbertOperator (Qubits q)) h) A) := by
  subst n
  simpa using hA

private theorem isSkewSymmetric_cast_qubits {m n : ℕ} (h : m = n)
    (A : HilbertOperator (Qubits m)) (hA : IsSkewSymmetric A) :
    IsSkewSymmetric
      (cast (congrArg (fun q => HilbertOperator (Qubits q)) h) A) := by
  subst n
  simpa using hA

private theorem isPurelyImaginary_tensor_of_real_of_purelyImaginary
    {m n : ℕ} (G : HilbertOperator (Qubits m))
    (K : HilbertOperator (Qubits n)) (hG : IsRealOperator G)
    (hK : IsPurelyImaginary K) :
    IsPurelyImaginary (HilbertOperator.tensor G K) := by
  intro i j
  rw [HilbertOperator.tensor_apply, map_mul, hG, hK]
  ring

private theorem isPurelyImaginary_tensor_of_purelyImaginary_of_real
    {m n : ℕ} (G : HilbertOperator (Qubits m))
    (K : HilbertOperator (Qubits n)) (hG : IsPurelyImaginary G)
    (hK : IsRealOperator K) :
    IsPurelyImaginary (HilbertOperator.tensor G K) := by
  intro i j
  rw [HilbertOperator.tensor_apply, map_mul, hG, hK]
  ring

private theorem isSkewSymmetric_tensor_of_symmetric_of_skewSymmetric
    {m n : ℕ} (G : HilbertOperator (Qubits m))
    (K : HilbertOperator (Qubits n)) (hG : G.transpose = G)
    (hK : IsSkewSymmetric K) :
    IsSkewSymmetric (HilbertOperator.tensor G K) := by
  ext i j
  rw [Matrix.transpose_apply, HilbertOperator.tensor_apply]
  change
    G (prodEquiv.symm j).1 (prodEquiv.symm i).1
          * K (prodEquiv.symm j).2 (prodEquiv.symm i).2 =
      -(HilbertOperator.tensor G K i j)
  rw [HilbertOperator.tensor_apply]
  have hGij := congrFun
    (congrFun hG (prodEquiv.symm i).1) (prodEquiv.symm j).1
  have hKij := congrFun
    (congrFun hK (prodEquiv.symm i).2) (prodEquiv.symm j).2
  change G (prodEquiv.symm j).1 (prodEquiv.symm i).1 =
    G (prodEquiv.symm i).1 (prodEquiv.symm j).1 at hGij
  change K (prodEquiv.symm j).2 (prodEquiv.symm i).2 =
    -K (prodEquiv.symm i).2 (prodEquiv.symm j).2 at hKij
  rw [hGij, hKij]
  ring

private theorem isSkewSymmetric_tensor_of_skewSymmetric_of_symmetric
    {m n : ℕ} (G : HilbertOperator (Qubits m))
    (K : HilbertOperator (Qubits n)) (hG : IsSkewSymmetric G)
    (hK : K.transpose = K) :
    IsSkewSymmetric (HilbertOperator.tensor G K) := by
  ext i j
  rw [Matrix.transpose_apply, HilbertOperator.tensor_apply]
  change
    G (prodEquiv.symm j).1 (prodEquiv.symm i).1
          * K (prodEquiv.symm j).2 (prodEquiv.symm i).2 =
      -(HilbertOperator.tensor G K i j)
  rw [HilbertOperator.tensor_apply]
  have hGij := congrFun
    (congrFun hG (prodEquiv.symm i).1) (prodEquiv.symm j).1
  have hKij := congrFun
    (congrFun hK (prodEquiv.symm i).2) (prodEquiv.symm j).2
  change G (prodEquiv.symm j).1 (prodEquiv.symm i).1 =
    -G (prodEquiv.symm i).1 (prodEquiv.symm j).1 at hGij
  change K (prodEquiv.symm j).2 (prodEquiv.symm i).2 =
    K (prodEquiv.symm i).2 (prodEquiv.symm j).2 at hKij
  rw [hGij, hKij]
  ring

/-- The local Pauli `Y` operator has purely imaginary computational-basis entries. -/
theorem pauliYAt_isPurelyImaginary {n : ℕ} (k : Fin n) :
    IsPurelyImaginary (pauliYAt k) := by
  unfold pauliYAt
  apply isPurelyImaginary_cast_qubits
  · omega
  apply isPurelyImaginary_tensor_of_real_of_purelyImaginary
  · intro i j
    simp [Matrix.one_apply]
  · apply isPurelyImaginary_tensor_of_purelyImaginary_of_real
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [Gate.YOp]
    · intro i j
      simp [Matrix.one_apply]

/-- The local Pauli `Y` operator is skew-symmetric in the computational basis. -/
theorem pauliYAt_isSkewSymmetric {n : ℕ} (k : Fin n) :
    IsSkewSymmetric (pauliYAt k) := by
  unfold pauliYAt
  apply isSkewSymmetric_cast_qubits
  · omega
  apply isSkewSymmetric_tensor_of_symmetric_of_skewSymmetric
  · ext i j
    simp [Matrix.transpose_apply, Matrix.one_apply, eq_comm]
  · apply isSkewSymmetric_tensor_of_skewSymmetric_of_symmetric
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Gate.YOp, Matrix.transpose_apply]
    · ext i j
      simp [Matrix.transpose_apply, Matrix.one_apply, eq_comm]

/-- The local Pauli `Y` operator is an observable. -/
theorem pauliYAt_isObservable {n : ℕ} (k : Fin n) :
    IsObservable (pauliYAt k) := by
  exact isObservable_of_purelyImaginary_of_skewSymmetric
    (pauliYAt k) (pauliYAt_isPurelyImaginary k)
      (pauliYAt_isSkewSymmetric k)

/-- Every purely imaginary skew-symmetric observable has zero complex expectation
on every real normalized pure state. -/
theorem complexExpectation_eq_zero_of_real_of_purelyImaginary_of_skewSymmetric
    {R : Register} (ψ : PureState R) (A : HilbertOperator R)
    (hψ : IsRealState ψ) (hAImag : IsPurelyImaginary A)
    (hASkew : IsSkewSymmetric A) :
    complexExpectation ψ A = 0 := by
  classical
  have hAObs : IsObservable A :=
    isObservable_of_purelyImaginary_of_skewSymmetric A hAImag hASkew
  have hskew : ∀ i j, A j i = -A i j := by
    intro i j
    have h := congrFun (congrFun hAObs i) j
    change starRingEnd ℂ (A j i) = A i j at h
    rw [hAImag j i] at h
    exact neg_eq_iff_eq_neg.mp h
  unfold complexExpectation
  simp only [PiLp.inner_apply, RCLike.inner_apply,
    HilbertOperator.applyVec_apply]
  change (∑ i, (∑ j, A i j * ψ j) * starRingEnd ℂ (ψ i)) = 0
  unfold IsRealState at hψ
  simp_rw [hψ]
  simp_rw [Finset.sum_mul]
  let S : ℂ := ∑ i, ∑ j, A i j * ψ j * ψ i
  change S = 0
  have hneg : S = -S := by
    dsimp only [S]
    calc
      (∑ i, ∑ j, A i j * ψ j * ψ i)
          = ∑ j, ∑ i, A j i * ψ i * ψ j := by
              rw [Finset.sum_comm]
      _ = ∑ j, ∑ i, -(A i j * ψ j * ψ i) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hskew i j]
              ring
      _ = -(∑ i, ∑ j, A i j * ψ j * ψ i) := by
              rw [Finset.sum_comm]
              simp
  have hsum : S + S = 0 := by
    rw [eq_neg_iff_add_eq_zero] at hneg
    exact hneg
  calc
    S = (1 / 2 : ℂ) * (S + S) := by ring
    _ = 0 := by rw [hsum, mul_zero]

/-- For every valid qubit position, Pauli `Y` has zero expectation in the state
prepared from `|0^n⟩` by a real unitary circuit. -/
theorem vanishing_pauliY_expectation_real_circuit {n : ℕ} (U : Gate (Qubits n))
    (hU : IsRealOperator (U : HilbertOperator (Qubits n))) :
    ∀ k : Fin n, complexExpectation (circuitOutput U) (pauliYAt k) = 0 := by
  intro k
  exact
    complexExpectation_eq_zero_of_real_of_purelyImaginary_of_skewSymmetric
      (circuitOutput U) (pauliYAt k) (circuitOutput_isReal U hU)
        (pauliYAt_isPurelyImaginary k) (pauliYAt_isSkewSymmetric k)

end

end VanishingPauliYExpectationRealCircuits
end QAlgFormalized
