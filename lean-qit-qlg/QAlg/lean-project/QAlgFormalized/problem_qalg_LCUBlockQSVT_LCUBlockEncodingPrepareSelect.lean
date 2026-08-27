import QAlgBench.Base

/-!
# PREPARE/SELECT block encoding for a linear combination of unitaries

The equivalence `basisIndex : L ≃ Fin (2 ^ a)` identifies the finite index
set `L` with the full computational basis of an `a`-qubit ancilla.  The
system is an `n`-qubit register.
-/

open scoped BigOperators

namespace QAlgFormalized.LCUBlockEncodingPrepareSelect

open QAlgBench

noncomputable section

variable {L : Type} [Fintype L] [DecidableEq L] {a n : ℕ}

/-- The coefficient one-norm
`α = ∑ ℓ, α_ℓ` of a linear combination of unitaries. -/
def coefficientOneNorm (coeff : L → ℝ) : ℝ :=
  ∑ ℓ, coeff ℓ

/-- The system operator `A = ∑ ℓ, α_ℓ U_ℓ`. -/
def lcuOperator (coeff : L → ℝ)
    (U : L → Gate (Qubits n)) : HilbertOperator (Qubits n) :=
  ∑ ℓ, (coeff ℓ : ℂ) • (U ℓ : HilbertOperator (Qubits n))

/-- The normalized ancilla state prepared by `P`:
`(1 / √α) ∑ ℓ, √α_ℓ |ℓ⟩`. -/
def prepareVector (basisIndex : L ≃ Fin (2 ^ a)) (coeff : L → ℝ) :
    StateVector (Qubits a) :=
  ((((Real.sqrt (coefficientOneNorm coeff))⁻¹ : ℝ) : ℂ)) •
    ∑ ℓ, (Real.sqrt (coeff ℓ) : ℂ) •
      (PureState.ket (R := Qubits a) (basisIndex ℓ) :
        StateVector (Qubits a))

/-- The PREPARE condition
`P |0^a⟩ = (1 / √α) ∑ ℓ, √α_ℓ |ℓ⟩`. -/
def IsPrepare (basisIndex : L ≃ Fin (2 ^ a)) (coeff : L → ℝ)
    (P : Gate (Qubits a)) : Prop :=
  P.applyVec
      (PureState.ket (R := Qubits a) (0 : Fin (2 ^ a)) :
        StateVector (Qubits a)) =
    prepareVector basisIndex coeff

/-- The SELECT operator
`∑ ℓ, |ℓ⟩⟨ℓ| ⊗ U_ℓ`. -/
def selectOperator (basisIndex : L ≃ Fin (2 ^ a))
    (U : L → Gate (Qubits n)) :
    HilbertOperator (Qubits (a + n)) :=
  ∑ ℓ, HilbertOperator.tensor
    (OrthogonalProjector.basisOp (basisIndex ℓ))
    (U ℓ : HilbertOperator (Qubits n))

/-- SELECT is unitary when each selected system operator is a unitary gate. -/
theorem selectOperator_mem_unitaryGroup
    (basisIndex : L ≃ Fin (2 ^ a))
    (U : L → Gate (Qubits n)) :
    selectOperator basisIndex U ∈
      Matrix.unitaryGroup (Fin (2 ^ (a + n))) ℂ := by
  have hselect (r c : Fin (2 ^ (a + n))) :
      selectOperator basisIndex U r c =
        if (prodEquiv.symm r).1 = (prodEquiv.symm c).1 then
          U (basisIndex.symm (prodEquiv.symm r).1)
            (prodEquiv.symm r).2 (prodEquiv.symm c).2
        else 0 := by
    rw [selectOperator, Matrix.sum_apply]
    simp only [HilbertOperator.tensor_apply,
      OrthogonalProjector.basisOp, Matrix.of_apply]
    rw [Fintype.sum_eq_single (basisIndex.symm (prodEquiv.symm r).1)]
    · simp [eq_comm]
    · intro b hb
      have hne : (prodEquiv.symm r).1 ≠ basisIndex b := by
        intro h
        apply hb
        simpa using (congrArg basisIndex.symm h).symm
      simp [hne]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hselect]
  rw [← Equiv.sum_comp (prodEquiv (m := a) (n := n)),
    Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply]
  by_cases hij : (prodEquiv.symm i).1 = (prodEquiv.symm j).1
  · simp only [hij]
    have hU := Matrix.mem_unitaryGroup_iff.mp
      (U (basisIndex.symm (prodEquiv.symm j).1)).unitary
    rw [Matrix.star_eq_conjTranspose] at hU
    have hentry := congrFun (congrFun hU (prodEquiv.symm i).2)
      (prodEquiv.symm j).2
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at hentry
    have heq : i = j ↔ (prodEquiv.symm i).2 = (prodEquiv.symm j).2 := by
      constructor
      · exact fun h => congrArg (fun z => (prodEquiv.symm z).2) h
      · intro h
        apply prodEquiv.symm.injective
        exact Prod.ext hij h
    simpa [Matrix.one_apply, heq] using hentry
  · have hji : (prodEquiv.symm j).1 ≠ (prodEquiv.symm i).1 := Ne.symm hij
    have hneij : i ≠ j := by
      intro h
      apply hij
      exact congrArg (fun z => (prodEquiv.symm z).1) h
    simp [hji, hneij]

/-- SELECT bundled as a unitary gate. -/
def selectGate (basisIndex : L ≃ Fin (2 ^ a))
    (U : L → Gate (Qubits n)) :
    Gate (Qubits (a + n)) :=
  Gate.ofUnitary (selectOperator basisIndex U)
    (selectOperator_mem_unitaryGroup basisIndex U)

/-- The PREPARE/SELECT walk
`W = (P† ⊗ I_S) SELECT (P ⊗ I_S)`. -/
def lcuWalk (P : Gate (Qubits a))
    (basisIndex : L ≃ Fin (2 ^ a))
    (U : L → Gate (Qubits n)) : Gate (Qubits (a + n)) :=
  P.conjTranspose.tensor (1 : Gate (Qubits n)) *
    selectGate basisIndex U *
    P.tensor (1 : Gate (Qubits n))

/-- If all coefficients are positive, then their one-norm is positive. -/
theorem coefficientOneNorm_pos (basisIndex : L ≃ Fin (2 ^ a))
    (coeff : L → ℝ)
    (hcoeff : ∀ ℓ, 0 < coeff ℓ) :
    0 < coefficientOneNorm coeff := by
  unfold coefficientOneNorm
  exact Finset.sum_pos (fun ℓ _ => hcoeff ℓ)
    ⟨basisIndex.symm 0, Finset.mem_univ _⟩

/-- The all-zero ancilla block of the PREPARE/SELECT walk is exactly
`A / α`.  This is the matrix form of
`(⟨0^a| ⊗ I_S) W (|0^a⟩ ⊗ I_S) = A / α`. -/
theorem projectedBlock_lcuWalk
    (basisIndex : L ≃ Fin (2 ^ a))
    (coeff : L → ℝ)
    (U : L → Gate (Qubits n))
    (P : Gate (Qubits a))
    (hcoeff : ∀ ℓ, 0 < coeff ℓ)
    (hprepare : IsPrepare basisIndex coeff P) :
    projectedBlock a n
        (lcuWalk P basisIndex U : HilbertOperator (Qubits (a + n))) =
      ((coefficientOneNorm coeff : ℂ)⁻¹) • lcuOperator coeff U := by
  have hP (ℓ : L) :
      P (basisIndex ℓ) (0 : Fin (2 ^ a)) =
        (((Real.sqrt (coefficientOneNorm coeff))⁻¹ : ℝ) : ℂ) *
          (Real.sqrt (coeff ℓ) : ℂ) := by
    have hp := congrArg
      (fun v : StateVector (Qubits a) => v (basisIndex ℓ)) hprepare
    simpa [IsPrepare, prepareVector, Gate.applyVec,
      HilbertOperator.applyVec_ket, PureState.ket_apply] using hp
  have halpha := coefficientOneNorm_pos basisIndex coeff hcoeff
  have hanc (ℓ : L) :
      (((P : HilbertOperator (Qubits a)).conjTranspose *
        OrthogonalProjector.basisOp (basisIndex ℓ)) *
        (P : HilbertOperator (Qubits a))) 0 0 =
        (coefficientOneNorm coeff : ℂ)⁻¹ * (coeff ℓ : ℂ) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
      OrthogonalProjector.basisOp, hP]
    norm_cast
    field_simp
    nlinarith [Real.sq_sqrt (le_of_lt halpha),
      Real.sq_sqrt (le_of_lt (hcoeff ℓ))]
  have hwalk :
      (lcuWalk P basisIndex U : HilbertOperator (Qubits (a + n))) =
        ∑ ℓ, HilbertOperator.tensor
          (((P : HilbertOperator (Qubits a)).conjTranspose *
            OrthogonalProjector.basisOp (basisIndex ℓ)) *
            (P : HilbertOperator (Qubits a)))
          (U ℓ : HilbertOperator (Qubits n)) := by
    simp only [lcuWalk, Gate.coe_mul, Gate.coe_conjTranspose,
      Gate.coe_one, Gate.tensor, Gate.coe_ofUnitary, selectGate]
    rw [selectOperator, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [HilbertOperator.tensor_mul_tensor,
      HilbertOperator.tensor_mul_tensor]
    simp
  rw [hwalk]
  ext i j
  simp [projectedBlock, Matrix.sum_apply, HilbertOperator.tensor_apply,
    hanc, lcuOperator]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [mul_assoc]

/-- Consequently `W` is a perfect
`(α, a, 0)` block encoding of `A`. -/
theorem lcuWalk_isBlockEncoding
    (basisIndex : L ≃ Fin (2 ^ a))
    (coeff : L → ℝ)
    (U : L → Gate (Qubits n))
    (P : Gate (Qubits a))
    (hcoeff : ∀ ℓ, 0 < coeff ℓ)
    (hprepare : IsPrepare basisIndex coeff P) :
    BlockEncoding (coefficientOneNorm coeff) a n 0
      (lcuWalk P basisIndex U) (lcuOperator coeff U) := by
  apply ExactBlockEncoding.toScaledBlockEncoding
    (coefficientOneNorm_pos basisIndex coeff hcoeff)
  rw [exactBlockEncoding_iff_projectedBlock]
  exact projectedBlock_lcuWalk basisIndex coeff U P hcoeff hprepare

end

end QAlgFormalized.LCUBlockEncodingPrepareSelect
