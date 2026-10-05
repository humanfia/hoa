import QAlgBench.Base

/-!
# Controlled-unitary invariant eigenspaces

This file formalizes the standard two-dimensional invariant blocks of a
controlled unitary.  The two coordinates are ordered by the control states
`|0⟩` and `|1⟩`.
-/

namespace QAlgFormalized

open scoped ComplexConjugate
open QAlgBench
open QAlgBench.PureState

noncomputable section

/-- The rank-one operator `|ψ⟩⟨φ|` in the computational basis. -/
def controlledEigenKetBra {n : ℕ}
    (ψ φ : StateVector (Qubits n)) : HilbertOperator (Qubits n) :=
  Matrix.vecMulVec ψ (fun k => starRingEnd ℂ (φ k))

/-- The span of `|0⟩|ψ⟩` and `|1⟩|ψ⟩`. -/
def controlledEigenSubspace {n : ℕ}
    (ψ : StateVector (Qubits n)) : Submodule ℂ (StateVector (Qubits (1 + n))) :=
  Submodule.span ℂ
    {StateVector.tensor (ket0 : StateVector (Qubits 1)) ψ,
      StateVector.tensor (ket1 : StateVector (Qubits 1)) ψ}

/-- The ordered coordinate map
`(a,b) ↦ a |0⟩|ψ⟩ + b |1⟩|ψ⟩` for the controlled eigenspace. -/
def controlledEigenCoordinates {n : ℕ}
    (ψ : StateVector (Qubits n)) (c : Fin 2 → ℂ) :
    StateVector (Qubits (1 + n)) :=
  c 0 • StateVector.tensor (ket0 : StateVector (Qubits 1)) ψ
    + c 1 • StateVector.tensor (ket1 : StateVector (Qubits 1)) ψ

/-- The expected matrix of a controlled unitary on the block belonging to an
eigenphase `x`. -/
def controlledEigenBlock (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, Complex.exp (Complex.I * (x : ℂ))]

/-- If `U` has the displayed spectral decomposition, then every eigenvector
defines a two-dimensional invariant subspace for `controlled U`.  In the
ordered coordinates `|0⟩|ψ_j⟩, |1⟩|ψ_j⟩`, the restricted matrix is
`diag(1, exp(i x_j))`. -/
theorem controlled_unitary_invariant_subspaces
    {n : ℕ} {ι : Type} [Fintype ι]
    (U : Gate (Qubits n))
    (x : ι → ℝ)
    (ψ : OrthonormalBasis ι ℂ (StateVector (Qubits n)))
    (h_spectral :
      (U : HilbertOperator (Qubits n)) =
        ∑ j, Complex.exp (Complex.I * (x j : ℂ)) •
          controlledEigenKetBra (ψ j) (ψ j)) :
    ∀ j : ι,
      Module.finrank ℂ (controlledEigenSubspace (ψ j)) = 2 ∧
      Set.MapsTo
        (HilbertOperator.applyVec
          (Gate.controlled U : HilbertOperator (Qubits (1 + n))))
        (controlledEigenSubspace (ψ j))
        (controlledEigenSubspace (ψ j)) ∧
      ∀ c : Fin 2 → ℂ,
        HilbertOperator.applyVec
            (Gate.controlled U : HilbertOperator (Qubits (1 + n)))
            (controlledEigenCoordinates (ψ j) c) =
          controlledEigenCoordinates (ψ j)
            ((controlledEigenBlock (x j)).mulVec c) := by
  classical
  intro j
  have h_eigen :
      U.applyVec (ψ j) =
        Complex.exp (Complex.I * (x j : ℂ)) • ψ j := by
    have h_rank (i : ι) :
        HilbertOperator.applyVec
            (controlledEigenKetBra (ψ i) (ψ i)) (ψ j) =
          if i = j then ψ j else 0 := by
      have hinner := orthonormal_iff_ite.mp ψ.orthonormal i j
      rw [PiLp.inner_apply] at hinner
      simp only [RCLike.inner_apply] at hinner
      ext k
      rw [HilbertOperator.applyVec_apply]
      change
        (∑ t, ((ψ i) k * starRingEnd ℂ ((ψ i) t)) * (ψ j) t) = _
      calc
        _ = (ψ i) k *
              (∑ t, (ψ j) t * starRingEnd ℂ ((ψ i) t)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          ring
        _ = (ψ i) k * (if i = j then 1 else 0) := by rw [hinner]
        _ = (if i = j then ψ j else 0) k := by
          split_ifs with hij
          · subst i
            simp
          · simp
    rw [Gate.applyVec, h_spectral, HilbertOperator.sum_applyVec]
    simp only [HilbertOperator.smul_applyVec, h_rank]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      simp [hij]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  have h_dim :
      Module.finrank ℂ (controlledEigenSubspace (ψ j)) = 2 := by
    let v0 :=
      StateVector.tensor (ket0 : StateVector (Qubits 1)) (ψ j)
    let v1 :=
      StateVector.tensor (ket1 : StateVector (Qubits 1)) (ψ j)
    let v : Fin 2 → StateVector (Qubits (1 + n)) := ![v0, v1]
    have hv : LinearIndependent ℂ v := by
      rw [linearIndependent_fin2]
      constructor
      · intro hzero
        have hnorm := congrArg norm hzero
        simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one] at hnorm
        dsimp [v1] at hnorm
        rw [StateVector.norm_tensor, ket1.norm_eq_one,
          ψ.orthonormal.norm_eq_one, one_mul, norm_zero] at hnorm
        exact one_ne_zero hnorm
      · intro a ha
        simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one] at ha
        have hi := congrArg
          (fun w : StateVector (Qubits (1 + n)) => inner ℂ v0 w) ha
        dsimp [v0, v1] at hi
        rw [inner_smul_right, StateVector.inner_tensor_tensor,
          StateVector.inner_tensor_tensor] at hi
        have h01 :
            inner ℂ (ket0 : StateVector (Qubits 1))
              (ket1 : StateVector (Qubits 1)) = 0 := by
          rw [PiLp.inner_apply]
          simp [RCLike.inner_apply, ket0, ket1, PureState.ket]
        have h00 :
            inner ℂ (ket0 : StateVector (Qubits 1))
              (ket0 : StateVector (Qubits 1)) = 1 := by
          rw [inner_self_eq_norm_sq_to_K, ket0.norm_eq_one]
          norm_num
        have hψ : inner ℂ (ψ j) (ψ j) = 1 :=
          (orthonormal_iff_ite.mp ψ.orthonormal j j).trans (if_pos rfl)
        rw [h01, h00, hψ] at hi
        norm_num at hi
    have hrange : Set.range v = {v0, v1} := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [v]
      · intro hz
        rcases hz with (rfl | rfl)
        · exact ⟨0, by simp [v]⟩
        · exact ⟨1, by simp [v]⟩
    change Module.finrank ℂ (Submodule.span ℂ {v0, v1}) = 2
    rw [← hrange, finrank_span_eq_card hv, Fintype.card_fin]
  have h_invariant :
      Set.MapsTo
        (HilbertOperator.applyVec
          (Gate.controlled U : HilbertOperator (Qubits (1 + n))))
        (controlledEigenSubspace (ψ j))
        (controlledEigenSubspace (ψ j)) := by
    intro z hz
    rw [controlledEigenSubspace] at hz ⊢
    rcases Submodule.mem_span_pair.mp hz with ⟨a, b, rfl⟩
    rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
      HilbertOperator.applyVec_smul, Gate.controlled_applyVec_ket0_tensor,
      Gate.controlled_applyVec_ket1_tensor]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (by simp))
    · rw [h_eigen, StateVector.tensor_smul]
      exact Submodule.smul_mem _ _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have h_coordinates :
      ∀ c : Fin 2 → ℂ,
        HilbertOperator.applyVec
            (Gate.controlled U : HilbertOperator (Qubits (1 + n)))
            (controlledEigenCoordinates (ψ j) c) =
          controlledEigenCoordinates (ψ j)
            ((controlledEigenBlock (x j)).mulVec c) := by
    intro c
    rw [controlledEigenCoordinates, HilbertOperator.applyVec_add,
      HilbertOperator.applyVec_smul, HilbertOperator.applyVec_smul,
      Gate.controlled_applyVec_ket0_tensor,
      Gate.controlled_applyVec_ket1_tensor, h_eigen,
      StateVector.tensor_smul]
    unfold controlledEigenCoordinates controlledEigenBlock
    congr 1
    · simp [Matrix.mulVec, dotProduct]
    · rw [← smul_assoc]
      congr 1
      simp [Matrix.mulVec, dotProduct, mul_comm]
  exact ⟨h_dim, h_invariant, h_coordinates⟩

end

end QAlgFormalized
