import QAlgBench.Base

/-!
# Third moment from two controlled-SWAP tests

This file models the two auxiliary qubits and the three copies of the data
register by the finite basis

`(A₁ × A₂) × ((B₁ × B₂) × B₃)`.

The explicit product association fixes the register order used by all tensor
products below.
-/

open scoped Kronecker

namespace QAlgFormalized.QSPParameterTrace.ThirdMomentTwoControlledSWAPTests

open QAlgBench

noncomputable section

/-- The computational basis of either auxiliary qubit. -/
abbrev Qubit : Type := (Qubits 1).Index

/-- The ordered data-register basis `((B₁ × B₂) × B₃)`. -/
abbrev DataRegisters (ι : Type) : Type := (ι × ι) × ι

/-- The ordered basis `(A₁ × A₂) × ((B₁ × B₂) × B₃)` of the full system. -/
abbrev FullRegister (ι : Type) : Type := (Qubit × Qubit) × DataRegisters ι

/--
A finite-dimensional density matrix is Hermitian, has nonnegative quadratic
forms, and has unit trace.
-/
def IsDensityMatrix {ι : Type} [Fintype ι] (ρ : Matrix ι ι ℂ) : Prop :=
  ρ.conjTranspose = ρ
    ∧ (∀ v : ι → ℂ,
        0 ≤ (∑ i, ∑ j, star (v i) * ρ i j * v j).re)
    ∧ Matrix.trace ρ = 1

/-- The one-qubit density operator `|+⟩⟨+|`. -/
def plusProjector : Matrix Qubit Qubit ℂ :=
  fun _ _ => (2 : ℂ)⁻¹

/-- The permutation of the three data registers that swaps `B₁` and `B₂`. -/
def swap12Permutation (ι : Type) : Equiv.Perm (DataRegisters ι) where
  toFun x := ((x.1.2, x.1.1), x.2)
  invFun x := ((x.1.2, x.1.1), x.2)
  left_inv := by
    rintro ⟨⟨x₁, x₂⟩, x₃⟩
    rfl
  right_inv := by
    rintro ⟨⟨x₁, x₂⟩, x₃⟩
    rfl

/-- The permutation of the three data registers that swaps `B₁` and `B₃`. -/
def swap13Permutation (ι : Type) : Equiv.Perm (DataRegisters ι) where
  toFun x := ((x.2, x.1.2), x.1.1)
  invFun x := ((x.2, x.1.2), x.1.1)
  left_inv := by
    rintro ⟨⟨x₁, x₂⟩, x₃⟩
    rfl
  right_inv := by
    rintro ⟨⟨x₁, x₂⟩, x₃⟩
    rfl

/-- The permutation matrix `S₁₂` on `B₁B₂B₃`. -/
def swap12Operator {ι : Type} [DecidableEq ι] :
    Matrix (DataRegisters ι) (DataRegisters ι) ℂ :=
  (swap12Permutation ι).permMatrix ℂ

/-- The permutation matrix `S₁₃` on `B₁B₂B₃`. -/
def swap13Operator {ι : Type} [DecidableEq ι] :
    Matrix (DataRegisters ι) (DataRegisters ι) ℂ :=
  (swap13Permutation ι).permMatrix ℂ

/--
`U₁ = |0⟩⟨0|_{A₁} ⊗ I_{A₂} ⊗ I
    + |1⟩⟨1|_{A₁} ⊗ I_{A₂} ⊗ S₁₂`.
-/
def U1 {ι : Type} [DecidableEq ι] :
    Matrix (FullRegister ι) (FullRegister ι) ℂ :=
  ((Gate.proj0 ⊗ₖ (1 : Matrix Qubit Qubit ℂ))
      ⊗ₖ (1 : Matrix (DataRegisters ι) (DataRegisters ι) ℂ))
    +
  ((Gate.proj1 ⊗ₖ (1 : Matrix Qubit Qubit ℂ))
      ⊗ₖ swap12Operator (ι := ι))

/--
`U₂ = I_{A₁} ⊗ |0⟩⟨0|_{A₂} ⊗ I
    + I_{A₁} ⊗ |1⟩⟨1|_{A₂} ⊗ S₁₃`.
-/
def U2 {ι : Type} [DecidableEq ι] :
    Matrix (FullRegister ι) (FullRegister ι) ℂ :=
  (((1 : Matrix Qubit Qubit ℂ) ⊗ₖ Gate.proj0)
      ⊗ₖ (1 : Matrix (DataRegisters ι) (DataRegisters ι) ℂ))
    +
  (((1 : Matrix Qubit Qubit ℂ) ⊗ₖ Gate.proj1)
      ⊗ₖ swap13Operator (ι := ι))

/--
The input state
`|+⟩⟨+|_{A₁} ⊗ |+⟩⟨+|_{A₂} ⊗ ρ_{B₁} ⊗ ρ_{B₂} ⊗ ρ_{B₃}`.
-/
def sigmaIn {ι : Type} (ρ : Matrix ι ι ℂ) :
    Matrix (FullRegister ι) (FullRegister ι) ℂ :=
  (plusProjector ⊗ₖ plusProjector) ⊗ₖ ((ρ ⊗ₖ ρ) ⊗ₖ ρ)

/-- The output state `U₂ U₁ σ_in U₁† U₂†`, in exactly that multiplication order. -/
def sigmaOut {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) :
    Matrix (FullRegister ι) (FullRegister ι) ℂ :=
  U2 (ι := ι) * U1 (ι := ι) * sigmaIn ρ
    * (U1 (ι := ι)).conjTranspose * (U2 (ι := ι)).conjTranspose

/-- The measured observable `X_{A₁} ⊗ X_{A₂} ⊗ I_{B₁B₂B₃}`. -/
def xxObservable {ι : Type} [DecidableEq ι] :
    Matrix (FullRegister ι) (FullRegister ι) ℂ :=
  (((Gate.X : HilbertOperator (Qubits 1))
      ⊗ₖ (Gate.X : HilbertOperator (Qubits 1)))
    ⊗ₖ (1 : Matrix (DataRegisters ι) (DataRegisters ι) ℂ))

/--
Two controlled-SWAP tests measure the third moment of a density matrix:
`tr[(X_{A₁} ⊗ X_{A₂} ⊗ I) σ_out] = tr(ρ³)`.
-/
theorem thirdMoment_twoControlledSWAPTests
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) :
    Matrix.trace (xxObservable (ι := ι) * sigmaOut ρ) = Matrix.trace (ρ ^ 3) := by
  classical
  have hc00 :
      Matrix.trace
          ((Gate.X : HilbertOperator (Qubits 1))
            * (Gate.proj0 * plusProjector * Gate.proj0.conjTranspose)) =
        0 := by
    rw [Matrix.trace_fin_two]
    simp only [Matrix.mul_apply, plusProjector, Gate.proj0, Gate.X, Gate.ofPerm,
      Gate.ofUnitary, Equiv.Perm.permMatrix, PEquiv.toMatrix]
    norm_num
    change (∑ x : Fin 2, (1 / 2 : ℂ) * star (![0, 0] x)) = 0
    rw [Fin.sum_univ_two]
    norm_num
  have hc01 :
      Matrix.trace
          ((Gate.X : HilbertOperator (Qubits 1))
            * (Gate.proj0 * plusProjector * Gate.proj1.conjTranspose)) =
        (2 : ℂ)⁻¹ := by
    rw [Matrix.trace_fin_two]
    simp only [Matrix.mul_apply, plusProjector, Gate.proj0, Gate.proj1, Gate.X,
      Gate.ofPerm, Gate.ofUnitary, Equiv.Perm.permMatrix, PEquiv.toMatrix]
    norm_num
    change (∑ x : Fin 2, (1 / 2 : ℂ) * star (![0, 1] x)) = (1 / 2 : ℂ)
    rw [Fin.sum_univ_two]
    norm_num
  have hc10 :
      Matrix.trace
          ((Gate.X : HilbertOperator (Qubits 1))
            * (Gate.proj1 * plusProjector * Gate.proj0.conjTranspose)) =
        (2 : ℂ)⁻¹ := by
    rw [Matrix.trace_fin_two]
    simp only [Matrix.mul_apply, plusProjector, Gate.proj0, Gate.proj1, Gate.X,
      Gate.ofPerm, Gate.ofUnitary, Equiv.Perm.permMatrix, PEquiv.toMatrix]
    norm_num
    change (∑ x : Fin 2, (1 / 2 : ℂ) * star (![1, 0] x)) = (1 / 2 : ℂ)
    rw [Fin.sum_univ_two]
    norm_num
  have hc11 :
      Matrix.trace
          ((Gate.X : HilbertOperator (Qubits 1))
            * (Gate.proj1 * plusProjector * Gate.proj1.conjTranspose)) =
        0 := by
    rw [Matrix.trace_fin_two]
    simp only [Matrix.mul_apply, plusProjector, Gate.proj1, Gate.X, Gate.ofPerm,
      Gate.ofUnitary, Equiv.Perm.permMatrix, PEquiv.toMatrix]
    norm_num
    change (∑ x : Fin 2, (1 / 2 : ℂ) * star (![0, 0] x)) = 0
    rw [Fin.sum_univ_two]
    norm_num
  have hcontrolled :
      U2 (ι := ι) * U1 (ι := ι) =
        (((Gate.proj0 ⊗ₖ Gate.proj0)
              ⊗ₖ (1 : Matrix (DataRegisters ι) (DataRegisters ι) ℂ))
          +
          ((Gate.proj1 ⊗ₖ Gate.proj0) ⊗ₖ swap12Operator (ι := ι)))
        +
        (((Gate.proj0 ⊗ₖ Gate.proj1) ⊗ₖ swap13Operator (ι := ι))
          +
          ((Gate.proj1 ⊗ₖ Gate.proj1)
            ⊗ₖ (swap13Operator (ι := ι) * swap12Operator (ι := ι)))) := by
    rw [U2, U1, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    simp only [← Matrix.mul_kronecker_mul]
    simp
  have hsigma :
      sigmaOut ρ =
        (U2 (ι := ι) * U1 (ι := ι)) * sigmaIn ρ
          * (U2 (ι := ι) * U1 (ι := ι)).conjTranspose := by
    simp [sigmaOut, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hmeasurement :
      Matrix.trace (xxObservable (ι := ι) * sigmaOut ρ) =
        (4 : ℂ)⁻¹ *
          (Matrix.trace
              (((ρ ⊗ₖ ρ) ⊗ₖ ρ) *
                (swap13Operator (ι := ι) * swap12Operator (ι := ι)).conjTranspose)
            +
            Matrix.trace
              (swap12Operator (ι := ι) * ((ρ ⊗ₖ ρ) ⊗ₖ ρ)
                * (swap13Operator (ι := ι)).conjTranspose)
            +
            Matrix.trace
              (swap13Operator (ι := ι) * ((ρ ⊗ₖ ρ) ⊗ₖ ρ)
                * (swap12Operator (ι := ι)).conjTranspose)
            +
            Matrix.trace
              (swap13Operator (ι := ι) * swap12Operator (ι := ι)
                * ((ρ ⊗ₖ ρ) ⊗ₖ ρ))) := by
    rw [hsigma, hcontrolled]
    simp only [xxObservable, sigmaIn, Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, Matrix.add_mul, Matrix.mul_add]
    simp only [← Matrix.mul_kronecker_mul]
    simp only [Matrix.trace_add, Matrix.trace_kronecker]
    simp only [Matrix.one_mul, Matrix.mul_one, hc00, hc01, hc10, hc11,
      zero_mul, zero_add, mul_zero, add_zero]
    ring
  have hswap12_star :
      (swap12Operator (ι := ι)).conjTranspose = swap12Operator (ι := ι) := by
    rw [swap12Operator, Matrix.conjTranspose_permMatrix]
    congr 1
  have hswap13_star :
      (swap13Operator (ι := ι)).conjTranspose = swap13Operator (ι := ι) := by
    rw [swap13Operator, Matrix.conjTranspose_permMatrix]
    congr 1
  have hcycle12_13 :
      Matrix.trace
          (((ρ ⊗ₖ ρ) ⊗ₖ ρ)
            * (swap12Operator (ι := ι) * swap13Operator (ι := ι))) =
        Matrix.trace (ρ ^ 3) := by
    rw [show
        swap12Operator (ι := ι) * swap13Operator (ι := ι) =
          (swap13Permutation ι * swap12Permutation ι).permMatrix ℂ by
      rw [swap12Operator, swap13Operator, Matrix.permMatrix_mul]]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.kroneckerMap_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]
    simp
    simp only [Fintype.sum_prod_type, swap12Permutation, swap13Permutation]
    simp [pow_succ, Matrix.mul_apply]
    simp_rw [Finset.sum_mul]
    calc
      (∑ x, ∑ y, ∑ z, ρ z x * ρ x y * ρ y z) =
          ∑ x, ∑ z, ∑ y, ρ z x * ρ x y * ρ y z := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.sum_comm]
      _ = ∑ z, ∑ x, ∑ y, ρ z x * ρ x y * ρ y z := by
        rw [Finset.sum_comm]
      _ = ∑ x, ∑ y, ∑ z, ρ x z * ρ z y * ρ y x := by
        symm
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_comm]
  have hcycle13_12 :
      Matrix.trace
          (((ρ ⊗ₖ ρ) ⊗ₖ ρ)
            * (swap13Operator (ι := ι) * swap12Operator (ι := ι))) =
        Matrix.trace (ρ ^ 3) := by
    rw [show
        swap13Operator (ι := ι) * swap12Operator (ι := ι) =
          (swap12Permutation ι * swap13Permutation ι).permMatrix ℂ by
      rw [swap12Operator, swap13Operator, Matrix.permMatrix_mul]]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.kroneckerMap_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]
    simp
    simp only [Fintype.sum_prod_type, swap12Permutation, swap13Permutation]
    simp [pow_succ, Matrix.mul_apply]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    ring
  have hterm1 :
      Matrix.trace
          (((ρ ⊗ₖ ρ) ⊗ₖ ρ) *
            (swap13Operator (ι := ι) * swap12Operator (ι := ι)).conjTranspose) =
        Matrix.trace (ρ ^ 3) := by
    simpa [Matrix.conjTranspose_mul, hswap12_star, hswap13_star] using hcycle12_13
  have hterm2 :
      Matrix.trace
          (swap12Operator (ι := ι) * ((ρ ⊗ₖ ρ) ⊗ₖ ρ)
            * (swap13Operator (ι := ι)).conjTranspose) =
        Matrix.trace (ρ ^ 3) := by
    rw [hswap13_star]
    calc
      Matrix.trace
          (swap12Operator (ι := ι) * ((ρ ⊗ₖ ρ) ⊗ₖ ρ)
            * swap13Operator (ι := ι)) =
          Matrix.trace
            (swap13Operator (ι := ι) * swap12Operator (ι := ι)
              * ((ρ ⊗ₖ ρ) ⊗ₖ ρ)) :=
        Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace
            (((ρ ⊗ₖ ρ) ⊗ₖ ρ) * swap13Operator (ι := ι)
              * swap12Operator (ι := ι)) :=
        Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace (ρ ^ 3) := by
        simpa [Matrix.mul_assoc] using hcycle13_12
  have hterm3 :
      Matrix.trace
          (swap13Operator (ι := ι) * ((ρ ⊗ₖ ρ) ⊗ₖ ρ)
            * (swap12Operator (ι := ι)).conjTranspose) =
        Matrix.trace (ρ ^ 3) := by
    rw [hswap12_star]
    calc
      Matrix.trace
          (swap13Operator (ι := ι) * ((ρ ⊗ₖ ρ) ⊗ₖ ρ)
            * swap12Operator (ι := ι)) =
          Matrix.trace
            (swap12Operator (ι := ι) * swap13Operator (ι := ι)
              * ((ρ ⊗ₖ ρ) ⊗ₖ ρ)) :=
        Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace
            (((ρ ⊗ₖ ρ) ⊗ₖ ρ) * swap12Operator (ι := ι)
              * swap13Operator (ι := ι)) :=
        Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace (ρ ^ 3) := by
        simpa [Matrix.mul_assoc] using hcycle12_13
  have hterm4 :
      Matrix.trace
          (swap13Operator (ι := ι) * swap12Operator (ι := ι)
            * ((ρ ⊗ₖ ρ) ⊗ₖ ρ)) =
        Matrix.trace (ρ ^ 3) := by
    calc
      Matrix.trace
          (swap13Operator (ι := ι) * swap12Operator (ι := ι)
            * ((ρ ⊗ₖ ρ) ⊗ₖ ρ)) =
          Matrix.trace
            (((ρ ⊗ₖ ρ) ⊗ₖ ρ) * swap13Operator (ι := ι)
              * swap12Operator (ι := ι)) :=
        Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace (ρ ^ 3) := by
        simpa [Matrix.mul_assoc] using hcycle13_12
  rw [hmeasurement, hterm1, hterm2, hterm3, hterm4]
  ring

end

end QAlgFormalized.QSPParameterTrace.ThirdMomentTwoControlledSWAPTests
