import QITBench.Base

/-!
# Kraus representation from a system-environment unitary

Both two-dimensional Hilbert spaces are represented in their computational
bases by `Fin 2`.  Thus operators on either qubit are complex `2 × 2`
matrices, and operators on the joint system use the product basis
`Fin 2 × Fin 2`.
-/

open scoped BigOperators

namespace QITFormalized.KrausRepresentationSystemEnvironmentUnitary

open QITBench

noncomputable section

/-- The computational-basis label type for both the system and environment. -/
abbrev Qubit := Fin 2

/-- The Pauli `X` matrix. -/
def pauliX : CMatrix Qubit :=
  !![(0 : ℂ), 1;
     1, 0]

/-- The Pauli `Y` matrix. -/
def pauliY : CMatrix Qubit :=
  !![(0 : ℂ), -Complex.I;
     Complex.I, 0]

/-- The coefficient `1 / √2`, regarded as a complex scalar. -/
def invSqrtTwo : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The joint operator
`U = (1 / √2) X ⊗ I_E + (1 / √2) Y ⊗ X_E`. -/
def interactionUnitary : CMatrix (Qubit × Qubit) :=
  invSqrtTwo • Matrix.kronecker pauliX (1 : CMatrix Qubit) +
    invSqrtTwo • Matrix.kronecker pauliY pauliX

/-- The environment projector `|0⟩⟨0|_E`. -/
def environmentZeroProjector : CMatrix Qubit :=
  Matrix.single 0 0 1

/-- The system operator obtained as the environment matrix element
`⟨k| V |e⟩_E`. -/
def environmentMatrixElement
    (V : CMatrix (Qubit × Qubit)) (k e : Qubit) : CMatrix Qubit :=
  fun i j => V (i, k) (j, e)

/-- The Kraus operator `E_k = ⟨k| U |0⟩_E`. -/
def krausOperator (k : Qubit) : CMatrix Qubit :=
  environmentMatrixElement interactionUnitary k 0

/-- The matrix map given by the two environment-indexed Kraus operators. -/
def krausMap : MatrixMap Qubit Qubit :=
  MatrixMap.ofKraus krausOperator

/-- The reduced system evolution obtained by initializing the environment in
`|0⟩_E` and tracing it out after conjugation by `U`. -/
def reducedSystemEvolution (ρ : CMatrix Qubit) : CMatrix Qubit :=
  partialTraceB
    (interactionUnitary *
      Matrix.kronecker ρ environmentZeroProjector *
      Matrix.conjTranspose interactionUnitary)

/-- The concrete joint interaction is unitary. -/
theorem interactionUnitary_isUnitary :
    interactionUnitary * Matrix.conjTranspose interactionUnitary = 1 ∧
      Matrix.conjTranspose interactionUnitary * interactionUnitary = 1 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by
    norm_num
  constructor <;>
    ext ⟨i, j⟩ ⟨i', j'⟩ <;>
    fin_cases i <;>
    fin_cases j <;>
    fin_cases i' <;>
    fin_cases j' <;>
    simp [interactionUnitary, invSqrtTwo, pauliX, pauliY,
      Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two] <;>
    field_simp <;>
    norm_num [Complex.I_sq, Complex.I_mul_I] <;>
    exact_mod_cast hsqrt.symm

/-- The environment matrix elements of the unitary satisfy the
trace-preserving Kraus completeness relation. -/
theorem krausOperator_completeness :
    (∑ k : Qubit,
      Matrix.conjTranspose (krausOperator k) * krausOperator k) =
        (1 : CMatrix Qubit) := by
  have hsqrtC : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by
    exact_mod_cast (show Real.sqrt 2 ^ 2 = 2 by norm_num)
  ext i j
  fin_cases i <;>
    fin_cases j <;>
    simp [krausOperator, environmentMatrixElement, interactionUnitary,
      invSqrtTwo, pauliX, pauliY, Matrix.mul_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two] <;>
    field_simp <;>
    norm_num [Complex.I_sq, Complex.I_mul_I, hsqrtC]

/-- The Kraus map is trace preserving as a consequence of completeness. -/
theorem krausMap_isTracePreserving :
    MatrixMap.IsTracePreserving krausMap := by
  rw [krausMap]
  apply MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one
  simpa [MatrixMap.krausAdjoint] using krausOperator_completeness

/-- The CPTP channel determined by the environment matrix elements of `U`. -/
def reducedSystemChannel : Channel Qubit Qubit where
  map := krausMap
  completelyPositive := by
    rw [krausMap]
    exact MatrixMap.ofKraus_completelyPositive krausOperator
  tracePreserving := krausMap_isTracePreserving
  mapsPositive := by
    rw [krausMap]
    exact MatrixMap.ofKraus_mapsPositive krausOperator

/-- For every system density matrix, tracing out the initialized environment
is the Kraus map with `E_k = ⟨k|U|0⟩_E`.  The two matrix elements are
`E_0 = X / √2` and `E_1 = Y / √2`, and their completeness relation makes the
map trace preserving. -/
theorem reducedSystemChannel_krausRepresentation (ρS : State Qubit) :
    reducedSystemEvolution ρS.matrix =
        (reducedSystemChannel.applyState ρS).matrix ∧
      (reducedSystemChannel.applyState ρS).matrix =
        ∑ k : Qubit,
          krausOperator k * ρS.matrix *
            Matrix.conjTranspose (krausOperator k) ∧
      (∀ k : Qubit,
        krausOperator k =
          environmentMatrixElement interactionUnitary k 0) ∧
      krausOperator 0 = invSqrtTwo • pauliX ∧
      krausOperator 1 = invSqrtTwo • pauliY ∧
      (∑ k : Qubit,
        Matrix.conjTranspose (krausOperator k) * krausOperator k) =
          (1 : CMatrix Qubit) := by
  refine ⟨?_, rfl, fun k => rfl, ?_, ?_, krausOperator_completeness⟩
  · change reducedSystemEvolution ρS.matrix = krausMap ρS.matrix
    ext i j
    fin_cases i <;>
      fin_cases j <;>
      simp [reducedSystemEvolution, partialTraceB, krausMap,
        MatrixMap.ofKraus, krausOperator, environmentMatrixElement,
        interactionUnitary, environmentZeroProjector, invSqrtTwo, pauliX,
        pauliY, Matrix.mul_apply, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;>
      fin_cases j <;>
      simp [krausOperator, environmentMatrixElement, interactionUnitary,
        invSqrtTwo, pauliX, pauliY, Matrix.kronecker,
        Matrix.kroneckerMap_apply]
  · ext i j
    fin_cases i <;>
      fin_cases j <;>
      simp [krausOperator, environmentMatrixElement, interactionUnitary,
        invSqrtTwo, pauliX, pauliY, Matrix.kronecker,
        Matrix.kroneckerMap_apply]

end

end QITFormalized.KrausRepresentationSystemEnvironmentUnitary
