import QITBench.Base

/-!
# Unitarity of a system-environment evolution

The system and environment are both qubits, represented by the computational
basis index type `Fin 2`.  The tensor product is represented by the Kronecker
product on the product basis.
-/

namespace QITFormalized.UnitaritySystemEnvironmentEvolution

open QITBench

noncomputable section

/-- The Pauli `X` matrix on a qubit. -/
def pauliX : CMatrix (Fin 2) :=
  !![(0 : ℂ), 1;
     1, 0]

/-- The Pauli `Y` matrix on a qubit. -/
def pauliY : CMatrix (Fin 2) :=
  !![(0 : ℂ), -Complex.I;
     Complex.I, 0]

/-- The prescribed joint evolution on a system qubit and an environment
qubit:

`U = (1 / √2) (X ⊗ I) + (1 / √2) (Y ⊗ X)`.
-/
def systemEnvironmentEvolution : CMatrix (Fin 2 × Fin 2) :=
  ((1 : ℂ) / Real.sqrt 2) •
      Matrix.kronecker pauliX (1 : CMatrix (Fin 2)) +
    ((1 : ℂ) / Real.sqrt 2) • Matrix.kronecker pauliY pauliX

/-- The specified system-environment evolution is unitary. -/
theorem systemEnvironmentEvolution_unitary :
    systemEnvironmentEvolution ∈
      Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    norm_num
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast (show (Real.sqrt 2 : ℝ) ^ 2 = 2 by norm_num)
  rw [Matrix.mem_unitaryGroup_iff]
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [Matrix.mul_apply, ← Finset.univ_product_univ, Finset.sum_product,
      systemEnvironmentEvolution, pauliX, pauliY, Matrix.kronecker,
      Matrix.kroneckerMap, Fin.sum_univ_two]
  all_goals field_simp [hsqrt]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq, hsq]

end

end QITFormalized.UnitaritySystemEnvironmentEvolution
