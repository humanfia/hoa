/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

/-!
# Partial-SWAP marginal splitter

Both qubit systems use `Fin 2` as their fixed computational-basis label type.
Consequently, the same matrix `rho.matrix` represents the input state on `B`
and the corresponding state on `A`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QITFormalized

open QITBench

noncomputable section

/-- There is one global two-qubit unitary which, for every input qubit density
operator `rho`, splits the state information equally between the two output
marginals. -/
theorem exists_partialSWAP_marginalSplitter :
    ∃ V : CMatrix (Prod (Fin 2) (Fin 2)),
      (Matrix.conjTranspose V * V = 1 ∧
        V * Matrix.conjTranspose V = 1) ∧
      ∀ rho : State (Fin 2),
        partialTraceA
            (V *
              Matrix.kronecker
                ((1 / 2 : ℂ) • (1 : CMatrix (Fin 2)))
                rho.matrix *
              Matrix.conjTranspose V) =
            (1 / 2 : ℂ) • rho.matrix +
              (1 / 4 : ℂ) • (1 : CMatrix (Fin 2)) ∧
        partialTraceB
            (V *
              Matrix.kronecker
                ((1 / 2 : ℂ) • (1 : CMatrix (Fin 2)))
                rho.matrix *
              Matrix.conjTranspose V) =
            (1 / 2 : ℂ) • rho.matrix +
              (1 / 4 : ℂ) • (1 : CMatrix (Fin 2)) := by
  let S : CMatrix (Prod (Fin 2) (Fin 2)) :=
    fun x y => if x = (y.2, y.1) then 1 else 0
  let V : CMatrix (Prod (Fin 2) (Fin 2)) :=
    ((1 + Complex.I) / 2 : ℂ) • (1 : CMatrix (Prod (Fin 2) (Fin 2))) +
      ((1 - Complex.I) / 2 : ℂ) • S
  refine ⟨V, ?_, ?_⟩
  · constructor
    · ext ⟨i, j⟩ ⟨k, l⟩
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
        simp [V, S, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two] <;>
        ring_nf <;>
        simp [Complex.I_sq] <;>
        norm_num
    · ext ⟨i, j⟩ ⟨k, l⟩
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
        simp [V, S, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two] <;>
        ring_nf <;>
        simp [Complex.I_sq] <;>
        norm_num
  · intro rho
    have htrace : rho.matrix 0 0 + rho.matrix 1 1 = 1 := by
      simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using rho.trace_eq_one
    constructor
    · ext j j'
      fin_cases j <;> fin_cases j' <;>
        simp [partialTraceA, V, S, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
          Fin.sum_univ_two] <;>
        ring_nf <;>
        rw [Complex.I_sq] <;>
        ring_nf <;>
        linear_combination (1 / 4 : ℂ) * htrace
    · ext i i'
      fin_cases i <;> fin_cases i' <;>
        simp [partialTraceB, V, S, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
          Fin.sum_univ_two] <;>
        ring_nf <;>
        rw [Complex.I_sq] <;>
        ring_nf <;>
        linear_combination (1 / 4 : ℂ) * htrace

end

end QITFormalized
