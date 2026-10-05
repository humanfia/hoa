import QAlgBench.Base

/-!
# Orthonormality of coherently encoded Markov-chain rows

For a row-stochastic real matrix `P`, this file represents the coherent
encoding

`|ψᵢ⟩ = |i⟩ ⊗ ∑ j, √(Pᵢⱼ) |j⟩`

in the product computational basis and states that these vectors form an
orthonormal family.
-/

open QAlgBench

namespace QAlgFormalized.OrthonormalityCoherentMarkovChainRows

/-- A finite quantum register whose computational basis is indexed by `Fin d`. -/
def finRegister (d : ℕ) : Register where
  Index := Fin d
  fintype := inferInstance
  decEq := inferInstance

/--
The coherent encoding of row `i` of `P`.

The basis vector indexed by `(i, j)` is the product ket `|i⟩ ⊗ |j⟩`, so this
finite sum is the coordinate realization of
`|i⟩ ⊗ ∑ j, √(P i j) |j⟩` in `ℂ^d ⊗ ℂ^d`.
-/
noncomputable def coherentRowState {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    StateVector (Register.prod (finRegister d) (finRegister d)) :=
  ∑ j : Fin d, (Real.sqrt (P i j) : ℂ) • PiLp.single 2 (i, j) 1

/--
The coherent encodings of the rows of a real row-stochastic matrix form an
orthonormal family.
-/
theorem coherentRowState_orthonormal {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℝ)
    (h_nonnegative : ∀ i j, 0 ≤ P i j)
    (h_row_sum : ∀ i, ∑ j : Fin d, P i j = 1) :
    Orthonormal ℂ (coherentRowState P) := by
  change Orthonormal ℂ (fun i : Fin d =>
    ∑ j : Fin d, (Real.sqrt (P i j) : ℂ) •
      (PiLp.single 2 (i, j) 1 : EuclideanSpace ℂ (Fin d × Fin d)))
  rw [orthonormal_iff_ite]
  intro i i'
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    EuclideanSpace.inner_single_left]
  by_cases h : i = i'
  · subst i'
    simp only [Complex.conj_ofReal, map_one, PiLp.single_apply, Prod.mk.injEq,
      true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    norm_cast
    have hsqrt : ∀ x : Fin d,
        Real.sqrt (P i x) * Real.sqrt (P i x) = P i x :=
      fun x => Real.mul_self_sqrt (h_nonnegative i x)
    simpa only [hsqrt] using h_row_sum i
  · simp [h]

end QAlgFormalized.OrthonormalityCoherentMarkovChainRows
