module

public import QITBench.Base

/-!
# Maximally entangled state and the Hilbert--Schmidt inner product

The finite types `R` and `Q` label the fixed computational bases of the two
Hilbert spaces.  Thus `CMatrix R` and `CMatrix Q` are the coordinate matrices
of operators in those bases, while an equivalence `R ≃ Q` is the
basis-preserving identification of the two spaces.
-/

@[expose] public section

open scoped BigOperators

namespace QITFormalized.NormFidelityAndContinuityTools

noncomputable section

universe u v

/-- Reindex an operator on `Q` as an operator on `R` using the chosen
identification of their computational bases. -/
def operatorInIdentifiedBasis
    {R : Type u} {Q : Type v}
    (basisEquiv : R ≃ Q) (B : QITBench.CMatrix Q) :
    QITBench.CMatrix R :=
  fun i j => B (basisEquiv i) (basisEquiv j)

/-- Entrywise complex conjugation of an operator in its fixed computational
basis. -/
def entrywiseConjugate
    {R : Type u} (A : QITBench.CMatrix R) :
    QITBench.CMatrix R :=
  fun i j => star (A i j)

/-- The unnormalized maximally entangled vector
`∑ i, |i_R⟩ ⊗ |basisEquiv i_Q⟩`, expressed in the product computational
basis. -/
def unnormalizedMaximallyEntangledVector
    {R : Type u} {Q : Type v} [DecidableEq Q]
    (basisEquiv : R ≃ Q) :
    R × Q → ℂ :=
  fun ij => if ij.2 = basisEquiv ij.1 then 1 else 0

/-- The coordinate form of the bra-ket scalar `⟨ψ| X |ψ⟩`. -/
def braKet
    {ι : Type*} [Fintype ι]
    (ψ : ι → ℂ) (X : QITBench.CMatrix ι) : ℂ :=
  ∑ i : ι, ∑ j : ι, star (ψ i) * X i j * ψ j

/-- For the unnormalized maximally entangled vector, contraction against
`A ⊗ B` is the trace pairing of `Aᵀ` with `B`, after transporting `B` through
the chosen basis identification. -/
theorem maximallyEntangledState_transpose_trace
    {R : Type u} {Q : Type v}
    [Fintype R] [DecidableEq R] [Fintype Q] [DecidableEq Q]
    (d : ℕ)
    (hRdim : Fintype.card R = d)
    (hQdim : Fintype.card Q = d)
    (basisEquiv : R ≃ Q)
    (A : QITBench.CMatrix R) (B : QITBench.CMatrix Q) :
    braKet (unnormalizedMaximallyEntangledVector basisEquiv)
        (Matrix.kronecker A B) =
      (Matrix.transpose A * operatorInIdentifiedBasis basisEquiv B).trace := by
  simp [braKet, unnormalizedMaximallyEntangledVector,
    operatorInIdentifiedBasis, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Equivalently, entrywise conjugating the first operator turns the
transpose in the preceding identity into the conjugate transpose `Aᴴ`. -/
theorem maximallyEntangledState_conjugate_adjoint_trace
    {R : Type u} {Q : Type v}
    [Fintype R] [DecidableEq R] [Fintype Q] [DecidableEq Q]
    (d : ℕ)
    (hRdim : Fintype.card R = d)
    (hQdim : Fintype.card Q = d)
    (basisEquiv : R ≃ Q)
    (A : QITBench.CMatrix R) (B : QITBench.CMatrix Q) :
    braKet (unnormalizedMaximallyEntangledVector basisEquiv)
        (Matrix.kronecker (entrywiseConjugate A) B) =
      (Matrix.conjTranspose A * operatorInIdentifiedBasis basisEquiv B).trace := by
  simp [braKet, unnormalizedMaximallyEntangledVector, entrywiseConjugate,
    operatorInIdentifiedBasis, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

end

end QITFormalized.NormFidelityAndContinuityTools
