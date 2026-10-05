/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base
public import QITBench.Base.OneShot

/-!
# A Choi matrix acting on a canonical square-root input state

The finite index types below are the fixed orthonormal bases of the systems.
An equivalence `A ≃ A'` records the chosen identification of the input system
with its reference copy.  The canonical entangled vector and its rank-one
matrix are unnormalized, as in the source statement.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QITFormalized
namespace ChoiMatrixActingCanonicalInputState

open QITBench

universe u v w

noncomputable section

variable {A : Type u} {A' : Type v} {B : Type w}
variable [Fintype A] [DecidableEq A]
variable [Fintype A'] [DecidableEq A']
variable [Fintype B] [DecidableEq B]

/-- The unnormalized vector
`|Γ⟩_{AA'} = ∑ i, |i⟩_A |e i⟩_{A'}` for the fixed basis identification `e`. -/
def canonicalEntangledVector (e : A ≃ A') : A × A' → ℂ :=
  fun i => if e i.1 = i.2 then 1 else 0

/-- The unnormalized canonical rank-one matrix
`Γ_{AA'} = |Γ⟩⟨Γ|_{AA'}`. -/
def canonicalEntangledMatrix (e : A ≃ A') : CMatrix (A × A') :=
  rankOneMatrix (canonicalEntangledVector e)

/-- The Choi matrix
`J_N = (id_A ⊗ N_{A' → B})(Γ_{AA'})` in the fixed basis identification. -/
def choiMatrix (N : Channel A' B) (e : A ≃ A') : CMatrix (A × B) :=
  ((Channel.idChannel A).prod N).map (canonicalEntangledMatrix e)

/-- The canonical input matrix
`φ_{AA'} = (ρ_A^{1/2} ⊗ I_{A'}) Γ_{AA'}
  (ρ_A^{1/2} ⊗ I_{A'})`. -/
def squareRootInputMatrix (rho : State A) (e : A ≃ A') : CMatrix (A × A') :=
  Matrix.kronecker (OneShot.matrixSqrt rho.matrix) (1 : CMatrix A') *
      canonicalEntangledMatrix e *
    Matrix.kronecker (OneShot.matrixSqrt rho.matrix) (1 : CMatrix A')

/-- Acting with the channel on the primed half of the canonical square-root
input is the same as conjugating its Choi matrix on the reference half. -/
theorem choiMatrix_acting_canonicalInputState
    (N : Channel A' B) (e : A ≃ A') (rho : State A) :
    ((Channel.idChannel A).prod N).map (squareRootInputMatrix rho e) =
      Matrix.kronecker (OneShot.matrixSqrt rho.matrix) (1 : CMatrix B) *
          choiMatrix N e *
        Matrix.kronecker (OneShot.matrixSqrt rho.matrix) (1 : CMatrix B) := by
  have map_apply (X : CMatrix (A × A')) (a a' : A) (b b' : B) :
      ((Channel.idChannel A).prod N).map X (a, b) (a', b') =
        ∑ j : A', ∑ j' : A',
          X (a, j) (a', j') *
            N.map (Matrix.single j j' (1 : ℂ)) b b' := by
    have id_map (Y : CMatrix A) : (Channel.idChannel A).map Y = Y := by
      simp [Channel.idChannel, MatrixMap.ofKraus]
    change (MatrixMap.kron (Channel.idChannel A).map N.map X) (a, b) (a', b') = _
    simp only [MatrixMap.kron, id_map]
    simp only [Matrix.single_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single a']
      · simp
      · intro x _ hx
        simp [hx]
      · simp
    · intro x _ hx
      simp [hx]
    · simp
  have left_mul_input (R : CMatrix A) (X : CMatrix (A × A'))
      (a a' : A) (j j' : A') :
      (Matrix.kronecker R (1 : CMatrix A') * X) (a, j) (a', j') =
        ∑ p : A, R a p * X (p, j) (a', j') := by
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  have right_mul_input (R : CMatrix A) (X : CMatrix (A × A'))
      (a a' : A) (j j' : A') :
      (X * Matrix.kronecker R (1 : CMatrix A')) (a, j) (a', j') =
        ∑ q : A, X (a, j) (q, j') * R q a' := by
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single j']
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have left_mul_output (R : CMatrix A) (X : CMatrix (A × B))
      (a a' : A) (b b' : B) :
      (Matrix.kronecker R (1 : CMatrix B) * X) (a, b) (a', b') =
        ∑ p : A, R a p * X (p, b) (a', b') := by
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  have right_mul_output (R : CMatrix A) (X : CMatrix (A × B))
      (a a' : A) (b b' : B) :
      (X * Matrix.kronecker R (1 : CMatrix B)) (a, b) (a', b') =
        ∑ q : A, X (a, b) (q, b') * R q a' := by
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single b']
    · simp
    · intro c _ hc
      simp [hc]
    · simp
  ext ⟨a, b⟩ ⟨a', b'⟩
  unfold squareRootInputMatrix choiMatrix
  rw [map_apply, right_mul_output]
  simp_rw [right_mul_input, left_mul_input, left_mul_output, map_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ j : A', ∑ q : A, ∑ j' : A', ∑ p : A,
        OneShot.matrixSqrt rho.matrix a p *
            canonicalEntangledMatrix e (p, j) (q, j') *
          OneShot.matrixSqrt rho.matrix q a' *
        N.map (Matrix.single j j' 1) b b' := by
      refine Finset.sum_congr rfl fun j _ => ?_
      exact Finset.sum_comm
    _ = ∑ q : A, ∑ j : A', ∑ j' : A', ∑ p : A,
        OneShot.matrixSqrt rho.matrix a p *
            canonicalEntangledMatrix e (p, j) (q, j') *
          OneShot.matrixSqrt rho.matrix q a' *
        N.map (Matrix.single j j' 1) b b' := by
      exact Finset.sum_comm
    _ = ∑ q : A, ∑ j : A', ∑ p : A, ∑ j' : A',
        OneShot.matrixSqrt rho.matrix a p *
            canonicalEntangledMatrix e (p, j) (q, j') *
          OneShot.matrixSqrt rho.matrix q a' *
        N.map (Matrix.single j j' 1) b b' := by
      refine Finset.sum_congr rfl fun q _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      exact Finset.sum_comm
    _ = ∑ q : A, ∑ p : A, ∑ j : A', ∑ j' : A',
        OneShot.matrixSqrt rho.matrix a p *
            canonicalEntangledMatrix e (p, j) (q, j') *
          OneShot.matrixSqrt rho.matrix q a' *
        N.map (Matrix.single j j' 1) b b' := by
      refine Finset.sum_congr rfl fun q _ => ?_
      exact Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun q _ => ?_
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun j' _ => ?_
      ring

end

end ChoiMatrixActingCanonicalInputState
end QITFormalized
