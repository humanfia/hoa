import QITBench.Base
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Symmetric projector

We use the finite coordinate model from `QITBench.Base`: a `d`-dimensional
complex Hilbert space has basis `Fin d`, and its `n`-fold tensor power uses
the benchmark's recursive `QITBench.TensorPower` basis.
-/

open scoped BigOperators

namespace QITFormalized.MixedUnitaryObstructionsAndSymmetry.SymmetricProjector

/-- Computational-basis labels for the `n`-fold tensor power of `ℂ^d`. -/
abbrev TensorBasis (d n : ℕ) : Type := QITBench.TensorPower (Fin d) n

/-- Coordinate vectors in the `n`-fold tensor power of `ℂ^d`. -/
abbrev TensorVector (d n : ℕ) : Type := TensorBasis d n → ℂ

/-- Coordinate matrices acting on the `n`-fold tensor power of `ℂ^d`. -/
abbrev TensorOperator (d n : ℕ) : Type :=
  Matrix (TensorBasis d n) (TensorBasis d n) ℂ

/-- The benchmark's recursive tensor-power labels, viewed as tuples indexed by
the tensor slots `Fin n`. -/
def tensorPowerBasisEquiv (d : ℕ) :
    (n : ℕ) → TensorBasis d n ≃ (Fin n → Fin d)
  | 0 =>
      { toFun := fun _ i => Fin.elim0 i
        invFun := fun _ => PUnit.unit
        left_inv := by
          intro x
          cases x
          rfl
        right_inv := by
          intro x
          funext i
          exact Fin.elim0 i }
  | n + 1 =>
      ((Equiv.refl (Fin d)).prodCongr (tensorPowerBasisEquiv d n)).trans
        (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d))

/-- The coordinate vector of
`ψ 0 ⊗ ⋯ ⊗ ψ (n - 1)` in the product basis. -/
def pureTensor {d n : ℕ} (ψ : Fin n → (Fin d → ℂ)) : TensorVector d n :=
  fun x => ∏ i, ψ i (tensorPowerBasisEquiv d n x i)

/-- Precomposition by `π` on slot-indexed tensor-basis labels. -/
def piSlotPermutation {d n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n → Fin d) where
  toFun x := x ∘ π
  invFun x := x ∘ π.symm
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

/-- The permutation of tensor-basis labels induced by permuting tensor slots.

The choice `x ↦ x ∘ π` makes the associated matrix act on pure tensors by
placing factor `ψ (π⁻¹ i)` in output slot `i`, matching the convention in the
source statement.
-/
def tensorSlotPermutation {d n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (TensorBasis d n) :=
  (tensorPowerBasisEquiv d n).trans
    ((piSlotPermutation (d := d) π).trans (tensorPowerBasisEquiv d n).symm)

/-- The matrix `W^π` of the permutation representation on tensor factors. -/
def tensorPermutation {d n : ℕ} (π : Equiv.Perm (Fin n)) :
    TensorOperator d n :=
  (tensorSlotPermutation (d := d) π).permMatrix ℂ

/-- The defining action
`W^π (ψ₁ ⊗ ⋯ ⊗ ψₙ) = ψ_{π⁻¹(1)} ⊗ ⋯ ⊗ ψ_{π⁻¹(n)}`. -/
theorem tensorPermutation_mulVec_pureTensor {d n : ℕ}
    (π : Equiv.Perm (Fin n)) (ψ : Fin n → (Fin d → ℂ)) :
    Matrix.mulVec (tensorPermutation (d := d) π) (pureTensor ψ) =
      pureTensor (fun i => ψ (π.symm i)) := by
  rw [tensorPermutation, Matrix.permMatrix_mulVec]
  funext x
  change
    (∏ i, ψ i (tensorPowerBasisEquiv d n
      (tensorSlotPermutation (d := d) π x) i)) =
      ∏ i, ψ (π.symm i) (tensorPowerBasisEquiv d n x i)
  have hslot :
      tensorPowerBasisEquiv d n (tensorSlotPermutation (d := d) π x) =
        tensorPowerBasisEquiv d n x ∘ π := by
    exact (tensorPowerBasisEquiv d n).apply_symm_apply _
  rw [hslot]
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    (Equiv.prod_comp π.symm
      (fun i => ψ i (tensorPowerBasisEquiv d n x (π i)))).symm

/-- Every tensor-factor permutation matrix is unitary. -/
theorem tensorPermutation_unitary {d n : ℕ} (π : Equiv.Perm (Fin n)) :
    tensorPermutation (d := d) π ∈
      Matrix.unitaryGroup (TensorBasis d n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  simp [tensorPermutation, Matrix.star_eq_conjTranspose, ← Matrix.permMatrix_mul]

/-- The identity permutation is represented by the identity operator. -/
theorem tensorPermutation_one {d n : ℕ} :
    tensorPermutation (d := d) (1 : Equiv.Perm (Fin n)) = 1 := by
  have hslot :
      tensorSlotPermutation (d := d) (1 : Equiv.Perm (Fin n)) = 1 := by
    ext x
    apply (tensorPowerBasisEquiv d n).injective
    simp [tensorSlotPermutation, piSlotPermutation]
  simp [tensorPermutation, hslot]

/-- Tensor-factor permutation matrices respect permutation composition. -/
theorem tensorPermutation_mul {d n : ℕ} (π σ : Equiv.Perm (Fin n)) :
    tensorPermutation (d := d) (π * σ) =
      tensorPermutation (d := d) π * tensorPermutation (d := d) σ := by
  have hslot :
      tensorSlotPermutation (d := d) (π * σ) =
        tensorSlotPermutation (d := d) σ *
          tensorSlotPermutation (d := d) π := by
    ext x
    apply (tensorPowerBasisEquiv d n).injective
    simp [tensorSlotPermutation, piSlotPermutation]
    funext i
    rfl
  unfold tensorPermutation
  rw [hslot, Matrix.permMatrix_mul]

/-- The normalized average of the tensor-factor permutation representation:
`Π_{Sym^n(ℂ^d)} = (1 / n!) ∑_{π ∈ S_n} W^π`. -/
noncomputable def symmetricProjector (d n : ℕ) : TensorOperator d n :=
  ((Nat.factorial n : ℂ)⁻¹) •
    ∑ π : Equiv.Perm (Fin n), tensorPermutation (d := d) π

/-- The normalized permutation average is an orthogonal projector.

For complex matrices, `IsStarProjection` means precisely that the matrix is
idempotent and self-adjoint (with matrix star equal to conjugate transpose).
-/
theorem symmetricProjector_isOrthogonalProjector (d n : ℕ) :
    IsStarProjection (symmetricProjector d n) := by
  let T : Equiv.Perm (Fin n) → TensorOperator d n :=
    fun π => tensorPermutation (d := d) π
  have hT_mul (π σ : Equiv.Perm (Fin n)) :
      T π * T σ = T (π * σ) := by
    simpa only [T] using (tensorPermutation_mul (d := d) π σ).symm
  have hT_star (π : Equiv.Perm (Fin n)) : star (T π) = T π⁻¹ := by
    have hleft : star (T π) * T π = 1 := by
      dsimp only [T]
      exact Matrix.mem_unitaryGroup_iff'.mp
        (tensorPermutation_unitary (d := d) π)
    have hright : T π * T π⁻¹ = 1 := by
      rw [hT_mul]
      simpa only [mul_inv_cancel] using
        (tensorPermutation_one (d := d) (n := n))
    calc
      star (T π) = star (T π) * 1 := (mul_one _).symm
      _ = star (T π) * (T π * T π⁻¹) := by rw [hright]
      _ = (star (T π) * T π) * T π⁻¹ := (mul_assoc _ _ _).symm
      _ = T π⁻¹ := by rw [hleft, one_mul]
  have hsum_mul :
      (∑ π, T π) * (∑ σ, T σ) =
        (n.factorial : ℂ) • ∑ τ, T τ := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum, hT_mul]
    calc
      (∑ π : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n), T (π * σ)) =
          ∑ π : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n), T τ := by
        apply Finset.sum_congr rfl
        intro π _
        exact Equiv.sum_comp (Equiv.mulLeft π) T
      _ = (n.factorial : ℂ) • ∑ τ, T τ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin]
        exact (Nat.cast_smul_eq_nsmul ℂ n.factorial _).symm
  rw [isStarProjection_iff']
  constructor
  · change (((n.factorial : ℂ)⁻¹) • ∑ π, T π) *
        (((n.factorial : ℂ)⁻¹) • ∑ π, T π) =
      ((n.factorial : ℂ)⁻¹) • ∑ π, T π
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hsum_mul, smul_smul,
      mul_assoc, inv_mul_cancel₀, mul_one]
    exact_mod_cast Nat.factorial_ne_zero n
  · change star (((n.factorial : ℂ)⁻¹) • ∑ π, T π) =
      ((n.factorial : ℂ)⁻¹) • ∑ π, T π
    rw [StarModule.star_smul]
    have hscalar_star :
        star ((n.factorial : ℂ)⁻¹) = (n.factorial : ℂ)⁻¹ := by
      simp
    rw [hscalar_star]
    congr 1
    calc
      star (∑ π, T π) = ∑ π, star (T π) := star_sum _ _
      _ = ∑ π, T π⁻¹ := by simp_rw [hT_star]
      _ = ∑ π, T π := Equiv.sum_comp (Equiv.inv _) T

end QITFormalized.MixedUnitaryObstructionsAndSymmetry.SymmetricProjector
