import QITBench.Base
import Mathlib.Algebra.Star.StarProjection
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The antisymmetric projector

The standard complex Hilbert space with basis indexed by `a` is represented by
matrices, and `QITBench.TensorPower a n` indexes its `n`-fold tensor power.
-/

open scoped ComplexConjugate

namespace QITBench.AntisymmetricProjector

universe u

noncomputable section

/-- A unitary representation of the symmetric group `Sₙ` on the `n`-fold
tensor power of a finite-dimensional complex Hilbert space. -/
abbrev UnitaryPermutationRepresentation
    (a : Type u) [Fintype a] [DecidableEq a] (n : ℕ) :=
  Equiv.Perm (Fin n) →* Matrix.unitaryGroup (TensorPower a n) ℂ

/-- The signed average of a permutation representation:
`Π_ASym = (1 / n!) ∑_π sgn(π) W^π`. -/
def antisymmetricProjector
    {a : Type u} [Fintype a] [DecidableEq a] (n : ℕ)
    (W : UnitaryPermutationRepresentation a n) :
    CMatrix (TensorPower a n) :=
  ((n.factorial : ℂ)⁻¹) •
    ∑ π : Equiv.Perm (Fin n),
      Equiv.Perm.sign π • (W π : CMatrix (TensorPower a n))

/-- The signed average of the unitary permutation representation is an
orthogonal projector (equivalently, a self-adjoint idempotent). -/
theorem antisymmetricProjector_isOrthogonalProjector
    {a : Type u} [Fintype a] [DecidableEq a] (n : ℕ)
    (W : UnitaryPermutationRepresentation a n) :
    IsStarProjection (antisymmetricProjector n W) := by
  let T : Equiv.Perm (Fin n) → CMatrix (TensorPower a n) :=
    fun π => Equiv.Perm.sign π • (W π : CMatrix (TensorPower a n))
  have hT_mul (π σ : Equiv.Perm (Fin n)) : T π * T σ = T (π * σ) := by
    dsimp only [T]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← Equiv.Perm.sign_mul,
      ← Matrix.UnitaryGroup.mul_val, ← map_mul]
  have hT_star (π : Equiv.Perm (Fin n)) : star (T π) = T π⁻¹ := by
    dsimp only [T]
    rw [StarModule.star_smul]
    change Equiv.Perm.sign π • star (W π : CMatrix (TensorPower a n)) =
      Equiv.Perm.sign π⁻¹ • (W π⁻¹ : CMatrix (TensorPower a n))
    rw [Equiv.Perm.sign_inv]
    congr 1
    rw [← Matrix.UnitaryGroup.inv_val, ← map_inv]
  have hsum_mul : (∑ π, T π) * (∑ σ, T σ) =
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
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
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
    have hscalar_star : star ((n.factorial : ℂ)⁻¹) = (n.factorial : ℂ)⁻¹ := by
      simp
    rw [hscalar_star]
    congr 1
    calc
      star (∑ π, T π) = ∑ π, star (T π) := star_sum _ _
      _ = ∑ π, T π⁻¹ := by simp_rw [hT_star]
      _ = ∑ π, T π := Equiv.sum_comp (Equiv.inv _) T

end

end QITBench.AntisymmetricProjector
