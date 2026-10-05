import QAlgBench.Base
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Rank

open scoped BigOperators ComplexOrder

namespace QAlgFormalized.RankStrongFourierSamplingConditionalState

noncomputable section

universe u v

variable {G : Type u} [Group G] [Fintype G]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- A finite-dimensional unitary representation in a chosen Fourier basis. -/
abbrev UnitaryRepresentation :=
  G →* Matrix.unitaryGroup ι ℂ

/-- The ordinary linear representation underlying a matrix-valued unitary
representation. -/
def UnitaryRepresentation.toRepresentation
    (σ : UnitaryRepresentation (G := G) (ι := ι)) :
    Representation ℂ G (ι → ℂ) where
  toFun g := (σ g : Matrix ι ι ℂ).mulVecLin
  map_one' := by ext v i; simp
  map_mul' g h := by ext v i; simp

/-- Irreducibility of a unitary matrix representation. -/
def UnitaryRepresentation.IsIrreducible
    (σ : UnitaryRepresentation (G := G) (ι := ι)) : Prop :=
  IsSimpleOrder (Subrepresentation σ.toRepresentation)

/-- The dimension `d_σ` of the representation space. -/
def UnitaryRepresentation.dimension
    (_σ : UnitaryRepresentation (G := G) (ι := ι)) : ℕ :=
  Fintype.card ι

/-- The finite order `|H|` of a subgroup of `G`. -/
def subgroupOrder (H : Subgroup G) : ℕ := by
  classical
  exact Fintype.card H

/-- The operator `σ(H) = ∑ h ∈ H, σ(h)`. -/
def subgroupOperatorSum (σ : UnitaryRepresentation (G := G) (ι := ι))
    (H : Subgroup G) : Matrix ι ι ℂ := by
  classical
  exact ∑ h : H, (σ (h : G) : Matrix ι ι ℂ)

/-- The character `χ_σ(g) = tr(σ(g))`. -/
def character (σ : UnitaryRepresentation (G := G) (ι := ι)) (g : G) : ℂ :=
  Matrix.trace (σ g : Matrix ι ι ℂ)

/-- The character sum over `H`. -/
def subgroupCharacterSum (σ : UnitaryRepresentation (G := G) (ι := ι))
    (H : Subgroup G) : ℂ := by
  classical
  exact ∑ h : H, character σ (h : G)

/-- The conjugated character sum used by the conditional-state convention. -/
def conjugateSubgroupCharacterSum
    (σ : UnitaryRepresentation (G := G) (ι := ι))
    (H : Subgroup G) : ℂ := by
  classical
  exact ∑ h : H, starRingEnd ℂ (character σ (h : G))

/-- Entrywise complex conjugation in the chosen Fourier basis. -/
def entrywiseConjugate (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A.map (starRingEnd ℂ)

/-- The `H`-invariant subspace of the representation space. -/
def subgroupInvariantSubspace
    (σ : UnitaryRepresentation (G := G) (ι := ι))
    (H : Subgroup G) : Submodule ℂ (ι → ℂ) where
  carrier :=
    {v | ∀ h : H, (σ (h : G) : Matrix ι ι ℂ).mulVec v = v}
  zero_mem' := by
    intro h
    simp
  add_mem' := by
    intro x y hx hy h
    simpa [Matrix.mulVec_add] using congrArg₂ (· + ·) (hx h) (hy h)
  smul_mem' := by
    intro c x hx h
    simpa [Matrix.mulVec_smul] using congrArg (c • ·) (hx h)

/-- The subgroup-averaging operator `P_{H,σ} = |H|⁻¹ σ(H)`. -/
def subgroupAveragingProjector
    (σ : UnitaryRepresentation (G := G) (ι := ι))
    (H : Subgroup G) : Matrix ι ι ℂ :=
  ((subgroupOrder H : ℂ)⁻¹) • subgroupOperatorSum σ H

/-- The conditional strong-Fourier state in the entrywise-conjugated
Fourier-transform convention. -/
def conditionalStrongFourierState
    (σ : UnitaryRepresentation (G := G) (ι := ι))
    (H : Subgroup G) : Matrix ι ι ℂ :=
  (conjugateSubgroupCharacterSum σ H)⁻¹ •
    entrywiseConjugate (subgroupOperatorSum σ H)

/-- `P` is the orthogonal projector onto `S`: it is self-adjoint, idempotent,
and its column space is exactly `S`. -/
def IsOrthogonalProjectorOnto
    (P : Matrix ι ι ℂ) (S : Submodule ℂ (ι → ℂ)) : Prop :=
  P.conjTranspose = P ∧ P * P = P ∧ P.mulVecLin.range = S

/-- Subgroup averaging and the conditional strong-Fourier state obey the
projector, normalization, and character-rank formulas. -/
theorem rankStrongFourierSamplingConditionalState
    (σ : UnitaryRepresentation (G := G) (ι := ι)) (H : Subgroup G)
    (hσ_irreducible : σ.IsIrreducible)
    (h_conditional : conjugateSubgroupCharacterSum σ H ≠ 0) :
    IsOrthogonalProjectorOnto (subgroupAveragingProjector σ H)
        (subgroupInvariantSubspace σ H) ∧
      conditionalStrongFourierState σ H =
        ((Matrix.rank (subgroupAveragingProjector σ H) : ℂ)⁻¹) •
          entrywiseConjugate (subgroupAveragingProjector σ H) ∧
      Matrix.rank (conditionalStrongFourierState σ H) =
        Matrix.rank (subgroupAveragingProjector σ H) ∧
      (Matrix.rank (conditionalStrongFourierState σ H) : ℂ) =
        (subgroupOrder H : ℂ)⁻¹ * subgroupCharacterSum σ H ∧
      (Matrix.rank (subgroupAveragingProjector σ H) : ℂ) =
        (subgroupOrder H : ℂ)⁻¹ * subgroupCharacterSum σ H ∧
      (Matrix.rank (conditionalStrongFourierState σ H) : ℂ) =
        (subgroupOrder H : ℂ)⁻¹ * conjugateSubgroupCharacterSum σ H ∧
      (Matrix.rank (subgroupAveragingProjector σ H) : ℂ) =
        (subgroupOrder H : ℂ)⁻¹ * conjugateSubgroupCharacterSum σ H := by
  classical
  clear hσ_irreducible
  have h_card : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card H).ne'
  letI : Invertible (Fintype.card H : ℂ) := invertibleOfNonzero h_card
  have h_order : (subgroupOrder H : ℂ) ≠ 0 := by
    change (Fintype.card H : ℂ) ≠ 0
    exact h_card

  let τ : Representation ℂ H (ι → ℂ) :=
    σ.toRepresentation.comp H.subtype
  have h_averageMap :
      (subgroupAveragingProjector σ H).mulVecLin = τ.averageMap := by
    apply LinearMap.ext
    intro v
    funext i
    simp [τ, subgroupAveragingProjector, subgroupOrder, subgroupOperatorSum,
      UnitaryRepresentation.toRepresentation,
      Representation.averageMap, GroupAlgebra.average, Representation.asAlgebraHom,
      MonoidAlgebra.lift, invOf_eq_inv]
  have h_invariants :
      subgroupInvariantSubspace σ H = τ.invariants := rfl
  have h_projection :
      LinearMap.IsProj (subgroupInvariantSubspace σ H)
        (subgroupAveragingProjector σ H).mulVecLin := by
    rw [h_averageMap, h_invariants]
    exact Representation.isProj_averageMap τ

  have h_idempotent :
      subgroupAveragingProjector σ H * subgroupAveragingProjector σ H =
        subgroupAveragingProjector σ H := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply', Matrix.mulVecLin_mul]
    exact h_projection.isIdempotentElem.eq
  have h_selfAdjoint :
      (subgroupAveragingProjector σ H).conjTranspose =
        subgroupAveragingProjector σ H := by
    have h_unitary_inverse (h : H) :
        (σ (h : G) : Matrix ι ι ℂ).conjTranspose =
          (σ ((h⁻¹ : H) : G) : Matrix ι ι ℂ) := by
      rw [← Matrix.star_eq_conjTranspose]
      rw [← Matrix.UnitaryGroup.inv_val]
      simp
    rw [subgroupAveragingProjector, Matrix.conjTranspose_smul]
    simp only [star_inv₀, star_natCast, subgroupOperatorSum,
      Matrix.conjTranspose_sum, h_unitary_inverse]
    exact congrArg (fun A => (subgroupOrder H : ℂ)⁻¹ • A)
      (Equiv.sum_comp (Equiv.inv H)
        (fun h : H => (σ (h : G) : Matrix ι ι ℂ)))
  have h_orthogonal :
      IsOrthogonalProjectorOnto (subgroupAveragingProjector σ H)
        (subgroupInvariantSubspace σ H) :=
    ⟨h_selfAdjoint, h_idempotent, h_projection.range⟩

  have h_trace_rank :
      Matrix.trace (subgroupAveragingProjector σ H) =
        (Matrix.rank (subgroupAveragingProjector σ H) : ℂ) := by
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_apply']
    rw [h_projection.trace, Matrix.rank, h_projection.range]
  have h_trace_character :
      Matrix.trace (subgroupAveragingProjector σ H) =
        (subgroupOrder H : ℂ)⁻¹ * subgroupCharacterSum σ H := by
    simp [subgroupAveragingProjector, subgroupOperatorSum,
      subgroupCharacterSum, character, Matrix.trace_smul]
  have h_rank_character :
      (Matrix.rank (subgroupAveragingProjector σ H) : ℂ) =
        (subgroupOrder H : ℂ)⁻¹ * subgroupCharacterSum σ H :=
    h_trace_rank.symm.trans h_trace_character
  have h_character :
      subgroupCharacterSum σ H =
        (subgroupOrder H : ℂ) *
          (Matrix.rank (subgroupAveragingProjector σ H) : ℂ) :=
    (inv_mul_eq_iff_eq_mul₀ h_order).mp h_rank_character.symm
  have h_conjugate_as_star :
      conjugateSubgroupCharacterSum σ H =
        starRingEnd ℂ (subgroupCharacterSum σ H) := by
    simp [conjugateSubgroupCharacterSum, subgroupCharacterSum]
  have h_conjugate_character :
      conjugateSubgroupCharacterSum σ H =
        (subgroupOrder H : ℂ) *
          (Matrix.rank (subgroupAveragingProjector σ H) : ℂ) := by
    rw [h_conjugate_as_star, h_character]
    simp
  have h_rank_conjugate :
      (Matrix.rank (subgroupAveragingProjector σ H) : ℂ) =
        (subgroupOrder H : ℂ)⁻¹ *
          conjugateSubgroupCharacterSum σ H := by
    rw [h_conjugate_character, ← mul_assoc, inv_mul_cancel₀ h_order, one_mul]

  have h_entrywise_projector :
      entrywiseConjugate (subgroupAveragingProjector σ H) =
        (subgroupOrder H : ℂ)⁻¹ •
          entrywiseConjugate (subgroupOperatorSum σ H) := by
    ext i j
    simp [entrywiseConjugate, subgroupAveragingProjector]
  have h_normalized :
      conditionalStrongFourierState σ H =
        ((Matrix.rank (subgroupAveragingProjector σ H) : ℂ)⁻¹) •
          entrywiseConjugate (subgroupAveragingProjector σ H) := by
    rw [conditionalStrongFourierState, h_conjugate_character,
      h_entrywise_projector, smul_smul]
    congr 1
    rw [mul_inv_rev]

  have h_rank_smul (c : ℂ) (hc : c ≠ 0) (A : Matrix ι ι ℂ) :
      Matrix.rank (c • A) = Matrix.rank A := by
    have h_range : (c • A).mulVecLin.range = A.mulVecLin.range := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨c • x, by simp⟩
      · rintro ⟨x, rfl⟩
        refine ⟨c⁻¹ • x, ?_⟩
        simp [smul_smul, hc]
    unfold Matrix.rank
    exact h_range ▸ rfl
  have h_rank_entrywise (A : Matrix ι ι ℂ) :
      Matrix.rank (entrywiseConjugate A) = Matrix.rank A := by
    have h_entrywise :
        entrywiseConjugate A = A.conjTranspose.transpose := by
      ext i j
      rfl
    rw [h_entrywise, Matrix.rank_transpose, Matrix.rank_conjTranspose]
  have h_rank_nonzero :
      (Matrix.rank (subgroupAveragingProjector σ H) : ℂ) ≠ 0 := by
    intro h_zero
    apply h_conditional
    rw [h_conjugate_character, h_zero, mul_zero]
  have h_state_rank :
      Matrix.rank (conditionalStrongFourierState σ H) =
        Matrix.rank (subgroupAveragingProjector σ H) := by
    rw [h_normalized,
      h_rank_smul _ (inv_ne_zero h_rank_nonzero),
      h_rank_entrywise]
  have h_state_character :
      (Matrix.rank (conditionalStrongFourierState σ H) : ℂ) =
        (subgroupOrder H : ℂ)⁻¹ * subgroupCharacterSum σ H := by
    rw [h_state_rank]
    exact h_rank_character
  have h_state_conjugate :
      (Matrix.rank (conditionalStrongFourierState σ H) : ℂ) =
        (subgroupOrder H : ℂ)⁻¹ *
          conjugateSubgroupCharacterSum σ H := by
    rw [h_state_rank]
    exact h_rank_conjugate

  exact ⟨h_orthogonal, h_normalized, h_state_rank, h_state_character,
    h_rank_character, h_state_conjugate, h_rank_conjugate⟩

end

end QAlgFormalized.RankStrongFourierSamplingConditionalState
