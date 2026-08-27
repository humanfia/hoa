import Chemlib.ReactionNetwork.DeficiencyRank
import Chemlib.ReactionNetwork.Incidence
import Chemlib.ReactionNetwork.LinkageClass
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Incidence image and rank

For a finite reaction network, the image of the directed incidence map is the
subspace of vectors whose coordinates sum to zero on each linkage class. Its
dimension is therefore the number of complexes minus the number of linkage
classes. The proof permits loop columns, parallel reaction identifiers,
isolated complexes, and empty finite index types.

Source references:
* `corpus.research_contracts:reaction_network.incidence_rank` and
  `corpus.scope:reaction_network.incidence_rank`.
* ACK-2010, Section 2, Definitions 2.1--2.4 and the linkage-class paragraph.
* YU-CRACIUN-2018, Section 2.2, Definition 2.7.
-/

namespace Chemlib.ReactionNetwork

noncomputable section

/-! ## Project-local Mathlib supplement — Incidence rank -/

private theorem incidence_mulVec_piSingle
    {Species ComplexId ReactionId : Type}
    [Finite ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (r : ReactionId) :
    N.incidenceMatrix.mulVecLin (Pi.basisFun ℝ ReactionId r) =
      Pi.basisFun ℝ ComplexId (N.target r) -
        Pi.basisFun ℝ ComplexId (N.source r) := by
  classical
  letI : Fintype ComplexId := Fintype.ofFinite _
  ext c
  simp [Pi.basisFun_apply, incidenceMatrix, Matrix.mulVec, dotProduct,
    Pi.single_apply]

private theorem transpose_incidence_mulVec_apply
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (x : ComplexId → ℝ) (r : ReactionId) :
    Matrix.mulVec N.incidenceMatrix.transpose x r =
      x (N.target r) - x (N.source r) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, incidenceMatrix]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp

private theorem mem_ker_transpose_incidence_iff
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (x : ComplexId → ℝ) :
    x ∈ LinearMap.ker N.incidenceMatrix.transpose.mulVecLin ↔
      ∀ r, x (N.target r) = x (N.source r) := by
  rw [LinearMap.mem_ker]
  change Matrix.mulVec N.incidenceMatrix.transpose x = 0 ↔ _
  constructor
  · intro h r
    have hr := congr_fun h r
    rw [transpose_incidence_mulVec_apply] at hr
    simpa only [Pi.zero_apply, sub_eq_zero] using hr
  · intro h
    funext r
    change Matrix.mulVec N.incidenceMatrix.transpose x r = 0
    rw [transpose_incidence_mulVec_apply, sub_eq_zero]
    exact h r

private theorem linkageClassOf_source_eq_target
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (r : ReactionId) :
    N.linkageClassOf (N.source r) = N.linkageClassOf (N.target r) := by
  rw [← N.sameLinkageClass_iff_linkageClass_eq]
  letI := N.reactionQuiver
  exact (Quiver.WeaklyConnectedComponent.eq _ _).2
    ⟨Quiver.Hom.toPath (Sum.inl
      (⟨r, rfl, rfl⟩ : Quiver.Hom (N.source r) (N.target r)))⟩

private noncomputable def linkageClassPullback
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    (LinkageClass N → ℝ) →ₗ[ℝ] (ComplexId → ℝ) :=
  LinearMap.funLeft ℝ ℝ N.linkageClassOf

private theorem eq_along_symm_hom
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (x : ComplexId → ℝ)
    (h : ∀ r, x (N.target r) = x (N.source r))
    {a b : ComplexId}
    (e : @Quiver.Hom (Quiver.Symmetrify ComplexId)
      (@Quiver.symmetrifyQuiver ComplexId N.reactionQuiver) a b) :
    x a = x b := by
  cases e with
  | inl e =>
      rcases e with ⟨r, hs, ht⟩
      simpa [hs, ht] using (h r).symm
  | inr e =>
      rcases e with ⟨r, hs, ht⟩
      simpa [hs, ht] using h r

private theorem eq_along_symm_path
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (x : ComplexId → ℝ)
    (h : ∀ r, x (N.target r) = x (N.source r))
    {a b : ComplexId}
    (p : @Quiver.Path (Quiver.Symmetrify ComplexId)
      (@Quiver.symmetrifyQuiver ComplexId N.reactionQuiver) a b) :
    x a = x b := by
  induction p with
  | nil => rfl
  | cons p e ih => exact ih.trans (eq_along_symm_hom N x h e)

private theorem ker_transposeIncidence_eq_range_linkageClassPullback
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    LinearMap.ker N.incidenceMatrix.transpose.mulVecLin =
      LinearMap.range N.linkageClassPullback := by
  ext x
  rw [mem_ker_transpose_incidence_iff]
  constructor
  · intro hx
    letI := N.reactionQuiver
    let y : Quiver.WeaklyConnectedComponent ComplexId → ℝ :=
      Quotient.lift x (fun _ _ h ↦ eq_along_symm_path N x hx h.some)
    refine ⟨y, ?_⟩
    funext c
    rfl
  · rintro ⟨y, rfl⟩ r
    change y (N.linkageClassOf (N.target r)) =
      y (N.linkageClassOf (N.source r))
    rw [N.linkageClassOf_source_eq_target]

private theorem finrank_ker_transposeIncidence
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    Module.finrank ℝ (LinearMap.ker N.incidenceMatrix.transpose.mulVecLin) =
      N.linkageClassCount := by
  classical
  letI : Finite (LinkageClass N) :=
    Finite.of_surjective N.linkageClassOf
      (fun c ↦ Quotient.inductionOn c (fun a ↦ ⟨a, rfl⟩))
  letI : Fintype (LinkageClass N) := Fintype.ofFinite _
  rw [N.ker_transposeIncidence_eq_range_linkageClassPullback]
  rw [LinearMap.finrank_range_of_inj]
  · rw [Module.finrank_fintype_fun_eq_card, linkageClassCount_eq_natCard,
      Nat.card_eq_fintype_card]
  · exact LinearMap.funLeft_injective_of_surjective ℝ ℝ _
      (fun c ↦ Quotient.inductionOn c (fun a ↦ ⟨a, rfl⟩))

private theorem incidenceRank_add_linkageClassCount_eq_complexCount
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.incidenceRank + N.linkageClassCount = Fintype.card ComplexId := by
  classical
  calc
    N.incidenceRank + N.linkageClassCount =
        N.incidenceMatrix.transpose.rank +
          Module.finrank ℝ
            (LinearMap.ker N.incidenceMatrix.transpose.mulVecLin) := by
      rw [N.finrank_ker_transposeIncidence]
      have hrank := (Matrix.rank_transpose N.incidenceMatrix).symm
      change N.incidenceRank = N.incidenceMatrix.transpose.rank at hrank
      exact congrArg (fun k ↦ k + N.linkageClassCount) hrank
    _ = Module.finrank ℝ (ComplexId → ℝ) :=
      LinearMap.finrank_range_add_finrank_ker _
    _ = Fintype.card ComplexId := Module.finrank_fintype_fun_eq_card ℝ

private noncomputable def linkageClassSum
    {Species ComplexId ReactionId : Type} [Fintype ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    (ComplexId → ℝ) →ₗ[ℝ] (LinkageClass N → ℝ) := by
  letI : Finite (LinkageClass N) :=
    Finite.of_surjective N.linkageClassOf
      (fun c ↦ Quotient.inductionOn c (fun a ↦ ⟨a, rfl⟩))
  exact FunOnFinite.linearMap ℝ ℝ N.linkageClassOf

/-- Vectors whose coordinates sum to zero separately on every linkage class. -/
def componentwiseZeroSumSubspace
    {Species ComplexId ReactionId : Type} [Fintype ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    Submodule ℝ (ComplexId → ℝ) :=
  LinearMap.ker N.linkageClassSum

/-- Membership is the componentwise zero-sum condition on linkage classes. -/
theorem mem_componentwiseZeroSumSubspace_iff
    {Species ComplexId ReactionId : Type} [Fintype ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    [DecidableEq (LinkageClass N)]
    (x : ComplexId → ℝ) :
    x ∈ componentwiseZeroSumSubspace N ↔
      ∀ K : LinkageClass N,
        ∑ c : {c : ComplexId // N.linkageClassOf c = K}, x c.1 = 0 := by
  letI : Finite (LinkageClass N) :=
    Finite.of_surjective N.linkageClassOf
      (fun c ↦ Quotient.inductionOn c (fun a ↦ ⟨a, rfl⟩))
  change N.linkageClassSum x = 0 ↔ _
  constructor
  · intro h K
    have hK := congr_fun h K
    rw [linkageClassSum, FunOnFinite.linearMap_apply_apply] at hK
    simp only [Pi.zero_apply] at hK
    rw [← Finset.sum_subtype
      (p := fun c ↦ N.linkageClassOf c = K)
      (Finset.univ.filter (fun c ↦ N.linkageClassOf c = K)) (by simp) x]
    exact hK
  · intro h
    funext K
    rw [linkageClassSum, FunOnFinite.linearMap_apply_apply]
    simp only [Pi.zero_apply]
    rw [Finset.sum_subtype
      (p := fun c ↦ N.linkageClassOf c = K)
      (Finset.univ.filter (fun c ↦ N.linkageClassOf c = K)) (by simp) x]
    exact h K

private theorem linkageClassSum_surjective
    {Species ComplexId ReactionId : Type} [Fintype ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    Function.Surjective N.linkageClassSum := by
  classical
  letI : Finite (LinkageClass N) :=
    Finite.of_surjective N.linkageClassOf
      (fun c ↦ Quotient.inductionOn c (fun a ↦ ⟨a, rfl⟩))
  letI : Fintype (LinkageClass N) := Fintype.ofFinite _
  intro y
  refine ⟨∑ k, y k • Pi.basisFun ℝ ComplexId (Quotient.out k), ?_⟩
  ext k
  have hout : ∀ c : LinkageClass N,
      N.linkageClassOf (Quotient.out c) = c := by
    intro c
    exact Quotient.out_eq c
  simp only [linkageClassSum, map_sum, map_smul,
    FunOnFinite.linearMap_piSingle, Pi.basisFun_apply, hout,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hbk
    rw [Pi.single_eq_of_ne hbk.symm, mul_zero]
  · simp

private theorem linkageClassSum_comp_incidence_eq_zero
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.linkageClassSum.comp N.incidenceMatrix.mulVecLin = 0 := by
  classical
  apply (Pi.basisFun ℝ ReactionId).ext
  intro r
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [N.incidence_mulVec_piSingle]
  simp [linkageClassSum, N.linkageClassOf_source_eq_target]

private theorem incidenceRange_le_componentwiseZeroSumSubspace
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    LinearMap.range N.incidenceMatrix.mulVecLin ≤
      N.componentwiseZeroSumSubspace := by
  exact LinearMap.range_le_ker_iff.mpr
    N.linkageClassSum_comp_incidence_eq_zero

private theorem linkageClassCount_add_finrank_componentwiseZeroSumSubspace
    {Species ComplexId ReactionId : Type} [Fintype ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.linkageClassCount +
        Module.finrank ℝ N.componentwiseZeroSumSubspace =
      Fintype.card ComplexId := by
  classical
  letI : Finite (LinkageClass N) :=
    Finite.of_surjective N.linkageClassOf
      (fun c ↦ Quotient.inductionOn c (fun a ↦ ⟨a, rfl⟩))
  letI : Fintype (LinkageClass N) := Fintype.ofFinite _
  have h := LinearMap.finrank_range_add_finrank_ker N.linkageClassSum
  rw [LinearMap.range_eq_top.mpr N.linkageClassSum_surjective,
    finrank_top, Module.finrank_fintype_fun_eq_card] at h
  rw [Module.finrank_fintype_fun_eq_card] at h
  change N.linkageClassCount +
    Module.finrank ℝ (LinearMap.ker N.linkageClassSum) =
      Fintype.card ComplexId
  rw [linkageClassCount_eq_natCard, Nat.card_eq_fintype_card]
  exact h

/-- The incidence-map image is the componentwise zero-sum subspace. -/
theorem incidenceRange_eq_componentwiseZeroSumSubspace
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    LinearMap.range N.incidenceMatrix.mulVecLin =
      componentwiseZeroSumSubspace N := by
  apply Submodule.eq_of_le_of_finrank_eq
    N.incidenceRange_le_componentwiseZeroSumSubspace
  have hrank := N.incidenceRank_add_linkageClassCount_eq_complexCount
  have hzero :=
    N.linkageClassCount_add_finrank_componentwiseZeroSumSubspace
  unfold incidenceRank at hrank
  omega

/-- Incidence rank is the number of complexes minus the number of linkage classes. -/
theorem incidenceRank_eq_complexCount_sub_linkageClassCount
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.incidenceRank = Fintype.card ComplexId - N.linkageClassCount := by
  have h := N.incidenceRank_add_linkageClassCount_eq_complexCount
  omega

end


end Chemlib.ReactionNetwork
