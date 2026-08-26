import ChemistryLib.ReactionNetwork.TerminalKernelGenerator
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Preorder.Finite

/-!
# A basis of the weighted-Laplacian kernel

The positive vectors supported on the terminal strong components span the
entire kernel of the weighted complex-graph Laplacian and form a basis of it.
The proof follows the terminal-component restriction and dimension argument
of GUNAWARDENA-2003, Section 4, Theorem 4.2 (source corpus SHA-256
`f191f4cdfe12d2a6bf5f91ce1e3358a12780f12a4b6f296b0b095f0fa42fd530`).
Positive reaction-rate labels remain explicit hypotheses.
-/

open scoped BigOperators

namespace ChemistryLib.ReactionNetwork

private theorem exists_path_to_terminalStrongComponent
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (c : ComplexId) :
    letI := N.reactionQuiver
    ∃ C : TerminalStrongComponent N,
      ∃ d, d ∈ C.1 ∧ Nonempty (Quiver.Path c d) := by
  classical
  letI := N.reactionQuiver
  letI : Preorder ComplexId :=
    { le := fun a b ↦ Nonempty (Quiver.Path a b)
      le_refl := fun _ ↦ ⟨Quiver.Path.nil⟩
      le_trans := fun _ _ _ hab hbc ↦ ⟨hab.some.comp hbc.some⟩ }
  obtain ⟨d, hcd, hdmax⟩ :=
    (Finset.univ : Finset ComplexId).exists_le_maximal (Finset.mem_univ c)
  let C : Finset ComplexId :=
    Finset.univ.filter (fun z ↦ N.SameStrongLinkageClass d z)
  have hC : IsTerminalStrongComponent N C := by
    refine ⟨⟨d, ?_⟩, ?_, ?_⟩
    · simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    · intro a ha b
      have hda : N.SameStrongLinkageClass d a := by
        simpa [C] using ha
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
      unfold SameStrongLinkageClass at hda ⊢
      constructor
      · exact fun hdb ↦ hda.symm.trans hdb
      · exact fun hab ↦ hda.trans hab
    · intro r hsource
      have hscc : N.SameStrongLinkageClass d (N.source r) := by
        simpa [C] using hsource
      have hdsource : Nonempty (Quiver.Path d (N.source r)) :=
        (Quiver.exists_path_of_stronglyConnectedComponent_eq hscc).1
      have hedge : Quiver.Hom (N.source r) (N.target r) :=
        ⟨r, rfl, rfl⟩
      have hdtarget : d ≤ N.target r :=
        ⟨hdsource.some.comp hedge.toPath⟩
      have htargetd : N.target r ≤ d :=
        hdmax.2 (Finset.mem_univ _) hdtarget
      have htargetscc : N.SameStrongLinkageClass d (N.target r) :=
        Quiver.stronglyConnectedComponent_eq_of_path hdtarget htargetd
      simpa [C] using htargetscc
  refine ⟨⟨C, hC⟩, d, ?_, hcd⟩
  simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

private noncomputable def terminalRepresentative
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    (C : TerminalStrongComponent N) : ComplexId :=
  C.2.1.choose

private theorem terminalRepresentative_mem
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    (C : TerminalStrongComponent N) :
    terminalRepresentative C ∈ C.1 :=
  C.2.1.choose_spec

private theorem exists_path_to_terminalRepresentative
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (c : ComplexId) :
    letI := N.reactionQuiver
    ∃ C : TerminalStrongComponent N,
      Nonempty (Quiver.Path c (terminalRepresentative C)) := by
  letI := N.reactionQuiver
  obtain ⟨C, d, hdC, hcd⟩ := exists_path_to_terminalStrongComponent N c
  have hscc : N.SameStrongLinkageClass d (terminalRepresentative C) :=
    (C.2.2.1 d hdC (terminalRepresentative C)).mp
      (terminalRepresentative_mem C)
  have hdroot : Nonempty (Quiver.Path d (terminalRepresentative C)) :=
    (Quiver.exists_path_of_stronglyConnectedComponent_eq hscc).1
  exact ⟨C, ⟨hcd.some.comp hdroot.some⟩⟩

private theorem transpose_weightedLaplacian_mulVec_apply
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (y : ComplexId → ℝ) (d : ComplexId) :
    Matrix.mulVec (N.weightedLaplacian k).transpose y d =
      ∑ r, if N.source r = d then k r * (y (N.target r) - y d) else 0 := by
  simp only [weightedLaplacian, Matrix.transpose_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, sourceRateMatrix, incidenceMatrix]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hsd : N.source r = d
  · subst d
    simp [sub_mul, Finset.sum_sub_distrib, mul_sub]
  · have hds : d ≠ N.source r := fun h ↦ hsd h.symm
    simp [hsd, hds]

private theorem harmonic_outgoing_eq_of_isMax
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r)
    (y : ComplexId → ℝ)
    (hy : Matrix.mulVec (N.weightedLaplacian k).transpose y = 0)
    (d : ComplexId) (hmax : ∀ c, y c ≤ y d)
    (r : ReactionId) (hs : N.source r = d) :
    y (N.target r) = y d := by
  let term : ReactionId → ℝ := fun q ↦
    if N.source q = d then k q * (y (N.target q) - y d) else 0
  have hterm : ∀ q ∈ (Finset.univ : Finset ReactionId), term q ≤ 0 := by
    intro q _
    by_cases hq : N.source q = d
    · simp only [term, if_pos hq]
      exact mul_nonpos_of_nonneg_of_nonpos (hk q).le (sub_nonpos.mpr (hmax _))
    · simp [term, hq]
  have hsum : ∑ q, term q = 0 := by
    rw [← transpose_weightedLaplacian_mulVec_apply N k y d]
    exact congrFun hy d
  have hrzero : term r = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hsum r (Finset.mem_univ r)
  simp only [term, if_pos hs] at hrzero
  exact sub_eq_zero.mp (mul_eq_zero.mp hrzero |>.resolve_left (ne_of_gt (hk r)))

private theorem harmonic_eq_along_path_of_isMax
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r)
    (y : ComplexId → ℝ)
    (hy : Matrix.mulVec (N.weightedLaplacian k).transpose y = 0)
    (d : ComplexId) (hmax : ∀ c, y c ≤ y d) :
    letI := N.reactionQuiver
    ∀ {c : ComplexId}, Quiver.Path d c → y c = y d := by
  letI := N.reactionQuiver
  intro c p
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      have hmaxb : ∀ z, y z ≤ y b := by
        intro z
        rw [ih]
        exact hmax z
      have hedge := harmonic_outgoing_eq_of_isMax N k hk y hy b hmaxb e.1 e.2.1
      calc
        y c = y (N.target e.1) := congrArg y e.2.2.symm
        _ = y b := hedge
        _ = y d := ih

private theorem harmonic_nonpos_of_terminalRepresentative_zero
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Nonempty ComplexId]
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r)
    (y : ComplexId → ℝ)
    (hy : Matrix.mulVec (N.weightedLaplacian k).transpose y = 0)
    (hz : ∀ C : TerminalStrongComponent N,
      y (terminalRepresentative C) = 0) :
    ∀ c, y c ≤ 0 := by
  letI := N.reactionQuiver
  obtain ⟨d, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ComplexId) y Finset.univ_nonempty
  obtain ⟨C, hpath⟩ := exists_path_to_terminalRepresentative N d
  have heq : y (terminalRepresentative C) = y d :=
    harmonic_eq_along_path_of_isMax N k hk y hy d
      (fun z ↦ hmax z (Finset.mem_univ z)) hpath.some
  have hyd : y d = 0 := heq.symm.trans (hz C)
  intro c
  simpa [hyd] using hmax c (Finset.mem_univ c)

private theorem harmonic_eq_zero_of_terminalRepresentative_zero
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Nonempty ComplexId]
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r)
    (y : ComplexId → ℝ)
    (hy : Matrix.mulVec (N.weightedLaplacian k).transpose y = 0)
    (hz : ∀ C : TerminalStrongComponent N,
      y (terminalRepresentative C) = 0) :
    y = 0 := by
  have hupper :=
    harmonic_nonpos_of_terminalRepresentative_zero N k hk y hy hz
  have hyneg : Matrix.mulVec (N.weightedLaplacian k).transpose (-y) = 0 := by
    change (N.weightedLaplacian k).transpose.mulVecLin (-y) = 0
    rw [map_neg]
    change -(Matrix.mulVec (N.weightedLaplacian k).transpose y) = 0
    rw [hy, neg_zero]
  have hzneg : ∀ C : TerminalStrongComponent N,
      (-y) (terminalRepresentative C) = 0 := by
    intro C
    simp [hz C]
  have hlowerNeg :=
    harmonic_nonpos_of_terminalRepresentative_zero N k hk (-y) hyneg hzneg
  funext c
  have hu := hupper c
  have hl := hlowerNeg c
  simp only [Pi.neg_apply] at hl
  change y c = 0
  linarith

private noncomputable def terminalRestriction
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) :
    (LinearMap.ker (N.weightedLaplacian k).transpose.mulVecLin) →ₗ[ℝ]
      (TerminalStrongComponent N → ℝ) :=
  (LinearMap.funLeft ℝ ℝ
    (fun C : TerminalStrongComponent N ↦ terminalRepresentative C)).comp
      (LinearMap.ker (N.weightedLaplacian k).transpose.mulVecLin).subtype

private theorem terminalRestriction_injective
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Nonempty ComplexId]
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    Function.Injective (terminalRestriction N k) := by
  intro x y hxy
  apply Subtype.ext
  have hxker := LinearMap.mem_ker.mp x.2
  have hyker := LinearMap.mem_ker.mp y.2
  have hdiffker :
      Matrix.mulVec (N.weightedLaplacian k).transpose (x.1 - y.1) = 0 := by
    change (N.weightedLaplacian k).transpose.mulVecLin (x.1 - y.1) = 0
    rw [map_sub, hxker, hyker, sub_zero]
  have hdiffroots : ∀ C : TerminalStrongComponent N,
      (x.1 - y.1) (terminalRepresentative C) = 0 := by
    intro C
    have hC := congrFun hxy C
    change x.1 (terminalRepresentative C) =
      y.1 (terminalRepresentative C) at hC
    exact sub_eq_zero.mpr hC
  exact sub_eq_zero.mp
    (harmonic_eq_zero_of_terminalRepresentative_zero
      N k hk (x.1 - y.1) hdiffker hdiffroots)

private theorem finrank_ker_transpose_weightedLaplacian_le_terminalCount
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Nonempty ComplexId]
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    Module.finrank ℝ
      (LinearMap.ker (N.weightedLaplacian k).transpose.mulVecLin) ≤
        Fintype.card (TerminalStrongComponent N) := by
  calc
    Module.finrank ℝ
        (LinearMap.ker (N.weightedLaplacian k).transpose.mulVecLin) ≤
        Module.finrank ℝ (TerminalStrongComponent N → ℝ) :=
      (terminalRestriction N k).finrank_le_finrank_of_injective
        (terminalRestriction_injective N k hk)
    _ = Fintype.card (TerminalStrongComponent N) :=
      Module.finrank_fintype_fun_eq_card ℝ

private theorem finrank_weightedLaplacianKernel_le_terminalCount
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Nonempty ComplexId]
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    Module.finrank ℝ (weightedLaplacianKernel N k) ≤
      Fintype.card (TerminalStrongComponent N) := by
  have htranspose :=
    finrank_ker_transpose_weightedLaplacian_le_terminalCount N k hk
  have hnull := LinearMap.finrank_range_add_finrank_ker
    (N.weightedLaplacian k).mulVecLin
  have hnullT := LinearMap.finrank_range_add_finrank_ker
    (N.weightedLaplacian k).transpose.mulVecLin
  have hrank := Matrix.rank_transpose (N.weightedLaplacian k)
  change Module.finrank ℝ
      (LinearMap.range (N.weightedLaplacian k).transpose.mulVecLin) =
    Module.finrank ℝ
      (LinearMap.range (N.weightedLaplacian k).mulVecLin) at hrank
  unfold weightedLaplacianKernel
  omega

private theorem terminalKernelGenerators_linearIndependent_private
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    LinearIndependent ℝ (terminalKernelGenerator N k hk) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro f hf C
  let c := terminalRepresentative C
  have hcC : terminalStrongComponentMem N C c := terminalRepresentative_mem C
  have hpos : 0 < terminalKernelGenerator N k hk C c :=
    (terminalKernelGenerator_pos_iff_mem N k hk C c).2 hcC
  have hzero : ∀ D : TerminalStrongComponent N, D ≠ C →
      terminalKernelGenerator N k hk D c = 0 := by
    intro D hDC
    have hnotmem : ¬ terminalStrongComponentMem N D c := by
      intro hcD
      exact Set.disjoint_left.mp
        (terminalStrongComponents_disjoint N D C hDC) hcD hcC
    have hnonneg := terminalKernelGenerator_nonnegative N k hk D c
    have hnpos := (terminalKernelGenerator_pos_iff_mem N k hk D c).not.mpr hnotmem
    linarith
  have hpoint := congrFun hf c
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hpoint
  have hsingle :
      (∑ D, f D * terminalKernelGenerator N k hk D c) =
        f C * terminalKernelGenerator N k hk C c := by
    apply Finset.sum_eq_single C
    · intro D _ hDC
      simp [hzero D hDC]
    · simp
  rw [hsingle] at hpoint
  exact (mul_eq_zero.mp hpoint).resolve_right (ne_of_gt hpos)

/-- The terminal-component generators span the weighted-Laplacian kernel. -/
theorem span_terminalKernelGenerators
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    Submodule.span ℝ (Set.range (terminalKernelGenerator N k hk)) =
      weightedLaplacianKernel N k := by
  have hle :
      Submodule.span ℝ (Set.range (terminalKernelGenerator N k hk)) ≤
        weightedLaplacianKernel N k := by
    apply Submodule.span_le.mpr
    rintro g ⟨C, rfl⟩
    exact terminalKernelGenerator_mem_kernel N k hk C
  cases isEmpty_or_nonempty ComplexId with
  | inl hComplexId =>
      letI := hComplexId
      apply le_antisymm hle
      intro x _
      have hx : x = 0 := by
        funext c
        exact isEmptyElim c
      rw [hx]
      exact Submodule.zero_mem _
  | inr hComplexId =>
      letI := hComplexId
      apply Submodule.eq_of_le_of_finrank_le hle
      calc
        Module.finrank ℝ (weightedLaplacianKernel N k) ≤
            Fintype.card (TerminalStrongComponent N) :=
          finrank_weightedLaplacianKernel_le_terminalCount N k hk
        _ = Module.finrank ℝ
            (Submodule.span ℝ
              (Set.range (terminalKernelGenerator N k hk))) :=
          (Module.finrank_eq_card_basis
            (Module.Basis.span
              (terminalKernelGenerators_linearIndependent_private N k hk))).symm

/-- The terminal-component generators, regarded as kernel elements, form a basis. -/
noncomputable def terminalKernelBasis
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    Module.Basis (TerminalStrongComponent N) ℝ (weightedLaplacianKernel N k) := by
  let v : TerminalStrongComponent N → weightedLaplacianKernel N k :=
    fun C ↦ ⟨terminalKernelGenerator N k hk C,
      terminalKernelGenerator_mem_kernel N k hk C⟩
  have hli : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp (weightedLaplacianKernel N k).subtype
    have hv :
        (weightedLaplacianKernel N k).subtype ∘ v =
          terminalKernelGenerator N k hk := by
      rfl
    rw [hv]
    exact terminalKernelGenerators_linearIndependent_private N k hk
  have hkernelFinrank :
      Module.finrank ℝ (weightedLaplacianKernel N k) =
        Fintype.card (TerminalStrongComponent N) := by
    rw [← span_terminalKernelGenerators N k hk]
    exact Module.finrank_eq_card_basis (Module.Basis.span
      (terminalKernelGenerators_linearIndependent_private N k hk))
  have hspanFinrank :
      Module.finrank ℝ (Submodule.span ℝ (Set.range v)) =
        Fintype.card (TerminalStrongComponent N) :=
    Module.finrank_eq_card_basis (Module.Basis.span hli)
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ := by
    apply Submodule.eq_of_le_of_finrank_le le_top
    rw [show Module.finrank ℝ
        (⊤ : Submodule ℝ (weightedLaplacianKernel N k)) =
        Module.finrank ℝ (weightedLaplacianKernel N k) by simp,
      hkernelFinrank, hspanFinrank]
  exact Module.Basis.mk hli (hspan.ge)

/-- Each terminal kernel basis vector is the chosen generator for its component. -/
theorem terminalKernelBasis_apply
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    ∀ C : TerminalStrongComponent N,
      ((terminalKernelBasis N k hk C : weightedLaplacianKernel N k) :
          ComplexId → ℝ) =
        terminalKernelGenerator N k hk C := by
  intro C
  simp [terminalKernelBasis]

/-- The terminal-component kernel generators are linearly independent. -/
theorem terminalKernelGenerators_linearIndependent
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    LinearIndependent ℝ (terminalKernelGenerator N k hk) :=
  terminalKernelGenerators_linearIndependent_private N k hk

end ChemistryLib.ReactionNetwork
