import Chemlib.ReactionNetwork.Laplacian
import Chemlib.ReactionNetwork.TerminalComponent
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Positive terminal-component kernel generators

For each terminal strong component of a finite reaction network, this module
constructs a nonnegative vector in the kernel of the weighted complex-graph
Laplacian whose support is exactly that component.

The construction follows GUNAWARDENA-2003, Sections 3--4, equations (10) and
(16), and Theorem 4.2 (source corpus SHA-256
`f191f4cdfe12d2a6bf5f91ce1e3358a12780f12a4b6f296b0b095f0fa42fd530`).
Positive reaction-rate labels remain explicit hypotheses.
-/

open scoped BigOperators

namespace Chemlib.ReactionNetwork

/-- The kernel of the weighted complex-graph Laplacian. -/
def weightedLaplacianKernel
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) : Submodule ℝ (ComplexId → ℝ) :=
  LinearMap.ker (N.weightedLaplacian k).mulVecLin

private abbrev TerminalVertex
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    {N : Chemlib.ReactionNetwork Species ComplexId ReactionId}
    (C : TerminalStrongComponent N) : Type :=
  {c : ComplexId // c ∈ C.1}

private abbrev TerminalReaction
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    {N : Chemlib.ReactionNetwork Species ComplexId ReactionId}
    (C : TerminalStrongComponent N) : Type :=
  {r : ReactionId // N.source r ∈ C.1}

private def terminalSubnetwork
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (C : TerminalStrongComponent N) :
    Chemlib.ReactionNetwork Species (TerminalVertex C) (TerminalReaction C) where
  complex c := N.complex c.1
  source r := ⟨N.source r.1, r.2⟩
  target r := ⟨N.target r.1, C.2.2.2 r.1 r.2⟩

private theorem exists_terminalSubnetwork_path_of_path
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (C : TerminalStrongComponent N)
    {a b : ComplexId} (ha : a ∈ C.1)
    (p : @Quiver.Path ComplexId N.reactionQuiver a b) :
    ∃ hb : b ∈ C.1,
      Nonempty (@Quiver.Path (TerminalVertex C)
        (terminalSubnetwork N C).reactionQuiver
        ⟨a, ha⟩ ⟨b, hb⟩) := by
  letI := (terminalSubnetwork N C).reactionQuiver
  induction p with
  | nil => exact ⟨ha, ⟨Quiver.Path.nil⟩⟩
  | @cons b c p e ih =>
      obtain ⟨hb, q⟩ := ih
      have hs : N.source e.1 ∈ C.1 := by
        rw [e.2.1]
        exact hb
      have hc : c ∈ C.1 := by
        rw [← e.2.2]
        exact C.2.2.2 e.1 hs
      let rC : TerminalReaction C := ⟨e.1, hs⟩
      have edgeC : @Quiver.Hom (TerminalVertex C)
          (terminalSubnetwork N C).reactionQuiver
          ⟨b, hb⟩ ⟨c, hc⟩ := by
        refine ⟨rC, ?_, ?_⟩
        · apply Subtype.ext
          exact e.2.1
        · apply Subtype.ext
          exact e.2.2
      exact ⟨hc, ⟨q.some.cons edgeC⟩⟩

private theorem terminalSubnetwork_stronglyConnected
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (C : TerminalStrongComponent N) :
    letI := (terminalSubnetwork N C).reactionQuiver
    Quiver.IsStronglyConnected (TerminalVertex C) := by
  letI := N.reactionQuiver
  letI := (terminalSubnetwork N C).reactionQuiver
  intro a b
  have hab : N.SameStrongLinkageClass a.1 b.1 :=
    (C.2.2.1 a.1 a.2 b.1).mp b.2
  obtain ⟨p⟩ := (Quiver.exists_path_of_stronglyConnectedComponent_eq hab).1
  obtain ⟨hb, q⟩ := exists_terminalSubnetwork_path_of_path N C a.2 p
  have heq : (⟨b.1, hb⟩ : TerminalVertex C) = b := Subtype.ext rfl
  rw [heq] at q
  exact q

private def terminalZeroExtend
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    {N : Chemlib.ReactionNetwork Species ComplexId ReactionId}
    (C : TerminalStrongComponent N) :
    (TerminalVertex C → ℝ) →ₗ[ℝ] (ComplexId → ℝ) where
  toFun x c := if h : c ∈ C.1 then x ⟨c, h⟩ else 0
  map_add' x y := by
    funext c
    by_cases h : c ∈ C.1 <;> simp [h]
  map_smul' a x := by
    funext c
    by_cases h : c ∈ C.1 <;> simp [h]

@[simp] private theorem terminalZeroExtend_apply_mem
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    {N : Chemlib.ReactionNetwork Species ComplexId ReactionId}
    (C : TerminalStrongComponent N)
    (x : TerminalVertex C → ℝ) (c : TerminalVertex C) :
    terminalZeroExtend C x c.1 = x c := by
  change (if h : c.1 ∈ C.1 then x ⟨c.1, h⟩ else 0) = x c
  simp only [dif_pos c.2]

@[simp] private theorem terminalZeroExtend_apply_not_mem
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    {N : Chemlib.ReactionNetwork Species ComplexId ReactionId}
    (C : TerminalStrongComponent N)
    (x : TerminalVertex C → ℝ) (c : ComplexId) (hc : c ∉ C.1) :
    terminalZeroExtend C x c = 0 := by
  change (if h : c ∈ C.1 then x ⟨c, h⟩ else 0) = 0
  simp only [dif_neg hc]

private theorem weightedLaplacian_mulVec_apply_bridge
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : ComplexId → ℝ) (c : ComplexId) :
    Matrix.mulVec (N.weightedLaplacian k) x c =
      ∑ r, ((if c = N.target r then 1 else 0) -
          (if c = N.source r then 1 else 0)) * (k r * x (N.source r)) := by
  rw [weightedLaplacian, ← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, sourceRateMatrix, incidenceMatrix]

private theorem weightedLaplacian_zeroExtend_apply_mem
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (C : TerminalStrongComponent N)
    (k : ReactionId → ℝ) (x : TerminalVertex C → ℝ)
    (c : TerminalVertex C) :
    Matrix.mulVec (N.weightedLaplacian k) (terminalZeroExtend C x) c.1 =
      Matrix.mulVec
        ((terminalSubnetwork N C).weightedLaplacian (fun r ↦ k r.1)) x c := by
  rw [weightedLaplacian_mulVec_apply_bridge,
    weightedLaplacian_mulVec_apply_bridge]
  let p : ReactionId → Prop := fun r ↦ N.source r ∈ C.1
  let F : ReactionId → ℝ := fun r ↦
    ((if c.1 = N.target r then 1 else 0) -
      (if c.1 = N.source r then 1 else 0)) *
        (k r * terminalZeroExtend C x (N.source r))
  change (∑ r, F r) = _
  calc
    (∑ r, F r) = ∑ r, if p r then F r else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hs : p r
      · simp [hs]
      · rw [if_neg hs]
        simp [F, p, hs, terminalZeroExtend_apply_not_mem]
    _ = ∑ r ∈ Finset.univ.filter p, F r := by
      simpa using (Finset.sum_filter p F).symm
    _ = ∑ r : TerminalReaction C, F r.1 := by
      simpa [p] using
        (Finset.sum_subtype (Finset.univ.filter p) (by simp [p]) F)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [F]
      simp only [terminalSubnetwork]
      have ht : c.1 = N.target r.1 ↔
          c = (⟨N.target r.1, C.2.2.2 r.1 r.2⟩ : TerminalVertex C) := by
        constructor
        · exact fun h ↦ Subtype.ext h
        · exact fun h ↦ congrArg Subtype.val h
      have hs : c.1 = N.source r.1 ↔
          c = (⟨N.source r.1, r.2⟩ : TerminalVertex C) := by
        constructor
        · exact fun h ↦ Subtype.ext h
        · exact fun h ↦ congrArg Subtype.val h
      simp only [ht, hs]
      congr 2
      exact terminalZeroExtend_apply_mem C x ⟨N.source r.1, r.2⟩

private theorem weightedLaplacian_zeroExtend_apply_not_mem
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (C : TerminalStrongComponent N)
    (k : ReactionId → ℝ) (x : TerminalVertex C → ℝ)
    (c : ComplexId) (hc : c ∉ C.1) :
    Matrix.mulVec (N.weightedLaplacian k) (terminalZeroExtend C x) c = 0 := by
  rw [weightedLaplacian_mulVec_apply_bridge]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hs : N.source r ∈ C.1
  · have ht : N.target r ∈ C.1 := C.2.2.2 r hs
    have hcs : c ≠ N.source r := fun h ↦ hc (h ▸ hs)
    have hct : c ≠ N.target r := fun h ↦ hc (h ▸ ht)
    simp [hcs, hct]
  · rw [terminalZeroExtend_apply_not_mem C x (N.source r) hs]
    simp

private theorem terminalZeroExtend_mem_weightedLaplacianKernel
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (C : TerminalStrongComponent N)
    (k : ReactionId → ℝ) (x : TerminalVertex C → ℝ)
    (hx : Matrix.mulVec
      ((terminalSubnetwork N C).weightedLaplacian (fun r ↦ k r.1)) x = 0) :
    Matrix.mulVec (N.weightedLaplacian k) (terminalZeroExtend C x) = 0 := by
  funext c
  by_cases hc : c ∈ C.1
  · let cC : TerminalVertex C := ⟨c, hc⟩
    rw [show c = cC.1 from rfl,
      weightedLaplacian_zeroExtend_apply_mem N C k x cC]
    exact congrFun hx cC
  · exact weightedLaplacian_zeroExtend_apply_not_mem N C k x c hc

private theorem simplex_kernel_or_strict_separator
    {Index : Type} [Fintype Index] [Nonempty Index] [DecidableEq Index]
    (A : Matrix Index Index ℝ) :
    (∃ x ∈ stdSimplex ℝ Index, Matrix.mulVec A x = 0) ∨
      ∃ f : StrongDual ℝ (Index → ℝ),
        ∀ i, f (Matrix.mulVec A (Pi.single i 1)) < 0 := by
  classical
  by_cases hk : ∃ x ∈ stdSimplex ℝ Index, Matrix.mulVec A x = 0
  · exact Or.inl hk
  · right
    let s : Set (Index → ℝ) := A.mulVecLin '' stdSimplex ℝ Index
    have hsconv : Convex ℝ s := (convex_stdSimplex ℝ Index).linear_image A.mulVecLin
    have hscompact : IsCompact s :=
      (isCompact_stdSimplex ℝ Index).image A.mulVecLin.toContinuousLinearMap.continuous
    have hzero : (0 : Index → ℝ) ∉ s := by
      rintro ⟨x, hx, hAx⟩
      apply hk
      refine ⟨x, hx, ?_⟩
      simpa using hAx
    have hdisj : Disjoint s ({0} : Set (Index → ℝ)) :=
      Set.disjoint_singleton_right.mpr hzero
    obtain ⟨f, u, v, hfu, huv, hv⟩ :=
      geometric_hahn_banach_compact_closed hsconv hscompact
        (convex_singleton 0) isClosed_singleton hdisj
    refine ⟨f, fun i ↦ ?_⟩
    have himage : Matrix.mulVec A (Pi.single i 1) ∈ s := by
      refine ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, ?_⟩
      rfl
    have hleft := hfu _ himage
    have hright := hv 0 (Set.mem_singleton 0)
    simp only [map_zero] at hright
    linarith

private theorem functional_mulVec_single_eq_transpose_mulVec
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (A : Matrix Index Index ℝ) (f : StrongDual ℝ (Index → ℝ)) (d : Index) :
    f (Matrix.mulVec A (Pi.single d 1)) =
      Matrix.mulVec A.transpose (fun c ↦ f (Pi.single c 1)) d := by
  rw [Matrix.mulVec_single_one]
  conv_lhs =>
    rw [← LinearMap.sum_single_apply (fun _ : Index ↦ ℝ) (A.col d)]
  rw [map_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.col_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro c _
  have hsingle : Pi.single c (A c d) = (A c d) • Pi.single c (1 : ℝ) := by
    rw [← Pi.single_smul]
    simp
  rw [hsingle, map_smul]
  rfl

private theorem transpose_weightedLaplacian_mulVec_apply
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
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

private theorem source_eq_zero_of_target_eq_zero_of_kernel
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r)
    (x : ComplexId → ℝ) (hx : ∀ c, 0 ≤ x c)
    (hker : Matrix.mulVec (N.weightedLaplacian k) x = 0)
    (c : ComplexId) (hc : x c = 0)
    (r : ReactionId) (ht : N.target r = c) :
    x (N.source r) = 0 := by
  by_cases hs : N.source r = c
  · rw [hs, hc]
  · let term : ReactionId → ℝ := fun q ↦
      ((if c = N.target q then 1 else 0) -
        (if c = N.source q then 1 else 0)) * (k q * x (N.source q))
    have hnonneg : ∀ q ∈ (Finset.univ : Finset ReactionId), 0 ≤ term q := by
      intro q _
      by_cases hqt : c = N.target q <;> by_cases hqs : c = N.source q
      · have hloop : N.target q = N.source q := hqt.symm.trans hqs
        simp [term, hqt, hloop]
      · simp only [term, if_pos hqt, if_neg hqs, sub_zero, one_mul]
        exact mul_nonneg (hk q).le (hx _)
      · simp [term, hqs, hqs ▸ hc]
      · simp [term, hqt, hqs]
    have hsum : ∑ q, term q = 0 := by
      rw [← weightedLaplacian_mulVec_apply_bridge N k x c]
      exact congrFun hker c
    have hrzero : term r = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum r (Finset.mem_univ r)
    have hct : c = N.target r := ht.symm
    have hcs : c ≠ N.source r := fun h ↦ hs h.symm
    simp only [term, if_pos hct, if_neg hcs, sub_zero, one_mul] at hrzero
    exact (mul_eq_zero.mp hrzero).resolve_left (ne_of_gt (hk r))

private theorem source_zero_along_path
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r)
    (x : ComplexId → ℝ) (hx : ∀ c, 0 ≤ x c)
    (hker : Matrix.mulVec (N.weightedLaplacian k) x = 0) :
    letI := N.reactionQuiver
    ∀ {a c : ComplexId}, Quiver.Path a c → x c = 0 → x a = 0 := by
  letI := N.reactionQuiver
  intro a c p
  induction p with
  | nil => exact id
  | @cons b c p e ih =>
      intro hc
      have hb : x b = 0 := by
        simpa [e.2.1] using
          source_eq_zero_of_target_eq_zero_of_kernel N k hk x hx hker
            c hc e.1 e.2.2
      exact ih hb

private theorem simplex_kernel_strictlyPositive_of_stronglyConnected
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Nonempty ComplexId]
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r)
    (hsc : letI := N.reactionQuiver; Quiver.IsStronglyConnected ComplexId)
    (x : ComplexId → ℝ) (hx : x ∈ stdSimplex ℝ ComplexId)
    (hker : Matrix.mulVec (N.weightedLaplacian k) x = 0) :
    ∀ c, 0 < x c := by
  letI := N.reactionQuiver
  intro c
  have hne : x c ≠ 0 := by
    intro hc
    have hall : ∀ d, x d = 0 := by
      intro d
      exact source_zero_along_path N k hk x hx.1 hker (hsc d c).some hc
    have hsumzero : ∑ d, x d = 0 := by simp [hall]
    linarith [hx.2]
  exact lt_of_le_of_ne (hx.1 c) hne.symm

private theorem exists_simplex_weightedLaplacian_kernel
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Nonempty ComplexId]
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 ≤ k r) :
    ∃ x ∈ stdSimplex ℝ ComplexId,
      Matrix.mulVec (N.weightedLaplacian k) x = 0 := by
  rcases simplex_kernel_or_strict_separator (N.weightedLaplacian k) with hker | hsep
  · exact hker
  · obtain ⟨f, hf⟩ := hsep
    let y : ComplexId → ℝ := fun c ↦ f (Pi.single c 1)
    obtain ⟨d, -, hmin⟩ :=
      Finset.exists_min_image (Finset.univ : Finset ComplexId) y Finset.univ_nonempty
    have hterms : 0 ≤
        ∑ r, if N.source r = d then k r * (y (N.target r) - y d) else 0 := by
      apply Finset.sum_nonneg
      intro r _
      by_cases hs : N.source r = d
      · simp only [if_pos hs]
        exact mul_nonneg (hk r) (sub_nonneg.mpr (hmin _ (Finset.mem_univ _)))
      · simp [hs]
    have hformula :
        f (Matrix.mulVec (N.weightedLaplacian k) (Pi.single d 1)) =
          ∑ r, if N.source r = d then k r * (y (N.target r) - y d) else 0 := by
      rw [functional_mulVec_single_eq_transpose_mulVec]
      exact transpose_weightedLaplacian_mulVec_apply N k y d
    exfalso
    exact (not_lt_of_ge (hformula.symm ▸ hterms)) (hf d)

/-- Every terminal strong component supports a nonnegative weighted-Laplacian
kernel vector which is strictly positive exactly on that component. -/
theorem exists_terminalKernelGenerator
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    ∀ C : TerminalStrongComponent N,
      ∃ g : ComplexId → ℝ,
        g ∈ weightedLaplacianKernel N k ∧
        (∀ c, 0 ≤ g c) ∧
        ∀ c, 0 < g c ↔ terminalStrongComponentMem N C c := by
  intro C
  let NC := terminalSubnetwork N C
  let kC : TerminalReaction C → ℝ := fun r ↦ k r.1
  letI : Nonempty (TerminalVertex C) := ⟨⟨C.2.1.choose, C.2.1.choose_spec⟩⟩
  have hkC : ∀ r, 0 < kC r := fun r ↦ hk r.1
  obtain ⟨x, hxsimplex, hxker⟩ :=
    exists_simplex_weightedLaplacian_kernel NC kC (fun r ↦ (hkC r).le)
  have hsc : letI := NC.reactionQuiver;
      Quiver.IsStronglyConnected (TerminalVertex C) :=
    terminalSubnetwork_stronglyConnected N C
  have hxpos : ∀ c, 0 < x c :=
    simplex_kernel_strictlyPositive_of_stronglyConnected
      NC kC hkC hsc x hxsimplex hxker
  let g : ComplexId → ℝ := terminalZeroExtend C x
  refine ⟨g, ?_, ?_, ?_⟩
  · change Matrix.mulVec (N.weightedLaplacian k) g = 0
    exact terminalZeroExtend_mem_weightedLaplacianKernel N C k x hxker
  · intro c
    by_cases hc : c ∈ C.1
    · let cC : TerminalVertex C := ⟨c, hc⟩
      change 0 ≤ terminalZeroExtend C x c
      rw [show c = cC.1 from rfl, terminalZeroExtend_apply_mem C x cC]
      exact (hxpos cC).le
    · change 0 ≤ terminalZeroExtend C x c
      rw [terminalZeroExtend_apply_not_mem C x c hc]
  · intro c
    change 0 < g c ↔ c ∈ C.1
    constructor
    · intro hg
      by_contra hc
      have hz : g c = 0 := terminalZeroExtend_apply_not_mem C x c hc
      linarith
    · intro hc
      let cC : TerminalVertex C := ⟨c, hc⟩
      change 0 < terminalZeroExtend C x c
      rw [show c = cC.1 from rfl, terminalZeroExtend_apply_mem C x cC]
      exact hxpos cC

/-- A chosen positive kernel generator for each terminal strong component. -/
noncomputable def terminalKernelGenerator
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    TerminalStrongComponent N → ComplexId → ℝ :=
  fun C ↦ Classical.choose (exists_terminalKernelGenerator N k hk C)

/-- The chosen terminal generator lies in the weighted-Laplacian kernel. -/
theorem terminalKernelGenerator_mem_kernel
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    ∀ C : TerminalStrongComponent N,
      terminalKernelGenerator N k hk C ∈ weightedLaplacianKernel N k := by
  intro C
  exact (Classical.choose_spec (exists_terminalKernelGenerator N k hk C)).1

/-- The chosen terminal generator is pointwise nonnegative. -/
theorem terminalKernelGenerator_nonnegative
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    ∀ C : TerminalStrongComponent N, ∀ c : ComplexId,
      0 ≤ terminalKernelGenerator N k hk C c := by
  intro C
  exact (Classical.choose_spec (exists_terminalKernelGenerator N k hk C)).2.1

/-- The chosen terminal generator is positive exactly on its component. -/
theorem terminalKernelGenerator_pos_iff_mem
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    ∀ C : TerminalStrongComponent N, ∀ c : ComplexId,
      0 < terminalKernelGenerator N k hk C c ↔
        terminalStrongComponentMem N C c := by
  intro C
  exact (Classical.choose_spec (exists_terminalKernelGenerator N k hk C)).2.2

end Chemlib.ReactionNetwork
