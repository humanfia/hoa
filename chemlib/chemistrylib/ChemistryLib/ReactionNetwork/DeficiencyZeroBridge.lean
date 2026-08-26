import ChemistryLib.ReactionNetwork.DeficiencyKernel
import ChemistryLib.ReactionNetwork.TerminalKernelGenerator
import Mathlib.Analysis.SpecialFunctions.Exp

/- USER: Reuse the independently compiled zero-sorry proof at
`/tmp/DeficiencyZeroBridgeFallback.lean` (SHA-256
`57308b9e37f017bd3f19984f51d7db8c90b7143939af234bebf57ba5f7a33d4c`).
Its four theorem bodies match this lock exactly.  Keep this file's locked
imports/API and transplant the proof bodies; do not open alternate proof trees. -/

/-!
# Deficiency-zero bridge lemmas

These statements connect complex monomials, the deficiency-zero linear
decomposition, and positive kernels of the weighted complex-graph Laplacian.
They follow the deficiency-zero setup in YU-CRACIUN-2018, Section 2.2 and
Theorem 2.8 (source corpus SHA-256
`087c3303f891486c8056bd60bd540dc85bf1b862999249906199e8b57a6dc671`,
<https://arxiv.org/pdf/1805.10371v1>),
together with GUNAWARDENA-2003, Sections 4 and 6--7, especially Theorems 4.2,
6.2, 6.4, and 7.1 (source corpus SHA-256
`f191f4cdfe12d2a6bf5f91ce1e3358a12780f12a4b6f296b0b095f0fa42fd530`,
<https://www.jeremy-gunawardena.com/papers/crnt.pdf>).
Reaction-rate labels remain explicit parameters.
-/

namespace ChemistryLib.ReactionNetwork

open scoped BigOperators

noncomputable section

/-! ## Project-local Mathlib supplement — Deficiency-zero bridges -/

private noncomputable def strongComponentFinset
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ReactionNetwork Species ComplexId ReactionId) (c : ComplexId) :
    Finset ComplexId := by
  classical
  exact Finset.univ.filter (fun d => N.SameStrongLinkageClass c d)

private theorem strongComponentFinset_isTerminal
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ReactionNetwork Species ComplexId ReactionId)
    (hwr : N.WeaklyReversible) (c : ComplexId) :
    N.IsTerminalStrongComponent (strongComponentFinset N c) := by
  classical
  refine ⟨⟨c, ?_⟩, ?_, ?_⟩
  · simp only [strongComponentFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    unfold SameStrongLinkageClass
    rfl
  · intro a ha b
    simp only [strongComponentFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] at ha ⊢
    unfold SameStrongLinkageClass at ha ⊢
    constructor
    · exact fun hcb => ha.symm.trans hcb
    · exact fun hab => ha.trans hab
  · intro r hr
    simp only [strongComponentFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hr ⊢
    unfold SameStrongLinkageClass at hr ⊢
    exact hr.trans ((N.weaklyReversible_iff_sameStrongLinkageClass.mp hwr r))

private noncomputable def terminalThrough
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ReactionNetwork Species ComplexId ReactionId)
    (hwr : N.WeaklyReversible) (c : ComplexId) :
    N.TerminalStrongComponent :=
  ⟨strongComponentFinset N c, strongComponentFinset_isTerminal N hwr c⟩

private theorem terminalThrough_mem
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ReactionNetwork Species ComplexId ReactionId)
    (hwr : N.WeaklyReversible) (c : ComplexId) :
    N.terminalStrongComponentMem (terminalThrough N hwr c) c := by
  unfold terminalStrongComponentMem terminalThrough
  simp only [strongComponentFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  unfold SameStrongLinkageClass
  rfl

private def globalKernelVector
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) : ComplexId → ℝ :=
  ∑ C : N.TerminalStrongComponent, N.terminalKernelGenerator k hk C

private theorem globalKernelVector_mem
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    globalKernelVector N k hk ∈ N.weightedLaplacianKernel k := by
  unfold globalKernelVector
  exact Submodule.sum_mem _ fun C _ => N.terminalKernelGenerator_mem_kernel k hk C

private theorem globalKernelVector_pos
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ReactionNetwork Species ComplexId ReactionId)
    (hwr : N.WeaklyReversible)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    ∀ c, 0 < globalKernelVector N k hk c := by
  intro c
  have hterm : 0 < N.terminalKernelGenerator k hk (terminalThrough N hwr c) c :=
    (N.terminalKernelGenerator_pos_iff_mem k hk _ c).2 (terminalThrough_mem N hwr c)
  have hle :
      N.terminalKernelGenerator k hk (terminalThrough N hwr c) c ≤
        ∑ C : N.TerminalStrongComponent, N.terminalKernelGenerator k hk C c := by
    exact Finset.single_le_sum (s := Finset.univ)
      (fun C _ => N.terminalKernelGenerator_nonnegative k hk C c)
      (Finset.mem_univ _)
  exact hterm.trans_le (by simpa [globalKernelVector, Finset.sum_apply] using hle)

private theorem deficiencyZero_restrictedKer_eq_bot
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : ReactionNetwork Species ComplexId ReactionId)
    (hδ : N.deficiency = 0) :
    LinearMap.ker (N.complexCompositionOnIncidenceImage) = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  rw [← N.deficiency_eq_finrank_ker_complexCompositionOnIncidenceImage]
  exact hδ

private theorem basisFun_toDual_comp_mulVecLin
    {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℝ) :
    (Pi.basisFun ℝ m).toDual.comp M.mulVecLin =
      M.transpose.mulVecLin.dualMap.comp (Pi.basisFun ℝ n).toDual := by
  apply (Pi.basisFun ℝ n).ext
  intro j
  apply (Pi.basisFun ℝ m).ext
  intro i
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply,
    LinearMap.dualMap_apply]
  rw [(Pi.basisFun ℝ m).toDual_apply_left,
    (Pi.basisFun ℝ n).toDual_apply_right]
  simp [Pi.basisFun_apply]

private theorem sourceRateMatrix_mulVec_apply
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (v : ComplexId → ℝ) (r : ReactionId) :
    Matrix.mulVec (N.sourceRateMatrix k) v r = k r * v (N.source r) := by
  simp [Matrix.mulVec, dotProduct, sourceRateMatrix]

/-- Complex monomials turn coordinatewise exponentials into the exponential
of the transposed complex-composition image. -/
theorem complexMonomialVector_exp
    {Species ComplexId ReactionId : Type} [Fintype Species]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (u : Species → ℝ) :
    N.complexMonomialVector (fun s ↦ Real.exp (u s)) =
      fun c ↦ Real.exp (Matrix.mulVec N.compositionMatrix.transpose u c) := by
  classical
  funext c
  unfold complexMonomialVector Complex.monomial
  rw [Finsupp.prod_pow]
  simp_rw [← Real.exp_nat_mul]
  rw [← Real.exp_sum]
  congr 1

/-- At deficiency zero, every complex-space vector splits into a transposed
composition image and a vector killed by transposed incidence. -/
theorem deficiencyZero_logDecomposition
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
    [DecidableEq Species] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (hdef : N.deficiency = 0) (z : ComplexId → ℝ) :
    ∃ u : Species → ℝ, ∃ q : ComplexId → ℝ,
      z = Matrix.mulVec N.compositionMatrix.transpose u + q ∧
        Matrix.mulVec N.incidenceMatrix.transpose q = 0 := by
  classical
  let A : (ComplexId → ℝ) →ₗ[ℝ] (Species → ℝ) :=
    N.compositionMatrix.mulVecLin
  let At : (Species → ℝ) →ₗ[ℝ] (ComplexId → ℝ) :=
    N.compositionMatrix.transpose.mulVecLin
  let B : (ReactionId → ℝ) →ₗ[ℝ] (ComplexId → ℝ) :=
    N.incidenceMatrix.mulVecLin
  let Bt : (ComplexId → ℝ) →ₗ[ℝ] (ReactionId → ℝ) :=
    N.incidenceMatrix.transpose.mulVecLin
  let U : Submodule ℝ (ComplexId → ℝ) :=
    LinearMap.range At ⊔ LinearMap.ker Bt
  have hU : U = ⊤ := by
    rw [← Submodule.dualAnnihilator_eq_bot_iff]
    apply le_antisymm
    · intro phi hphi
      rw [Submodule.mem_bot]
      have hvanish : ∀ x ∈ U, phi x = 0 :=
        (Submodule.mem_dualAnnihilator phi).mp hphi
      have hAtAnn :
          phi ∈ (LinearMap.range At).dualAnnihilator := by
        apply (Submodule.mem_dualAnnihilator phi).mpr
        intro x hx
        exact hvanish x (Submodule.mem_sup_left hx)
      have hBtAnn :
          phi ∈ (LinearMap.ker Bt).dualAnnihilator := by
        apply (Submodule.mem_dualAnnihilator phi).mpr
        intro x hx
        exact hvanish x (Submodule.mem_sup_right hx)
      have hAtZero : At.dualMap phi = 0 := by
        have hAtKer : phi ∈ LinearMap.ker At.dualMap := by
          simpa only [LinearMap.ker_dualMap_eq_dualAnnihilator_range] using hAtAnn
        exact LinearMap.mem_ker.mp hAtKer
      have hBtRange : phi ∈ LinearMap.range Bt.dualMap := by
        rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
        exact hBtAnn
      rcases hBtRange with ⟨psi, hpsi⟩
      let bS := Pi.basisFun ℝ Species
      let bC := Pi.basisFun ℝ ComplexId
      let bR := Pi.basisFun ℝ ReactionId
      let w : ComplexId → ℝ := bC.toDualEquiv.symm phi
      let r : ReactionId → ℝ := bR.toDualEquiv.symm psi
      have hphi : bC.toDual w = phi := by
        change bC.toDualEquiv w = phi
        exact bC.toDualEquiv.apply_symm_apply phi
      have hpsi' : bR.toDual r = psi := by
        change bR.toDualEquiv r = psi
        exact bR.toDualEquiv.apply_symm_apply psi
      have hAwDual : bS.toDual (A w) = 0 := by
        calc
          bS.toDual (A w) = At.dualMap (bC.toDual w) := by
            exact LinearMap.congr_fun
              (basisFun_toDual_comp_mulVecLin N.compositionMatrix) w
          _ = At.dualMap phi := by rw [hphi]
          _ = 0 := hAtZero
      have hAw : A w = 0 := bS.toDual_inj (A w) hAwDual
      have hBrDual : bC.toDual (B r) = bC.toDual w := by
        calc
          bC.toDual (B r) = Bt.dualMap (bR.toDual r) := by
            exact LinearMap.congr_fun
              (basisFun_toDual_comp_mulVecLin N.incidenceMatrix) r
          _ = Bt.dualMap psi := by rw [hpsi']
          _ = phi := hpsi
          _ = bC.toDual w := hphi.symm
      have hBr : B r = w := bC.toDual_injective hBrDual
      have hwRange : w ∈ LinearMap.range B := ⟨r, hBr⟩
      let wr : LinearMap.range B := ⟨w, hwRange⟩
      have hwrKer : wr ∈ LinearMap.ker N.complexCompositionOnIncidenceImage := by
        apply LinearMap.mem_ker.mpr
        change A w = 0
        exact hAw
      have hwrZero : wr = 0 := by
        rw [deficiencyZero_restrictedKer_eq_bot N hdef] at hwrKer
        simpa using hwrKer
      have hw : w = 0 := congr_arg Subtype.val hwrZero
      calc
        phi = bC.toDual w := hphi.symm
        _ = 0 := by rw [hw, map_zero]
    · exact bot_le
  have hz : z ∈ U := by rw [hU]; exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hz with ⟨a, ha, q, hq, haz⟩
  rcases ha with ⟨u, rfl⟩
  refine ⟨u, q, ?_, ?_⟩
  · exact haz.symm
  · exact LinearMap.mem_ker.mp hq

/-- Weak reversibility and positive reaction rates give a pointwise-positive
weighted-Laplacian kernel vector. -/
theorem weaklyReversible_exists_positive_weightedLaplacianKernel
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (hwr : N.WeaklyReversible) (k : ReactionId → ℝ)
    (hk : ∀ r, 0 < k r) :
    ∃ b : ComplexId → ℝ,
      b ∈ N.weightedLaplacianKernel k ∧ ∀ c, 0 < b c := by
  exact ⟨globalKernelVector N k hk, globalKernelVector_mem N k hk,
    globalKernelVector_pos N hwr k hk⟩

/-- Rescaling a weighted-Laplacian kernel vector by the negative exponential
of a transposed-incidence kernel vector preserves the weighted-Laplacian
kernel. -/
theorem weightedLaplacianKernel_rescale_exp_neg
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (b q : ComplexId → ℝ)
    (hb : b ∈ N.weightedLaplacianKernel k)
    (hq : Matrix.mulVec N.incidenceMatrix.transpose q = 0) :
    (fun c ↦ b c * Real.exp (-q c)) ∈ N.weightedLaplacianKernel k := by
  have hqedge : ∀ r, q (N.target r) = q (N.source r) := by
    intro r
    have hr := congr_fun hq r
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      incidenceMatrix] at hr
    simp_rw [sub_mul] at hr
    rw [Finset.sum_sub_distrib] at hr
    exact sub_eq_zero.mp (by simpa using hr)
  change Matrix.mulVec (N.weightedLaplacian k)
      (fun c ↦ b c * Real.exp (-q c)) = 0
  change Matrix.mulVec (N.weightedLaplacian k) b = 0 at hb
  rw [N.weightedLaplacian_eq_incidence_mul_sourceRate,
    ← Matrix.mulVec_mulVec] at hb ⊢
  funext c
  have hc := congr_fun hb c
  change ∑ r, N.incidenceMatrix c r *
      Matrix.mulVec (N.sourceRateMatrix k) b r = 0 at hc
  simp_rw [sourceRateMatrix_mulVec_apply] at hc
  change ∑ r, N.incidenceMatrix c r *
      Matrix.mulVec (N.sourceRateMatrix k)
        (fun c ↦ b c * Real.exp (-q c)) r = 0
  simp_rw [sourceRateMatrix_mulVec_apply]
  calc
    _ = ∑ r, Real.exp (-q c) *
        (N.incidenceMatrix c r * (k r * b (N.source r))) := by
      apply Finset.sum_congr rfl
      intro r _
      unfold incidenceMatrix
      by_cases ht : c = N.target r
      · have hqs : q (N.source r) = q c := by
          rw [ht, hqedge r]
        simp [ht, hqs]
        ring
      · by_cases hs : c = N.source r
        · simp [hs]
          ring
        · simp [ht, hs]
    _ = Real.exp (-q c) *
        (∑ r, N.incidenceMatrix c r * (k r * b (N.source r))) := by
      rw [Finset.mul_sum]
    _ = 0 := by rw [hc, mul_zero]

end

end ChemistryLib.ReactionNetwork
