import QITBench.Base.OneShot
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Negative conditional entropy and pure-state entanglement

This file formalizes the finite-dimensional statement that a normalized
bipartite pure state is entangled exactly when the conditional entropy of the
second subsystem given the first is negative.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace QITFormalized.NegativeConditionalEntropyEntanglementPureBipartiteStates

open QITBench

noncomputable section

universe u v

/-- The base-2 von Neumann entropy of a finite-dimensional density state.

The eigenvalues are real and nonnegative because `rho` is positive
semidefinite.  Lean's convention `Real.log 0 = 0` realizes the standard
continuous convention `0 * log₂ 0 = 0`.
-/
noncomputable def vonNeumannEntropy
    {A : Type u} [Fintype A] [DecidableEq A]
    (rho : State A) : ℝ :=
  -∑ i, rho.pos.1.eigenvalues i * QITBench.OneShot.log2 (rho.pos.1.eigenvalues i)

/-- A bipartite pure vector is a product vector when its amplitudes factor into
one local vector for Alice and one local vector for Bob. -/
def IsProductVector
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (psi : PureVector (A × B)) : Prop :=
  ∃ psiA : A → ℂ, ∃ psiB : B → ℂ,
    ∀ i j, psi.amp (i, j) = psiA i * psiB j

/-- Entanglement of a bipartite pure vector is failure to be a product
vector. -/
def IsEntangled
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (psi : PureVector (A × B)) : Prop :=
  ¬ IsProductVector psi

/-- The quantum conditional entropy `S(B|A) = S(rhoAB) - S(rhoA)`, where
`rhoA = Tr_B(rhoAB)`.  The benchmark definition `State.marginalA` is precisely
the partial trace over the second subsystem. -/
noncomputable def conditionalEntropyBGivenA
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rhoAB : State (A × B)) : ℝ :=
  vonNeumannEntropy rhoAB - vonNeumannEntropy rhoAB.marginalA

private theorem stateEigenvalues_isProbability
    {H : Type*} [Fintype H] [DecidableEq H] (rho : State H) :
    OneShot.IsProbabilityDistribution rho.pos.1.eigenvalues := by
  constructor
  · exact rho.pos.eigenvalues_nonneg
  · have htrace := rho.pos.1.trace_eq_sum_eigenvalues
    rw [rho.trace_eq_one] at htrace
    have hre := congrArg Complex.re htrace
    simpa using hre.symm

private theorem probabilityEntropy_nonneg
    {X : Type*} [Fintype X] (p : X → ℝ)
    (hp : OneShot.IsProbabilityDistribution p) :
    0 ≤ OneShot.schmidtEntropy p := by
  have hp_le_one (i : X) : p i ≤ 1 := by
    rw [← hp.2]
    exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
  have hnat : 0 ≤ ∑ i, Real.negMulLog (p i) :=
    Finset.sum_nonneg fun i _ =>
      Real.negMulLog_nonneg (hp.1 i) (hp_le_one i)
  have hlog : 0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  unfold OneShot.schmidtEntropy OneShot.log2
  rw [← Finset.sum_neg_distrib]
  calc
    0 ≤ (∑ i, Real.negMulLog (p i)) / Real.log 2 :=
      div_nonneg hnat hlog
    _ = ∑ i, -(p i * (Real.log (p i) / Real.log 2)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.negMulLog]
      ring

private theorem stateEntropy_nonneg
    {H : Type*} [Fintype H] [DecidableEq H] (rho : State H) :
    0 ≤ vonNeumannEntropy rho := by
  change 0 ≤ OneShot.schmidtEntropy rho.pos.1.eigenvalues
  exact probabilityEntropy_nonneg _ (stateEigenvalues_isProbability rho)

private theorem probabilityEntropy_eq_zero_iff_support_card_le_one
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : OneShot.IsProbabilityDistribution p) :
    OneShot.schmidtEntropy p = 0 ↔
      Fintype.card {i // p i ≠ 0} ≤ 1 := by
  have hp_le_one (i : X) : p i ≤ 1 := by
    rw [← hp.2]
    exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
  have hentropy : OneShot.schmidtEntropy p =
      (∑ i, Real.negMulLog (p i)) / Real.log 2 := by
    unfold OneShot.schmidtEntropy OneShot.log2
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.negMulLog]
    ring
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hzero_or_one (i : X) (hi : Real.negMulLog (p i) = 0) :
      p i = 0 ∨ p i = 1 := by
    by_cases hpi : p i = 0
    · exact Or.inl hpi
    right
    by_contra hpone
    have hpos : 0 < p i := lt_of_le_of_ne (hp.1 i) (Ne.symm hpi)
    have hlt : p i < 1 := lt_of_le_of_ne (hp_le_one i) hpone
    have hlogneg : Real.log (p i) < 0 := Real.log_neg hpos hlt
    have hnegmulpos : 0 < Real.negMulLog (p i) := by
      rw [Real.negMulLog]
      exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr hpos) hlogneg
    exact (ne_of_gt hnegmulpos) hi
  constructor
  · intro hH
    have hsum : (∑ i, Real.negMulLog (p i)) = 0 := by
      have hdiv : (∑ i, Real.negMulLog (p i)) / Real.log 2 = 0 := by
        rw [← hentropy]
        exact hH
      exact (div_eq_zero_iff.mp hdiv).resolve_right hlog
    have hterm (i : X) : Real.negMulLog (p i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Real.negMulLog_nonneg (hp.1 j) (hp_le_one j))).mp hsum i
        (Finset.mem_univ i)
    rw [Fintype.card_le_one_iff]
    intro i j
    apply Subtype.ext
    by_contra hij
    have hpi : p i = 1 :=
      (hzero_or_one i (hterm i)).resolve_left i.property
    have hpj : p j = 1 :=
      (hzero_or_one j (hterm j)).resolve_left j.property
    have hle :=
      Finset.sum_le_univ_sum_of_nonneg (hp.1) (s := {i.1, j.1})
    rw [Finset.sum_pair (by simpa using hij), hpi, hpj, hp.2] at hle
    norm_num at hle
  · intro hcard
    have hex : ∃ i : X, p i ≠ 0 := by
      by_contra h
      push Not at h
      have hsumzero : (∑ i, p i) = 0 := by simp [h]
      linarith [hp.2]
    obtain ⟨i, hi⟩ := hex
    have hsub : Subsingleton {j // p j ≠ 0} :=
      Fintype.card_le_one_iff_subsingleton.mp hcard
    have hother (j : X) (hji : j ≠ i) : p j = 0 := by
      by_contra hj
      have heq : (⟨j, hj⟩ : {k // p k ≠ 0}) = ⟨i, hi⟩ :=
        hsub.elim _ _
      exact hji (congrArg Subtype.val heq)
    have hsump : (∑ j, p j) = p i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact hother j hji
      · simp
    have hpi : p i = 1 := by
      rw [← hsump]
      exact hp.2
    rw [hentropy]
    have hsumneg : (∑ j, Real.negMulLog (p j)) = 0 := by
      calc
        (∑ j, Real.negMulLog (p j)) = Real.negMulLog (p i) := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            simp [hother j hji]
          · simp
        _ = 0 := by simp [hpi]
    rw [hsumneg, zero_div]

private theorem stateEntropy_eq_zero_iff_rank_le_one
    {H : Type*} [Fintype H] [DecidableEq H] (rho : State H) :
    vonNeumannEntropy rho = 0 ↔ rho.matrix.rank ≤ 1 := by
  change OneShot.schmidtEntropy rho.pos.1.eigenvalues = 0 ↔ _
  rw [probabilityEntropy_eq_zero_iff_support_card_le_one _
    (stateEigenvalues_isProbability rho)]
  rw [rho.pos.1.rank_eq_card_non_zero_eigs]

private theorem productVector_iff_amplitudeMatrix_rank_le_one
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (psi : PureVector (A × B)) :
    IsProductVector psi ↔
      (show Matrix A B ℂ from fun i j => psi.amp (i, j)).rank ≤ 1 := by
  let M : Matrix A B ℂ := fun i j => psi.amp (i, j)
  change IsProductVector psi ↔ M.rank ≤ 1
  constructor
  · rintro ⟨psiA, psiB, hfac⟩
    have hM : M = Matrix.vecMulVec psiA psiB := by
      ext i j
      simpa [M, Matrix.vecMulVec_apply] using hfac i j
    rw [hM]
    exact Matrix.rank_vecMulVec_le psiA psiB
  · intro hrank
    have hM : M ≠ 0 := by
      intro hzero
      have htrace := psi.trace_rankOne_eq_one
      have hamp : psi.amp = 0 := by
        funext x
        change M x.1 x.2 = 0
        rw [hzero]
        rfl
      simp [hamp, rankOneMatrix] at htrace
    obtain ⟨i0, hi0⟩ : ∃ i : A, M.row i ≠ 0 := by
      by_contra h
      push Not at h
      apply hM
      ext i j
      have hij := congrFun (h i) j
      exact hij
    let S : Submodule ℂ (B → ℂ) :=
      Submodule.span ℂ (Set.range M.row)
    have hrow_mem : M.row i0 ∈ S :=
      Submodule.subset_span (Set.mem_range_self i0)
    let w0 : S := ⟨M.row i0, hrow_mem⟩
    have hw0 : w0 ≠ 0 := by
      intro h
      apply hi0
      exact congrArg Subtype.val h
    have hfin_le : Module.finrank ℂ S ≤ 1 := by
      rw [← Matrix.rank_eq_finrank_span_row]
      exact hrank
    have hfin_pos : 0 < Module.finrank ℂ S := by
      rw [Module.finrank_pos_iff]
      exact nontrivial_iff.mpr ⟨w0, 0, hw0⟩
    have hfin : Module.finrank ℂ S = 1 := by omega
    have hall : ∀ w : S, ∃ c : ℂ, c • w0 = w :=
      (finrank_eq_one_iff_of_nonzero' w0 hw0).mp hfin
    have hcoeff : ∀ i : A, ∃ c : ℂ, c • w0 =
        (⟨M.row i, Submodule.subset_span (Set.mem_range_self i)⟩ : S) := by
      intro i
      exact hall _
    choose psiA hpsiA using hcoeff
    refine ⟨psiA, M.row i0, ?_⟩
    intro i j
    have hij :=
      congrArg (fun w : S => (w : B → ℂ) j) (hpsiA i)
    simpa [M, w0, Matrix.row] using hij.symm

private theorem marginalA_rank_eq_amplitudeMatrix_rank
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (psi : PureVector (A × B)) :
    psi.state.marginalA.matrix.rank =
      (show Matrix A B ℂ from fun i j => psi.amp (i, j)).rank := by
  let M : Matrix A B ℂ := fun i j => psi.amp (i, j)
  have hmat : psi.state.marginalA.matrix = M * M.conjTranspose := by
    ext i i'
    simp [State.marginalA, partialTraceB, PureVector.state, M,
      Matrix.mul_apply, rankOneMatrix_apply]
  rw [hmat, Matrix.rank_self_mul_conjTranspose]

private theorem productVector_iff_marginalA_rank_le_one
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (psi : PureVector (A × B)) :
    IsProductVector psi ↔ psi.state.marginalA.matrix.rank ≤ 1 := by
  rw [marginalA_rank_eq_amplitudeMatrix_rank]
  exact productVector_iff_amplitudeMatrix_rank_le_one psi

/-- A normalized bipartite pure vector is entangled if and only if the
conditional entropy of Bob's subsystem given Alice's subsystem is negative. -/
theorem entangled_iff_conditionalEntropyBGivenA_neg
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (psi : PureVector (A × B)) :
    IsEntangled psi ↔ conditionalEntropyBGivenA psi.state < 0 := by
  have hpure : vonNeumannEntropy psi.state = 0 :=
    (stateEntropy_eq_zero_iff_rank_le_one psi.state).2
      psi.state_matrix_rank_le_one
  have hmarg_nonneg : 0 ≤ vonNeumannEntropy psi.state.marginalA :=
    stateEntropy_nonneg psi.state.marginalA
  constructor
  · intro hentangled
    have hnrank : ¬psi.state.marginalA.matrix.rank ≤ 1 := by
      intro hrank
      exact hentangled <|
        (productVector_iff_marginalA_rank_le_one psi).2 hrank
    have hne : vonNeumannEntropy psi.state.marginalA ≠ 0 := by
      intro hzero
      exact hnrank <|
        (stateEntropy_eq_zero_iff_rank_le_one psi.state.marginalA).1 hzero
    have hpos : 0 < vonNeumannEntropy psi.state.marginalA :=
      lt_of_le_of_ne hmarg_nonneg (Ne.symm hne)
    unfold conditionalEntropyBGivenA
    rw [hpure]
    linarith
  · intro hnegative hproduct
    have hrank : psi.state.marginalA.matrix.rank ≤ 1 :=
      (productVector_iff_marginalA_rank_le_one psi).1 hproduct
    have hmarg_zero : vonNeumannEntropy psi.state.marginalA = 0 :=
      (stateEntropy_eq_zero_iff_rank_le_one psi.state.marginalA).2 hrank
    unfold conditionalEntropyBGivenA at hnegative
    rw [hpure, hmarg_zero] at hnegative
    linarith

end

end QITFormalized.NegativeConditionalEntropyEntanglementPureBipartiteStates
