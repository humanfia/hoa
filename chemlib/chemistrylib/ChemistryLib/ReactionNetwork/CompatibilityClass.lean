import ChemistryLib.ReactionNetwork.ComplexBalanceDissipation
import ChemistryLib.ReactionNetwork.PositiveCompatibilityGeometry
import ChemistryLib.ReactionNetwork.Stoichiometry

/-!
# Stoichiometric compatibility classes

This module combines the finite-dimensional positive compatibility geometry
with the log-locus and dissipation equality case for complex-balanced
mass-action systems.  It proves existence and uniqueness of a positive
complex-balanced (equivalently, positive steady) state in every positive
stoichiometric compatibility class.  No global-attraction claim is made.

Source references:

* GUNAWARDENA-2003, Section 6, Theorems 6.2 and 6.4,
  <https://www.jeremy-gunawardena.com/papers/crnt.pdf> (source SHA-256
  `f191f4cdfe12d2a6bf5f91ce1e3358a12780f12a4b6f296b0b095f0fa42fd530`).
* YU-CRACIUN-2018, Section 2.1, Theorem 2.3,
  <https://arxiv.org/pdf/1805.10371v1> (source SHA-256
  `087c3303f891486c8056bd60bd540dc85bf1b862999249906199e8b57a6dc671`).
-/

open scoped BigOperators

namespace ChemistryLib.ReactionNetwork

noncomputable section

/-- A species vector is stoichiometrically orthogonal when its finite dot
product with every vector in the stoichiometric subspace vanishes. -/
def IsStoichiometricallyOrthogonal
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (z : Species → ℝ) : Prop :=
  ∀ v ∈ N.stoichiometricSubspace, ∑ s, z s * v s = 0

/-- Two concentration states are stoichiometrically compatible when their
difference lies in the network's stoichiometric subspace. -/
def StoichiometricallyCompatible
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (x y : Species → ℝ) : Prop :=
  y - x ∈ N.stoichiometricSubspace

/-! ## Private bridges between the locked predecessor APIs -/

private theorem complex_monomial_pos_compatibility
    {Species : Type} (y : ChemistryLib.Complex Species)
    (x : Species → ℝ) (hx : ∀ s, 0 < x s) :
    0 < ChemistryLib.Complex.monomial y x := by
  unfold ChemistryLib.Complex.monomial
  apply Finset.prod_pos
  intro s hs
  exact pow_pos (hx s) _

private theorem log_complex_monomial_compatibility
    {Species : Type} [Fintype Species]
    (y : ChemistryLib.Complex Species)
    (x : Species → ℝ) (hx : ∀ s, 0 < x s) :
    Real.log (ChemistryLib.Complex.monomial y x) =
      ∑ s, (y s : ℝ) * Real.log (x s) := by
  classical
  unfold ChemistryLib.Complex.monomial
  change Real.log (y.support.prod fun s => x s ^ y s) =
    ∑ s, (y s : ℝ) * Real.log (x s)
  rw [Real.log_prod]
  · simp_rw [Real.log_pow]
    apply Finset.sum_subset (Finset.subset_univ y.support)
    intro s hs hnot
    have hy : y s = 0 := Finsupp.notMem_support_iff.mp hnot
    simp [hy]
  · intro s hs
    exact pow_ne_zero _ (ne_of_gt (hx s))

private theorem complexActivityRatio_pos_compatibility
    {Species ComplexId ReactionId : Type}
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (xStar x : Species → ℝ) (c : ComplexId)
    (hxStar : ∀ s, 0 < xStar s) (hx : ∀ s, 0 < x s) :
    0 < N.complexActivityRatio xStar x c := by
  unfold complexActivityRatio complexMonomialVector
  exact div_pos
    (complex_monomial_pos_compatibility (N.complex c) x hx)
    (complex_monomial_pos_compatibility (N.complex c) xStar hxStar)

private theorem log_complexActivityRatio_compatibility
    {Species ComplexId ReactionId : Type} [Fintype Species]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (xStar x : Species → ℝ) (c : ComplexId)
    (hxStar : ∀ s, 0 < xStar s) (hx : ∀ s, 0 < x s) :
    Real.log (N.complexActivityRatio xStar x c) =
      ∑ s, (N.complex c s : ℝ) *
        (Real.log (x s) - Real.log (xStar s)) := by
  unfold complexActivityRatio complexMonomialVector
  rw [
    Real.log_div
      (ne_of_gt (complex_monomial_pos_compatibility (N.complex c) x hx))
      (ne_of_gt
        (complex_monomial_pos_compatibility (N.complex c) xStar hxStar)),
    log_complex_monomial_compatibility (N.complex c) x hx,
    log_complex_monomial_compatibility (N.complex c) xStar hxStar]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

private theorem log_pairing_reactionVector_compatibility
    {Species ComplexId ReactionId : Type} [Fintype Species]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (xStar x : Species → ℝ) (r : ReactionId)
    (hxStar : ∀ s, 0 < xStar s) (hx : ∀ s, 0 < x s) :
    ∑ s, (Real.log (x s) - Real.log (xStar s)) *
        N.reactionVector r s =
      Real.log
        (N.complexActivityRatio xStar x (N.target r) /
          N.complexActivityRatio xStar x (N.source r)) := by
  rw [Real.log_div
    (ne_of_gt (complexActivityRatio_pos_compatibility
      N xStar x (N.target r) hxStar hx))
    (ne_of_gt (complexActivityRatio_pos_compatibility
      N xStar x (N.source r) hxStar hx)),
    log_complexActivityRatio_compatibility
      N xStar x (N.target r) hxStar hx,
    log_complexActivityRatio_compatibility
      N xStar x (N.source r) hxStar hx]
  unfold reactionVector product reactant
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro s hs <;>
    ring

private theorem massActionFlux_eq_reference_mul_activityRatio_compatibility
    {Species ComplexId ReactionId : Type}
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ) (r : ReactionId)
    (hxStar : ∀ s, 0 < xStar s) :
    N.massActionFlux k x r =
      N.massActionFlux k xStar r *
        N.complexActivityRatio xStar x (N.source r) := by
  unfold massActionFlux complexActivityRatio complexMonomialVector reactant
  field_simp [ne_of_gt (complex_monomial_pos_compatibility
    (N.complex (N.source r)) xStar hxStar)]

private theorem complexBalanced_of_activityRatio_source_eq_target
    {Species ComplexId ReactionId : Type}
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ)
    (hbal : N.IsComplexBalanced k xStar) (hx : ∀ s, 0 < x s)
    (hedge : ∀ r, N.complexActivityRatio xStar x (N.source r) =
      N.complexActivityRatio xStar x (N.target r)) :
    N.IsComplexBalanced k x := by
  refine ⟨hbal.1, hx, ?_⟩
  intro c
  calc
    (∑ r, if N.target r = c then N.massActionFlux k x r else 0) =
        (∑ r, if N.target r = c then
          N.massActionFlux k xStar r *
            N.complexActivityRatio xStar x c else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      split_ifs with hrc
      · rw [massActionFlux_eq_reference_mul_activityRatio_compatibility
          N k xStar x r hbal.2.1, hedge r, hrc]
      · rfl
    _ = (∑ r, if N.target r = c then
          N.massActionFlux k xStar r else 0) *
        N.complexActivityRatio xStar x c := by
      rw [Finset.sum_mul]
      simp only [ite_mul, zero_mul]
    _ = (∑ r, if N.source r = c then
          N.massActionFlux k xStar r else 0) *
        N.complexActivityRatio xStar x c := by
      rw [hbal.2.2 c]
    _ = (∑ r, if N.source r = c then
          N.massActionFlux k xStar r *
            N.complexActivityRatio xStar x c else 0) := by
      rw [Finset.sum_mul]
      simp only [ite_mul, zero_mul]
    _ = (∑ r, if N.source r = c then N.massActionFlux k x r else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      split_ifs with hrc
      · rw [massActionFlux_eq_reference_mul_activityRatio_compatibility
          N k xStar x r hbal.2.1, hrc]
      · rfl

private theorem activityRatio_source_eq_target_of_orbital_zero
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
    [DecidableEq Species] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ)
    (hbal : N.IsComplexBalanced k xStar) (hx : ∀ s, 0 < x s)
    (horbit : N.pseudoHelmholtzOrbitalDerivative k xStar x = 0) :
    ∀ r, N.complexActivityRatio xStar x (N.source r) =
      N.complexActivityRatio xStar x (N.target r) := by
  have hderiv :=
    N.pseudoHelmholtz_derivative_eq_neg_dissipation k xStar x hbal hx
  rw [horbit] at hderiv
  have hdiss : N.complexBalanceDissipation k xStar x = 0 :=
    neg_eq_zero.mp hderiv.symm
  exact
    (N.complexBalanceDissipation_eq_zero_iff_activityRatio_source_eq_target
      k xStar x hbal hx).mp hdiss

private theorem positiveSteadyState_isComplexBalanced_core
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
    [DecidableEq Species] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ)
    (hbal : N.IsComplexBalanced k xStar) (hx : ∀ s, 0 < x s)
    (hsteady : N.IsSteadyState k x) :
    N.IsComplexBalanced k x := by
  have horbit : N.pseudoHelmholtzOrbitalDerivative k xStar x = 0 := by
    unfold pseudoHelmholtzOrbitalDerivative
    rw [hsteady]
    simp
  exact complexBalanced_of_activityRatio_source_eq_target N k xStar x hbal hx
    (activityRatio_source_eq_target_of_orbital_zero
      N k xStar x hbal hx horbit)

private theorem logOrthogonal_of_activityRatio_source_eq_target
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (xStar x : Species → ℝ)
    (hxStar : ∀ s, 0 < xStar s) (hx : ∀ s, 0 < x s)
    (hedge : ∀ r, N.complexActivityRatio xStar x (N.source r) =
      N.complexActivityRatio xStar x (N.target r)) :
    ∀ v ∈ N.stoichiometricSubspace,
      ∑ s, (Real.log (x s) - Real.log (xStar s)) * v s = 0 := by
  intro v hv
  rcases hv with ⟨a, rfl⟩
  change ∑ s, (Real.log (x s) - Real.log (xStar s)) *
    Matrix.mulVec N.stoichiometricMatrix a s = 0
  simp only [stoichiometricMatrix_mulVec_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r hr
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul,
    log_pairing_reactionVector_compatibility N xStar x r hxStar hx,
    hedge r,
    div_self (ne_of_gt (complexActivityRatio_pos_compatibility
      N xStar x (N.target r) hxStar hx)), Real.log_one, zero_mul]

private theorem activityRatio_source_eq_target_of_logOrthogonal
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (xStar x : Species → ℝ)
    (hxStar : ∀ s, 0 < xStar s) (hx : ∀ s, 0 < x s)
    (horth : ∀ v ∈ N.stoichiometricSubspace,
      ∑ s, (Real.log (x s) - Real.log (xStar s)) * v s = 0) :
    ∀ r, N.complexActivityRatio xStar x (N.source r) =
      N.complexActivityRatio xStar x (N.target r) := by
  intro r
  have hrv : N.reactionVector r ∈ N.stoichiometricSubspace := by
    rw [N.stoichiometricSubspace_eq_span]
    apply Submodule.subset_span
    exact ⟨r, rfl⟩
  have hdot := horth (N.reactionVector r) hrv
  rw [log_pairing_reactionVector_compatibility N xStar x r hxStar hx] at hdot
  have hlog :
      Real.log
          (N.complexActivityRatio xStar x (N.target r) /
            N.complexActivityRatio xStar x (N.source r)) =
        Real.log 1 := by
    simpa using hdot
  have hratio :
      N.complexActivityRatio xStar x (N.target r) /
          N.complexActivityRatio xStar x (N.source r) = 1 :=
    Real.strictMonoOn_log.injOn
      (div_pos
        (complexActivityRatio_pos_compatibility
          N xStar x (N.target r) hxStar hx)
        (complexActivityRatio_pos_compatibility
          N xStar x (N.source r) hxStar hx))
      (by simpa only [Set.mem_Ioi] using (zero_lt_one : (0 : ℝ) < 1)) hlog
  exact ((div_eq_one_iff_eq (ne_of_gt
    (complexActivityRatio_pos_compatibility
      N xStar x (N.source r) hxStar hx))).mp hratio).symm

private theorem isComplexBalanced_iff_logOrthogonal_core
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
    [DecidableEq Species] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ)
    (hbal : N.IsComplexBalanced k xStar) (hx : ∀ s, 0 < x s) :
    (N.IsComplexBalanced k x ↔
      ∀ v ∈ N.stoichiometricSubspace,
        ∑ s, (Real.log (x s) - Real.log (xStar s)) * v s = 0) := by
  constructor
  · intro hxbal
    apply logOrthogonal_of_activityRatio_source_eq_target
      N xStar x hbal.2.1 hx
    have hsteady := N.complexBalanced_isSteadyState k x hxbal
    have horbit : N.pseudoHelmholtzOrbitalDerivative k xStar x = 0 := by
      unfold pseudoHelmholtzOrbitalDerivative
      rw [hsteady]
      simp
    exact activityRatio_source_eq_target_of_orbital_zero
      N k xStar x hbal hx horbit
  · intro horth
    exact complexBalanced_of_activityRatio_source_eq_target N k xStar x hbal hx
      (activityRatio_source_eq_target_of_logOrthogonal
        N xStar x hbal.2.1 hx horth)

/-- Every positive stoichiometric compatibility class contains exactly one
positive complex-balanced state relative to a complex-balanced reference. -/
theorem existsUnique_positiveComplexBalanced_compatible
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
    [DecidableEq Species] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar : Species → ℝ)
    (hbal : N.IsComplexBalanced k xStar) :
    ∀ x, (∀ s, 0 < x s) →
      ∃! y : Species → ℝ, (∀ s, 0 < y s) ∧
        N.StoichiometricallyCompatible x y ∧ N.IsComplexBalanced k y := by
  intro x hx
  obtain ⟨y, hy, huniq⟩ :=
    existsUnique_positive_logOrthogonal_mem_affineClass
      N.stoichiometricSubspace xStar x hbal.2.1 hx
  refine ⟨y, ⟨hy.1, hy.2.1, ?_⟩, ?_⟩
  · exact (isComplexBalanced_iff_logOrthogonal_core
      N k xStar y hbal hy.1).2 hy.2.2
  · intro z hz
    apply huniq z
    exact ⟨hz.1, hz.2.1,
      (isComplexBalanced_iff_logOrthogonal_core
        N k xStar z hbal hz.1).1 hz.2.2⟩

/-- Every positive stoichiometric compatibility class contains exactly one
positive mass-action steady state in a complex-balanced system. -/
theorem existsUnique_positiveSteadyState_compatible
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
    [DecidableEq Species] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar : Species → ℝ)
    (hbal : N.IsComplexBalanced k xStar) :
    ∀ x, (∀ s, 0 < x s) →
      ∃! y : Species → ℝ, (∀ s, 0 < y s) ∧
        N.StoichiometricallyCompatible x y ∧ N.IsSteadyState k y := by
  intro x hx
  obtain ⟨y, hy, huniq⟩ :=
    N.existsUnique_positiveComplexBalanced_compatible k xStar hbal x hx
  refine ⟨y, ⟨hy.1, hy.2.1,
    N.complexBalanced_isSteadyState k y hy.2.2⟩, ?_⟩
  intro z hz
  apply huniq z
  exact ⟨hz.1, hz.2.1,
    positiveSteadyState_isComplexBalanced_core
      N k xStar z hbal hz.1 hz.2.2⟩

/-- The pointwise logarithmic concentration ratio relative to a reference
state. -/
def logConcentrationRatio {Species : Type}
    (xStar x : Species → ℝ) : Species → ℝ :=
  fun s ↦ Real.log (x s) - Real.log (xStar s)

/-- Relative to a complex-balanced reference, the positive complex-balanced
locus is exactly the relative-log orthogonal locus. -/
theorem isComplexBalanced_iff_logConcentrationRatio_orthogonal
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
    [DecidableEq Species] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ)
    (hbal : N.IsComplexBalanced k xStar) (hx : ∀ s, 0 < x s) :
    (N.IsComplexBalanced k x ↔
      N.IsStoichiometricallyOrthogonal
        (ChemistryLib.ReactionNetwork.logConcentrationRatio xStar x)) := by
  simpa [IsStoichiometricallyOrthogonal, logConcentrationRatio] using
    (isComplexBalanced_iff_logOrthogonal_core N k xStar x hbal hx)

/-- The orthogonality predicate unfolds to its finite-dot-product form. -/
theorem isStoichiometricallyOrthogonal_iff
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (z : Species → ℝ) :
    (N.IsStoichiometricallyOrthogonal z ↔
      ∀ v ∈ N.stoichiometricSubspace, ∑ s, z s * v s = 0) := by
  rfl

/-- Evaluation of the logarithmic concentration ratio. -/
theorem logConcentrationRatio_apply {Species : Type}
    (xStar x : Species → ℝ) (s : Species) :
    ChemistryLib.ReactionNetwork.logConcentrationRatio xStar x s =
      Real.log (x s) - Real.log (xStar s) := by
  rfl

/-- Every positive steady state of a system admitting a complex-balanced
reference state is itself complex-balanced. -/
theorem positiveSteadyState_isComplexBalanced
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
    [DecidableEq Species] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ)
    (hbal : N.IsComplexBalanced k xStar) (hx : ∀ s, 0 < x s)
    (hsteady : N.IsSteadyState k x) :
    N.IsComplexBalanced k x := by
  exact positiveSteadyState_isComplexBalanced_core
    N k xStar x hbal hx hsteady

/-- Stoichiometric compatibility unfolds to affine subspace membership. -/
theorem stoichiometricallyCompatible_iff
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (x y : Species → ℝ) :
    (N.StoichiometricallyCompatible x y ↔
      y - x ∈ N.stoichiometricSubspace) := by
  rfl

end

end ChemistryLib.ReactionNetwork
