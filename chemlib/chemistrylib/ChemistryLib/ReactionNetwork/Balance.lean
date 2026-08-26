import ChemistryLib.ReactionNetwork.Laplacian

/-!
# Detailed and complex balance

This module scaffolds the reaction-network-native balance predicates and their
connections to the weighted complex-graph Laplacian.  The definitions follow
GUNAWARDENA-2003, Section 6, Proposition 6.1, and YU-CRACIUN-2018, Section
2.1, Definitions 2.1--2.2 and equations (6)--(7).  Rate constants and
concentration states remain explicit parameters; positivity is part of each
balance predicate.

The locked `totalFluxBetween` API is intentionally generic in a supplied
reaction-indexed value.  Passing `N.massActionFlux k x` specializes it to the
mass-action aggregate while preserving parallel reaction identifiers.
-/

namespace ChemistryLib.ReactionNetwork

/-! ## Project-local Mathlib supplement — Balance predicates and graph consequences -/

/-- Every reaction has positive rate, every species has positive concentration,
and total incoming mass-action flux equals total outgoing flux at each complex.
-/
def IsComplexBalanced
    {Species ComplexId ReactionId : Type}
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ) : Prop :=
  (∀ r, 0 < k r) ∧
    (∀ s, 0 < x s) ∧
    (∀ c,
      Finset.univ.sum
          (fun r ↦ if N.target r = c then N.massActionFlux k x r else 0) =
        Finset.univ.sum
          (fun r ↦ if N.source r = c then N.massActionFlux k x r else 0))

/-- Positive rates and state, with aggregate mass-action flux equal in both
directions for every ordered pair of complexes. -/
def IsDetailedBalanced
    {Species ComplexId ReactionId : Type}
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ) : Prop :=
  (∀ r, 0 < k r) ∧
    (∀ s, 0 < x s) ∧
    (∀ a b,
      Finset.univ.sum
          (fun r ↦
            if N.source r = a ∧ N.target r = b then
              N.massActionFlux k x r
            else 0) =
        Finset.univ.sum
          (fun r ↦
            if N.source r = b ∧ N.target r = a then
              N.massActionFlux k x r
            else 0))

/-- Complex balance is equivalent to positivity together with annihilation of
the complex-monomial vector by the weighted Laplacian. -/
theorem complexBalanced_iff_weightedLaplacian
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ) :
    N.IsComplexBalanced k x ↔
    (∀ r, 0 < k r) ∧
        (∀ s, 0 < x s) ∧
          Matrix.mulVec (N.weightedLaplacian k)
              (N.complexMonomialVector x) = 0 := by
  constructor
  · rintro ⟨hk, hx, hbal⟩
    refine ⟨hk, hx, ?_⟩
    rw [N.weightedLaplacian_mulVec_complexMonomial]
    funext c
    change Finset.univ.sum
        (fun r ↦ N.incidenceMatrix c r * N.massActionFlux k x r) = 0
    simp only [incidenceMatrix]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    simpa [eq_comm] using hbal c
  · rintro ⟨hk, hx, hlap⟩
    refine ⟨hk, hx, ?_⟩
    rw [N.weightedLaplacian_mulVec_complexMonomial] at hlap
    intro c
    have hc := congr_fun hlap c
    change Finset.univ.sum
        (fun r ↦ N.incidenceMatrix c r * N.massActionFlux k x r) = 0 at hc
    simp only [incidenceMatrix] at hc
    simp_rw [sub_mul] at hc
    rw [Finset.sum_sub_distrib] at hc
    rw [sub_eq_zero] at hc
    simpa [eq_comm] using hc

/-- A complex-balanced state is a mass-action steady state. -/
theorem complexBalanced_isSteadyState
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ)
    (h : N.IsComplexBalanced k x) :
    N.IsSteadyState k x := by
  change N.massActionVectorField k x = 0
  rw [N.massActionVectorField_eq_composition_mulVec_weightedLaplacian]
  rw [(complexBalanced_iff_weightedLaplacian N k x).mp h |>.2.2]
  exact Matrix.mulVec_zero _

private theorem positive_balanced_flow_has_return_path
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (v : ReactionId → ℝ)
    (hv : ∀ q, 0 < v q)
    (hbal : ∀ c,
      Finset.univ.sum (fun q ↦ if N.target q = c then v q else 0) =
        Finset.univ.sum (fun q ↦ if N.source q = c then v q else 0))
    (r : ReactionId) :
    letI := N.reactionQuiver
    Nonempty (Quiver.Path (N.target r) (N.source r)) := by
  classical
  letI := N.reactionQuiver
  by_contra hreturn
  let reachable : Finset ComplexId :=
    Finset.univ.filter
      (fun c ↦ Nonempty (Quiver.Path (N.target r) c))
  have htarget : N.target r ∈ reachable := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨Quiver.Path.nil⟩⟩
  have hsource : N.source r ∉ reachable := by
    simp only [reachable, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hreturn
  have hclosed : ∀ q, N.source q ∈ reachable → N.target q ∈ reachable := by
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨p⟩ := hq.2
    exact ⟨p.cons
      (⟨q, rfl, rfl⟩ : Quiver.Hom (N.source q) (N.target q))⟩
  have hsum :
      Finset.univ.sum
          (fun q ↦ if N.target q ∈ reachable then v q else 0) =
        Finset.univ.sum
          (fun q ↦ if N.source q ∈ reachable then v q else 0) := by
    calc
      _ = reachable.sum (fun c ↦
          Finset.univ.sum
            (fun q ↦ if N.target q = c then v q else 0)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q hq
        exact
          (Finset.sum_ite_eq reachable (N.target q) (fun _ ↦ v q)).symm
      _ = reachable.sum (fun c ↦
          Finset.univ.sum
            (fun q ↦ if N.source q = c then v q else 0)) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hbal c
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q hq
        exact Finset.sum_ite_eq reachable (N.source q) (fun _ ↦ v q)
  have hstrict :
      Finset.univ.sum
          (fun q ↦ if N.source q ∈ reachable then v q else 0) <
        Finset.univ.sum
          (fun q ↦ if N.target q ∈ reachable then v q else 0) := by
    apply Finset.sum_lt_sum
    · intro q hq
      by_cases hs : N.source q ∈ reachable
      · have ht := hclosed q hs
        simp [hs, ht]
      · by_cases ht : N.target q ∈ reachable
        · simp [hs, ht, le_of_lt (hv q)]
        · simp [hs, ht]
    · refine ⟨r, Finset.mem_univ _, ?_⟩
      simp [hsource, htarget, hv r]
  exact (ne_of_lt hstrict) hsum.symm

/-- A positive complex-balanced flux has a weakly reversible reaction graph. -/
theorem complexBalanced_weaklyReversible
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ)
    (h : N.IsComplexBalanced k x) :
    N.WeaklyReversible := by
  rcases h with ⟨hk, hx, hbal⟩
  have hflux : ∀ q, 0 < N.massActionFlux k x q := by
    intro q
    unfold massActionFlux Complex.monomial
    apply mul_pos (hk q)
    apply Finset.prod_pos
    intro s hs
    exact pow_pos (hx s) _
  intro r
  exact positive_balanced_flow_has_return_path N
    (N.massActionFlux k x) hflux hbal r

/-- Detailed balance implies complex balance. -/
theorem detailedBalanced_complexBalanced
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ)
    (h : N.IsDetailedBalanced k x) :
    N.IsComplexBalanced k x := by
  rcases h with ⟨hk, hx, hpair⟩
  refine ⟨hk, hx, ?_⟩
  intro c
  calc
    Finset.univ.sum
        (fun r ↦ if N.target r = c then N.massActionFlux k x r else 0) =
        Finset.univ.sum (fun a ↦
          Finset.univ.sum (fun r ↦
            if N.source r = a ∧ N.target r = c then
              N.massActionFlux k x r
            else 0)) := by
      rw [← Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hrc : N.target r = c <;> simp [hrc]
    _ = Finset.univ.sum (fun a ↦
          Finset.univ.sum (fun r ↦
            if N.source r = c ∧ N.target r = a then
              N.massActionFlux k x r
            else 0)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hpair a c
    _ = Finset.univ.sum
        (fun r ↦ if N.source r = c then N.massActionFlux k x r else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hrc : N.source r = c <;> simp [hrc]

/-- Detailed balance implies weak reversibility, without requiring a finite
complex index type. -/
theorem detailedBalanced_weaklyReversible
    {Species ComplexId ReactionId : Type}
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ)
    (h : N.IsDetailedBalanced k x) :
    N.WeaklyReversible := by
  rcases h with ⟨hk, hx, hpair⟩
  have hflux : ∀ q, 0 < N.massActionFlux k x q := by
    intro q
    unfold massActionFlux Complex.monomial
    apply mul_pos (hk q)
    apply Finset.prod_pos
    intro s hs
    exact pow_pos (hx s) _
  letI := N.reactionQuiver
  intro r
  have hex : ∃ r', N.source r' = N.target r ∧ N.target r' = N.source r := by
    have hleft : 0 < Finset.univ.sum (fun q ↦
        if N.source q = N.source r ∧ N.target q = N.target r then
          N.massActionFlux k x q
        else 0) := by
      apply Finset.sum_pos'
      · intro q hq
        split_ifs
        · exact le_of_lt (hflux q)
        · exact le_rfl
      · refine ⟨r, Finset.mem_univ _, ?_⟩
        simp [hflux r]
    have hright : 0 < Finset.univ.sum (fun q ↦
        if N.source q = N.target r ∧ N.target q = N.source r then
          N.massActionFlux k x q
        else 0) := by
      rw [← hpair (N.source r) (N.target r)]
      exact hleft
    have hnonneg : ∀ q, q ∈ (Finset.univ : Finset ReactionId) →
        0 ≤ (if N.source q = N.target r ∧ N.target q = N.source r then
          N.massActionFlux k x q else 0) := by
      intro q hq
      split_ifs
      · exact le_of_lt (hflux q)
      · exact le_rfl
    obtain ⟨q, hq, hqpos⟩ :=
      (Finset.sum_pos_iff_of_nonneg hnonneg).mp hright
    by_cases hqends : N.source q = N.target r ∧ N.target q = N.source r
    · exact ⟨q, hqends.1, hqends.2⟩
    · simp [hqends] at hqpos
  obtain ⟨r', hrs, hrt⟩ := hex
  exact ⟨Quiver.Hom.toPath (⟨r', hrs, hrt⟩ : Quiver.Hom (N.target r) (N.source r))⟩

/-- The finite aggregate of supplied reaction-indexed values on reactions from
one complex to another.  Parallel reaction identifiers remain distinct. -/
def totalFluxBetween
    {Species ComplexId ReactionId : Type}
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (a b : ComplexId) : ℝ :=
  Finset.univ.sum
    (fun r ↦ if N.source r = a ∧ N.target r = b then k r else 0)

end ChemistryLib.ReactionNetwork
