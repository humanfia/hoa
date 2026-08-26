import ChemistryLib.Autocatalysis.Criteria

/-!
# Exact dual certificates for non-production

An integer potential separates a target species from the species admitted as
inputs.  Its weighted amount cannot increase in any reaction, so the exact
integer balance of a food-supported hyperflow forces the target output to
vanish.  This is only the soundness direction: no Farkas-style existence or
completeness statement is asserted.

Source references:
* ANDERSEN-ETAL-2021, Definition 5 and equation (9).
* `corpus.scope:autocatalysis.oscillation`, dual-certificate contract.
-/

namespace ChemistryLib.Autocatalysis

/-- Exact integer separating-potential data certifying that `target` cannot be
produced from inputs supported on `food`. -/
structure ProductionDualCertificate
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (food : Finset Species) (target : Species) : Type where
  potential : Species → ℤ
  potential_nonnegative : ∀ s, 0 ≤ potential s
  potential_zero_on_food : ∀ s ∈ food, potential s = 0
  potential_positive_target : 0 < potential target
  reaction_nonincreasing : ∀ r,
    (∑ s, potential s *
      ((N.product r s : ℤ) - (N.reactant r s : ℤ))) ≤ 0

/-- A separating potential forces every food-supported hyperflow to have zero
target output. -/
theorem output_eq_zero_of_dual
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    {food : Finset Species} {target : Species}
    (certificate : ProductionDualCertificate N food target) :
    ∀ f : IntegerHyperflow N, InputSupported food f → f.output target = 0 := by
  classical
  intro f hsupported
  have hinput : ∑ s, certificate.potential s * f.input s = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    by_cases hzero : f.input s = 0
    · simp [hzero]
    · have hpositive : 0 < f.input s :=
        lt_of_le_of_ne (f.input_nonnegative s) (Ne.symm hzero)
      rw [certificate.potential_zero_on_food s (hsupported s hpositive)]
      simp
  have hreactions :
      (∑ r, (∑ s, certificate.potential s *
        ((N.product r s : ℤ) - (N.reactant r s : ℤ))) * f.reaction r) ≤ 0 := by
    apply Finset.sum_nonpos
    intro r hr
    exact mul_nonpos_of_nonpos_of_nonneg
      (certificate.reaction_nonincreasing r) (f.reaction_nonnegative r)
  have hbalance :
      (∑ s, certificate.potential s * (f.output s - f.input s)) =
        ∑ r, (∑ s, certificate.potential s *
          ((N.product r s : ℤ) - (N.reactant r s : ℤ))) * f.reaction r := by
    calc
      (∑ s, certificate.potential s * (f.output s - f.input s)) =
          ∑ s, certificate.potential s * reactionChangeZ N f.reaction s := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [congrFun f.balance s]
      _ = ∑ r, (∑ s, certificate.potential s *
          ((N.product r s : ℤ) - (N.reactant r s : ℤ))) * f.reaction r := by
            simp only [reactionChangeZ, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            simp only [mul_assoc]
  have hnet :
      (∑ s, certificate.potential s * (f.output s - f.input s)) ≤ 0 := by
    rw [hbalance]
    exact hreactions
  have houtput : ∑ s, certificate.potential s * f.output s ≤ 0 := by
    calc
      (∑ s, certificate.potential s * f.output s) =
          (∑ s, certificate.potential s * f.output s) -
            ∑ s, certificate.potential s * f.input s := by rw [hinput, sub_zero]
      _ = ∑ s, certificate.potential s * (f.output s - f.input s) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ ≤ 0 := hnet
  have htarget_le :
      certificate.potential target * f.output target ≤
        ∑ s, certificate.potential s * f.output s := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun s ↦ certificate.potential s * f.output s)
      (fun s hs ↦ mul_nonneg (certificate.potential_nonnegative s)
        (f.output_nonnegative s)) (Finset.mem_univ target)
  have hproduct : certificate.potential target * f.output target = 0 := by
    apply le_antisymm (htarget_le.trans houtput)
    exact mul_nonneg (certificate.potential_nonnegative target)
      (f.output_nonnegative target)
  rcases mul_eq_zero.mp hproduct with hpotential | htarget
  · exact (ne_of_gt certificate.potential_positive_target hpotential).elim
  · exact htarget

/-- A food-supported formal autocatalytic witness is exclusive when a dual
certificate rules out target production from food alone. -/
theorem exclusiveAutocatalytic_of_formal_and_dual
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    {food : Finset Species} {target : Species}
    {f : IntegerHyperflow N}
    (hsupported : InputSupported
      (@insert Species (Finset Species) (by classical infer_instance) target food) f)
    (hformal : FormalAutocatalytic f target)
    (certificate : ProductionDualCertificate N food target) :
    ExclusiveAutocatalytic (N := N) food target := by
  classical
  constructor
  · exact ⟨f, hsupported, hformal⟩
  · rintro ⟨g, hg_supported, hg_input, hg_output⟩
    have hg_zero := output_eq_zero_of_dual certificate g hg_supported
    exact (ne_of_gt hg_output) hg_zero

end ChemistryLib.Autocatalysis
