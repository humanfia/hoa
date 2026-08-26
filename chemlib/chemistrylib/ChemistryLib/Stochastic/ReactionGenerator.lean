import ChemistryLib.Stochastic.FiniteGenerator
import ChemistryLib.Stochastic.Propensity

/-!
# Reaction generators on finite closed count classes

This module defines the stochastic chemical reaction generator from ACK-2010,
Section 3.1, equations (3.3)--(3.5), and its restriction to a finite closed
count-state class as used in Section 4, Theorem 4.1.  The source is recorded by
artifact `222b8bed89ef875d89943a8634560dc29758ab803d5ad7054cb639fe21280c3c`
and the sanitized research contracts `research:ack_2010:ctmc_generator` and
`research:ack_2010:product_form_stationary`.

Only the finite algebraic rate kernel and its generator are constructed here;
no stochastic process, nonexplosion, or long-time assertion is made.
-/

open scoped BigOperators

namespace ChemistryLib.Stochastic

/-- The mass-action reaction generator, as a finite sum over reaction indices. -/
def reactionGenerator {Species Complex Reaction : Type} [Fintype Species]
    [Fintype Reaction]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (f : CountState Species → ℝ)
    (x : CountState Species) : ℝ :=
  ∑ r, massActionPropensity N κ r x * (f (fire N x r) - f x)

/-- The reaction generator annihilates constant functions. -/
theorem reactionGenerator_const {Species Complex Reaction : Type} [Fintype Species]
    [Fintype Reaction]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (a : ℝ) (x : CountState Species) :
    reactionGenerator N κ (fun _ ↦ a) x = 0 := by
  simp [reactionGenerator]

/-- A finite count class is closed when every enabled reaction stays in it. -/
def IsClosedCountClass {Species Complex Reaction : Type}
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (Ω : Finset (CountState Species)) : Prop := by
  classical
  exact ∀ ⦃x⦄, x ∈ Ω → ∀ r, CanFire N r x → fire N x r ∈ Ω

/-- A finite count class is irreducible when it is nonempty and every two of
its states are connected by a finite sequence of enabled internal firings. -/
def IsIrreducibleCountClass {Species Complex Reaction : Type}
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (Ω : Finset (CountState Species)) : Prop := by
  classical
  exact Ω.Nonempty ∧ ∀ x y : ↥Ω,
    Relation.ReflTransGen
      (fun u v : ↥Ω ↦ ∃ r, CanFire N r u.1 ∧ v.1 = fire N u.1 r) x y

/-- An irreducible finite count class has at least one state. -/
theorem irreducibleCountClass_nonempty {Species Complex Reaction : Type}
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (Ω : Finset (CountState Species))
    (h : IsIrreducibleCountClass N Ω) : Ω.Nonempty := by
  exact h.1

/-- The finite-state rate kernel obtained by collecting all reactions with a
given successor in the count-class subtype. -/
noncomputable def restrictedRateKernel {Species Complex Reaction : Type}
    [Fintype Species] [Fintype Reaction]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (Ω : Finset (CountState Species)) : RateKernel ↥Ω :=
  fun x y ↦ ∑ r, if fire N x.1 r = y.1 then massActionPropensity N κ r x.1 else 0

/-- Nonnegative rate constants make the restricted rate kernel a jump-rate
kernel on every closed finite count class. -/
theorem restrictedRateKernel_isJumpRateKernel
    {Species Complex Reaction : Type} [Fintype Species] [Fintype Reaction]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (Ω : Finset (CountState Species))
    (hκ : ∀ r, 0 ≤ κ r) (_hΩ : IsClosedCountClass N Ω) :
    IsJumpRateKernel (restrictedRateKernel N κ Ω) := by
  classical
  intro x y _hxy
  change 0 ≤ ∑ r, if fire N x.1 r = y.1 then massActionPropensity N κ r x.1 else 0
  have hsum : ∀ s : Finset Reaction,
      0 ≤ ∑ r ∈ s, if fire N x.1 r = y.1 then massActionPropensity N κ r x.1 else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert r s hrs ih =>
        rw [Finset.sum_insert hrs]
        apply add_nonneg
        · split
          · exact massActionPropensity_nonneg N κ hκ r x.1
          · exact le_rfl
        · exact ih
  simpa using hsum Finset.univ

/-- On a closed finite count class, the finite-state kernel generator agrees
with the unrestricted reaction generator. -/
theorem generator_restrictedRateKernel_eq_reactionGenerator
    {Species Complex Reaction : Type} [Fintype Species] [Fintype Reaction]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (Ω : Finset (CountState Species))
    (hΩ : IsClosedCountClass N Ω) (f : CountState Species → ℝ) (x : ↥Ω) :
    generator (restrictedRateKernel N κ Ω) (fun y ↦ f y.1) x =
      reactionGenerator N κ f x.1 := by
  classical
  unfold generator reactionGenerator restrictedRateKernel
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hr : CanFire N r x.1
  · let y : ↥Ω := ⟨fire N x.1 r, hΩ x.property r hr⟩
    rw [Finset.sum_eq_single y]
    · simp [y]
    · intro z _hz hzy
      have hne : fire N x.1 r ≠ z.1 := by
        intro heq
        apply hzy
        exact Subtype.ext heq.symm
      simp [hne]
    · simp
  · have hzero : massActionPropensity N κ r x.1 = 0 :=
      massActionPropensity_eq_zero_of_not_canFire N κ r x.1 hr
    simp [hzero]

end ChemistryLib.Stochastic
