import ChemistryLib.ReactionNetwork.Balance
import ChemistryLib.Stochastic.ClosedClassProduct

/-!
# Complex-balanced Poisson product forms

This module records the finite-reaction master-equation identity and its
finite closed-class stationary-distribution consequence from
Anderson--Craciun--Kurtz (2010), Section 4, equations (4.2)--(4.4) and
Theorem 4.1.  For a reaction, the incoming term at `x` is evaluated at the
predecessor count state obtained by subtracting the product complex and adding
the reactant complex; the term is zero when the product complex is not
available at `x`.

Only algebraic stationarity on an explicitly finite closed irreducible class
is asserted.  No countably infinite process, nonexplosion, uniqueness,
convergence, or path-space statement is constructed here.
-/

open scoped BigOperators

namespace ChemistryLib.Stochastic

noncomputable section

/-- Total raw Poisson-product inflow at a count state.  Each summand is the
product weight at the reaction-specific predecessor multiplied by the
mass-action propensity there; if the product complex cannot be subtracted
from `x`, that reaction contributes zero. -/
def productFormIncomingRate
    {Species Complex Reaction : Type}
    [Fintype Species] [Fintype Reaction]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (c : Species → ℝ) (x : CountState Species) : ℝ :=
  ∑ r,
    if ∀ i, N.product r i ≤ x i then
      let z : CountState Species :=
        fun i ↦ x i - N.product r i + N.reactant r i
      poissonProductWeight c z * massActionPropensity N κ r z
    else
      0

/-- Total raw Poisson-product outflow at a count state: its product weight
times the sum of all mass-action propensities enabled there. -/
def productFormOutgoingRate
    {Species Complex Reaction : Type}
    [Fintype Species] [Fintype Reaction]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (c : Species → ℝ) (x : CountState Species) : ℝ :=
  poissonProductWeight c x * ∑ r, massActionPropensity N κ r x

/-! ## Project-local Mathlib supplement — Poisson factorial cancellation -/

private def complexResidualWeight
    {Species : Type} [Fintype Species]
    (c : Species → ℝ) (y : ChemistryLib.Complex Species)
    (x : CountState Species) : ℝ :=
  if ∀ i, y i ≤ x i then
    ∏ i, poissonFactor (c i) (x i - y i)
  else
    0

private theorem poissonFactor_mul_fallingFactorial_add
    (c : ℝ) (m a : ℕ) :
    poissonFactor c (m + a) * (fallingFactorial (m + a) a : ℝ) =
      c ^ a * poissonFactor c m := by
  unfold poissonFactor fallingFactorial
  have hma : a ≤ m + a := Nat.le_add_left a m
  have hfac0 := Nat.factorial_mul_descFactorial hma
  have hsub : m + a - a = m := by omega
  rw [hsub] at hfac0
  have hfacR :
      (m.factorial : ℝ) * ((m + a).descFactorial a : ℝ) =
        ((m + a).factorial : ℝ) := by
    exact_mod_cast hfac0
  rw [pow_add]
  field_simp
  rw [← hfacR]
  ring

private theorem poissonProductWeight_mul_fallingFactorial_add
    {Species : Type} [Fintype Species]
    (c : Species → ℝ) (m a : Species → ℕ) :
    poissonProductWeight c (fun i ↦ m i + a i) *
        ∏ i, (fallingFactorial (m i + a i) (a i) : ℝ) =
      (∏ i, c i ^ a i) * ∏ i, poissonFactor (c i) (m i) := by
  unfold poissonProductWeight
  rw [← Finset.prod_mul_distrib]
  simp_rw [poissonFactor_mul_fallingFactorial_add]
  exact Finset.prod_mul_distrib

private theorem poissonProductWeight_mul_massActionFactor_add
    {Species : Type} [Fintype Species]
    (c : Species → ℝ) (k : ℝ) (m : Species → ℕ)
    (a : ChemistryLib.Complex Species) :
    poissonProductWeight c (fun i ↦ m i + a i) *
        (k * ∏ i, (fallingFactorial (m i + a i) (a i) : ℝ)) =
      (k * ChemistryLib.Complex.monomial a c) *
        ∏ i, poissonFactor (c i) (m i) := by
  rw [show ChemistryLib.Complex.monomial a c = ∏ i, c i ^ a i by
    exact Finsupp.prod_pow a c]
  rw [show poissonProductWeight c (fun i ↦ m i + a i) *
        (k * ∏ i, (fallingFactorial (m i + a i) (a i) : ℝ)) =
      k * (poissonProductWeight c (fun i ↦ m i + a i) *
        ∏ i, (fallingFactorial (m i + a i) (a i) : ℝ)) by ring]
  rw [poissonProductWeight_mul_fallingFactorial_add]
  ring

private theorem incomingReactionWeight_eq_complexResidualWeight
    {Species Complex Reaction : Type} [Fintype Species]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (c : Species → ℝ) (x : CountState Species)
    (r : Reaction) (h : ∀ i, N.product r i ≤ x i) :
    poissonProductWeight c
        (fun i ↦ x i - N.product r i + N.reactant r i) *
      massActionPropensity N κ r
        (fun i ↦ x i - N.product r i + N.reactant r i) =
      N.massActionFlux κ c r *
        complexResidualWeight c (N.product r) x := by
  rw [complexResidualWeight, if_pos h]
  unfold massActionPropensity ChemistryLib.ReactionNetwork.massActionFlux
  exact poissonProductWeight_mul_massActionFactor_add c (κ r)
    (fun i ↦ x i - N.product r i) (N.reactant r)

private theorem outgoingReactionWeight_eq_complexResidualWeight
    {Species Complex Reaction : Type} [Fintype Species]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (c : Species → ℝ) (x : CountState Species)
    (r : Reaction) :
    poissonProductWeight c x * massActionPropensity N κ r x =
      N.massActionFlux κ c r *
        complexResidualWeight c (N.reactant r) x := by
  by_cases h : CanFire N r x
  · have h' : ∀ i, N.reactant r i ≤ x i := h
    rw [complexResidualWeight, if_pos h']
    have hx : x = fun i ↦ (x i - N.reactant r i) + N.reactant r i := by
      funext i
      exact (Nat.sub_add_cancel (h i)).symm
    conv_lhs => rw [hx]
    unfold massActionPropensity ChemistryLib.ReactionNetwork.massActionFlux
    exact poissonProductWeight_mul_massActionFactor_add c (κ r)
      (fun i ↦ x i - N.reactant r i) (N.reactant r)
  · have h' : ¬ ∀ i, N.reactant r i ≤ x i := h
    rw [complexResidualWeight, if_neg h',
      massActionPropensity_eq_zero_of_not_canFire N κ r x h]
    simp

private theorem sum_fiberwise
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (v : A → ℝ) (w : B → ℝ) :
    (∑ a, v a * w (f a)) =
      ∑ b, (∑ a, if f a = b then v a else 0) * w b := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  simp

/-- Deterministic complex balance gives the pointwise master-equation balance
of the raw Poisson product weight.  This is the algebraic content of
ACK-2010, Section 4, equations (4.2)--(4.4). -/
theorem complexBalanced_productForm_pointwiseStationary
    {Species Complex Reaction : Type}
    [Fintype Species] [Fintype Complex] [Fintype Reaction]
    [DecidableEq Complex]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (c : Species → ℝ)
    (hcb : N.IsComplexBalanced κ c) :
    ∀ x, productFormIncomingRate N κ c x =
      productFormOutgoingRate N κ c x := by
  classical
  intro x
  have hin :
      productFormIncomingRate N κ c x =
        ∑ r, N.massActionFlux κ c r *
          complexResidualWeight c (N.product r) x := by
    unfold productFormIncomingRate
    apply Finset.sum_congr rfl
    intro r _hr
    by_cases h : ∀ i, N.product r i ≤ x i
    · rw [if_pos h]
      dsimp only
      exact incomingReactionWeight_eq_complexResidualWeight N κ c x r h
    · rw [if_neg h, complexResidualWeight, if_neg h]
      simp
  have hout :
      productFormOutgoingRate N κ c x =
        ∑ r, N.massActionFlux κ c r *
          complexResidualWeight c (N.reactant r) x := by
    unfold productFormOutgoingRate
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    exact outgoingReactionWeight_eq_complexResidualWeight N κ c x r
  rw [hin, hout]
  rcases hcb with ⟨_hκ, _hc, hbal⟩
  change (∑ r, N.massActionFlux κ c r *
      complexResidualWeight c (N.complex (N.target r)) x) =
    ∑ r, N.massActionFlux κ c r *
      complexResidualWeight c (N.complex (N.source r)) x
  rw [sum_fiberwise N.target (N.massActionFlux κ c)
      (fun y ↦ complexResidualWeight c (N.complex y) x)]
  rw [sum_fiberwise N.source (N.massActionFlux κ c)
      (fun y ↦ complexResidualWeight c (N.complex y) x)]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [hbal y]

private def productFormIncomingReactionRate
    {Species Complex Reaction : Type} [Fintype Species]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (c : Species → ℝ) (r : Reaction)
    (y : CountState Species) : ℝ :=
  if ∀ i, N.product r i ≤ y i then
    let z : CountState Species :=
      fun i ↦ y i - N.product r i + N.reactant r i
    poissonProductWeight c z * massActionPropensity N κ r z
  else
    0

private theorem product_le_of_canFire_fire_eq
    {Species Complex Reaction : Type}
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (r : Reaction) (z y : CountState Species)
    (hz : CanFire N r z) (hfire : fire N z r = y) :
    ∀ i, N.product r i ≤ y i := by
  intro i
  have hi := congr_fun hfire i
  unfold fire at hi
  have hcan := hz i
  omega

private theorem eq_predecessor_of_canFire_fire_eq
    {Species Complex Reaction : Type}
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (r : Reaction) (z y : CountState Species)
    (hz : CanFire N r z) (hfire : fire N z r = y) :
    z = fun i ↦ y i - N.product r i + N.reactant r i := by
  funext i
  have hi := congr_fun hfire i
  unfold fire at hi
  have hcan := hz i
  omega

private theorem predecessor_canFire
    {Species Complex Reaction : Type}
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (r : Reaction) (y : CountState Species)
    (_hy : ∀ i, N.product r i ≤ y i) :
    CanFire N r (fun i ↦ y i - N.product r i + N.reactant r i) := by
  intro i
  change N.reactant r i ≤ y i - N.product r i + N.reactant r i
  omega

private theorem fire_predecessor
    {Species Complex Reaction : Type}
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (r : Reaction) (y : CountState Species)
    (hy : ∀ i, N.product r i ≤ y i) :
    fire N (fun i ↦ y i - N.product r i + N.reactant r i) r = y := by
  funext i
  unfold fire
  change (y i - N.product r i + N.reactant r i) - N.reactant r i +
    N.product r i = y i
  have hyi := hy i
  omega

private theorem restrictedRateKernel_rowSum
    {Species Complex Reaction : Type}
    [Fintype Species] [Fintype Reaction]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (Ω : Finset (CountState Species))
    (hΩ : IsClosedCountClass N Ω) (x : ↥Ω) :
    ∑ y, restrictedRateKernel N κ Ω x y =
      ∑ r, massActionPropensity N κ r x.1 := by
  classical
  unfold restrictedRateKernel
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

private theorem restrictedIncomingReaction_le_productFormIncomingReactionRate
    {Species Complex Reaction : Type} [Fintype Species]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (c : Species → ℝ)
    (Ω : Finset (CountState Species))
    (hκ : ∀ r, 0 ≤ κ r) (hc : ∀ i, 0 < c i)
    (y : ↥Ω) (r : Reaction) :
    (∑ x : ↥Ω, poissonProductWeight c x.1 *
      (if fire N x.1 r = y.1 then massActionPropensity N κ r x.1 else 0)) ≤
      productFormIncomingReactionRate N κ c r y.1 := by
  classical
  by_cases hy : ∀ i, N.product r i ≤ y.1 i
  · let p : CountState Species :=
      fun i ↦ y.1 i - N.product r i + N.reactant r i
    have hpcan : CanFire N r p := predecessor_canFire N r y.1 hy
    have hpfire : fire N p r = y.1 := fire_predecessor N r y.1 hy
    by_cases hpΩ : p ∈ Ω
    · let ps : ↥Ω := ⟨p, hpΩ⟩
      have hsum :
          (∑ x : ↥Ω, poissonProductWeight c x.1 *
            (if fire N x.1 r = y.1 then
              massActionPropensity N κ r x.1 else 0)) =
            poissonProductWeight c p * massActionPropensity N κ r p := by
        rw [Finset.sum_eq_single ps]
        · simp [ps, hpfire]
        · intro z _hz hzps
          by_cases hzfire : fire N z.1 r = y.1
          · by_cases hzcan : CanFire N r z.1
            · have hzval : z.1 = p :=
                eq_predecessor_of_canFire_fire_eq N r z.1 y.1 hzcan hzfire
              exfalso
              apply hzps
              exact Subtype.ext hzval
            · have hzero :=
                massActionPropensity_eq_zero_of_not_canFire N κ r z.1 hzcan
              simp [hzfire, hzero]
          · simp [hzfire]
        · simp
      rw [hsum, productFormIncomingReactionRate, if_pos hy]
    · have hsum :
          (∑ x : ↥Ω, poissonProductWeight c x.1 *
            (if fire N x.1 r = y.1 then
              massActionPropensity N κ r x.1 else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro z _hz
        by_cases hzfire : fire N z.1 r = y.1
        · by_cases hzcan : CanFire N r z.1
          · have hzval : z.1 = p :=
              eq_predecessor_of_canFire_fire_eq N r z.1 y.1 hzcan hzfire
            exfalso
            apply hpΩ
            rw [← hzval]
            exact z.property
          · have hzero :=
              massActionPropensity_eq_zero_of_not_canFire N κ r z.1 hzcan
            simp [hzfire, hzero]
        · simp [hzfire]
      rw [hsum, productFormIncomingReactionRate, if_pos hy]
      exact mul_nonneg (poissonProductWeight_pos c hc p).le
        (massActionPropensity_nonneg N κ hκ r p)
  · have hsum :
        (∑ x : ↥Ω, poissonProductWeight c x.1 *
          (if fire N x.1 r = y.1 then
            massActionPropensity N κ r x.1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro z _hz
      by_cases hzfire : fire N z.1 r = y.1
      · have hznot : ¬ CanFire N r z.1 := by
          intro hzcan
          exact hy (product_le_of_canFire_fire_eq N r z.1 y.1 hzcan hzfire)
        have hzero :=
          massActionPropensity_eq_zero_of_not_canFire N κ r z.1 hznot
        simp [hzfire, hzero]
      · simp [hzfire]
    rw [hsum, productFormIncomingReactionRate, if_neg hy]

private theorem restrictedIncoming_le_productFormIncomingRate
    {Species Complex Reaction : Type}
    [Fintype Species] [Fintype Reaction]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (c : Species → ℝ)
    (Ω : Finset (CountState Species))
    (hκ : ∀ r, 0 ≤ κ r) (hc : ∀ i, 0 < c i)
    (y : ↥Ω) :
    (∑ x : ↥Ω, poissonProductWeight c x.1 *
        restrictedRateKernel N κ Ω x y) ≤
      productFormIncomingRate N κ c y.1 := by
  classical
  unfold restrictedRateKernel
  change (∑ x : ↥Ω, poissonProductWeight c x.1 *
      ∑ r, if fire N x.1 r = y.1 then
        massActionPropensity N κ r x.1 else 0) ≤
    ∑ r, productFormIncomingReactionRate N κ c r y.1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro r _hr
  exact restrictedIncomingReaction_le_productFormIncomingReactionRate
    N κ c Ω hκ hc y r

private theorem restrictedIncoming_eq_productFormIncomingRate
    {Species Complex Reaction : Type}
    [Fintype Species] [Fintype Complex] [Fintype Reaction]
    [DecidableEq Complex]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (c : Species → ℝ)
    (Ω : Finset (CountState Species))
    (hcb : N.IsComplexBalanced κ c)
    (hclosed : IsClosedCountClass N Ω) (y : ↥Ω) :
    (∑ x : ↥Ω, poissonProductWeight c x.1 *
        restrictedRateKernel N κ Ω x y) =
      productFormIncomingRate N κ c y.1 := by
  classical
  have hκ : ∀ r, 0 ≤ κ r := fun r ↦ (hcb.1 r).le
  have hc : ∀ i, 0 < c i := hcb.2.1
  have hle : ∀ z : ↥Ω,
      (∑ x : ↥Ω, poissonProductWeight c x.1 *
          restrictedRateKernel N κ Ω x z) ≤
        productFormIncomingRate N κ c z.1 :=
    fun z ↦ restrictedIncoming_le_productFormIncomingRate N κ c Ω hκ hc z
  have hsum :
      (∑ z : ↥Ω, ∑ x : ↥Ω, poissonProductWeight c x.1 *
          restrictedRateKernel N κ Ω x z) =
        ∑ z : ↥Ω, productFormIncomingRate N κ c z.1 := by
    calc
      (∑ z : ↥Ω, ∑ x : ↥Ω, poissonProductWeight c x.1 *
          restrictedRateKernel N κ Ω x z) =
          ∑ x : ↥Ω, poissonProductWeight c x.1 *
            ∑ z : ↥Ω, restrictedRateKernel N κ Ω x z := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _hx
        rw [Finset.mul_sum]
      _ = ∑ x : ↥Ω, productFormOutgoingRate N κ c x.1 := by
        apply Finset.sum_congr rfl
        intro x _hx
        unfold productFormOutgoingRate
        rw [restrictedRateKernel_rowSum N κ Ω hclosed x]
      _ = ∑ z : ↥Ω, productFormIncomingRate N κ c z.1 := by
        apply Finset.sum_congr rfl
        intro z _hz
        exact (complexBalanced_productForm_pointwiseStationary N κ c hcb z.1).symm
  have hall := (Finset.sum_eq_sum_iff_of_le
    (s := (Finset.univ : Finset ↥Ω)) (fun z _hz ↦ hle z)).mp hsum
  exact hall y (Finset.mem_univ y)

private theorem restrictedRateKernel_raw_globalBalance
    {Species Complex Reaction : Type}
    [Fintype Species] [Fintype Complex] [Fintype Reaction]
    [DecidableEq Complex]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (c : Species → ℝ)
    (Ω : Finset (CountState Species))
    (hcb : N.IsComplexBalanced κ c)
    (hclosed : IsClosedCountClass N Ω) (y : ↥Ω) :
    (∑ x : ↥Ω, poissonProductWeight c x.1 *
        restrictedRateKernel N κ Ω x y) =
      poissonProductWeight c y.1 *
        ∑ z : ↥Ω, restrictedRateKernel N κ Ω y z := by
  rw [restrictedIncoming_eq_productFormIncomingRate N κ c Ω hcb hclosed y]
  rw [complexBalanced_productForm_pointwiseStationary N κ c hcb y.1]
  unfold productFormOutgoingRate
  rw [restrictedRateKernel_rowSum N κ Ω hclosed y]

private theorem generator_sum_eq_zero_of_globalBalance
    {State : Type} [Fintype State]
    (q : RateKernel State) (μ : State → ℝ)
    (hbal : ∀ y, (∑ x, μ x * q x y) = μ y * ∑ z, q y z)
    (f : State → ℝ) :
    ∑ x, μ x * generator q f x = 0 := by
  unfold generator
  calc
    (∑ x, μ x * ∑ y, q x y * (f y - f x)) =
        ∑ x, ((∑ y, μ x * q x y * f y) -
          ∑ y, μ x * q x y * f x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _hy
      ring
    _ = (∑ x, ∑ y, μ x * q x y * f y) -
        ∑ x, ∑ y, μ x * q x y * f x := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ y, (∑ x, μ x * q x y) * f y) -
        ∑ x, μ x * (∑ y, q x y) * f x := by
      congr 1
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _hy
        rw [Finset.sum_mul]
      · apply Finset.sum_congr rfl
        intro x _hx
        calc
          (∑ y, μ x * q x y * f x) =
              (∑ y, μ x * q x y) * f x := by
            rw [Finset.sum_mul]
          _ = μ x * (∑ y, q x y) * f x := by
            rw [Finset.mul_sum]
    _ = 0 := by
      simp_rw [hbal]
      ring

/-- On a finite closed irreducible count class, the normalized restriction of
the Poisson product weight is a stationary distribution for the restricted
mass-action rate kernel.  This is the finite-class specialization of
ACK-2010, Theorem 4.1. -/
theorem complexBalanced_finiteClosedIrreducibleClass_productForm_stationary
    {Species Complex Reaction : Type}
    [Fintype Species] [Fintype Complex] [Fintype Reaction]
    [DecidableEq Complex]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (c : Species → ℝ)
    (Ω : Finset (CountState Species))
    (hcb : N.IsComplexBalanced κ c)
    (hclosed : IsClosedCountClass N Ω)
    (hirreducible : IsIrreducibleCountClass N Ω) :
    IsStationaryDistribution (restrictedRateKernel N κ Ω)
      (classProductForm c Ω) := by
  classical
  have hc : ∀ i, 0 < c i := hcb.2.1
  have hΩ : Ω.Nonempty := irreducibleCountClass_nonempty N Ω hirreducible
  have hZ : 0 < classNormalization c Ω := classNormalization_pos c Ω hc hΩ
  refine ⟨classProductForm_nonneg c Ω hc hZ,
    classProductForm_sum_eq_one c Ω hZ, ?_⟩
  intro f
  have hraw :
      ∑ x : ↥Ω, poissonProductWeight c x.1 *
          generator (restrictedRateKernel N κ Ω) f x = 0 :=
    generator_sum_eq_zero_of_globalBalance
      (restrictedRateKernel N κ Ω) (fun x ↦ poissonProductWeight c x.1)
      (restrictedRateKernel_raw_globalBalance N κ c Ω hcb hclosed) f
  unfold classProductForm
  simp_rw [div_eq_mul_inv]
  calc
    (∑ x : ↥Ω, (poissonProductWeight c x.1 *
        (classNormalization c Ω)⁻¹) *
          generator (restrictedRateKernel N κ Ω) f x) =
        ∑ x : ↥Ω, (poissonProductWeight c x.1 *
          generator (restrictedRateKernel N κ Ω) f x) *
            (classNormalization c Ω)⁻¹ := by
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = (∑ x : ↥Ω, poissonProductWeight c x.1 *
          generator (restrictedRateKernel N κ Ω) f x) *
            (classNormalization c Ω)⁻¹ := by
      rw [Finset.sum_mul]
    _ = 0 := by rw [hraw, zero_mul]

end

end ChemistryLib.Stochastic
