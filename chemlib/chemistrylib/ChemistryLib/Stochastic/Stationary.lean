import ChemistryLib.Stochastic.FiniteGenerator

/-!
# Finite-state stationary measures

This module gives algebraic notions of stationarity for finite-state rate
kernels.  It follows ACK-2010, Section 3.1, equation (3.5), and Section 4,
equations (4.1)--(4.4), as recorded by source artifact
`222b8bed89ef875d89943a8634560dc29758ab803d5ad7054cb639fe21280c3c` and
the sanitized research contracts `research:ack_2010:ctmc_generator` and
`research:ack_2010:product_form_stationary`.

Only generator balance is expressed here.  In particular, this module
constructs no stochastic process and makes no uniqueness, convergence, or
long-time claim.
-/

open scoped BigOperators

namespace ChemistryLib.Stochastic

/-- A stationary distribution is a nonnegative, normalized weight that
annihilates the generator. -/
def IsStationaryDistribution {State : Type} [Fintype State]
    (q : RateKernel State) (π : State → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧
    (∑ x, π x = 1) ∧
      ∀ f : State → ℝ, ∑ x, π x * generator q f x = 0

/-- A stationary measure is a nonnegative weight that annihilates the
generator; unlike a stationary distribution, it need not be normalized. -/
def IsStationaryMeasure {State : Type} [Fintype State]
    (q : RateKernel State) (π : State → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧
    ∀ f : State → ℝ, ∑ x, π x * generator q f x = 0

/-- For a finite-state jump-rate kernel, a weight is stationary exactly when
it is nonnegative and annihilates the generator against every test function. -/
theorem isStationaryMeasure_iff_annihilates_generator
    {State : Type} [Fintype State]
    (q : RateKernel State) (π : State → ℝ) (_hq : IsJumpRateKernel q) :
    IsStationaryMeasure q π ↔
      ((∀ x, 0 ≤ π x) ∧
        (∀ f : State → ℝ, ∑ x, π x * generator q f x = 0)) := by
  rfl

end ChemistryLib.Stochastic
