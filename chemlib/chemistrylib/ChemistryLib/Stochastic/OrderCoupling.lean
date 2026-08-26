import Mathlib.Data.Fintype.Prod
import ChemistryLib.Stochastic.FiniteGenerator

/-!
# Finite-state order-coupling certificates

This module gives an assumption-carrying algebraic certificate for a supplied
joint jump-rate kernel.  Its generator grounding follows ACK-2010, Section 3.1,
equations (3.1)--(3.5), for generator grounding only.  Its order-support
requirement records the global goal `coupling/order-certificates`.

The certificate asserts only jump-rate, generator-marginal, and order-support
conditions.  It makes no existence, stochastic-process, pathwise-coupling, or
fluctuation claim.
-/

namespace ChemistryLib.Stochastic

/-- The supplied joint kernel has the supplied coordinate generators as
marginals and cannot jump from an ordered pair to an unordered pair. -/
def IsOrderCouplingCertificate {State : Type} [Fintype State] [Preorder State]
    (q₁ q₂ : RateKernel State) (Q : RateKernel (State × State)) : Prop :=
  IsJumpRateKernel q₁ ∧
    IsJumpRateKernel q₂ ∧
    IsJumpRateKernel Q ∧
    (∀ (f : State → ℝ) (x₁ x₂ : State),
      generator Q (fun z ↦ f z.1) (x₁, x₂) = generator q₁ f x₁) ∧
    (∀ (f : State → ℝ) (x₁ x₂ : State),
      generator Q (fun z ↦ f z.2) (x₁, x₂) = generator q₂ f x₂) ∧
    (∀ x₁ x₂ y₁ y₂,
      x₁ ≤ x₂ →
        ¬ y₁ ≤ y₂ →
          (x₁, x₂) ≠ (y₁, y₂) →
            Q (x₁, x₂) (y₁, y₂) = 0)

/-- The order-coupling certificate is exactly its algebraic generator and
order-support data. -/
theorem isOrderCouplingCertificate_iff_generator_marginals
    {State : Type} [Fintype State] [Preorder State]
    (q₁ q₂ : RateKernel State) (Q : RateKernel (State × State)) :
    IsOrderCouplingCertificate q₁ q₂ Q ↔
      IsJumpRateKernel q₁ ∧
        IsJumpRateKernel q₂ ∧
        IsJumpRateKernel Q ∧
        (∀ (f : State → ℝ) (x₁ x₂ : State),
          generator Q (fun z ↦ f z.1) (x₁, x₂) = generator q₁ f x₁) ∧
        (∀ (f : State → ℝ) (x₁ x₂ : State),
          generator Q (fun z ↦ f z.2) (x₁, x₂) = generator q₂ f x₂) ∧
        (∀ x₁ x₂ y₁ y₂,
          x₁ ≤ x₂ →
            ¬ y₁ ≤ y₂ →
              (x₁, x₂) ≠ (y₁, y₂) →
                Q (x₁, x₂) (y₁, y₂) = 0) :=
  Iff.rfl

end ChemistryLib.Stochastic
