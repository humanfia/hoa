/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QAlgBench.Init
public import QAlgBench.Base.Tensor

/-!
# Computational-basis and terminal projective measurements

The computational-basis Born rule is register-polymorphic.  Qubit-specific
helpers, such as the marginal probability of the first qubit, are provided only
where the statement genuinely refers to qubits.
-/

@[expose] public section

namespace QAlgBench

/-- A terminal projective measurement over a finite register. -/
structure TerminalPVM (R : Register) (outcome : Type) [Fintype outcome] where
  /-- Projector for one terminal outcome. -/
  projector : outcome → HilbertOperator R
  /-- Projectors sum to the identity. -/
  complete : (∑ x, projector x) = (1 : HilbertOperator R)
  /-- Distinct projectors are orthogonal. -/
  orthogonal : ∀ x y, x ≠ y → projector x * projector y = 0
  /-- Each projector is idempotent. -/
  idempotent : ∀ x, projector x * projector x = projector x
  /-- Each projector is self-adjoint. -/
  selfAdjoint : ∀ x, (projector x).conjTranspose = projector x

namespace StateVector

noncomputable section

variable {R : Register}

/-- Born rule: probability of observing outcome `x` in the computational basis. -/
def probOutcome (psi : StateVector R) (x : R.Index) : ℝ :=
  ‖psi x‖ ^ 2

theorem probOutcome_nonneg (psi : StateVector R) (x : R.Index) :
    0 ≤ probOutcome psi x :=
  sq_nonneg _

/-- The Born-rule weights sum to the squared norm. -/
theorem sum_probOutcome (psi : StateVector R) :
    ∑ x, probOutcome psi x = ‖psi‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖psi i‖)]
  rfl

@[simp]
theorem probOutcome_ket (x y : R.Index) :
    probOutcome (PureState.ket x : StateVector R) y = if y = x then 1 else 0 := by
  rw [probOutcome, PureState.ket_apply]
  by_cases h : y = x
  · rw [if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h]
    simp

/-- Probability that measuring qubit 0 of a `1+n` qubit raw state yields `b`. -/
def probQubit0 {n : Nat} (psi : StateVector (Qubits (1 + n))) (b : Fin (2 ^ 1)) : ℝ :=
  ∑ y : Fin (2 ^ n), ‖psi (prodEquiv (b, y))‖ ^ 2

theorem probQubit0_nonneg {n : Nat} (psi : StateVector (Qubits (1 + n)))
    (b : Fin (2 ^ 1)) :
    0 ≤ probQubit0 psi b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Scaling a raw state vector scales the marginal probability by the squared
scalar norm. -/
theorem probQubit0_smul {n : Nat} (c : ℂ) (psi : StateVector (Qubits (1 + n)))
    (b : Fin (2 ^ 1)) :
    probQubit0 (c • psi) b = ‖c‖ ^ 2 * probQubit0 psi b := by
  rw [probQubit0, probQubit0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PiLp.smul_apply, smul_eq_mul, norm_mul, mul_pow]

/-- Born-rule probability for an arbitrary terminal PVM. -/
def probPVM {outcome : Type} [Fintype outcome]
    (psi : StateVector R) (pvm : TerminalPVM R outcome) (x : outcome) : ℝ :=
  ‖HilbertOperator.applyVec (pvm.projector x) psi‖ ^ 2

theorem probPVM_nonneg {outcome : Type} [Fintype outcome]
    (psi : StateVector R) (pvm : TerminalPVM R outcome) (x : outcome) :
    0 ≤ probPVM psi pvm x :=
  sq_nonneg _

end

end StateVector

namespace PureState

noncomputable section

variable {R : Register}

/-- Born-rule probability for a pure state. -/
def probOutcome (psi : PureState R) (x : R.Index) : ℝ :=
  StateVector.probOutcome (psi : StateVector R) x

theorem probOutcome_nonneg (psi : PureState R) (x : R.Index) :
    0 ≤ probOutcome psi x :=
  StateVector.probOutcome_nonneg (psi : StateVector R) x

/-- Pure-state outcome probabilities form a probability distribution. -/
theorem sum_probOutcome (psi : PureState R) :
    ∑ x, probOutcome psi x = 1 := by
  change ∑ x, StateVector.probOutcome (psi : StateVector R) x = 1
  rw [StateVector.sum_probOutcome, psi.norm_eq_one, one_pow]

/-- Compatibility name for the pure-state probability distribution theorem. -/
theorem sum_probOutcome_eq_one (psi : PureState R) :
    ∑ x, probOutcome psi x = 1 :=
  sum_probOutcome psi

@[simp]
theorem probOutcome_ket (x y : R.Index) :
    probOutcome (ket x) y = if y = x then 1 else 0 :=
  StateVector.probOutcome_ket x y

/-- Expectation value `<psi|O|psi>` of an observable `O`, represented as a real
number via the real part. -/
def expVal (psi : PureState R) (O : HilbertOperator R) : ℝ :=
  (inner ℂ (psi : StateVector R) (HilbertOperator.applyVec O (psi : StateVector R))).re

/-- Probability that measuring qubit 0 of a `1+n` qubit pure state yields `b`. -/
def probQubit0 {n : Nat} (psi : PureState (Qubits (1 + n))) (b : Fin (2 ^ 1)) : ℝ :=
  StateVector.probQubit0 (psi : StateVector (Qubits (1 + n))) b

theorem probQubit0_nonneg {n : Nat} (psi : PureState (Qubits (1 + n)))
    (b : Fin (2 ^ 1)) :
    0 ≤ probQubit0 psi b :=
  StateVector.probQubit0_nonneg (psi : StateVector (Qubits (1 + n))) b

/-- Compatibility name for raw-vector marginal scaling. -/
theorem probQubit0_smul {n : Nat} (c : ℂ) (psi : StateVector (Qubits (1 + n)))
    (b : Fin (2 ^ 1)) :
    StateVector.probQubit0 (c • psi) b
      = ‖c‖ ^ 2 * StateVector.probQubit0 psi b :=
  StateVector.probQubit0_smul c psi b

/-- Born-rule probability for an arbitrary terminal PVM. -/
def probPVM {outcome : Type} [Fintype outcome]
    (psi : PureState R) (pvm : TerminalPVM R outcome) (x : outcome) : ℝ :=
  StateVector.probPVM (psi : StateVector R) pvm x

theorem probPVM_nonneg {outcome : Type} [Fintype outcome]
    (psi : PureState R) (pvm : TerminalPVM R outcome) (x : outcome) :
    0 ≤ probPVM psi pvm x :=
  StateVector.probPVM_nonneg (psi : StateVector R) pvm x

end

end PureState

end QAlgBench

