import QAlgBench.Base
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Local marginal after an unread projective measurement

This file models two distinguished one-qubit subsystems.  The `prodEquiv`
indexing from `QAlgBench.Base` identifies their tensor-product computational
basis with the basis of `Qubits (1 + 1)`.
-/

namespace QAlgFormalized.LocalMarginalUnreadProjectiveMeasurement

open scoped ComplexOrder Matrix
open QAlgBench

noncomputable section

/-- Operators on either one-qubit subsystem. -/
abbrev QubitOperator := HilbertOperator (Qubits 1)

/-- Operators on the bipartite system
`ℂ² ⊗ ℂ²`, indexed using the Base library's tensor-product equivalence. -/
abbrev BipartiteQubitOperator := HilbertOperator (Qubits (1 + 1))

/-- A finite-dimensional density operator is positive semidefinite and has
unit trace.  Positive semidefiniteness includes Hermiticity in Mathlib's
definition. -/
def IsDensityOperator (ρ : BipartiteQubitOperator) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

/-- The computational-basis rank-one operator `|b⟩⟨b'|`. -/
def computationalKetBra (b b' : Fin 2) : QubitOperator :=
  Matrix.single b b' 1

/-- The joint projector `I_A ⊗ |b⟩⟨b|_B`. -/
def projectorB (b : Fin 2) : BipartiteQubitOperator :=
  HilbertOperator.tensor (1 : QubitOperator) (computationalKetBra b b)

/-- The state after the computational-basis projective measurement on `B`
when its outcome is discarded:
`ρ ↦ ∑ b, (I_A ⊗ |b⟩⟨b|) ρ (I_A ⊗ |b⟩⟨b|)`. -/
def unreadMeasurementB (ρ : BipartiteQubitOperator) :
    BipartiteQubitOperator :=
  ∑ b : Fin 2, projectorB b * ρ * projectorB b

/-- The `A`-operator `ρ⁽ᴬ⁾_{bb'}` occurring as the `(b,b')` block of a
bipartite operator `ρ` in the computational basis of `B`. -/
def blockA (ρ : BipartiteQubitOperator) (b b' : Fin 2) :
    QubitOperator :=
  fun a a' =>
    ρ (prodEquiv (m := 1) (n := 1) (a, b))
      (prodEquiv (m := 1) (n := 1) (a', b'))

/-- Partial trace over `B`, expressed in the product computational basis. -/
def partialTraceB (ρ : BipartiteQubitOperator) : QubitOperator :=
  fun a a' =>
    ∑ b : Fin 2,
      ρ (prodEquiv (m := 1) (n := 1) (a, b))
        (prodEquiv (m := 1) (n := 1) (a', b))

/-- Every bipartite operator is the sum of its `B`-indexed operator blocks. -/
theorem block_decomposition (ρ : BipartiteQubitOperator) :
    ρ =
      ∑ b : Fin 2, ∑ b' : Fin 2,
        HilbertOperator.tensor (blockA ρ b b') (computationalKetBra b b') := by
  classical
  ext i j
  rw [← (prodEquiv (m := 1) (n := 1)).apply_symm_apply i,
    ← (prodEquiv (m := 1) (n := 1)).apply_symm_apply j]
  rcases (prodEquiv (m := 1) (n := 1)).symm i with ⟨a, b⟩
  rcases (prodEquiv (m := 1) (n := 1)).symm j with ⟨a', b'⟩
  fin_cases b <;> fin_cases b' <;>
    simp [blockA, computationalKetBra, Matrix.single]

/-- Discarding the outcome of the computational-basis measurement on `B`
removes precisely the off-diagonal `B` blocks. -/
theorem unreadMeasurementB_eq_diagonal_blocks
    (ρ : BipartiteQubitOperator) (hρ : IsDensityOperator ρ) :
    unreadMeasurementB ρ =
      HilbertOperator.tensor (blockA ρ 0 0) (computationalKetBra 0 0)
        + HilbertOperator.tensor (blockA ρ 1 1) (computationalKetBra 1 1) := by
  classical
  unfold unreadMeasurementB
  conv_lhs =>
    enter [2, b]
    rw [block_decomposition ρ]
  simp only [Fin.sum_univ_two, projectorB, mul_add, add_mul,
    HilbertOperator.tensor_mul_tensor]
  repeat' first | rw [HilbertOperator.tensor_mul_tensor]
  simp [computationalKetBra, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne]

/-- A local non-selective projective measurement on `B` does not change the
reduced density operator of subsystem `A`. -/
theorem partialTraceB_unreadMeasurementB
    (ρ : BipartiteQubitOperator) (hρ : IsDensityOperator ρ) :
    partialTraceB (unreadMeasurementB ρ) = partialTraceB ρ := by
  rw [unreadMeasurementB_eq_diagonal_blocks ρ hρ]
  ext a a'
  simp [partialTraceB, blockA, computationalKetBra, Fin.sum_univ_two]

end

end QAlgFormalized.LocalMarginalUnreadProjectiveMeasurement
