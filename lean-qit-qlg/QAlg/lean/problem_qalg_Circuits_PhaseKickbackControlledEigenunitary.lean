import QAlgBench.Base

/-!
# Phase kickback for a controlled eigenunitary

The target register is an arbitrary finite register.  The generic product
constructions below are needed because the tensor operations in `QAlgBench.Base`
are specialized to registers of the form `Qubits n`.
-/

namespace QAlgFormalized.PhaseKickbackControlledEigenunitary

open QAlgBench

noncomputable section

/-- Tensor product of raw state vectors on arbitrary finite registers. -/
def stateTensor {C T : Register} (φ : StateVector C) (ψ : StateVector T) :
    StateVector (Register.prod C T) :=
  WithLp.toLp 2 fun i => φ i.1 * ψ i.2

/-- Kronecker product of Hilbert operators on arbitrary finite registers. -/
def operatorTensor {C T : Register} (A : HilbertOperator C) (B : HilbertOperator T) :
    HilbertOperator (Register.prod C T) :=
  fun i j => A i.1 j.1 * B i.2 j.2

/-- The initialized control vector `α |0⟩ + β |1⟩`. -/
def controlVector (α β : ℂ) : StateVector (Qubits 1) :=
  α • (PureState.ket0 : StateVector (Qubits 1)) +
    β • (PureState.ket1 : StateVector (Qubits 1))

/-- The control vector after receiving the eigenphase on its `|1⟩` branch. -/
def phaseKickedControlVector (α β : ℂ) (θ : ℝ) : StateVector (Qubits 1) :=
  α • (PureState.ket0 : StateVector (Qubits 1)) +
    (β * Complex.exp ((θ : ℂ) * Complex.I)) •
      (PureState.ket1 : StateVector (Qubits 1))

/-- The controlled operator
`|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` for an arbitrary finite target register. -/
def controlledOperator {T : Register} (U : Gate T) :
    HilbertOperator (Register.prod (Qubits 1) T) :=
  operatorTensor Gate.proj0 (1 : HilbertOperator T) +
    operatorTensor Gate.proj1 (U : HilbertOperator T)

/-- A raw bipartite vector is separable when it is the tensor product of two
normalized pure states. -/
def IsSeparable {C T : Register} (v : StateVector (Register.prod C T)) : Prop :=
  ∃ φ : PureState C, ∃ ψ : PureState T,
    v = stateTensor (φ : StateVector C) (ψ : StateVector T)

/-- The phase-kickback identity for a normalized eigenvector of a unitary. -/
theorem phaseKickback_identity
    {T : Register}
    (U : Gate T)
    (ψ : PureState T)
    (θ : ℝ)
    (hθ : θ ∈ Set.Ico 0 (2 * Real.pi))
    (α β : ℂ)
    (hcontrol : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1)
    (heigen :
      U.applyVec (ψ : StateVector T) =
        Complex.exp ((θ : ℂ) * Complex.I) • (ψ : StateVector T)) :
    HilbertOperator.applyVec (controlledOperator U)
        (stateTensor (controlVector α β) (ψ : StateVector T))
      =
    stateTensor (phaseKickedControlVector α β θ) (ψ : StateVector T) := by
  classical
  have tensor_action {C T : Register} (A : HilbertOperator C) (B : HilbertOperator T)
      (φ : StateVector C) (χ : StateVector T) :
      HilbertOperator.applyVec (operatorTensor A B) (stateTensor φ χ) =
        stateTensor (HilbertOperator.applyVec A φ) (HilbertOperator.applyVec B χ) := by
    apply WithLp.ofLp_injective
    funext i
    rcases i with ⟨iC, iT⟩
    change (∑ x : C.Index × T.Index,
        (A iC x.1 * B iT x.2) * (φ x.1 * χ x.2)) =
      (∑ x : C.Index, A iC x * φ x) *
        ∑ x : T.Index, B iT x * χ x
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    simp only [mul_assoc, mul_left_comm]
  rw [controlledOperator, HilbertOperator.add_applyVec,
    tensor_action, tensor_action]
  have heigen' :
      HilbertOperator.applyVec (U : HilbertOperator T) (ψ : StateVector T) =
        Complex.exp ((θ : ℂ) * Complex.I) • (ψ : StateVector T) := heigen
  rw [HilbertOperator.one_applyVec, heigen']
  apply WithLp.ofLp_injective
  funext i
  rcases i with ⟨iC, iT⟩
  change (stateTensor
        (HilbertOperator.applyVec Gate.proj0 (controlVector α β)) (ψ : StateVector T) +
      stateTensor (HilbertOperator.applyVec Gate.proj1 (controlVector α β))
        (Complex.exp ((θ : ℂ) * Complex.I) • (ψ : StateVector T))) (iC, iT) =
    stateTensor (phaseKickedControlVector α β θ) (ψ : StateVector T) (iC, iT)
  simp [stateTensor, controlVector, phaseKickedControlVector]
  ring

/-- In particular, the output of phase kickback remains a separable pure
state across the control/target cut. -/
theorem phaseKickback_output_isSeparable
    {T : Register}
    (U : Gate T)
    (ψ : PureState T)
    (θ : ℝ)
    (hθ : θ ∈ Set.Ico 0 (2 * Real.pi))
    (α β : ℂ)
    (hcontrol : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1)
    (heigen :
      U.applyVec (ψ : StateVector T) =
        Complex.exp ((θ : ℂ) * Complex.I) • (ψ : StateVector T)) :
    IsSeparable
      (HilbertOperator.applyVec (controlledOperator U)
        (stateTensor (controlVector α β) (ψ : StateVector T))) := by
  have hphase_norm : ‖phaseKickedControlVector α β θ‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    change Real.sqrt (∑ i : Fin 2, ‖phaseKickedControlVector α β θ i‖ ^ 2) = 1
    rw [Fin.sum_univ_two]
    simp [phaseKickedControlVector, PureState.ket0, PureState.ket1,
      Complex.norm_exp_ofReal_mul_I, hcontrol]
  refine ⟨PureState.ofVec (phaseKickedControlVector α β θ) hphase_norm, ψ, ?_⟩
  apply phaseKickback_identity <;> assumption

/-- The output has a normalized control factor whose `|0⟩` amplitude remains
`α` and whose `|1⟩` amplitude is multiplied by the eigenvalue
`exp(i θ)`.  This states the transfer of the eigenphase to the relative phase
of the control register without requiring either amplitude to be nonzero. -/
theorem phaseKickback_phase_transferred_to_control
    {T : Register}
    (U : Gate T)
    (ψ : PureState T)
    (θ : ℝ)
    (hθ : θ ∈ Set.Ico 0 (2 * Real.pi))
    (α β : ℂ)
    (hcontrol : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1)
    (heigen :
      U.applyVec (ψ : StateVector T) =
        Complex.exp ((θ : ℂ) * Complex.I) • (ψ : StateVector T)) :
    ∃ φout : PureState (Qubits 1),
      HilbertOperator.applyVec (controlledOperator U)
          (stateTensor (controlVector α β) (ψ : StateVector T))
        =
          stateTensor (φout : StateVector (Qubits 1)) (ψ : StateVector T) ∧
      φout 0 = α ∧
      φout 1 = β * Complex.exp ((θ : ℂ) * Complex.I) := by
  have hphase_norm : ‖phaseKickedControlVector α β θ‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    change Real.sqrt (∑ i : Fin 2, ‖phaseKickedControlVector α β θ i‖ ^ 2) = 1
    rw [Fin.sum_univ_two]
    simp [phaseKickedControlVector, PureState.ket0, PureState.ket1,
      Complex.norm_exp_ofReal_mul_I, hcontrol]
  refine ⟨PureState.ofVec (phaseKickedControlVector α β θ) hphase_norm, ?_, ?_, ?_⟩
  · apply phaseKickback_identity <;> assumption
  · simp [phaseKickedControlVector, PureState.ket0, PureState.ket1]
  · simp [phaseKickedControlVector, PureState.ket0, PureState.ket1]

end

end QAlgFormalized.PhaseKickbackControlledEigenunitary
