import QAlgBench.Base

/-!
# Post-measurement state after observing the first qubit

The natural-number parameter `m` is the number of unmeasured qubits, so the
full register has `1 + m` qubits.  The vectors `α₀` and `α₁` contain the
computational-basis amplitudes whose first qubit is respectively `0` and `1`.
-/

open scoped BigOperators

namespace QAlgFormalized

open QAlgBench

noncomputable section

/-- For a normalized state
`|0⟩ ⊗ α₀ + |1⟩ ⊗ α₁`, measuring the first qubit in the computational basis
gives outcome `1` with weight `∑ y, ‖α₁ y‖²`.  If that weight is positive, the
displayed rescaling of the outcome-`1` branch is a normalized pure state of the
entire register. -/
theorem postMeasurementStateObservedQubit
    {m : ℕ}
    (α₀ α₁ : StateVector (Qubits m))
    (ψ : PureState (Qubits (1 + m)))
    (hψ :
      (ψ : StateVector (Qubits (1 + m))) =
        StateVector.tensor
            (PureState.ket0 : StateVector (Qubits 1)) α₀
          + StateVector.tensor
            (PureState.ket1 : StateVector (Qubits 1)) α₁) :
    PureState.probQubit0 ψ 1 =
        ∑ y : Fin (2 ^ m), ‖α₁ y‖ ^ 2
      ∧
        ((0 < ∑ y : Fin (2 ^ m), ‖α₁ y‖ ^ 2) →
          ∃ ψ' : PureState (Qubits (1 + m)),
            (ψ' : StateVector (Qubits (1 + m))) =
              ((Real.sqrt (∑ y : Fin (2 ^ m), ‖α₁ y‖ ^ 2) : ℂ)⁻¹) •
                StateVector.tensor
                  (PureState.ket1 : StateVector (Qubits 1)) α₁) := by
  have hsum :
      ∑ y : Fin (2 ^ m), ‖α₁ y‖ ^ 2 = ‖α₁‖ ^ 2 := by
    simpa [StateVector.probOutcome] using
      (StateVector.sum_probOutcome α₁)
  constructor
  · change
      StateVector.probQubit0
          (ψ : StateVector (Qubits (1 + m))) 1 =
        ∑ y : Fin (2 ^ m), ‖α₁ y‖ ^ 2
    rw [hψ, PureState.probQubit1_ket0_tensor_add_ket1_tensor, hsum]
  · intro hpos
    have hsqrt_pos :
        0 < Real.sqrt (∑ y : Fin (2 ^ m), ‖α₁ y‖ ^ 2) :=
      Real.sqrt_pos.2 hpos
    have hnorm_α₁ :
        ‖α₁‖ = Real.sqrt (∑ y : Fin (2 ^ m), ‖α₁ y‖ ^ 2) := by
      rw [hsum, Real.sqrt_sq (norm_nonneg α₁)]
    have hnorm :
        ‖((Real.sqrt (∑ y : Fin (2 ^ m), ‖α₁ y‖ ^ 2) : ℂ)⁻¹) •
            StateVector.tensor
              (PureState.ket1 : StateVector (Qubits 1)) α₁‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _),
        StateVector.norm_tensor, PureState.norm_eq_one', one_mul, hnorm_α₁,
        inv_mul_cancel₀ hsqrt_pos.ne']
    exact ⟨PureState.ofVec _ hnorm, rfl⟩

end

end QAlgFormalized
