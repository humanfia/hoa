/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QAlgBench.Init
public import QAlgBench.Base.Gate
public import QAlgBench.Base.Components.Kets

/-!
# Common oracle components

Reusable Core-level oracle components.  Oracles exposed from this file are
`Gate`s; raw `HilbertOperator` definitions appear only as implementation
operators or as genuinely non-unitary projectors/blocks in other modules.
-/

@[expose] public section

namespace QAlgBench

open PureState

noncomputable section

namespace Gate

variable {n : Nat}

/-! ### XOR oracles -/

/-- The basis involution underlying the XOR oracle:
`(x, b) ↦ (x, b ⊕ f x)`, with the bit flip written as `Fin.rev`. -/
def xorPerm (f : Fin (2 ^ n) -> Bool) :
    Equiv.Perm (Fin (2 ^ n) × Fin (2 ^ 1)) where
  toFun p := (p.1, if f p.1 then p.2.rev else p.2)
  invFun p := (p.1, if f p.1 then p.2.rev else p.2)
  left_inv p := by by_cases h : f p.1 <;> simp [h]
  right_inv p := by by_cases h : f p.1 <;> simp [h]

@[simp]
theorem xorPerm_apply (f : Fin (2 ^ n) -> Bool) (p : Fin (2 ^ n) × Fin (2 ^ 1)) :
    xorPerm f p = (p.1, if f p.1 then p.2.rev else p.2) :=
  rfl

/-- The XOR oracle is an involution. -/
@[simp]
theorem xorPerm_symm (f : Fin (2 ^ n) -> Bool) : (xorPerm f).symm = xorPerm f :=
  rfl

/-- The XOR (bit-flip) oracle of `f`, as a permutation Gate (Qubits on) `n + 1` qubits. -/
def xorOracle (f : Fin (2 ^ n) -> Bool) : Gate (Qubits (n + 1)) :=
  ofPerm (prodEquiv.permCongr (xorPerm f))

theorem xorOracle_mem_unitaryGroup (f : Fin (2 ^ n) -> Bool) :
    (xorOracle f : HilbertOperator (Qubits (n + 1)))
      ∈ Matrix.unitaryGroup (Fin (2 ^ (n + 1))) ℂ :=
  (xorOracle f).unitary

theorem xorOracle_apply (f : Fin (2 ^ n) -> Bool) (ψ : PureState (Qubits (n + 1)))
    (i : Fin (2 ^ (n + 1))) :
    (xorOracle f).apply ψ i = ψ (prodEquiv (xorPerm f (prodEquiv.symm i))) := by
  rw [xorOracle, ofPerm_apply, Equiv.permCongr_apply]

/-- Action on basis kets: `U_f |x⟩|b⟩ = |x⟩|b ⊕ f(x)⟩`. -/
theorem xorOracle_apply_ket (f : Fin (2 ^ n) -> Bool) (x : Fin (2 ^ n))
    (b : Fin (2 ^ 1)) :
    (xorOracle f).apply (ket (prodEquiv (x, b)))
      = ket (prodEquiv (x, if f x then b.rev else b)) := by
  rw [xorOracle, ofPerm_apply_ket]
  congr 1
  change prodEquiv ((xorPerm f).symm (prodEquiv.symm (prodEquiv (x, b))))
      = prodEquiv (x, if f x then b.rev else b)
  rw [Equiv.symm_apply_apply, xorPerm_symm, xorPerm_apply]

end Gate

variable {n : Nat}

/-! ### Phase oracles -/

/-- The concrete diagonal phase-oracle operator. -/
def phaseOracleOp {n : Nat} (marked : Fin (2 ^ n) -> Bool) : HilbertOperator (Qubits n) :=
  fun i j => if i = j then (if marked j then -1 else 1 : ℂ) else 0

theorem phaseOracle_mem_unitaryGroup {n : Nat} (marked : Fin (2 ^ n) -> Bool) :
    phaseOracleOp marked ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · subst j
    by_cases hm : marked i <;> simp [phaseOracleOp, hm]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [phaseOracleOp, hij, hji]

/-- The reusable phase oracle Gate (Qubits for) a marked-set predicate. -/
def phaseOracle {n : Nat} (marked : Fin (2 ^ n) -> Bool) : Gate (Qubits n) :=
  Gate.ofUnitary (phaseOracleOp marked) (phaseOracle_mem_unitaryGroup marked)

theorem phaseOracle_apply_ket {n : Nat} (marked : Fin (2 ^ n) -> Bool) (j : Fin (2 ^ n)) :
    (phaseOracle marked).applyVec (PureState.ket (R := Qubits n) j : StateVector (Qubits n)) =
      ((if marked j then -1 else 1 : ℂ) •
        (PureState.ket (R := Qubits n) j : StateVector (Qubits n))) := by
  by_cases hm : marked j
  · simp [hm]
    apply WithLp.ofLp_injective
    funext i
    rw [show ((phaseOracle marked).applyVec
            (PureState.ket (R := Qubits n) j : StateVector (Qubits n))).ofLp i =
          (phaseOracle marked).applyVec
            (PureState.ket (R := Qubits n) j : StateVector (Qubits n)) i from rfl,
      show ((-(PureState.ket (R := Qubits n) j : StateVector (Qubits n))).ofLp i) =
          (-(PureState.ket (R := Qubits n) j : StateVector (Qubits n))) i from rfl,
      Gate.applyVec, HilbertOperator.applyVec_ket]
    by_cases hij : i = j
    · subst i
      simp [phaseOracle, phaseOracleOp, hm, PureState.ket_apply]
    · simp [phaseOracle, phaseOracleOp, PureState.ket_apply, hij]
  · simp [hm]
    apply WithLp.ofLp_injective
    funext i
    rw [show ((phaseOracle marked).applyVec
            (PureState.ket (R := Qubits n) j : StateVector (Qubits n))).ofLp i =
          (phaseOracle marked).applyVec
            (PureState.ket (R := Qubits n) j : StateVector (Qubits n)) i from rfl,
      show ((PureState.ket (R := Qubits n) j : StateVector (Qubits n)).ofLp i) =
          (PureState.ket (R := Qubits n) j : StateVector (Qubits n)) i from rfl,
      Gate.applyVec, HilbertOperator.applyVec_ket]
    by_cases hij : i = j
    · subst i
      simp [phaseOracle, phaseOracleOp, hm, PureState.ket_apply]
    · simp [phaseOracle, phaseOracleOp, PureState.ket_apply, hij]

/-! ### XOR-oracle special states -/

/-- On a `|+>` target the XOR oracle acts trivially, whatever `f` is. -/
theorem xorOracle_apply_tensor_ketPlus (f : Fin (2 ^ n) -> Bool)
    (x : Fin (2 ^ n)) :
    (Gate.xorOracle f).apply ((ket x).tensor ketPlus)
      = (ket x).tensor ketPlus := by
  ext i
  rcases (prodEquiv (m := n) (n := 1)).surjective i with ⟨⟨y, b⟩, rfl⟩
  rw [Gate.xorOracle_apply, PureState.tensor_apply_prod, PureState.tensor_apply_prod]
  simp only [Equiv.symm_apply_apply, Gate.xorPerm_apply]
  by_cases hy : y = x
  · subst y
    by_cases h : f x <;> fin_cases b <;> simp [h, ketPlus_apply]
  · by_cases h : f y <;> fin_cases b <;>
      simp [h, hy, PureState.ket_apply]

end

end QAlgBench
