import QAlgBench.Base

/-!
# Spectral projectors of a Boolean phase oracle

For a Boolean predicate `f` on the computational basis of an `n`-qubit
register, this file states the exact spectral projectors of its phase oracle
and the resulting trace formula.
-/

namespace QAlgFormalized

open QAlgBench

noncomputable section

/-- The operator `(I + O_f) / 2`, proposed as the projector onto the
`+1`-eigenspace of the Boolean phase oracle. -/
def phaseOraclePositiveProjectorOp {n : ℕ} (f : Fin (2 ^ n) → Bool) :
    HilbertOperator (Qubits n) :=
  (2 : ℂ)⁻¹ • ((1 : HilbertOperator (Qubits n)) + phaseOracleOp f)

/-- The operator `(I - O_f) / 2`, proposed as the projector onto the
`-1`-eigenspace of the Boolean phase oracle. -/
def phaseOracleNegativeProjectorOp {n : ℕ} (f : Fin (2 ^ n) → Bool) :
    HilbertOperator (Qubits n) :=
  (2 : ℂ)⁻¹ • ((1 : HilbertOperator (Qubits n)) - phaseOracleOp f)

/-- The operators `(I + O_f) / 2` and `(I - O_f) / 2` are orthogonal
projectors whose fixed-vector spaces are exactly the `+1`- and
`-1`-eigenspaces of `O_f`, respectively. -/
theorem phaseOracle_spectralProjectors {n : ℕ} (f : Fin (2 ^ n) → Bool) :
    ∃ positive negative : OrthogonalProjector n,
      positive.op = phaseOraclePositiveProjectorOp f ∧
      negative.op = phaseOracleNegativeProjectorOp f ∧
      (∀ ψ : StateVector (Qubits n),
        (HilbertOperator.applyVec (phaseOracleOp f) ψ = ψ ↔
          HilbertOperator.applyVec positive.op ψ = ψ)) ∧
      (∀ ψ : StateVector (Qubits n),
        (HilbertOperator.applyVec (phaseOracleOp f) ψ = -ψ ↔
          HilbertOperator.applyVec negative.op ψ = ψ)) := by
  have horacle : phaseOracleOp f =
      Matrix.diagonal (fun i => if f i then (-1 : ℂ) else 1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [phaseOracleOp]
    · simp [phaseOracleOp, hij]
  have hpos : phaseOraclePositiveProjectorOp f =
      Matrix.diagonal (fun i => if f i then (0 : ℂ) else 1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hf : f i <;>
        simp [phaseOraclePositiveProjectorOp, phaseOracleOp, hf]
      ring
    · simp [phaseOraclePositiveProjectorOp, phaseOracleOp, hij]
  have hneg : phaseOracleNegativeProjectorOp f =
      Matrix.diagonal (fun i => if f i then (1 : ℂ) else 0) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hf : f i <;>
        simp [phaseOracleNegativeProjectorOp, phaseOracleOp, hf]
      ring
    · simp [phaseOracleNegativeProjectorOp, phaseOracleOp, hij]
  have horacleApply (ψ : StateVector (Qubits n)) (i : Fin (2 ^ n)) :
      HilbertOperator.applyVec (phaseOracleOp f) ψ i =
        if f i then -ψ i else ψ i := by
    rw [horacle]
    change Matrix.mulVec
      (Matrix.diagonal (fun i => if f i then (-1 : ℂ) else 1)) ψ.ofLp i = _
    rw [Matrix.mulVec_diagonal]
    by_cases hf : f i <;> simp [hf]
  have hposApply (ψ : StateVector (Qubits n)) (i : Fin (2 ^ n)) :
      HilbertOperator.applyVec (phaseOraclePositiveProjectorOp f) ψ i =
        if f i then 0 else ψ i := by
    rw [hpos]
    change Matrix.mulVec
      (Matrix.diagonal (fun i => if f i then (0 : ℂ) else 1)) ψ.ofLp i = _
    rw [Matrix.mulVec_diagonal]
    by_cases hf : f i <;> simp [hf]
  have hnegApply (ψ : StateVector (Qubits n)) (i : Fin (2 ^ n)) :
      HilbertOperator.applyVec (phaseOracleNegativeProjectorOp f) ψ i =
        if f i then ψ i else 0 := by
    rw [hneg]
    change Matrix.mulVec
      (Matrix.diagonal (fun i => if f i then (1 : ℂ) else 0)) ψ.ofLp i = _
    rw [Matrix.mulVec_diagonal]
    by_cases hf : f i <;> simp [hf]
  let positive : OrthogonalProjector n :=
    { op := phaseOraclePositiveProjectorOp f
      selfAdjoint := by
        rw [hpos]
        ext i j
        by_cases hij : i = j
        · subst j
          by_cases hf : f i <;> simp [Matrix.conjTranspose_apply, hf]
        · have hji : j ≠ i := fun h => hij h.symm
          simp [Matrix.conjTranspose_apply, hij, hji]
      idempotent := by
        rw [hpos, Matrix.diagonal_mul_diagonal]
        ext i j
        by_cases hij : i = j
        · subst j
          by_cases hf : f i <;> simp [hf]
        · simp [hij] }
  let negative : OrthogonalProjector n :=
    { op := phaseOracleNegativeProjectorOp f
      selfAdjoint := by
        rw [hneg]
        ext i j
        by_cases hij : i = j
        · subst j
          by_cases hf : f i <;> simp [Matrix.conjTranspose_apply, hf]
        · have hji : j ≠ i := fun h => hij h.symm
          simp [Matrix.conjTranspose_apply, hij, hji]
      idempotent := by
        rw [hneg, Matrix.diagonal_mul_diagonal]
        ext i j
        by_cases hij : i = j
        · subst j
          by_cases hf : f i <;> simp [hf]
        · simp [hij] }
  refine ⟨positive, negative, rfl, rfl, ?_, ?_⟩
  · intro ψ
    constructor
    · intro h
      ext i
      rw [hposApply]
      have hi := congrArg (fun φ : StateVector (Qubits n) => φ i) h
      rw [horacleApply] at hi
      by_cases hf : f i
      · simpa [hf] using (neg_eq_self.mp (by simpa [hf] using hi)).symm
      · simp [hf]
    · intro h
      ext i
      rw [horacleApply]
      have hi := congrArg (fun φ : StateVector (Qubits n) => φ i) h
      change HilbertOperator.applyVec (phaseOraclePositiveProjectorOp f) ψ i = ψ i at hi
      rw [hposApply] at hi
      by_cases hf : f i
      · have hz : ψ i = 0 := by simpa [hf] using hi.symm
        simp [hf, hz]
      · simp [hf]
  · intro ψ
    constructor
    · intro h
      ext i
      rw [hnegApply]
      have hi := congrArg (fun φ : StateVector (Qubits n) => φ i) h
      rw [horacleApply] at hi
      by_cases hf : f i
      · simp [hf]
      · have hz : ψ i = 0 := neg_eq_self.mp (by simpa [hf] using hi.symm)
        simp [hf, hz]
    · intro h
      ext i
      rw [horacleApply]
      have hi := congrArg (fun φ : StateVector (Qubits n) => φ i) h
      change HilbertOperator.applyVec (phaseOracleNegativeProjectorOp f) ψ i = ψ i at hi
      rw [hnegApply] at hi
      by_cases hf : f i
      · simp [hf]
      · have hz : ψ i = 0 := by simpa [hf] using hi.symm
        simp [hf, hz]

/-- The trace of a Boolean phase oracle is the number of unmarked inputs minus
the number of marked inputs, namely `2^n - 2 |f⁻¹(1)|`. -/
theorem phaseOracle_trace {n : ℕ} (f : Fin (2 ^ n) → Bool) :
    Matrix.trace (phaseOracleOp f) =
      (2 ^ n : ℂ) -
        2 * ((Finset.univ.filter (fun x => f x)).card : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, phaseOracleOp, if_pos]
  have hmarked :
      (∑ x : Fin (2 ^ n), (if f x then (1 : ℂ) else 0)) =
        ((Finset.univ.filter (fun x => f x)).card : ℂ) := by
    rw [← Finset.sum_filter]
    simp
  calc
    (∑ x, (if f x then -1 else 1 : ℂ)) =
        ∑ x, (1 - 2 * (if f x then 1 else 0) : ℂ) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hf : f x
      · simp [hf]
        ring
      · simp [hf]
    _ = (∑ _x : Fin (2 ^ n), (1 : ℂ)) -
          2 * ∑ x, (if f x then (1 : ℂ) else 0) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (2 ^ n : ℂ) -
          2 * ((Finset.univ.filter (fun x => f x)).card : ℂ) := by
      rw [hmarked]
      simp

end

end QAlgFormalized
