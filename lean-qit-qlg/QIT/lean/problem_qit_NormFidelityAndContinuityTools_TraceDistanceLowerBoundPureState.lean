import QITBench.Base.OneShot
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Trace-distance lower bound for a pure state

This file formalizes the pure-state specialization of the lower
Fuchs--van de Graaf bound.  A `QITBench.PureVector` supplies the normalized
vector `ψ`, its associated state is `ψ.state = |ψ⟩⟨ψ|`, and an arbitrary
`QITBench.State` supplies the density operator `σ`.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace QITFormalized.TraceDistanceLowerBoundPureState

open QITBench

noncomputable section

universe u

variable {d : Type u} [Fintype d] [DecidableEq d]

private theorem re_trace_mul_nonneg_of_posSemidef
    {A B : Matrix d d ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have hXB : (X * B * X.conjTranspose).PosSemidef :=
    hB.mul_mul_conjTranspose_same X
  have htr : 0 ≤ (X * B * X.conjTranspose).trace := hXB.trace_nonneg
  have hre : 0 ≤ (X * B * star X).trace.re := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Complex.nonneg_iff.mp htr).1
  rw [hX]
  calc
    (star X * X * B).trace.re = (X * B * star X).trace.re := by
      rw [Matrix.trace_mul_cycle X B (star X)]
    _ ≥ 0 := hre

private theorem re_trace_mul_le_posPart
    (A E : Matrix d d ℂ) (hA : A.IsHermitian)
    (hEpos : E.PosSemidef) (hEle : E ≤ 1) :
    (A * E).trace.re ≤ (A⁺).trace.re := by
  have hPpos : (A⁺).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A)
  have hQpos : (A⁻).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A)
  have hQE : 0 ≤ (A⁻ * E).trace.re :=
    re_trace_mul_nonneg_of_posSemidef hQpos hEpos
  have hcomp : (1 - E).PosSemidef := Matrix.le_iff.mp hEle
  have hcompP : 0 ≤ ((1 - E) * A⁺).trace.re :=
    re_trace_mul_nonneg_of_posSemidef hcomp hPpos
  have hPEle : (A⁺ * E).trace.re ≤ (A⁺).trace.re := by
    have hrewrite : ((1 - E) * A⁺).trace.re =
        (A⁺).trace.re - (A⁺ * E).trace.re := by
      rw [sub_mul, Matrix.one_mul, Matrix.trace_sub,
        Matrix.trace_mul_comm E A⁺]
      rfl
    rw [hrewrite] at hcompP
    linarith
  calc
    (A * E).trace.re = ((A⁺ - A⁻) * E).trace.re := by
      rw [CFC.posPart_sub_negPart A hA]
    _ = (A⁺ * E).trace.re - (A⁻ * E).trace.re := by
      rw [sub_mul, Matrix.trace_sub]
      rfl
    _ ≤ (A⁺).trace.re := by linarith

private theorem traceNorm_eq_two_re_trace_posPart_of_trace_zero
    (A : Matrix d d ℂ) (hA : A.IsHermitian) (htr : A.trace = 0) :
    OneShot.traceNorm A = 2 * (A⁺).trace.re := by
  have hparts : (A⁺).trace = (A⁻).trace := by
    have h := congrArg Matrix.trace (CFC.posPart_sub_negPart A hA)
    rw [Matrix.trace_sub, htr] at h
    exact sub_eq_zero.mp h
  rw [OneShot.traceNorm, OneShot.matrixSqrt]
  change (CFC.abs A).trace.re = _
  rw [← CFC.posPart_add_negPart A hA, Matrix.trace_add, hparts]
  simp only [Complex.add_re]
  ring

private theorem trace_pureState_mul
    (ψ : PureVector d) (M : Matrix d d ℂ) :
    (ψ.state.matrix * M).trace =
      (fun i => star (ψ.amp i)) ⬝ᵥ Matrix.mulVec M ψ.amp := by
  simp only [PureVector.state_matrix, rankOneMatrix_apply, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, dotProduct, Matrix.mulVec]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The trace distance `D(ρ, σ) = (1 / 2) ‖ρ - σ‖₁` between density
operators, using the finite-dimensional trace norm from `QITBench.Base.OneShot`. -/
def traceDistance
    {d : Type u} [Fintype d] [DecidableEq d]
    (ρ σ : State d) : ℝ :=
  (1 / 2 : ℝ) * OneShot.traceNorm (ρ.matrix - σ.matrix)

/-- The source's pure-state fidelity
`F(|ψ⟩, σ) = sqrt (⟨ψ|σ|ψ⟩)`.

The expectation of a positive semidefinite matrix is real; `Complex.re`
extracts that real value in the ambient complex-matrix representation. -/
def pureStateFidelity
    {d : Type u} [Fintype d] [DecidableEq d]
    (ψ : PureVector d) (σ : State d) : ℝ :=
  Real.sqrt
    (Complex.re
      ((fun i => star (ψ.amp i)) ⬝ᵥ Matrix.mulVec σ.matrix ψ.amp))

/-- For a normalized pure state `|ψ⟩⟨ψ|` and an arbitrary density operator
`σ`, one minus the squared pure-state fidelity is at most their trace
distance. -/
theorem one_sub_pureStateFidelity_sq_le_traceDistance
    {d : Type u} [Fintype d] [DecidableEq d]
    (ψ : PureVector d) (σ : State d) :
    1 - pureStateFidelity ψ σ ^ 2 ≤ traceDistance ψ.state σ := by
  let P : Matrix d d ℂ := ψ.state.matrix
  let A : Matrix d d ℂ := P - σ.matrix
  let q : ℝ :=
    Complex.re
      ((fun i => star (ψ.amp i)) ⬝ᵥ Matrix.mulVec σ.matrix ψ.amp)
  have hq : 0 ≤ q := by
    have h := σ.pos.dotProduct_mulVec_nonneg ψ.amp
    exact (Complex.nonneg_iff.mp (by simpa [q] using h)).1
  have hfid : pureStateFidelity ψ σ ^ 2 = q := by
    simpa [pureStateFidelity, q] using Real.sq_sqrt hq
  have hAherm : A.IsHermitian := by
    exact ψ.state.pos.isHermitian.sub σ.pos.isHermitian
  have hPtr : P.trace = 1 := ψ.state.trace_eq_one
  have hAtr : A.trace = 0 := by
    simp only [A, Matrix.trace_sub, hPtr, σ.trace_eq_one, sub_self]
  have hPid : P * P = P := by
    simpa [P] using ψ.state_matrix_mul_self
  have hPle : P ≤ 1 := by
    rw [Matrix.le_iff]
    exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent
      P ψ.state.pos hPid
  have htest : (A * P).trace.re ≤ (A⁺).trace.re :=
    re_trace_mul_le_posPart A P hAherm ψ.state.pos hPle
  have htracePM :
      (P * σ.matrix).trace =
        (fun i => star (ψ.amp i)) ⬝ᵥ Matrix.mulVec σ.matrix ψ.amp := by
    simpa [P] using trace_pureState_mul ψ σ.matrix
  have htestValue : (A * P).trace.re = 1 - q := by
    calc
      (A * P).trace.re =
          ((P * P) - σ.matrix * P).trace.re := by
            change ((P - σ.matrix) * P).trace.re =
              ((P * P) - σ.matrix * P).trace.re
            rw [sub_mul]
      _ = (P - σ.matrix * P).trace.re := by rw [hPid]
      _ = (P.trace - (σ.matrix * P).trace).re := by
            rw [Matrix.trace_sub]
      _ = ((1 : ℂ) - (P * σ.matrix).trace).re := by
            rw [hPtr, Matrix.trace_mul_comm σ.matrix P]
      _ = 1 - q := by rw [htracePM]; rfl
  have hnorm :
      OneShot.traceNorm A = 2 * (A⁺).trace.re :=
    traceNorm_eq_two_re_trace_posPart_of_trace_zero A hAherm hAtr
  calc
    1 - pureStateFidelity ψ σ ^ 2 = 1 - q := by rw [hfid]
    _ ≤ (A⁺).trace.re := by rw [← htestValue]; exact htest
    _ = (1 / 2 : ℝ) * OneShot.traceNorm A := by rw [hnorm]; ring
    _ = traceDistance ψ.state σ := by rfl

end

end QITFormalized.TraceDistanceLowerBoundPureState
