/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.State
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Pure vectors and rank-one states

Rank-one vector kernels provide pure-state infrastructure for the purification
route registered from [Wilde2011Qst, qit-notes.tex:10238-10290] and
[Gour2024Resources, BookQRT.tex:2051-2069].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QITBench

universe u v

noncomputable section

variable {a : Type u}

/-- The rank-one matrix kernel `|ψ⟩⟨ψ|` associated to an amplitude vector. -/
def rankOneMatrix (ψ : a -> ℂ) : CMatrix a :=
  Matrix.vecMulVec ψ (fun i => star (ψ i))

@[simp]
theorem rankOneMatrix_apply (ψ : a -> ℂ) (i j : a) :
    rankOneMatrix ψ i j = ψ i * star (ψ j) := by
  simp [rankOneMatrix, Matrix.vecMulVec_apply]

/-- The rank-one kernel is Hermitian. -/
@[simp]
theorem rankOneMatrix_conjTranspose (ψ : a -> ℂ) :
    (rankOneMatrix ψ)ᴴ = rankOneMatrix ψ := by
  rw [rankOneMatrix, Matrix.conjTranspose_vecMulVec]
  ext i j
  simp [Matrix.vecMulVec_apply]

/-- The rank-one kernel is Hermitian, as a predicate. -/
theorem rankOneMatrix_isHermitian (ψ : a -> ℂ) :
    (rankOneMatrix ψ).IsHermitian :=
  rankOneMatrix_conjTranspose ψ

variable [Fintype a]

/-- The rank-one kernel is positive semidefinite. -/
theorem rankOneMatrix_pos (ψ : a -> ℂ) :
    (rankOneMatrix ψ).PosSemidef := by
  simpa [rankOneMatrix] using Matrix.posSemidef_vecMulVec_self_star ψ

/-- The trace of `|ψ⟩⟨ψ|` is the squared norm dot product. -/
@[simp]
theorem rankOneMatrix_trace (ψ : a -> ℂ) :
    (rankOneMatrix ψ).trace = ψ ⬝ᵥ (fun i => star (ψ i)) := by
  simp [rankOneMatrix]

/-- Rank-one kernels have matrix rank at most one. -/
theorem rankOneMatrix_rank_le_one (ψ : a -> ℂ) :
    (rankOneMatrix ψ).rank ≤ 1 := by
  simpa [rankOneMatrix] using Matrix.rank_vecMulVec_le ψ (fun i => star (ψ i))

variable [DecidableEq a]

/-- A pure vector is an amplitude vector whose rank-one kernel has trace one. -/
structure PureVector (a : Type u) [Fintype a] [DecidableEq a] where
  amp : a -> ℂ
  trace_rankOne_eq_one : (rankOneMatrix amp).trace = 1

namespace PureVector

variable (ψ : PureVector a)

/-- The state represented by a trace-normalized pure vector. -/
def state : State a where
  matrix := rankOneMatrix ψ.amp
  pos := rankOneMatrix_pos ψ.amp
  trace_eq_one := ψ.trace_rankOne_eq_one

@[simp]
theorem state_matrix :
    ψ.state.matrix = rankOneMatrix ψ.amp :=
  rfl

@[simp]
theorem state_matrix_apply (i j : a) :
    ψ.state.matrix i j = ψ.amp i * star (ψ.amp j) := by
  simp [state]

theorem state_matrix_rank_le_one :
    ψ.state.matrix.rank ≤ 1 := by
  simpa using rankOneMatrix_rank_le_one ψ.amp

@[simp]
theorem state_matrix_conjTranspose :
    (ψ.state.matrix)ᴴ = ψ.state.matrix := by
  simp [state]

theorem state_matrix_isHermitian :
    ψ.state.matrix.IsHermitian :=
  state_matrix_conjTranspose ψ

/-- Relabel a normalized pure vector along a finite basis equivalence. -/
def reindex {β : Type v} [Fintype β] [DecidableEq β]
    (e : a ≃ β) : PureVector β where
  amp := fun j => ψ.amp (e.symm j)
  trace_rankOne_eq_one := by
    calc
      (rankOneMatrix (fun j : β => ψ.amp (e.symm j))).trace =
          ∑ j : β, ψ.amp (e.symm j) * star (ψ.amp (e.symm j)) := by
            simp [Matrix.trace, rankOneMatrix_apply]
      _ = ∑ i : a, ψ.amp i * star (ψ.amp i) := by
            refine Fintype.sum_equiv e.symm
              (fun j : β => ψ.amp (e.symm j) * star (ψ.amp (e.symm j)))
              (fun i : a => ψ.amp i * star (ψ.amp i)) ?_
            intro j
            simp
      _ = (rankOneMatrix ψ.amp).trace := by
            simp [Matrix.trace, rankOneMatrix_apply]
      _ = 1 := ψ.trace_rankOne_eq_one

@[simp]
theorem reindex_amp {β : Type v} [Fintype β] [DecidableEq β]
    (e : a ≃ β) (j : β) :
    (ψ.reindex e).amp j = ψ.amp (e.symm j) :=
  rfl

/-- Relabeling a pure vector and then forming its state agrees with relabeling
the associated rank-one state. -/
theorem reindex_state {β : Type v} [Fintype β] [DecidableEq β]
    (e : a ≃ β) :
    (ψ.reindex e).state = ψ.state.reindex e := by
  apply State.ext
  ext i j
  simp [State.reindex, PureVector.state, rankOneMatrix_apply]

/-- The density matrix of a normalized pure vector is idempotent. -/
@[simp]
theorem state_matrix_mul_self :
    ψ.state.matrix * ψ.state.matrix = ψ.state.matrix := by
  have hdot : (fun i => star (ψ.amp i)) ⬝ᵥ ψ.amp = 1 := by
    have htrace := ψ.trace_rankOne_eq_one
    rw [rankOneMatrix_trace] at htrace
    rw [dotProduct_comm]
    exact htrace
  change rankOneMatrix ψ.amp * rankOneMatrix ψ.amp = rankOneMatrix ψ.amp
  rw [rankOneMatrix, Matrix.vecMulVec_mul_vecMulVec, hdot]
  simp

end PureVector

end

end QITBench
