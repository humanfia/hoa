/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QAlgBench.Init
public import QAlgBench.Base.Gate
public import QAlgBench.Base.Util.FinPow

/-!
# Block encodings

Core-level predicates for exact and approximate block encodings.  Following
the standard `(alpha, a, epsilon)` convention, the carrier `U` is a unitary
`Gate`, while the encoded target `A` is a possibly non-unitary
`HilbertOperator`.  The ancilla convention is explicit: the block is obtained by
projecting the ancilla register onto the computational-basis state `0^a` on both
sides, with system basis labels carried by `QAlgBench.prodEquiv`.
-/

@[expose] public section

namespace QAlgBench

noncomputable section

/-- The top-left projected system block
`(<0^a| ⊗ I) U (|0^a> ⊗ I)` as a Hilbert operator on the system register. -/
def projectedBlock (a n : Nat) (U : HilbertOperator (Qubits (a + n))) :
    HilbertOperator (Qubits n) :=
  fun i j =>
    U (prodEquiv ((0 : Fin (2 ^ a)), i)) (prodEquiv ((0 : Fin (2 ^ a)), j))

/-- A finite-dimensional squared error for the projected block.  This records
the norm-style `epsilon` convention without committing Core to a heavier
operator-norm API. -/
def blockEncodingErrorSq (a n : Nat) (alpha : ℝ) (U : Gate (Qubits (a + n)))
    (A : HilbertOperator (Qubits n)) : ℝ :=
  ∑ i : Fin (2 ^ n), ∑ j : Fin (2 ^ n),
    Complex.normSq
      (A i j - (alpha : ℂ) * projectedBlock a n (U : HilbertOperator (Qubits (a + n))) i j)

/-- An `(alpha, a, epsilon)` block encoding: after scaling the top-left
projected block by `alpha`, the result is within `epsilon` of `A`. -/
structure BlockEncoding (alpha : ℝ) (a n : Nat) (epsilon : ℝ)
    (U : Gate (Qubits (a + n))) (A : HilbertOperator (Qubits n)) : Prop where
  alpha_pos : 0 < alpha
  epsilon_nonneg : 0 <= epsilon
  block_error : blockEncodingErrorSq a n alpha U A <= epsilon ^ 2

/-- Exact block encoding with ancilla size `a`: the `0^a` projected block of
the unitary carrier `U` is exactly the system operator `A`.  This is the
`alpha = 1`, `epsilon = 0` special case of `BlockEncoding`, witnessed by
`ExactBlockEncoding.toBlockEncoding`. -/
structure ExactBlockEncoding (a n : Nat) (U : Gate (Qubits (a + n)))
    (A : HilbertOperator (Qubits n)) : Prop where
  block_eq : ∀ i j : Fin (2 ^ n),
    projectedBlock a n (U : HilbertOperator (Qubits (a + n))) i j = A i j

theorem ExactBlockEncoding.projected_block_eq {a n : Nat} {U : Gate (Qubits (a + n))}
    {A : HilbertOperator (Qubits n)} (h : ExactBlockEncoding a n U A) :
    projectedBlock a n (U : HilbertOperator (Qubits (a + n))) = A := by
  ext i j
  exact h.block_eq i j

theorem ExactBlockEncoding.block_entry {a n : Nat} {U : Gate (Qubits (a + n))}
    {A : HilbertOperator (Qubits n)} (h : ExactBlockEncoding a n U A) (i j : Fin (2 ^ n)) :
    (U : HilbertOperator (Qubits (a + n)))
      (prodEquiv ((0 : Fin (2 ^ a)), i)) (prodEquiv ((0 : Fin (2 ^ a)), j))
      = A i j :=
  h.block_eq i j

theorem exactBlockEncoding_iff_projectedBlock {a n : Nat}
    {U : Gate (Qubits (a + n))} {A : HilbertOperator (Qubits n)} :
    ExactBlockEncoding a n U A ↔
      projectedBlock a n (U : HilbertOperator (Qubits (a + n))) = A := by
  constructor
  · intro h
    exact h.projected_block_eq
  · intro h
    exact ⟨by intro i j; rw [h]⟩

theorem ExactBlockEncoding.toBlockEncoding {a n : Nat} {U : Gate (Qubits (a + n))}
    {A : HilbertOperator (Qubits n)} (h : ExactBlockEncoding a n U A) :
    BlockEncoding 1 a n 0 U A := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  simp [blockEncodingErrorSq, h.block_eq]

/-- If the projected block exactly equals `alpha⁻¹ A`, then the same carrier is
an exact `(alpha, a, 0)` block encoding of `A`. -/
theorem ExactBlockEncoding.toScaledBlockEncoding {alpha : ℝ} (halpha : 0 < alpha)
    {a n : Nat} {U : Gate (Qubits (a + n))} {A : HilbertOperator (Qubits n)}
    (h : ExactBlockEncoding a n U ((alpha : ℂ)⁻¹ • A)) :
    BlockEncoding alpha a n 0 U A := by
  refine ⟨halpha, by norm_num, ?_⟩
  have halphaC : ((alpha : ℂ) ≠ 0) := by
    exact_mod_cast ne_of_gt halpha
  have hmulC : (alpha : ℂ) * (alpha : ℂ)⁻¹ = 1 := by
    exact mul_inv_cancel₀ halphaC
  have hentry : ∀ i j : Fin (2 ^ n),
      A i j - (alpha : ℂ) * ((alpha : ℂ)⁻¹ * A i j) = 0 := by
    intro i j
    rw [← mul_assoc, hmulC, one_mul, sub_self]
  rw [show blockEncodingErrorSq a n alpha U A = 0 by
    simp [blockEncodingErrorSq, h.block_eq, hentry]]
  norm_num

/-- Compatibility name for approximate block encodings. -/
abbrev ApproxBlockEncoding (alpha : ℝ) (a n : Nat) (epsilon : ℝ)
    (U : Gate (Qubits (a + n))) (A : HilbertOperator (Qubits n)) : Prop :=
  BlockEncoding alpha a n epsilon U A

end

end QAlgBench
