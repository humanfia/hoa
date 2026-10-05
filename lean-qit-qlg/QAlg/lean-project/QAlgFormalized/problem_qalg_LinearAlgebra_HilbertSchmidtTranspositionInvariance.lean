import QAlgBench.Base

/-!
# Hilbert--Schmidt transposition invariance

For square complex matrices, transposition preserves the Hilbert--Schmidt
inner product and hence the distance induced by the Hilbert--Schmidt norm.
-/

namespace QAlgFormalized.HilbertSchmidtTranspositionInvariance

noncomputable section

/-- The Hilbert--Schmidt inner product on square complex matrices:
`⟪B, C⟫ₕₛ = trace (Bᴴ C)`. -/
def hilbertSchmidtInner {d : ℕ}
    (B C : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  Matrix.trace (B.conjTranspose * C)

/-- The real Hilbert--Schmidt norm induced by `hilbertSchmidtInner`. -/
def hilbertSchmidtNorm {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Real.sqrt (hilbertSchmidtInner A A).re

/-- Transposition preserves the Hilbert--Schmidt inner product. Unfolding
`hilbertSchmidtInner` gives
`trace ((Uᵀ)ᴴ Vᵀ) = trace (Uᴴ V)`. -/
theorem hilbertSchmidtInner_transpose {d : ℕ}
    (U V : Matrix (Fin d) (Fin d) ℂ) :
    hilbertSchmidtInner U.transpose V.transpose =
      hilbertSchmidtInner U V := by
  unfold hilbertSchmidtInner
  rw [Matrix.transpose_conjTranspose]
  calc
    (U.map star * V.transpose).trace =
        (V.transpose * U.map star).trace := Matrix.trace_mul_comm _ _
    _ = (U.conjTranspose * V).transpose.trace := by
      rw [Matrix.transpose_mul, Matrix.conjTranspose_transpose]
    _ = (U.conjTranspose * V).trace := Matrix.trace_transpose _

/-- Transposition is an isometry for Hilbert--Schmidt distance. -/
theorem hilbertSchmidtNorm_transpose_sub {d : ℕ}
    (U V : Matrix (Fin d) (Fin d) ℂ) :
    hilbertSchmidtNorm (U.transpose - V.transpose) =
      hilbertSchmidtNorm (U - V) := by
  rw [← Matrix.transpose_sub]
  unfold hilbertSchmidtNorm
  rw [hilbertSchmidtInner_transpose]

end

end QAlgFormalized.HilbertSchmidtTranspositionInvariance
