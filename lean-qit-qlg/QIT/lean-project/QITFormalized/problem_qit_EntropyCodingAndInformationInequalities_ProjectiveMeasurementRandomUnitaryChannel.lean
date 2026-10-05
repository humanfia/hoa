import QITBench.Base

namespace QITFormalized.ProjectiveMeasurementRandomUnitaryChannel

open QITBench

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The complementary projector `Q = I - P`. -/
def projectorComplement (P : CMatrix a) : CMatrix a :=
  1 - P

/-- The matrix produced by the non-selective two-outcome projective measurement. -/
def nonSelectiveProjectiveMeasurement (P ρ : CMatrix a) : CMatrix a :=
  P * ρ * P + projectorComplement P * ρ * projectorComplement P

/-- A two-outcome non-selective projective measurement is a mixture of two fixed
unitary conjugations, uniformly for every density operator. -/
theorem projectiveMeasurement_eq_randomUnitary
    (P : CMatrix a) (hP : IsStarProjection P) :
    ∃ U₁ U₂ : Matrix.unitaryGroup a ℂ, ∃ p : ℝ,
      0 ≤ p ∧ p ≤ 1 ∧
        ∀ ρ : State a,
          nonSelectiveProjectiveMeasurement P ρ.matrix =
            (p : ℂ) •
                (U₁.1 * ρ.matrix * Matrix.conjTranspose U₁.1) +
              ((1 - p : ℝ) : ℂ) •
                (U₂.1 * ρ.matrix * Matrix.conjTranspose U₂.1) := by
  let U₂ : Matrix.unitaryGroup a ℂ :=
    ⟨2 * P - 1, hP.two_mul_sub_one_mem_unitary⟩
  refine ⟨1, U₂, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro ρ
  simp [nonSelectiveProjectiveMeasurement, projectorComplement, U₂,
    ← Matrix.star_eq_conjTranspose, hP.isSelfAdjoint.star_eq]
  noncomm_ring
  module

end

end QITFormalized.ProjectiveMeasurementRandomUnitaryChannel
