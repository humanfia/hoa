import QITBench.Base

open scoped ComplexOrder MatrixOrder

namespace QITFormalized.UnitalityChoiRepresentation

open QITBench

noncomputable section

/-- The unnormalized maximally entangled vector
`|Γ⟩ = ∑ i, |i⟩ ⊗ |i⟩` in the shared `Fin d` computational basis. -/
def unnormalizedMaximallyEntangledKet (d : ℕ) : Fin d × Fin d → ℂ :=
  fun ij => if ij.1 = ij.2 then 1 else 0

/-- The rank-one operator `|Γ⟩⟨Γ|` for the unnormalized maximally entangled
vector in the shared computational basis. -/
def unnormalizedMaximallyEntangledProjector (d : ℕ) :
    CMatrix (Fin d × Fin d) :=
  Matrix.vecMulVec (unnormalizedMaximallyEntangledKet d)
    (fun ij => star (unnormalizedMaximallyEntangledKet d ij))

/-- The unnormalized Choi matrix
`J_Φ = (id ⊗ Φ)(|Γ⟩⟨Γ|)`.

Both the input and output systems use `Fin d`, recording the stipulated equal
dimensions and the fixed common computational-basis labels. -/
def unnormalizedChoiMatrix (d : ℕ)
    (Phi : MatrixMap (Fin d) (Fin d)) : CMatrix (Fin d × Fin d) :=
  MatrixMap.kron (LinearMap.id : MatrixMap (Fin d) (Fin d)) Phi
    (unnormalizedMaximallyEntangledProjector d)

/-- The explicit `|Γ⟩⟨Γ|` construction agrees with QITBench's matrix-unit
definition of the unnormalized Choi matrix. -/
theorem unnormalizedChoiMatrix_eq_choi (d : ℕ)
    (Phi : MatrixMap (Fin d) (Fin d)) :
    unnormalizedChoiMatrix d Phi = MatrixMap.choi Phi := by
  ext x y
  rcases x with ⟨xA, xB⟩
  rcases y with ⟨yA, yB⟩
  classical
  simp [unnormalizedChoiMatrix, unnormalizedMaximallyEntangledProjector,
    unnormalizedMaximallyEntangledKet, MatrixMap.kron, MatrixMap.choi,
    Matrix.vecMulVec, Matrix.single]
  rw [Finset.sum_eq_single xA]
  rw [Finset.sum_eq_single yA]
  rw [Finset.sum_eq_single xA]
  rw [Finset.sum_eq_single yA]
  all_goals aesop

/-- Tracing the input/reference subsystem of an unnormalized Choi matrix
returns the image of the identity. -/
theorem partialTraceA_choi_eq_apply_one (d : ℕ)
    (Phi : MatrixMap (Fin d) (Fin d)) :
    partialTraceA (MatrixMap.choi Phi) = Phi (1 : CMatrix (Fin d)) := by
  have hOne :
      (∑ i : Fin d, Matrix.single i i (1 : ℂ)) =
        (1 : CMatrix (Fin d)) := by
    ext i i'
    by_cases h : i = i'
    · subst i'
      classical
      simp only [Matrix.sum_apply]
      rw [Finset.sum_eq_single i] <;> aesop
    · classical
      simp only [Matrix.sum_apply]
      have hrhs : (1 : CMatrix (Fin d)) i i' = 0 := by simp [h]
      rw [hrhs]
      apply Finset.sum_eq_zero
      aesop
  ext j j'
  simp only [partialTraceA, MatrixMap.choi]
  rw [← Matrix.sum_apply, ← map_sum, hOne]

/-- A completely positive map between the two `d`-dimensional systems is
unital iff the first-subsystem partial trace of its unnormalized Choi matrix
is the output identity. -/
theorem unital_iff_partialTraceA_unnormalizedChoi (d : ℕ)
    (Phi : MatrixMap (Fin d) (Fin d))
    (_hCP : MatrixMap.IsCompletelyPositive Phi) :
    Phi (1 : CMatrix (Fin d)) = 1 ↔
      partialTraceA (unnormalizedChoiMatrix d Phi) = 1 := by
  rw [unnormalizedChoiMatrix_eq_choi, partialTraceA_choi_eq_apply_one]

end

end QITFormalized.UnitalityChoiRepresentation
