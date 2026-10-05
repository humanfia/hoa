import QAlgBench.Base

/-!
# Linear dependence over `ℝ` versus `𝔽₂`

The same three coordinate vectors are linearly independent over `ℝ` but
linearly dependent over the two-element field.  Their binary span consists
exactly of the zero vector and the three given vectors.
-/

namespace QAlgFormalized
namespace LinearDependenceRvsFtwo

/-- Three-dimensional real coordinate vectors. -/
abbrev RealVec3 := Fin 3 → ℝ

/-- Three-dimensional coordinate vectors over the two-element field. -/
abbrev F2Vec3 := Fin 3 → ZMod 2

/-- The real vector `(1, 1, 0)ᵀ`. -/
def v1Real : RealVec3 := ![1, 1, 0]

/-- The real vector `(0, 1, 1)ᵀ`. -/
def v2Real : RealVec3 := ![0, 1, 1]

/-- The real vector `(1, 0, 1)ᵀ`. -/
def v3Real : RealVec3 := ![1, 0, 1]

/-- The binary vector `(1, 1, 0)ᵀ`. -/
def v1F2 : F2Vec3 := ![1, 1, 0]

/-- The binary vector `(0, 1, 1)ᵀ`. -/
def v2F2 : F2Vec3 := ![0, 1, 1]

/-- The binary vector `(1, 0, 1)ᵀ`. -/
def v3F2 : F2Vec3 := ![1, 0, 1]

/-- The three given vectors are linearly independent over `ℝ`. -/
theorem real_linearIndependent :
    LinearIndependent ℝ ![v1Real, v2Real, v3Real] := by
  rw [Fintype.linearIndependent_iff]
  intro g h i
  have h0 := congr_fun h 0
  have h1 := congr_fun h 1
  have h2 := congr_fun h 2
  simp [v1Real, v2Real, v3Real, Fin.sum_univ_succ] at h0 h1 h2
  fin_cases i <;> simp <;> linarith

/-- The three given vectors are linearly dependent over `𝔽₂`. -/
theorem f2_linearDependent :
    ¬ LinearIndependent (ZMod 2) ![v1F2, v2F2, v3F2] := by
  rw [not_linearIndependent_iff]
  refine ⟨Finset.univ, fun _ => 1, ?_, 0, Finset.mem_univ _, ?_⟩
  · ext i
    fin_cases i <;> decide
  · decide

/--
The full binary span of the three given vectors is the four-element set
consisting of the zero vector and the three given vectors.
-/
theorem f2_span :
    ((Submodule.span (ZMod 2) {v1F2, v2F2, v3F2} :
        Submodule (ZMod 2) F2Vec3) : Set F2Vec3) =
      {0, v1F2, v2F2, v3F2} := by
  let S : Submodule (ZMod 2) F2Vec3 :=
    { carrier := {0, v1F2, v2F2, v3F2}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with (rfl | rfl | rfl | rfl) <;>
          rcases hy with (rfl | rfl | rfl | rfl) <;>
          decide
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with (rfl | rfl | rfl | rfl)
        · simp
        all_goals fin_cases c <;> decide }
  apply le_antisymm
  · change Submodule.span (ZMod 2) {v1F2, v2F2, v3F2} ≤ S
    apply Submodule.span_le.2
    intro x hx
    change x ∈ ({v1F2, v2F2, v3F2} : Set F2Vec3) at hx
    change x ∈ ({0, v1F2, v2F2, v3F2} : Set F2Vec3)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    aesop
  · intro x hx
    change x ∈ ({0, v1F2, v2F2, v3F2} : Set F2Vec3) at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)

end LinearDependenceRvsFtwo
end QAlgFormalized
