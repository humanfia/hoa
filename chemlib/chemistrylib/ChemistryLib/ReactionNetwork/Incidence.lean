import ChemistryLib.ReactionNetwork.Graph
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Complex composition and reaction incidence

The matrix convention is fixed here: species index composition rows, complexes
index composition columns and incidence rows, and reactions index incidence
columns.
-/

namespace ChemistryLib.ReactionNetwork

/-- The complex-composition matrix, with species rows and complex columns. -/
def compositionMatrix
    {Species ComplexId ReactionId : Type}
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) :
    Matrix Species ComplexId ℝ :=
  fun s c ↦ N.complex c s

/-- Directed incidence, using `+1` at the target and `-1` at the source. -/
def incidenceMatrix
    {Species ComplexId ReactionId : Type} [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) :
    Matrix ComplexId ReactionId ℝ :=
  fun c r ↦
    (if c = N.target r then 1 else 0) -
      (if c = N.source r then 1 else 0)

/-- Every column of the directed incidence matrix has total weight zero. -/
theorem incidence_column_sum
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (r : ReactionId) :
    Finset.univ.sum (fun c ↦ N.incidenceMatrix c r) = 0 := by
  simp [incidenceMatrix]

end ChemistryLib.ReactionNetwork
