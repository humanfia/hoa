import Chemlib.ReactionNetwork.Incidence
import Chemlib.ReactionNetwork.Stoichiometry
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Incidence and stoichiometric ranks

The two network ranks are the dimensions of the ranges of the corresponding
matrix linear maps.  The stoichiometric rank is at most the incidence rank
because stoichiometry factors through the incidence map.

The definitions follow YU-CRACIUN-2018, Section 1, equation (5), and Section
2.2, Definition 2.7, together with ACK-2010, Section 2, Definitions 2.3--2.4.
-/

namespace Chemlib.ReactionNetwork

noncomputable section

/-- The dimension of the range of the reaction incidence map. -/
def incidenceRank
    {Species ComplexId ReactionId : Type}
    [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) : ℕ :=
  Module.finrank ℝ (LinearMap.range N.incidenceMatrix.mulVecLin)

/-- The incidence rank is the finrank of the incidence-map range. -/
theorem incidenceRank_eq_finrank_range
    {Species ComplexId ReactionId : Type}
    [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.incidenceRank =
      Module.finrank ℝ (LinearMap.range N.incidenceMatrix.mulVecLin) :=
  rfl

/-- The dimension of the range of the stoichiometric map. -/
def stoichiometricRank
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) : ℕ :=
  Module.finrank ℝ (LinearMap.range N.stoichiometricMatrix.mulVecLin)

/-- The stoichiometric rank is the finrank of the stoichiometric-map range. -/
theorem stoichiometricRank_eq_finrank_range
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.stoichiometricRank =
      Module.finrank ℝ (LinearMap.range N.stoichiometricMatrix.mulVecLin) :=
  rfl

/-- The stoichiometric rank is the dimension of the stoichiometric subspace. -/
theorem stoichiometricRank_eq_finrank_stoichiometricSubspace
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.stoichiometricRank = Module.finrank ℝ N.stoichiometricSubspace :=
  rfl

/-- Stoichiometric rank cannot exceed incidence rank. -/
theorem stoichiometricRank_le_incidenceRank
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.stoichiometricRank ≤ N.incidenceRank := by
  unfold stoichiometricRank incidenceRank
  calc
    Module.finrank ℝ (LinearMap.range N.stoichiometricMatrix.mulVecLin) =
        Module.finrank ℝ
          (Submodule.map N.compositionMatrix.mulVecLin
            (LinearMap.range N.incidenceMatrix.mulVecLin)) := by
      rw [stoichiometricMatrix_eq_composition_mul_incidence N,
        Matrix.mulVecLin_mul, LinearMap.range_comp]
    _ = Module.finrank ℝ
          (LinearMap.range
            (N.compositionMatrix.mulVecLin.domRestrict
              (LinearMap.range N.incidenceMatrix.mulVecLin))) := by
      rw [LinearMap.range_domRestrict]
    _ ≤ Module.finrank ℝ (LinearMap.range N.incidenceMatrix.mulVecLin) :=
      LinearMap.finrank_range_le _

end

end Chemlib.ReactionNetwork
