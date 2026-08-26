import ChemistryLib.ReactionNetwork.Basic
import ChemistryLib.ReactionNetwork.Stoichiometry

/-!
# Integer hyperflows

This module formalizes the nonnegative integer reaction and exchange flows of
`ANDERSEN-ETAL-2021`, equation (2), Definitions 1–2, and equation (5).  The
exact signed species balance is kept over `ℤ`; its real-valued consequence is
the stoichiometric-matrix formulation used in Lemmas 3–4.
-/

namespace ChemistryLib.Autocatalysis

/-- The exact signed species change produced by an integer reaction flow. -/
def reactionChangeZ
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (v : ReactionId → ℤ) : Species → ℤ :=
  fun s ↦ Finset.univ.sum fun r ↦
    ((N.product r s : ℤ) - (N.reactant r s : ℤ)) * v r

/-- A nonnegative integer hyperflow with input and output exchange and exact
species balance. -/
structure IntegerHyperflow
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) : Type where
  reaction : ReactionId → ℤ
  input : Species → ℤ
  output : Species → ℤ
  reaction_nonnegative : ∀ r, 0 ≤ reaction r
  input_nonnegative : ∀ s, 0 ≤ input s
  output_nonnegative : ∀ s, 0 ≤ output s
  balance : reactionChangeZ N reaction = fun s ↦ output s - input s

namespace IntegerHyperflow

/-- The reaction part of a hyperflow is the composite reaction whose signed
change equals net output exchange. -/
theorem composite_balance
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (f : IntegerHyperflow N) :
    reactionChangeZ N f.reaction = fun s ↦ f.output s - f.input s := by
  exact f.balance

/-- Casting the exact integer balance recovers multiplication by the real
stoichiometric matrix. -/
theorem real_stoichiometric_balance
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (f : IntegerHyperflow N) :
    Matrix.mulVec (ChemistryLib.ReactionNetwork.stoichiometricMatrix N)
        (fun r ↦ (f.reaction r : ℝ)) =
      fun s ↦ ((f.output s - f.input s : ℤ) : ℝ) := by
  funext s
  rw [← congrFun (composite_balance N f) s]
  simp [Matrix.mulVec, dotProduct,
    ChemistryLib.ReactionNetwork.stoichiometricMatrix,
    ChemistryLib.ReactionNetwork.reactionVector, reactionChangeZ]

end IntegerHyperflow

end ChemistryLib.Autocatalysis
