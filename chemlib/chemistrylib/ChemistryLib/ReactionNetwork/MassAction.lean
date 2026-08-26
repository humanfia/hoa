import ChemistryLib.ReactionNetwork.Stoichiometry

/-!
# Algebraic mass-action kinetics

This first cone uses real-valued states and rate assignments.  Positivity and
balance hypotheses belong to later modules; the algebraic factorization and
steady-state predicate do not require them.
-/

namespace ChemistryLib

namespace Complex

/-- The finite-support concentration monomial associated with a complex. -/
def monomial {Species A : Type} [CommMonoid A]
    (y : Complex Species) (x : Species → A) : A :=
  y.prod fun s n ↦ x s ^ n

/-- The monomial associated with the zero complex is one. -/
@[simp] theorem zero_monomial {Species A : Type} [CommMonoid A]
    (x : Species → A) :
    monomial (0 : Complex Species) x = 1 := by
  rfl

end Complex

namespace ReactionNetwork

/-- The mass-action flux through each reaction. -/
def massActionFlux
    {Species ComplexId ReactionId : Type}
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ) : ReactionId → ℝ :=
  fun r ↦ k r * Complex.monomial (N.reactant r) x

/-- The mass-action vector field is stoichiometric matrix times flux. -/
def massActionVectorField
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ) : Species → ℝ :=
  Matrix.mulVec N.stoichiometricMatrix (N.massActionFlux k x)

/-- A state is steady exactly when its mass-action vector field vanishes. -/
def IsSteadyState
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ) : Prop :=
  N.massActionVectorField k x = 0

/-- Every mass-action vector field belongs to the stoichiometric subspace. -/
theorem massActionVectorField_mem_stoichiometricSubspace
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ) :
    N.massActionVectorField k x ∈ N.stoichiometricSubspace := by
  exact N.mulVec_mem_stoichiometricSubspace (N.massActionFlux k x)

/-- A reaction whose reactant is the zero complex has constant flux. -/
theorem massActionFlux_zero_reactant
    {Species ComplexId ReactionId : Type}
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ) (r : ReactionId)
    (h : N.reactant r = 0) : N.massActionFlux k x r = k r := by
  simp [massActionFlux, h]

end ReactionNetwork

end ChemistryLib
