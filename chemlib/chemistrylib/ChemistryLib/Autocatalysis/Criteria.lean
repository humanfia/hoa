import ChemistryLib.Autocatalysis.StoichiometricAdapters

/-!
# Formal and exclusive autocatalysis criteria

These predicates express formal and exclusive autocatalysis using exact integer
hyperflows and a finite set of allowed input species.

Source references:
* ANDERSEN-ETAL-2021, Definitions 1--2 and 5, and equation (9).
* Sanitized contract `research:andersen_autocatalysis_2021:integer_hyperflow`.
-/

namespace ChemistryLib.Autocatalysis

/-- A hyperflow is formally autocatalytic for a species when its positive input
flow is strictly smaller than its output flow. -/
def FormalAutocatalytic
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    (f : IntegerHyperflow N) (x : Species) : Prop :=
  0 < f.input x ∧ f.input x < f.output x

/-- Every species with positive input exchange belongs to the allowed food set. -/
def InputSupported
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    (food : Finset Species) (f : IntegerHyperflow N) : Prop := by
  classical
  exact ∀ s, 0 < f.input s → s ∈ food

/-- A species has a food-supported formal autocatalytic witness, but cannot be
produced by any food-supported hyperflow that has zero input of that species. -/
def ExclusiveAutocatalytic
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    (food : Finset Species) (x : Species) : Prop := by
  classical
  exact
    (∃ f : IntegerHyperflow N,
      InputSupported (insert x food) f ∧ FormalAutocatalytic f x) ∧
    ¬ ∃ f : IntegerHyperflow N,
      InputSupported food f ∧ f.input x = 0 ∧ 0 < f.output x

end ChemistryLib.Autocatalysis
