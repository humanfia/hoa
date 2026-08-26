import ChemistryLib.Autocatalysis.Criteria

/-!
# Milo and Nghe flows

This module expresses the Milo-set conditions (M1)--(M4), their strictly
productive Nghe specialization, and reaction-support minimality for Milo
flows.  Stoichiometric incidence is represented by positive reactant and
product coefficients, while the distinguished source and target edges are
the input and output fields of an integer hyperflow.

Source reference:
* ANDERSEN-ETAL-2021, Definition 6, Lemma 7, and Definitions 8--9.
-/

namespace ChemistryLib.Autocatalysis

/-- A Milo flow is nondecreasing on its selected species and strictly
increasing on at least one of them.  Every selected species is both consumed
and produced by used reactions, and every used reaction meets the selected
set on both its reactant and product sides. -/
def MiloFlow
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    (M : Finset Species) (f : IntegerHyperflow N) : Prop := by
  classical
  exact
    (∀ x ∈ M, 0 < f.input x ∧ f.input x ≤ f.output x) ∧
    (∃ x ∈ M, f.input x < f.output x) ∧
    (∀ x ∈ M,
      (∃ r, 0 < f.reaction r ∧ 0 < N.reactant r x) ∧
      (∃ r, 0 < f.reaction r ∧ 0 < N.product r x)) ∧
    (∀ r, 0 < f.reaction r →
      (∃ x ∈ M, 0 < N.reactant r x) ∧
      (∃ x ∈ M, 0 < N.product r x))

/-- A Nghe flow satisfies the incidence conditions of a Milo flow and is
strictly productive on every species in its nonempty selected set. -/
def NgheFlow
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    (M : Finset Species) (f : IntegerHyperflow N) : Prop := by
  classical
  exact
    M.Nonempty ∧
    (∀ x ∈ M, 0 < f.input x ∧ f.input x < f.output x) ∧
    (∀ x ∈ M,
      (∃ r, 0 < f.reaction r ∧ 0 < N.reactant r x) ∧
      (∃ r, 0 < f.reaction r ∧ 0 < N.product r x)) ∧
    (∀ r, 0 < f.reaction r →
      (∃ x ∈ M, 0 < N.reactant r x) ∧
      (∃ x ∈ M, 0 < N.product r x))

/-- Definition 8's support-minimal cycle condition: no flow with strictly
smaller used-reaction support satisfies (M1) and (M2) on the selected set.
The competing flow is not required to satisfy the incidence conditions (M3)
and (M4). -/
def SupportMinimalMilo
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    (M : Finset Species) (f : IntegerHyperflow N) : Prop := by
  classical
  exact
    MiloFlow M f ∧
    ¬ ∃ g : IntegerHyperflow N,
      (∀ r, g.reaction r ≠ 0 → f.reaction r ≠ 0) ∧
      (∃ r, f.reaction r ≠ 0 ∧ g.reaction r = 0) ∧
      (∀ x ∈ M, 0 < g.input x ∧ g.input x ≤ g.output x) ∧
      (∃ x ∈ M, g.input x < g.output x)

/-- Lemma 7: a Milo flow is formally autocatalytic for at least one species
in its Milo set. -/
theorem miloFlow_exists_formalAutocatalytic
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    {M : Finset Species} {f : IntegerHyperflow N}
    (hf : MiloFlow M f) :
    ∃ x ∈ M, FormalAutocatalytic f x := by
  rcases hf with ⟨hnondecreasing, ⟨x, hx, hstrict⟩, _⟩
  exact ⟨x, hx, (hnondecreasing x hx).1, hstrict⟩

/-- Every Nghe flow is a Milo flow. -/
theorem ngheFlow_miloFlow
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    {M : Finset Species} {f : IntegerHyperflow N}
    (hf : NgheFlow M f) : MiloFlow M f := by
  rcases hf with ⟨⟨x, hx⟩, hstrict, hincidence, hcoverage⟩
  refine ⟨?_, ⟨x, hx, (hstrict x hx).2⟩, hincidence, hcoverage⟩
  intro y hy
  exact ⟨(hstrict y hy).1, (hstrict y hy).2.le⟩

end ChemistryLib.Autocatalysis
