import ChemistryLib.ReactionNetwork.Basic

/-!
# Count-state reaction jumps

This module gives the guarded count-vector firing semantics for a stochastic
chemical reaction network.  It follows ACK-2010, Section 3.1, equations
(3.1)--(3.2), as recorded by the sanitized research contract
`research:ack_2010:ctmc_generator`.
-/

namespace ChemistryLib.Stochastic

/-- A molecular count for each species. -/
abbrev CountState (Species : Type) : Type := Species → ℕ

/-- A reaction can fire when its reactant complex is available coordinatewise. -/
def CanFire {Species Complex Reaction : Type}
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (r : Reaction) (x : CountState Species) : Prop :=
  ∀ i, N.reactant r i ≤ x i

/-- The candidate count state obtained by consuming reactants and producing products. -/
def fire {Species Complex Reaction : Type}
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (x : CountState Species) (r : Reaction) : CountState Species :=
  fun i ↦ x i - N.reactant r i + N.product r i

/-- On the firing domain, `fire` has the expected coordinatewise update. -/
theorem fire_apply_of_canFire {Species Complex Reaction : Type}
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (x : CountState Species) (r : Reaction) (i : Species)
    (_h : CanFire N r x) :
    fire N x r i = x i - N.reactant r i + N.product r i :=
  rfl

end ChemistryLib.Stochastic
