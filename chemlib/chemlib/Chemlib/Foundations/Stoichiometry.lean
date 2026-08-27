import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs

/-!
# Stoichiometric numbers

A stoichiometric number assigns a signed rational coefficient to each species:
products have positive coefficients, reactants have negative coefficients, and a
species participates precisely when its coefficient is nonzero.  For a finite
species type, the stoichiometric support collects exactly those participating
species.

Sources:

* `IUPAC-GOLDBOOK-5.0.0:S06025 definition 1`
* `icho_2026_t2_a2:T2-A2`
* `icho_2026_t4_a6:T4-A6`
* `icho_2026_t7_a2:T7-A2`
* `icho_2026_t7_a3:T7-A3`
-/

namespace Chemlib.Foundations

/-- A signed rational stoichiometric coefficient for every species. -/
abbrev StoichiometricNumber (Species : Type) : Type := Species → ℚ

/-- A species is a product when its stoichiometric number is positive. -/
def isProduct {Species : Type} (ν : StoichiometricNumber Species) (s : Species) : Prop :=
  0 < ν s

/-- A species is a reactant when its stoichiometric number is negative. -/
def isReactant {Species : Type} (ν : StoichiometricNumber Species) (s : Species) : Prop :=
  ν s < 0

/-- A species participates when its stoichiometric number is nonzero. -/
def participates {Species : Type} (ν : StoichiometricNumber Species) (s : Species) : Prop :=
  ν s ≠ 0

/-- The finite set of species with nonzero stoichiometric number. -/
def stoichiometricSupport {Species : Type} [Fintype Species] [DecidableEq Species]
    (ν : StoichiometricNumber Species) : Finset Species :=
  Finset.univ.filter (fun s => ν s ≠ 0)

/-- Membership in the stoichiometric support is equivalent to participation. -/
theorem mem_stoichiometricSupport {Species : Type} [Fintype Species] [DecidableEq Species]
    (ν : StoichiometricNumber Species) (s : Species) :
    s ∈ stoichiometricSupport ν ↔ participates ν s := by
  simp [stoichiometricSupport, participates]

end Chemlib.Foundations
