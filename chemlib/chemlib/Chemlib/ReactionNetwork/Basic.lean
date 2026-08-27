import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Finite reaction-network data

This module fixes the data representation used by the first Chemlib
release cone.  Finiteness is supplied by `Fintype` instances in the modules
that form finite sums; the network itself keeps the three index types
independent.
-/

namespace Chemlib

/-- A chemical complex is a finitely supported vector of natural
stoichiometric coefficients. -/
abbrev Complex (Species : Type) : Type := Species →₀ ℕ

/-- An indexed chemical reaction network.  Distinct reaction identifiers may
have the same source and target, so parallel reactions are represented
faithfully. -/
structure ReactionNetwork (Species ComplexId ReactionId : Type) : Type where
  complex : ComplexId → Complex Species
  source : ReactionId → ComplexId
  target : ReactionId → ComplexId

/-- The complex having no species. -/
def zeroComplex {Species : Type} : Complex Species := 0

namespace ReactionNetwork

/-- The stoichiometric complex consumed by a reaction. -/
def reactant {Species ComplexId ReactionId : Type}
    (N : ReactionNetwork Species ComplexId ReactionId)
    (r : ReactionId) : Complex Species :=
  N.complex (N.source r)

/-- The stoichiometric complex produced by a reaction. -/
def product {Species ComplexId ReactionId : Type}
    (N : ReactionNetwork Species ComplexId ReactionId)
    (r : ReactionId) : Complex Species :=
  N.complex (N.target r)

end ReactionNetwork

end Chemlib
