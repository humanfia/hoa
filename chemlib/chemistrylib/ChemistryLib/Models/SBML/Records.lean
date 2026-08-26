import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import ChemistryLib.ReactionNetwork.Basic

/-!
# Finite SBML model records

This module records the parameter-dependent composition matrix and the finite
reaction-network skeleton needed to compile an SBML model.  Species metadata
keeps the SBML `boundaryCondition`, `constant`, and optional initial
concentration values distinct.

The representation is grounded in BioModels model `BIOMD0000000040`, in
particular the `listOfSpecies` and `listOfReactions` of the Field--Körös--Noyes
Oregonator model.  The cited raw SBML artifact has SHA-256
`0bf2abb25229f3fe7979315139396f9c0bcdb06370ae9c835f7d3fc0e0c79c6a`.
-/

namespace ChemistryLib.Models.SBML

/-- The SBML attributes of a species that affect finite-model compilation. -/
structure SpeciesRecord : Type where
  boundaryCondition : Bool
  constant : Bool
  initialConcentration : Option ℝ

/-- A parameter-dependent SBML model together with its reaction-network
skeleton and the compatibility law at every source complex. -/
structure ParametricModel
    (Params Species ComplexId Reaction : Type) : Type where
  composition : Params → Matrix Species ComplexId ℝ
  reversible : Reaction → Bool
  skeleton : ChemistryLib.ReactionNetwork Species ComplexId Reaction
  source_eq : ∀ (p : Params) (r : Reaction) (s : Species),
    composition p s (skeleton.source r) = (skeleton.reactant r s : ℝ)
  species : Species → SpeciesRecord

end ChemistryLib.Models.SBML
