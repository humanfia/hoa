import ChemistryLib.Models.SBML.Records
import ChemistryLib.ReactionNetwork.Incidence

/-!
# Symbolic compilation of SBML stoichiometry

This module compiles the parameter-dependent complex composition of an SBML
model into product, reactant, and stoichiometric matrices.  It also exposes an
explicit row restriction for internal species and relates the compiled matrix
to the directed incidence matrix of the fixed reaction skeleton.

The construction is grounded in BioModels model `BIOMD0000000040`, especially
SBML reactions `Reaction1`--`Reaction5` of the Field--Körös--Noyes Oregonator
model.  The cited raw SBML artifact has SHA-256
`0bf2abb25229f3fe7979315139396f9c0bcdb06370ae9c835f7d3fc0e0c79c6a`.
-/

namespace ChemistryLib.Models.SBML

/-- Product stoichiometry, read from the parameter-dependent composition at
each reaction target. -/
def productMatrix
    {Params Species ComplexId Reaction : Type}
    (m : ParametricModel Params Species ComplexId Reaction) :
    Params → Matrix Species Reaction ℝ :=
  fun p s r ↦ m.composition p s (m.skeleton.target r)

/-- Reactant stoichiometry, read from the natural reactant complexes of the
fixed reaction skeleton. -/
def reactantMatrix
    {Params Species ComplexId Reaction : Type}
    (m : ParametricModel Params Species ComplexId Reaction) :
    Params → Matrix Species Reaction ℝ :=
  fun _ s r ↦ (m.skeleton.reactant r s : ℝ)

/-- Net stoichiometry: product composition minus reactant composition. -/
def stoichiometricMatrix
    {Params Species ComplexId Reaction : Type}
    (m : ParametricModel Params Species ComplexId Reaction) :
    Params → Matrix Species Reaction ℝ :=
  fun p ↦ productMatrix m p - reactantMatrix m p

/-- Restrict the full stoichiometric matrix to species selected by an explicit
embedding of the internal-state index. -/
def internalStoichiometricMatrix
    {Params Species ComplexId Reaction Internal : Type}
    (m : ParametricModel Params Species ComplexId Reaction)
    (embedding : Internal → Species) :
    Params → Matrix Internal Reaction ℝ :=
  fun p i r ↦ stoichiometricMatrix m p (embedding i) r

theorem internalStoichiometricMatrix_apply
    {Params Species ComplexId Reaction Internal : Type}
    (m : ParametricModel Params Species ComplexId Reaction)
    (embedding : Internal → Species)
    (p : Params) (i : Internal) (r : Reaction) :
    internalStoichiometricMatrix m embedding p i r =
      stoichiometricMatrix m p (embedding i) r := by
  rfl

theorem stoichiometricMatrix_apply
    {Params Species ComplexId Reaction : Type}
    (m : ParametricModel Params Species ComplexId Reaction)
    (p : Params) (s : Species) (r : Reaction) :
    stoichiometricMatrix m p s r =
      productMatrix m p s r - reactantMatrix m p s r := by
  rfl

theorem stoichiometricMatrix_eq_mul_incidence
    {Params Species ComplexId Reaction : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (m : ParametricModel Params Species ComplexId Reaction)
    (p : Params) :
    stoichiometricMatrix m p =
      (m.composition p) * m.skeleton.incidenceMatrix := by
  ext s r
  simp only [stoichiometricMatrix, productMatrix, reactantMatrix, Matrix.sub_apply]
  rw [Matrix.mul_apply]
  simp_rw [ChemistryLib.ReactionNetwork.incidenceMatrix, mul_sub]
  rw [Finset.sum_sub_distrib]
  simp [m.source_eq]

end ChemistryLib.Models.SBML
