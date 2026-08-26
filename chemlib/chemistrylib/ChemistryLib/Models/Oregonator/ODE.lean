import ChemistryLib.Models.Oregonator.Data
import ChemistryLib.ReactionNetwork.MassAction

/-!
# Oregonator mass-action ODE

This module lifts the three dynamical Oregonator concentrations to the full
five-species state, evaluates the five natural-reactant mass-action fluxes, and
restricts the resulting stoichiometric vector field to the internal species.

The sanitized campaign source is
`research:biomodels_oregonator_0040:ode_algebra`.  Its kinetic laws and
boundary-species distinction are grounded in BioModels model
`BIOMD0000000040`, specifically the kinetic-law MathML and parameter lists for
`Reaction1`--`Reaction5` and the boundary flags on `BrO3` and `HOBr`.
The cited raw SBML artifact has SHA-256
`0bf2abb25229f3fe7979315139396f9c0bcdb06370ae9c835f7d3fc0e0c79c6a`.

This is an algebraic ODE construction only; it makes no claim about numerical
trajectories, oscillation, or periodicity.
-/

namespace ChemistryLib.Models.Oregonator

/-- Empirical inputs to the Oregonator ODE: fixed boundary concentrations,
the real fifth-product coefficient, and the five reaction rate constants. -/
structure Parameters : Type where
  boundaryValue : Species → ℝ
  f : ℝ
  rate : Reaction → ℝ

/-- Extend an internal state by the fixed boundary concentrations. -/
def fullState (p : Parameters) (x : InternalSpecies → ℝ) : Species → ℝ
  | .Br => x .Br
  | .Ce => x .Ce
  | .HBrO2 => x .HBrO2
  | .BrO3 => p.boundaryValue .BrO3
  | .HOBr => p.boundaryValue .HOBr

/-- The state lift preserves all three internal coordinates and exposes the
two fixed boundary values only through `Parameters`. -/
theorem fullState_spec : ∀ (p : Parameters) (x : InternalSpecies → ℝ),
    fullState p x Species.Br = x InternalSpecies.Br ∧
    fullState p x Species.Ce = x InternalSpecies.Ce ∧
    fullState p x Species.HBrO2 = x InternalSpecies.HBrO2 ∧
    fullState p x Species.BrO3 = p.boundaryValue Species.BrO3 ∧
    fullState p x Species.HOBr = p.boundaryValue Species.HOBr := by
  intro p x
  simp [fullState]

/-- The five source-authenticated Oregonator mass-action fluxes. -/
def flux (p : Parameters) (x : InternalSpecies → ℝ) : Reaction → ℝ
  | .R1 => p.rate .R1 * x .Br * p.boundaryValue .BrO3
  | .R2 => p.rate .R2 * x .Br * x .HBrO2
  | .R3 => p.rate .R3 * p.boundaryValue .BrO3 * x .HBrO2
  | .R4 => p.rate .R4 * (x .HBrO2) ^ 2
  | .R5 => p.rate .R5 * x .Ce

/-- Coordinate form of the five Oregonator kinetic laws. -/
theorem flux_spec : ∀ (p : Parameters) (x : InternalSpecies → ℝ),
    flux p x Reaction.R1 =
      p.rate Reaction.R1 * x InternalSpecies.Br * p.boundaryValue Species.BrO3 ∧
    flux p x Reaction.R2 =
      p.rate Reaction.R2 * x InternalSpecies.Br * x InternalSpecies.HBrO2 ∧
    flux p x Reaction.R3 =
      p.rate Reaction.R3 * p.boundaryValue Species.BrO3 * x InternalSpecies.HBrO2 ∧
    flux p x Reaction.R4 =
      p.rate Reaction.R4 * (x InternalSpecies.HBrO2) ^ 2 ∧
    flux p x Reaction.R5 = p.rate Reaction.R5 * x InternalSpecies.Ce := by
  intro p x
  simp [flux]

/-- The explicit flux table is the core natural-reactant mass-action flux on
the lifted state, while the symbolic fifth-product coefficient remains `f`. -/
theorem flux_eq_massActionFlux : ∀ (data : OregonatorSourceData)
    (p : Parameters) (x : InternalSpecies → ℝ),
    flux p x =
      (oregonatorModel data).skeleton.massActionFlux p.rate (fullState p x) ∧
    (oregonatorModel data).composition p.f Species.Br
      ((oregonatorModel data).skeleton.target Reaction.R5) = p.f := by
  intro data p x
  constructor
  · funext r
    cases r <;>
      simp [flux, fullState, ChemistryLib.ReactionNetwork.massActionFlux,
        ChemistryLib.Complex.monomial, oregonatorModel,
        ChemistryLib.ReactionNetwork.reactant,
        show (Finset.univ : Finset Species) =
          {.Br, .Ce, .HBrO2, .BrO3, .HOBr} by rfl] <;> ring
  · simp [oregonatorModel]

/-- Internal stoichiometric matrix times the five-reaction flux vector. -/
noncomputable def vectorField (data : OregonatorSourceData) (p : Parameters)
    (x : InternalSpecies → ℝ) : InternalSpecies → ℝ :=
  Matrix.mulVec
    (ChemistryLib.Models.SBML.internalStoichiometricMatrix
      (oregonatorModel data) includeInternal p.f)
    (flux p x)

/-- Matrix form and all three coordinate equations of the Oregonator ODE. -/
theorem vectorField_spec : ∀ (data : OregonatorSourceData) (p : Parameters)
    (x : InternalSpecies → ℝ),
    vectorField data p x = Matrix.mulVec
      (ChemistryLib.Models.SBML.internalStoichiometricMatrix
        (oregonatorModel data) includeInternal p.f)
      (flux p x) ∧
    vectorField data p x InternalSpecies.Br =
      -flux p x Reaction.R1 - flux p x Reaction.R2 +
        p.f * flux p x Reaction.R5 ∧
    vectorField data p x InternalSpecies.Ce =
      flux p x Reaction.R3 - flux p x Reaction.R5 ∧
    vectorField data p x InternalSpecies.HBrO2 =
      flux p x Reaction.R1 - flux p x Reaction.R2 + flux p x Reaction.R3 -
        2 * flux p x Reaction.R4 := by
  intro data p x
  have hstoich := (oregonatorModel_spec data p.f).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [vectorField, Matrix.mulVec, dotProduct,
      ChemistryLib.Models.SBML.internalStoichiometricMatrix, includeInternal,
      hstoich, show (Finset.univ : Finset Reaction) =
        {.R1, .R2, .R3, .R4, .R5} by rfl]
    ring
  · simp [vectorField, Matrix.mulVec, dotProduct,
      ChemistryLib.Models.SBML.internalStoichiometricMatrix, includeInternal,
      hstoich, show (Finset.univ : Finset Reaction) =
        {.R1, .R2, .R3, .R4, .R5} by rfl]
    ring
  · simp [vectorField, Matrix.mulVec, dotProduct,
      ChemistryLib.Models.SBML.internalStoichiometricMatrix, includeInternal,
      hstoich, show (Finset.univ : Finset Reaction) =
        {.R1, .R2, .R3, .R4, .R5} by rfl]
    ring

end ChemistryLib.Models.Oregonator
