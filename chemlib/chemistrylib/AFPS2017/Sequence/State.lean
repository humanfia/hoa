import AFPS2017.Sequence.Residue
import ChemistryLib.Foundations.Amount

/-!
# Resin-bound sequence state

This module records the structural state used by the abstract solid-phase
sequence model. Resin loading and reactive-site amount reuse ChemistryLib's
dimensioned quantity and amount types; no empirical values are assigned here.

Source references:

* Sanitized sequence contract (`afps2017.sequence.contract:question`).
* Public Supplementary Information,
  SHA-256 `f7baa2cd59141ec38d95c9980e60117b596a9a78a9f4cbd4ae4e2cd4a2c8044e`
  (`afps2017.supplement`).
-/

namespace AFPS2017.Sequence

/-- Whether the growing chain's N terminus is protected or deprotected. -/
inductive NTerminalProtection : Type where
  | «protected»
  | deprotected

/-- The chemical dimension of amount of substance per unit mass. -/
def resinLoadingDimension : ChemistryLib.Units.ChemicalDimension :=
  ChemistryLib.Units.ChemicalDimension.amountOfSubstance /
    ChemistryLib.Units.ChemicalDimension.ofPhyslib _root_.Dimension.M𝓭

/-- A nonnegative resin loading with its chemical dimension tracked by the type. -/
abbrev ResinLoading : Type :=
  ChemistryLib.Units.NonnegativeQuantity resinLoadingDimension

/-- Forget the nonnegativity witness while retaining the resin-loading dimension. -/
def resinLoadingQuantity (loading : ResinLoading) :
    ChemistryLib.Units.Quantity resinLoadingDimension :=
  loading.1

/-- Structural state of a growing resin-bound chain, stored N-to-C. -/
structure ResinBoundState
    (Identity Chirality Protection Linker : Type) : Type where
  chainNToC : List (ResidueSpec Identity Chirality Protection)
  linker : Linker
  loading : ResinLoading
  nTerminalProtection : NTerminalProtection
  reactiveSiteAmount : ChemistryLib.Foundations.Amount

end AFPS2017.Sequence
