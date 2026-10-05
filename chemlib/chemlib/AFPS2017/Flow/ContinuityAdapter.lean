import Physlib.FluidDynamics.NavierStokes.Continuity

/-!
# Conditional continuity adapter

This module packages a supplied Physlib fluid state together with a supplied
smooth continuity certificate.  It does not assert that an AFPS reactor has
such a model or derive any reactor-performance conclusion.

Source basis:
* `afps2017.flow.protocol:question`
* `grounding:Physlib.FluidDynamics.NavierStokes.Continuity@1706ae68b63996f1d97717e672e50c9e3933d933`
-/

namespace AFPS2017.Flow

open FluidDynamics
open FluidDynamics.NavierStokes

/-- A fluid state equipped with a supplied smooth mass-continuity certificate. -/
structure ContinuumMassBalanceModel (d : Nat) where
  fluid : FluidState d
  smoothContinuity : SmoothContinuityEquation d fluid

namespace ContinuumMassBalanceModel

/-- Smooth continuity implies the classical continuity equation. -/
theorem classicalContinuity {d : Nat} (model : ContinuumMassBalanceModel d) :
    ClassicalContinuityEquation d model.fluid := by
  intro t x _ _
  exact model.smoothContinuity.2.2 t x

/-- The continuity residual of the packaged fluid state vanishes pointwise. -/
theorem residual_zero {d : Nat} (model : ContinuumMassBalanceModel d)
    (t : Time) (x : Space d) :
    continuityResidual d model.fluid t x = 0 :=
  model.smoothContinuity.2.2 t x

end ContinuumMassBalanceModel

end AFPS2017.Flow
