import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Finite-state jump-rate generators

This module defines an algebraic jump-rate kernel and its finite-state
generator.  It follows ACK-2010, Section 3.1, equations (3.1)--(3.5), as
recorded by source artifact
`222b8bed89ef875d89943a8634560dc29758ab803d5ad7054cb639fe21280c3c` and the
sanitized research contract `research:ack_2010:ctmc_generator`.

The interface is purely algebraic: it constructs no stochastic process and
makes no nonexplosion or long-time claims.
-/

open scoped BigOperators

namespace ChemistryLib.Stochastic

/-- A real-valued kernel on ordered pairs of states. -/
abbrev RateKernel (State : Type) : Type := State → State → ℝ

/-- A kernel is a jump-rate kernel when every off-diagonal rate is
nonnegative. -/
def IsJumpRateKernel {State : Type} (q : RateKernel State) : Prop :=
  ∀ x y, x ≠ y → 0 ≤ q x y

/-- The algebraic generator associated with a finite-state rate kernel. -/
def generator {State : Type} [Fintype State]
    (q : RateKernel State) (f : State → ℝ) (x : State) : ℝ :=
  ∑ y, q x y * (f y - f x)

end ChemistryLib.Stochastic
