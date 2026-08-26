import Mathlib

/-!
# Exact certificates for oscillatory dynamics

This module separates two kinds of exact witness:

* `ImaginaryEigenpairCrossingCertificate` records only a local complex
  eigenpair branch through a positive-frequency imaginary eigenvalue, together
  with its transverse crossing.  In particular, it does not assert a Hopf
  bifurcation or the existence of a periodic orbit.
* `PeriodicOrbitCertificate` independently records a nonconstant periodic
  trajectory satisfying the supplied autonomous ODE at every time.

The distinction follows the Hopf spectral/transversality contract in
`corpus.research_contracts:autocatalysis.oscillation` and the periodic-orbit
separation and certificate contracts in
`corpus.scope:autocatalysis.oscillation`.  The requirement that numerical
trajectories alone do not certify oscillation is the scope guard from
`BIOMODELS-BIOMD0000000040:oscillation`.
-/

namespace ChemistryLib.Dynamics

/--
An exact witness that a local eigenpair branch of a real matrix family crosses
the imaginary axis transversely at `μ₀`.

This is deliberately weaker than a Hopf-bifurcation certificate: it contains
no simplicity, spectral-isolation, nonlinear nondegeneracy, or periodic-orbit
claim.
-/
structure ImaginaryEigenpairCrossingCertificate {Index : Type}
    [Fintype Index] [DecidableEq Index]
    (J : ℝ → Matrix Index Index ℝ) (μ₀ : ℝ) : Type where
  /-- The locally certified complex eigenvalue branch. -/
  eigenvalue : ℝ → ℂ
  /-- A complex eigenvector branch for the real matrix family. -/
  eigenvector : ℝ → Index → ℂ
  /-- The derivative of `eigenvalue` at the critical parameter. -/
  eigenvalueDerivative : ℂ
  /-- The positive imaginary frequency at the critical parameter. -/
  frequency : ℝ
  /-- An open parameter neighborhood on which the eigenpair is certified. -/
  neighborhood : Set ℝ
  neighborhood_isOpen : IsOpen neighborhood
  critical_mem_neighborhood : μ₀ ∈ neighborhood
  eigenpair_on_neighborhood : ∀ μ ∈ neighborhood,
    eigenvector μ ≠ 0 ∧
      Matrix.mulVec ((J μ).map Complex.ofReal) (eigenvector μ) =
        eigenvalue μ • eigenvector μ
  critical_value_eq : eigenvalue μ₀ = Complex.I * frequency
  eigenvalue_derivative_at : HasDerivAt eigenvalue eigenvalueDerivative μ₀
  frequency_positive : 0 < frequency
  transverse_crossing : eigenvalueDerivative.re ≠ 0

namespace ImaginaryEigenpairCrossingCertificate

theorem atCritical_eigenpair {Index : Type} [Fintype Index] [DecidableEq Index]
    {J : ℝ → Matrix Index Index ℝ} {μ₀ : ℝ}
    (c : ImaginaryEigenpairCrossingCertificate J μ₀) :
    c.eigenvector μ₀ ≠ 0 ∧
      Matrix.mulVec ((J μ₀).map Complex.ofReal) (c.eigenvector μ₀) =
        c.eigenvalue μ₀ • c.eigenvector μ₀ :=
  c.eigenpair_on_neighborhood μ₀ c.critical_mem_neighborhood

theorem critical_eigenvalue {Index : Type} [Fintype Index] [DecidableEq Index]
    {J : ℝ → Matrix Index Index ℝ} {μ₀ : ℝ}
    (c : ImaginaryEigenpairCrossingCertificate J μ₀) :
    c.eigenvalue μ₀ = Complex.I * c.frequency :=
  c.critical_value_eq

theorem eigenvalue_hasDerivAt {Index : Type} [Fintype Index] [DecidableEq Index]
    {J : ℝ → Matrix Index Index ℝ} {μ₀ : ℝ}
    (c : ImaginaryEigenpairCrossingCertificate J μ₀) :
    HasDerivAt c.eigenvalue c.eigenvalueDerivative μ₀ :=
  c.eigenvalue_derivative_at

theorem frequency_pos {Index : Type} [Fintype Index] [DecidableEq Index]
    {J : ℝ → Matrix Index Index ℝ} {μ₀ : ℝ}
    (c : ImaginaryEigenpairCrossingCertificate J μ₀) :
    0 < c.frequency :=
  c.frequency_positive

theorem local_eigenpair_branch {Index : Type} [Fintype Index] [DecidableEq Index]
    {J : ℝ → Matrix Index Index ℝ} {μ₀ : ℝ}
    (c : ImaginaryEigenpairCrossingCertificate J μ₀) :
    ∃ U : Set ℝ, IsOpen U ∧ μ₀ ∈ U ∧ ∀ μ ∈ U,
      c.eigenvector μ ≠ 0 ∧
        Matrix.mulVec ((J μ).map Complex.ofReal) (c.eigenvector μ) =
          c.eigenvalue μ • c.eigenvector μ :=
  ⟨c.neighborhood, c.neighborhood_isOpen, c.critical_mem_neighborhood,
    c.eigenpair_on_neighborhood⟩

theorem transverse {Index : Type} [Fintype Index] [DecidableEq Index]
    {J : ℝ → Matrix Index Index ℝ} {μ₀ : ℝ}
    (c : ImaginaryEigenpairCrossingCertificate J μ₀) :
    c.eigenvalueDerivative.re ≠ 0 :=
  c.transverse_crossing

end ImaginaryEigenpairCrossingCertificate

/--
An exact nonconstant periodic orbit of the autonomous vector field `F`.

The certificate stores the ODE identity at every time, positivity of the
period, nonconstancy, and exact periodicity; a sampled or numerical trajectory
does not supply these fields.
-/
structure PeriodicOrbitCertificate {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : E → E) : Type where
  trajectory : ℝ → E
  period : ℝ
  satisfies_ode : ∀ t : ℝ, HasDerivAt trajectory (F (trajectory t)) t
  period_positive : 0 < period
  trajectory_nonconstant : ∃ t₁ t₂ : ℝ, trajectory t₁ ≠ trajectory t₂
  periodicity : Function.Periodic trajectory period

namespace PeriodicOrbitCertificate

theorem hasDerivAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} (c : PeriodicOrbitCertificate F) (t : ℝ) :
    HasDerivAt c.trajectory (F (c.trajectory t)) t :=
  c.satisfies_ode t

theorem isPeriodic {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} (c : PeriodicOrbitCertificate F) :
    Function.Periodic c.trajectory c.period :=
  c.periodicity

end PeriodicOrbitCertificate

end ChemistryLib.Dynamics
