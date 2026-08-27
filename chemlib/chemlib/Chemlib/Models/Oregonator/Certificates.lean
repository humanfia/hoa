import Chemlib.Dynamics.OscillationCertificate
import Chemlib.Models.Oregonator.Jacobian

/-!
# Exact Oregonator oscillation certificates

This module specializes exact spectral-crossing and periodic-orbit witnesses to
the authenticated, unscaled Oregonator `vectorField`.  The spectral certificate
stores equilibrium evidence separately from the local imaginary-eigenpair
crossing evidence; neither certificate infers an exact witness from numerical
data or asserts a Hopf bifurcation.

The vector field and the restriction against treating numerical trajectories as
exact oscillation certificates are grounded in
`BIOMODELS-BIOMD0000000040:five-flux vectorField specification and oscillation
scope guard`; the witness interface follows
`corpus.scope:autocatalysis.oscillation concrete-certificate contract`.
-/

namespace Chemlib.Models.Oregonator

/-- Exact equilibrium and local spectral-crossing evidence for an Oregonator
parameter family, kept as independent witness fields. -/
structure OregonatorImaginaryEigenpairCrossingCertificate
    (data : OregonatorSourceData) (p : ℝ → Parameters)
    (equilibrium : ℝ → InternalSpecies → ℝ) (μ₀ : ℝ) : Type where
  equilibriumWitness : ∀ μ : ℝ, IsEquilibrium data (p μ) (equilibrium μ)
  spectralWitness :
    Chemlib.Dynamics.ImaginaryEigenpairCrossingCertificate
      (fun μ ↦ jacobian data (p μ) (equilibrium μ)) μ₀

namespace OregonatorImaginaryEigenpairCrossingCertificate

/-- The stored local imaginary-eigenpair crossing certificate for the
Oregonator Jacobian family. -/
def crossing : ∀ {data : OregonatorSourceData} {p : ℝ → Parameters}
    {equilibrium : ℝ → InternalSpecies → ℝ} {μ₀ : ℝ}
    (c : OregonatorImaginaryEigenpairCrossingCertificate data p equilibrium μ₀),
    Chemlib.Dynamics.ImaginaryEigenpairCrossingCertificate
      (fun μ ↦ jacobian data (p μ) (equilibrium μ)) μ₀ := by
  intro data p equilibrium μ₀ c
  exact c.spectralWitness

/-- Every state in the certified family is an exact equilibrium of the
corresponding Oregonator vector field. -/
theorem equilibrium : ∀ {data : OregonatorSourceData} {p : ℝ → Parameters}
    {equilibrium : ℝ → InternalSpecies → ℝ} {μ₀ : ℝ}
    (c : OregonatorImaginaryEigenpairCrossingCertificate data p equilibrium μ₀)
    (μ : ℝ), IsEquilibrium data (p μ) (equilibrium μ) := by
  intro data p equilibrium μ₀ c μ
  exact c.equilibriumWitness μ

end OregonatorImaginaryEigenpairCrossingCertificate

/-- An exact periodic orbit of the reused Oregonator vector field, with no
state or time rescaling. -/
abbrev OregonatorPeriodicOrbitCertificate
    (data : OregonatorSourceData) (p : Parameters) : Type :=
  Chemlib.Dynamics.PeriodicOrbitCertificate (vectorField data p)

namespace OregonatorPeriodicOrbitCertificate

/-- The certified trajectory satisfies the original Oregonator vector field at
every time. -/
theorem vectorField_eq : ∀ {data : OregonatorSourceData} {p : Parameters}
    (c : OregonatorPeriodicOrbitCertificate data p) (t : ℝ),
    HasDerivAt c.trajectory (vectorField data p (c.trajectory t)) t := by
  intro data p c t
  exact c.satisfies_ode t

end OregonatorPeriodicOrbitCertificate

/-- Build an exact Oregonator periodic-orbit certificate directly from a
positive period, exact periodicity, nonconstancy, and pointwise ODE evidence. -/
def periodicOrbitCertificate_of_invariantCurve : ∀
    {data : OregonatorSourceData} {p : Parameters}
    {trajectory : ℝ → InternalSpecies → ℝ} {T : ℝ},
    0 < T →
    Function.Periodic trajectory T →
    (∃ t, trajectory t ≠ trajectory 0) →
    (∀ t, HasDerivAt trajectory (vectorField data p (trajectory t)) t) →
    OregonatorPeriodicOrbitCertificate data p := by
  intro data p trajectory T hT hPeriodic hNonconstant hODE
  exact {
    trajectory := trajectory
    period := T
    satisfies_ode := hODE
    period_positive := hT
    trajectory_nonconstant := by
      obtain ⟨t, ht⟩ := hNonconstant
      exact ⟨t, 0, ht⟩
    periodicity := hPeriodic
  }

end Chemlib.Models.Oregonator
