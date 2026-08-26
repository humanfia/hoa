import ChemistryLib.Models.Oregonator.ODE
import Physlib.Mathematics.FDerivCurry

/-!
# Oregonator equilibria and Jacobians

This module defines equilibria by vanishing of the authenticated, unscaled
Oregonator `vectorField` and represents its Mathlib Frechet derivative as a
coordinate matrix.  It also exposes the parameter/state derivative splitting
through the admitted `Physlib.Mathematics.FDerivCurry` adapter.

The kinetic laws and internal vector-field identity are grounded in BioModels
model `BIOMD0000000040`, `Reaction1`--`Reaction5`; the cited raw SBML artifact
has SHA-256
`0bf2abb25229f3fe7979315139396f9c0bcdb06370ae9c835f7d3fc0e0c79c6a`.
The derivative-layer contract is
`corpus.research_contracts:autocatalysis.oscillation Oregonator derivative
layer`.
-/

noncomputable section

namespace ChemistryLib.Models.Oregonator

/-- An equilibrium is a state at which the reused Oregonator vector field
vanishes. -/
def IsEquilibrium (data : OregonatorSourceData) (p : Parameters)
    (x : InternalSpecies → ℝ) : Prop :=
  vectorField data p x = 0

/-- The Oregonator vector field along a real-parameterized family of empirical
parameters, without any rescaling of state or time. -/
def parameterizedVectorField (data : OregonatorSourceData)
    (p : ℝ → Parameters) (μ : ℝ) (x : InternalSpecies → ℝ) :
    InternalSpecies → ℝ :=
  vectorField data (p μ) x

/-- The coordinate matrix of the Mathlib Frechet derivative of the reused
Oregonator vector field. -/
def jacobian (data : OregonatorSourceData) (p : Parameters)
    (x : InternalSpecies → ℝ) : Matrix InternalSpecies InternalSpecies ℝ :=
  fun i j ↦ fderiv ℝ (vectorField data p) x (Pi.single j 1) i

/-- Each Jacobian entry is the corresponding coordinate of the Frechet
derivative applied to a standard basis vector. -/
theorem jacobian_apply : ∀ (data : OregonatorSourceData) (p : Parameters)
    (x : InternalSpecies → ℝ) (i j : InternalSpecies),
    jacobian data p x i j =
      fderiv ℝ (vectorField data p) x (Pi.single j 1) i := by
  intro data p x i j
  rfl

/-- Evidence that a proposed matrix represents a genuine Frechet derivative
of the authenticated Oregonator vector field at the specified state. -/
structure OregonatorJacobianCertificate (data : OregonatorSourceData)
    (p : Parameters) (x : InternalSpecies → ℝ)
    (J : Matrix InternalSpecies InternalSpecies ℝ) : Type where
  linearization :
    (InternalSpecies → ℝ) →L[ℝ] (InternalSpecies → ℝ)
  isDerivative : HasFDerivAt (vectorField data p) linearization x
  represents : J = fun i j ↦ linearization (Pi.single j 1) i

namespace OregonatorJacobianCertificate

/-- The certified linearization is the Frechet derivative of the Oregonator
vector field at the certified state. -/
theorem hasFDerivAt : ∀ {data : OregonatorSourceData} {p : Parameters}
    {x : InternalSpecies → ℝ}
    {J : Matrix InternalSpecies InternalSpecies ℝ}
    (c : OregonatorJacobianCertificate data p x J),
    HasFDerivAt (vectorField data p) c.linearization x := by
  intro data p x J c
  exact c.isDerivative

/-- A certified coordinate matrix is the canonical Jacobian. -/
theorem jacobian_eq : ∀ {data : OregonatorSourceData} {p : Parameters}
    {x : InternalSpecies → ℝ}
    {J : Matrix InternalSpecies InternalSpecies ℝ}
    (c : OregonatorJacobianCertificate data p x J),
    J = jacobian data p x := by
  intro data p x J c
  ext i j
  calc
    J i j = c.linearization (Pi.single j 1) i := by
      exact congrFun (congrFun c.represents i) j
    _ = fderiv ℝ (vectorField data p) x (Pi.single j 1) i := by
      rw [c.isDerivative.fderiv]
    _ = jacobian data p x i j := by
      rfl

end OregonatorJacobianCertificate

/-- The parameter-direction derivative of the curried field agrees with the
joint derivative in the parameter direction. -/
theorem fderiv_curry_fst_parameterizedVectorField :
    ∀ (data : OregonatorSourceData) (p : ℝ → Parameters) (μ dμ : ℝ)
      (x : InternalSpecies → ℝ),
      DifferentiableAt ℝ (Function.uncurry (parameterizedVectorField data p))
          (μ, x) →
        fderiv ℝ (fun q ↦ parameterizedVectorField data p q x) μ dμ =
          fderiv ℝ (Function.uncurry (parameterizedVectorField data p))
            (μ, x) (dμ, 0) := by
  intro data p μ dμ x h
  exact fderiv_curry_fst
    (Function.uncurry (parameterizedVectorField data p)) μ x h dμ

/-- The state-direction derivative of the curried field agrees with the joint
derivative in the state direction. -/
theorem fderiv_curry_snd_parameterizedVectorField :
    ∀ (data : OregonatorSourceData) (p : ℝ → Parameters) (μ : ℝ)
      (x dx : InternalSpecies → ℝ),
      DifferentiableAt ℝ (Function.uncurry (parameterizedVectorField data p))
          (μ, x) →
        fderiv ℝ (parameterizedVectorField data p μ) x dx =
          fderiv ℝ (Function.uncurry (parameterizedVectorField data p))
            (μ, x) (0, dx) := by
  intro data p μ x dx h
  exact fderiv_curry_snd
    (Function.uncurry (parameterizedVectorField data p)) μ x h dx

/-- The joint derivative is the sum of its parameter and state directional
parts. -/
theorem fderiv_uncurry_parameterizedVectorField :
    ∀ (data : OregonatorSourceData) (p : ℝ → Parameters) (μ dμ : ℝ)
      (x dx : InternalSpecies → ℝ),
      DifferentiableAt ℝ (Function.uncurry (parameterizedVectorField data p))
          (μ, x) →
        fderiv ℝ (Function.uncurry (parameterizedVectorField data p))
            (μ, x) (dμ, dx) =
          fderiv ℝ (fun q ↦ parameterizedVectorField data p q x) μ dμ +
            fderiv ℝ (parameterizedVectorField data p μ) x dx := by
  intro data p μ dμ x dx h
  exact fderiv_uncurry (parameterizedVectorField data p) (μ, x) (dμ, dx) h

/-- The joint Frechet derivative splits as the sum of the parameter and state
derivatives composed with the product projections. -/
theorem fderiv_wrt_prod_parameterizedVectorField :
    ∀ (data : OregonatorSourceData) (p : ℝ → Parameters) (μ : ℝ)
      (x : InternalSpecies → ℝ),
      DifferentiableAt ℝ (Function.uncurry (parameterizedVectorField data p))
          (μ, x) →
        fderiv ℝ (Function.uncurry (parameterizedVectorField data p)) (μ, x) =
          (fderiv ℝ (fun q ↦ parameterizedVectorField data p q x) μ).comp
              (ContinuousLinearMap.fst ℝ ℝ (InternalSpecies → ℝ)) +
            (fderiv ℝ (parameterizedVectorField data p μ) x).comp
              (ContinuousLinearMap.snd ℝ ℝ (InternalSpecies → ℝ)) := by
  intro data p μ x h
  exact fderiv_wrt_prod h

end ChemistryLib.Models.Oregonator
