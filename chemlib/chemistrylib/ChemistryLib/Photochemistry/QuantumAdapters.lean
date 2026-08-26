import ChemistryLib.Units.ChemicalDimension
import Physlib.QuantumMechanics.QuantumSystem.Basic
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.QuantumMechanics.Hydrogen.Basic
import Physlib.CondensedMatter.TightBindingChain.Basic

/-!
# Quantum-mechanical adapters

This module provides deliberately narrow names for quantum-mechanical interfaces
already supplied by Physlib at commit
`1706ae68b63996f1d97717e672e50c9e3933d933`. Its capability sources are:

* hydrogen: `Physlib.QuantumMechanics.Hydrogen.Basic#QuantumMechanics.HydrogenAtom`
  and `Physlib.QuantumMechanics.QuantumSystem.Basic`;
* reduced Planck constant:
  `Physlib.QuantumMechanics.PlanckConstant#Constants.ℏ` and
  `Physlib.Units.Dimension`;
* tight binding:
  `Physlib.CondensedMatter.TightBindingChain.Basic#CondensedMatter.TightBindingChain.hamiltonian`
  and `Physlib.QuantumMechanics.QuantumSystem.Basic`.

No spectrum, Rydberg, or ab-initio electronic-structure claim is made here.
-/

namespace ChemistryLib.QuantumAdapters

noncomputable section

/-- Physlib's hydrogen-atom data, exposed without changing its semantics. -/
abbrev HydrogenAtom : Type := QuantumMechanics.HydrogenAtom

/-- Physlib's tight-binding-chain data. -/
abbrev TightBindingChain : Type := CondensedMatter.TightBindingChain

/-- The Hilbert space belonging to a Physlib tight-binding chain. -/
abbrev TightBindingHilbertSpace : CondensedMatter.TightBindingChain → Type :=
  CondensedMatter.TightBindingChain.HilbertSpace

/-- The Coulomb potential identity carried by a Physlib hydrogen atom. -/
theorem hydrogenPotential_eq : (H : QuantumMechanics.HydrogenAtom) →
    H.potential = fun x ↦ -H.k * ‖x‖⁻¹ :=
  QuantumMechanics.HydrogenAtom.potential_eq

/-- Physlib's positive reduced Planck constant. -/
abbrev reducedPlanckConstant : {x : ℝ // 0 < x} := Constants.ℏ

/-- Positivity is inherited from the subtype defining the Physlib constant. -/
theorem reducedPlanckConstant_pos : 0 < (reducedPlanckConstant : ℝ) :=
  reducedPlanckConstant.property

/-- Physlib's soft-core regularization of the hydrogen Hamiltonian. -/
def regularizedHydrogenHamiltonian (H : QuantumMechanics.HydrogenAtom) :
    ℝˣ → SchwartzMap (Space H.d) ℂ →L[ℂ] SchwartzMap (Space H.d) ℂ :=
  H.hamiltonianRegCLM

/-- The Hamiltonian of a Physlib tight-binding chain. -/
def tightBindingHamiltonian (T : CondensedMatter.TightBindingChain) :
    T.HilbertSpace →ₗ[ℂ] T.HilbertSpace :=
  T.hamiltonian

end

end ChemistryLib.QuantumAdapters
