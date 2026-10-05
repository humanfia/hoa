import QITBench.Base
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Dimension of the antisymmetric subspace of three copies

This file models `ℋ^{⊗ 3}` as the algebraic tensor product indexed by `Fin 3`.
For a finite-dimensional Hilbert space this has the same vector-space
dimension as the completed Hilbert tensor product.
-/

open scoped TensorProduct
open PiTensorProduct

namespace QITFormalized.DimensionAntisymmetricSubspaceThreeCopies

/-- The threefold tensor product `H ⊗ H ⊗ H`, with its factors indexed by
`Fin 3`. -/
abbrev TripleTensor (H : Type*) [AddCommGroup H] [Module ℂ H] :=
  ⨂[ℂ] _ : Fin 3, H

/-- The natural action `W^π` of a permutation of the three tensor factors.
On a pure tensor with factors `v i`, the resulting factor at `i` is
`v (π⁻¹ i)`. -/
noncomputable def permuteTensorFactors
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    (π : Equiv.Perm (Fin 3)) :
    TripleTensor H ≃ₗ[ℂ] TripleTensor H :=
  PiTensorProduct.reindex ℂ (fun _ : Fin 3 => H) π

/-- The third antisymmetric tensor power:
the simultaneous sign eigenspace for every permutation in `S₃`. -/
noncomputable def antisymmetricSubspaceThree
    (H : Type*) [AddCommGroup H] [Module ℂ H] :
    Submodule ℂ (TripleTensor H) where
  carrier := {ψ | ∀ π : Equiv.Perm (Fin 3),
    permuteTensorFactors H π ψ = ((π.sign : ℤˣ) : ℂ) • ψ}
  zero_mem' := by
    simp
  add_mem' := by
    intro x y hx hy π
    simp only [map_add, hx π, hy π, smul_add]
  smul_mem' := by
    intro c x hx π
    simp only [map_smul, hx π, smul_smul]
    rw [mul_comm]

/-- Membership in the antisymmetric subspace is exactly the sign-eigenvector
condition from the source statement. -/
theorem mem_antisymmetricSubspaceThree_iff
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    (ψ : TripleTensor H) :
    ψ ∈ antisymmetricSubspaceThree H ↔
      ∀ π : Equiv.Perm (Fin 3),
        permuteTensorFactors H π ψ = ((π.sign : ℤˣ) : ℂ) • ψ :=
  Iff.rfl

/- The exterior cube maps to the tensor cube by antisymmetrization.  The next
few lemmas show that, over `ℂ`, this identifies the exterior cube with the
simultaneous sign eigenspace used in the statement. -/

private noncomputable def tensorToExterior
    (H : Type*) [AddCommGroup H] [Module ℂ H] :
    TripleTensor H →ₗ[ℂ] ⋀[ℂ]^3 H :=
  PiTensorProduct.lift (exteriorPower.ιMulti ℂ 3).toMultilinearMap

private theorem tensorToExterior_comp_toTensorPower
    (H : Type*) [AddCommGroup H] [Module ℂ H] :
    (tensorToExterior H).comp (exteriorPower.toTensorPower ℂ H 3) =
      (6 : ℂ) • LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.toTensorPower_apply_ιMulti, map_sum,
    tensorToExterior, LinearMap.smul_apply, LinearMap.id_apply,
    Units.smul_def, map_zsmul, PiTensorProduct.lift.tprod]
  change (∑ x : Equiv.Perm (Fin 3), (x.sign : ℤ) •
      (exteriorPower.ιMulti ℂ 3) (v ∘ x)) =
    (6 : ℂ) • (exteriorPower.ιMulti ℂ 3) v
  simp_rw [(exteriorPower.ιMulti ℂ 3).map_perm v]
  simp [Units.smul_def, smul_smul, Fintype.card_perm]
  exact (Nat.cast_smul_eq_nsmul ℂ 6 ((exteriorPower.ιMulti ℂ 3) v)).symm

private theorem toTensorPower_mem_antisymmetricSubspaceThree
    (H : Type*) [AddCommGroup H] [Module ℂ H] (x : ⋀[ℂ]^3 H) :
    exteriorPower.toTensorPower ℂ H 3 x ∈ antisymmetricSubspaceThree H := by
  intro π
  change PiTensorProduct.reindex ℂ (fun _ : Fin 3 => H) π
      (exteriorPower.toTensorPower ℂ H 3 x) =
    ((π.sign : ℤˣ) : ℂ) • exteriorPower.toTensorPower ℂ H 3 x
  have hmaps :
      (PiTensorProduct.reindex ℂ (fun _ : Fin 3 => H) π).toLinearMap.comp
          (exteriorPower.toTensorPower ℂ H 3) =
        ((π.sign : ℤˣ) : ℂ) • exteriorPower.toTensorPower ℂ H 3 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
    simp [exteriorPower.toTensorPower_apply_ιMulti, PiTensorProduct.reindex_tprod]
    rw [Finset.smul_sum]
    apply Fintype.sum_equiv (Equiv.mulRight π.symm)
    intro σ
    simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm,
      Equiv.Perm.mul_apply]
    rcases Int.units_eq_one_or π.sign with hp | hp <;> simp [hp]
  exact LinearMap.congr_fun hmaps x

private theorem toTensorPower_tensorToExterior_of_mem
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    (x : TripleTensor H) (hx : x ∈ antisymmetricSubspaceThree H) :
    exteriorPower.toTensorPower ℂ H 3 (tensorToExterior H x) = (6 : ℂ) • x := by
  change (∀ π : Equiv.Perm (Fin 3),
    permuteTensorFactors H π x = ((π.sign : ℤˣ) : ℂ) • x) at hx
  have hprojector :
      (exteriorPower.toTensorPower ℂ H 3).comp (tensorToExterior H) =
        ∑ π : Equiv.Perm (Fin 3),
          (((π.sign : ℤˣ) : ℂ) • (permuteTensorFactors H π).toLinearMap) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp [tensorToExterior, exteriorPower.toTensorPower_apply_ιMulti,
      permuteTensorFactors, PiTensorProduct.reindex_tprod]
    apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin 3)))
    intro σ
    simp [Equiv.Perm.inv_def, Equiv.Perm.sign_symm, Units.smul_def,
      Int.cast_smul_eq_zsmul]
  rw [← LinearMap.comp_apply, hprojector]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe]
  simp_rw [hx]
  simp only [smul_smul]
  have hsign (π : Equiv.Perm (Fin 3)) :
      (((π.sign : ℤˣ) : ℂ) * ((π.sign : ℤˣ) : ℂ)) = 1 := by
    norm_cast
    exact congrArg Units.val (Int.units_mul_self π.sign)
  simp_rw [hsign, one_smul]
  simp [Fintype.card_perm]
  exact (Nat.cast_smul_eq_nsmul ℂ 6 x).symm

private noncomputable def exteriorPowerEquivAntisymmetricSubspaceThree
    (H : Type*) [AddCommGroup H] [Module ℂ H] :
    (⋀[ℂ]^3 H) ≃ₗ[ℂ] antisymmetricSubspaceThree H := by
  let f : (⋀[ℂ]^3 H) →ₗ[ℂ] antisymmetricSubspaceThree H :=
    (exteriorPower.toTensorPower ℂ H 3).codRestrict
      (antisymmetricSubspaceThree H) (toTensorPower_mem_antisymmetricSubspaceThree H)
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply smul_right_injective (⋀[ℂ]^3 H) (by norm_num : (6 : ℂ) ≠ 0)
    have hcomp := tensorToExterior_comp_toTensorPower H
    calc
      (6 : ℂ) • x = tensorToExterior H (exteriorPower.toTensorPower ℂ H 3 x) := by
        simpa using (LinearMap.congr_fun hcomp x).symm
      _ = tensorToExterior H (exteriorPower.toTensorPower ℂ H 3 y) :=
        congrArg (tensorToExterior H) (congrArg Subtype.val hxy)
      _ = (6 : ℂ) • y := by
        simpa using LinearMap.congr_fun hcomp y
  · intro x
    refine ⟨(6 : ℂ)⁻¹ • tensorToExterior H x.1, ?_⟩
    apply Subtype.ext
    change exteriorPower.toTensorPower ℂ H 3
        ((6 : ℂ)⁻¹ • tensorToExterior H x.1) = x.1
    rw [map_smul, toTensorPower_tensorToExterior_of_mem H x.1 x.2, smul_smul]
    norm_num

/-- If `H` is a `d`-dimensional complex Hilbert space, then its third
antisymmetric tensor power has dimension `d choose 3`, equivalently
`d(d-1)(d-2)/6`. -/
theorem finrank_antisymmetricSubspaceThree
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (d : ℕ) (h_dim : Module.finrank ℂ H = d) :
    Module.finrank ℂ (antisymmetricSubspaceThree H) = Nat.choose d 3 ∧
      Nat.choose d 3 = d * (d - 1) * (d - 2) / 6 := by
  constructor
  · rw [← h_dim, ← exteriorPower.finrank_eq (R := ℂ) (M := H) (n := 3)]
    exact (exteriorPowerEquivAntisymmetricSubspaceThree H).finrank_eq.symm
  · rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
    congr 1
    ac_rfl

end QITFormalized.DimensionAntisymmetricSubspaceThreeCopies
