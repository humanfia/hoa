import QITBench.Base
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Dimension of the symmetric subspace of three copies

For a finite-dimensional complex Hilbert space `H`, this file models
`H^{⊗3}` by a pi tensor product indexed by `Fin 3`.  A permutation
`π : Equiv.Perm (Fin 3)` acts by the canonical reindexing equivalence.
The symmetric subspace consists of the vectors fixed by every such
permutation.
-/

open scoped TensorProduct

universe u

namespace QITFormalized.DimensionSymmetricSubspaceThreeCopies

/-- The algebraic three-fold tensor power of `H`, indexed by the three copies. -/
abbrev TensorCube (H : Type u) [AddCommGroup H] [Module ℂ H] : Type u :=
  PiTensorProduct ℂ (fun _ : Fin 3 => H)

/-- The canonical action `W^π` which permutes the three tensor factors. -/
def tensorPermutation (H : Type u) [AddCommGroup H] [Module ℂ H]
    (π : Equiv.Perm (Fin 3)) : TensorCube H ≃ₗ[ℂ] TensorCube H :=
  PiTensorProduct.reindex ℂ (fun _ : Fin 3 => H) π

/-- The subspace of `H^{⊗3}` fixed by every permutation of its three factors. -/
noncomputable def symmetricSubspaceThreeCopies
    (H : Type u) [AddCommGroup H] [Module ℂ H] :
    Submodule ℂ (TensorCube H) :=
  ⨅ π : Equiv.Perm (Fin 3),
    LinearMap.ker
      ((tensorPermutation H π).toLinearMap -
        (LinearMap.id : TensorCube H →ₗ[ℂ] TensorCube H))

/-- Membership in the symmetric subspace is exactly invariance under all of `S₃`. -/
theorem mem_symmetricSubspaceThreeCopies_iff
    (H : Type u) [AddCommGroup H] [Module ℂ H] (ψ : TensorCube H) :
    ψ ∈ symmetricSubspaceThreeCopies H ↔
      ∀ π : Equiv.Perm (Fin 3), tensorPermutation H π ψ = ψ := by
  simp [symmetricSubspaceThreeCopies, LinearMap.mem_ker, sub_eq_zero]

/--
If `H` has complex dimension `d`, then its three-copy symmetric subspace has
dimension `choose (d + 2) 3 = d(d+1)(d+2)/6`.
-/
theorem finrank_symmetricSubspaceThreeCopies
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (d : ℕ) (hd : Module.finrank ℂ H = d) :
    Module.finrank ℂ (symmetricSubspaceThreeCopies H) = Nat.choose (d + 2) 3 ∧
      Nat.choose (d + 2) 3 = d * (d + 1) * (d + 2) / 6 := by
  classical
  letI : DecidableEq (Fin 3 → Fin d) := Classical.decEq _
  let b : Module.Basis (Fin d) ℂ H := Module.finBasisOfFinrankEq ℂ H hd
  let tb : Module.Basis (Fin 3 → Fin d) ℂ (TensorCube H) :=
    Basis.piTensorProduct (fun _ : Fin 3 => b)
  let e : TensorCube H ≃ₗ[ℂ] (Fin 3 → Fin d) → ℂ :=
    tb.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 3 → Fin d)

  have hcoord (π : Equiv.Perm (Fin 3)) (x : TensorCube H) (a : Fin 3 → Fin d) :
      e (tensorPermutation H π x) a = e x (a ∘ π) := by
    have hmaps :
        (LinearMap.proj a).comp
            (e.toLinearMap.comp (tensorPermutation H π).toLinearMap) =
          (LinearMap.proj (a ∘ π)).comp e.toLinearMap := by
      apply tb.ext
      intro q
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e, LinearEquiv.trans_apply,
        tb, Basis.piTensorProduct_apply, tensorPermutation,
        PiTensorProduct.reindex_tprod]
      rw [← Basis.piTensorProduct_apply, ← Basis.piTensorProduct_apply]
      simp only [Module.Basis.repr_self]
      change
        Pi.single (M := fun _ : (Fin 3 → Fin d) => ℂ)
              (fun i => q (π.symm i)) 1 a =
          Pi.single (M := fun _ : (Fin 3 → Fin d) => ℂ) q 1 (a ∘ π)
      by_cases hqa : (fun i => q (π.symm i)) = a
      · have hq : q = a ∘ π := by
          funext i
          simpa [Function.comp_def] using congr_fun hqa (π i)
        rw [hqa, hq, Pi.single_eq_same, Pi.single_eq_same]
      · have hq : q ≠ a ∘ π := by
          intro h
          apply hqa
          funext i
          simpa [Function.comp_def] using congr_fun h (π.symm i)
        exact
          (Pi.single_eq_of_ne
              (M := fun _ : (Fin 3 → Fin d) => ℂ) (Ne.symm hqa) 1).trans
            (Pi.single_eq_of_ne
              (M := fun _ : (Fin 3 → Fin d) => ℂ) (Ne.symm hq) 1).symm
    exact LinearMap.congr_fun hmaps x

  let SortedTriples := {a : Fin 3 → Fin d // Monotone a}
  let restrict :
      symmetricSubspaceThreeCopies H →ₗ[ℂ] SortedTriples → ℂ :=
    { toFun := fun x a => e x.1 a.1
      map_add' := by
        intro x y
        funext a
        simp
      map_smul' := by
        intro r x
        funext a
        simp }

  have hfix (x : symmetricSubspaceThreeCopies H) (π : Equiv.Perm (Fin 3)) :
      tensorPermutation H π x.1 = x.1 :=
    (mem_symmetricSubspaceThreeCopies_iff H x.1).mp x.2 π

  have hrestrict_injective : Function.Injective restrict := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    funext a
    let sa : SortedTriples := ⟨a ∘ Tuple.sort a, Tuple.monotone_sort a⟩
    have hxsort : e x.1 a = e x.1 (a ∘ Tuple.sort a) := by
      rw [← hcoord (Tuple.sort a) x.1 a, hfix x (Tuple.sort a)]
    have hysort : e y.1 a = e y.1 (a ∘ Tuple.sort a) := by
      rw [← hcoord (Tuple.sort a) y.1 a, hfix y (Tuple.sort a)]
    calc
      e x.1 a = e x.1 (a ∘ Tuple.sort a) := hxsort
      _ = restrict x sa := rfl
      _ = restrict y sa := congr_fun hxy sa
      _ = e y.1 (a ∘ Tuple.sort a) := rfl
      _ = e y.1 a := hysort.symm

  have hrestrict_surjective : Function.Surjective restrict := by
    intro z
    let coeff : (Fin 3 → Fin d) → ℂ :=
      fun a => z ⟨a ∘ Tuple.sort a, Tuple.monotone_sort a⟩
    let x₀ : TensorCube H := e.symm coeff
    have hx₀ : x₀ ∈ symmetricSubspaceThreeCopies H := by
      rw [mem_symmetricSubspaceThreeCopies_iff]
      intro π
      apply e.injective
      funext a
      rw [hcoord]
      simp only [x₀, LinearEquiv.apply_symm_apply, coeff]
      apply congr_arg z
      apply Subtype.ext
      exact Tuple.comp_perm_comp_sort_eq_comp_sort
    let x : symmetricSubspaceThreeCopies H := ⟨x₀, hx₀⟩
    refine ⟨x, ?_⟩
    funext s
    change e x₀ s.1 = z s
    rw [show e x₀ = coeff by simp [x₀]]
    change z ⟨s.1 ∘ Tuple.sort s.1, Tuple.monotone_sort s.1⟩ = z s
    apply congr_arg z
    apply Subtype.ext
    change s.1 ∘ Tuple.sort s.1 = s.1
    rw [(Tuple.sort_eq_refl_iff_monotone).2 s.2]
    rfl

  let invariantEquiv :
      symmetricSubspaceThreeCopies H ≃ₗ[ℂ] SortedTriples → ℂ :=
    LinearEquiv.ofBijective restrict ⟨hrestrict_injective, hrestrict_surjective⟩
  have hfinrank :
      Module.finrank ℂ (symmetricSubspaceThreeCopies H) =
        Fintype.card SortedTriples := by
    calc
      Module.finrank ℂ (symmetricSubspaceThreeCopies H) =
          Module.finrank ℂ (SortedTriples → ℂ) :=
        invariantEquiv.finrank_eq
      _ = Fintype.card SortedTriples :=
        Module.finrank_fintype_fun_eq_card ℂ

  let q : (Fin 3 → Fin d) → Sym (Fin d) 3 :=
    fun a => (List.Vector.ofFn a : Sym (Fin d) 3)
  have hq_perm (a : Fin 3 → Fin d) (π : Equiv.Perm (Fin 3)) :
      q (a ∘ π) = q a := by
    apply Sym.sound
    simpa [q, List.Vector.toList_ofFn] using π.ofFn_comp_perm a
  have hq_injective :
      Function.Injective (fun a : SortedTriples => q a.1) := by
    intro a c hac
    apply Subtype.ext
    apply List.ofFn_injective
    have hm :
        (↑(List.ofFn a.1) : Multiset (Fin d)) = ↑(List.ofFn c.1) := by
      exact congrArg Sym.toMultiset hac
    have hp : List.Perm (List.ofFn a.1) (List.ofFn c.1) :=
      Quotient.exact hm
    exact
      hp.eq_of_pairwise' a.2.sortedLE_ofFn.pairwise c.2.sortedLE_ofFn.pairwise
  have hq_surjective :
      Function.Surjective (fun a : SortedTriples => q a.1) := by
    intro s
    obtain ⟨l, hl⟩ := Quotient.exists_rep s.val
    have hlen : l.length = 3 := by
      have hc := congrArg Multiset.card hl
      simpa using hc.trans s.property
    let v : List.Vector (Fin d) 3 := ⟨l, hlen⟩
    let a : Fin 3 → Fin d := List.Vector.get v
    refine
      ⟨⟨a ∘ Tuple.sort a, Tuple.monotone_sort a⟩, ?_⟩
    calc
      q (a ∘ Tuple.sort a) = q a := hq_perm a (Tuple.sort a)
      _ = s := by
        apply Sym.ext
        change (↑(List.Vector.ofFn a).val : Multiset (Fin d)) = s.val
        rw [List.Vector.ofFn_get]
        exact hl
  let sortedEquiv : SortedTriples ≃ Sym (Fin d) 3 :=
    Equiv.ofBijective (fun a => q a.1) ⟨hq_injective, hq_surjective⟩
  have hcard : Fintype.card SortedTriples = Nat.choose (d + 2) 3 := by
    rw [Fintype.card_congr sortedEquiv, Sym.card_sym_eq_choose]
    simp

  constructor
  · exact hfinrank.trans hcard
  · rw [Nat.choose_eq_descFactorial_div_factorial]
    simp [Nat.descFactorial]
    congr 1
    ring

end QITFormalized.DimensionSymmetricSubspaceThreeCopies
