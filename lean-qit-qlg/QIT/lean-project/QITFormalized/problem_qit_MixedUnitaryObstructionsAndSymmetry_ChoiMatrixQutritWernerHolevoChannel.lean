import QITBench.Base

/-!
# Choi matrix of the qutrit Werner--Holevo map

This file uses the unnormalized Choi convention from `QITBench.MatrixMap.choi`.
The qutrit Hilbert space is represented in its standard basis by `Fin 3`, so
operators are complex matrices indexed by `Fin 3`.
-/

open scoped ComplexOrder MatrixOrder

namespace QITFormalized.ChoiMatrixQutritWernerHolevoChannel

open QITBench

noncomputable section

/-- The standard basis label type for the Hilbert space `ℂ³`. -/
abbrev Qutrit := Fin 3

/-- The coordinate vector of the pure tensor `x ⊗ y`. -/
def tensorKet (x y : Qutrit → ℂ) : Qutrit × Qutrit → ℂ :=
  fun ij => x ij.1 * y ij.2

/-- The swap operator on `ℂ³ ⊗ ℂ³`, written in the standard product basis. -/
def qutritSwap : CMatrix (Qutrit × Qutrit) :=
  fun ij kl => if ij = (kl.2, kl.1) then 1 else 0

/-- The swap operator interchanges the two factors of every pure tensor. -/
theorem qutritSwap_mulVec_tensorKet (x y : Qutrit → ℂ) :
    Matrix.mulVec qutritSwap (tensorKet x y) = tensorKet y x := by
  ext ⟨i, j⟩
  classical
  rw [show (Matrix.mulVec qutritSwap (tensorKet x y)) (i, j) =
      ∑ kl, qutritSwap (i, j) kl * tensorKet x y kl by rfl]
  rw [Finset.sum_eq_single (j, i)]
  · simp [qutritSwap, tensorKet, mul_comm]
  · intro b hb hne
    have hswap : (i, j) ≠ (b.2, b.1) := by
      intro h
      apply hne
      exact Prod.ext (congrArg Prod.snd h).symm (congrArg Prod.fst h).symm
    simp [qutritSwap, hswap]
  · simp

/-- The antisymmetric subspace of `ℂ³ ⊗ ℂ³` in product-basis coordinates. -/
def qutritAntisymmetricSubspace :
    Submodule ℂ ((Qutrit × Qutrit) → ℂ) where
  carrier := {ψ | ∀ i j, ψ (j, i) = -ψ (i, j)}
  zero_mem' := by
    simp
  add_mem' := by
    intro ψ φ hψ hφ i j
    simp only [Pi.add_apply]
    rw [hψ i j, hφ i j]
    abel
  smul_mem' := by
    intro c ψ hψ i j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hψ i j]
    simp

/-- Antisymmetrization of a bipartite qutrit vector. -/
def qutritAntisymmetrize
    (ψ : Qutrit × Qutrit → ℂ) : Qutrit × Qutrit → ℂ :=
  fun ij => (1 / 2 : ℂ) * (ψ ij - ψ (ij.2, ij.1))

/-- A standard coordinate vector in the product basis. -/
def qutritProductBasisKet
    (kl : Qutrit × Qutrit) : Qutrit × Qutrit → ℂ :=
  fun ij => if ij = kl then 1 else 0

/-- The matrix of antisymmetrization in the standard product basis. This
defines the antisymmetric projector independently of the desired
`(I ⊗ I - F) / 2` identity. -/
def qutritAntisymmetricProjector : CMatrix (Qutrit × Qutrit) :=
  fun ij kl => qutritAntisymmetrize (qutritProductBasisKet kl) ij

/-- Acting with the projector is the same as antisymmetrizing the vector. -/
theorem qutritAntisymmetricProjector_mulVec
    (ψ : Qutrit × Qutrit → ℂ) :
    Matrix.mulVec qutritAntisymmetricProjector ψ =
      qutritAntisymmetrize ψ := by
  ext ⟨i, j⟩
  change (∑ kl, ((1 / 2 : ℂ) *
      ((if (i, j) = kl then 1 else 0) -
        (if (j, i) = kl then 1 else 0))) * ψ kl) =
    (1 / 2 : ℂ) * (ψ (i, j) - ψ (j, i))
  calc
    _ = (∑ kl, (1 / 2 : ℂ) *
          (if (i, j) = kl then 1 else 0) * ψ kl) -
        (∑ kl, (1 / 2 : ℂ) *
          (if (j, i) = kl then 1 else 0) * ψ kl) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro kl hkl
      ring
    _ = _ := by simp [mul_sub]

/-- The explicit matrix above is a positive orthogonal projector whose range
is exactly the antisymmetric subspace. -/
theorem qutritAntisymmetricProjector_spec :
    qutritAntisymmetricProjector.PosSemidef ∧
      qutritAntisymmetricProjector * qutritAntisymmetricProjector =
        qutritAntisymmetricProjector ∧
      Set.range (fun ψ => Matrix.mulVec qutritAntisymmetricProjector ψ) =
        ((qutritAntisymmetricSubspace :
          Submodule ℂ ((Qutrit × Qutrit) → ℂ)) : Set ((Qutrit × Qutrit) → ℂ)) := by
  have hanti_idem (ψ : Qutrit × Qutrit → ℂ) :
      qutritAntisymmetrize (qutritAntisymmetrize ψ) =
        qutritAntisymmetrize ψ := by
    funext ⟨i, j⟩
    simp only [qutritAntisymmetrize]
    ring
  have hbasis (M : CMatrix (Qutrit × Qutrit))
      (ij kl : Qutrit × Qutrit) :
      Matrix.mulVec M (qutritProductBasisKet kl) ij = M ij kl := by
    change (∑ x, M ij x * (if x = kl then 1 else 0)) = M ij kl
    rw [Finset.sum_eq_single kl]
    · simp
    · intro b hb hne
      simp [hne]
    · simp
  have hPid :
      qutritAntisymmetricProjector * qutritAntisymmetricProjector =
        qutritAntisymmetricProjector := by
    ext ij kl
    have h := congrFun
      (qutritAntisymmetricProjector_mulVec
        (Matrix.mulVec qutritAntisymmetricProjector
          (qutritProductBasisKet kl))) ij
    rw [Matrix.mulVec_mulVec] at h
    rw [qutritAntisymmetricProjector_mulVec] at h
    rw [hanti_idem] at h
    simpa only [hbasis] using h
  have hHerm :
      Matrix.conjTranspose qutritAntisymmetricProjector =
        qutritAntisymmetricProjector := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.conjTranspose_apply, qutritAntisymmetricProjector,
      qutritAntisymmetrize, qutritProductBasisKet]
    simp only [Prod.mk.injEq]
    by_cases hik : i = k <;> by_cases hjl : j = l <;>
      by_cases hil : i = l <;> by_cases hjk : j = k <;>
      by_cases hkl : k = l <;>
      simp [hik, hjl, hil, hjk, hkl, and_comm, eq_comm]
  refine ⟨?_, hPid, ?_⟩
  · simpa only [hHerm, hPid] using
      (Matrix.posSemidef_conjTranspose_mul_self
        qutritAntisymmetricProjector)
  · ext ψ
    constructor
    · rintro ⟨φ, rfl⟩
      change ∀ i j,
        Matrix.mulVec qutritAntisymmetricProjector φ (j, i) =
          -Matrix.mulVec qutritAntisymmetricProjector φ (i, j)
      rw [qutritAntisymmetricProjector_mulVec]
      intro i j
      simp only [qutritAntisymmetrize]
      ring
    · intro hψ
      change ∀ i j, ψ (j, i) = -ψ (i, j) at hψ
      refine ⟨ψ, ?_⟩
      dsimp only
      rw [qutritAntisymmetricProjector_mulVec]
      funext ⟨i, j⟩
      simp only [qutritAntisymmetrize]
      rw [hψ i j]
      ring

/-- The qutrit Werner--Holevo matrix map
`X ↦ 1/2 (Tr(X) I - Xᵀ)`. -/
def qutritWernerHolevoMap : MatrixMap Qutrit Qutrit where
  toFun X :=
    (1 / 2 : ℂ) •
      (X.trace • (1 : CMatrix Qutrit) - Matrix.transpose X)
  map_add' := by
    intro X Y
    ext i j
    simp [Matrix.trace, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c X
    ext i j
    simp [Matrix.trace]
    rw [← Finset.mul_sum]
    ring

/-- Pointwise form of the qutrit Werner--Holevo map. -/
theorem qutritWernerHolevoMap_apply (X : CMatrix Qutrit) :
    qutritWernerHolevoMap X =
      (1 / 2 : ℂ) •
        (X.trace • (1 : CMatrix Qutrit) - Matrix.transpose X) := by
  rfl

/-- Under the unnormalized Choi convention, the Choi matrix of the qutrit
Werner--Holevo map is the antisymmetric projector. -/
theorem choi_qutritWernerHolevoMap :
    MatrixMap.choi qutritWernerHolevoMap =
        (1 / 2 : ℂ) •
          (Matrix.kronecker (1 : CMatrix Qutrit) (1 : CMatrix Qutrit) -
            qutritSwap) ∧
      (1 / 2 : ℂ) •
          (Matrix.kronecker (1 : CMatrix Qutrit) (1 : CMatrix Qutrit) -
            qutritSwap) =
        qutritAntisymmetricProjector := by
  have htrace (i k : Qutrit) :
      (Matrix.single i k (1 : ℂ)).trace =
        if i = k then 1 else 0 := by
    by_cases hik : i = k
    · subst k
      simp [Matrix.trace, Matrix.single]
    · have hki : k ≠ i := fun h => hik h.symm
      simp [Matrix.trace, Matrix.single, hik, hki]
  have hone (i k : Qutrit) :
      (1 : CMatrix Qutrit) i k = if i = k then 1 else 0 :=
    Matrix.one_apply
  constructor
  · ext ⟨i, j⟩ ⟨k, l⟩
    simp only [MatrixMap.choi, qutritWernerHolevoMap,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.transpose_apply, smul_eq_mul]
    rw [htrace i k, hone j l]
    simp only [Matrix.single, Matrix.kronecker, Matrix.kroneckerMap,
      Matrix.one_apply, qutritSwap, Prod.mk.injEq]
    by_cases hik : i = k <;> by_cases hjl : j = l <;>
      by_cases hil : i = l <;> by_cases hjk : j = k <;>
      by_cases hkl : k = l <;>
      simp [hik, hjl, hil, hjk, hkl, and_comm, eq_comm]
  · ext ⟨i, j⟩ ⟨k, l⟩
    change (1 / 2 : ℂ) *
        (((if i = k then 1 else 0) * (if j = l then 1 else 0)) -
          (if (i, j) = (l, k) then 1 else 0)) =
      (1 / 2 : ℂ) *
        ((if (i, j) = (k, l) then 1 else 0) -
          (if (j, i) = (k, l) then 1 else 0))
    simp only [Prod.mk.injEq]
    by_cases hik : i = k <;> by_cases hjl : j = l <;>
      by_cases hil : i = l <;> by_cases hjk : j = k <;>
      by_cases hkl : k = l <;>
      simp [hik, hjl, hil, hjk, hkl, and_comm]

/-- The qutrit Werner--Holevo map is completely positive. -/
theorem qutritWernerHolevoMap_isCompletelyPositive :
    MatrixMap.IsCompletelyPositive qutritWernerHolevoMap := by
  rw [MatrixMap.IsCompletelyPositive]
  have hchoi := choi_qutritWernerHolevoMap
  rw [hchoi.1, hchoi.2]
  exact qutritAntisymmetricProjector_spec.1

end

end QITFormalized.ChoiMatrixQutritWernerHolevoChannel
