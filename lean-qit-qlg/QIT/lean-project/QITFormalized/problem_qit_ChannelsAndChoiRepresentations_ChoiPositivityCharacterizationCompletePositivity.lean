import QITBench.Base

/-!
# Choi positivity characterizes complete positivity

This file uses the finite coordinate model from `QITBench.Base`. A finite type
`a` labels the fixed orthonormal computational basis of the input Hilbert
space, so `Fintype.card a` is its dimension. The second occurrence of `a` in
`a × a` is the identified copy `A' ≅ A`.
-/

open scoped ComplexOrder MatrixOrder

namespace QITFormalized.ChannelsAndChoiRepresentations

open QITBench

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The dimension `d_A` of the input Hilbert space in the fixed-basis model. -/
def inputDimension (a : Type u) [Fintype a] : Nat :=
  Fintype.card a

/-- The unnormalized vector
`|Γ⟩_{AA'} = ∑ᵢ |i⟩_A |i⟩_{A'}` in computational-basis coordinates.

Its coefficient on `(i,j)` is one exactly when the two basis labels agree.
-/
def unnormalizedMaximallyEntangledKet (a : Type u) [DecidableEq a] :
    a × a → ℂ :=
  fun ij => if ij.1 = ij.2 then 1 else 0

/-- The unnormalized Choi matrix
`(id_A ⊗ Φ_{A' → B})(|Γ⟩⟨Γ|_{AA'})`.
-/
def unnormalizedChoiMatrix (Phi : MatrixMap a b) : CMatrix (a × b) :=
  MatrixMap.kron (Channel.idChannel a).map Phi
    (rankOneMatrix (unnormalizedMaximallyEntangledKet a))

/-- Operational complete positivity: for every finite ancillary system `R`,
`id_R ⊗ Φ` maps positive semidefinite operators on `R ⊗ A` to positive
semidefinite operators on `R ⊗ B`.

Quantifying `r : Type u` is the finite-basis presentation of quantifying over
finite-dimensional ancillary Hilbert spaces; finite systems can be relabelled
within this universe.
-/
def IsCompletelyPositiveByAncillas (Phi : MatrixMap a b) : Prop :=
  ∀ (r : Type u) [Fintype r] [DecidableEq r]
    (X : CMatrix (r × a)), X.PosSemidef →
      (MatrixMap.kron (Channel.idChannel r).map Phi X).PosSemidef

/-- The maximally-entangled-state formula for the Choi matrix agrees with the
entrywise Choi matrix supplied by `QITBench.Base`.
-/
theorem unnormalizedChoiMatrix_eq_choi (Phi : MatrixMap a b) :
    unnormalizedChoiMatrix Phi = MatrixMap.choi Phi := by
  ext ij kl
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨i', j'⟩
  simp [unnormalizedChoiMatrix, unnormalizedMaximallyEntangledKet,
    rankOneMatrix_apply, Channel.idChannel, MatrixMap.ofKraus, MatrixMap.kron,
    MatrixMap.choi]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i']
    · simp [Matrix.single]
    · intro y _ hy
      simp [Matrix.single, hy]
    · intro hnot
      simp at hnot
  · intro x _ hx
    simp [Matrix.single, hx]
  · intro hnot
    simp at hnot

/-- A finite-dimensional complex-linear matrix map is completely positive in
the operational, all-ancillas sense if and only if its unnormalized Choi matrix
is positive semidefinite.
-/
theorem isCompletelyPositiveByAncillas_iff_choi_posSemidef
    (Phi : MatrixMap a b) :
    IsCompletelyPositiveByAncillas Phi ↔
      (unnormalizedChoiMatrix Phi).PosSemidef := by
  constructor
  · intro hPhi
    exact hPhi a (rankOneMatrix (unnormalizedMaximallyEntangledKet a))
      (rankOneMatrix_pos (unnormalizedMaximallyEntangledKet a))
  · intro hChoi r _ _ X hX
    have hPhi : MatrixMap.IsCompletelyPositive Phi := by
      rw [MatrixMap.IsCompletelyPositive, ← unnormalizedChoiMatrix_eq_choi]
      exact hChoi
    exact MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.kron (Channel.idChannel r).map Phi)
      (MatrixMap.isCompletelyPositive_kron (Channel.idChannel r).map Phi
        (Channel.idChannel r).completelyPositive hPhi)
      X hX

end

end QITFormalized.ChannelsAndChoiRepresentations
