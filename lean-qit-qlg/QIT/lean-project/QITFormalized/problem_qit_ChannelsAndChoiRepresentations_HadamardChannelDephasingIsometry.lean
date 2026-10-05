import QITBench.Base

/-!
# Hadamard channel from a basis-controlled dephasing isometry

The system Hilbert space is represented in its computational basis by `Fin d`.
The finite type `e` labels a fixed orthonormal basis of the auxiliary Hilbert
space.  Thus a family `η : Fin d → QITBench.PureVector e` is exactly the
basis-amplitude presentation of the unit vectors `|ηᵢ⟩`.
-/

open scoped ComplexOrder MatrixOrder

namespace QITFormalized.HadamardChannelDephasingIsometry

open QITBench

universe u

noncomputable section

variable {d : ℕ} {e : Type u}
variable [Fintype e] [DecidableEq e]

/-- The basis-controlled Stinespring operator
`U|i⟩ = |i⟩ ⊗ |ηᵢ⟩`, written in the product basis of `Fin d × e`. -/
def dephasingIsometry (η : Fin d → PureVector e) :
    Matrix (Fin d × e) (Fin d) ℂ :=
  fun jk i => if jk.1 = i then (η i).amp jk.2 else 0

/-- Entrywise form of the prescribed action
`U|i⟩ = |i⟩ ⊗ |ηᵢ⟩`. -/
theorem dephasingIsometry_apply (η : Fin d → PureVector e)
    (j : Fin d) (k : e) (i : Fin d) :
    dephasingIsometry η (j, k) i =
      if j = i then (η i).amp k else 0 := by
  rfl

/-- Unit normalization of every environment vector makes the
basis-controlled operator an isometry. -/
theorem dephasingIsometry_isometry (η : Fin d → PureVector e) :
    Matrix.conjTranspose (dephasingIsometry η) * dephasingIsometry η =
      (1 : CMatrix (Fin d)) := by
  ext i j
  simp [dephasingIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  by_cases hij : i = j
  · subst j
    simpa [rankOneMatrix_trace, dotProduct, mul_comm] using
      (η i).trace_rankOne_eq_one
  · simp [hij, Ne.symm hij]

/-- The map `ρ ↦ Tr_E (U ρ U†)` induced by the basis-controlled isometry. -/
def dephasingMap (η : Fin d → PureVector e) : MatrixMap (Fin d) (Fin d) where
  toFun ρ :=
    partialTraceB
      (dephasingIsometry η * ρ * Matrix.conjTranspose (dephasingIsometry η))
  map_add' := by
    intro ρ σ
    simp [Matrix.mul_add, Matrix.add_mul, partialTraceB_add]
  map_smul' := by
    intro c ρ
    simp [Matrix.mul_smul, Matrix.smul_mul, partialTraceB_smul]

/-- The diagonal Kraus operators obtained by resolving the environment output
in its fixed basis. -/
def dephasingKraus (η : Fin d → PureVector e) (k : e) :
    CMatrix (Fin d) :=
  fun i j => if i = j then (η i).amp k else 0

/-- Resolving the environment partial trace gives the diagonal Kraus
representation of the dephasing map. -/
theorem dephasingMap_eq_ofKraus (η : Fin d → PureVector e) :
    dephasingMap η = MatrixMap.ofKraus (dephasingKraus η) := by
  ext ρ i j
  simp [dephasingMap, partialTraceB, dephasingIsometry, dephasingKraus,
    MatrixMap.ofKraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : j = x
  · subst x
    rfl
  · simp [h]

/-- The Gram (correlation) matrix of the environment vectors. -/
def environmentGram (η : Fin d → PureVector e) : CMatrix (Fin d) :=
  fun i j => ∑ k : e, (η i).amp k * star ((η j).amp k)

/-- The environment Gram matrix is positive semidefinite. -/
theorem environmentGram_posSemidef (η : Fin d → PureVector e) :
    (environmentGram η).PosSemidef := by
  let V : Matrix (Fin d) e ℂ := fun i k => (η i).amp k
  have hV : environmentGram η = V * Matrix.conjTranspose V := by
    ext i j
    simp [environmentGram, V, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hV]
  exact Matrix.posSemidef_self_mul_conjTranspose V

/-- Unit environment vectors give a unit diagonal correlation matrix. -/
theorem environmentGram_diagonal (η : Fin d → PureVector e) :
    ∀ i : Fin d, environmentGram η i i = 1 := by
  intro i
  simpa [environmentGram, rankOneMatrix_trace] using (η i).trace_rankOne_eq_one

/-- Tracing out the environment acts by Schur multiplication with its Gram
matrix, on every input matrix and hence in particular on every density state. -/
theorem dephasingMap_eq_hadamard (η : Fin d → PureVector e)
    (ρ : CMatrix (Fin d)) :
    dephasingMap η ρ = Matrix.hadamard (environmentGram η) ρ := by
  rw [dephasingMap_eq_ofKraus]
  ext i j
  simp [MatrixMap.ofKraus, Matrix.sum_apply, dephasingKraus, environmentGram,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.hadamard]
  calc
    ∑ k, ∑ x, (η i).amp k * ρ i x *
        star (if j = x then (η j).amp k else 0) =
        ∑ k, (η i).amp k * ρ i j * star ((η j).amp k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single j]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    _ = ∑ k, (η i).amp k * star ((η j).amp k) * ρ i j := by
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    _ = (∑ k, (η i).amp k * star ((η j).amp k)) * ρ i j := by
      rw [Finset.sum_mul]

/-- The induced Stinespring map is completely positive. -/
theorem dephasingMap_isCompletelyPositive (η : Fin d → PureVector e) :
    MatrixMap.IsCompletelyPositive (dephasingMap η) := by
  rw [dephasingMap_eq_ofKraus]
  exact MatrixMap.ofKraus_completelyPositive (dephasingKraus η)

/-- The induced Stinespring map is trace preserving. -/
theorem dephasingMap_isTracePreserving (η : Fin d → PureVector e) :
    MatrixMap.IsTracePreserving (dephasingMap η) := by
  intro ρ
  rw [dephasingMap_eq_hadamard]
  simp [Matrix.trace, environmentGram_diagonal]

/-- The induced Stinespring map preserves positive semidefinite matrices. -/
theorem dephasingMap_mapsPositive (η : Fin d → PureVector e) :
    ∀ ρ : CMatrix (Fin d), ρ.PosSemidef → (dephasingMap η ρ).PosSemidef := by
  rw [dephasingMap_eq_ofKraus]
  exact MatrixMap.ofKraus_mapsPositive (dephasingKraus η)

/-- The CPTP channel induced by the basis-controlled dephasing isometry. -/
def dephasingChannel (η : Fin d → PureVector e) : Channel (Fin d) (Fin d) where
  map := dephasingMap η
  completelyPositive := dephasingMap_isCompletelyPositive η
  tracePreserving := dephasingMap_isTracePreserving η
  mapsPositive := dephasingMap_mapsPositive η

/-- The channel induced by the dephasing isometry is a Hadamard channel:
there is a positive semidefinite unit-diagonal matrix whose Schur action agrees
with the channel on every input matrix. -/
theorem hadamardChannel_dephasingIsometry (η : Fin d → PureVector e) :
    ∃ H : CMatrix (Fin d),
      H.PosSemidef ∧
        (∀ i : Fin d, H i i = 1) ∧
          ∀ ρ : CMatrix (Fin d),
            (dephasingChannel η).map ρ = Matrix.hadamard H ρ := by
  exact ⟨environmentGram η, environmentGram_posSemidef η,
    environmentGram_diagonal η, dephasingMap_eq_hadamard η⟩

end

end QITFormalized.HadamardChannelDephasingIsometry
