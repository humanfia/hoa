import QAlgBench.Base

/-!
# Unitary extension of the coherent encoding of a Markov chain

For a finite row-stochastic matrix `P`, the vectors whose `(a, b)` amplitudes
are `δ_{a,i} * √(P i b)` form an orthonormal family.  The theorem below states
that the corresponding partially prescribed matrix extends to a unitary
operator on the product register.
-/

open scoped BigOperators

namespace QAlgFormalized.UnitaryExtensionMarkovChainIsometry

/-- A register with computational-basis labels `Fin d`. -/
def finRegister (d : ℕ) : QAlgBench.Register where
  Index := Fin d
  fintype := inferInstance
  decEq := inferInstance

/-- The two-register space on which the coherent Markov-chain encoding acts. -/
def pairRegister (d : ℕ) : QAlgBench.Register :=
  QAlgBench.Register.prod (finRegister d) (finRegister d)

/--
A real square matrix is row-stochastic when all entries are nonnegative and
every row sums to one.
-/
def RowStochastic {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/--
The coherent state associated with row `i` of `P`.  At basis label `(a, b)`
its amplitude is `δ_{a,i} * √(P i b)`.
-/
noncomputable def coherentRowState {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) : QAlgBench.StateVector (pairRegister d) :=
  WithLp.toLp 2 fun ab =>
    if ab.1 = i then (Real.sqrt (P i ab.2) : ℂ) else 0

/--
The coherent row states of a row-stochastic matrix can be prescribed as the
columns indexed by `(i, 0)` of a unitary matrix on the product register.

The first concluding condition is the ket-action formulation
`U |i⟩|0⟩ = |ψᵢ⟩`; the second records the equivalent entrywise column formula.
-/
theorem exists_unitary_extension
    (d : ℕ) (hd : 0 < d) (P : Matrix (Fin d) (Fin d) ℝ)
    (hP : RowStochastic P) :
    ∃ U : QAlgBench.HilbertOperator (pairRegister d),
      U ∈ Matrix.unitaryGroup (pairRegister d).Index ℂ ∧
      (∀ i : Fin d,
        QAlgBench.HilbertOperator.applyVec U
            ((QAlgBench.PureState.ket (R := pairRegister d)
              (i, (⟨0, hd⟩ : Fin d)) :
                QAlgBench.PureState (pairRegister d)) :
              QAlgBench.StateVector (pairRegister d)) =
          coherentRowState P i) ∧
      ∀ a b i : Fin d,
        U (a, b) (i, (⟨0, hd⟩ : Fin d)) =
          if a = i then (Real.sqrt (P i b) : ℂ) else 0 := by
  classical
  let z : Fin d := ⟨0, hd⟩
  let s : Set ((pairRegister d).Index) := {x | x.2 = z}
  let v : (pairRegister d).Index → QAlgBench.StateVector (pairRegister d) :=
    fun x => coherentRowState P x.1
  have hinner (i k : Fin d) :
      inner ℂ (coherentRowState P i) (coherentRowState P k) =
        if i = k then 1 else 0 := by
    rw [PiLp.inner_apply]
    simp only [coherentRowState, RCLike.inner_apply]
    change (∑ x : Fin d × Fin d,
      (if x.1 = k then (Real.sqrt (P k x.2) : ℂ) else 0) *
        star (if x.1 = i then (Real.sqrt (P i x.2) : ℂ) else 0)) = _
    rw [Fintype.sum_prod_type]
    by_cases hik : i = k
    · subst k
      rw [if_pos rfl]
      calc
        (∑ x, ∑ y,
            (if x = i then (Real.sqrt (P i y) : ℂ) else 0) *
              star (if x = i then (Real.sqrt (P i y) : ℂ) else 0)) =
            ∑ x, if x = i then
              ∑ y, (Real.sqrt (P i y) : ℂ) * (Real.sqrt (P i y) : ℂ)
            else 0 := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hxi : x = i <;> simp [hxi]
        _ = ∑ y, (Real.sqrt (P i y) : ℂ) * (Real.sqrt (P i y) : ℂ) := by
              exact Fintype.sum_ite_eq' i _
        _ = 1 := by
              push_cast [← Complex.ofReal_mul]
              simp_rw [← sq, Real.sq_sqrt (hP.1 i _)]
              exact_mod_cast hP.2 i
    · have hki : k ≠ i := Ne.symm hik
      simp [hik, hki]
  have hv : Orthonormal ℂ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    intro x y
    have hsecond : x.1.2 = y.1.2 := x.2.trans y.2.symm
    have hxy : x = y ↔ x.1.1 = y.1.1 := by
      constructor
      · intro h
        exact congrArg (fun q => q.1.1) h
      · intro h
        apply Subtype.ext
        exact Prod.ext h hsecond
    change inner ℂ (coherentRowState P x.1.1) (coherentRowState P y.1.1) = _
    rw [hinner]
    exact if_congr hxy.symm rfl rfl
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let e := EuclideanSpace.basisFun (pairRegister d).Index ℂ
  let U : QAlgBench.HilbertOperator (pairRegister d) := e.toBasis.toMatrix b
  have hcol (i : Fin d) : b (i, z) = coherentRowState P i := by
    apply hb
    simp [s]
  have hU : U ∈ Matrix.unitaryGroup (pairRegister d).Index ℂ := by
    exact e.toMatrix_orthonormalBasis_mem_unitary b
  refine ⟨U, hU, ?_, ?_⟩
  · intro i
    ext ab
    rw [QAlgBench.HilbertOperator.applyVec_ket]
    have hi :=
      congrArg (fun w : QAlgBench.StateVector (pairRegister d) => w ab) (hcol i)
    dsimp [U, e]
    rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
    simpa [z] using hi
  · intro a b' i
    have hi :=
      congrArg (fun w : QAlgBench.StateVector (pairRegister d) => w (a, b')) (hcol i)
    dsimp [U, e]
    rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
    rw [hi]
    unfold coherentRowState
    exact if_congr Iff.rfl rfl rfl

end QAlgFormalized.UnitaryExtensionMarkovChainIsometry
