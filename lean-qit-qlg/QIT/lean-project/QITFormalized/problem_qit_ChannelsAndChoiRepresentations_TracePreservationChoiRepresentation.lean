import QITBench.Base

/-!
# Trace preservation in the Choi representation

For the unnormalized maximally entangled vector
`|Γ⟩ = ∑ i, |i⟩ ⊗ |i⟩`, the Base definition `MatrixMap.choi` is the matrix of
`(id ⊗ Φ)(|Γ⟩⟨Γ|)` in the product basis.  Thus its partial trace over the
output system is the identity exactly when `Φ` preserves trace.
-/

namespace QITBench

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace MatrixMap

/-- A completely positive endomorphism of a finite-dimensional matrix space
is trace-preserving iff the partial trace of its unnormalized Choi matrix over
the output system is the identity on the input system. -/
theorem isTracePreserving_iff_partialTraceB_choi_eq_one
    (Phi : MatrixMap a a) (_hCP : IsCompletelyPositive Phi) :
    IsTracePreserving Phi ↔
      partialTraceB (a := a) (b := a) (choi Phi) = (1 : CMatrix a) := by
  constructor
  · intro hTP
    ext i i'
    change (Phi (Matrix.single i i' (1 : Complex))).trace =
      (1 : CMatrix a) i i'
    rw [hTP, trace_single_one]
    simp [Matrix.one_apply]
  · intro hChoi X
    rw [trace_map_eq_sum_single]
    calc
      (∑ i : a, ∑ i' : a,
          X i i' * (Phi (Matrix.single i i' (1 : Complex))).trace) =
          ∑ i : a, ∑ i' : a,
            X i i' * (Matrix.single i i' (1 : Complex)).trace := by
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro i' _
              have hii' := congrFun (congrFun hChoi i) i'
              change (Phi (Matrix.single i i' (1 : Complex))).trace =
                (1 : CMatrix a) i i' at hii'
              rw [show (Phi (Matrix.single i i' (1 : Complex))).trace =
                  (Matrix.single i i' (1 : Complex)).trace by
                    calc
                      (Phi (Matrix.single i i' (1 : Complex))).trace =
                          (1 : CMatrix a) i i' := hii'
                      _ = if i = i' then 1 else 0 := by
                        simp [Matrix.one_apply]
                      _ = (Matrix.single i i' (1 : Complex)).trace :=
                        (trace_single_one i i').symm]
      _ = X.trace := by
        rw [Matrix.trace]
        simp [trace_single_one]

end MatrixMap

end

end QITBench
