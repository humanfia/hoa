import QITBench.Base
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Metrizable.Basic

/-!
# Fixed point of a finite-dimensional quantum channel

The finite type `a` indexes an orthonormal basis of the Hilbert space.
`QITBench.State a` is its density-operator state space, and
`QITBench.Channel a a` packages a completely positive, trace-preserving
complex-linear operation.  The `Nonempty a` assumption makes explicit the
standard quantum-information convention that the Hilbert space is nonzero.
-/

namespace QITFormalized

open QITBench Filter Function Bornology
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology

universe u

noncomputable section

local instance matrixFirstCountableTopology
    {m : Type*} {n : Type*} {R : Type*}
    [Fintype m] [Fintype n] [TopologicalSpace R] [FirstCountableTopology R] :
    FirstCountableTopology (Matrix m n R) :=
  inferInstanceAs (FirstCountableTopology (m → n → R))

private theorem isClosed_posSemidefMatrices
    {a : Type u} [Fintype a] [DecidableEq a] :
    IsClosed {M : CMatrix a | M.PosSemidef} := by
  rw [show {M : CMatrix a | M.PosSemidef} =
      {M | M.IsHermitian} ∩
        ⋂ x : a →₀ ℂ,
          {M | 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj} by
    ext M
    simp [Matrix.PosSemidef]]
  apply IsClosed.inter
  · apply isClosed_eq
    · fun_prop
    · fun_prop
  · apply isClosed_iInter
    intro x
    apply isClosed_le
    · fun_prop
    · change Continuous (fun M : CMatrix a =>
        ∑ i ∈ x.support, ∑ j ∈ x.support, star (x i) * M i j * x j)
      fun_prop

private theorem norm_entry_le_one_of_posSemidef_trace_one
    {a : Type u} [Fintype a] [DecidableEq a]
    {M : CMatrix a} (hM : M.PosSemidef) (htrace : M.trace = 1)
    (i j : a) : ‖M i j‖ ≤ 1 := by
  have hii0c : 0 ≤ M i i := hM.diag_nonneg
  have hjj0c : 0 ≤ M j j := hM.diag_nonneg
  have hii0 : 0 ≤ (M i i).re := (Complex.nonneg_iff.mp hii0c).1
  have hjj0 : 0 ≤ (M j j).re := (Complex.nonneg_iff.mp hjj0c).1
  have hii1c : M i i ≤ 1 := by
    rw [← htrace, Matrix.trace]
    simpa only [Matrix.diag_apply] using
      (Finset.single_le_sum (f := fun k : a => M k k)
        (fun k _ => hM.diag_nonneg) (Finset.mem_univ i))
  have hjj1c : M j j ≤ 1 := by
    rw [← htrace, Matrix.trace]
    simpa only [Matrix.diag_apply] using
      (Finset.single_le_sum (f := fun k : a => M k k)
        (fun k _ => hM.diag_nonneg) (Finset.mem_univ j))
  have hii1 : (M i i).re ≤ 1 := by
    simpa using (Complex.le_def.mp hii1c).1
  have hjj1 : (M j j).re ≤ 1 := by
    simpa using (Complex.le_def.mp hjj1c).1
  have hiiReal : M i i = (M i i).re := Complex.eq_re_of_ofReal_le hii0c
  have hjjReal : M j j = (M j j).re := Complex.eq_re_of_ofReal_le hjj0c
  have hji : M j i = star (M i j) := by
    simpa only [star_star] using congrArg star (hM.isHermitian.apply i j)
  let e : Fin 2 → a := ![i, j]
  have hdet := (hM.submatrix e).det_nonneg
  rw [Matrix.det_fin_two] at hdet
  have hdetre := (Complex.nonneg_iff.mp hdet).1
  simp only [Matrix.submatrix_apply, e, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hdetre
  rw [hiiReal, hjjReal, hji, ← starRingEnd_apply, Complex.mul_conj] at hdetre
  norm_num at hdetre
  have hprod : (M i i).re * (M j j).re ≤ 1 := by nlinarith
  have hsq : ‖M i j‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    rw [Complex.sq_norm]
    norm_num
    exact hdetre.trans hprod
  exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp hsq

private theorem isCompact_densityMatrices
    {a : Type u} [Fintype a] [DecidableEq a] :
    IsCompact {M : CMatrix a | M.PosSemidef ∧ M.trace = 1} := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · exact isClosed_posSemidefMatrices.inter
      (isClosed_eq (by fun_prop) continuous_const)
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨1, fun M hM => ?_⟩
    exact (Matrix.norm_le_iff zero_le_one).2 fun i j =>
      norm_entry_le_one_of_posSemidef_trace_one hM.1 hM.2 i j

/-- Every trace-preserving quantum operation on a nonzero finite-dimensional
Hilbert space has a density-operator fixed point. -/
theorem exists_fixedPoint_of_tracePreserving_quantumOperation
    {a : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
    (Phi : Channel a a) :
    ∃ rhoStar : State a, Phi.applyState rhoStar = rhoStar := by
  classical
  let i0 : a := Classical.choice (inferInstance : Nonempty a)
  let rho0 : State a := {
    matrix := Matrix.single i0 i0 1
    pos := QITBench.posSemidef_single i0
    trace_eq_one := by simp [Matrix.trace, Matrix.single]
  }
  let rho : ℕ → State a := fun n => (Phi.applyState^[n]) rho0
  have hrho : ∀ n, (rho n).matrix = (Phi.map^[n]) rho0.matrix := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        change ((Phi.applyState^[n.succ]) rho0).matrix =
          (Phi.map^[n.succ]) rho0.matrix
        rw [iterate_succ_apply', iterate_succ_apply']
        change Phi.map ((Phi.applyState^[n]) rho0).matrix =
          Phi.map ((Phi.map^[n]) rho0.matrix)
        rw [ih]
  let avg : ℕ → CMatrix a := fun n =>
    birkhoffAverage ℂ (Phi.map : CMatrix a → CMatrix a) id (n + 1) rho0.matrix
  have havg : ∀ n, (avg n).PosSemidef ∧ (avg n).trace = 1 := by
    intro n
    have hsum :
        (∑ k ∈ Finset.range (n + 1), (Phi.map^[k]) rho0.matrix).PosSemidef := by
      induction (Finset.range (n + 1)) using Finset.induction_on with
      | empty =>
          simpa using (Matrix.PosSemidef.zero : (0 : CMatrix a).PosSemidef)
      | @insert k s hks ih =>
          rw [Finset.sum_insert hks]
          rw [← hrho k]
          exact ((rho k).pos.add ih : _)
    constructor
    · change (((n + 1 : ℕ) : ℂ)⁻¹ •
        ∑ k ∈ Finset.range (n + 1), (Phi.map^[k]) rho0.matrix).PosSemidef
      exact hsum.smul (by positivity)
    · change (Matrix.trace (((n + 1 : ℕ) : ℂ)⁻¹ •
        ∑ k ∈ Finset.range (n + 1), (Phi.map^[k]) rho0.matrix)) = 1
      change (Matrix.traceLinearMap a ℂ ℂ) (((n + 1 : ℕ) : ℂ)⁻¹ •
        ∑ k ∈ Finset.range (n + 1), (Phi.map^[k]) rho0.matrix) = 1
      rw [map_smul, map_sum]
      simp only [Matrix.traceLinearMap_apply]
      have htraceOrbit :
          ∀ k, (Matrix.trace ((Phi.map^[k]) rho0.matrix)) = 1 := by
        intro k
        rw [← hrho k]
        exact (rho k).trace_eq_one
      simp_rw [htraceOrbit]
      rw [Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul, mul_one, smul_eq_mul]
      apply inv_mul_cancel₀
      exact_mod_cast Nat.succ_ne_zero n
  obtain ⟨Mstar, hMstar, phi, hphi, hconv⟩ :=
    (isCompact_densityMatrices (a := a)).tendsto_subseq havg
  have horbitBounded :
      IsBounded (Set.range (fun n => (Phi.map^[n]) rho0.matrix)) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨1, ?_⟩
    rintro M ⟨n, rfl⟩
    change ‖(Phi.map^[n]) rho0.matrix‖ ≤ 1
    rw [← hrho n]
    exact (Matrix.norm_le_iff zero_le_one).2 fun i j =>
      norm_entry_le_one_of_posSemidef_trace_one
        (rho n).pos (rho n).trace_eq_one i j
  have halmost :
      Tendsto (fun n => Phi.map (avg n) - avg n) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n =>
        birkhoffAverage ℂ (Phi.map : CMatrix a → CMatrix a) id n
            (Phi.map rho0.matrix) -
          birkhoffAverage ℂ (Phi.map : CMatrix a → CMatrix a) id n rho0.matrix)
        atTop (𝓝 0) := by
      apply tendsto_birkhoffAverage_apply_sub_birkhoffAverage ℂ
      simpa only [Function.id_def] using horbitBounded
    have hshift := hbase.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun n =>
      Phi.map (birkhoffAverage ℂ (Phi.map : CMatrix a → CMatrix a) id
          (n + 1) rho0.matrix) -
        birkhoffAverage ℂ (Phi.map : CMatrix a → CMatrix a) id
          (n + 1) rho0.matrix) atTop (𝓝 0)
    convert hshift using 1
    funext n
    congr 1
    rw [map_birkhoffAverage ℂ ℂ Phi.map]
    simp only [Function.comp_id]
    simp only [birkhoffAverage, birkhoffSum, Function.id_def]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    exact (iterate_succ_apply' (Phi.map : CMatrix a → CMatrix a)
      k rho0.matrix).symm.trans
        (iterate_succ_apply (Phi.map : CMatrix a → CMatrix a) k rho0.matrix)
  have hPhiConv :
      Tendsto (fun n => Phi.map (avg (phi n))) atTop (𝓝 (Phi.map Mstar)) :=
    (Phi.map.continuous_of_finiteDimensional.tendsto Mstar).comp hconv
  have hdiffConv :
      Tendsto (fun n => Phi.map (avg (phi n)) - avg (phi n)) atTop
        (𝓝 (Phi.map Mstar - Mstar)) :=
    hPhiConv.sub hconv
  have hdiffZero :
      Tendsto (fun n => Phi.map (avg (phi n)) - avg (phi n)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using halmost.comp hphi.tendsto_atTop
  have hfix : Phi.map Mstar = Mstar := by
    apply sub_eq_zero.mp
    exact tendsto_nhds_unique hdiffConv hdiffZero
  let rhoStar : State a := {
    matrix := Mstar
    pos := hMstar.1
    trace_eq_one := hMstar.2
  }
  refine ⟨rhoStar, ?_⟩
  apply State.ext
  exact hfix

end

end QITFormalized
