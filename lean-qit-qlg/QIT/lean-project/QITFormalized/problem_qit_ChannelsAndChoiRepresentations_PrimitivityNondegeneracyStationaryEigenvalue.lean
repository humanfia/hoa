import QITBench.Base
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Metrizable.Basic

/-!
# Primitivity and nondegeneracy of the stationary eigenvalue

This file formalizes primitivity of a finite-dimensional quantum channel and
the resulting nondegeneracy of the stationary eigenvalue `1`.
-/

open scoped ComplexOrder MatrixOrder
open Filter Function Bornology
open scoped Matrix.Norms.Elementwise Topology

namespace QITBench

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace Channel

/-- A channel is primitive when one common positive power sends every density
matrix to a positive-definite matrix. -/
def IsPrimitive (Φ : Channel a a) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ ρ : State a, ((Φ.map ^ n) ρ.matrix).PosDef

end Channel

namespace MatrixMap

/-- An eigenvalue is nondegenerate when its eigenspace is one-dimensional. -/
def IsNondegenerateEigenvalue (Φ : MatrixMap a a) (μ : ℂ) : Prop :=
  Module.finrank ℂ (Module.End.eigenspace Φ μ) = 1

end MatrixMap

/-- For a primitive finite-dimensional quantum channel, the stationary
eigenvalue `1` of its superoperator is nondegenerate. -/
theorem primitive_nondegenerate_stationary_eigenvalue
    [Nonempty a] (Φ : Channel a a) (hΦ : Φ.IsPrimitive) :
    Φ.map.IsNondegenerateEigenvalue 1 := by
  classical
  letI : FirstCountableTopology (CMatrix a) :=
    inferInstanceAs (FirstCountableTopology (a → a → ℂ))
  rcases hΦ with ⟨n, _hn, hprimitive⟩

  have fixed_pow (X : CMatrix a) (hX : Φ.map X = X) :
      ∀ k : ℕ, (Φ.map ^ k) X = X := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Module.End.mul_apply, hX, ih]

  have isClosed_posSemidefMatrices :
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

  have norm_entry_le_one_of_posSemidef_trace_one :
      ∀ {M : CMatrix a}, M.PosSemidef → M.trace = 1 →
        ∀ i j : a, ‖M i j‖ ≤ 1 := by
    intro M hM htrace i j
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
    have hiiReal : M i i = (M i i).re :=
      Complex.eq_re_of_ofReal_le hii0c
    have hjjReal : M j j = (M j j).re :=
      Complex.eq_re_of_ofReal_le hjj0c
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

  have isCompact_densityMatrices :
      IsCompact {M : CMatrix a | M.PosSemidef ∧ M.trace = 1} := by
    apply Metric.isCompact_iff_isClosed_bounded.mpr
    constructor
    · exact isClosed_posSemidefMatrices.inter
        (isClosed_eq (by fun_prop) continuous_const)
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨1, fun M hM => ?_⟩
      exact (Matrix.norm_le_iff zero_le_one).2 fun i j =>
        norm_entry_le_one_of_posSemidef_trace_one hM.1 hM.2 i j

  have exists_fixed_state :
      ∃ ρstar : State a, Φ.applyState ρstar = ρstar := by
    let i0 : a := Classical.choice (inferInstance : Nonempty a)
    let ρ0 : State a := {
      matrix := Matrix.single i0 i0 1
      pos := QITBench.posSemidef_single i0
      trace_eq_one := by simp [Matrix.trace, Matrix.single]
    }
    let ρ : ℕ → State a := fun k => (Φ.applyState^[k]) ρ0
    have hρ : ∀ k, (ρ k).matrix = (Φ.map^[k]) ρ0.matrix := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
          change ((Φ.applyState^[k.succ]) ρ0).matrix =
            (Φ.map^[k.succ]) ρ0.matrix
          rw [iterate_succ_apply', iterate_succ_apply']
          change Φ.map ((Φ.applyState^[k]) ρ0).matrix =
            Φ.map ((Φ.map^[k]) ρ0.matrix)
          rw [ih]
    let avg : ℕ → CMatrix a := fun k =>
      birkhoffAverage ℂ (Φ.map : CMatrix a → CMatrix a) id (k + 1) ρ0.matrix
    have havg : ∀ k, (avg k).PosSemidef ∧ (avg k).trace = 1 := by
      intro k
      have hsum :
          (∑ j ∈ Finset.range (k + 1), (Φ.map^[j]) ρ0.matrix).PosSemidef := by
        induction (Finset.range (k + 1)) using Finset.induction_on with
        | empty =>
            simpa using (Matrix.PosSemidef.zero : (0 : CMatrix a).PosSemidef)
        | @insert j s hjs ih =>
            rw [Finset.sum_insert hjs]
            rw [← hρ j]
            exact ((ρ j).pos.add ih : _)
      constructor
      · change (((k + 1 : ℕ) : ℂ)⁻¹ •
          ∑ j ∈ Finset.range (k + 1), (Φ.map^[j]) ρ0.matrix).PosSemidef
        exact hsum.smul (by positivity)
      · change (Matrix.trace (((k + 1 : ℕ) : ℂ)⁻¹ •
          ∑ j ∈ Finset.range (k + 1), (Φ.map^[j]) ρ0.matrix)) = 1
        change (Matrix.traceLinearMap a ℂ ℂ) (((k + 1 : ℕ) : ℂ)⁻¹ •
          ∑ j ∈ Finset.range (k + 1), (Φ.map^[j]) ρ0.matrix) = 1
        rw [map_smul, map_sum]
        simp only [Matrix.traceLinearMap_apply]
        have htraceOrbit :
            ∀ j, Matrix.trace ((Φ.map^[j]) ρ0.matrix) = 1 := by
          intro j
          rw [← hρ j]
          exact (ρ j).trace_eq_one
        simp_rw [htraceOrbit]
        rw [Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul, mul_one, smul_eq_mul]
        apply inv_mul_cancel₀
        exact_mod_cast Nat.succ_ne_zero k
    obtain ⟨Mstar, hMstar, φ, hφ, hconv⟩ :=
      isCompact_densityMatrices.tendsto_subseq havg
    have horbitBounded :
        IsBounded (Set.range (fun k => (Φ.map^[k]) ρ0.matrix)) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨1, ?_⟩
      rintro M ⟨k, rfl⟩
      change ‖(Φ.map^[k]) ρ0.matrix‖ ≤ 1
      rw [← hρ k]
      exact (Matrix.norm_le_iff zero_le_one).2 fun i j =>
        norm_entry_le_one_of_posSemidef_trace_one
          (ρ k).pos (ρ k).trace_eq_one i j
    have halmost :
        Tendsto (fun k => Φ.map (avg k) - avg k) atTop (𝓝 0) := by
      have hbase : Tendsto (fun k =>
          birkhoffAverage ℂ (Φ.map : CMatrix a → CMatrix a) id k
              (Φ.map ρ0.matrix) -
            birkhoffAverage ℂ (Φ.map : CMatrix a → CMatrix a) id k ρ0.matrix)
          atTop (𝓝 0) := by
        apply tendsto_birkhoffAverage_apply_sub_birkhoffAverage ℂ
        simpa only [Function.id_def] using horbitBounded
      have hshift := hbase.comp (tendsto_add_atTop_nat 1)
      change Tendsto (fun k =>
        Φ.map (birkhoffAverage ℂ (Φ.map : CMatrix a → CMatrix a) id
            (k + 1) ρ0.matrix) -
          birkhoffAverage ℂ (Φ.map : CMatrix a → CMatrix a) id
            (k + 1) ρ0.matrix) atTop (𝓝 0)
      convert hshift using 1
      funext k
      congr 1
      rw [map_birkhoffAverage ℂ ℂ Φ.map]
      simp only [Function.comp_id]
      simp only [birkhoffAverage, birkhoffSum, Function.id_def]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact (iterate_succ_apply' (Φ.map : CMatrix a → CMatrix a)
        j ρ0.matrix).symm.trans
          (iterate_succ_apply (Φ.map : CMatrix a → CMatrix a) j ρ0.matrix)
    have hΦconv :
        Tendsto (fun k => Φ.map (avg (φ k))) atTop (𝓝 (Φ.map Mstar)) :=
      (Φ.map.continuous_of_finiteDimensional.tendsto Mstar).comp hconv
    have hdiffConv :
        Tendsto (fun k => Φ.map (avg (φ k)) - avg (φ k)) atTop
          (𝓝 (Φ.map Mstar - Mstar)) := hΦconv.sub hconv
    have hdiffZero :
        Tendsto (fun k => Φ.map (avg (φ k)) - avg (φ k)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply] using halmost.comp hφ.tendsto_atTop
    have hfix : Φ.map Mstar = Mstar := by
      apply sub_eq_zero.mp
      exact tendsto_nhds_unique hdiffConv hdiffZero
    let ρstar : State a := {
      matrix := Mstar
      pos := hMstar.1
      trace_eq_one := hMstar.2
    }
    refine ⟨ρstar, ?_⟩
    apply State.ext
    exact hfix

  obtain ⟨σ, hσstate⟩ := exists_fixed_state
  have hσfix : Φ.map σ.matrix = σ.matrix :=
    congrArg State.matrix hσstate
  have hσPD : σ.matrix.PosDef := by
    have h := hprimitive σ
    rwa [fixed_pow σ.matrix hσfix n] at h

  have boundary_from_faithful_state :
      ∀ H : CMatrix a, H.IsHermitian → H.trace = 0 → H ≠ 0 →
        ∃ (t : ℝ) (A : CMatrix a), A = σ.matrix + t • H ∧
          A.PosSemidef ∧ ¬ A.PosDef := by
    intro H hHerm htr hHne
    let S : CMatrix a := CFC.sqrt σ.matrix
    have hσnonneg : 0 ≤ σ.matrix := hσPD.posSemidef.nonneg
    have hSunit : IsUnit S := by
      exact (CFC.isUnit_sqrt_iff σ.matrix hσnonneg).mpr hσPD.isUnit
    have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSunit
    have hSherm : S.IsHermitian := by
      rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose]
      exact (CFC.sqrt_nonneg σ.matrix).isSelfAdjoint.star_eq
    have hSself : Matrix.conjTranspose S = S := hSherm.eq
    have hSsq : S * S = σ.matrix := by
      simpa [S, pow_two] using CFC.sq_sqrt σ.matrix hσnonneg
    let T : CMatrix a := S⁻¹
    have hTself : Matrix.conjTranspose T = T := hSherm.inv.eq
    let K : CMatrix a := T * H * T
    have hKherm : K.IsHermitian := by
      rw [Matrix.IsHermitian]
      simp [K, Matrix.conjTranspose_mul, hTself, hHerm.eq, Matrix.mul_assoc]
    have hSKS : S * K * S = H := by
      calc
        S * K * S = (S * S⁻¹) * H * (S⁻¹ * S) := by
          simp only [K, T]
          noncomm_ring
        _ = H := by
          rw [Matrix.mul_nonsing_inv S hSdet, Matrix.nonsing_inv_mul S hSdet]
          simp
    have hKnpsd : ¬ K.PosSemidef := by
      intro hKpsd
      have hHpsd : H.PosSemidef := by
        rw [← hSKS]
        simpa only [hSself] using hKpsd.mul_mul_conjTranspose_same S
      exact hHne ((hHpsd.trace_eq_zero_iff).mp htr)
    obtain ⟨i0, _hi0, hmin⟩ :=
      Finset.exists_min_image Finset.univ hKherm.eigenvalues
        Finset.univ_nonempty
    have hmneg : hKherm.eigenvalues i0 < 0 := by
      by_contra hnot
      have hmnonneg : 0 ≤ hKherm.eigenvalues i0 := le_of_not_gt hnot
      have hallnonneg : 0 ≤ hKherm.eigenvalues := by
        intro i
        exact hmnonneg.trans (hmin i (Finset.mem_univ i))
      apply hKnpsd
      exact hKherm.posSemidef_iff_eigenvalues_nonneg.mpr hallnonneg
    let t : ℝ := -(hKherm.eigenvalues i0)⁻¹
    have hmne : hKherm.eigenvalues i0 ≠ 0 := ne_of_lt hmneg
    have htm : t * hKherm.eigenvalues i0 = -1 := by
      dsimp [t]
      rw [neg_mul, inv_mul_cancel₀ hmne]
    let D : CMatrix a := Matrix.diagonal
      (fun i => ((1 + t * hKherm.eigenvalues i : ℝ) : ℂ))
    have hdiag : ∀ i, 0 ≤ (1 + t * hKherm.eigenvalues i : ℝ) := by
      intro i
      have hle := hmin i (Finset.mem_univ i)
      have ht : 0 < t := by
        dsimp [t]
        exact neg_pos.mpr (inv_lt_zero.mpr hmneg)
      nlinarith
    have hD : D.PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro i
      exact RCLike.ofReal_nonneg.mpr (hdiag i)
    let E : CMatrix a :=
      Matrix.diagonal (RCLike.ofReal ∘ hKherm.eigenvalues)
    have hDE : D = 1 + (t : ℂ) • E := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D, E]
      · simp [D, E, hij]
    let B : CMatrix a := 1 + t • K
    let f :=
      Unitary.conjStarAlgAut ℂ (CMatrix a) hKherm.eigenvectorUnitary
    have hspec : K = f E := by
      simpa [f, E] using hKherm.spectral_theorem
    have hBeq : B = (hKherm.eigenvectorUnitary : CMatrix a) * D *
        Matrix.conjTranspose (hKherm.eigenvectorUnitary : CMatrix a) := by
      calc
        B = 1 + (t : ℂ) • K := by ext i j; simp [B]
        _ = 1 + (t : ℂ) • f E :=
          congrArg (fun X : CMatrix a => 1 + (t : ℂ) • X) hspec
        _ = f (1 + (t : ℂ) • E) := by
          rw [map_add, map_one, map_smul]
        _ = f D := by rw [hDE]
        _ = (hKherm.eigenvectorUnitary : CMatrix a) * D *
            Matrix.conjTranspose (hKherm.eigenvectorUnitary : CMatrix a) := by
          simp [f, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    have hBpsd : B.PosSemidef := by
      rw [hBeq]
      exact hD.mul_mul_conjTranspose_same _
    let v : a → ℂ := ⇑(hKherm.eigenvectorBasis i0)
    have hvne : v ≠ 0 := by
      dsimp [v]
      exact (WithLp.ofLp_eq_zero 2).ne.mpr
        (hKherm.eigenvectorBasis.orthonormal.ne_zero i0)
    have hBvec : Matrix.mulVec B v = 0 := by
      rw [show B = 1 + (t : ℂ) • K by ext i j; simp [B]]
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        show Matrix.mulVec K v = (hKherm.eigenvalues i0 : ℂ) • v by
          simpa [v] using hKherm.mulVec_eigenvectorBasis i0]
      rw [smul_smul, ← Complex.ofReal_mul, htm]
      simp
    have hBnot : ¬ B.PosDef := by
      intro hBpd
      have hinj : Function.Injective B.mulVec :=
        Matrix.mulVec_injective_iff_isUnit.mpr hBpd.isUnit
      exact hvne (hinj (hBvec.trans (Matrix.mulVec_zero B).symm))
    let A : CMatrix a := S * B * S
    have hAeq : A = σ.matrix + t • H := by
      calc
        A = S * (1 + (t : ℂ) • K) * S := by
          dsimp [A, B]
        _ = S * S + (t : ℂ) • (S * K * S) := by noncomm_ring
        _ = σ.matrix + (t : ℂ) • H := by rw [hSsq, hSKS]
        _ = σ.matrix + t • H := by ext i j; simp
    have hApsd : A.PosSemidef := by
      dsimp [A]
      simpa only [hSself] using hBpsd.mul_mul_conjTranspose_same S
    have hTunit : IsUnit T := Matrix.isUnit_nonsing_inv_iff.mpr hSunit
    have hTinj : Function.Injective T.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr hTunit
    have hBfromA : Matrix.conjTranspose T * A * T = B := by
      rw [hTself]
      dsimp [A]
      calc
        T * (S * B * S) * T = (T * S) * B * (S * T) := by noncomm_ring
        _ = B := by
          dsimp [T]
          rw [Matrix.nonsing_inv_mul S hSdet, Matrix.mul_nonsing_inv S hSdet]
          simp
    have hAnot : ¬ A.PosDef := by
      intro hApd
      apply hBnot
      rw [← hBfromA]
      exact hApd.conjTranspose_mul_mul_same hTinj
    exact ⟨t, A, hAeq, hApsd, hAnot⟩

  have hermitian_fixed_trace_zero :
      ∀ H : CMatrix a, H.IsHermitian → Φ.map H = H → H.trace = 0 → H = 0 := by
    intro H hHerm hHfix htr
    by_contra hHne
    obtain ⟨t, A, hAeq, hApsd, hAnot⟩ :=
      boundary_from_faithful_state H hHerm htr hHne
    let ρ : State a := {
      matrix := A
      pos := hApsd
      trace_eq_one := by
        rw [hAeq, Matrix.trace_add, Matrix.trace_smul, σ.trace_eq_one, htr]
        simp
    }
    have hAfix : Φ.map A = A := by
      rw [hAeq]
      change Φ.map (σ.matrix + (t : ℂ) • H) =
        σ.matrix + (t : ℂ) • H
      rw [map_add, map_smul, hσfix, hHfix]
    have hApow : (Φ.map ^ n) A = A := fixed_pow A hAfix n
    have hApd : A.PosDef := by
      have h := hprimitive ρ
      change ((Φ.map ^ n) A).PosDef at h
      rwa [hApow] at h
    exact hAnot hApd

  have map_conjTranspose (X : CMatrix a) :
      Φ.map X.conjTranspose = (Φ.map X).conjTranspose := by
    obtain ⟨K, hK⟩ :=
      MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
    rw [hK]
    simp [MatrixMap.ofKraus, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]

  have fixed_trace_zero :
      ∀ X : CMatrix a, Φ.map X = X → X.trace = 0 → X = 0 := by
    intro X hfix htr
    let H : CMatrix a := X + X.conjTranspose
    have hHherm : H.IsHermitian := by
      rw [Matrix.IsHermitian]
      simp [H, Matrix.conjTranspose_add, add_comm]
    have hHfix : Φ.map H = H := by
      dsimp [H]
      rw [map_add, map_conjTranspose, hfix]
    have hHtr : H.trace = 0 := by
      dsimp [H]
      rw [Matrix.trace_add, Matrix.trace_conjTranspose, htr]
      simp
    have hHzero := hermitian_fixed_trace_zero H hHherm hHfix hHtr
    have hXstar : X.conjTranspose = -X := by
      dsimp [H] at hHzero
      exact eq_neg_of_add_eq_zero_right hHzero
    let Y : CMatrix a := Complex.I • X
    have hYherm : Y.IsHermitian := by
      rw [Matrix.IsHermitian]
      simp [Y, Matrix.conjTranspose_smul, hXstar]
    have hYfix : Φ.map Y = Y := by
      dsimp [Y]
      rw [map_smul, hfix]
    have hYtr : Y.trace = 0 := by
      dsimp [Y]
      rw [Matrix.trace_smul, htr]
      simp
    have hYzero := hermitian_fixed_trace_zero Y hYherm hYfix hYtr
    dsimp [Y] at hYzero
    exact (smul_eq_zero.mp hYzero).resolve_left Complex.I_ne_zero

  change Module.finrank ℂ (Module.End.eigenspace Φ.map 1) = 1
  let E := Module.End.eigenspace Φ.map (1 : ℂ)
  let tr : E →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap a ℂ ℂ).comp (Submodule.subtype E)
  have htrinj : Function.Injective tr := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply fixed_trace_zero (x.1 - y.1)
    · have hx := x.2
      have hy := y.2
      change x.1 ∈ Module.End.eigenspace Φ.map (1 : ℂ) at hx
      change y.1 ∈ Module.End.eigenspace Φ.map (1 : ℂ) at hy
      rw [Module.End.mem_eigenspace_iff] at hx hy
      simp only [one_smul] at hx hy
      rw [map_sub, hx, hy]
    · have htrace : x.1.trace = y.1.trace := hxy
      rw [Matrix.trace_sub, htrace, sub_self]
  have hupper : Module.finrank ℂ E ≤ 1 := by
    simpa [tr] using LinearMap.finrank_le_finrank_of_injective htrinj
  have hσmem : σ.matrix ∈ E := by
    change σ.matrix ∈ Module.End.eigenspace Φ.map (1 : ℂ)
    rw [Module.End.mem_eigenspace_iff]
    simpa using hσfix
  have hEne : E ≠ ⊥ := by
    intro hEzero
    rw [hEzero] at hσmem
    have hσzero : σ.matrix = 0 := by simpa using hσmem
    have h := σ.trace_eq_one
    rw [hσzero] at h
    simp at h
  have hlower : 1 ≤ Module.finrank ℂ E :=
    Submodule.one_le_finrank_iff.mpr hEne
  exact Nat.le_antisymm hupper hlower

end

end QITBench
