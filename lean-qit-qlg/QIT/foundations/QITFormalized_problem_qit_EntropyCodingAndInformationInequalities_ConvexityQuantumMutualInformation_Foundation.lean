import QITBench.Base
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Classical-register infrastructure for conditional-entropy concavity

This file supplies the finite-dimensional state and marginal identities used
to reduce concavity of quantum conditional entropy to strong subadditivity.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace QITBench

universe u v w

noncomputable section

/-! ## Project-local Mathlib supplement — Scalar log-sum inequalities -/

/-- Weighted log-sum inequality, the scalar perspective inequality underlying
the commuting case of relative-entropy joint convexity. -/
theorem weighted_log_sum
    {ι : Type u} [Fintype ι]
    (p x y : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 < y i) :
    (∑ i, p i * x i) *
        Real.log ((∑ i, p i * x i) / (∑ i, p i * y i)) ≤
      ∑ i, p i * (x i * Real.log (x i / y i)) := by
  have hex : ∃ i, 0 < p i := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have hpzero : ∀ i, p i = 0 := fun i =>
      le_antisymm (h i) (hp i)
    have hzero : ∑ i, p i = 0 := by
      simp [hpzero]
    linarith
  let Y : ℝ := ∑ i, p i * y i
  have hY : 0 < Y := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (hp i) (hy i).le
    · obtain ⟨i, hi⟩ := hex
      exact ⟨i, Finset.mem_univ i, mul_pos hi (hy i)⟩
  let q : ι → ℝ := fun i => p i * y i / Y
  let z : ι → ℝ := fun i => x i / y i
  have hq (i : ι) : 0 ≤ q i :=
    div_nonneg (mul_nonneg (hp i) (hy i).le) hY.le
  have hqsum : ∑ i, q i = 1 := by
    change (∑ i, p i * y i / Y) = 1
    rw [← Finset.sum_div]
    exact div_self hY.ne'
  have hz (i : ι) : 0 ≤ z i :=
    div_nonneg (hx i) (hy i).le
  have hjensen := Real.convexOn_mul_log.map_sum_le
    (t := Finset.univ) (w := q) (p := z)
    (fun i _ => hq i) hqsum (fun i _ => hz i)
  simp only [smul_eq_mul] at hjensen
  have havg :
      (∑ i, q i * z i) = (∑ i, p i * x i) / Y := by
    change (∑ i, (p i * y i / Y) * (x i / y i)) = _
    calc
      _ = ∑ i, p i * x i / Y := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [ne_of_gt hY, ne_of_gt (hy i)]
      _ = _ :=
        (Finset.sum_div Finset.univ (fun i => p i * x i) Y).symm
  rw [havg] at hjensen
  have hscaled := mul_le_mul_of_nonneg_left hjensen hY.le
  calc
    (∑ i, p i * x i) *
        Real.log ((∑ i, p i * x i) / (∑ i, p i * y i)) =
        Y * (((∑ i, p i * x i) / Y) *
          Real.log ((∑ i, p i * x i) / Y)) := by
      change _ = (∑ i, p i * y i) * _
      field_simp [ne_of_gt hY]
      ring
    _ ≤ Y * (∑ i, q i * (z i * Real.log (z i))) := hscaled
    _ = ∑ i, p i * (x i * Real.log (x i / y i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change Y * (p i * y i / Y *
        (x i / y i * Real.log (x i / y i))) = _
      field_simp [ne_of_gt hY, ne_of_gt (hy i)]

/-- Coordinatewise weighted log-sum inequality for finite nonnegative vectors,
the classical joint-convexity core needed before the noncommutative lift. -/
theorem weighted_log_sum_coordinates
    {ι : Type u} {X : Type v} [Fintype ι] [Fintype X]
    (p : ι → ℝ) (x y : ι → X → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hx : ∀ i j, 0 ≤ x i j) (hy : ∀ i j, 0 < y i j) :
    (∑ j, (∑ i, p i * x i j) *
      Real.log ((∑ i, p i * x i j) / (∑ i, p i * y i j))) ≤
      ∑ i, p i * ∑ j, x i j * Real.log (x i j / y i j) := by
  calc
    _ ≤ ∑ j, ∑ i, p i *
        (x i j * Real.log (x i j / y i j)) :=
      Finset.sum_le_sum fun j _ =>
        weighted_log_sum p (fun i => x i j) (fun i => y i j)
          hp hsum (fun i => hx i j) (fun i => hy i j)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]

/-! ## Project-local Mathlib supplement — Classical register extensions -/

private def classicalPointState
    {ι : Type v} [Fintype ι] [DecidableEq ι] (i : ι) : State ι where
  matrix := Matrix.diagonal (Pi.single i 1)
  pos := Matrix.posSemidef_diagonal_iff.mpr fun j => by
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  trace_eq_one := by
    rw [Matrix.trace_diagonal]
    simp

/-- The characteristic polynomial of a finite block diagonal is the product
of the characteristic polynomials of its blocks. -/
theorem Matrix.charpoly_blockDiagonal
    {n : Type u} {ι : Type v}
    [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (M : ι → Matrix n n ℂ) :
    (Matrix.blockDiagonal M).charpoly = ∏ i, (M i).charpoly := by
  unfold Matrix.charpoly
  have hcharmatrix :
      (Matrix.blockDiagonal M).charmatrix =
        Matrix.blockDiagonal (fun i => (M i).charmatrix) := by
    ext xi yj
    rcases xi with ⟨x, i⟩
    rcases yj with ⟨y, j⟩
    by_cases hij : i = j
    · subst j
      simp [Matrix.charmatrix_apply, Matrix.diagonal_apply,
        Matrix.blockDiagonal_apply_eq]
    · simp [Matrix.blockDiagonal_apply_ne _ _ _ hij, hij]
  rw [hcharmatrix, Matrix.det_blockDiagonal]

/-- Summing any function over the roots of a block diagonal's characteristic
polynomial splits into the corresponding sum over the roots of each block. -/
theorem Matrix.sum_map_roots_charpoly_blockDiagonal
    {n : Type u} {ι : Type v} {R : Type w}
    [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    [AddCommMonoid R] (M : ι → Matrix n n ℂ) (f : ℂ → R) :
    ((Matrix.blockDiagonal M).charpoly.roots.map f).sum =
      ∑ i, ((M i).charpoly.roots.map f).sum := by
  rw [Matrix.charpoly_blockDiagonal]
  let polys : Multiset (Polynomial ℂ) :=
    Finset.univ.val.map fun i => (M i).charpoly
  have hprod : (∏ i, (M i).charpoly) = polys.prod := by
    simp [polys]
  have hzero : (0 : Polynomial ℂ) ∉ polys := by
    simp [polys, (Matrix.charpoly_monic _).ne_zero]
  rw [hprod, Polynomial.roots_multiset_prod polys hzero,
    Multiset.map_bind, Multiset.sum_bind]
  simp [polys]

/-- A spectral sum over a Hermitian block diagonal splits into the spectral
sums of its Hermitian blocks. -/
theorem Matrix.IsHermitian.sum_eigenvalues_blockDiagonal
    {n : Type u} {ι : Type v} {R : Type w}
    [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    [AddCommMonoid R] (M : ι → Matrix n n ℂ)
    (hM : ∀ i, (M i).IsHermitian)
    (hblock : (Matrix.blockDiagonal M).IsHermitian) (f : ℝ → R) :
    (∑ k, f (hblock.eigenvalues k)) =
      ∑ i, ∑ j, f ((hM i).eigenvalues j) := by
  calc
    (∑ k, f (hblock.eigenvalues k)) =
        ((Matrix.blockDiagonal M).charpoly.roots.map
          (fun z => f z.re)).sum := by
      rw [hblock.roots_charpoly_eq_eigenvalues]
      simp [Multiset.map_map]
    _ = ∑ i, ((M i).charpoly.roots.map (fun z => f z.re)).sum :=
      Matrix.sum_map_roots_charpoly_blockDiagonal M (fun z => f z.re)
    _ = ∑ i, ∑ j, f ((hM i).eigenvalues j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(hM i).roots_charpoly_eq_eigenvalues]
      simp [Multiset.map_map]

/-- Real scalar multiplication scales every root in the characteristic
polynomial factorization of a Hermitian matrix. -/
theorem Matrix.IsHermitian.charpoly_real_smul
    {n : Type u} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (r : ℝ) :
    (r • M).charpoly =
      ∏ i, (Polynomial.X -
        Polynomial.C ((r * hM.eigenvalues i : ℝ) : ℂ)) := by
  conv_lhs => rw [hM.spectral_theorem]
  rw [RCLike.real_smul_eq_coe_smul
      (K := ℂ) (E := Matrix n n ℂ),
    ← map_smul]
  rw [Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc]
  rw [Unitary.coe_star_mul_self, one_mul]
  rw [← RCLike.real_smul_eq_coe_smul
      (K := ℂ) (E := Matrix n n ℂ)]
  change
    (r • Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ))).charpoly = _
  have hdiag :
      r • Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ)) =
        Matrix.diagonal
          (fun i => ((r * hM.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    simp [Matrix.diagonal_apply, Complex.real_smul]
  rw [hdiag, Matrix.charpoly_diagonal]

/-- The roots of the characteristic polynomial of a real scalar multiple of
a Hermitian matrix are the correspondingly scaled original eigenvalues. -/
theorem Matrix.IsHermitian.roots_charpoly_real_smul
    {n : Type u} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (r : ℝ) :
    (r • M).charpoly.roots =
      Multiset.map (fun i => ((r * hM.eigenvalues i : ℝ) : ℂ))
        Finset.univ.val := by
  rw [Matrix.IsHermitian.charpoly_real_smul hM r, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C]
    simp
  · exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      Polynomial.X_sub_C_ne_zero _

/-- A spectral sum of a real scalar multiple of a Hermitian matrix can be
computed by scaling the original eigenvalues, independently of their order. -/
theorem Matrix.IsHermitian.sum_eigenvalues_real_smul
    {n : Type u} {R : Type v}
    [Fintype n] [DecidableEq n] [AddCommMonoid R]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (r : ℝ)
    (hscaled : (r • M).IsHermitian) (f : ℝ → R) :
    (∑ i, f (hscaled.eigenvalues i)) =
      ∑ i, f (r * hM.eigenvalues i) := by
  calc
    (∑ i, f (hscaled.eigenvalues i)) =
        ((r • M).charpoly.roots.map (fun z => f z.re)).sum := by
      rw [hscaled.roots_charpoly_eq_eigenvalues]
      simp [Multiset.map_map]
    _ = ∑ i, f (r * hM.eigenvalues i) := by
      rw [Matrix.IsHermitian.roots_charpoly_real_smul hM r]
      simp [Multiset.map_map]

/-- Partial trace over the first factor commutes with a finite real-weighted
average of bipartite state matrices. -/
theorem State.marginalB_matrix_eq_sum_smul_of_matrix_eq_sum_smul
    {A : Type u} {B : Type v} {ι : Type w}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype ι]
    (p : ι → ℝ) (sigma : ι → State (A × B)) (rho : State (A × B))
    (hrho : rho.matrix = ∑ i, (p i : ℂ) • (sigma i).matrix) :
    rho.marginalB.matrix =
      ∑ i, (p i : ℂ) • (sigma i).marginalB.matrix := by
  rw [State.marginalB_matrix, hrho]
  ext b b'
  simp only [partialTraceA, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change
    (∑ a : A, (p i : ℂ) * (sigma i).matrix (a, b) (a, b')) =
      (p i : ℂ) * ∑ a : A, (sigma i).matrix (a, b) (a, b')
  exact (Finset.mul_sum _ _ _).symm

/-- Trace pairing against a left-factor matrix can be computed after tracing
out the right tensor factor. -/
theorem partialTraceB_mul_trace_eq_trace_mul_kronecker_right
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (X : CMatrix (A × B)) (T : CMatrix A) :
    ((partialTraceB X) * T).trace =
      (X * Matrix.kronecker T (1 : CMatrix B)).trace := by
  simp [Matrix.trace, Matrix.mul_apply, partialTraceB,
    Matrix.kronecker, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.sum_mul]
  rw [Finset.sum_comm_cycle, Finset.sum_comm]

/-- The normalized state obtained by adjoining a classical label to a finite
ensemble of density states. -/
def State.classicalExtension
    {X : Type u} {ι : Type v}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (sigma : ι → State X)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) : State (X × ι) where
  matrix := ∑ i, p i • ((sigma i).prod (classicalPointState i)).matrix
  pos := by
    classical
    have hs : ∀ s : Finset ι,
        Matrix.PosSemidef
          (∑ i ∈ s, p i • ((sigma i).prod (classicalPointState i)).matrix) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simpa using
            (Matrix.PosSemidef.zero : (0 : CMatrix (X × ι)).PosSemidef)
      | @insert i s hi ih =>
          rw [Finset.sum_insert hi]
          exact
            (((sigma i).prod (classicalPointState i)).pos.smul (hp i)).add ih
    simpa using hs Finset.univ
  trace_eq_one := by
    rw [Matrix.trace_sum]
    simp_rw [Matrix.trace_smul, State.trace_eq_one, Complex.real_smul, mul_one]
    exact_mod_cast hsum

/-- The classical extension is the block-diagonal matrix with weighted state
blocks. -/
theorem State.classicalExtension_matrix_eq_blockDiagonal
    {X : Type u} {ι : Type v}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (sigma : ι → State X)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (State.classicalExtension p sigma hp hsum).matrix =
      Matrix.blockDiagonal (fun i => p i • (sigma i).matrix) := by
  ext xi yj
  rcases xi with ⟨x, i⟩
  rcases yj with ⟨y, j⟩
  simp only [State.classicalExtension, Matrix.sum_apply, Matrix.smul_apply,
    State.prod, classicalPointState]
  by_cases hij : i = j
  · subst j
    rw [Matrix.blockDiagonal_apply_eq]
    simp [Pi.single_apply]
  · rw [Matrix.blockDiagonal_apply_ne _ _ _ hij]
    simp [hij]

/-- Every spectral sum of a classical extension splits into the corresponding
weighted spectral sums of the component states. -/
theorem State.sum_eigenvalues_classicalExtension
    {X : Type u} {ι : Type v} {R : Type w}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    [AddCommMonoid R]
    (p : ι → ℝ) (sigma : ι → State X)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (f : ℝ → R) :
    (∑ k, f ((State.classicalExtension p sigma hp hsum).pos.isHermitian
      |>.eigenvalues k)) =
      ∑ i, ∑ j, f (p i * (sigma i).pos.isHermitian.eigenvalues j) := by
  let extension := State.classicalExtension p sigma hp hsum
  calc
    (∑ k, f (extension.pos.isHermitian.eigenvalues k)) =
        (extension.matrix.charpoly.roots.map (fun z => f z.re)).sum := by
      rw [extension.pos.isHermitian.roots_charpoly_eq_eigenvalues]
      simp [Multiset.map_map]
    _ = ((Matrix.blockDiagonal (fun i => p i • (sigma i).matrix)).charpoly.roots.map
          (fun z => f z.re)).sum := by
      rw [show extension.matrix =
          Matrix.blockDiagonal (fun i => p i • (sigma i).matrix) from
        State.classicalExtension_matrix_eq_blockDiagonal p sigma hp hsum]
    _ = ∑ i, ((p i • (sigma i).matrix).charpoly.roots.map
          (fun z => f z.re)).sum :=
      Matrix.sum_map_roots_charpoly_blockDiagonal
        (fun i => p i • (sigma i).matrix) (fun z => f z.re)
    _ = ∑ i, ∑ j,
        f (p i * (sigma i).pos.isHermitian.eigenvalues j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.IsHermitian.roots_charpoly_real_smul
        (sigma i).pos.isHermitian (p i)]
      simp [Multiset.map_map]

/-- The eigenvalues of a normalized density state sum to one. -/
theorem State.sum_eigenvalues_eq_one
    {X : Type u} [Fintype X] [DecidableEq X] (rho : State X) :
    ∑ i, rho.pos.isHermitian.eigenvalues i = 1 := by
  have h := rho.pos.isHermitian.trace_eq_sum_eigenvalues
  rw [rho.trace_eq_one] at h
  apply Complex.ofReal_injective
  simpa using h.symm

/-- The `x log x` spectral sum of a classical extension is its classical
weight contribution plus the weighted component spectral sums. -/
theorem State.sum_mul_log_eigenvalues_classicalExtension
    {X : Type u} {ι : Type v}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (sigma : ι → State X)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ k,
        let x :=
          (State.classicalExtension p sigma hp hsum).pos.isHermitian
            |>.eigenvalues k
        x * Real.log x) =
      ∑ i, (p i * Real.log (p i) +
        p i * ∑ j,
          let x := (sigma i).pos.isHermitian.eigenvalues j
          x * Real.log x) := by
  rw [State.sum_eigenvalues_classicalExtension p sigma hp hsum
    (fun x => x * Real.log x)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hpi : p i = 0
  · simp [hpi]
  have hterm : ∀ j,
      (p i * (sigma i).pos.isHermitian.eigenvalues j) *
          Real.log (p i * (sigma i).pos.isHermitian.eigenvalues j) =
        (p i * (sigma i).pos.isHermitian.eigenvalues j) *
          (Real.log (p i) +
            Real.log ((sigma i).pos.isHermitian.eigenvalues j)) := by
    intro j
    by_cases heig : (sigma i).pos.isHermitian.eigenvalues j = 0
    · simp [heig]
    · rw [Real.log_mul hpi heig]
  rw [show
      (∑ j, (p i * (sigma i).pos.isHermitian.eigenvalues j) *
        Real.log (p i * (sigma i).pos.isHermitian.eigenvalues j)) =
      ∑ j, (p i * (sigma i).pos.isHermitian.eigenvalues j) *
        (Real.log (p i) +
          Real.log ((sigma i).pos.isHermitian.eigenvalues j)) from
    Finset.sum_congr rfl fun j _ => hterm j]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have heigsum := State.sum_eigenvalues_eq_one (sigma i)
  calc
    (∑ j, p i * (sigma i).pos.isHermitian.eigenvalues j *
        Real.log (p i)) +
        ∑ j, p i * (sigma i).pos.isHermitian.eigenvalues j *
          Real.log ((sigma i).pos.isHermitian.eigenvalues j) =
      p i * Real.log (p i) *
          (∑ j, (sigma i).pos.isHermitian.eigenvalues j) +
        p i * (∑ j, (sigma i).pos.isHermitian.eigenvalues j *
          Real.log ((sigma i).pos.isHermitian.eigenvalues j)) := by
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = _ := by
      rw [heigsum]
      ring

/-- Tracing out the classical register of an extension recovers the weighted
average of the quantum state matrices. -/
theorem State.classicalExtension_marginalA_matrix
    {X : Type u} {ι : Type v}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (sigma : ι → State X)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (State.classicalExtension p sigma hp hsum).marginalA.matrix =
      ∑ i, (p i : ℂ) • (sigma i).matrix := by
  rw [State.marginalA_matrix,
    State.classicalExtension_matrix_eq_blockDiagonal]
  ext x y
  simp [partialTraceB, Complex.real_smul, Matrix.blockDiagonal_apply_eq,
    Matrix.sum_apply, Matrix.smul_apply]

/-- The `AB` marginal of the classical extension is a prescribed ensemble
average with the same underlying matrix. -/
theorem State.classicalExtension_marginalAB_eq_of_matrix_eq
    {A : Type u} {B : Type v} {ι : Type w}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (sigma : ι → State (A × B)) (rho : State (A × B))
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hrho : rho.matrix = ∑ i, (p i : ℂ) • (sigma i).matrix) :
    (State.classicalExtension p sigma hp hsum).marginalAB = rho := by
  apply State.ext
  rw [State.marginalAB_eq_marginalA,
    State.classicalExtension_marginalA_matrix]
  exact hrho.symm

/-- The `B` marginal of a classical extension agrees with the `B` marginal of
its prescribed `AB` ensemble average. -/
theorem State.classicalExtension_marginalBOfABC_eq_of_matrix_eq
    {A : Type u} {B : Type v} {ι : Type w}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (sigma : ι → State (A × B)) (rho : State (A × B))
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hrho : rho.matrix = ∑ i, (p i : ℂ) • (sigma i).matrix) :
    (State.classicalExtension p sigma hp hsum).marginalBOfABC =
      rho.marginalB := by
  rw [State.marginalBOfABC_eq,
    State.classicalExtension_marginalAB_eq_of_matrix_eq
      p sigma rho hp hsum hrho]

/-- The `BC` marginal of an `AB` ensemble's classical extension is the
classical extension of the individual `B` marginals. -/
theorem State.classicalExtension_marginalBC
    {A : Type u} {B : Type v} {ι : Type w}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (sigma : ι → State (A × B))
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (State.classicalExtension p sigma hp hsum).marginalBC =
      State.classicalExtension p (fun i => (sigma i).marginalB) hp hsum := by
  apply State.ext
  ext bi bj
  rcases bi with ⟨b, i⟩
  rcases bj with ⟨b', j⟩
  change
    (∑ a,
        (State.classicalExtension p sigma hp hsum).matrix
          ((a, b), i) ((a, b'), j)) =
      (State.classicalExtension p (fun i => (sigma i).marginalB) hp hsum).matrix
        (b, i) (b', j)
  rw [State.classicalExtension_matrix_eq_blockDiagonal,
    State.classicalExtension_matrix_eq_blockDiagonal]
  by_cases hij : i = j
  · subst j
    simp [Matrix.blockDiagonal_apply_eq, State.marginalB, partialTraceA,
      Matrix.smul_apply, Complex.real_smul, Finset.mul_sum]
  · simp [Matrix.blockDiagonal_apply_ne _ _ _ hij]

/-! ## Project-local Mathlib supplement — Spectral relative entropy -/

private def eigenbasisTransition
    {X : Type u} [Fintype X] [DecidableEq X]
    (rho sigma : State X) : Matrix.unitaryGroup X ℂ :=
  star rho.pos.isHermitian.eigenvectorUnitary *
    sigma.pos.isHermitian.eigenvectorUnitary

private theorem sum_normSq_eigenbasisTransition_row
    {X : Type u} [Fintype X] [DecidableEq X]
    (rho sigma : State X) (i : X) :
    ∑ j, Complex.normSq
        ((eigenbasisTransition rho sigma : CMatrix X) i j) = 1 := by
  let U := eigenbasisTransition rho sigma
  have hunit : (U : CMatrix X) * star (U : CMatrix X) = 1 :=
    Unitary.coe_mul_star_self U
  have h := congrArg (fun M : CMatrix X => M i i) hunit
  dsimp only at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.star_apply, Matrix.one_apply_eq] at h
  rw [← Complex.ofReal_inj]
  simpa [Complex.normSq_eq_conj_mul_self, mul_comm] using h

private theorem sum_normSq_eigenbasisTransition_col
    {X : Type u} [Fintype X] [DecidableEq X]
    (rho sigma : State X) (j : X) :
    ∑ i, Complex.normSq
        ((eigenbasisTransition rho sigma : CMatrix X) i j) = 1 := by
  let U := eigenbasisTransition rho sigma
  have hunit : star (U : CMatrix X) * (U : CMatrix X) = 1 :=
    Unitary.coe_star_mul_self U
  have h := congrArg (fun M : CMatrix X => M j j) hunit
  dsimp only at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.star_apply, Matrix.one_apply_eq] at h
  rw [← Complex.ofReal_inj]
  simpa [Complex.normSq_eq_conj_mul_self] using h

private theorem mul_log_le_mul_log_add_sub
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x * Real.log y ≤ x * Real.log x + y - x := by
  rcases hx.eq_or_lt with hzero | hxpos
  · rw [← hzero]
    simpa using hy.le
  · have hlog := Real.log_le_sub_one_of_pos (div_pos hy hxpos)
    rw [Real.log_div hy.ne' hxpos.ne'] at hlog
    calc
      x * Real.log y =
          x * (Real.log y - Real.log x) + x * Real.log x := by
        ring
      _ ≤ x * (y / x - 1) + x * Real.log x := by
        gcongr
      _ = x * Real.log x + y - x := by
        field_simp
        ring

/-- The Hermitian functional-calculus logarithm of a finite density matrix. -/
def State.spectralLogMatrix
    {X : Type u} [Fintype X] [DecidableEq X]
    (sigma : State X) : CMatrix X :=
  sigma.pos.isHermitian.cfc Real.log

/-- The spectral matrix logarithm of a density state is Hermitian. -/
theorem State.spectralLogMatrix_isHermitian
    {X : Type u} [Fintype X] [DecidableEq X] (sigma : State X) :
    sigma.spectralLogMatrix.IsHermitian := by
  unfold State.spectralLogMatrix
  rw [← sigma.pos.isHermitian.cfc_eq]
  exact IsSelfAdjoint.cfc

private theorem re_trace_diagonal_mul_mul_diagonal_mul_star
    {X : Type u} [Fintype X] [DecidableEq X]
    (W : CMatrix X) (x y : X → ℝ) :
    Complex.re
        ((Matrix.diagonal (Complex.ofReal ∘ x) * W *
          Matrix.diagonal (Complex.ofReal ∘ y) * star W).trace) =
      ∑ i, ∑ j, Complex.normSq (W i j) * (x i * y j) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply,
    Complex.normSq_apply, Complex.mul_re]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Pairing a state with a spectral matrix logarithm expands as the
cross-eigenbasis overlap sum used by finite quantum relative entropy. -/
theorem State.re_trace_mul_spectralLogMatrix
    {X : Type u} [Fintype X] [DecidableEq X]
    (rho sigma : State X) :
    Complex.re ((rho.matrix * sigma.spectralLogMatrix).trace) =
      ∑ i, ∑ j,
        Complex.normSq
            ((eigenbasisTransition rho sigma : CMatrix X) i j) *
          (rho.pos.isHermitian.eigenvalues i *
            Real.log (sigma.pos.isHermitian.eigenvalues j)) := by
  let U := rho.pos.isHermitian.eigenvectorUnitary
  let V := sigma.pos.isHermitian.eigenvectorUnitary
  let W := eigenbasisTransition rho sigma
  let Dx : CMatrix X :=
    Matrix.diagonal (Complex.ofReal ∘ rho.pos.isHermitian.eigenvalues)
  let Dy : CMatrix X :=
    Matrix.diagonal (Complex.ofReal ∘ Real.log ∘
      sigma.pos.isHermitian.eigenvalues)
  have hUstarU : star (U : CMatrix X) * (U : CMatrix X) = 1 :=
    Unitary.coe_star_mul_self U
  have hUUstar : (U : CMatrix X) * star (U : CMatrix X) = 1 :=
    Unitary.coe_mul_star_self U
  have hW :
      (W : CMatrix X) =
        star (U : CMatrix X) * (V : CMatrix X) := by
    rfl
  have hstarW :
      star (W : CMatrix X) =
        star (V : CMatrix X) * (U : CMatrix X) := by
    rw [hW, star_mul]
    simp
  have hrho :
      rho.matrix =
        (U : CMatrix X) * Dx * star (U : CMatrix X) :=
    rho.pos.isHermitian.spectral_theorem
  have hlogsigma :
      sigma.spectralLogMatrix =
        (V : CMatrix X) * Dy * star (V : CMatrix X) := by
    rfl
  have hconjugate (P : CMatrix X) :
      (star (U : CMatrix X) * P * (U : CMatrix X)).trace =
        P.trace := by
    rw [Matrix.trace_mul_cycle, hUUstar, one_mul]
  have hmatrix :
      star (U : CMatrix X) *
          (((U : CMatrix X) * Dx * star (U : CMatrix X)) *
            ((V : CMatrix X) * Dy * star (V : CMatrix X))) *
            (U : CMatrix X) =
        Dx * (W : CMatrix X) * Dy * star (W : CMatrix X) := by
    rw [hstarW, hW]
    calc
      _ = (star (U : CMatrix X) * (U : CMatrix X)) * Dx *
          star (U : CMatrix X) * (V : CMatrix X) * Dy *
            star (V : CMatrix X) * (U : CMatrix X) := by
        noncomm_ring
      _ = Dx * star (U : CMatrix X) * (V : CMatrix X) * Dy *
            star (V : CMatrix X) * (U : CMatrix X) := by
        rw [hUstarU]
        simp
      _ = _ := by
        noncomm_ring
  calc
    Complex.re ((rho.matrix * sigma.spectralLogMatrix).trace) =
        Complex.re
          ((star (U : CMatrix X) *
            (rho.matrix * sigma.spectralLogMatrix) *
              (U : CMatrix X)).trace) := by
      rw [hconjugate]
    _ = Complex.re
        ((Dx * (W : CMatrix X) * Dy * star (W : CMatrix X)).trace) := by
      rw [hrho, hlogsigma, hmatrix]
    _ = ∑ i, ∑ j, Complex.normSq ((W : CMatrix X) i j) *
          (rho.pos.isHermitian.eigenvalues i *
            Real.log (sigma.pos.isHermitian.eigenvalues j)) := by
      exact re_trace_diagonal_mul_mul_diagonal_mul_star
        (W : CMatrix X) rho.pos.isHermitian.eigenvalues
        (Real.log ∘ sigma.pos.isHermitian.eigenvalues)
    _ = _ := rfl

/-- The finite spectral formula for quantum relative entropy.  The
positive-definite reference case is the project-local analytic layer used
toward quantum data processing and strong subadditivity. -/
def State.spectralRelativeEntropy
    {X : Type u} [Fintype X] [DecidableEq X]
    (rho sigma : State X) : ℝ :=
  (∑ i,
      let x := rho.pos.isHermitian.eigenvalues i
      x * Real.log x) -
    ∑ i, ∑ j,
      Complex.normSq
          ((eigenbasisTransition rho sigma : CMatrix X) i j) *
        (rho.pos.isHermitian.eigenvalues i *
          Real.log (sigma.pos.isHermitian.eigenvalues j))

/-- Spectral relative entropy is the entropy spectral sum minus the trace
pairing with the reference state's matrix logarithm. -/
theorem State.spectralRelativeEntropy_eq_spectral_sum_sub_trace
    {X : Type u} [Fintype X] [DecidableEq X]
    (rho sigma : State X) :
    rho.spectralRelativeEntropy sigma =
      (∑ i,
        let x := rho.pos.isHermitian.eigenvalues i
        x * Real.log x) -
        Complex.re ((rho.matrix * sigma.spectralLogMatrix).trace) := by
  rw [State.spectralRelativeEntropy,
    State.re_trace_mul_spectralLogMatrix]

/-- A state's finite spectral relative entropy with itself vanishes. -/
theorem State.spectralRelativeEntropy_self
    {X : Type u} [Fintype X] [DecidableEq X] (rho : State X) :
    rho.spectralRelativeEntropy rho = 0 := by
  have htransition : eigenbasisTransition rho rho = 1 := by
    exact Unitary.star_mul_self rho.pos.isHermitian.eigenvectorUnitary
  unfold State.spectralRelativeEntropy
  rw [htransition]
  simp [Matrix.one_apply]

/-- Pairing a density matrix with its own spectral logarithm recovers its
`x log x` spectral sum. -/
theorem State.re_trace_mul_spectralLogMatrix_self
    {X : Type u} [Fintype X] [DecidableEq X] (rho : State X) :
    Complex.re ((rho.matrix * rho.spectralLogMatrix).trace) =
      ∑ i,
        let x := rho.pos.isHermitian.eigenvalues i
        x * Real.log x := by
  have hself := State.spectralRelativeEntropy_self rho
  rw [State.spectralRelativeEntropy_eq_spectral_sum_sub_trace] at hself
  linarith

/-- Klein's inequality for the finite spectral relative entropy when the
reference density matrix is positive definite. -/
theorem State.spectralRelativeEntropy_nonneg_of_posDef
    {X : Type u} [Fintype X] [DecidableEq X]
    (rho sigma : State X) (hsigma : sigma.matrix.PosDef) :
    0 ≤ rho.spectralRelativeEntropy sigma := by
  let x : X → ℝ := rho.pos.isHermitian.eigenvalues
  let y : X → ℝ := sigma.pos.isHermitian.eigenvalues
  let q : X → X → ℝ := fun i j =>
    Complex.normSq ((eigenbasisTransition rho sigma : CMatrix X) i j)
  have hx (i : X) : 0 ≤ x i := rho.pos.eigenvalues_nonneg i
  have hy (j : X) : 0 < y j := hsigma.eigenvalues_pos j
  have hrow (i : X) : ∑ j, q i j = 1 :=
    sum_normSq_eigenbasisTransition_row rho sigma i
  have hcol (j : X) : ∑ i, q i j = 1 :=
    sum_normSq_eigenbasisTransition_col rho sigma j
  have hxsum : ∑ i, x i = 1 := State.sum_eigenvalues_eq_one rho
  have hysum : ∑ j, y j = 1 := State.sum_eigenvalues_eq_one sigma
  have hterm (i j : X) :
      q i j * (x i * Real.log (y j)) ≤
        q i j * (x i * Real.log (x i) + y j - x i) :=
    mul_le_mul_of_nonneg_left
      (mul_log_le_mul_log_add_sub (hx i) (hy j))
      (Complex.normSq_nonneg _)
  have hsum :
      (∑ i, ∑ j, q i j * (x i * Real.log (y j))) ≤
        ∑ i, ∑ j,
          q i j * (x i * Real.log (x i) + y j - x i) :=
    Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => hterm i j
  have hxx :
      (∑ i, ∑ j, q i j * (x i * Real.log (x i))) =
        ∑ i, x i * Real.log (x i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, hrow, one_mul]
  have hyy :
      (∑ i, ∑ j, q i j * y j) = ∑ j, y j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, hcol, one_mul]
  have hxin :
      (∑ i, ∑ j, q i j * x i) = ∑ i, x i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, hrow, one_mul]
  have hrhs :
      (∑ i, ∑ j,
          q i j * (x i * Real.log (x i) + y j - x i)) =
        ∑ i, x i * Real.log (x i) := by
    calc
      (∑ i, ∑ j,
          q i j * (x i * Real.log (x i) + y j - x i)) =
          (∑ i, ∑ j, q i j * (x i * Real.log (x i))) +
            (∑ i, ∑ j, q i j * y j) -
              (∑ i, ∑ j, q i j * x i) := by
        simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib,
          Finset.sum_add_distrib]
      _ = (∑ i, x i * Real.log (x i)) +
          (∑ j, y j) - (∑ i, x i) := by
        rw [hxx, hyy, hxin]
      _ = ∑ i, x i * Real.log (x i) := by
        rw [hxsum, hysum]
        ring
  rw [State.spectralRelativeEntropy]
  change 0 ≤ (∑ i, x i * Real.log (x i)) -
    ∑ i, ∑ j, q i j * (x i * Real.log (y j))
  rw [hrhs] at hsum
  linarith

/-- Klein's inequality in trace-pairing form, ready for use with partial-trace
adjunction identities. -/
theorem State.spectral_sum_sub_re_trace_spectralLogMatrix_nonneg_of_posDef
    {X : Type u} [Fintype X] [DecidableEq X]
    (rho sigma : State X) (hsigma : sigma.matrix.PosDef) :
    0 ≤
      (∑ i,
        let x := rho.pos.isHermitian.eigenvalues i
        x * Real.log x) -
        Complex.re ((rho.matrix * sigma.spectralLogMatrix).trace) := by
  rw [← State.spectralRelativeEntropy_eq_spectral_sum_sub_trace]
  exact rho.spectralRelativeEntropy_nonneg_of_posDef sigma hsigma

/-! ## Project-local Mathlib supplement — Operator logarithm inequalities -/

open scoped Matrix.Norms.L2Operator

local instance matrixCStarAlgebra
    {X : Type u} [Fintype X] [DecidableEq X] :
    CStarAlgebra (CMatrix X) where
  norm_mul_self_le := Matrix.instCStarRing.norm_mul_self_le

/-- The real trace pairing of two positive semidefinite complex matrices is
nonnegative; this packages positivity of trace functionals for entropy proofs. -/
theorem Matrix.PosSemidef.re_trace_mul_nonneg
    {X : Type u} [Fintype X] [DecidableEq X]
    {A B : CMatrix X} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Complex.re ((A * B).trace) := by
  obtain ⟨C, hC⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have hCB : (C * B * C.conjTranspose).PosSemidef :=
    hB.mul_mul_conjTranspose_same C
  have htrace : 0 ≤ (C * B * C.conjTranspose).trace :=
    hCB.trace_nonneg
  have hre : 0 ≤ Complex.re ((C * B * star C).trace) := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Complex.nonneg_iff.mp htrace).1
  rw [hC]
  calc
    0 ≤ Complex.re ((C * B * star C).trace) := hre
    _ = Complex.re ((star C * C * B).trace) := by
      rw [Matrix.trace_mul_cycle C B (star C)]

/-- Pairing on the left by a positive semidefinite matrix preserves the
Loewner order on the right after taking the real trace. -/
theorem Matrix.PosSemidef.re_trace_mul_mono_right
    {X : Type u} [Fintype X] [DecidableEq X]
    {P A B : CMatrix X} (hP : P.PosSemidef) (hAB : A ≤ B) :
    Complex.re ((P * A).trace) ≤ Complex.re ((P * B).trace) := by
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hnonneg :=
    Matrix.PosSemidef.re_trace_mul_nonneg hP hdiff
  have hdecomp :
      (P * B).trace =
        (P * A).trace + (P * (B - A)).trace := by
    rw [mul_sub, Matrix.trace_sub]
    abel
  rw [hdecomp, Complex.add_re]
  linarith

/-- A normalized nonnegative finite combination of positive definite complex
matrices remains positive definite, even when some weights vanish. -/
theorem Matrix.PosDef.sum_smul_of_nonneg
    {X : Type u} {ι : Type v}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (M : ι → CMatrix X)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hM : ∀ i, (M i).PosDef) :
    (∑ i, p i • M i).PosDef := by
  have hex : ∃ i, 0 < p i := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have hpzero : ∀ i, p i = 0 := fun i =>
      le_antisymm (h i) (hp i)
    have hzero : ∑ i, p i = 0 := by
      simp [hpzero]
    linarith
  obtain ⟨i, hi⟩ := hex
  let f : ι → CMatrix X := fun j => p j • M j
  have hrest :
      (∑ j ∈ (Finset.univ.erase i), f j).PosSemidef :=
    Matrix.posSemidef_sum (Finset.univ.erase i) fun j _ =>
      (hM j).posSemidef.smul (hp j)
  have hiPos : (f i).PosDef := (hM i).smul hi
  have hsplit :=
    Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  change (∑ i, f i).PosDef
  rw [← hsplit]
  exact Matrix.PosDef.posSemidef_add hrest hiPos

/-- Operator monotonicity of the logarithm, expressed through the
matrix-specific finite spectral functional calculus. -/
theorem Matrix.PosDef.cfc_log_mono
    {X : Type u} [Fintype X] [DecidableEq X]
    {A B : CMatrix X} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : A ≤ B) :
    hA.isHermitian.cfc Real.log ≤ hB.isHermitian.cfc Real.log := by
  calc
    hA.isHermitian.cfc Real.log = CFC.log A := by
      exact (hA.isHermitian.cfc_eq Real.log).symm
    _ ≤ CFC.log B :=
      CFC.log_le_log hAB hA.isStrictlyPositive
    _ = hB.isHermitian.cfc Real.log :=
      hB.isHermitian.cfc_eq Real.log

/-- Finite operator Jensen for the concave matrix logarithm, including
normalized ensembles with zero weights. -/
theorem Matrix.PosDef.sum_smul_cfc_log_le
    {X : Type u} {ι : Type v}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (M : ι → CMatrix X)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hM : ∀ i, (M i).PosDef) :
    (∑ i, p i • (hM i).isHermitian.cfc Real.log) ≤
      (Matrix.PosDef.sum_smul_of_nonneg p M hp hsum hM).isHermitian.cfc
        Real.log := by
  let avg : CMatrix X := ∑ i, p i • M i
  have havg : avg.PosDef :=
    Matrix.PosDef.sum_smul_of_nonneg p M hp hsum hM
  have hjensen :
      (∑ i, p i • CFC.log (M i)) ≤ CFC.log avg :=
    CFC.concaveOn_log.le_map_sum
      (t := Finset.univ) (w := p) (p := M)
      (fun i _ => hp i) hsum
      (fun i _ => (hM i).isStrictlyPositive)
  change
    (∑ i, p i • (hM i).isHermitian.cfc Real.log) ≤
      havg.isHermitian.cfc Real.log
  calc
    (∑ i, p i • (hM i).isHermitian.cfc Real.log) =
        ∑ i, p i • CFC.log (M i) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact (hM i).isHermitian.cfc_eq Real.log |>.symm
    _ ≤ CFC.log avg := hjensen
    _ = havg.isHermitian.cfc Real.log :=
      havg.isHermitian.cfc_eq Real.log

/-! ## Project-local Mathlib supplement — Unitary twirling infrastructure -/

/-- Conjugating a density state by a finite unitary produces another density
state, providing the state-level action used in twirling arguments. -/
def State.unitaryConjugate
    {X : Type u} [Fintype X] [DecidableEq X]
    (U : Matrix.unitaryGroup X ℂ) (rho : State X) : State X where
  matrix :=
    (U : CMatrix X) * rho.matrix *
      Matrix.conjTranspose (U : CMatrix X)
  pos := rho.pos.mul_mul_conjTranspose_same (U : CMatrix X)
  trace_eq_one := by
    calc
      ((U : CMatrix X) * rho.matrix *
          Matrix.conjTranspose (U : CMatrix X)).trace =
          (Matrix.conjTranspose (U : CMatrix X) *
            (U : CMatrix X) * rho.matrix).trace := by
        rw [Matrix.trace_mul_cycle]
      _ = rho.matrix.trace := by
        rw [show
          Matrix.conjTranspose (U : CMatrix X) * (U : CMatrix X) = 1 by
            simpa [Matrix.star_eq_conjTranspose] using
              Matrix.UnitaryGroup.star_mul_self U]
        simp
      _ = 1 := rho.trace_eq_one

/-- Unitary conjugation preserves strict positive definiteness of density
matrices. -/
theorem State.unitaryConjugate_posDef
    {X : Type u} [Fintype X] [DecidableEq X]
    (U : Matrix.unitaryGroup X ℂ) (rho : State X)
    (hrho : rho.matrix.PosDef) :
    (rho.unitaryConjugate U).matrix.PosDef := by
  change ((U : CMatrix X) * rho.matrix *
    Matrix.conjTranspose (U : CMatrix X)).PosDef
  rw [← Matrix.star_eq_conjTranspose]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
    Unitary.isUnit_coe).2 hrho

/-- Extend a unitary on the left tensor factor by the identity on the right
factor. -/
def Matrix.UnitaryGroup.onProdLeft
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (U : Matrix.unitaryGroup A ℂ) : Matrix.unitaryGroup (A × B) ℂ :=
  ⟨Matrix.kronecker (U : CMatrix A) (1 : CMatrix B), by
    apply Matrix.kronecker_mem_unitary
    · exact U.property
    · exact SetLike.coe_mem (1 : Matrix.unitaryGroup B ℂ)⟩

private theorem unitaryOnProdLeft_mul_apply
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (U : Matrix.unitaryGroup A ℂ) (M : CMatrix (A × B))
    (a x : A) (b b' : B) :
    (((Matrix.UnitaryGroup.onProdLeft (B := B) U :
        Matrix.unitaryGroup (A × B) ℂ) :
        CMatrix (A × B)) * M) (a, b) (x, b') =
      ∑ y, (U : CMatrix A) a y * M (y, b) (x, b') := by
  simp [Matrix.UnitaryGroup.onProdLeft, Matrix.mul_apply,
    Matrix.kronecker, Matrix.one_apply, Fintype.sum_prod_type]

private theorem mul_unitaryOnProdLeft_conjTranspose_apply
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (U : Matrix.unitaryGroup A ℂ) (M : CMatrix (A × B))
    (a x : A) (b b' : B) :
    (M * Matrix.conjTranspose
      ((Matrix.UnitaryGroup.onProdLeft (B := B) U :
          Matrix.unitaryGroup (A × B) ℂ) :
        CMatrix (A × B))) (a, b) (x, b') =
      ∑ y, M (a, b) (y, b') * star ((U : CMatrix A) x y) := by
  let W : CMatrix (A × B) :=
    ((Matrix.UnitaryGroup.onProdLeft (B := B) U :
        Matrix.unitaryGroup (A × B) ℂ) :
      CMatrix (A × B))
  calc
    (M * Matrix.conjTranspose W) (a, b) (x, b') =
        star ((W * star M) (x, b') (a, b)) := by
      rw [← Matrix.star_eq_conjTranspose]
      conv_lhs => rw [← star_star M]
      rw [← star_mul]
      rfl
    _ = star
        (∑ y, (U : CMatrix A) x y * (star M) (y, b') (a, b)) := by
      rw [unitaryOnProdLeft_mul_apply]
    _ = _ := by
      simp [Matrix.star_apply, mul_comm]

private theorem unitaryConjugate_onProdLeft_diag_apply
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (U : Matrix.unitaryGroup A ℂ) (rho : State (A × B))
    (a : A) (b b' : B) :
    (rho.unitaryConjugate
        (Matrix.UnitaryGroup.onProdLeft (B := B) U)).matrix
          (a, b) (a, b') =
      ∑ x, ∑ y, (U : CMatrix A) a x *
        rho.matrix (x, b) (y, b') * star ((U : CMatrix A) a y) := by
  change
    ((((Matrix.UnitaryGroup.onProdLeft (B := B) U :
          Matrix.unitaryGroup (A × B) ℂ) :
          CMatrix (A × B)) *
        rho.matrix *
          Matrix.conjTranspose
            ((Matrix.UnitaryGroup.onProdLeft (B := B) U :
                Matrix.unitaryGroup (A × B) ℂ) :
              CMatrix (A × B))) (a, b) (a, b')) = _
  rw [mul_unitaryOnProdLeft_conjTranspose_apply]
  simp_rw [unitaryOnProdLeft_mul_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem sum_unitary_mul_star_unitary
    {A : Type u} [Fintype A] [DecidableEq A]
    (U : Matrix.unitaryGroup A ℂ) (i j : A) :
    ∑ a, (U : CMatrix A) a i * star ((U : CMatrix A) a j) =
      if i = j then 1 else 0 := by
  have hunit : star (U : CMatrix A) * (U : CMatrix A) = 1 :=
    Unitary.coe_star_mul_self U
  have h := congrArg (fun M : CMatrix A => M j i) hunit
  dsimp only at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.star_apply, Matrix.one_apply] at h
  simpa [mul_comm, eq_comm] using h

/-- A local unitary on the traced-out factor leaves the complementary density
state unchanged. -/
theorem State.unitaryConjugate_onProdLeft_marginalB
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (U : Matrix.unitaryGroup A ℂ) (rho : State (A × B)) :
    (rho.unitaryConjugate
        (Matrix.UnitaryGroup.onProdLeft (B := B) U)).marginalB =
      rho.marginalB := by
  apply State.ext
  rw [State.marginalB_matrix, State.marginalB_matrix]
  ext b b'
  simp only [partialTraceA]
  simp_rw [unitaryConjugate_onProdLeft_diag_apply]
  calc
    (∑ a, ∑ x, ∑ y,
        (U : CMatrix A) a x * rho.matrix (x, b) (y, b') *
          star ((U : CMatrix A) a y)) =
        ∑ x, ∑ y, rho.matrix (x, b) (y, b') *
          ∑ a, (U : CMatrix A) a x * star ((U : CMatrix A) a y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ i, rho.matrix (i, b) (i, b') := by
      simp_rw [sum_unitary_mul_star_unitary]
      simp

/-- Averaging any finite family of local unitaries on the left factor still
leaves the right marginal unchanged. -/
theorem State.classicalExtension_unitaryConjugate_onProdLeft_marginalA_marginalB
    {A : Type u} {B : Type v} {ι : Type w}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (U : ι → Matrix.unitaryGroup A ℂ) (rho : State (A × B)) :
    ((State.classicalExtension p
      (fun i => rho.unitaryConjugate
        (Matrix.UnitaryGroup.onProdLeft (B := B) (U i))) hp hsum).marginalA
        |>.marginalB) = rho.marginalB := by
  let sigma : ι → State (A × B) := fun i =>
    rho.unitaryConjugate
      (Matrix.UnitaryGroup.onProdLeft (B := B) (U i))
  let avg : State (A × B) :=
    (State.classicalExtension p sigma hp hsum).marginalA
  apply State.ext
  calc
    avg.marginalB.matrix =
        ∑ i, (p i : ℂ) • (sigma i).marginalB.matrix :=
      State.marginalB_matrix_eq_sum_smul_of_matrix_eq_sum_smul
        p sigma avg
          (State.classicalExtension_marginalA_matrix p sigma hp hsum)
    _ = ∑ i, (p i : ℂ) • rho.marginalB.matrix := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show (sigma i).marginalB = rho.marginalB by
        exact State.unitaryConjugate_onProdLeft_marginalB (U i) rho]
    _ = rho.marginalB.matrix := by
      rw [← Finset.sum_smul]
      have hsumC : ∑ i, (p i : ℂ) = 1 := by
        exact_mod_cast hsum
      rw [hsumC, one_smul]

/-- Unitary conjugation preserves the ordered eigenvalue family selected by
the finite Hermitian spectral theorem. -/
theorem State.unitaryConjugate_eigenvalues
    {X : Type u} [Fintype X] [DecidableEq X]
    (U : Matrix.unitaryGroup X ℂ) (rho : State X) :
    (rho.unitaryConjugate U).pos.isHermitian.eigenvalues =
      rho.pos.isHermitian.eigenvalues := by
  apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).2
  calc
    (rho.unitaryConjugate U).matrix.charpoly =
        (Matrix.conjTranspose (U : CMatrix X) *
          ((U : CMatrix X) * rho.matrix)).charpoly := by
      exact Matrix.charpoly_mul_comm _ _
    _ = rho.matrix.charpoly := by
      rw [← Matrix.mul_assoc]
      rw [show
        Matrix.conjTranspose (U : CMatrix X) * (U : CMatrix X) = 1 by
          simpa [Matrix.star_eq_conjTranspose] using
            Matrix.UnitaryGroup.star_mul_self U]
      simp

/-- The spectral matrix logarithm is equivariant under unitary conjugation. -/
theorem State.spectralLogMatrix_unitaryConjugate
    {X : Type u} [Fintype X] [DecidableEq X]
    (U : Matrix.unitaryGroup X ℂ) (rho : State X) :
    (rho.unitaryConjugate U).spectralLogMatrix =
      (U : CMatrix X) * rho.spectralLogMatrix *
        Matrix.conjTranspose (U : CMatrix X) := by
  let phi : CMatrix X →⋆ₐ[ℂ] CMatrix X :=
    Unitary.conjStarAlgAut ℂ (CMatrix X) U
  have hspec : (spectrum ℝ rho.matrix).Finite := by
    rw [rho.pos.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  have hphi : Continuous phi := by
    change Continuous (fun A : CMatrix X =>
      (U : CMatrix X) * A * star (U : CMatrix X))
    fun_prop
  have hmap :
      phi (cfc Real.log rho.matrix) =
        cfc Real.log (phi rho.matrix) :=
    phi.map_cfc Real.log rho.matrix
      (hf := hspec.continuousOn _) (hφ := hphi)
      (ha := rho.pos.isHermitian) (hφa := by
        change (rho.unitaryConjugate U).matrix.IsHermitian
        exact (rho.unitaryConjugate U).pos.isHermitian)
  unfold State.spectralLogMatrix
  calc
    (rho.unitaryConjugate U).pos.isHermitian.cfc Real.log =
        cfc Real.log (rho.unitaryConjugate U).matrix :=
      ((rho.unitaryConjugate U).pos.isHermitian.cfc_eq Real.log).symm
    _ = cfc Real.log (phi rho.matrix) := rfl
    _ = phi (cfc Real.log rho.matrix) := hmap.symm
    _ = phi (rho.pos.isHermitian.cfc Real.log) := by
      rw [rho.pos.isHermitian.cfc_eq]
    _ = (U : CMatrix X) * rho.pos.isHermitian.cfc Real.log *
        Matrix.conjTranspose (U : CMatrix X) := rfl

/-- Simultaneous unitary conjugation leaves finite spectral relative entropy
unchanged, supplying the invariance ingredient for a twirling proof. -/
theorem State.spectralRelativeEntropy_unitaryConjugate
    {X : Type u} [Fintype X] [DecidableEq X]
    (U : Matrix.unitaryGroup X ℂ) (rho sigma : State X) :
    (rho.unitaryConjugate U).spectralRelativeEntropy
        (sigma.unitaryConjugate U) =
      rho.spectralRelativeEntropy sigma := by
  rw [State.spectralRelativeEntropy_eq_spectral_sum_sub_trace,
    State.spectralRelativeEntropy_eq_spectral_sum_sub_trace]
  rw [State.unitaryConjugate_eigenvalues,
    State.spectralLogMatrix_unitaryConjugate]
  congr 1
  apply congrArg Complex.re
  have hUstarU :
      Matrix.conjTranspose (U : CMatrix X) * (U : CMatrix X) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.UnitaryGroup.star_mul_self U
  calc
    ((rho.unitaryConjugate U).matrix *
        ((U : CMatrix X) * sigma.spectralLogMatrix *
          Matrix.conjTranspose (U : CMatrix X))).trace =
        ((U : CMatrix X) *
          (rho.matrix * sigma.spectralLogMatrix) *
            Matrix.conjTranspose (U : CMatrix X)).trace := by
      congr 1
      change
        ((U : CMatrix X) * rho.matrix *
            Matrix.conjTranspose (U : CMatrix X)) *
            ((U : CMatrix X) * sigma.spectralLogMatrix *
              Matrix.conjTranspose (U : CMatrix X)) = _
      calc
        _ = (U : CMatrix X) * rho.matrix *
            (Matrix.conjTranspose (U : CMatrix X) * (U : CMatrix X)) *
              sigma.spectralLogMatrix *
                Matrix.conjTranspose (U : CMatrix X) := by
          noncomm_ring
        _ = _ := by
          rw [hUstarU]
          simp
          noncomm_ring
    _ = (Matrix.conjTranspose (U : CMatrix X) * (U : CMatrix X) *
        (rho.matrix * sigma.spectralLogMatrix)).trace := by
      rw [Matrix.trace_mul_cycle]
    _ = (rho.matrix * sigma.spectralLogMatrix).trace := by
      rw [hUstarU, one_mul]

/-- Assuming positive-definite joint convexity for one finite ensemble,
spectral relative entropy contracts under its corresponding mixed-unitary
average.  This isolates the analytic joint-convexity input from the finite
twirling reduction used toward partial-trace data processing. -/
theorem State.spectralRelativeEntropy_mixedUnitary_average_le_of_joint_convex
    {X : Type u} {ι : Type v}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (rho sigma : State X) (hsigma : sigma.matrix.PosDef)
    (U : ι → Matrix.unitaryGroup X ℂ)
    (hjoint :
      ∀ (tau omega : ι → State X),
        (∀ i, (omega i).matrix.PosDef) →
        ((State.classicalExtension p tau hp hsum).marginalA
              |>.spectralRelativeEntropy
                (State.classicalExtension p omega hp hsum).marginalA) ≤
          ∑ i, p i * (tau i).spectralRelativeEntropy (omega i)) :
    ((State.classicalExtension p
          (fun i => rho.unitaryConjugate (U i)) hp hsum).marginalA
        |>.spectralRelativeEntropy
          (State.classicalExtension p
            (fun i => sigma.unitaryConjugate (U i)) hp hsum).marginalA) ≤
      rho.spectralRelativeEntropy sigma := by
  calc
    _ ≤ ∑ i, p i *
        (rho.unitaryConjugate (U i)).spectralRelativeEntropy
          (sigma.unitaryConjugate (U i)) :=
      hjoint (fun i => rho.unitaryConjugate (U i))
        (fun i => sigma.unitaryConjugate (U i))
        (fun i => State.unitaryConjugate_posDef (U i) sigma hsigma)
    _ = ∑ i, p i * rho.spectralRelativeEntropy sigma := by
      apply Finset.sum_congr rfl
      intro i _
      rw [State.spectralRelativeEntropy_unitaryConjugate]
    _ = rho.spectralRelativeEntropy sigma := by
      rw [← Finset.sum_mul, hsum, one_mul]

/-- With the first density state fixed, positive-definite spectral relative
entropy is convex in a finite ensemble of reference states. -/
theorem State.spectralRelativeEntropy_convex_reference
    {X : Type u} {ι : Type v}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (rho : State X) (p : ι → ℝ) (sigma : ι → State X)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hsigma : ∀ i, (sigma i).matrix.PosDef) :
    rho.spectralRelativeEntropy
        (State.classicalExtension p sigma hp hsum).marginalA ≤
      ∑ i, p i * rho.spectralRelativeEntropy (sigma i) := by
  classical
  let avg : State X :=
    (State.classicalExtension p sigma hp hsum).marginalA
  have havgMatrix :
      avg.matrix = ∑ i, p i • (sigma i).matrix :=
    State.classicalExtension_marginalA_matrix p sigma hp hsum
  have hjensen :
      (∑ i, p i • CFC.log (sigma i).matrix) ≤
        CFC.log (∑ i, p i • (sigma i).matrix) :=
    CFC.concaveOn_log.le_map_sum
      (t := Finset.univ) (w := p)
      (p := fun i => (sigma i).matrix)
      (fun i _ => hp i) hsum
      (fun i _ => (hsigma i).isStrictlyPositive)
  have hlog :
      (∑ i, p i • (sigma i).spectralLogMatrix) ≤
        avg.spectralLogMatrix := by
    calc
      (∑ i, p i • (sigma i).spectralLogMatrix) =
          ∑ i, p i • CFC.log (sigma i).matrix := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        unfold State.spectralLogMatrix
        calc
          (sigma i).pos.isHermitian.cfc Real.log =
              cfc Real.log (sigma i).matrix :=
            ((sigma i).pos.isHermitian.cfc_eq Real.log).symm
          _ = CFC.log (sigma i).matrix := rfl
      _ ≤ CFC.log (∑ i, p i • (sigma i).matrix) := hjensen
      _ = CFC.log avg.matrix :=
        congrArg CFC.log havgMatrix.symm
      _ = avg.spectralLogMatrix := by
        unfold State.spectralLogMatrix
        exact avg.pos.isHermitian.cfc_eq Real.log
  have hpair :=
    Matrix.PosSemidef.re_trace_mul_mono_right rho.pos hlog
  have hpairSum :
      Complex.re
          ((rho.matrix *
            ∑ i, p i • (sigma i).spectralLogMatrix).trace) =
        ∑ i, p i * Complex.re
          ((rho.matrix * (sigma i).spectralLogMatrix).trace) := by
    simp [Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_smul,
      Complex.real_smul]
  rw [hpairSum] at hpair
  simp_rw [State.spectralRelativeEntropy_eq_spectral_sum_sub_trace]
  let entropyTerm : ℝ := ∑ i,
    let x := rho.pos.isHermitian.eigenvalues i
    x * Real.log x
  change
    entropyTerm -
        Complex.re ((rho.matrix * avg.spectralLogMatrix).trace) ≤
      ∑ i, p i *
        (entropyTerm -
          Complex.re
            ((rho.matrix * (sigma i).spectralLogMatrix).trace))
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  linarith

/-! ## Project-local Mathlib supplement — Gibbs variational principle -/

/-- The exponential of a finite Hermitian complex matrix is positive
definite, supplying the full-rank Gibbs reference used below. -/
theorem Matrix.IsHermitian.normedSpace_exp_posDef
    {X : Type u} [Fintype X] [DecidableEq X]
    {H : CMatrix X} (hH : H.IsHermitian) :
    (NormedSpace.exp H).PosDef := by
  rw [← Matrix.isStrictlyPositive_iff_posDef]
  refine ⟨hH.isSelfAdjoint.exp_nonneg, ?_⟩
  rw [isUnit_iff_exists_inv]
  refine ⟨NormedSpace.exp (-H), ?_⟩
  calc
    NormedSpace.exp H * NormedSpace.exp (-H) =
        NormedSpace.exp (H + (-H)) :=
      (Matrix.exp_add_of_commute H (-H)
        (Commute.neg_right (Commute.refl H))).symm
    _ = 1 := by simp

/-- The normalized matrix exponential of a finite Hermitian matrix, regarded
as a density state. -/
def Matrix.IsHermitian.gibbsState
    {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
    {H : CMatrix X} (hH : H.IsHermitian) : State X where
  matrix := ((NormedSpace.exp H).trace.re)⁻¹ • NormedSpace.exp H
  pos := by
    exact ((Matrix.IsHermitian.normedSpace_exp_posDef hH).posSemidef.smul
      (inv_nonneg.mpr
        ((Complex.pos_iff.mp
          (Matrix.IsHermitian.normedSpace_exp_posDef hH).trace_pos).1.le)))
  trace_eq_one := by
    have htrace :
        (((NormedSpace.exp H).trace.re : ℝ) : ℂ) =
          (NormedSpace.exp H).trace := by
      rw [(hH.exp).trace_eq_sum_eigenvalues]
      simp
    have htracePos : 0 < (NormedSpace.exp H).trace.re :=
      (Complex.pos_iff.mp
        (Matrix.IsHermitian.normedSpace_exp_posDef hH).trace_pos).1
    rw [Matrix.trace_smul]
    calc
      ((NormedSpace.exp H).trace.re)⁻¹ •
          (NormedSpace.exp H).trace =
          ((NormedSpace.exp H).trace.re)⁻¹ •
            (((NormedSpace.exp H).trace.re : ℝ) : ℂ) := by
        rw [htrace]
      _ = 1 := by
        rw [Complex.real_smul]
        norm_cast
        exact inv_mul_cancel₀ htracePos.ne'

/-- The normalized exponential Gibbs state is itself strictly positive
definite. -/
theorem Matrix.IsHermitian.gibbsState_matrix_posDef
    {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
    {H : CMatrix X} (hH : H.IsHermitian) :
    (Matrix.IsHermitian.gibbsState hH).matrix.PosDef := by
  change (((NormedSpace.exp H).trace.re)⁻¹ • NormedSpace.exp H).PosDef
  exact (Matrix.IsHermitian.normedSpace_exp_posDef hH).smul
    (inv_pos.mpr
      (Complex.pos_iff.mp
        (Matrix.IsHermitian.normedSpace_exp_posDef hH).trace_pos).1)

/-- The spectral logarithm of a Gibbs state is its Hamiltonian shifted by the
logarithm of the partition function. -/
theorem Matrix.IsHermitian.gibbsState_spectralLogMatrix
    {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
    {H : CMatrix X} (hH : H.IsHermitian) :
    (Matrix.IsHermitian.gibbsState hH).spectralLogMatrix =
      H - Real.log (NormedSpace.exp H).trace.re • (1 : CMatrix X) := by
  let Z : ℝ := (NormedSpace.exp H).trace.re
  have hZ : 0 < Z :=
    (Complex.pos_iff.mp
      (Matrix.IsHermitian.normedSpace_exp_posDef hH).trace_pos).1
  have hlogexp : CFC.log (NormedSpace.exp H) = H :=
    CFC.log_exp H hH.isSelfAdjoint
  calc
    (Matrix.IsHermitian.gibbsState hH).spectralLogMatrix =
        CFC.log (Matrix.IsHermitian.gibbsState hH).matrix := by
      unfold State.spectralLogMatrix
      exact
        ((Matrix.IsHermitian.gibbsState hH).pos.isHermitian.cfc_eq
          Real.log).symm
    _ = CFC.log (Z⁻¹ • NormedSpace.exp H) := by rfl
    _ = (algebraMap ℝ (CMatrix X)) (Real.log Z⁻¹) +
          CFC.log (NormedSpace.exp H) :=
      CFC.log_smul' (NormedSpace.exp H) (inv_pos.mpr hZ)
        (Matrix.IsHermitian.normedSpace_exp_posDef hH).isStrictlyPositive
    _ = H - Real.log Z • (1 : CMatrix X) := by
      rw [hlogexp, Real.log_inv, Algebra.algebraMap_eq_smul_one]
      module

/-- Finite-dimensional Gibbs variational inequality, derived from the
project-local positive-definite Klein inequality. -/
theorem State.gibbs_variational
    {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
    (rho : State X) {H : CMatrix X} (hH : H.IsHermitian) :
    Complex.re ((rho.matrix * H).trace) -
        (∑ i,
          let x := rho.pos.isHermitian.eigenvalues i
          x * Real.log x) ≤
      Real.log (NormedSpace.exp H).trace.re := by
  let gamma : State X := Matrix.IsHermitian.gibbsState hH
  let Z : ℝ := (NormedSpace.exp H).trace.re
  have hgamma : gamma.matrix.PosDef :=
    Matrix.IsHermitian.gibbsState_matrix_posDef hH
  have hloggamma :
      gamma.spectralLogMatrix =
        H - Real.log Z • (1 : CMatrix X) :=
    Matrix.IsHermitian.gibbsState_spectralLogMatrix hH
  have hpair :
      Complex.re ((rho.matrix * gamma.spectralLogMatrix).trace) =
        Complex.re ((rho.matrix * H).trace) - Real.log Z := by
    rw [hloggamma]
    simp [mul_sub, Matrix.trace_sub, Matrix.trace_smul,
      Complex.real_smul, rho.trace_eq_one]
  have hnonneg :=
    State.spectralRelativeEntropy_nonneg_of_posDef rho gamma hgamma
  rw [State.spectralRelativeEntropy_eq_spectral_sum_sub_trace,
    hpair] at hnonneg
  linarith

/-- A unit trace-exponential bound converts the Gibbs variational principle
into the entropy inequality needed by trace-exponential proofs of strong
subadditivity. -/
theorem State.re_trace_mul_le_spectral_sum_of_exp_trace_le_one
    {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
    (rho : State X) {H : CMatrix X} (hH : H.IsHermitian)
    (htrace : (NormedSpace.exp H).trace.re ≤ 1) :
    Complex.re ((rho.matrix * H).trace) ≤
      ∑ i,
        let x := rho.pos.isHermitian.eigenvalues i
        x * Real.log x := by
  have hZ : 0 ≤ (NormedSpace.exp H).trace.re :=
    (Complex.pos_iff.mp
      (Matrix.IsHermitian.normedSpace_exp_posDef hH).trace_pos).1.le
  have hlog : Real.log (NormedSpace.exp H).trace.re ≤ 0 :=
    Real.log_nonpos hZ htrace
  have hvariational := State.gibbs_variational rho hH
  linarith

/-! ## Project-local Mathlib supplement — Resolvent normalization -/

private theorem integrableOn_sq_div_add_sq
    {a : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => a ^ 2 / (a + t) ^ 2) (Set.Ioi 0) := by
  let g : ℝ → ℝ := fun t => -(a ^ 2 / (a + t))
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt g (a ^ 2 / (a + t) ^ 2) t := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    have hden : a + t ≠ 0 := ne_of_gt (by linarith)
    convert
      (((hasDerivAt_const t (a ^ 2)).div
        ((hasDerivAt_const t a).add (hasDerivAt_id t))
        hden).neg) using 1 <;>
      dsimp [g] <;> field_simp [hden] <;> ring
  have hnonneg : ∀ t ∈ Set.Ioi (0 : ℝ),
      0 ≤ a ^ 2 / (a + t) ^ 2 := by
    intro t ht
    positivity
  have htendsto : Filter.Tendsto g Filter.atTop (nhds 0) := by
    dsimp [g]
    have hden : Filter.Tendsto (fun t : ℝ => a + t)
        Filter.atTop Filter.atTop :=
      tendsto_const_nhds.add_atTop Filter.tendsto_id
    simpa only [neg_zero] using
      (tendsto_const_nhds.div_atTop hden).neg
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    hderiv hnonneg htendsto

/-- The scalar resolvent-square integral used in the three-matrix
specialization of Lieb's trace inequality. -/
theorem integral_sq_div_add_sq
    {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ in Set.Ioi 0, a ^ 2 / (a + t) ^ 2 = a := by
  let g : ℝ → ℝ := fun t => -(a ^ 2 / (a + t))
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt g (a ^ 2 / (a + t) ^ 2) t := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    have hden : a + t ≠ 0 := ne_of_gt (by linarith)
    convert
      (((hasDerivAt_const t (a ^ 2)).div
        ((hasDerivAt_const t a).add (hasDerivAt_id t))
        hden).neg) using 1 <;>
      dsimp [g] <;> field_simp [hden] <;> ring
  have hnonneg : ∀ t ∈ Set.Ioi (0 : ℝ),
      0 ≤ a ^ 2 / (a + t) ^ 2 := by
    intro t ht
    positivity
  have htendsto : Filter.Tendsto g Filter.atTop (nhds 0) := by
    dsimp [g]
    have hden : Filter.Tendsto (fun t : ℝ => a + t)
        Filter.atTop Filter.atTop :=
      tendsto_const_nhds.add_atTop Filter.tendsto_id
    simpa only [neg_zero] using
      (tendsto_const_nhds.div_atTop hden).neg
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    hderiv hnonneg htendsto]
  dsimp [g]
  field_simp [ha.ne']
  ring

/-- The trace of a Hermitian matrix squared against two copies of a real
functional calculus is the corresponding eigenvalue sum. -/
theorem Matrix.IsHermitian.re_trace_self_mul_cfc_sq
    {X : Type u} [Fintype X] [DecidableEq X]
    {M : CMatrix X} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    Complex.re ((M * M * hM.cfc f * hM.cfc f).trace) =
      ∑ i, hM.eigenvalues i ^ 2 * (f (hM.eigenvalues i)) ^ 2 := by
  let U := hM.eigenvectorUnitary
  let D : CMatrix X :=
    Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ))
  let R : CMatrix X :=
    Matrix.diagonal (fun i => (f (hM.eigenvalues i) : ℂ))
  have hUstarU : star (U : CMatrix X) * (U : CMatrix X) = 1 :=
    Unitary.coe_star_mul_self U
  have hMspec : M = (U : CMatrix X) * D * star (U : CMatrix X) :=
    hM.spectral_theorem
  have hRspec : hM.cfc f =
      (U : CMatrix X) * R * star (U : CMatrix X) := by
    rfl
  have hprod :
      M * M * hM.cfc f * hM.cfc f =
        (U : CMatrix X) * (D * D * R * R) * star (U : CMatrix X) := by
    rw [hRspec, hMspec]
    calc
      _ = (U : CMatrix X) * D *
          (star (U : CMatrix X) * (U : CMatrix X)) * D *
          (star (U : CMatrix X) * (U : CMatrix X)) * R *
          (star (U : CMatrix X) * (U : CMatrix X)) * R *
          star (U : CMatrix X) := by noncomm_ring
      _ = _ := by
        rw [hUstarU]
        simp
        noncomm_ring
  rw [hprod, Matrix.trace_mul_cycle, hUstarU, one_mul]
  simp [D, R, Matrix.trace, Complex.mul_re]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- For a positive-definite matrix, the spectral resolvent is its ordinary
matrix resolvent at every nonnegative scalar. -/
theorem Matrix.PosDef.cfc_inv_add_smul_one
    {X : Type u} [Fintype X] [DecidableEq X]
    {M : CMatrix X} (hM : M.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    hM.isHermitian.cfc (fun x => (x + t)⁻¹) =
      (M + t • (1 : CMatrix X))⁻¹ := by
  have hnonzero : ∀ x ∈ spectrum ℝ M, x + t ≠ 0 := by
    intro x hx
    rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ne_of_gt
      (add_pos_of_pos_of_nonneg (hM.eigenvalues_pos i) ht)
  calc
    hM.isHermitian.cfc (fun x => (x + t)⁻¹) =
        cfc (fun x => (x + t)⁻¹) M :=
      (hM.isHermitian.cfc_eq _).symm
    _ = Ring.inverse (cfc (fun x => x + t) M) :=
      cfc_inv (fun x : ℝ => x + t) M hnonzero (by fun_prop)
        hM.isHermitian.isSelfAdjoint
    _ = Ring.inverse (M + t • (1 : CMatrix X)) := by
      congr 1
      rw [cfc_add_const t (fun x : ℝ => x) M, cfc_id' ℝ M,
        Algebra.algebraMap_eq_smul_one]
    _ = (M + t • (1 : CMatrix X))⁻¹ := by
      rw [Matrix.nonsing_inv_eq_ringInverse]

/-- A positive-definite matrix commutes with every nonnegative scalar
resolvent of itself. -/
theorem Matrix.PosDef.commute_inv_add_smul_one
    {X : Type u} [Fintype X] [DecidableEq X]
    {M : CMatrix X} (hM : M.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    Commute M (M + t • (1 : CMatrix X))⁻¹ := by
  rw [← Matrix.PosDef.cfc_inv_add_smul_one hM t ht]
  rw [← hM.isHermitian.cfc_eq]
  exact
    (hM.isHermitian.isSelfAdjoint.commute_cfc
      (Commute.refl M) (fun x : ℝ => (x + t)⁻¹)).symm

private theorem State.integral_sum_eigenvalue_resolvent_sq
    {X : Type u} [Fintype X] [DecidableEq X]
    (rho : State X) (hrho : rho.matrix.PosDef) :
    ∫ t : ℝ in Set.Ioi 0,
      ∑ i, rho.pos.isHermitian.eigenvalues i ^ 2 /
        (rho.pos.isHermitian.eigenvalues i + t) ^ 2 = 1 := by
  rw [MeasureTheory.integral_finsetSum Finset.univ]
  · simp_rw [integral_sq_div_add_sq (hrho.eigenvalues_pos _)]
    exact State.sum_eigenvalues_eq_one rho
  · intro i hi
    exact integrableOn_sq_div_add_sq (hrho.eigenvalues_pos i)

private theorem State.integral_re_trace_self_mul_spectralResolvent_sq
    {X : Type u} [Fintype X] [DecidableEq X]
    (rho : State X) (hrho : rho.matrix.PosDef) :
    ∫ t : ℝ in Set.Ioi 0,
      Complex.re
        ((rho.matrix * rho.matrix *
          rho.pos.isHermitian.cfc (fun x => (x + t)⁻¹) *
          rho.pos.isHermitian.cfc (fun x => (x + t)⁻¹)).trace) = 1 := by
  have hpoint (t : ℝ) :
      Complex.re
          ((rho.matrix * rho.matrix *
            rho.pos.isHermitian.cfc (fun x => (x + t)⁻¹) *
            rho.pos.isHermitian.cfc (fun x => (x + t)⁻¹)).trace) =
        ∑ i, rho.pos.isHermitian.eigenvalues i ^ 2 /
          (rho.pos.isHermitian.eigenvalues i + t) ^ 2 := by
    rw [Matrix.IsHermitian.re_trace_self_mul_cfc_sq]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [div_eq_mul_inv]
    rw [inv_pow]
  simp_rw [hpoint]
  exact State.integral_sum_eigenvalue_resolvent_sq rho hrho

/-- The resolvent expression on the right side of the density-matrix
specialization of Lieb's three-matrix inequality integrates to one. -/
theorem State.integral_re_trace_self_mul_resolvent_sq
    {X : Type u} [Fintype X] [DecidableEq X]
    (rho : State X) (hrho : rho.matrix.PosDef) :
    ∫ t : ℝ in Set.Ioi 0,
      Complex.re
        ((rho.matrix * rho.matrix *
          (rho.matrix + t • (1 : CMatrix X))⁻¹ *
          (rho.matrix + t • (1 : CMatrix X))⁻¹).trace) = 1 := by
  calc
    _ = ∫ t : ℝ in Set.Ioi 0,
        Complex.re
          ((rho.matrix * rho.matrix *
            rho.pos.isHermitian.cfc (fun x => (x + t)⁻¹) *
            rho.pos.isHermitian.cfc (fun x => (x + t)⁻¹)).trace) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Matrix.PosDef.cfc_inv_add_smul_one hrho t ht.le]
    _ = 1 :=
      State.integral_re_trace_self_mul_spectralResolvent_sq rho hrho

end

end QITBench
