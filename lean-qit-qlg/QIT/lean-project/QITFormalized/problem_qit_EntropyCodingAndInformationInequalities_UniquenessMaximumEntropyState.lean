import QITBench.Base.OneShot
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Uniqueness of the maximum-entropy state

This file models a `d`-dimensional Hilbert space by the standard finite basis
`Fin d`.  It records the random-unitary twirl, the strict concavity ingredient,
the strict entropy bound away from the completely mixed state, and uniqueness
of the maximum-entropy state.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace QITFormalized.UniquenessMaximumEntropyState

open QITBench

noncomputable section

/-- The completely mixed state `Id / d` on a `d`-dimensional Hilbert space. -/
noncomputable def maximallyMixedState (d : ℕ) [NeZero d] : State (Fin d) where
  matrix := ((d : ℝ)⁻¹) • (1 : CMatrix (Fin d))
  pos := Matrix.PosSemidef.one.smul (by positivity)
  trace_eq_one := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    simp [NeZero.ne d]

/-- Conjugation of a density state by a unitary matrix. -/
noncomputable def unitaryConjugate
    {a : Type*} [Fintype a] [DecidableEq a]
    (U : Matrix.unitaryGroup a ℂ) (rho : State a) : State a where
  matrix := (U : CMatrix a) * rho.matrix *
    Matrix.conjTranspose (U : CMatrix a)
  pos := rho.pos.mul_mul_conjTranspose_same (U : CMatrix a)
  trace_eq_one := by
    calc
      ((U : CMatrix a) * rho.matrix *
          Matrix.conjTranspose (U : CMatrix a)).trace =
          (Matrix.conjTranspose (U : CMatrix a) *
            (U : CMatrix a) * rho.matrix).trace := by
            rw [Matrix.trace_mul_cycle]
      _ = rho.matrix.trace := by
        rw [show Matrix.conjTranspose (U : CMatrix a) *
            (U : CMatrix a) = 1 by
          simpa [Matrix.star_eq_conjTranspose] using
            Matrix.UnitaryGroup.star_mul_self U]
        simp
      _ = 1 := rho.trace_eq_one

/-- A binary convex combination of density states. -/
noncomputable def convexCombination
    {a : Type*} [Fintype a] [DecidableEq a]
    (t : ℝ) (rho sigma : State a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    State a where
  matrix := t • rho.matrix + (1 - t) • sigma.matrix
  pos := (rho.pos.smul ht0).add (sigma.pos.smul (sub_nonneg.mpr ht1))
  trace_eq_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      rho.trace_eq_one, sigma.trace_eq_one]
    norm_num

/-- Base-2 von Neumann entropy, namely the Shannon entropy of the eigenvalues
of a density operator (with Mathlib's convention `log 0 = 0`). -/
noncomputable def vonNeumannEntropy
    {a : Type*} [Fintype a] [DecidableEq a] (rho : State a) : ℝ :=
  QITBench.OneShot.schmidtEntropy rho.pos.isHermitian.eigenvalues

private lemma schmidtEntropy_eq_sum_negMulLog
    {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    QITBench.OneShot.schmidtEntropy p =
      (∑ i, Real.negMulLog (p i)) / Real.log 2 := by
  unfold QITBench.OneShot.schmidtEntropy QITBench.OneShot.log2
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.negMulLog]
  ring

private lemma sum_negMulLog_le_log_card
    (n : ℕ) [NeZero n] (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∑ i, Real.negMulLog (p i) ≤ Real.log (n : ℝ) := by
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast NeZero.pos n
  have hj := Real.strictConcaveOn_negMulLog.concaveOn.le_map_sum
    (t := Finset.univ) (w := fun _ : Fin n => (n : ℝ)⁻¹) (p := p)
    (fun _ _ => inv_nonneg.mpr hn.le)
    (by simp [hn.ne'])
    (fun i _ => hp i)
  have hj' : (n : ℝ)⁻¹ * (∑ i, Real.negMulLog (p i)) ≤
      Real.negMulLog ((n : ℝ)⁻¹) := by
    simpa [smul_eq_mul, ← Finset.mul_sum, hsum] using hj
  have hval :
      Real.negMulLog ((n : ℝ)⁻¹) =
        (n : ℝ)⁻¹ * Real.log (n : ℝ) := by
    rw [Real.negMulLog, Real.log_inv]
    ring
  rw [hval] at hj'
  exact (mul_le_mul_iff_of_pos_left (inv_pos.mpr hn)).mp hj'

private lemma sum_negMulLog_lt_log_card
    (n : ℕ) [NeZero n] (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hne : p ≠ fun _ => (n : ℝ)⁻¹) :
    ∑ i, Real.negMulLog (p i) < Real.log (n : ℝ) := by
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast NeZero.pos n
  have hpairs : ∃ j ∈ (Finset.univ : Finset (Fin n)),
      ∃ k ∈ (Finset.univ : Finset (Fin n)), p j ≠ p k := by
    by_contra h
    push Not at h
    let k : Fin n := ⟨0, NeZero.pos n⟩
    have hconst : ∀ j, p j = p k :=
      fun j => h j (Finset.mem_univ j) k (Finset.mem_univ k)
    have hsum' : (n : ℝ) * p k = 1 := by
      simpa [hconst] using hsum
    apply hne
    funext j
    rw [hconst]
    exact eq_inv_of_mul_eq_one_right hsum'
  have hj := Real.strictConcaveOn_negMulLog.lt_map_sum
    (t := Finset.univ) (w := fun _ : Fin n => (n : ℝ)⁻¹) (p := p)
    (fun _ _ => inv_pos.mpr hn)
    (by simp [hn.ne'])
    (fun i _ => hp i)
    hpairs
  have hj' : (n : ℝ)⁻¹ * (∑ i, Real.negMulLog (p i)) <
      Real.negMulLog ((n : ℝ)⁻¹) := by
    simpa [smul_eq_mul, ← Finset.mul_sum, hsum] using hj
  have hval :
      Real.negMulLog ((n : ℝ)⁻¹) =
        (n : ℝ)⁻¹ * Real.log (n : ℝ) := by
    rw [Real.negMulLog, Real.log_inv]
    ring
  rw [hval] at hj'
  exact (mul_lt_mul_iff_of_pos_left (inv_pos.mpr hn)).mp hj'

private lemma state_eigenvalues_sum
    (d : ℕ) [NeZero d] (rho : State (Fin d)) :
    ∑ i, rho.pos.isHermitian.eigenvalues i = 1 := by
  have h := rho.trace_eq_one
  rw [rho.pos.isHermitian.trace_eq_sum_eigenvalues] at h
  have hr := congrArg Complex.re h
  simpa using hr

private lemma state_eq_maximallyMixed_of_eigenvalues_eq
    (d : ℕ) [NeZero d] (rho : State (Fin d))
    (h : rho.pos.isHermitian.eigenvalues = fun _ => (d : ℝ)⁻¹) :
    rho = maximallyMixedState d := by
  apply State.ext
  rw [rho.pos.isHermitian.spectral_theorem, h]
  have hdiag :
      Matrix.diagonal (RCLike.ofReal ∘ fun _ : Fin d => (d : ℝ)⁻¹) =
        ((d : ℝ)⁻¹) • (1 : CMatrix (Fin d)) := by
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  rw [hdiag]
  change ((rho.pos.isHermitian.eigenvectorUnitary : CMatrix (Fin d)) *
      (((d : ℝ)⁻¹) • (1 : CMatrix (Fin d)))) *
      star (rho.pos.isHermitian.eigenvectorUnitary : CMatrix (Fin d)) = _
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hu : (rho.pos.isHermitian.eigenvectorUnitary : CMatrix (Fin d)) *
      star (rho.pos.isHermitian.eigenvectorUnitary : CMatrix (Fin d)) = 1 :=
    Unitary.coe_mul_star_self _
  rw [hu]
  rfl

private lemma maximallyMixedState_eigenvalues
    (d : ℕ) [NeZero d] :
    (maximallyMixedState d).pos.isHermitian.eigenvalues =
      fun _ => (d : ℝ)⁻¹ := by
  funext i
  let hA := (maximallyMixedState d).pos.isHermitian
  have heig := hA.mulVec_eigenvectorBasis i
  change Matrix.mulVec (((d : ℝ)⁻¹) • (1 : CMatrix (Fin d)))
      (⇑(hA.eigenvectorBasis i)) = _ at heig
  rw [Matrix.smul_mulVec, Matrix.one_mulVec] at heig
  have hv : (⇑(hA.eigenvectorBasis i) : Fin d → ℂ) ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 <|
      hA.eigenvectorBasis.orthonormal.ne_zero i
  have hc : (((d : ℝ)⁻¹ : ℝ) : ℂ) =
      ((hA.eigenvalues i : ℝ) : ℂ) :=
    (smul_left_injective ℂ hv) heig
  exact_mod_cast hc.symm

private lemma schmidtEntropy_uniform
    (d : ℕ) [NeZero d] :
    QITBench.OneShot.schmidtEntropy (fun _ : Fin d => (d : ℝ)⁻¹) =
      QITBench.OneShot.log2 (d : ℝ) := by
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne d
  unfold QITBench.OneShot.schmidtEntropy QITBench.OneShot.log2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Real.log_inv]
  field_simp

private lemma state_eigenvalues_unitaryConjugate
    {a : Type*} [Fintype a] [DecidableEq a]
    (U : Matrix.unitaryGroup a ℂ) (rho : State a) :
    (unitaryConjugate U rho).pos.isHermitian.eigenvalues =
      rho.pos.isHermitian.eigenvalues := by
  apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).2
  calc
    ((unitaryConjugate U rho).matrix).charpoly =
        (Matrix.conjTranspose (U : CMatrix a) *
          ((U : CMatrix a) * rho.matrix)).charpoly := by
      exact Matrix.charpoly_mul_comm _ _
    _ = rho.matrix.charpoly := by
      rw [← Matrix.mul_assoc]
      rw [show Matrix.conjTranspose (U : CMatrix a) *
          (U : CMatrix a) = 1 by
        simpa [Matrix.star_eq_conjTranspose] using
          Matrix.UnitaryGroup.star_mul_self U]
      simp

/-- Von Neumann entropy is invariant under unitary conjugation. -/
theorem vonNeumannEntropy_unitaryConjugate
    {a : Type*} [Fintype a] [DecidableEq a]
    (U : Matrix.unitaryGroup a ℂ) (rho : State a) :
    vonNeumannEntropy (unitaryConjugate U rho) =
      vonNeumannEntropy rho := by
  unfold vonNeumannEntropy
  rw [state_eigenvalues_unitaryConjugate]

private noncomputable def permutationUnitary
    {a : Type*} [Fintype a] [DecidableEq a]
    (σ : Equiv.Perm a) : Matrix.unitaryGroup a ℂ := by
  refine ⟨σ.permMatrix ℂ, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

private noncomputable def cyclicEigenUnitary
    (d : ℕ) [NeZero d] (rho : State (Fin d)) (k : Fin d) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  rho.pos.isHermitian.eigenvectorUnitary *
    permutationUnitary (finCycle k) *
      (rho.pos.isHermitian.eigenvectorUnitary)⁻¹

private lemma permMatrix_mul_diagonal_mul_conjTranspose
    {a : Type*} [Fintype a] [DecidableEq a]
    (σ : Equiv.Perm a) (f : a → ℂ) :
    σ.permMatrix ℂ * Matrix.diagonal f *
        Matrix.conjTranspose (σ.permMatrix ℂ) =
      Matrix.diagonal (f ∘ σ) := by
  classical
  ext i j
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (σ i)]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

private lemma cyclicEigenUnitary_conjugation
    (d : ℕ) [NeZero d] (rho : State (Fin d)) (k : Fin d) :
    ((cyclicEigenUnitary d rho k : Matrix.unitaryGroup (Fin d) ℂ) :
        CMatrix (Fin d)) *
          rho.matrix *
            Matrix.conjTranspose
              ((cyclicEigenUnitary d rho k :
                Matrix.unitaryGroup (Fin d) ℂ) : CMatrix (Fin d)) =
      (rho.pos.isHermitian.eigenvectorUnitary : CMatrix (Fin d)) *
        Matrix.diagonal
          (RCLike.ofReal ∘ rho.pos.isHermitian.eigenvalues ∘ finCycle k) *
        star (rho.pos.isHermitian.eigenvectorUnitary :
          CMatrix (Fin d)) := by
  let E := rho.pos.isHermitian.eigenvectorUnitary
  let P := permutationUnitary (finCycle k)
  let D : CMatrix (Fin d) :=
    Matrix.diagonal (RCLike.ofReal ∘ rho.pos.isHermitian.eigenvalues)
  have hEsE : star (E : CMatrix (Fin d)) * (E : CMatrix (Fin d)) = 1 :=
    Unitary.coe_star_mul_self E
  calc
    ((cyclicEigenUnitary d rho k : Matrix.unitaryGroup (Fin d) ℂ) :
          CMatrix (Fin d)) *
            rho.matrix *
              Matrix.conjTranspose
                ((cyclicEigenUnitary d rho k :
                  Matrix.unitaryGroup (Fin d) ℂ) : CMatrix (Fin d)) =
        ((cyclicEigenUnitary d rho k :
            Matrix.unitaryGroup (Fin d) ℂ) : CMatrix (Fin d)) *
          ((E : CMatrix (Fin d)) * D * star (E : CMatrix (Fin d))) *
            Matrix.conjTranspose
              ((cyclicEigenUnitary d rho k :
                Matrix.unitaryGroup (Fin d) ℂ) : CMatrix (Fin d)) := by
      congr 2
      exact rho.pos.isHermitian.spectral_theorem
    _ = _ := by
      change (((E * P * E⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
          CMatrix (Fin d)) *
        ((E : CMatrix (Fin d)) * D * star (E : CMatrix (Fin d))) *
        Matrix.conjTranspose
          (((E * P * E⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
            CMatrix (Fin d)))) = _
      simp only [Submonoid.coe_mul, ← Unitary.star_eq_inv,
        Unitary.coe_star]
      rw [← Matrix.star_eq_conjTranspose]
      simp only [star_mul, star_star, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star (E : CMatrix (Fin d)))
          (E : CMatrix (Fin d)), hEsE, Matrix.one_mul]
      rw [← Matrix.mul_assoc (star (E : CMatrix (Fin d)))
          (E : CMatrix (Fin d)), hEsE, Matrix.one_mul]
      rw [show star (P : CMatrix (Fin d)) =
          Matrix.conjTranspose ((finCycle k).permMatrix ℂ) by rfl]
      rw [show (P : CMatrix (Fin d)) =
          (finCycle k).permMatrix ℂ by rfl]
      rw [← Matrix.mul_assoc ((finCycle k).permMatrix ℂ) D]
      rw [← Matrix.mul_assoc (((finCycle k).permMatrix ℂ) * D)
        (Matrix.conjTranspose ((finCycle k).permMatrix ℂ))
        (star (E : CMatrix (Fin d)))]
      rw [permMatrix_mul_diagonal_mul_conjTranspose]
      rfl

private lemma sum_cyclic_diagonals
    (d : ℕ) [NeZero d] (f : Fin d → ℂ) :
    (∑ k : Fin d, Matrix.diagonal (f ∘ finCycle k)) =
      (∑ x, f x) • (1 : CMatrix (Fin d)) := by
  classical
  ext i j
  rw [Matrix.sum_apply, Matrix.smul_apply]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Function.comp_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one]
    calc
      (∑ k, f (finCycle k i)) = ∑ k, f (finCycle i k) := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        simp [add_comm]
      _ = ∑ x, f x := Equiv.sum_comp (finCycle i) f
  · simp [hij]

private lemma sum_cyclicEigenUnitary_conjugates
    (d : ℕ) [NeZero d] (rho : State (Fin d)) :
    (∑ k : Fin d, (unitaryConjugate
      (cyclicEigenUnitary d rho k) rho).matrix) =
        (1 : CMatrix (Fin d)) := by
  simp_rw [unitaryConjugate, cyclicEigenUnitary_conjugation]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum]
  change ((rho.pos.isHermitian.eigenvectorUnitary : CMatrix (Fin d)) *
      (∑ k : Fin d, Matrix.diagonal
        ((Complex.ofReal ∘ rho.pos.isHermitian.eigenvalues) ∘ finCycle k))) *
      star (rho.pos.isHermitian.eigenvectorUnitary : CMatrix (Fin d)) = 1
  rw [sum_cyclic_diagonals]
  have hsumR := state_eigenvalues_sum d rho
  have hsumC :
      ∑ i, ((rho.pos.isHermitian.eigenvalues i : ℝ) : ℂ) = 1 := by
    exact_mod_cast hsumR
  have hsumC' :
      ∑ i, (Complex.ofReal ∘ rho.pos.isHermitian.eigenvalues) i = 1 := by
    simpa using hsumC
  rw [hsumC']
  simp only [one_smul, Matrix.mul_one]
  exact Unitary.coe_mul_star_self _

private lemma unitary_row_normSq_sum
    {a : Type*} [Fintype a] [DecidableEq a]
    (E : Matrix.unitaryGroup a ℂ) (j : a) :
    ∑ i, Complex.normSq ((E : CMatrix a) j i) = 1 := by
  have hunit : (E : CMatrix a) * star (E : CMatrix a) = 1 :=
    Unitary.coe_mul_star_self E
  have h := congrArg (fun M : CMatrix a => M j j) hunit
  dsimp only at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.star_apply, Matrix.one_apply_eq] at h
  rw [← Complex.ofReal_inj]
  simpa [Complex.normSq_eq_conj_mul_self, mul_comm] using h

private lemma unitary_col_normSq_sum
    {a : Type*} [Fintype a] [DecidableEq a]
    (E : Matrix.unitaryGroup a ℂ) (i : a) :
    ∑ j, Complex.normSq ((E : CMatrix a) j i) = 1 := by
  have hunit : star (E : CMatrix a) * (E : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self E
  have h := congrArg (fun M : CMatrix a => M i i) hunit
  dsimp only at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.star_apply, Matrix.one_apply_eq] at h
  rw [← Complex.ofReal_inj]
  simpa [Complex.normSq_eq_conj_mul_self] using h

private lemma state_diag_re_eq_eigenvalue_average
    {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) (j : a) :
    Complex.re (rho.matrix j j) =
      ∑ i, Complex.normSq
          ((rho.pos.isHermitian.eigenvectorUnitary : CMatrix a) j i) *
        rho.pos.isHermitian.eigenvalues i := by
  let E := rho.pos.isHermitian.eigenvectorUnitary
  let f := rho.pos.isHermitian.eigenvalues
  have hs := rho.pos.isHermitian.spectral_theorem
  have h := congrArg (fun M : CMatrix a => Complex.re (M j j)) hs
  dsimp only at h
  change Complex.re (rho.matrix j j) =
    Complex.re (((E : CMatrix a) *
      Matrix.diagonal (Complex.ofReal ∘ f) *
        star (E : CMatrix a)) j j) at h
  rw [h]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_comm, mul_left_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.normSq_apply]
  dsimp [E, f]
  ring

private lemma state_apply_eq_eigenvalue_sum
    {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) (j k : a) :
    rho.matrix j k =
      ∑ i, (rho.pos.isHermitian.eigenvectorUnitary : CMatrix a) j i *
        (rho.pos.isHermitian.eigenvalues i : ℂ) *
        star ((rho.pos.isHermitian.eigenvectorUnitary : CMatrix a) k i) := by
  let E := rho.pos.isHermitian.eigenvectorUnitary
  let lam := rho.pos.isHermitian.eigenvalues
  have hs := rho.pos.isHermitian.spectral_theorem
  have h := congrArg (fun M : CMatrix a => M j k) hs
  dsimp only at h
  change rho.matrix j k =
    ((E : CMatrix a) * Matrix.diagonal (Complex.ofReal ∘ lam) *
      star (E : CMatrix a)) j k at h
  rw [h]
  simp [Matrix.mul_apply, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [E, lam]

private lemma state_diag_re_nonneg
    {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) (i : a) :
    0 ≤ Complex.re (rho.matrix i i) :=
  (Complex.nonneg_iff.mp rho.pos.diag_nonneg).1

private lemma sum_negMulLog_eigenvalues_le_diagonal
    {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) :
    (∑ i, Real.negMulLog (rho.pos.isHermitian.eigenvalues i)) ≤
      ∑ j, Real.negMulLog (Complex.re (rho.matrix j j)) := by
  let E := rho.pos.isHermitian.eigenvectorUnitary
  let lam := rho.pos.isHermitian.eigenvalues
  have hrow (j : a) :
      (∑ i, Complex.normSq ((E : CMatrix a) j i) •
          Real.negMulLog (lam i)) ≤
        Real.negMulLog (Complex.re (rho.matrix j j)) := by
    have hj := Real.strictConcaveOn_negMulLog.concaveOn.le_map_sum
      (t := Finset.univ)
      (w := fun i : a => Complex.normSq ((E : CMatrix a) j i))
      (p := lam)
      (fun _ _ => Complex.normSq_nonneg _)
      (by simpa using unitary_row_normSq_sum E j)
      (fun i _ => rho.pos.eigenvalues_nonneg i)
    calc
      (∑ i, Complex.normSq ((E : CMatrix a) j i) •
          Real.negMulLog (lam i)) ≤
          Real.negMulLog
            (∑ i, Complex.normSq ((E : CMatrix a) j i) * lam i) := by
        simpa [smul_eq_mul] using hj
      _ = Real.negMulLog (Complex.re (rho.matrix j j)) := by
        rw [state_diag_re_eq_eigenvalue_average]
  calc
    (∑ i, Real.negMulLog (rho.pos.isHermitian.eigenvalues i)) =
        ∑ j, ∑ i, Complex.normSq ((E : CMatrix a) j i) *
          Real.negMulLog (lam i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_mul, unitary_col_normSq_sum]
      simp [lam]
    _ ≤ ∑ j, Real.negMulLog (Complex.re (rho.matrix j j)) := by
      exact Finset.sum_le_sum fun j _ => by
        simpa [smul_eq_mul] using hrow j

private lemma exists_mixed_eigenvalues_of_not_isDiag
    {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) (hdiag : ¬rho.matrix.IsDiag) :
    ∃ j i k,
      Complex.normSq
          ((rho.pos.isHermitian.eigenvectorUnitary : CMatrix a) j i) ≠ 0 ∧
        Complex.normSq
          ((rho.pos.isHermitian.eigenvectorUnitary : CMatrix a) j k) ≠ 0 ∧
        rho.pos.isHermitian.eigenvalues i ≠
          rho.pos.isHermitian.eigenvalues k := by
  let E := rho.pos.isHermitian.eigenvectorUnitary
  let lam := rho.pos.isHermitian.eigenvalues
  by_contra h
  push Not at h
  apply hdiag
  intro j k hjk
  have hex : ∃ i, Complex.normSq ((E : CMatrix a) j i) ≠ 0 := by
    by_contra hz
    push Not at hz
    have hsum := unitary_row_normSq_sum E j
    simp [hz] at hsum
  obtain ⟨i₀, hi₀⟩ := hex
  rw [state_apply_eq_eigenvalue_sum]
  calc
    (∑ i, (E : CMatrix a) j i * (lam i : ℂ) *
        star ((E : CMatrix a) k i)) =
        ∑ i, (lam i₀ : ℂ) *
          ((E : CMatrix a) j i * star ((E : CMatrix a) k i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hEi : (E : CMatrix a) j i = 0
      · simp [hEi]
      · have hwi :
            Complex.normSq ((E : CMatrix a) j i) ≠ 0 := by
          simpa [Complex.normSq_eq_zero] using hEi
        have hlam : lam i = lam i₀ := h j i i₀ hwi hi₀
        rw [hlam]
        ring
    _ = (lam i₀ : ℂ) *
        ∑ i, (E : CMatrix a) j i * star ((E : CMatrix a) k i) := by
      rw [Finset.mul_sum]
    _ = (lam i₀ : ℂ) *
        (((E : CMatrix a) * star (E : CMatrix a)) j k) := by
      rw [Matrix.mul_apply]
      simp only [Matrix.star_apply]
    _ = 0 := by
      have hunit : (E : CMatrix a) * star (E : CMatrix a) = 1 :=
        Unitary.coe_mul_star_self E
      rw [hunit, Matrix.one_apply]
      simp [hjk]

private lemma sum_negMulLog_eigenvalues_lt_diagonal_of_not_isDiag
    {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) (hdiag : ¬rho.matrix.IsDiag) :
    (∑ i, Real.negMulLog (rho.pos.isHermitian.eigenvalues i)) <
      ∑ j, Real.negMulLog (Complex.re (rho.matrix j j)) := by
  let E := rho.pos.isHermitian.eigenvectorUnitary
  let lam := rho.pos.isHermitian.eigenvalues
  obtain ⟨j₀, i₀, k₀, hi₀, hk₀, hik⟩ :=
    exists_mixed_eigenvalues_of_not_isDiag rho hdiag
  have hrow (j : a) :
      (∑ i, Complex.normSq ((E : CMatrix a) j i) *
          Real.negMulLog (lam i)) ≤
        Real.negMulLog (Complex.re (rho.matrix j j)) := by
    have hj := Real.strictConcaveOn_negMulLog.concaveOn.le_map_sum
      (t := Finset.univ)
      (w := fun i : a => Complex.normSq ((E : CMatrix a) j i))
      (p := lam)
      (fun _ _ => Complex.normSq_nonneg _)
      (by simpa using unitary_row_normSq_sum E j)
      (fun i _ => rho.pos.eigenvalues_nonneg i)
    calc
      (∑ i, Complex.normSq ((E : CMatrix a) j i) *
          Real.negMulLog (lam i)) ≤
          Real.negMulLog
            (∑ i, Complex.normSq ((E : CMatrix a) j i) * lam i) := by
        simpa [smul_eq_mul] using hj
      _ = Real.negMulLog (Complex.re (rho.matrix j j)) := by
        rw [state_diag_re_eq_eigenvalue_average]
  have hrow_strict :
      (∑ i, Complex.normSq ((E : CMatrix a) j₀ i) *
          Real.negMulLog (lam i)) <
        Real.negMulLog (Complex.re (rho.matrix j₀ j₀)) := by
    have hle := hrow j₀
    apply lt_of_le_of_ne hle
    intro heq
    have heq' :
        Real.negMulLog
            (∑ i, Complex.normSq ((E : CMatrix a) j₀ i) * lam i) =
          ∑ i, Complex.normSq ((E : CMatrix a) j₀ i) *
            Real.negMulLog (lam i) := by
      rw [← state_diag_re_eq_eigenvalue_average]
      exact heq.symm
    have hall := (Real.strictConcaveOn_negMulLog.map_sum_eq_iff'
      (t := Finset.univ)
      (w := fun i : a => Complex.normSq ((E : CMatrix a) j₀ i))
      (p := lam)
      (fun _ _ => Complex.normSq_nonneg _)
      (by simpa using unitary_row_normSq_sum E j₀)
      (fun i _ => rho.pos.eigenvalues_nonneg i)).1 (by
        simpa [smul_eq_mul] using heq')
    have hi := hall i₀ (Finset.mem_univ i₀) (by
      simpa [E] using hi₀)
    have hk := hall k₀ (Finset.mem_univ k₀) (by
      simpa [E] using hk₀)
    apply hik
    change lam i₀ = lam k₀
    exact hi.trans hk.symm
  calc
    (∑ i, Real.negMulLog (rho.pos.isHermitian.eigenvalues i)) =
        ∑ j, ∑ i, Complex.normSq ((E : CMatrix a) j i) *
          Real.negMulLog (lam i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_mul, unitary_col_normSq_sum]
      simp [lam]
    _ < ∑ j, Real.negMulLog (Complex.re (rho.matrix j j)) := by
      apply Finset.sum_lt_sum
      · intro j hj
        exact hrow j
      · exact ⟨j₀, Finset.mem_univ j₀, hrow_strict⟩

private lemma state_eigenvalue_eq_diag_re_of_isDiag_of_entry_ne_zero
    {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) (hdiag : rho.matrix.IsDiag) (j i : a)
    (hE : (rho.pos.isHermitian.eigenvectorUnitary :
      CMatrix a) j i ≠ 0) :
    rho.pos.isHermitian.eigenvalues i =
      Complex.re (rho.matrix j j) := by
  let E := rho.pos.isHermitian.eigenvectorUnitary
  let lam := rho.pos.isHermitian.eigenvalues
  have heig := rho.pos.isHermitian.mulVec_eigenvectorBasis i
  have hj := congrFun heig j
  change Matrix.mulVec rho.matrix
      (fun x => (E : CMatrix a) x i) j =
    (lam i : ℂ) * (E : CMatrix a) j i at hj
  have hmul : Matrix.mulVec rho.matrix
      (fun x => (E : CMatrix a) x i) j =
    rho.matrix j j * (E : CMatrix a) j i := by
    rw [← hdiag.diagonal_diag]
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [hmul] at hj
  have hc : rho.matrix j j = (lam i : ℂ) :=
    mul_right_cancel₀ hE hj
  have hr := congrArg Complex.re hc
  simpa [lam] using hr.symm

private lemma sum_negMulLog_eigenvalues_eq_diagonal_of_isDiag
    {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) (hdiag : rho.matrix.IsDiag) :
    (∑ i, Real.negMulLog (rho.pos.isHermitian.eigenvalues i)) =
      ∑ j, Real.negMulLog (Complex.re (rho.matrix j j)) := by
  let E := rho.pos.isHermitian.eigenvectorUnitary
  let lam := rho.pos.isHermitian.eigenvalues
  calc
    (∑ i, Real.negMulLog (rho.pos.isHermitian.eigenvalues i)) =
        ∑ j, ∑ i, Complex.normSq ((E : CMatrix a) j i) *
          Real.negMulLog (lam i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_mul, unitary_col_normSq_sum]
      simp [lam]
    _ = ∑ j, Real.negMulLog (Complex.re (rho.matrix j j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (∑ i, Complex.normSq ((E : CMatrix a) j i) *
            Real.negMulLog (lam i)) =
            ∑ i, Complex.normSq ((E : CMatrix a) j i) *
              Real.negMulLog (Complex.re (rho.matrix j j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hE : (E : CMatrix a) j i = 0
          · simp [hE]
          · have hlam :=
              state_eigenvalue_eq_diag_re_of_isDiag_of_entry_ne_zero
                rho hdiag j i (by simpa [E] using hE)
            change lam i = Complex.re (rho.matrix j j) at hlam
            rw [hlam]
        _ = Real.negMulLog (Complex.re (rho.matrix j j)) := by
          rw [← Finset.sum_mul, unitary_row_normSq_sum]
          simp

private lemma unitaryConjugate_injective
    {a : Type*} [Fintype a] [DecidableEq a]
    (U : Matrix.unitaryGroup a ℂ) :
    Function.Injective (unitaryConjugate U : State a → State a) := by
  intro rho sigma h
  apply State.ext
  have hm := congrArg State.matrix h
  change (U : CMatrix a) * rho.matrix *
      Matrix.conjTranspose (U : CMatrix a) =
    (U : CMatrix a) * sigma.matrix *
      Matrix.conjTranspose (U : CMatrix a) at hm
  have hm' := congrArg
    (fun M : CMatrix a =>
      Matrix.conjTranspose (U : CMatrix a) * M * (U : CMatrix a)) hm
  have hsU : Matrix.conjTranspose (U : CMatrix a) *
      (U : CMatrix a) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self U
  have hUs : (U : CMatrix a) *
      Matrix.conjTranspose (U : CMatrix a) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self U
  simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc
      (Matrix.conjTranspose (U : CMatrix a)) (U : CMatrix a),
    hsU, Matrix.one_mul, hUs, Matrix.mul_one] using hm'

/-- Strict concavity of von Neumann entropy for two distinct density states
and a genuinely nontrivial convex weight. -/
theorem vonNeumannEntropy_strictConcavity
    {a : Type*} [Fintype a] [DecidableEq a]
    (rho sigma : State a) (hneq : rho ≠ sigma)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    t * vonNeumannEntropy rho + (1 - t) * vonNeumannEntropy sigma <
      vonNeumannEntropy
        (convexCombination t rho sigma ht0.le (le_of_lt ht1)) := by
  let tau := convexCombination t rho sigma ht0.le (le_of_lt ht1)
  let E := tau.pos.isHermitian.eigenvectorUnitary
  let W : Matrix.unitaryGroup a ℂ := star E
  let rho' := unitaryConjugate W rho
  let sigma' := unitaryConjugate W sigma
  let tau' := unitaryConjugate W tau
  have hmat :
      tau'.matrix =
        t • rho'.matrix + (1 - t) • sigma'.matrix := by
    change (W : CMatrix a) *
        (t • rho.matrix + (1 - t) • sigma.matrix) *
          Matrix.conjTranspose (W : CMatrix a) =
      t • ((W : CMatrix a) * rho.matrix *
        Matrix.conjTranspose (W : CMatrix a)) +
      (1 - t) • ((W : CMatrix a) * sigma.matrix *
        Matrix.conjTranspose (W : CMatrix a))
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.smul_mul]
  have htau_matrix :
      tau'.matrix =
        Matrix.diagonal
          (Complex.ofReal ∘ tau.pos.isHermitian.eigenvalues) := by
    change (star (E : CMatrix a)) * tau.matrix *
        Matrix.conjTranspose (star (E : CMatrix a)) =
      Matrix.diagonal
        (Complex.ofReal ∘ tau.pos.isHermitian.eigenvalues)
    simpa [Matrix.star_eq_conjTranspose] using
      tau.pos.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have htau_diag : tau'.matrix.IsDiag := by
    rw [htau_matrix]
    exact Matrix.isDiag_diagonal _
  have hneq' : rho' ≠ sigma' := by
    intro h
    exact hneq (unitaryConjugate_injective W h)
  have hre (j : a) :
      Complex.re (tau'.matrix j j) =
        t * Complex.re (rho'.matrix j j) +
          (1 - t) * Complex.re (sigma'.matrix j j) := by
    have h := congrArg (fun M : CMatrix a => Complex.re (M j j)) hmat
    simpa using h
  have hcoord (j : a) :
      t * Real.negMulLog (Complex.re (rho'.matrix j j)) +
          (1 - t) * Real.negMulLog (Complex.re (sigma'.matrix j j)) ≤
        Real.negMulLog (Complex.re (tau'.matrix j j)) := by
    have h := Real.strictConcaveOn_negMulLog.concaveOn.2
      (state_diag_re_nonneg rho' j)
      (state_diag_re_nonneg sigma' j)
      ht0.le (sub_nonneg.mpr ht1.le) (by ring)
    simpa only [smul_eq_mul, ← hre j] using h
  have hcoord_strict {j : a}
      (hj : Complex.re (rho'.matrix j j) ≠
        Complex.re (sigma'.matrix j j)) :
      t * Real.negMulLog (Complex.re (rho'.matrix j j)) +
          (1 - t) * Real.negMulLog (Complex.re (sigma'.matrix j j)) <
        Real.negMulLog (Complex.re (tau'.matrix j j)) := by
    have h := Real.strictConcaveOn_negMulLog.2
      (state_diag_re_nonneg rho' j)
      (state_diag_re_nonneg sigma' j)
      hj ht0 (sub_pos.mpr ht1) (by ring)
    simpa only [smul_eq_mul, ← hre j] using h
  have hcoord_sum :
      t * (∑ j, Real.negMulLog (Complex.re (rho'.matrix j j))) +
          (1 - t) *
            (∑ j, Real.negMulLog (Complex.re (sigma'.matrix j j))) ≤
        ∑ j, Real.negMulLog (Complex.re (tau'.matrix j j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => hcoord j
  have htau_entropy :
      (∑ i, Real.negMulLog (tau'.pos.isHermitian.eigenvalues i)) =
        ∑ j, Real.negMulLog (Complex.re (tau'.matrix j j)) :=
    sum_negMulLog_eigenvalues_eq_diagonal_of_isDiag tau' htau_diag
  have hnatural :
      t * (∑ i, Real.negMulLog (rho'.pos.isHermitian.eigenvalues i)) +
          (1 - t) *
            (∑ i, Real.negMulLog (sigma'.pos.isHermitian.eigenvalues i)) <
        ∑ i, Real.negMulLog (tau'.pos.isHermitian.eigenvalues i) := by
    by_cases hrdiag : rho'.matrix.IsDiag
    · by_cases hsdiag : sigma'.matrix.IsDiag
      · have hdiag_ne :
            ∃ j, Complex.re (rho'.matrix j j) ≠
              Complex.re (sigma'.matrix j j) := by
          by_contra h
          push Not at h
          apply hneq'
          apply State.ext
          ext i j
          by_cases hij : i = j
          · subst j
            calc
              rho'.matrix i i =
                  (Complex.re (rho'.matrix i i) : ℂ) :=
                (rho'.pos.isHermitian.coe_re_apply_self i).symm
              _ = (Complex.re (sigma'.matrix i i) : ℂ) := by
                rw [h i]
              _ = sigma'.matrix i i :=
                sigma'.pos.isHermitian.coe_re_apply_self i
          · rw [hrdiag hij, hsdiag hij]
        obtain ⟨j₀, hj₀⟩ := hdiag_ne
        have hcoord_sum_strict :
            t * (∑ j, Real.negMulLog
              (Complex.re (rho'.matrix j j))) +
                (1 - t) * (∑ j, Real.negMulLog
                  (Complex.re (sigma'.matrix j j))) <
              ∑ j, Real.negMulLog
                (Complex.re (tau'.matrix j j)) := by
          rw [Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          apply Finset.sum_lt_sum
          · intro j hj
            exact hcoord j
          · exact ⟨j₀, Finset.mem_univ j₀,
              hcoord_strict hj₀⟩
        rw [sum_negMulLog_eigenvalues_eq_diagonal_of_isDiag
            rho' hrdiag,
          sum_negMulLog_eigenvalues_eq_diagonal_of_isDiag
            sigma' hsdiag,
          htau_entropy]
        exact hcoord_sum_strict
      · have hslt :=
          sum_negMulLog_eigenvalues_lt_diagonal_of_not_isDiag
            sigma' hsdiag
        have hrle :=
          sum_negMulLog_eigenvalues_le_diagonal rho'
        rw [htau_entropy]
        nlinarith [mul_lt_mul_of_pos_left hslt (sub_pos.mpr ht1),
          mul_le_mul_of_nonneg_left hrle ht0.le]
    · have hrlt :=
        sum_negMulLog_eigenvalues_lt_diagonal_of_not_isDiag
          rho' hrdiag
      have hsle :=
        sum_negMulLog_eigenvalues_le_diagonal sigma'
      rw [htau_entropy]
      nlinarith [mul_lt_mul_of_pos_left hrlt ht0,
        mul_le_mul_of_nonneg_left hsle (sub_nonneg.mpr ht1.le)]
  have hnatural' :
      t * (∑ i, Real.negMulLog (rho.pos.isHermitian.eigenvalues i)) +
          (1 - t) *
            (∑ i, Real.negMulLog (sigma.pos.isHermitian.eigenvalues i)) <
        ∑ i, Real.negMulLog (tau.pos.isHermitian.eigenvalues i) := by
    simpa [rho', sigma', tau',
      state_eigenvalues_unitaryConjugate] using hnatural
  simp only [vonNeumannEntropy, schmidtEntropy_eq_sum_negMulLog]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv := (div_lt_div_iff_of_pos_right hlog).2 hnatural'
  simpa only [tau] using (show
    t * ((∑ i, Real.negMulLog (rho.pos.isHermitian.eigenvalues i)) /
          Real.log 2) +
        (1 - t) *
          ((∑ i, Real.negMulLog (sigma.pos.isHermitian.eigenvalues i)) /
            Real.log 2) <
      (∑ i, Real.negMulLog
        (tau.pos.isHermitian.eigenvalues i)) / Real.log 2 by
    ring_nf at hdiv ⊢
    exact hdiv)

/-- The `d²`-term random-unitary twirl sends every state to `Id / d`.

The type `Fin (d ^ 2)` is the zero-based Lean counterpart of the source
indices `i = 1, ..., d²`.
-/
theorem exists_randomUnitary_twirl
    (d : ℕ) [NeZero d] (rho : State (Fin d)) :
    ∃ U : Fin (d ^ 2) → Matrix.unitaryGroup (Fin d) ℂ,
      (((d : ℝ) ^ 2)⁻¹) •
          (∑ i, (unitaryConjugate (U i) rho).matrix) =
        (maximallyMixedState d).matrix := by
  let e : Fin d × Fin d ≃ Fin (d ^ 2) :=
    finProdFinEquiv.trans (finCongr (by simp [pow_two]))
  let U : Fin (d ^ 2) → Matrix.unitaryGroup (Fin d) ℂ :=
    fun i => cyclicEigenUnitary d rho (e.symm i).1
  refine ⟨U, ?_⟩
  change (((d : ℝ) ^ 2)⁻¹) •
      (∑ i, (unitaryConjugate
        (cyclicEigenUnitary d rho (e.symm i).1) rho).matrix) =
      ((d : ℝ)⁻¹) • (1 : CMatrix (Fin d))
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  rw [show (∑ k : Fin d, ∑ _l : Fin d,
      (unitaryConjugate (cyclicEigenUnitary d rho k) rho).matrix) =
        d • (∑ k : Fin d,
          (unitaryConjugate (cyclicEigenUnitary d rho k) rho).matrix) by
    simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.sum_nsmul]]
  rw [sum_cyclicEigenUnitary_conjugates]
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne d
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  field_simp

/-- Every density state other than `Id / d` has entropy strictly below
`log₂ d`. -/
theorem vonNeumannEntropy_lt_log2_dim
    (d : ℕ) [NeZero d] (rho : State (Fin d))
    (hneq : rho ≠ maximallyMixedState d) :
    vonNeumannEntropy rho < QITBench.OneShot.log2 (d : ℝ) := by
  have hevne :
      rho.pos.isHermitian.eigenvalues ≠ fun _ => (d : ℝ)⁻¹ := by
    intro hev
    exact hneq (state_eq_maximallyMixed_of_eigenvalues_eq d rho hev)
  rw [vonNeumannEntropy,
    schmidtEntropy_eq_sum_negMulLog rho.pos.isHermitian.eigenvalues,
    QITBench.OneShot.log2]
  exact (div_lt_div_iff_of_pos_right (Real.log_pos (by norm_num))).2 <|
    sum_negMulLog_lt_log_card d rho.pos.isHermitian.eigenvalues
      rho.pos.eigenvalues_nonneg (state_eigenvalues_sum d rho) hevne

/-- The completely mixed state has entropy `log₂ d`, every state has entropy
at most that value, and equality occurs exactly for the completely mixed
state.  Thus `Id / d` is the unique maximum-entropy state. -/
theorem maximallyMixedState_unique_entropyMaximizer
    (d : ℕ) [NeZero d] :
    vonNeumannEntropy (maximallyMixedState d) =
        QITBench.OneShot.log2 (d : ℝ) ∧
      ∀ rho : State (Fin d),
        vonNeumannEntropy rho ≤ QITBench.OneShot.log2 (d : ℝ) ∧
          (vonNeumannEntropy rho = QITBench.OneShot.log2 (d : ℝ) ↔
            rho = maximallyMixedState d) := by
  have hmax :
      vonNeumannEntropy (maximallyMixedState d) =
        QITBench.OneShot.log2 (d : ℝ) := by
    rw [vonNeumannEntropy, maximallyMixedState_eigenvalues]
    exact schmidtEntropy_uniform d
  refine ⟨hmax, ?_⟩
  intro rho
  by_cases h : rho = maximallyMixedState d
  · subst rho
    exact ⟨hmax.le, ⟨fun _ => rfl, fun _ => hmax⟩⟩
  · have hlt := vonNeumannEntropy_lt_log2_dim d rho h
    refine ⟨hlt.le, ⟨?_, ?_⟩⟩
    · intro heq
      exfalso
      exact (ne_of_lt hlt) heq
    · intro heq
      exact (h heq).elim

end

end QITFormalized.UniquenessMaximumEntropyState
