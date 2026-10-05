import QAlgBench.Base

open scoped BigOperators

namespace QAlgFormalized.CommonStabilizerFullRankStates

open QAlgBench

noncomputable section

/-- The rank-one operator `|ψ⟩⟨φ|` in the matrix model used by `QAlgBench`. -/
def ketBra {R : Register} (ψ φ : StateVector R) : HilbertOperator R :=
  Matrix.vecMulVec (fun i => ψ i) (fun j => starRingEnd ℂ (φ j))

/-- The operator with the prescribed real eigenvalues in the prescribed
orthonormal basis. -/
def spectralOperator {R : Register} {d : ℕ} (eigenvalue : Fin d → ℝ)
    (basis : OrthonormalBasis (Fin d) ℂ (StateVector R)) : HilbertOperator R :=
  ∑ i, (eigenvalue i : ℂ) • ketBra (basis i) (basis i)

/-- Unitary gates that stabilize both operators under unitary conjugation. -/
def commonUnitaryStabilizer {R : Register} (ρ σ : HilbertOperator R) : Set (Gate R) :=
  {W |
    (W : HilbertOperator R) * ρ * (W : HilbertOperator R).conjTranspose = ρ ∧
    (W : HilbertOperator R) * σ * (W : HilbertOperator R).conjTranspose = σ}

/-- Scalar unitary gates, presented as `exp(iθ) I`. -/
def scalarUnitaryGates (R : Register) : Set (Gate R) :=
  {W | ∃ θ : ℝ,
    (W : HilbertOperator R) = Complex.exp (θ * Complex.I) • (1 : HilbertOperator R)}

private lemma ketBra_applyVec {R : Register} (ψ φ x : StateVector R) :
    HilbertOperator.applyVec (ketBra ψ φ) x = inner ℂ φ x • ψ := by
  ext k
  change (∑ j, ψ k * starRingEnd ℂ (φ j) * x j) =
    (∑ j, x j * starRingEnd ℂ (φ j)) * ψ k
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma spectralOperator_applyVec {R : Register} {d : ℕ} (a : Fin d → ℝ)
    (b : OrthonormalBasis (Fin d) ℂ (StateVector R)) (x : StateVector R) :
    HilbertOperator.applyVec (spectralOperator a b) x =
      ∑ i, ((a i : ℂ) * b.repr x i) • b i := by
  unfold spectralOperator
  rw [HilbertOperator.sum_applyVec]
  simp_rw [HilbertOperator.smul_applyVec, ketBra_applyVec, ← b.repr_apply_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul]

private lemma spectralOperator_apply_basis {R : Register} {d : ℕ} (a : Fin d → ℝ)
    (b : OrthonormalBasis (Fin d) ℂ (StateVector R)) (i : Fin d) :
    HilbertOperator.applyVec (spectralOperator a b) (b i) = (a i : ℂ) • b i := by
  rw [spectralOperator_applyVec]
  simp [b.repr_self]

private lemma spectralOperator_repr_apply {R : Register} {d : ℕ} (a : Fin d → ℝ)
    (b : OrthonormalBasis (Fin d) ℂ (StateVector R)) (x : StateVector R) (k : Fin d) :
    b.repr (HilbertOperator.applyVec (spectralOperator a b) x) k =
      (a k : ℂ) * b.repr x k := by
  rw [b.repr_apply_apply, spectralOperator_applyVec]
  simp [inner_sum, inner_smul_right, OrthonormalBasis.inner_eq_ite]

private lemma eq_smul_basis_of_spectral_eigenvector {R : Register} {d : ℕ}
    (a : Fin d → ℝ) (b : OrthonormalBasis (Fin d) ℂ (StateVector R))
    (ha : Function.Injective a) (x : StateVector R) (i : Fin d)
    (hx : HilbertOperator.applyVec (spectralOperator a b) x = (a i : ℂ) • x) :
    x = b.repr x i • b i := by
  apply b.repr.injective
  ext k
  have hcoord := congrArg (fun y : StateVector R => b.repr y k) hx
  rw [spectralOperator_repr_apply] at hcoord
  simp only [b.repr_apply_apply, inner_smul_right] at hcoord
  by_cases hki : k = i
  · subst k
    simp [b.repr_apply_apply]
  · have hak : (a k : ℂ) ≠ (a i : ℂ) := by
      exact_mod_cast (fun h => hki (ha h))
    have hprod : ((a k : ℂ) - (a i : ℂ)) * inner ℂ (b k) x = 0 := by
      linear_combination hcoord
    have hkInner : inner ℂ (b k) x = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hak)
    simpa [b.repr_apply_apply, hki] using hkInner

/-- A unitary stabilizing two full-rank density operators with simple spectra
and everywhere-nonzero overlaps between their eigenbases is scalar.  An
orthonormal basis indexed by `Fin d` records that the Hilbert space has
dimension `d`; positivity and trace-one normalization of every displayed
spectrum record full rank and the density-operator condition. -/
theorem common_stabilizer_is_scalar {R : Register} {d : ℕ}
    (ρ σ : HilbertOperator R)
    (r s : Fin d → ℝ)
    (rBasis sBasis : OrthonormalBasis (Fin d) ℂ (StateVector R))
    (hr_pos : ∀ i, 0 < r i)
    (hs_pos : ∀ j, 0 < s j)
    (hr_trace : ∑ i, r i = 1)
    (hs_trace : ∑ j, s j = 1)
    (hr_simple : Function.Injective r)
    (hs_simple : Function.Injective s)
    (hρ : ρ = spectralOperator r rBasis)
    (hσ : σ = spectralOperator s sBasis)
    (hcross : ∀ i j, inner ℂ (rBasis i) (sBasis j) ≠ 0)
    (W : Gate R)
    (hWρ :
      (W : HilbertOperator R) * ρ * (W : HilbertOperator R).conjTranspose = ρ)
    (hWσ :
      (W : HilbertOperator R) * σ * (W : HilbertOperator R).conjTranspose = σ) :
    ∃ θ : ℝ,
      (W : HilbertOperator R) =
        Complex.exp (θ * Complex.I) • (1 : HilbertOperator R) := by
  have hstar_mul :
      (W : HilbertOperator R).conjTranspose * (W : HilbertOperator R) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp W.unitary
  have hcommρ : (W : HilbertOperator R) * ρ = ρ * (W : HilbertOperator R) := by
    calc
      (W : HilbertOperator R) * ρ =
          ((W : HilbertOperator R) * ρ * (W : HilbertOperator R).conjTranspose) *
            (W : HilbertOperator R) := by
              rw [Matrix.mul_assoc, hstar_mul, Matrix.mul_one]
      _ = ρ * (W : HilbertOperator R) := by rw [hWρ]
  have hcommσ : (W : HilbertOperator R) * σ = σ * (W : HilbertOperator R) := by
    calc
      (W : HilbertOperator R) * σ =
          ((W : HilbertOperator R) * σ * (W : HilbertOperator R).conjTranspose) *
            (W : HilbertOperator R) := by
              rw [Matrix.mul_assoc, hstar_mul, Matrix.mul_one]
      _ = σ * (W : HilbertOperator R) := by rw [hWσ]
  have hcommr : (W : HilbertOperator R) * spectralOperator r rBasis =
      spectralOperator r rBasis * (W : HilbertOperator R) := by
    simpa only [← hρ] using hcommρ
  have hcomms : (W : HilbertOperator R) * spectralOperator s sBasis =
      spectralOperator s sBasis * (W : HilbertOperator R) := by
    simpa only [← hσ] using hcommσ
  let α : Fin d → ℂ := fun i =>
    rBasis.repr (HilbertOperator.applyVec (W : HilbertOperator R) (rBasis i)) i
  let β : Fin d → ℂ := fun j =>
    sBasis.repr (HilbertOperator.applyVec (W : HilbertOperator R) (sBasis j)) j
  have hWr (i : Fin d) :
      HilbertOperator.applyVec (W : HilbertOperator R) (rBasis i) = α i • rBasis i := by
    apply eq_smul_basis_of_spectral_eigenvector r rBasis hr_simple
    calc
      HilbertOperator.applyVec (spectralOperator r rBasis)
          (HilbertOperator.applyVec (W : HilbertOperator R) (rBasis i)) =
          HilbertOperator.applyVec (spectralOperator r rBasis * (W : HilbertOperator R))
            (rBasis i) := by rw [HilbertOperator.mul_applyVec]
      _ = HilbertOperator.applyVec ((W : HilbertOperator R) * spectralOperator r rBasis)
            (rBasis i) := by rw [← hcommr]
      _ = HilbertOperator.applyVec (W : HilbertOperator R)
            (HilbertOperator.applyVec (spectralOperator r rBasis) (rBasis i)) := by
              rw [HilbertOperator.mul_applyVec]
      _ = (r i : ℂ) • HilbertOperator.applyVec (W : HilbertOperator R) (rBasis i) := by
              rw [spectralOperator_apply_basis, HilbertOperator.applyVec_smul]
  have hWs (j : Fin d) :
      HilbertOperator.applyVec (W : HilbertOperator R) (sBasis j) = β j • sBasis j := by
    apply eq_smul_basis_of_spectral_eigenvector s sBasis hs_simple
    calc
      HilbertOperator.applyVec (spectralOperator s sBasis)
          (HilbertOperator.applyVec (W : HilbertOperator R) (sBasis j)) =
          HilbertOperator.applyVec (spectralOperator s sBasis * (W : HilbertOperator R))
            (sBasis j) := by rw [HilbertOperator.mul_applyVec]
      _ = HilbertOperator.applyVec ((W : HilbertOperator R) * spectralOperator s sBasis)
            (sBasis j) := by rw [← hcomms]
      _ = HilbertOperator.applyVec (W : HilbertOperator R)
            (HilbertOperator.applyVec (spectralOperator s sBasis) (sBasis j)) := by
              rw [HilbertOperator.mul_applyVec]
      _ = (s j : ℂ) • HilbertOperator.applyVec (W : HilbertOperator R) (sBasis j) := by
              rw [spectralOperator_apply_basis, HilbertOperator.applyVec_smul]
  have hαunit (i : Fin d) : starRingEnd ℂ (α i) * α i = 1 := by
    have hinner := HilbertOperator.inner_applyVec_applyVec_of_mem_unitaryGroup
      W.unitary (rBasis i) (rBasis i)
    rw [hWr i] at hinner
    rw [inner_smul_left, inner_smul_right] at hinner
    simpa only [rBasis.inner_eq_one, mul_one] using hinner
  have hβα (i j : Fin d) : β j = α i := by
    have hinner := HilbertOperator.inner_applyVec_applyVec_of_mem_unitaryGroup
      W.unitary (rBasis i) (sBasis j)
    rw [hWr i, hWs j] at hinner
    simp only [inner_smul_left, inner_smul_right] at hinner
    have hprod : (starRingEnd ℂ (α i) * β j) * inner ℂ (rBasis i) (sBasis j) =
        1 * inner ℂ (rBasis i) (sBasis j) := by
      rw [one_mul]
      calc
        (starRingEnd ℂ (α i) * β j) * inner ℂ (rBasis i) (sBasis j) =
            β j * (starRingEnd ℂ (α i) * inner ℂ (rBasis i) (sBasis j)) := by ring
        _ = inner ℂ (rBasis i) (sBasis j) := hinner
    have hab : starRingEnd ℂ (α i) * β j = 1 :=
      mul_right_cancel₀ (hcross i j) hprod
    have hstar_ne : starRingEnd ℂ (α i) ≠ 0 := by
      intro hzero
      have hunit := hαunit i
      rw [hzero, zero_mul] at hunit
      exact zero_ne_one hunit
    apply mul_left_cancel₀ hstar_ne
    exact hab.trans (hαunit i).symm
  have hd : 0 < d := by
    by_contra hnot
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hnot
    subst d
    norm_num at hr_trace
  let i₀ : Fin d := ⟨0, hd⟩
  have hαeq (i : Fin d) : α i = α i₀ :=
    (hβα i i₀).symm.trans (hβα i₀ i₀)
  have hscalar : (W : HilbertOperator R) = α i₀ • (1 : HilbertOperator R) := by
    apply HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis rBasis
    intro i
    rw [hWr i, hαeq i, HilbertOperator.smul_applyVec, HilbertOperator.one_applyVec]
  have hnormα : ‖α i₀‖ = 1 := by
    simpa only [hWr i₀, norm_smul, rBasis.norm_eq_one, mul_one] using
      (HilbertOperator.norm_applyVec_of_mem_unitaryGroup W.unitary (rBasis i₀))
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff (α i₀)).mp hnormα
  exact ⟨θ, hscalar.trans (by rw [hθ])⟩

/-- Set-level reformulation: the common unitary stabilizer is exactly the
scalar copy of `U(1)`. -/
theorem commonUnitaryStabilizer_eq_scalarUnitaryGates {R : Register} {d : ℕ}
    (ρ σ : HilbertOperator R)
    (r s : Fin d → ℝ)
    (rBasis sBasis : OrthonormalBasis (Fin d) ℂ (StateVector R))
    (hr_pos : ∀ i, 0 < r i)
    (hs_pos : ∀ j, 0 < s j)
    (hr_trace : ∑ i, r i = 1)
    (hs_trace : ∑ j, s j = 1)
    (hr_simple : Function.Injective r)
    (hs_simple : Function.Injective s)
    (hρ : ρ = spectralOperator r rBasis)
    (hσ : σ = spectralOperator s sBasis)
    (hcross : ∀ i j, inner ℂ (rBasis i) (sBasis j) ≠ 0) :
    commonUnitaryStabilizer ρ σ = scalarUnitaryGates R := by
  ext W
  constructor
  · intro hW
    exact common_stabilizer_is_scalar ρ σ r s rBasis sBasis hr_pos hs_pos
      hr_trace hs_trace hr_simple hs_simple hρ hσ hcross W hW.1 hW.2
  · rintro ⟨θ, hθ⟩
    have hc : starRingEnd ℂ (Complex.exp (θ * Complex.I)) *
        Complex.exp (θ * Complex.I) = 1 := by
      rw [RCLike.conj_mul, Complex.norm_exp]
      norm_num
    constructor <;> rw [hθ] <;> simp [hc, smul_smul]

end

end QAlgFormalized.CommonStabilizerFullRankStates
