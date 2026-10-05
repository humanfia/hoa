import QAlgBench.Base

open Filter

namespace QAlgFormalized
namespace ApproximateTwoDesignDepthHaarLossFluctuations

open QAlgBench

noncomputable section

/-!
This file formalizes the circuit ensemble, its second-moment operator,
approximate two-design depth, and exact-Haar loss fluctuations from the source
problem.  The only import is the configured benchmark Base module.
-/

/-! ## Registers, circuits, and Lie-algebra assumptions -/

/-- The Hilbert-space dimension of an `n`-qubit register. -/
abbrev qubitDimension (n : ℕ) : ℕ := 2 ^ n

/-- Square complex operators on the `n`-qubit Hilbert space. -/
abbrev QubitOperator (n : ℕ) := HilbertOperator (Qubits n)

/-- Exact `SU(2^n)` matrices, using the special-unitary group available through
the configured Base import. -/
abbrev SpecialUnitary (n : ℕ) :=
  Matrix.specialUnitaryGroup (Fin (qubitDimension n)) ℂ

/-- A real expectation functional on an outcome type. -/
abbrev RealExpectation (Omega : Type) := (Omega → ℝ) →ₗ[ℝ] ℝ

/-- Continuous real observables on `SU(2^n)`.  Restricting the Haar functional
to this carrier is essential: a translation-invariant linear functional on
*all* real-valued functions on an infinite compact group is inconsistent,
whereas normalized Haar integration is a positive bi-invariant functional on
continuous observables. -/
abbrev HaarObservable (n : ℕ) :=
  ContinuousMap (SpecialUnitary n) ℝ

/-- Left translation of a continuous Haar observable. -/
def leftTranslateHaarObservable {n : ℕ} (V : SpecialUnitary n)
    (f : HaarObservable n) : HaarObservable n where
  toFun U := f (V * U)
  continuous_toFun :=
    f.continuous.comp (continuous_const.mul continuous_id)

/-- Right translation of a continuous Haar observable. -/
def rightTranslateHaarObservable {n : ℕ} (V : SpecialUnitary n)
    (f : HaarObservable n) : HaarObservable n where
  toFun U := f (U * V)
  continuous_toFun :=
    f.continuous.comp (continuous_id.mul continuous_const)

/-- Complexification of a real expectation functional. -/
def complexExpectation {Omega : Type}
    (expectation : RealExpectation Omega) (f : Omega → ℂ) : ℂ :=
  expectation (fun omega => (f omega).re) +
    Complex.I * expectation (fun omega => (f omega).im)

/-- Entrywise expectation of a finite complex matrix. -/
def expectedMatrix {Omega i : Type} [Fintype i]
    (expectation : RealExpectation Omega)
    (F : Omega → Matrix i i ℂ) : Matrix i i ℂ :=
  fun a b => complexExpectation expectation (fun omega => F omega a b)

/-- A probability ensemble of `L` real layer parameters.  Positivity and
normalization ensure that `expectation` represents a probability law rather
than an arbitrary linear functional. -/
structure LayerParameterEnsemble (L : ℕ) where
  Sample : Type
  parameters : Sample → Fin L → ℝ
  expectation : RealExpectation Sample
  normalized : expectation (fun _ => 1) = 1
  nonnegative :
    ∀ f : Sample → ℝ, (∀ omega, 0 ≤ f omega) → 0 ≤ expectation f

/-- Exact normalized Haar expectation on `SU(2^n)`, characterized as a
positive normalized bi-invariant real-linear functional on continuous
observables.  This is the standard Riesz-functional presentation of Haar
probability on a compact group.  Moment identities are deliberately not
fields: they are consequences to be derived from exact Haar randomness (apart
from the explicitly assumed pure-state second-moment identity in the source).

The linearity laws spell out pointwise addition and real scalar multiplication
because the configured Base import exposes `ContinuousMap` but not its bundled
module structure. -/
structure HaarExpectation (n : ℕ) where
  expectation : HaarObservable n → ℝ
  map_add :
    ∀ (f g : HaarObservable n),
      expectation
          ⟨fun U => f U + g U, f.continuous.add g.continuous⟩ =
        expectation f + expectation g
  map_smul :
    ∀ (r : ℝ) (f : HaarObservable n),
      expectation
          ⟨fun U => r * f U, continuous_const.mul f.continuous⟩ =
        r * expectation f
  normalized :
    expectation (ContinuousMap.const (SpecialUnitary n) 1) = 1
  nonnegative :
    ∀ f : HaarObservable n,
      (∀ U, 0 ≤ f U) → 0 ≤ expectation f
  left_invariant :
    ∀ (V : SpecialUnitary n) (f : HaarObservable n),
      expectation (leftTranslateHaarObservable V f) = expectation f
  right_invariant :
    ∀ (V : SpecialUnitary n) (f : HaarObservable n),
      expectation (rightTranslateHaarObservable V f) = expectation f

/-- Complex expectation obtained from the real Haar functional on the real and
imaginary parts of a continuous complex observable. -/
def haarComplexExpectation {n : ℕ} (haar : HaarExpectation n)
    (f : ContinuousMap (SpecialUnitary n) ℂ) : ℂ :=
  haar.expectation
      ⟨fun U => (f U).re,
        Complex.continuous_re.comp f.continuous⟩ +
    Complex.I *
      haar.expectation
        ⟨fun U => (f U).im,
          Complex.continuous_im.comp f.continuous⟩

/-- Entrywise Haar expectation of a continuously parameterized finite complex
matrix.  Continuity is required precisely at the scalar coordinate level on
which the Haar functional acts. -/
def haarExpectedMatrix {n : ℕ} {i : Type} [Fintype i]
    (haar : HaarExpectation n)
    (F : SpecialUnitary n → Matrix i i ℂ)
    (hF : ∀ a b, Continuous (fun U => F U a b)) :
    Matrix i i ℂ :=
  fun a b =>
    haarComplexExpectation haar
      ⟨fun U => F U a b, hF a b⟩

/-- The matrix exponential, written as its convergent power series because the
configured Base API has no matrix-exponential wrapper. -/
def operatorExponential {n : ℕ} (A : QubitOperator n) : QubitOperator n :=
  ∑' k : ℕ, ((Nat.factorial k : ℂ)⁻¹) • A ^ k

/-- The ordered parametrized circuit
`exp(i θ₁ H₁) ... exp(i θ_L H_L)`.  A `Fin L` index `0` represents source
index `1`, and `List.ofFn` fixes increasing layer order. -/
def parametrizedCircuit {n L : ℕ}
    (H : Fin L → QubitOperator n) (theta : Fin L → ℝ) :
    QubitOperator n :=
  (List.ofFn fun ell : Fin L =>
      operatorExponential (((theta ell : ℂ) * Complex.I) • H ell)).foldl
    (fun product layer => product * layer) 1

/-- Hermiticity expressed using the conjugate transpose available from Base. -/
def IsHermitian {n : ℕ} (A : QubitOperator n) : Prop :=
  A.conjTranspose = A

/-- Skew-Hermiticity, i.e. membership in the matrix model of `𝔲(N)`. -/
def IsSkewHermitian {n : ℕ} (A : QubitOperator n) : Prop :=
  A.conjTranspose = -A

/-- Closure conditions for a real matrix Lie subalgebra. -/
def IsRealLieSubalgebra {n : ℕ} (s : Set (QubitOperator n)) : Prop :=
  (0 : QubitOperator n) ∈ s ∧
  (∀ A ∈ s, ∀ B ∈ s, A + B ∈ s) ∧
  (∀ (r : ℝ) (A : QubitOperator n), A ∈ s → (r : ℂ) • A ∈ s) ∧
  (∀ A ∈ s, ∀ B ∈ s, A * B - B * A ∈ s)

/-- The real Lie algebra generated by the skew-Hermitian matrices `i H_ell`. -/
def dynamicalLieAlgebra {n L : ℕ}
    (H : Fin L → QubitOperator n) : Set (QubitOperator n) :=
  Set.sInter {s : Set (QubitOperator n) |
    IsRealLieSubalgebra s ∧ ∀ ell, Complex.I • H ell ∈ s}

/-- The standard matrix realization of `𝔰𝔲(2^n)`: traceless
skew-Hermitian matrices. -/
def specialUnitaryLieAlgebra (n : ℕ) : Set (QubitOperator n) :=
  {A | IsSkewHermitian A ∧ Matrix.trace A = 0}

/-- The source assumption that the dynamical Lie algebra is all of
`𝔰𝔲(2^n)`. -/
def HasFullSpecialUnitaryLieAlgebra {n L : ℕ}
    (H : Fin L → QubitOperator n) : Prop :=
  dynamicalLieAlgebra H = specialUnitaryLieAlgebra n

/-- A real-valued function on natural inputs is literally the evaluation of a
real polynomial. -/
def IsPolynomialFunction (p : ℕ → ℝ) : Prop :=
  ∃ q : Polynomial ℝ, ∀ n, p n = q.eval (n : ℝ)

/-! ## Circuit and Haar second-moment operators -/

/-- Operators on two copies of the `n`-qubit Hilbert space. -/
abbrev TwoCopyOperator (n : ℕ) := QubitOperator (n + n)

/-- A second-moment superoperator on two-copy operators. -/
abbrev TwoCopyMomentOperator (n : ℕ) :=
  TwoCopyOperator n → TwoCopyOperator n

/-- Conjugation of a two-copy operator by `U ⊗ U`. -/
def twoCopyConjugation {n : ℕ} (U : QubitOperator n)
    (X : TwoCopyOperator n) : TwoCopyOperator n :=
  let U2 : TwoCopyOperator n := HilbertOperator.tensor U U
  (U2 * X) * U2.conjTranspose

/-- Every scalar coordinate of two-copy conjugation depends continuously on
the special-unitary matrix.  This packages the regularity needed to apply the
Haar functional; it is an analytic fact, not an additional source
assumption. -/
theorem twoCopyConjugation_continuous_entry {n : ℕ}
    (X : TwoCopyOperator n)
    (a b : Fin (qubitDimension (n + n))) :
    Continuous (fun U : SpecialUnitary n =>
      twoCopyConjugation U.1 X a b) := by
  have hentry (i j : Fin (qubitDimension n)) :
      Continuous (fun U : SpecialUnitary n => U.1 i j) := by
    exact (continuous_apply_apply i j).comp continuous_subtype_val
  continuity

/-- The second-moment operator induced by the declared `L`-layer circuit and
the probability ensemble of its parameter vectors. -/
def circuitSecondMomentOperator {n L : ℕ}
    (H : Fin L → QubitOperator n) (ensemble : LayerParameterEnsemble L) :
    TwoCopyMomentOperator n :=
  fun X =>
    expectedMatrix ensemble.expectation (fun omega =>
      twoCopyConjugation
        (parametrizedCircuit H (ensemble.parameters omega)) X)

/-- The Haar second-moment operator on the same two-copy space. -/
def haarSecondMomentOperator {n : ℕ} (haar : HaarExpectation n) :
    TwoCopyMomentOperator n :=
  fun X =>
    haarExpectedMatrix haar (fun U =>
      twoCopyConjugation U.1 X)
      (twoCopyConjugation_continuous_entry X)

/-- The tensor-factor swap on
`ℂ^(2^n) ⊗ ℂ^(2^n)`, represented on product-basis indices. -/
def tensorSwap (n : ℕ) :
    Matrix (Fin (qubitDimension n) × Fin (qubitDimension n))
      (Fin (qubitDimension n) × Fin (qubitDimension n)) ℂ :=
  fun row column =>
    if row = (column.2, column.1) then 1 else 0

/-- The same factor-swap operator on the Base two-copy register, reindexed
through the canonical equivalence
`Fin (2^n) × Fin (2^n) ≃ Fin (2^(n+n))`. -/
def twoCopySwapOperator (n : ℕ) : TwoCopyOperator n :=
  Matrix.reindex (prodEquiv (m := n) (n := n))
    (prodEquiv (m := n) (n := n)) (tensorSwap n)

/-- The Haar-fixed (trivial-representation) sector for two-copy conjugation:
the span of the identity and factor swap. -/
def trivialTwoCopySubspace (n : ℕ) :
    Submodule ℂ (TwoCopyOperator n) :=
  Submodule.span ℂ
    ({(1 : TwoCopyOperator n), twoCopySwapOperator n} :
      Set (TwoCopyOperator n))

/-- Hilbert--Schmidt orthogonal complement of a matrix subspace, expressed
through the trace pairing `tr(Y†X)` because Base does not bundle an inner
product-space instance for matrices. -/
def hilbertSchmidtOrthogonalComplement {n : ℕ}
    (W : Submodule ℂ (TwoCopyOperator n)) :
    Submodule ℂ (TwoCopyOperator n) where
  carrier :=
    {X | ∀ Y, Y ∈ W →
      Matrix.trace (Y.conjTranspose * X) = 0}
  zero_mem' := by
    intro Y hY
    simp
  add_mem' := by
    intro A B hA hB Y hY
    rw [Matrix.mul_add, Matrix.trace_add, hA Y hY, hB Y hY, add_zero]
  smul_mem' := by
    intro c X hX Y hY
    rw [Matrix.mul_smul, Matrix.trace_smul, hX Y hY, smul_zero]

/-- The designated nontrivial two-copy sector: the Hilbert--Schmidt
orthogonal complement of the entire Haar-fixed identity/swap sector.  It is
canonical and cannot be replaced by an accidentally agreeing witness line. -/
def nontrivialTwoCopySubspace (n : ℕ) :
    Submodule ℂ (TwoCopyOperator n) :=
  hilbertSchmidtOrthogonalComplement (trivialTwoCopySubspace n)

/-- The source does not select a particular norm for the distance between
moment operators.  This structure records a genuine distance after restriction
to a declared two-copy subspace: zero distance means equality on that
subspace, and the usual nonnegativity, symmetry, and triangle laws hold. -/
structure RestrictedTwoCopyMomentDistance (n : ℕ) where
  distance :
    Submodule ℂ (TwoCopyOperator n) →
      TwoCopyMomentOperator n → TwoCopyMomentOperator n → ℝ
  nonnegative :
    ∀ W Phi Psi, 0 ≤ distance W Phi Psi
  eq_zero_iff :
    ∀ W Phi Psi,
      distance W Phi Psi = 0 ↔ ∀ X : W, Phi X = Psi X
  symmetric :
    ∀ W Phi Psi, distance W Phi Psi = distance W Psi Phi
  triangle :
    ∀ W Phi Psi Xi,
      distance W Phi Xi ≤ distance W Phi Psi + distance W Psi Xi

/-- The actual restricted distance between the circuit ensemble's second
moment and the Haar second moment. -/
def circuitToHaarSecondMomentDistance {n L : ℕ}
    (H : Fin L → QubitOperator n) (ensemble : LayerParameterEnsemble L)
    (haar : HaarExpectation n)
    (momentDistance : RestrictedTwoCopyMomentDistance n) : ℝ :=
  momentDistance.distance (nontrivialTwoCopySubspace n)
    (circuitSecondMomentOperator H ensemble)
    (haarSecondMomentOperator haar)

/-- The declared `L`-layer circuit ensemble is an `epsilon`-approximate
unitary `2`-design exactly when its restricted second-moment distance from Haar
is at most `epsilon`. -/
def IsApproximateUnitaryTwoDesign {n L : ℕ}
    (H : Fin L → QubitOperator n) (ensemble : LayerParameterEnsemble L)
    (haar : HaarExpectation n)
    (momentDistance : RestrictedTwoCopyMomentDistance n)
    (epsilon : ℝ) : Prop :=
  circuitToHaarSecondMomentDistance H ensemble haar
    momentDistance ≤ epsilon

/-- The logarithmic lower bound on the number of layers. -/
def twoDesignDepthThreshold (gamma epsilon : ℝ) : ℝ :=
  Real.log (1 / epsilon) / Real.log (1 / (1 - gamma))

/-- Under the stated contraction of the circuit ensemble's actual second
moment toward Haar, the displayed logarithmic depth is sufficient for an
`epsilon`-approximate unitary `2`-design. -/
theorem approximateTwoDesign_of_depth
    {n L : ℕ}
    (H : Fin L → QubitOperator n)
    (ensemble : LayerParameterEnsemble L)
    (hH : ∀ ell, IsHermitian (H ell))
    (hiH : ∀ ell, IsSkewHermitian (Complex.I • H ell))
    (hLie : HasFullSpecialUnitaryLieAlgebra H)
    (haar : HaarExpectation n)
    (momentDistance : RestrictedTwoCopyMomentDistance n)
    (p : ℕ → ℝ) (hpPolynomial : IsPolynomialFunction p)
    (hpPositive : 0 < p n)
    (gamma epsilon : ℝ)
    (hgammaPositive : 0 < gamma) (hgammaLessOne : gamma < 1)
    (hgap : 1 / p n ≤ gamma)
    (hcontraction :
      circuitToHaarSecondMomentDistance H ensemble haar
          momentDistance ≤
        (1 - gamma) ^ L)
    (hepsilon : epsilon ∈ Set.Ioo (0 : ℝ) 1)
    (hdepth : twoDesignDepthThreshold gamma epsilon ≤ (L : ℝ)) :
    IsApproximateUnitaryTwoDesign H ensemble haar
      momentDistance epsilon := by
  dsimp [IsApproximateUnitaryTwoDesign]
  refine hcontraction.trans ?_
  have hqpos : 0 < 1 - gamma := by linarith
  apply (Real.pow_le_iff_le_log (n := L) hqpos hepsilon.1).2
  have hdenpos : 0 < Real.log (1 / (1 - gamma)) :=
    Real.log_pos (one_lt_one_div hqpos (by linarith))
  rw [twoDesignDepthThreshold, div_le_iff₀ hdenpos] at hdepth
  simp only [one_div, Real.log_inv] at hdepth
  linarith

/-! ## Inverse-polynomial accuracy and asymptotic depth -/

/-- Uniform circuit-ensemble data used for the asymptotic
`O(p(n) log n)` depth claim.  Its contraction field concerns the second moment
computed from the actual generators and parameter law at every `(n,L)`. -/
structure SecondMomentContractionFamily where
  p : ℕ → ℝ
  p_polynomial : IsPolynomialFunction p
  p_positive : ∀ n, 0 < p n
  gamma : ℕ → ℝ
  gamma_positive : ∀ n, 0 < gamma n
  gamma_less_one : ∀ n, gamma n < 1
  gap_lower : ∀ n, 1 / p n ≤ gamma n
  generators : ∀ n L, Fin L → QubitOperator n
  generators_hermitian :
    ∀ n L ell, IsHermitian (generators n L ell)
  generators_skew :
    ∀ n L ell, IsSkewHermitian (Complex.I • generators n L ell)
  ensemble : ∀ _n L, LayerParameterEnsemble L
  haar : ∀ n, HaarExpectation n
  momentDistance : ∀ n, RestrictedTwoCopyMomentDistance n
  contraction :
    ∀ n L,
      circuitToHaarSecondMomentDistance
          (generators n L) (ensemble n L) (haar n)
          (momentDistance n) ≤
        (1 - gamma n) ^ L

/-- A concrete integer depth at inverse-polynomial accuracy
`epsilon_n = n^{-c}`. -/
def inversePolynomialDesignDepth
    (model : SecondMomentContractionFamily) (c : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (c * model.p n * Real.log (n : ℝ))

/-- For fixed `c > 0`, the concrete depth above eventually makes the actual
circuit ensemble at that depth an `n^{-c}`-approximate unitary `2`-design, and
the depth is `O(p(n) log n)` as `n → ∞`. -/
theorem inversePolynomialAccuracy_depth_isBigO
    (model : SecondMomentContractionFamily) (c : ℝ) (hc : 0 < c)
    (hfullLie :
      ∀ᶠ n in atTop,
        let L := inversePolynomialDesignDepth model c n
        HasFullSpecialUnitaryLieAlgebra (model.generators n L)) :
    (∀ᶠ n in atTop,
      let L := inversePolynomialDesignDepth model c n
      IsApproximateUnitaryTwoDesign
        (model.generators n L) (model.ensemble n L) (model.haar n)
        (model.momentDistance n) (Real.rpow (n : ℝ) (-c))) ∧
    Asymptotics.IsBigO atTop
      (fun n : ℕ => (inversePolynomialDesignDepth model c n : ℝ))
      (fun n : ℕ => model.p n * Real.log (n : ℝ)) := by
  constructor
  · filter_upwards [hfullLie, eventually_ge_atTop 2] with n hnLie hn
    dsimp only at hnLie ⊢
    have hnOne : 1 < (n : ℝ) := by exact_mod_cast hn
    have hnPos : 0 < (n : ℝ) := zero_lt_one.trans hnOne
    have hepsilonPos :
        0 < Real.rpow (n : ℝ) (-c) :=
      Real.rpow_pos_of_pos hnPos _
    have hepsilonLt :
        Real.rpow (n : ℝ) (-c) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hnOne (by linarith)
    refine approximateTwoDesign_of_depth
      (hH := model.generators_hermitian n
        (inversePolynomialDesignDepth model c n))
      (hiH := model.generators_skew n
        (inversePolynomialDesignDepth model c n))
      (hLie := hnLie)
      (p := model.p) (hpPolynomial := model.p_polynomial)
      (hpPositive := model.p_positive n)
      (gamma := model.gamma n)
      (epsilon := Real.rpow (n : ℝ) (-c))
      (hgammaPositive := model.gamma_positive n)
      (hgammaLessOne := model.gamma_less_one n)
      (hgap := model.gap_lower n)
      (hcontraction := model.contraction n
        (inversePolynomialDesignDepth model c n))
      (hepsilon := ⟨hepsilonPos, hepsilonLt⟩)
      (hdepth := ?_)
    have hqPos : 0 < 1 - model.gamma n := by
      linarith [model.gamma_less_one n]
    have hdenLower :
        1 / model.p n ≤
          Real.log (1 / (1 - model.gamma n)) := by
      calc
        1 / model.p n ≤ model.gamma n := model.gap_lower n
        _ ≤ Real.log (1 / (1 - model.gamma n)) := by
          rw [one_div, Real.log_inv]
          linarith [Real.log_le_sub_one_of_pos hqPos]
    have hdenPos :
        0 < Real.log (1 / (1 - model.gamma n)) :=
      lt_of_lt_of_le (one_div_pos.mpr (model.p_positive n)) hdenLower
    rw [twoDesignDepthThreshold, div_le_iff₀ hdenPos]
    rw [one_div, Real.log_inv, Real.rpow_eq_pow,
      Real.log_rpow hnPos (-c)]
    have hceil :
        c * model.p n * Real.log (n : ℝ) ≤
          (inversePolynomialDesignDepth model c n : ℝ) := by
      exact Nat.le_ceil _
    have hpDen :
        1 ≤
          Real.log (1 / (1 - model.gamma n)) * model.p n := by
      exact (div_le_iff₀ (model.p_positive n)).mp hdenLower
    have hlogNonnegative : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (le_of_lt hnOne)
    calc
      -(-c * Real.log (n : ℝ)) =
          c * Real.log (n : ℝ) := by ring
      _ ≤ (c * Real.log (n : ℝ)) *
          (Real.log (1 / (1 - model.gamma n)) * model.p n) :=
        by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hpDen
              (mul_nonneg hc.le hlogNonnegative)
      _ = (c * model.p n * Real.log (n : ℝ)) *
          Real.log (1 / (1 - model.gamma n)) := by ring
      _ ≤ (inversePolynomialDesignDepth model c n : ℝ) *
          Real.log (1 / (1 - model.gamma n)) :=
        mul_le_mul_of_nonneg_right hceil hdenPos.le
  · apply Asymptotics.IsBigO.of_bound
      (c + (Real.log 2)⁻¹)
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnOne : 1 < (n : ℝ) := by exact_mod_cast hn
    have hlogNonnegative : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (le_of_lt hnOne)
    have hpInvLt :
        1 / model.p n < 1 :=
      (model.gap_lower n).trans_lt (model.gamma_less_one n)
    have hpOne : 1 ≤ model.p n :=
      (div_lt_one (model.p_positive n)).mp hpInvLt |>.le
    have hbaseNonnegative :
        0 ≤ model.p n * Real.log (n : ℝ) :=
      mul_nonneg (model.p_positive n).le hlogNonnegative
    have hlogTwoPos : 0 < Real.log 2 :=
      Real.log_pos (by norm_num)
    have hlogLower :
        Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have hbaseLower :
        Real.log 2 ≤ model.p n * Real.log (n : ℝ) :=
      hlogLower.trans <|
        show Real.log (n : ℝ) ≤
          model.p n * Real.log (n : ℝ) by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hpOne hlogNonnegative
    have hone :
        1 ≤ (Real.log 2)⁻¹ *
          (model.p n * Real.log (n : ℝ)) := by
      calc
        1 = (Real.log 2)⁻¹ * Real.log 2 := by
          field_simp
        _ ≤ (Real.log 2)⁻¹ *
            (model.p n * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hbaseLower
            (inv_nonneg.mpr hlogTwoPos.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg hbaseNonnegative]
    have hargumentNonnegative :
        0 ≤ c * model.p n * Real.log (n : ℝ) :=
      mul_nonneg (mul_nonneg hc.le (model.p_positive n).le)
        hlogNonnegative
    calc
      (inversePolynomialDesignDepth model c n : ℝ) ≤
          c * model.p n * Real.log (n : ℝ) + 1 :=
        (Nat.ceil_lt_add_one hargumentNonnegative).le
      _ = c * (model.p n * Real.log (n : ℝ)) + 1 := by ring
      _ ≤ c * (model.p n * Real.log (n : ℝ)) +
          (Real.log 2)⁻¹ *
            (model.p n * Real.log (n : ℝ)) :=
        add_le_add_right hone _
      _ = (c + (Real.log 2)⁻¹) *
          (model.p n * Real.log (n : ℝ)) := by ring

/-! ## Exact Haar averages and loss fluctuations -/

/-- Density operators on `n` qubits: Hermitian, positive semidefinite, and of
unit trace.  Positivity is stated through nonnegative quadratic forms. -/
structure DensityOperator (n : ℕ) where
  op : QubitOperator n
  hermitian : IsHermitian op
  positiveSemidefinite :
    ∀ psi : StateVector (Qubits n),
      0 ≤ (inner ℂ psi (HilbertOperator.applyVec op psi)).re
  trace_one : Matrix.trace op = 1

/-- A traceless Hermitian observable satisfying `tr(O^2) ≤ 2^n`. -/
structure BoundedTracelessObservable (n : ℕ) where
  op : QubitOperator n
  hermitian : IsHermitian op
  traceless : Matrix.trace op = 0
  squareTrace_le_dimension :
    (Matrix.trace (op * op)).re ≤ (qubitDimension n : ℝ)

/-- The rank-one projector `|psi><psi|`. -/
def pureProjector {n : ℕ} (psi : PureState (Qubits n)) :
    QubitOperator n :=
  fun i j => psi i * star (psi j)

/-- Unitary conjugation of a state by an `SU(2^n)` matrix. -/
def conjugatedState {n : ℕ} (U : SpecialUnitary n)
    (rho : QubitOperator n) : QubitOperator n :=
  (U.1 * rho) * U.1.conjTranspose

/-- The real Haar loss
`f_U(rho,O) = tr(U rho U† O)`.  The real part is explicit in Lean; under the
Hermiticity assumptions the complex trace has zero imaginary part. -/
def haarLoss {n : ℕ} (U : SpecialUnitary n)
    (rho O : QubitOperator n) : ℝ :=
  (Matrix.trace (conjugatedState U rho * O)).re

/-- Haar loss is a continuous observable of the special-unitary matrix.  This
regularity follows from finite sums and products of matrix coordinates and is
not an extra hypothesis on the physical data. -/
theorem haarLoss_continuous {n : ℕ}
    (rho O : QubitOperator n) :
    Continuous (fun U : SpecialUnitary n => haarLoss U rho O) := by
  have hentry (i j : Fin (qubitDimension n)) :
      Continuous (fun U : SpecialUnitary n => U.1 i j) := by
    exact (continuous_apply_apply i j).comp continuous_subtype_val
  continuity

/-- The loss bundled in the continuous-observable carrier of exact Haar
expectation. -/
def haarLossObservable {n : ℕ} (rho O : QubitOperator n) :
    HaarObservable n where
  toFun U := haarLoss U rho O
  continuous_toFun := haarLoss_continuous rho O

/-- The squared centered version of a continuous Haar observable. -/
def centeredSquareHaarObservable {n : ℕ} (haar : HaarExpectation n)
    (f : HaarObservable n) : HaarObservable n where
  toFun U := (f U - haar.expectation f) ^ 2
  continuous_toFun :=
    (f.continuous.sub continuous_const).pow 2

/-- Variance with respect to exact normalized Haar expectation. -/
def haarVariance {n : ℕ} (haar : HaarExpectation n)
    (f : HaarObservable n) : ℝ :=
  haar.expectation (centeredSquareHaarObservable haar f)

/-- Root-mean-square Haar fluctuation. -/
def haarRMSFluctuation {n : ℕ} (haar : HaarExpectation n)
    (f : HaarObservable n) : ℝ :=
  Real.sqrt (haarVariance haar f)

/-- Scalar coordinates of the tensor square of a conjugated state vary
continuously with the special-unitary matrix. -/
theorem conjugatedStateTensorSquare_continuous_entry {n : ℕ}
    (rho : QubitOperator n)
    (a b : Fin (qubitDimension n) × Fin (qubitDimension n)) :
    Continuous (fun U : SpecialUnitary n =>
      Matrix.kronecker
        (conjugatedState U rho)
        (conjugatedState U rho) a b) := by
  have hentry (i j : Fin (qubitDimension n)) :
      Continuous (fun U : SpecialUnitary n => U.1 i j) := by
    exact (continuous_apply_apply i j).comp continuous_subtype_val
  continuity

/-- Exact Haar expectation of the tensor square of a conjugated state, using
the same continuous Haar law that defines the first moment and variance. -/
def haarTwoCopyStateExpectation {n : ℕ} (haar : HaarExpectation n)
    (rho : QubitOperator n) :
    Matrix (Fin (qubitDimension n) × Fin (qubitDimension n))
      (Fin (qubitDimension n) × Fin (qubitDimension n)) ℂ :=
  haarExpectedMatrix haar
    (fun U =>
      Matrix.kronecker
        (conjugatedState U rho)
        (conjugatedState U rho))
    (conjugatedStateTensorSquare_continuous_entry rho)

/-- The normalization `1 / (N(N+1))` appearing in the Haar second moment. -/
def haarSecondMomentNormalization (n : ℕ) : ℂ :=
  ((qubitDimension n : ℂ) * ((qubitDimension n : ℂ) + 1))⁻¹

/-- Additivity of the complexification of the real Haar functional. -/
theorem haarComplexExpectation_add {n : ℕ} (haar : HaarExpectation n)
    (f g : ContinuousMap (SpecialUnitary n) ℂ) :
    haarComplexExpectation haar
        ⟨fun U => f U + g U, f.continuous.add g.continuous⟩ =
      haarComplexExpectation haar f + haarComplexExpectation haar g := by
  let fr : HaarObservable n :=
    ⟨fun U => (f U).re, Complex.continuous_re.comp f.continuous⟩
  let fi : HaarObservable n :=
    ⟨fun U => (f U).im, Complex.continuous_im.comp f.continuous⟩
  let gr : HaarObservable n :=
    ⟨fun U => (g U).re, Complex.continuous_re.comp g.continuous⟩
  let gi : HaarObservable n :=
    ⟨fun U => (g U).im, Complex.continuous_im.comp g.continuous⟩
  have hre :
      haar.expectation
          ⟨fun U => (f U + g U).re,
            Complex.continuous_re.comp
              (f.continuous.add g.continuous)⟩ =
        haar.expectation fr + haar.expectation gr := by
    calc
      _ = haar.expectation
          ⟨fun U => fr U + gr U,
            fr.continuous.add gr.continuous⟩ := by
            congr 1
      _ = haar.expectation fr + haar.expectation gr :=
        haar.map_add fr gr
  have him :
      haar.expectation
          ⟨fun U => (f U + g U).im,
            Complex.continuous_im.comp
              (f.continuous.add g.continuous)⟩ =
        haar.expectation fi + haar.expectation gi := by
    calc
      _ = haar.expectation
          ⟨fun U => fi U + gi U,
            fi.continuous.add gi.continuous⟩ := by
            congr 1
      _ = haar.expectation fi + haar.expectation gi :=
        haar.map_add fi gi
  unfold haarComplexExpectation
  change
    haar.expectation ⟨fun U => (f U + g U).re, _⟩ +
        Complex.I *
          haar.expectation ⟨fun U => (f U + g U).im, _⟩ =
      (haar.expectation fr + Complex.I * haar.expectation fi) +
        (haar.expectation gr + Complex.I * haar.expectation gi)
  rw [hre, him]
  push_cast
  ring

/-- Complex homogeneity of the complexified Haar functional. -/
theorem haarComplexExpectation_mul {n : ℕ} (haar : HaarExpectation n)
    (c : ℂ) (f : ContinuousMap (SpecialUnitary n) ℂ) :
    haarComplexExpectation haar
        ⟨fun U => c * f U, continuous_const.mul f.continuous⟩ =
      c * haarComplexExpectation haar f := by
  let fr : HaarObservable n :=
    ⟨fun U => (f U).re, Complex.continuous_re.comp f.continuous⟩
  let fi : HaarObservable n :=
    ⟨fun U => (f U).im, Complex.continuous_im.comp f.continuous⟩
  let crfr : HaarObservable n :=
    ⟨fun U => c.re * fr U, continuous_const.mul fr.continuous⟩
  let ncifi : HaarObservable n :=
    ⟨fun U => (-c.im) * fi U, continuous_const.mul fi.continuous⟩
  let cifr : HaarObservable n :=
    ⟨fun U => c.im * fr U, continuous_const.mul fr.continuous⟩
  let crfi : HaarObservable n :=
    ⟨fun U => c.re * fi U, continuous_const.mul fi.continuous⟩
  have hre :
      haar.expectation
          ⟨fun U => (c * f U).re,
            Complex.continuous_re.comp
              (continuous_const.mul f.continuous)⟩ =
        c.re * haar.expectation fr -
          c.im * haar.expectation fi := by
    calc
      _ = haar.expectation
          ⟨fun U => crfr U + ncifi U,
            crfr.continuous.add ncifi.continuous⟩ := by
            congr 1
            ext U
            simp [crfr, ncifi, fr, fi, Complex.mul_re,
              sub_eq_add_neg]
      _ = haar.expectation crfr + haar.expectation ncifi :=
        haar.map_add crfr ncifi
      _ = c.re * haar.expectation fr +
          (-c.im) * haar.expectation fi := by
        rw [haar.map_smul, haar.map_smul]
      _ = c.re * haar.expectation fr -
          c.im * haar.expectation fi := by ring
  have him :
      haar.expectation
          ⟨fun U => (c * f U).im,
            Complex.continuous_im.comp
              (continuous_const.mul f.continuous)⟩ =
        c.im * haar.expectation fr +
          c.re * haar.expectation fi := by
    calc
      _ = haar.expectation
          ⟨fun U => cifr U + crfi U,
            cifr.continuous.add crfi.continuous⟩ := by
            congr 1
            ext U
            simp [cifr, crfi, fr, fi, Complex.mul_im, add_comm]
      _ = haar.expectation cifr + haar.expectation crfi :=
        haar.map_add cifr crfi
      _ = c.im * haar.expectation fr +
          c.re * haar.expectation fi := by
        rw [haar.map_smul, haar.map_smul]
  unfold haarComplexExpectation
  change
    haar.expectation
          ⟨fun U => (c * f U).re, _⟩ +
        Complex.I * haar.expectation
          ⟨fun U => (c * f U).im, _⟩ =
      c * (haar.expectation fr +
        Complex.I * haar.expectation fi)
  rw [hre, him]
  apply Complex.ext <;> simp [mul_add, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- The real part of complex Haar expectation is the expectation of the real
part. -/
theorem haarComplexExpectation_re {n : ℕ} (haar : HaarExpectation n)
    (f : ContinuousMap (SpecialUnitary n) ℂ) :
    (haarComplexExpectation haar f).re =
      haar.expectation
        ⟨fun U => (f U).re,
          Complex.continuous_re.comp f.continuous⟩ := by
  simp [haarComplexExpectation]

/-- Complex Haar expectation inherits left invariance. -/
theorem haarComplexExpectation_left_invariant {n : ℕ}
    (haar : HaarExpectation n) (V : SpecialUnitary n)
    (f : ContinuousMap (SpecialUnitary n) ℂ) :
    haarComplexExpectation haar
        ⟨fun U => f (V * U),
          f.continuous.comp (continuous_const.mul continuous_id)⟩ =
      haarComplexExpectation haar f := by
  let fr : HaarObservable n :=
    ⟨fun U => (f U).re, Complex.continuous_re.comp f.continuous⟩
  let fi : HaarObservable n :=
    ⟨fun U => (f U).im, Complex.continuous_im.comp f.continuous⟩
  have hre :
      haar.expectation
          ⟨fun U => (f (V * U)).re,
            Complex.continuous_re.comp <|
              f.continuous.comp
                (continuous_const.mul continuous_id)⟩ =
        haar.expectation fr := by
    calc
      _ = haar.expectation (leftTranslateHaarObservable V fr) := by
        congr 1
      _ = haar.expectation fr := haar.left_invariant V fr
  have him :
      haar.expectation
          ⟨fun U => (f (V * U)).im,
            Complex.continuous_im.comp <|
              f.continuous.comp
                (continuous_const.mul continuous_id)⟩ =
        haar.expectation fi := by
    calc
      _ = haar.expectation (leftTranslateHaarObservable V fi) := by
        congr 1
      _ = haar.expectation fi := haar.left_invariant V fi
  unfold haarComplexExpectation
  change
    haar.expectation ⟨fun U => (f (V * U)).re, _⟩ +
        Complex.I *
          haar.expectation ⟨fun U => (f (V * U)).im, _⟩ =
      haar.expectation fr + Complex.I * haar.expectation fi
  rw [hre, him]

/-- A determinant-one diagonal unitary whose two distinguished phases are
`i` and `-i`. -/
def twoPhaseSpecialUnitary {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    Matrix.specialUnitaryGroup ι ℂ := by
  let d : ι → ℂ := fun k =>
    if k = i then Complex.I else if k = j then -Complex.I else 1
  let D : Matrix ι ι ℂ := Matrix.diagonal d
  refine ⟨D, (Matrix.mem_specialUnitaryGroup_iff).2 ⟨?_, ?_⟩⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    have hstar :
        star D = Matrix.diagonal (fun k => star (d k)) := by
      ext k l
      by_cases hkl : k = l
      · subst l
        simp [D, Matrix.star_apply]
      · simp [D, Matrix.star_apply, Matrix.diagonal, hkl, Ne.symm hkl]
    rw [hstar, Matrix.diagonal_mul_diagonal]
    ext k l
    by_cases hkl : k = l
    · subst l
      by_cases hki : k = i
      · subst k
        norm_num [d]
      · by_cases hkj : k = j
        · subst k
          norm_num [d, hki]
        · simp [d, hki, hkj]
    · simp [Matrix.diagonal, hkl]
  · rw [Matrix.det_diagonal]
    have hd (k : ι) :
        d k =
          (if k = i then Complex.I else 1) *
            (if k = j then -Complex.I else 1) := by
      by_cases hki : k = i
      · subst k
        simp [d, hij]
      · by_cases hkj : k = j
        · subst k
          simp [d, hki]
        · simp [d, hki, hkj]
    calc
      ∏ k, d k = ∏ k,
          ((if k = i then Complex.I else 1) *
            (if k = j then -Complex.I else 1)) := by
              apply Finset.prod_congr rfl
              intro k hk
              exact hd k
      _ = (∏ k, if k = i then Complex.I else 1) *
          (∏ k, if k = j then -Complex.I else 1) :=
        Finset.prod_mul_distrib
      _ = 1 := by simp

/-- A determinant-one signed transposition matrix. -/
def swapSpecialUnitary {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    Matrix.specialUnitaryGroup ι ℂ := by
  let d : ι → ℂ := fun k => if k = i then -1 else 1
  let D : Matrix ι ι ℂ := Matrix.diagonal d
  let W : Matrix ι ι ℂ := (Equiv.swap i j).permMatrix ℂ
  have hD : D ∈ Matrix.unitaryGroup ι ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hstar :
        star D = Matrix.diagonal (fun k => star (d k)) := by
      ext k l
      by_cases hkl : k = l
      · subst l
        simp [D, Matrix.star_apply]
      · simp [D, Matrix.star_apply, Matrix.diagonal, hkl, Ne.symm hkl]
    rw [hstar, Matrix.diagonal_mul_diagonal]
    ext k l
    by_cases hkl : k = l
    · subst l
      by_cases hki : k = i <;> simp [d, hki]
    · simp [Matrix.diagonal, hkl]
  have hW : W ∈ Matrix.unitaryGroup ι ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp
  refine ⟨D * W, (Matrix.mem_specialUnitaryGroup_iff).2 ⟨?_, ?_⟩⟩
  · exact (Matrix.unitaryGroup ι ℂ).mul_mem hD hW
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    have hdprod : ∏ k, d k = -1 := by simp [d]
    rw [hdprod]
    simp [W, Equiv.Perm.sign_swap hij]

/-- Multiplying Haar variables on the left conjugates the state on the left
and right by the translating unitary. -/
theorem conjugatedState_mul {n : ℕ} (V U : SpecialUnitary n)
    (rho : QubitOperator n) :
    conjugatedState (V * U) rho =
      (V.1 * conjugatedState U rho) * V.1.conjTranspose := by
  simp only [conjugatedState, Submonoid.coe_mul,
    Matrix.conjTranspose_mul]
  noncomm_ring

/-- Complex Haar expectation of the zero observable. -/
theorem haarComplexExpectation_zero {n : ℕ} (haar : HaarExpectation n) :
    haarComplexExpectation haar
        (ContinuousMap.const (SpecialUnitary n) 0) = 0 := by
  let z : HaarObservable n :=
    ContinuousMap.const (SpecialUnitary n) 0
  let one : HaarObservable n :=
    ContinuousMap.const (SpecialUnitary n) 1
  have hz : haar.expectation z = 0 := by
    calc
      haar.expectation z =
          haar.expectation
            ⟨fun U => 0 * one U,
              continuous_const.mul one.continuous⟩ := by
                congr 1
                ext U
                simp [z, one]
      _ = 0 * haar.expectation one := haar.map_smul 0 one
      _ = 0 := zero_mul _
  unfold haarComplexExpectation
  change
    (haar.expectation z : ℂ) +
        Complex.I * (haar.expectation z : ℂ) = 0
  rw [hz]
  norm_num

/-- Complex Haar expectation commutes with finite sums. -/
theorem haarComplexExpectation_sum {n : ℕ} (haar : HaarExpectation n)
    {ι : Type} [Fintype ι]
    (f : ι → ContinuousMap (SpecialUnitary n) ℂ) :
    haarComplexExpectation haar
        ⟨fun U => ∑ i, f i U,
          continuous_finset_sum _ fun i _ => (f i).continuous⟩ =
      ∑ i, haarComplexExpectation haar (f i) := by
  classical
  have hs : ∀ s : Finset ι,
      haarComplexExpectation haar
          ⟨fun U => ∑ i ∈ s, f i U,
            continuous_finset_sum _ fun i _ => (f i).continuous⟩ =
        ∑ i ∈ s, haarComplexExpectation haar (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        calc
          haarComplexExpectation haar
              ⟨fun U => ∑ i ∈ (∅ : Finset ι), f i U, _⟩ =
            haarComplexExpectation haar
              (ContinuousMap.const (SpecialUnitary n) 0) := by
                congr 2
          _ = 0 := haarComplexExpectation_zero haar
    | @insert a s ha ih =>
        let fs : ContinuousMap (SpecialUnitary n) ℂ :=
          ⟨fun U => ∑ i ∈ s, f i U,
            continuous_finset_sum _ fun i _ => (f i).continuous⟩
        calc
          haarComplexExpectation haar
              ⟨fun U => ∑ i ∈ insert a s, f i U, _⟩ =
            haarComplexExpectation haar
              ⟨fun U => f a U + fs U,
                (f a).continuous.add fs.continuous⟩ := by
                  congr 1
                  ext U
                  simp [fs, ha]
          _ = haarComplexExpectation haar (f a) +
              haarComplexExpectation haar fs :=
            haarComplexExpectation_add haar (f a) fs
          _ = ∑ i ∈ insert a s,
              haarComplexExpectation haar (f i) := by
            rw [ih]
            simp [ha]
  simpa using hs Finset.univ

/-- Continuity of a scalar coordinate of the conjugated state. -/
theorem conjugatedState_continuous_entry {n : ℕ}
    (rho : QubitOperator n) (a b : Fin (qubitDimension n)) :
    Continuous (fun U : SpecialUnitary n =>
      conjugatedState U rho a b) := by
  have hentry (i j : Fin (qubitDimension n)) :
      Continuous (fun U : SpecialUnitary n => U.1 i j) := by
    exact (continuous_apply_apply i j).comp continuous_subtype_val
  continuity

/-- The first Haar moment of a conjugated state. -/
def haarFirstStateExpectation {n : ℕ} (haar : HaarExpectation n)
    (rho : QubitOperator n) : QubitOperator n :=
  haarExpectedMatrix haar (fun U => conjugatedState U rho)
    (conjugatedState_continuous_entry rho)

/-- The two-phase special unitary negates the corresponding off-diagonal
matrix coordinate under conjugation. -/
theorem twoPhaseSpecialUnitary_conjugation_entry
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) (hij : i ≠ j) :
    let V := twoPhaseSpecialUnitary i j hij
    ((V.1 * A) * V.1.conjTranspose) i j = -A i j := by
  simp [twoPhaseSpecialUnitary, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.conjTranspose_apply, hij, Ne.symm hij]
  calc
    Complex.I * A i j * Complex.I =
        (Complex.I * Complex.I) * A i j := by ring
    _ = -A i j := by rw [Complex.I_mul_I]; ring

/-- The signed swap special unitary interchanges the two corresponding
diagonal coordinates under conjugation. -/
theorem swapSpecialUnitary_conjugation_diagonal
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) (hij : i ≠ j) :
    let V := swapSpecialUnitary i j hij
    ((V.1 * A) * V.1.conjTranspose) i i = A j j := by
  let d : ι → ℂ := fun k => if k = i then -1 else 1
  let D : Matrix ι ι ℂ := Matrix.diagonal d
  let W : Matrix ι ι ℂ := (Equiv.swap i j).permMatrix ℂ
  change (((D * W) * A) * (D * W).conjTranspose) i i = A j j
  rw [Matrix.conjTranspose_mul]
  have hstarD :
      D.conjTranspose = Matrix.diagonal (fun k => star (d k)) := by
    ext k l
    by_cases hkl : k = l
    · subst l
      simp [D, Matrix.conjTranspose_apply]
    · simp [D, Matrix.conjTranspose_apply, Matrix.diagonal,
        hkl, Ne.symm hkl]
  have hreassociate :
      (((D * W) * A) * (W.conjTranspose * D.conjTranspose)) =
        (D * ((W * A) * W.conjTranspose)) * D.conjTranspose := by
    noncomm_ring
  rw [hreassociate]
  change
    ((Matrix.diagonal d * ((W * A) * W.conjTranspose)) *
        D.conjTranspose) i i = A j j
  rw [hstarD, Matrix.mul_diagonal]
  rw [Matrix.diagonal_mul]
  have hperm :
      ((W * A) * W.conjTranspose) i i = A j j := by
    rw [show W.conjTranspose =
        ((Equiv.swap i j)⁻¹).permMatrix ℂ by
          simpa [W] using
            (Matrix.conjTranspose_permMatrix (R := ℂ)
              (Equiv.swap i j))]
    rw [PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    simp [W, Matrix.submatrix_apply]
  rw [hperm]
  simp [d]

/-- Off-diagonal entries of the first conjugation moment vanish by invariance
under a two-phase diagonal special unitary. -/
theorem haarFirstStateExpectation_offDiagonal
    {n : ℕ} (haar : HaarExpectation n) (rho : QubitOperator n)
    (i j : Fin (qubitDimension n)) (hij : i ≠ j) :
    haarFirstStateExpectation haar rho i j = 0 := by
  let f : ContinuousMap (SpecialUnitary n) ℂ :=
    ⟨fun U => conjugatedState U rho i j,
      conjugatedState_continuous_entry rho i j⟩
  let V : SpecialUnitary n := twoPhaseSpecialUnitary i j hij
  let translated : ContinuousMap (SpecialUnitary n) ℂ :=
    ⟨fun U => f (V * U),
      f.continuous.comp (continuous_const.mul continuous_id)⟩
  let negated : ContinuousMap (SpecialUnitary n) ℂ :=
    ⟨fun U => (-1 : ℂ) * f U,
      continuous_const.mul f.continuous⟩
  have htranslate :
      haarComplexExpectation haar translated =
        haarComplexExpectation haar f :=
    haarComplexExpectation_left_invariant haar V f
  have hpoint : translated = negated := by
    ext U
    change conjugatedState (V * U) rho i j =
      (-1 : ℂ) * conjugatedState U rho i j
    rw [conjugatedState_mul]
    simpa [V] using
      twoPhaseSpecialUnitary_conjugation_entry
        (conjugatedState U rho) i j hij
  have hnegate :
      haarComplexExpectation haar negated =
        (-1 : ℂ) * haarComplexExpectation haar f :=
    haarComplexExpectation_mul haar (-1) f
  change haarComplexExpectation haar f = 0
  have hself :
      haarComplexExpectation haar f =
        (-1 : ℂ) * haarComplexExpectation haar f := by
    calc
      haarComplexExpectation haar f =
          haarComplexExpectation haar translated := htranslate.symm
      _ = haarComplexExpectation haar negated :=
        congrArg (haarComplexExpectation haar) hpoint
      _ = (-1 : ℂ) * haarComplexExpectation haar f := hnegate
  linear_combination (2 : ℂ)⁻¹ * hself

/-- All diagonal entries of the first conjugation moment agree, by invariance
under signed transpositions. -/
theorem haarFirstStateExpectation_diagonal_eq
    {n : ℕ} (haar : HaarExpectation n) (rho : QubitOperator n)
    (i j : Fin (qubitDimension n)) :
    haarFirstStateExpectation haar rho i i =
      haarFirstStateExpectation haar rho j j := by
  by_cases hij : i = j
  · subst j
    rfl
  let fi : ContinuousMap (SpecialUnitary n) ℂ :=
    ⟨fun U => conjugatedState U rho i i,
      conjugatedState_continuous_entry rho i i⟩
  let fj : ContinuousMap (SpecialUnitary n) ℂ :=
    ⟨fun U => conjugatedState U rho j j,
      conjugatedState_continuous_entry rho j j⟩
  let V : SpecialUnitary n := swapSpecialUnitary i j hij
  let translated : ContinuousMap (SpecialUnitary n) ℂ :=
    ⟨fun U => fi (V * U),
      fi.continuous.comp (continuous_const.mul continuous_id)⟩
  have htranslate :
      haarComplexExpectation haar translated =
        haarComplexExpectation haar fi :=
    haarComplexExpectation_left_invariant haar V fi
  have hpoint : translated = fj := by
    ext U
    change conjugatedState (V * U) rho i i =
      conjugatedState U rho j j
    rw [conjugatedState_mul]
    simpa [V] using
      swapSpecialUnitary_conjugation_diagonal
        (conjugatedState U rho) i j hij
  change haarComplexExpectation haar fi =
    haarComplexExpectation haar fj
  rw [← htranslate, hpoint]

/-- Exact Haar randomness gives zero mean loss for every density operator and
every traceless Hermitian observable.  In particular, this theorem must derive
the required first-moment consequence from normalized bi-invariance; it is not
assumed as a field of `HaarExpectation`. -/
theorem haarLoss_mean_zero
    {n : ℕ} (haar : HaarExpectation n)
    (rho : DensityOperator n) (O : BoundedTracelessObservable n) :
    haar.expectation (haarLossObservable rho.op O.op) = 0 := by
  let base :
      (Fin (qubitDimension n) × Fin (qubitDimension n)) →
        ContinuousMap (SpecialUnitary n) ℂ :=
    fun x =>
      ⟨fun U => conjugatedState U rho.op x.1 x.2,
        conjugatedState_continuous_entry rho.op x.1 x.2⟩
  let term :
      (Fin (qubitDimension n) × Fin (qubitDimension n)) →
        ContinuousMap (SpecialUnitary n) ℂ :=
    fun x =>
      ⟨fun U => O.op x.2 x.1 * base x U,
        continuous_const.mul (base x).continuous⟩
  let total : ContinuousMap (SpecialUnitary n) ℂ :=
    ⟨fun U => ∑ x, term x U,
      continuous_finset_sum _ fun x _ => (term x).continuous⟩
  have htotalPoint (U : SpecialUnitary n) :
      total U =
        Matrix.trace (conjugatedState U rho.op * O.op) := by
    change
      (∑ x :
          Fin (qubitDimension n) × Fin (qubitDimension n),
        O.op x.2 x.1 *
          conjugatedState U rho.op x.1 x.2) =
        Matrix.trace (conjugatedState U rho.op * O.op)
    rw [Fintype.sum_prod_type, Matrix.trace]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hreal :
      haar.expectation (haarLossObservable rho.op O.op) =
        (haarComplexExpectation haar total).re := by
    calc
      haar.expectation (haarLossObservable rho.op O.op) =
          haar.expectation
            ⟨fun U => (total U).re,
              Complex.continuous_re.comp total.continuous⟩ := by
                congr 1
                ext U
                change haarLoss U rho.op O.op = (total U).re
                rw [htotalPoint]
                rfl
      _ = (haarComplexExpectation haar total).re :=
        (haarComplexExpectation_re haar total).symm
  have hterm (x :
      Fin (qubitDimension n) × Fin (qubitDimension n)) :
      haarComplexExpectation haar (term x) =
        O.op x.2 x.1 *
          haarFirstStateExpectation haar rho.op x.1 x.2 := by
    change
      haarComplexExpectation haar
          ⟨fun U => O.op x.2 x.1 * base x U, _⟩ =
        O.op x.2 x.1 * haarComplexExpectation haar (base x)
    exact haarComplexExpectation_mul haar (O.op x.2 x.1) (base x)
  have htotalExpectation :
      haarComplexExpectation haar total =
        ∑ x :
            Fin (qubitDimension n) × Fin (qubitDimension n),
          O.op x.2 x.1 *
            haarFirstStateExpectation haar rho.op x.1 x.2 := by
    calc
      haarComplexExpectation haar total =
          ∑ x :
              Fin (qubitDimension n) × Fin (qubitDimension n),
            haarComplexExpectation haar (term x) :=
        haarComplexExpectation_sum haar term
      _ = ∑ x :
              Fin (qubitDimension n) × Fin (qubitDimension n),
            O.op x.2 x.1 *
              haarFirstStateExpectation haar rho.op x.1 x.2 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hterm x
  have hsumZero :
      (∑ x :
          Fin (qubitDimension n) × Fin (qubitDimension n),
        O.op x.2 x.1 *
          haarFirstStateExpectation haar rho.op x.1 x.2) = 0 := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ i, ∑ j,
          O.op j i *
            haarFirstStateExpectation haar rho.op i j) =
          ∑ i, O.op i i *
            haarFirstStateExpectation haar rho.op i i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_eq_single i]
        · intro j hj hji
          rw [haarFirstStateExpectation_offDiagonal
            haar rho.op i j (Ne.symm hji)]
          simp
        · simp
      _ = ∑ i, O.op i i *
            haarFirstStateExpectation haar rho.op 0 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [haarFirstStateExpectation_diagonal_eq
          haar rho.op i 0]
      _ = Matrix.trace O.op *
            haarFirstStateExpectation haar rho.op 0 0 := by
        change
          (∑ i, O.op i i *
            haarFirstStateExpectation haar rho.op 0 0) =
          (∑ i, O.op i i) *
            haarFirstStateExpectation haar rho.op 0 0
        rw [Finset.sum_mul]
      _ = 0 := by rw [O.traceless, zero_mul]
  rw [hreal, htotalExpectation, hsumZero]
  norm_num

/-- Contracting `O ⊗ O` against the identity-plus-swap tensor gives the
standard two trace invariants. -/
theorem identity_add_swap_contraction {n : ℕ} (O : QubitOperator n) :
    (∑ x :
        (Fin (qubitDimension n) × Fin (qubitDimension n)) ×
          (Fin (qubitDimension n) × Fin (qubitDimension n)),
      O x.1.2 x.1.1 * O x.2.2 x.2.1 *
        ((1 : Matrix
            (Fin (qubitDimension n) × Fin (qubitDimension n))
            (Fin (qubitDimension n) × Fin (qubitDimension n)) ℂ) +
          tensorSwap n)
          (x.1.1, x.2.1) (x.1.2, x.2.2)) =
      Matrix.trace O * Matrix.trace O + Matrix.trace (O * O) := by
  simp only [Fintype.sum_prod_type, Matrix.add_apply, Matrix.one_apply,
    tensorSwap]
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  · simp only [Matrix.trace, Matrix.diag]
    simp only [Prod.mk.injEq, ite_and]
    simp
    simpa [pow_two] using
      (Finset.sum_mul_sum (Finset.univ) (Finset.univ)
        (fun x => O x x) (fun x => O x x)).symm
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    simp only [Prod.mk.injEq, ite_and]
    simp
    rw [Finset.sum_comm]

/-- For a pure input state, the explicitly assumed Haar two-copy identity
implies the exact loss variance and the bound `1/(N+1)`.  The identity is
stated for `|psi><psi|`; `hrhoPure` is therefore the necessary bridge to the
variance of the declared density operator `rho`. -/
theorem haarLoss_variance
    {n : ℕ} (haar : HaarExpectation n)
    (rho : DensityOperator n) (psi : PureState (Qubits n))
    (hrhoPure : rho.op = pureProjector psi)
    (O : BoundedTracelessObservable n)
    (hHaarSecondMoment :
      haarTwoCopyStateExpectation haar (pureProjector psi) =
        haarSecondMomentNormalization n •
          ((1 : Matrix
              (Fin (qubitDimension n) × Fin (qubitDimension n))
              (Fin (qubitDimension n) × Fin (qubitDimension n)) ℂ) +
            tensorSwap n)) :
    haarVariance haar (haarLossObservable rho.op O.op) =
        (Matrix.trace (O.op * O.op)).re /
          ((qubitDimension n : ℝ) * ((qubitDimension n : ℝ) + 1)) ∧
      haarVariance haar (haarLossObservable rho.op O.op) ≤
        1 / ((qubitDimension n : ℝ) + 1) := by
  have hmean :
      haar.expectation (haarLossObservable rho.op O.op) = 0 :=
    haarLoss_mean_zero haar rho O
  have hstateHermitian (U : SpecialUnitary n) :
      (conjugatedState U rho.op).conjTranspose =
        conjugatedState U rho.op := by
    have hrho := rho.hermitian
    unfold IsHermitian at hrho
    unfold conjugatedState
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hrho,
      Matrix.mul_assoc]
  have htraceReal (U : SpecialUnitary n) :
      star (Matrix.trace (conjugatedState U rho.op * O.op)) =
        Matrix.trace (conjugatedState U rho.op * O.op) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      hstateHermitian U, O.hermitian]
    exact Matrix.trace_mul_comm O.op (conjugatedState U rho.op)
  let base :
      ((Fin (qubitDimension n) × Fin (qubitDimension n)) ×
        (Fin (qubitDimension n) × Fin (qubitDimension n))) →
        ContinuousMap (SpecialUnitary n) ℂ :=
    fun x =>
      ⟨fun U =>
          conjugatedState U rho.op x.1.1 x.1.2 *
            conjugatedState U rho.op x.2.1 x.2.2,
        (conjugatedState_continuous_entry rho.op x.1.1 x.1.2).mul
          (conjugatedState_continuous_entry rho.op x.2.1 x.2.2)⟩
  let term :
      ((Fin (qubitDimension n) × Fin (qubitDimension n)) ×
        (Fin (qubitDimension n) × Fin (qubitDimension n))) →
        ContinuousMap (SpecialUnitary n) ℂ :=
    fun x =>
      ⟨fun U =>
          (O.op x.1.2 x.1.1 * O.op x.2.2 x.2.1) * base x U,
        continuous_const.mul (base x).continuous⟩
  let total : ContinuousMap (SpecialUnitary n) ℂ :=
    ⟨fun U => ∑ x, term x U,
      continuous_finset_sum _ fun x _ => (term x).continuous⟩
  have htotalPoint (U : SpecialUnitary n) :
      total U =
        (Matrix.trace (conjugatedState U rho.op * O.op)) ^ 2 := by
    change
      (∑ x :
          (Fin (qubitDimension n) × Fin (qubitDimension n)) ×
            (Fin (qubitDimension n) × Fin (qubitDimension n)),
        (O.op x.1.2 x.1.1 * O.op x.2.2 x.2.1) *
          (conjugatedState U rho.op x.1.1 x.1.2 *
            conjugatedState U rho.op x.2.1 x.2.2)) =
        (Matrix.trace (conjugatedState U rho.op * O.op)) ^ 2
    have htrace :
        (∑ x : Fin (qubitDimension n) × Fin (qubitDimension n),
          O.op x.2 x.1 * conjugatedState U rho.op x.1 x.2) =
            Matrix.trace (conjugatedState U rho.op * O.op) := by
      rw [Fintype.sum_prod_type]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    calc
      (∑ x :
          (Fin (qubitDimension n) × Fin (qubitDimension n)) ×
            (Fin (qubitDimension n) × Fin (qubitDimension n)),
        (O.op x.1.2 x.1.1 * O.op x.2.2 x.2.1) *
          (conjugatedState U rho.op x.1.1 x.1.2 *
            conjugatedState U rho.op x.2.1 x.2.2)) =
          ∑ a : Fin (qubitDimension n) × Fin (qubitDimension n),
            ∑ b : Fin (qubitDimension n) × Fin (qubitDimension n),
              (O.op a.2 a.1 *
                conjugatedState U rho.op a.1 a.2) *
              (O.op b.2 b.1 *
                conjugatedState U rho.op b.1 b.2) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ =
          (∑ a : Fin (qubitDimension n) × Fin (qubitDimension n),
            O.op a.2 a.1 * conjugatedState U rho.op a.1 a.2) *
          (∑ b : Fin (qubitDimension n) × Fin (qubitDimension n),
            O.op b.2 b.1 * conjugatedState U rho.op b.1 b.2) :=
        (Finset.sum_mul_sum Finset.univ Finset.univ _ _).symm
      _ = (Matrix.trace (conjugatedState U rho.op * O.op)) ^ 2 := by
        rw [htrace]
        ring
  have hbase (x :
      (Fin (qubitDimension n) × Fin (qubitDimension n)) ×
        (Fin (qubitDimension n) × Fin (qubitDimension n))) :
      haarComplexExpectation haar (base x) =
        haarTwoCopyStateExpectation haar rho.op
          (x.1.1, x.2.1) (x.1.2, x.2.2) := by
    rfl
  have hterm (x :
      (Fin (qubitDimension n) × Fin (qubitDimension n)) ×
        (Fin (qubitDimension n) × Fin (qubitDimension n))) :
      haarComplexExpectation haar (term x) =
        (O.op x.1.2 x.1.1 * O.op x.2.2 x.2.1) *
          haarTwoCopyStateExpectation haar rho.op
            (x.1.1, x.2.1) (x.1.2, x.2.2) := by
    change
      haarComplexExpectation haar
          ⟨fun U =>
            (O.op x.1.2 x.1.1 * O.op x.2.2 x.2.1) *
              base x U, _⟩ =
        (O.op x.1.2 x.1.1 * O.op x.2.2 x.2.1) *
          haarComplexExpectation haar (base x)
    exact haarComplexExpectation_mul haar
      (O.op x.1.2 x.1.1 * O.op x.2.2 x.2.1) (base x)
  have htotalExpectation :
      haarComplexExpectation haar total =
        ∑ x :
          (Fin (qubitDimension n) × Fin (qubitDimension n)) ×
            (Fin (qubitDimension n) × Fin (qubitDimension n)),
          (O.op x.1.2 x.1.1 * O.op x.2.2 x.2.1) *
            haarTwoCopyStateExpectation haar rho.op
              (x.1.1, x.2.1) (x.1.2, x.2.2) := by
    calc
      haarComplexExpectation haar total =
          ∑ x :
            (Fin (qubitDimension n) × Fin (qubitDimension n)) ×
              (Fin (qubitDimension n) × Fin (qubitDimension n)),
            haarComplexExpectation haar (term x) :=
        haarComplexExpectation_sum haar term
      _ = ∑ x :
            (Fin (qubitDimension n) × Fin (qubitDimension n)) ×
              (Fin (qubitDimension n) × Fin (qubitDimension n)),
            (O.op x.1.2 x.1.1 * O.op x.2.2 x.2.1) *
              haarTwoCopyStateExpectation haar rho.op
                (x.1.1, x.2.1) (x.1.2, x.2.2) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hterm x
  have hSecond :
      haarTwoCopyStateExpectation haar rho.op =
        haarSecondMomentNormalization n •
          ((1 : Matrix
              (Fin (qubitDimension n) × Fin (qubitDimension n))
              (Fin (qubitDimension n) × Fin (qubitDimension n)) ℂ) +
            tensorSwap n) := by
    rw [hrhoPure]
    exact hHaarSecondMoment
  have htotalValue :
      haarComplexExpectation haar total =
        haarSecondMomentNormalization n *
          Matrix.trace (O.op * O.op) := by
    rw [htotalExpectation]
    calc
      (∑ x :
          (Fin (qubitDimension n) × Fin (qubitDimension n)) ×
            (Fin (qubitDimension n) × Fin (qubitDimension n)),
        (O.op x.1.2 x.1.1 * O.op x.2.2 x.2.1) *
          haarTwoCopyStateExpectation haar rho.op
            (x.1.1, x.2.1) (x.1.2, x.2.2)) =
          ∑ x :
            (Fin (qubitDimension n) × Fin (qubitDimension n)) ×
              (Fin (qubitDimension n) × Fin (qubitDimension n)),
            (O.op x.1.2 x.1.1 * O.op x.2.2 x.2.1) *
              (haarSecondMomentNormalization n *
                ((1 : Matrix
                    (Fin (qubitDimension n) × Fin (qubitDimension n))
                    (Fin (qubitDimension n) × Fin (qubitDimension n)) ℂ) +
                  tensorSwap n)
                    (x.1.1, x.2.1) (x.1.2, x.2.2)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hSecond]
        rfl
      _ = haarSecondMomentNormalization n *
          (∑ x :
            (Fin (qubitDimension n) × Fin (qubitDimension n)) ×
              (Fin (qubitDimension n) × Fin (qubitDimension n)),
            (O.op x.1.2 x.1.1 * O.op x.2.2 x.2.1) *
              ((1 : Matrix
                  (Fin (qubitDimension n) × Fin (qubitDimension n))
                  (Fin (qubitDimension n) × Fin (qubitDimension n)) ℂ) +
                tensorSwap n)
                  (x.1.1, x.2.1) (x.1.2, x.2.2)) := by
        conv_rhs => rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = haarSecondMomentNormalization n *
          (Matrix.trace O.op * Matrix.trace O.op +
            Matrix.trace (O.op * O.op)) := by
        rw [identity_add_swap_contraction]
      _ = haarSecondMomentNormalization n *
          Matrix.trace (O.op * O.op) := by
        rw [O.traceless]
        ring
  have hvarianceExpectation :
      haarVariance haar (haarLossObservable rho.op O.op) =
        (haarComplexExpectation haar total).re := by
    let squareLoss : HaarObservable n :=
      ⟨fun U => (haarLoss U rho.op O.op) ^ 2,
        (haarLoss_continuous rho.op O.op).pow 2⟩
    have hcentered :
        centeredSquareHaarObservable haar
            (haarLossObservable rho.op O.op) =
          squareLoss := by
      ext U
      change
        (haarLoss U rho.op O.op -
          haar.expectation (haarLossObservable rho.op O.op)) ^ 2 =
            (haarLoss U rho.op O.op) ^ 2
      rw [hmean]
      simp
    unfold haarVariance
    rw [hcentered]
    calc
      haar.expectation squareLoss =
        haar.expectation
          ⟨fun U => (total U).re,
            Complex.continuous_re.comp total.continuous⟩ := by
              congr 1
              ext U
              change (haarLoss U rho.op O.op) ^ 2 = (total U).re
              rw [htotalPoint]
              have hz := Complex.conj_eq_iff_re.mp (htraceReal U)
              unfold haarLoss
              rw [← hz]
              norm_num [Complex.mul_re, pow_two]
      _ = (haarComplexExpectation haar total).re :=
        (haarComplexExpectation_re haar total).symm
  have hformula :
      haarVariance haar (haarLossObservable rho.op O.op) =
        (Matrix.trace (O.op * O.op)).re /
          ((qubitDimension n : ℝ) *
            ((qubitDimension n : ℝ) + 1)) := by
    rw [hvarianceExpectation, htotalValue]
    unfold haarSecondMomentNormalization
    have hden :
        (qubitDimension n : ℂ) * ((qubitDimension n : ℂ) + 1) =
          ((((qubitDimension n : ℝ) *
            ((qubitDimension n : ℝ) + 1)) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hden, ← Complex.ofReal_inv]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [div_eq_mul_inv]
    ring
  refine ⟨hformula, ?_⟩
  rw [hformula]
  have hNpos : 0 < (qubitDimension n : ℝ) := by positivity
  have hNpOnePos : 0 < (qubitDimension n : ℝ) + 1 := by positivity
  calc
    (Matrix.trace (O.op * O.op)).re /
          ((qubitDimension n : ℝ) *
            ((qubitDimension n : ℝ) + 1)) ≤
        (qubitDimension n : ℝ) /
          ((qubitDimension n : ℝ) *
            ((qubitDimension n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right O.squareTrace_le_dimension
        (mul_nonneg hNpos.le hNpOnePos.le)
    _ = 1 / ((qubitDimension n : ℝ) + 1) := by
      field_simp

/-- The resulting fluctuation is exponentially small in the qubit count:
the variance is at most `2^{-n}` and the root-mean-square fluctuation is at
most `2^{-n/2}`. -/
theorem haarLoss_exponential_fluctuation
    {n : ℕ} (haar : HaarExpectation n)
    (rho : DensityOperator n) (psi : PureState (Qubits n))
    (hrhoPure : rho.op = pureProjector psi)
    (O : BoundedTracelessObservable n)
    (hHaarSecondMoment :
      haarTwoCopyStateExpectation haar (pureProjector psi) =
        haarSecondMomentNormalization n •
          ((1 : Matrix
              (Fin (qubitDimension n) × Fin (qubitDimension n))
              (Fin (qubitDimension n) × Fin (qubitDimension n)) ℂ) +
            tensorSwap n)) :
    haarVariance haar (haarLossObservable rho.op O.op) ≤
        Real.rpow 2 (-(n : ℝ)) ∧
      haarRMSFluctuation haar (haarLossObservable rho.op O.op) ≤
        Real.rpow 2 (-(n : ℝ) / 2) := by
  have hvariance :=
    (haarLoss_variance haar rho psi hrhoPure O hHaarSecondMoment).2
  have hdimensionPos : 0 < (qubitDimension n : ℝ) := by positivity
  have hinverseDimension :
      1 / (qubitDimension n : ℝ) = Real.rpow 2 (-(n : ℝ)) := by
    symm
    calc
      Real.rpow 2 (-(n : ℝ)) =
          (Real.rpow 2 (n : ℝ))⁻¹ :=
        Real.rpow_neg (by norm_num) (n : ℝ)
      _ = ((2 : ℝ) ^ n)⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast 2 n)
      _ = 1 / (qubitDimension n : ℝ) := by
        norm_num [qubitDimension]
  have hvarianceExponential :
      haarVariance haar (haarLossObservable rho.op O.op) ≤
        Real.rpow 2 (-(n : ℝ)) := by
    calc
      haarVariance haar (haarLossObservable rho.op O.op) ≤
          1 / ((qubitDimension n : ℝ) + 1) :=
        hvariance
      _ ≤ 1 / (qubitDimension n : ℝ) := by
        apply one_div_le_one_div_of_le hdimensionPos
        linarith
      _ = Real.rpow 2 (-(n : ℝ)) := hinverseDimension
  refine ⟨hvarianceExponential, ?_⟩
  unfold haarRMSFluctuation
  calc
    Real.sqrt (haarVariance haar (haarLossObservable rho.op O.op)) ≤
        Real.sqrt (Real.rpow 2 (-(n : ℝ))) :=
      Real.sqrt_le_sqrt hvarianceExponential
    _ = Real.rpow 2 (-(n : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      calc
        Real.rpow (Real.rpow 2 (-(n : ℝ))) (1 / 2) =
            Real.rpow 2 ((-(n : ℝ)) * (1 / 2)) :=
          (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
            (-(n : ℝ)) (1 / 2)).symm
        _ = Real.rpow 2 (-(n : ℝ) / 2) := by
          congr 1
          ring

end

end ApproximateTwoDesignDepthHaarLossFluctuations
end QAlgFormalized
