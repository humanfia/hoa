import QITFoundations.QITFormalized_problem_qit_OneShotEntropiesAndHypothesisTesting_ConverseEntanglementConcentration_Foundation

/-!
# Converse for entanglement concentration

This file states the asymptotic converse for converting tensor powers of a
finite-dimensional bipartite pure state into maximally entangled states by
finite-round LOCC protocols.
-/

open scoped BigOperators ComplexOrder MatrixOrder Topology
open Filter

namespace QITFormalized.OneShotEntropiesAndHypothesisTesting.ConverseEntanglementConcentration

open QITBench QITBench.OneShot

noncomputable section

universe u v

/-! ## Project-local Mathlib supplement — spectral AEP and asymptotic reduction -/

/-- The eigenvalues of a finite-dimensional density state form the probability
distribution needed by a classical information-spectrum argument. -/
theorem stateEigenvalues_isProbabilityDistribution
    {X : Type u} [Fintype X] [DecidableEq X] (ρ : State X) :
    IsProbabilityDistribution
      (fun i => ρ.pos.isHermitian.eigenvalues i) := by
  constructor
  · intro i
    exact ρ.pos.eigenvalues_nonneg i
  · have h := ρ.pos.isHermitian.trace_eq_sum_eigenvalues
    rw [ρ.trace_eq_one] at h
    apply Complex.ofReal_injective
    simpa using h.symm

/-- The project entropy is exactly the Shannon entropy of the reduced-state
eigenvalue distribution. -/
theorem entanglementEntropy_eq_schmidtEntropy_eigenvalues
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) :
    entanglementEntropy ψ =
      schmidtEntropy
        (fun i => ψ.state.marginalA.pos.isHermitian.eigenvalues i) := by
  rfl

/-- Every positive binary exponent gives a geometrically decaying sequence
along the natural numbers. -/
lemma binaryExponentialDecay_tendsto_zero (δ : ℝ) (hδ : 0 < δ) :
    Tendsto
      (fun n : ℕ => Real.rpow 2 (-((n : ℝ) * δ)))
      atTop (𝓝 0) := by
  let a : ℝ := (2 : ℝ) ^ (-δ)
  have ha0 : 0 ≤ a :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have ha1 : a < 1 := by
    dsimp [a]
    exact
      (Real.rpow_lt_one_iff_of_pos
        (by norm_num : (0 : ℝ) < 2)).2
        (Or.inl ⟨by norm_num, neg_lt_zero.mpr hδ⟩)
  have hpow :
      Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1
  convert hpow using 1
  funext n
  dsimp [a]
  change
    (2 : ℝ) ^ (-((n : ℝ) * δ)) =
      ((2 : ℝ) ^ (-δ)) ^ n
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- A vanishing one-shot fidelity upper bound at every forbidden rate is
enough for the asymptotic converse. -/
theorem asymptoticRateAtMost_of_eventual_fidelity_vanishes
    (entropy : ℝ)
    (M : ℕ → ℕ)
    (fidelity : ℕ → ℝ)
    (hfidelity : Tendsto fidelity atTop (𝓝 1))
    (hvanish : ∀ R : ℝ,
      entropy < R →
        ∃ bound : ℕ → ℝ,
          Tendsto bound atTop (𝓝 0) ∧
            ∀ᶠ n in atTop,
              concentrationRate M n > R →
                fidelity n ≤ bound n) :
    AsymptoticRateAtMost entropy M := by
  apply asymptoticRateAtMost_of_eventual_fidelity_gap
    entropy M fidelity hfidelity
  intro R hR
  obtain ⟨bound, hbound, hcontrol⟩ := hvanish R hR
  refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
  have hboundHalf :
      ∀ᶠ n in atTop, bound n ≤ (1 : ℝ) / 2 :=
    hbound.eventually (Iic_mem_nhds (by norm_num))
  filter_upwards [hcontrol, hboundHalf] with n hn hnhalf
  intro hnR
  exact (hn hnR).trans hnhalf

/-- An eventual exponentially decaying fidelity estimate at each forbidden
rate is a convenient sufficient form of the one-shot converse. -/
theorem asymptoticRateAtMost_of_eventual_exponential_fidelity_bound
    (entropy : ℝ)
    (M : ℕ → ℕ)
    (fidelity : ℕ → ℝ)
    (hfidelity : Tendsto fidelity atTop (𝓝 1))
    (hexponential : ∀ R : ℝ,
      entropy < R →
        ∃ C δ : ℝ, 0 < δ ∧
          ∀ᶠ n in atTop,
            concentrationRate M n > R →
              fidelity n ≤
                C * Real.rpow 2 (-((n : ℝ) * δ))) :
    AsymptoticRateAtMost entropy M := by
  apply asymptoticRateAtMost_of_eventual_fidelity_vanishes
    entropy M fidelity hfidelity
  intro R hR
  obtain ⟨C, δ, hδ, hcontrol⟩ := hexponential R hR
  refine
    ⟨fun n => C * Real.rpow 2 (-((n : ℝ) * δ)), ?_, hcontrol⟩
  simpa using
    tendsto_const_nhds.mul
      (binaryExponentialDecay_tendsto_zero δ hδ)

/-! ### A finite-spectrum upper-tail AEP -/

/-- The product weight of an IID string over a finite spectral probability
distribution. -/
noncomputable def iidSpectrumWeight
    {X : Type u} (p : X → ℝ) :
    (n : ℕ) → TensorPower X n → ℝ
  | 0, _ => 1
  | n + 1, xs =>
      p xs.1 * iidSpectrumWeight p n xs.2

/-- The base-two self-information of one spectral outcome. -/
noncomputable def schmidtSelfInformation
    {X : Type u} (p : X → ℝ) (x : X) : ℝ :=
  -log2 (p x)

/-- The additive self-information of an IID spectral string. -/
noncomputable def iidSchmidtSelfInformation
    {X : Type u} (p : X → ℝ) :
    (n : ℕ) → TensorPower X n → ℝ
  | 0, _ => 0
  | n + 1, xs =>
      schmidtSelfInformation p xs.1 +
        iidSchmidtSelfInformation p n xs.2

/-- The total IID probability of strings whose self-information exceeds the
threshold `n T`. -/
noncomputable def iidHighInformationMass
    {X : Type u} [Fintype X]
    (p : X → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  ∑ xs : TensorPower X n,
    if (n : ℝ) * T < iidSchmidtSelfInformation p n xs
    then iidSpectrumWeight p n xs
    else 0

/-- IID spectral weights are nonnegative when the one-letter spectrum is a
probability distribution. -/
lemma iidSpectrumWeight_nonneg
    {X : Type u} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    ∀ (n : ℕ) (xs : TensorPower X n),
      0 ≤ iidSpectrumWeight p n xs := by
  intro n
  induction n with
  | zero =>
      intro xs
      simp [iidSpectrumWeight]
  | succ n ih =>
      intro xs
      exact mul_nonneg (hp.1 xs.1) (ih xs.2)

/-- IID spectral weights retain total mass one at every blocklength. -/
lemma iidSpectrumWeight_sum
    {X : Type u} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    ∀ n : ℕ,
      ∑ xs : TensorPower X n, iidSpectrumWeight p n xs = 1 := by
  intro n
  induction n with
  | zero =>
      simp [TensorPower, iidSpectrumWeight]
  | succ n ih =>
      change
        (∑ xs : X × TensorPower X n,
          iidSpectrumWeight p (n + 1) xs) = 1
      rw [Fintype.sum_prod_type]
      change
        (∑ x : X, ∑ xs : TensorPower X n,
          p x * iidSpectrumWeight p n xs) = 1
      calc
        _ = (∑ x : X, p x) *
            (∑ xs : TensorPower X n,
              iidSpectrumWeight p n xs) := by
          rw [Finset.sum_mul_sum]
        _ = 1 := by rw [hp.2, ih, one_mul]

/-- The one-letter variance of spectral self-information around its Shannon
entropy. -/
noncomputable def schmidtInformationVariance
    {X : Type u} [Fintype X] (p : X → ℝ) : ℝ :=
  ∑ x,
    p x * (schmidtSelfInformation p x - schmidtEntropy p) ^ 2

private noncomputable def centeredSchmidtSelfInformation
    {X : Type u} [Fintype X] (p : X → ℝ) (x : X) : ℝ :=
  schmidtSelfInformation p x - schmidtEntropy p

private noncomputable def iidCenteredSchmidtSelfInformation
    {X : Type u} [Fintype X] (p : X → ℝ) :
    (n : ℕ) → TensorPower X n → ℝ
  | 0, _ => 0
  | n + 1, xs =>
      centeredSchmidtSelfInformation p xs.1 +
        iidCenteredSchmidtSelfInformation p n xs.2

private theorem schmidtSelfInformation_mean
    {X : Type u} [Fintype X] (p : X → ℝ) :
    ∑ x, p x * schmidtSelfInformation p x =
      schmidtEntropy p := by
  simp only [schmidtSelfInformation, schmidtEntropy]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

private theorem centeredSchmidtSelfInformation_mean_zero
    {X : Type u} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    ∑ x, p x * centeredSchmidtSelfInformation p x = 0 := by
  calc
    ∑ x, p x * centeredSchmidtSelfInformation p x =
        (∑ x, p x * schmidtSelfInformation p x) -
          schmidtEntropy p * ∑ x, p x := by
            simp only [centeredSchmidtSelfInformation, mul_sub,
              Finset.sum_sub_distrib]
            apply congrArg₂ (· - ·) rfl
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = 0 := by
      rw [schmidtSelfInformation_mean, hp.2]
      ring

private theorem schmidtInformationVariance_nonneg
    {X : Type u} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    0 ≤ schmidtInformationVariance p := by
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (hp.1 x) (sq_nonneg _)

private theorem iidCenteredSchmidtSelfInformation_mean_zero
    {X : Type u} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    ∀ n : ℕ,
      ∑ xs : TensorPower X n,
          iidSpectrumWeight p n xs *
            iidCenteredSchmidtSelfInformation p n xs = 0 := by
  intro n
  induction n with
  | zero =>
      simp [TensorPower, iidSpectrumWeight,
        iidCenteredSchmidtSelfInformation]
  | succ n ih =>
      change
        (∑ pair : X × TensorPower X n,
          iidSpectrumWeight p (n + 1) pair *
            iidCenteredSchmidtSelfInformation p (n + 1) pair) = 0
      rw [Fintype.sum_prod_type]
      change
        (∑ x : X, ∑ xs : TensorPower X n,
          (p x * iidSpectrumWeight p n xs) *
            (centeredSchmidtSelfInformation p x +
              iidCenteredSchmidtSelfInformation p n xs)) = 0
      calc
        _ =
            (∑ x : X,
                p x * centeredSchmidtSelfInformation p x) *
                (∑ xs : TensorPower X n,
                  iidSpectrumWeight p n xs) +
              (∑ x : X, p x) *
                (∑ xs : TensorPower X n,
                  iidSpectrumWeight p n xs *
                    iidCenteredSchmidtSelfInformation p n xs) := by
              rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x hx
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro xs hxs
              ring
        _ = 0 := by
          rw [centeredSchmidtSelfInformation_mean_zero p hp,
            iidSpectrumWeight_sum p hp n, hp.2, ih]
          ring

set_option maxHeartbeats 800000 in
private theorem iidCenteredSchmidtSelfInformation_secondMoment
    {X : Type u} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    ∀ n : ℕ,
      ∑ xs : TensorPower X n,
          iidSpectrumWeight p n xs *
            (iidCenteredSchmidtSelfInformation p n xs) ^ 2 =
        (n : ℝ) * schmidtInformationVariance p := by
  intro n
  induction n with
  | zero =>
      simp [TensorPower, iidSpectrumWeight,
        iidCenteredSchmidtSelfInformation]
  | succ n ih =>
      change
        (∑ pair : X × TensorPower X n,
          iidSpectrumWeight p (n + 1) pair *
            (iidCenteredSchmidtSelfInformation p (n + 1) pair) ^ 2) =
          ((n + 1 : ℕ) : ℝ) * schmidtInformationVariance p
      rw [Fintype.sum_prod_type]
      change
        (∑ x : X, ∑ xs : TensorPower X n,
          (p x * iidSpectrumWeight p n xs) *
            (centeredSchmidtSelfInformation p x +
              iidCenteredSchmidtSelfInformation p n xs) ^ 2) =
          ((n + 1 : ℕ) : ℝ) * schmidtInformationVariance p
      calc
        _ =
            (∑ x : X,
                p x * (centeredSchmidtSelfInformation p x) ^ 2) *
                (∑ xs : TensorPower X n,
                  iidSpectrumWeight p n xs) +
              2 *
                ((∑ x : X,
                    p x * centeredSchmidtSelfInformation p x) *
                  (∑ xs : TensorPower X n,
                    iidSpectrumWeight p n xs *
                      iidCenteredSchmidtSelfInformation p n xs)) +
              (∑ x : X, p x) *
                (∑ xs : TensorPower X n,
                  iidSpectrumWeight p n xs *
                    (iidCenteredSchmidtSelfInformation p n xs) ^ 2) := by
              rw [Finset.sum_mul_sum, Finset.sum_mul_sum,
                Finset.sum_mul_sum]
              simp only [Finset.mul_sum]
              rw [← Finset.sum_add_distrib,
                ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x hx
              rw [← Finset.sum_add_distrib,
                ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro xs hxs
              ring
        _ = ((n + 1 : ℕ) : ℝ) *
              schmidtInformationVariance p := by
          rw [show
              (∑ x : X,
                  p x *
                    (centeredSchmidtSelfInformation p x) ^ 2) =
                schmidtInformationVariance p by
                  rfl,
            iidSpectrumWeight_sum p hp n,
            centeredSchmidtSelfInformation_mean_zero p hp,
            iidCenteredSchmidtSelfInformation_mean_zero p hp n,
            hp.2, ih]
          push_cast
          ring

private theorem iidCenteredSchmidtSelfInformation_eq_sub
    {X : Type u} [Fintype X] (p : X → ℝ) :
    ∀ (n : ℕ) (xs : TensorPower X n),
      iidCenteredSchmidtSelfInformation p n xs =
        iidSchmidtSelfInformation p n xs -
          (n : ℝ) * schmidtEntropy p := by
  intro n
  induction n with
  | zero =>
      intro xs
      simp [iidCenteredSchmidtSelfInformation,
        iidSchmidtSelfInformation]
  | succ n ih =>
      intro xs
      simp only [iidCenteredSchmidtSelfInformation,
        iidSchmidtSelfInformation]
      rw [ih]
      simp only [centeredSchmidtSelfInformation]
      push_cast
      ring

private theorem iidHighInformationMass_nonneg
    {X : Type u} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (n : ℕ) :
    0 ≤ iidHighInformationMass p T n := by
  apply Finset.sum_nonneg
  intro xs hxs
  split
  · exact iidSpectrumWeight_nonneg p hp n xs
  · exact le_rfl

set_option maxHeartbeats 800000 in
private theorem iidHighInformationMass_mul_gap_sq_le
    {X : Type u} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (hT : schmidtEntropy p < T)
    (n : ℕ) :
    iidHighInformationMass p T n *
          ((n : ℝ) * (T - schmidtEntropy p)) ^ 2 ≤
      (n : ℝ) * schmidtInformationVariance p := by
  rw [← iidCenteredSchmidtSelfInformation_secondMoment p hp n]
  unfold iidHighInformationMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro xs hxs
  split
  · rename_i hhigh
    have hcenter :=
      iidCenteredSchmidtSelfInformation_eq_sub p n xs
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hgap : 0 < T - schmidtEntropy p := sub_pos.mpr hT
    have hsquares :
        ((n : ℝ) * (T - schmidtEntropy p)) ^ 2 ≤
          (iidCenteredSchmidtSelfInformation p n xs) ^ 2 := by
      rw [hcenter]
      nlinarith [mul_nonneg hn hgap.le]
    exact
      mul_le_mul_of_nonneg_left hsquares
        (iidSpectrumWeight_nonneg p hp n xs)
  · simpa using
      mul_nonneg
        (iidSpectrumWeight_nonneg p hp n xs) (sq_nonneg _)

/-- Chebyshev's inequality gives an explicit `O(1/n)` upper bound on the
high-self-information spectral tail. -/
theorem iidHighInformationMass_le_variance_bound
    {X : Type u} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (hT : schmidtEntropy p < T)
    (n : ℕ) (hn : 0 < n) :
    iidHighInformationMass p T n ≤
      schmidtInformationVariance p /
        ((n : ℝ) * (T - schmidtEntropy p) ^ 2) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hgap : 0 < T - schmidtEntropy p := sub_pos.mpr hT
  have hbase :=
    iidHighInformationMass_mul_gap_sq_le p hp T hT n
  have hcancel :
      iidHighInformationMass p T n *
          ((n : ℝ) * (T - schmidtEntropy p) ^ 2) ≤
        schmidtInformationVariance p := by
    apply le_of_mul_le_mul_left _ hnR
    calc
      (n : ℝ) *
            (iidHighInformationMass p T n *
              ((n : ℝ) * (T - schmidtEntropy p) ^ 2)) =
          iidHighInformationMass p T n *
            ((n : ℝ) * (T - schmidtEntropy p)) ^ 2 := by
              ring
      _ ≤ (n : ℝ) * schmidtInformationVariance p := hbase
  exact
    (le_div_iff₀ (mul_pos hnR (sq_pos_of_pos hgap))).2 hcancel

/-- The upper information-spectrum tail of a finite IID probability
distribution vanishes above its Shannon entropy. -/
theorem iidHighInformationMass_tendsto_zero
    {X : Type u} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (hT : schmidtEntropy p < T) :
    Tendsto (iidHighInformationMass p T) atTop (𝓝 0) := by
  let C : ℝ :=
    schmidtInformationVariance p /
      (T - schmidtEntropy p) ^ 2
  have hbound :
      Tendsto (fun n : ℕ => C * ((n : ℝ)⁻¹))
        atTop (𝓝 0) := by
    simpa using
      tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop (R := ℝ)))
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall
      (iidHighInformationMass_nonneg p hp T)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := by omega
    calc
      iidHighInformationMass p T n ≤
          schmidtInformationVariance p /
            ((n : ℝ) * (T - schmidtEntropy p) ^ 2) :=
        iidHighInformationMass_le_variance_bound
          p hp T hT n hnpos
      _ = C * ((n : ℝ)⁻¹) := by
        dsimp [C]
        field_simp
  · exact hbound

/-- The high-information tail of the reduced-state IID spectrum vanishes above
the input entanglement entropy. -/
theorem entanglementSpectrum_highInformationMass_tendsto_zero
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B))
    (T : ℝ) (hT : entanglementEntropy ψ < T) :
    Tendsto
      (iidHighInformationMass
        (fun i =>
          ψ.state.marginalA.pos.isHermitian.eigenvalues i)
        T)
      atTop (𝓝 0) := by
  apply iidHighInformationMass_tendsto_zero
    (fun i => ψ.state.marginalA.pos.isHermitian.eigenvalues i)
    (stateEigenvalues_isProbabilityDistribution
      ψ.state.marginalA)
    T
  rwa [← entanglementEntropy_eq_schmidtEntropy_eigenvalues ψ]

private theorem rpow_log2_of_pos
    (x : ℝ) (hx : 0 < x) :
    Real.rpow 2 (log2 x) = x := by
  change (2 : ℝ) ^ (log2 x) = x
  rw [Real.rpow_def_of_pos (by norm_num)]
  unfold log2
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [show
      Real.log 2 * (Real.log x / Real.log 2) =
        Real.log x by
          field_simp]
  exact Real.exp_log hx

private theorem rpow_neg_schmidtSelfInformation
    {X : Type u} (p : X → ℝ) (x : X)
    (hx : 0 < p x) :
    Real.rpow 2 (-schmidtSelfInformation p x) = p x := by
  simp only [schmidtSelfInformation, neg_neg]
  exact rpow_log2_of_pos (p x) hx

/-- A positive IID spectral weight is exactly two to the negative additive
self-information. -/
theorem rpow_neg_iidSchmidtSelfInformation_eq_iidSpectrumWeight
    {X : Type u} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    ∀ (n : ℕ) (xs : TensorPower X n),
      0 < iidSpectrumWeight p n xs →
        Real.rpow 2 (-iidSchmidtSelfInformation p n xs) =
          iidSpectrumWeight p n xs := by
  intro n
  induction n with
  | zero =>
      intro xs hxs
      simp [iidSchmidtSelfInformation, iidSpectrumWeight]
  | succ n ih =>
      intro xs hxs
      have hhead0 : 0 ≤ p xs.1 := hp.1 xs.1
      have htail0 : 0 ≤ iidSpectrumWeight p n xs.2 :=
        iidSpectrumWeight_nonneg p hp n xs.2
      have hprod :
          0 < p xs.1 * iidSpectrumWeight p n xs.2 := hxs
      have hboth :
          0 < p xs.1 ∧ 0 < iidSpectrumWeight p n xs.2 := by
        rcases mul_pos_iff.mp hprod with h | h
        · exact h
        · exact (not_lt_of_ge hhead0 h.1).elim
      change
        (2 : ℝ) ^
            (-(schmidtSelfInformation p xs.1 +
              iidSchmidtSelfInformation p n xs.2)) =
          p xs.1 * iidSpectrumWeight p n xs.2
      rw [neg_add, Real.rpow_add (by norm_num)]
      have hheadEq :
          (2 : ℝ) ^ (-schmidtSelfInformation p xs.1) =
            p xs.1 :=
        rpow_neg_schmidtSelfInformation p xs.1 hboth.1
      have htailEq :
          (2 : ℝ) ^ (-iidSchmidtSelfInformation p n xs.2) =
            iidSpectrumWeight p n xs.2 :=
        ih xs.2 hboth.2
      rw [hheadEq, htailEq]

/-- Positive low-self-information IID strings, the finite spectral subspace
used in the strong-converse truncation. -/
noncomputable def iidLowInformationSupport
    {X : Type u} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (T : ℝ) (n : ℕ) :
    Finset (TensorPower X n) :=
  Finset.univ.filter fun xs =>
    0 < iidSpectrumWeight p n xs ∧
      iidSchmidtSelfInformation p n xs ≤ (n : ℝ) * T

/-- Each string in the low-information support has weight at least the
threshold `2⁻ⁿᵀ`. -/
theorem rpow_neg_threshold_le_iidSpectrumWeight_of_mem_lowInformationSupport
    {X : Type u} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (n : ℕ) (xs : TensorPower X n)
    (hxs : xs ∈ iidLowInformationSupport p T n) :
    Real.rpow 2 (-((n : ℝ) * T)) ≤
      iidSpectrumWeight p n xs := by
  have hmem :
      0 < iidSpectrumWeight p n xs ∧
        iidSchmidtSelfInformation p n xs ≤ (n : ℝ) * T := by
    simpa [iidLowInformationSupport] using hxs
  rw [← rpow_neg_iidSchmidtSelfInformation_eq_iidSpectrumWeight
    p hp n xs hmem.1]
  exact
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (neg_le_neg hmem.2)

/-- The dimension of the positive low-information spectral support, multiplied
by its minimum spectral weight, is at most one. -/
theorem iidLowInformationSupport_card_mul_rpow_neg_threshold_le_one
    {X : Type u} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (n : ℕ) :
    ((iidLowInformationSupport p T n).card : ℝ) *
        Real.rpow 2 (-((n : ℝ) * T)) ≤ 1 := by
  rw [← iidSpectrumWeight_sum p hp n]
  calc
    ((iidLowInformationSupport p T n).card : ℝ) *
          Real.rpow 2 (-((n : ℝ) * T)) =
        ∑ xs ∈ iidLowInformationSupport p T n,
          Real.rpow 2 (-((n : ℝ) * T)) := by
            simp
    _ ≤ ∑ xs ∈ iidLowInformationSupport p T n,
          iidSpectrumWeight p n xs := by
            apply Finset.sum_le_sum
            intro xs hxs
            exact
              rpow_neg_threshold_le_iidSpectrumWeight_of_mem_lowInformationSupport
                p hp T n xs hxs
    _ ≤ ∑ xs ∈ (Finset.univ : Finset (TensorPower X n)),
          iidSpectrumWeight p n xs := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ _)
            intro xs hxs hxsSupport
            exact iidSpectrumWeight_nonneg p hp n xs

/-- The positive low-information support has dimension at most `2ⁿᵀ`. -/
theorem iidLowInformationSupport_card_le_rpow
    {X : Type u} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (n : ℕ) :
    ((iidLowInformationSupport p T n).card : ℝ) ≤
      Real.rpow 2 ((n : ℝ) * T) := by
  have hcard :=
    iidLowInformationSupport_card_mul_rpow_neg_threshold_le_one
      p hp T n
  have hbpos :
      0 < Real.rpow 2 (-((n : ℝ) * T)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  calc
    ((iidLowInformationSupport p T n).card : ℝ) ≤
        1 / Real.rpow 2 (-((n : ℝ) * T)) :=
      (le_div_iff₀ hbpos).2 hcard
    _ = Real.rpow 2 ((n : ℝ) * T) := by
      have hneg :
          Real.rpow 2 (-((n : ℝ) * T)) =
            (Real.rpow 2 ((n : ℝ) * T))⁻¹ := by
        exact Real.rpow_neg (by norm_num) _
      rw [hneg, one_div, inv_inv]

/-- A realized concentration rate above `R` forces the integer target rank
strictly above `2ⁿᴿ` at every positive blocklength. -/
theorem rpow_lt_targetRank_of_concentrationRate_gt
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n)
    (R : ℝ) (n : ℕ) (hn : 0 < n)
    (hR : concentrationRate M n > R) :
    Real.rpow 2 ((n : ℝ) * R) < (M n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hMpos : (0 : ℝ) < (M n : ℝ) := by
    exact_mod_cast hM n
  have hlog : (n : ℝ) * R < log2 (M n) := by
    unfold concentrationRate at hR
    rw [show
      (1 / (n : ℝ)) = ((n : ℝ))⁻¹ by
        exact one_div _] at hR
    exact (lt_inv_mul_iff₀ hnR).mp hR
  calc
    Real.rpow 2 ((n : ℝ) * R) <
        Real.rpow 2 (log2 (M n)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlog
    _ = (M n : ℝ) :=
      rpow_log2_of_pos _ hMpos

/-- Above a forbidden rate `R > T`, the ratio of the low-information spectral
support dimension to target rank is exponentially small. -/
theorem iidLowInformationSupport_card_div_target_lt_exponential
    {X : Type u} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n)
    (R T : ℝ) (n : ℕ) (hn : 0 < n)
    (hR : concentrationRate M n > R) :
    ((iidLowInformationSupport p T n).card : ℝ) / (M n : ℝ) <
      Real.rpow 2 (-((n : ℝ) * (R - T))) := by
  have hMpos : (0 : ℝ) < (M n : ℝ) := by
    exact_mod_cast hM n
  have hExpRM :=
    rpow_lt_targetRank_of_concentrationRate_gt M hM R n hn hR
  have hExpT :
      0 < Real.rpow 2 ((n : ℝ) * T) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hExpR :
      0 < Real.rpow 2 ((n : ℝ) * R) :=
    Real.rpow_pos_of_pos (by norm_num) _
  calc
    ((iidLowInformationSupport p T n).card : ℝ) / (M n : ℝ) ≤
        Real.rpow 2 ((n : ℝ) * T) / (M n : ℝ) :=
      div_le_div_of_nonneg_right
        (iidLowInformationSupport_card_le_rpow p hp T n)
        hMpos.le
    _ < Real.rpow 2 ((n : ℝ) * T) /
          Real.rpow 2 ((n : ℝ) * R) :=
      (div_lt_div_iff_of_pos_left hExpT hMpos hExpR).2 hExpRM
    _ = Real.rpow 2 (-((n : ℝ) * (R - T))) := by
      calc
        Real.rpow 2 ((n : ℝ) * T) /
              Real.rpow 2 ((n : ℝ) * R) =
            Real.rpow 2
              ((n : ℝ) * T - (n : ℝ) * R) :=
          (Real.rpow_sub
            (by norm_num : (0 : ℝ) < 2) _ _).symm
        _ = Real.rpow 2 (-((n : ℝ) * (R - T))) := by
          congr 1
          ring

/-- The explicit scalar error envelope obtained by truncating an IID spectrum
at threshold `T` while comparing it with a target rate `R`. -/
noncomputable def iidSpectralConverseEnvelope
    {X : Type u} [Fintype X]
    (p : X → ℝ) (R T : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (iidHighInformationMass p T n) +
    Real.sqrt (Real.rpow 2 (-((n : ℝ) * (R - T))))

/-- The spectral truncation envelope vanishes whenever the threshold lies
strictly between Shannon entropy and the forbidden target rate. -/
theorem iidSpectralConverseEnvelope_tendsto_zero
    {X : Type u} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (R T : ℝ)
    (hEntropyT : schmidtEntropy p < T)
    (hTR : T < R) :
    Tendsto (iidSpectralConverseEnvelope p R T)
      atTop (𝓝 0) := by
  have htail :=
    iidHighInformationMass_tendsto_zero p hp T hEntropyT
  have hsqrtTail :
      Tendsto
        (fun n => Real.sqrt (iidHighInformationMass p T n))
        atTop (𝓝 0) := by
    simpa using
      Real.continuous_sqrt.continuousAt.tendsto.comp htail
  have hexponential :=
    binaryExponentialDecay_tendsto_zero (R - T)
      (sub_pos.mpr hTR)
  have hsqrtExponential :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt
            (Real.rpow 2 (-((n : ℝ) * (R - T)))))
        atTop (𝓝 0) := by
    simpa using
      Real.continuous_sqrt.continuousAt.tendsto.comp hexponential
  simpa [iidSpectralConverseEnvelope] using
    hsqrtTail.add hsqrtExponential

/-- Once fidelity is bounded by the explicit IID spectral truncation envelope,
the upper-tail AEP supplies the full asymptotic rate converse. -/
theorem asymptoticRateAtMost_of_eventual_iidSpectralConverseEnvelope
    {X : Type u} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (entropy : ℝ)
    (hEntropy : entropy = schmidtEntropy p)
    (M : ℕ → ℕ)
    (fidelity : ℕ → ℝ)
    (hfidelity : Tendsto fidelity atTop (𝓝 1))
    (honeShot : ∀ R : ℝ,
      entropy < R →
        ∀ᶠ n in atTop,
          concentrationRate M n > R →
            fidelity n ≤
              iidSpectralConverseEnvelope
                p R ((entropy + R) / 2) n) :
    AsymptoticRateAtMost entropy M := by
  apply asymptoticRateAtMost_of_eventual_fidelity_vanishes
    entropy M fidelity hfidelity
  intro R hR
  let T : ℝ := (entropy + R) / 2
  have hEntropyT : schmidtEntropy p < T := by
    rw [← hEntropy]
    dsimp [T]
    linarith
  have hTR : T < R := by
    dsimp [T]
    linarith
  refine
    ⟨iidSpectralConverseEnvelope p R T,
      iidSpectralConverseEnvelope_tendsto_zero
      p hp R T hEntropyT hTR, ?_⟩
  simpa [T] using honeShot R hR

/-! ### Pure maximally-entangled target infrastructure -/

/-- The canonical maximally-entangled density matrix has trace one whenever
its Schmidt rank is positive. -/
theorem maximallyEntangledDensity_trace_eq_one
    (M : ℕ) (hM : 0 < M) :
    (maximallyEntangledDensity M).trace = 1 := by
  rw [maximallyEntangledDensity, rankOneMatrix_trace]
  simp only [dotProduct, maximallyEntangledVector]
  rw [Fintype.sum_prod_type]
  simp
  have hsqrt : Real.sqrt (M : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hM))
  field_simp
  norm_cast
  exact (Real.sq_sqrt (Nat.cast_nonneg M)).symm

/-- The canonical rank-`M` maximally-entangled vector, bundled as a normalized
`PureVector` for positive `M`. -/
noncomputable def maximallyEntangledPureVector
    (M : ℕ) (hM : 0 < M) :
    PureVector (Fin M × Fin M) where
  amp := maximallyEntangledVector M
  trace_rankOne_eq_one := by
    simpa [maximallyEntangledDensity] using
      maximallyEntangledDensity_trace_eq_one M hM

/-- The state of the bundled maximally-entangled pure vector is the canonical
maximally-entangled density matrix used by the theorem statement. -/
@[simp]
theorem maximallyEntangledPureVector_state_matrix
    (M : ℕ) (hM : 0 < M) :
    (maximallyEntangledPureVector M hM).state.matrix =
      maximallyEntangledDensity M := by
  rfl

/-- Matrix functional calculus fixes every normalized rank-one density
projection under square root. -/
theorem matrixSqrt_pureVector_state_matrix
    {X : Type u} [Fintype X] [DecidableEq X]
    (φ : PureVector X) :
    matrixSqrt φ.state.matrix = φ.state.matrix := by
  unfold matrixSqrt
  exact
    CFC.sqrt_unique φ.state_matrix_mul_self φ.state.pos.nonneg

/-- The recursively factored amplitude of an arbitrary bipartite pure-state
tensor power in the `Aⁿ × Bⁿ` coordinates used by `State.tensorPowerBipartite`. -/
noncomputable def tensorPowerBipartiteAmplitude
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (φ : PureVector (A × B)) :
    (n : ℕ) → TensorPower A n → TensorPower B n → ℂ
  | 0, _, _ => 1
  | n + 1, as, bs =>
      φ.amp (as.1, bs.1) *
        tensorPowerBipartiteAmplitude φ n as.2 bs.2

private theorem tensorPowerBipartite_matrix_apply
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (φ : PureVector (A × B)) :
    ∀ (n : ℕ)
      (i j : TensorPower A n × TensorPower B n),
      (φ.state.tensorPowerBipartite n).matrix i j =
        tensorPowerBipartiteAmplitude φ n i.1 i.2 *
          star (tensorPowerBipartiteAmplitude φ n j.1 j.2) := by
  intro n
  induction n with
  | zero =>
      intro i j
      rcases i with ⟨ia, ib⟩
      rcases j with ⟨ja, jb⟩
      cases ia
      cases ib
      cases ja
      cases jb
      simp [State.tensorPowerBipartite, State.tensorPower,
        tensorPowerProdEquiv, State.reindex, State.unit,
        tensorPowerBipartiteAmplitude]
  | succ n ih =>
      intro i j
      rcases i with ⟨⟨ia, ias⟩, ⟨ib, ibs⟩⟩
      rcases j with ⟨⟨ja, jas⟩, ⟨jb, jbs⟩⟩
      change
        (φ.state.tensorPower (n + 1)).matrix
            ((ia, ib),
              (tensorPowerProdEquiv A B n).symm (ias, ibs))
            ((ja, jb),
              (tensorPowerProdEquiv A B n).symm (jas, jbs)) =
          _
      simp only [State.tensorPower, State.prod, Matrix.kronecker,
        Matrix.kroneckerMap_apply, PureVector.state_matrix_apply,
        tensorPowerBipartiteAmplitude]
      have hrest := ih (ias, ibs) (jas, jbs)
      change
        (φ.state.tensorPower n).matrix
            ((tensorPowerProdEquiv A B n).symm (ias, ibs))
            ((tensorPowerProdEquiv A B n).symm (jas, jbs)) =
          _ at hrest
      rw [hrest]
      rw [star_mul']
      ring

/-- The concrete tensor-power state matrix is the rank-one matrix of the
recursively factored bipartite amplitude. -/
theorem tensorPowerBipartite_matrix_eq_rankOne
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (φ : PureVector (A × B)) (n : ℕ) :
    (φ.state.tensorPowerBipartite n).matrix =
      rankOneMatrix
        (fun i : TensorPower A n × TensorPower B n =>
          tensorPowerBipartiteAmplitude φ n i.1 i.2) := by
  ext i j
  rw [tensorPowerBipartite_matrix_apply]
  simp only [rankOneMatrix_apply]

/-- Tensor powers of a bipartite pure state remain bundled pure vectors in the
party-grouped `Aⁿ × Bⁿ` coordinates. -/
noncomputable def tensorPowerBipartitePureVector
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (φ : PureVector (A × B)) (n : ℕ) :
    PureVector (TensorPower A n × TensorPower B n) where
  amp := fun i => tensorPowerBipartiteAmplitude φ n i.1 i.2
  trace_rankOne_eq_one := by
    rw [← tensorPowerBipartite_matrix_eq_rankOne φ n]
    exact (φ.state.tensorPowerBipartite n).trace_eq_one

/-- The bundled tensor-power pure vector has exactly the existing
`State.tensorPowerBipartite` state. -/
@[simp]
theorem tensorPowerBipartitePureVector_state
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (φ : PureVector (A × B)) (n : ℕ) :
    (tensorPowerBipartitePureVector φ n).state =
      φ.state.tensorPowerBipartite n := by
  apply State.ext
  exact (tensorPowerBipartite_matrix_eq_rankOne φ n).symm

/-! ### Explicit IID Schmidt decomposition -/

private noncomputable def iidSchmidtLeftAmplitude
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) :
    (n : ℕ) → TensorPower A n → TensorPower A n → ℂ
  | 0, _, _ => 1
  | n + 1, xs, as =>
      ψ.state.marginalA.pos.isHermitian.eigenvectorBasis xs.1 as.1 *
        iidSchmidtLeftAmplitude ψ n xs.2 as.2

private noncomputable def iidSchmidtRightAmplitude
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) :
    (n : ℕ) → TensorPower A n → TensorPower B n → ℂ
  | 0, _, _ => 1
  | n + 1, xs, bs =>
      (∑ a : A,
          star
              (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis xs.1 a) *
            ψ.amp (a, bs.1)) *
        iidSchmidtRightAmplitude ψ n xs.2 bs.2

private noncomputable def iidSchmidtComponent
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (n : ℕ) (xs : TensorPower A n) :
    TensorPower A n × TensorPower B n → ℂ :=
  fun ab =>
    iidSchmidtLeftAmplitude ψ n xs ab.1 *
      iidSchmidtRightAmplitude ψ n xs ab.2

private theorem sum_iidSchmidtComponent
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) :
    ∀ n : ℕ,
      ∑ xs : TensorPower A n, iidSchmidtComponent ψ n xs =
        fun ab =>
          tensorPowerBipartiteAmplitude ψ n ab.1 ab.2 := by
  intro n
  induction n with
  | zero =>
      funext ab
      rcases ab with ⟨as, bs⟩
      cases as
      cases bs
      simp [TensorPower, iidSchmidtComponent,
        iidSchmidtLeftAmplitude, iidSchmidtRightAmplitude,
        tensorPowerBipartiteAmplitude]
  | succ n ih =>
      funext ab
      rcases ab with ⟨⟨a, as⟩, ⟨b, bs⟩⟩
      have hhead :=
        congrFun (sum_marginalEigenvectorAmplitude ψ) (a, b)
      have htail := congrFun ih (as, bs)
      simp only [Finset.sum_apply]
      change
        (∑ xs : A × TensorPower A n,
            iidSchmidtComponent ψ (n + 1) xs
              ((a, as), (b, bs))) =
          tensorPowerBipartiteAmplitude ψ (n + 1)
            (a, as) (b, bs)
      rw [Fintype.sum_prod_type]
      simp only [iidSchmidtComponent,
        iidSchmidtLeftAmplitude, iidSchmidtRightAmplitude,
        tensorPowerBipartiteAmplitude]
      calc
        (∑ x : A, ∑ xs : TensorPower A n,
            (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis x a *
                iidSchmidtLeftAmplitude ψ n xs as) *
              ((∑ a' : A,
                  star
                      (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis x a') *
                    ψ.amp (a', b)) *
                iidSchmidtRightAmplitude ψ n xs bs)) =
            (∑ x : A,
                ψ.state.marginalA.pos.isHermitian.eigenvectorBasis x a *
                  ∑ a' : A,
                    star
                        (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis x a') *
                      ψ.amp (a', b)) *
              (∑ xs : TensorPower A n,
                iidSchmidtLeftAmplitude ψ n xs as *
                  iidSchmidtRightAmplitude ψ n xs bs) := by
              rw [Finset.sum_mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro xs hxs
              ring
        _ =
            ψ.amp (a, b) *
              tensorPowerBipartiteAmplitude ψ n as bs := by
          simp only [Finset.sum_apply, marginalEigenvectorAmplitude] at hhead
          simp only [Finset.sum_apply, iidSchmidtComponent] at htail
          rw [hhead, htail]

private theorem marginalEigenvectorBasis_amplitudeSquaredNorm
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (i : A) :
    amplitudeSquaredNorm
        (fun a =>
          ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i a) =
      1 := by
  rw [amplitudeSquaredNorm, ← PiLp.norm_sq_eq_of_L2]
  rw [
    ψ.state.marginalA.pos.isHermitian.eigenvectorBasis.orthonormal.1 i]
  norm_num

private theorem iidSchmidtLeftAmplitude_amplitudeSquaredNorm
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) :
    ∀ (n : ℕ) (xs : TensorPower A n),
      amplitudeSquaredNorm (iidSchmidtLeftAmplitude ψ n xs) = 1 := by
  intro n
  induction n with
  | zero =>
      intro xs
      cases xs
      simp [TensorPower, iidSchmidtLeftAmplitude,
        amplitudeSquaredNorm]
  | succ n ih =>
      intro xs
      change
        amplitudeSquaredNorm
            (fun as : A × TensorPower A n =>
              ψ.state.marginalA.pos.isHermitian.eigenvectorBasis xs.1 as.1 *
                iidSchmidtLeftAmplitude ψ n xs.2 as.2) =
          1
      rw [amplitudeSquaredNorm_product,
        marginalEigenvectorBasis_amplitudeSquaredNorm ψ xs.1,
        ih xs.2, one_mul]

private theorem iidSchmidtRightAmplitude_amplitudeSquaredNorm
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) :
    ∀ (n : ℕ) (xs : TensorPower A n),
      amplitudeSquaredNorm (iidSchmidtRightAmplitude ψ n xs) =
        iidSpectrumWeight
          (fun i =>
            ψ.state.marginalA.pos.isHermitian.eigenvalues i)
          n xs := by
  intro n
  induction n with
  | zero =>
      intro xs
      cases xs
      simp [TensorPower, iidSchmidtRightAmplitude,
        iidSpectrumWeight, amplitudeSquaredNorm]
  | succ n ih =>
      intro xs
      change
        amplitudeSquaredNorm
            (fun bs : B × TensorPower B n =>
              (∑ a : A,
                  star
                      (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis
                        xs.1 a) *
                    ψ.amp (a, bs.1)) *
                iidSchmidtRightAmplitude ψ n xs.2 bs.2) =
          ψ.state.marginalA.pos.isHermitian.eigenvalues xs.1 *
            iidSpectrumWeight
              (fun i =>
                ψ.state.marginalA.pos.isHermitian.eigenvalues i)
              n xs.2
      calc
        amplitudeSquaredNorm
            (fun bs : B × TensorPower B n =>
              (∑ a : A,
                  star
                      (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis
                        xs.1 a) *
                    ψ.amp (a, bs.1)) *
                iidSchmidtRightAmplitude ψ n xs.2 bs.2) =
            amplitudeSquaredNorm
                (fun b : B =>
                  ∑ a : A,
                    star
                        (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis
                          xs.1 a) *
                      ψ.amp (a, b)) *
              amplitudeSquaredNorm
                (iidSchmidtRightAmplitude ψ n xs.2) :=
          amplitudeSquaredNorm_product
            (fun b : B =>
              ∑ a : A,
                star
                    (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis
                      xs.1 a) *
                  ψ.amp (a, b))
            (iidSchmidtRightAmplitude ψ n xs.2)
        _ =
            ψ.state.marginalA.pos.isHermitian.eigenvalues xs.1 *
              iidSpectrumWeight
                (fun i =>
                  ψ.state.marginalA.pos.isHermitian.eigenvalues i)
                n xs.2 := by
          rw [marginalEigenvector_projected_amplitudeSquaredNorm ψ xs.1,
            ih xs.2]

private theorem iidSchmidtComponent_amplitudeSquaredNorm
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (n : ℕ) (xs : TensorPower A n) :
    amplitudeSquaredNorm (iidSchmidtComponent ψ n xs) =
      iidSpectrumWeight
        (fun i =>
          ψ.state.marginalA.pos.isHermitian.eigenvalues i)
        n xs := by
  change
    amplitudeSquaredNorm
        (fun ab : TensorPower A n × TensorPower B n =>
          iidSchmidtLeftAmplitude ψ n xs ab.1 *
            iidSchmidtRightAmplitude ψ n xs ab.2) =
      _
  rw [amplitudeSquaredNorm_product,
    iidSchmidtLeftAmplitude_amplitudeSquaredNorm ψ n xs,
    iidSchmidtRightAmplitude_amplitudeSquaredNorm ψ n xs,
    one_mul]

private theorem dotProduct_product
    {A : Type u} {B : Type v}
    [Fintype A] [Fintype B]
    (a c : A → ℂ) (b d : B → ℂ) :
    (fun ab : A × B => star (a ab.1 * b ab.2)) ⬝ᵥ
        (fun ab : A × B => c ab.1 * d ab.2) =
      ((fun i => star (a i)) ⬝ᵥ c) *
        ((fun j => star (b j)) ⬝ᵥ d) := by
  simp only [dotProduct, Fintype.sum_prod_type, star_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem marginalEigenvectorBasis_dotProduct_eq_zero
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) {i j : A} (hij : i ≠ j) :
    (fun a =>
        star
          (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i a)) ⬝ᵥ
        (fun a =>
          ψ.state.marginalA.pos.isHermitian.eigenvectorBasis j a) =
      0 := by
  let e := ψ.state.marginalA.pos.isHermitian.eigenvectorBasis
  calc
    (fun a => star (e i a)) ⬝ᵥ (fun a => e j a) =
        inner ℂ (e i) (e j) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dotProduct, Pi.star_apply]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = 0 := by rw [e.inner_eq_ite, if_neg hij]

private theorem iidSchmidtLeftAmplitude_dotProduct_eq_zero
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) :
    ∀ (n : ℕ) {xs ys : TensorPower A n},
      xs ≠ ys →
        (fun as => star (iidSchmidtLeftAmplitude ψ n xs as)) ⬝ᵥ
            iidSchmidtLeftAmplitude ψ n ys =
          0 := by
  intro n
  induction n with
  | zero =>
      intro xs ys hxy
      cases xs
      cases ys
      exact (hxy rfl).elim
  | succ n ih =>
      intro xs ys hxy
      rcases xs with ⟨x, xs⟩
      rcases ys with ⟨y, ys⟩
      change
        (fun as : A × TensorPower A n =>
          star
            (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis x as.1 *
              iidSchmidtLeftAmplitude ψ n xs as.2)) ⬝ᵥ
            (fun as : A × TensorPower A n =>
              ψ.state.marginalA.pos.isHermitian.eigenvectorBasis y as.1 *
                iidSchmidtLeftAmplitude ψ n ys as.2) =
          0
      rw [dotProduct_product]
      by_cases hhead : x = y
      · subst y
        have htail : xs ≠ ys := by
          intro h
          subst ys
          exact hxy rfl
        rw [ih htail, mul_zero]
      · rw [marginalEigenvectorBasis_dotProduct_eq_zero ψ hhead,
          zero_mul]

private theorem iidSchmidtComponent_dotProduct_eq_zero
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (n : ℕ)
    {xs ys : TensorPower A n} (hxy : xs ≠ ys) :
    (fun ab => star (iidSchmidtComponent ψ n xs ab)) ⬝ᵥ
        iidSchmidtComponent ψ n ys =
      0 := by
  change
    (fun ab : TensorPower A n × TensorPower B n =>
      star
        (iidSchmidtLeftAmplitude ψ n xs ab.1 *
          iidSchmidtRightAmplitude ψ n xs ab.2)) ⬝ᵥ
        (fun ab : TensorPower A n × TensorPower B n =>
          iidSchmidtLeftAmplitude ψ n ys ab.1 *
            iidSchmidtRightAmplitude ψ n ys ab.2) =
      0
  rw [dotProduct_product,
    iidSchmidtLeftAmplitude_dotProduct_eq_zero ψ n hxy,
    zero_mul]

private noncomputable def iidSchmidtTruncation
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (n : ℕ)
    (S : Finset (TensorPower A n)) :
    TensorPower A n × TensorPower B n → ℂ :=
  ∑ xs ∈ S, iidSchmidtComponent ψ n xs

private theorem iidSchmidtTruncation_add_compl
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (n : ℕ)
    (S : Finset (TensorPower A n)) :
    iidSchmidtTruncation ψ n S +
        iidSchmidtTruncation ψ n (Finset.univ \ S) =
      fun ab =>
        tensorPowerBipartiteAmplitude ψ n ab.1 ab.2 := by
  unfold iidSchmidtTruncation
  calc
    (∑ xs ∈ S, iidSchmidtComponent ψ n xs) +
          ∑ xs ∈ Finset.univ \ S, iidSchmidtComponent ψ n xs =
        ∑ xs : TensorPower A n, iidSchmidtComponent ψ n xs := by
      rw [add_comm]
      exact Finset.sum_sdiff (Finset.subset_univ S)
    _ =
        (fun ab =>
          tensorPowerBipartiteAmplitude ψ n ab.1 ab.2) :=
      sum_iidSchmidtComponent ψ n

private theorem iidSchmidtTruncation_amplitudeSquaredNorm
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (n : ℕ)
    (S : Finset (TensorPower A n)) :
    amplitudeSquaredNorm (iidSchmidtTruncation ψ n S) =
      ∑ xs ∈ S,
        iidSpectrumWeight
          (fun i =>
            ψ.state.marginalA.pos.isHermitian.eigenvalues i)
          n xs := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [iidSchmidtTruncation, amplitudeSquaredNorm]
  | @insert xs S hxs ih =>
      have horth :
          (fun ab => star (iidSchmidtComponent ψ n xs ab)) ⬝ᵥ
              iidSchmidtTruncation ψ n S =
            0 := by
        unfold iidSchmidtTruncation
        rw [dotProduct_sum]
        apply Finset.sum_eq_zero
        intro ys hys
        apply iidSchmidtComponent_dotProduct_eq_zero ψ n
        intro h
        apply hxs
        rwa [h]
      have hadd :=
        amplitudeSquaredNorm_add_of_dotProduct_eq_zero
          (iidSchmidtComponent ψ n xs)
          (iidSchmidtTruncation ψ n S) horth
      calc
        amplitudeSquaredNorm
            (iidSchmidtTruncation ψ n (insert xs S)) =
            amplitudeSquaredNorm
              (iidSchmidtComponent ψ n xs +
                iidSchmidtTruncation ψ n S) := by
          congr 1
          simp [iidSchmidtTruncation, hxs]
        _ =
            amplitudeSquaredNorm (iidSchmidtComponent ψ n xs) +
              amplitudeSquaredNorm (iidSchmidtTruncation ψ n S) :=
          hadd
        _ =
            iidSpectrumWeight
                (fun i =>
                  ψ.state.marginalA.pos.isHermitian.eigenvalues i)
                n xs +
              ∑ ys ∈ S,
                iidSpectrumWeight
                  (fun i =>
                    ψ.state.marginalA.pos.isHermitian.eigenvalues i)
                  n ys := by
          rw [iidSchmidtComponent_amplitudeSquaredNorm, ih]
        _ =
            ∑ ys ∈ insert xs S,
              iidSpectrumWeight
                (fun i =>
                  ψ.state.marginalA.pos.isHermitian.eigenvalues i)
                n ys := by
          rw [Finset.sum_insert hxs]

private theorem iidSpectrumWeight_sum_compl_lowInformationSupport
    {X : Type u} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (n : ℕ) :
    (∑ xs ∈
        (Finset.univ \ iidLowInformationSupport p T n),
        iidSpectrumWeight p n xs) =
      iidHighInformationMass p T n := by
  rw [← Fintype.sum_ite_mem]
  unfold iidHighInformationMass
  apply Finset.sum_congr rfl
  intro xs hxs
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    iidLowInformationSupport, Finset.mem_filter]
  by_cases hweight : 0 < iidSpectrumWeight p n xs
  · by_cases hinformation :
        iidSchmidtSelfInformation p n xs ≤ (n : ℝ) * T
    · have hnotHigh :
          ¬(n : ℝ) * T < iidSchmidtSelfInformation p n xs :=
        not_lt_of_ge hinformation
      simp [hweight, hinformation, hnotHigh]
    · have hhigh :
          (n : ℝ) * T < iidSchmidtSelfInformation p n xs :=
        lt_of_not_ge hinformation
      simp [hweight, hinformation, hhigh]
  · have hweightZero :
        iidSpectrumWeight p n xs = 0 :=
      le_antisymm (not_lt.mp hweight)
        (iidSpectrumWeight_nonneg p hp n xs)
    simp [hweightZero]

private theorem iidSchmidtTruncation_compl_amplitudeSquaredNorm
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (T : ℝ) (n : ℕ) :
    amplitudeSquaredNorm
        (iidSchmidtTruncation ψ n
          (Finset.univ \
            iidLowInformationSupport
              (fun i =>
                ψ.state.marginalA.pos.isHermitian.eigenvalues i)
              T n)) =
      iidHighInformationMass
        (fun i =>
          ψ.state.marginalA.pos.isHermitian.eigenvalues i)
        T n := by
  rw [iidSchmidtTruncation_amplitudeSquaredNorm]
  exact
    iidSpectrumWeight_sum_compl_lowInformationSupport
      (fun i =>
        ψ.state.marginalA.pos.isHermitian.eigenvalues i)
      (stateEigenvalues_isProbabilityDistribution ψ.state.marginalA)
      T n

/-- Regard a bipartite amplitude vector as its coefficient matrix, whose
matrix rank is the pure state's Schmidt rank. -/
def bipartiteAmplitudeMatrix
    {A : Type u} {B : Type v}
    (z : A × B → ℂ) : Matrix A B ℂ :=
  fun a b => z (a, b)

/-- Acting by a product matrix on a bipartite vector is left/right
multiplication of its coefficient matrix. -/
theorem bipartiteAmplitudeMatrix_kronecker_mulVec
    {A : Type u} {B : Type v}
    {A' : Type*} {B' : Type*}
    [Fintype A] [Fintype B]
    (L : Matrix A' A ℂ) (R : Matrix B' B ℂ)
    (z : A × B → ℂ) :
    bipartiteAmplitudeMatrix ((Matrix.kronecker L R).mulVec z) =
      L * bipartiteAmplitudeMatrix z * R.transpose := by
  ext a' b'
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.mul_apply,
    Matrix.transpose_apply, bipartiteAmplitudeMatrix]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- A product Kraus branch cannot increase the Schmidt matrix rank of a pure
bipartite input vector. -/
theorem rank_bipartiteAmplitudeMatrix_kronecker_mulVec_le
    {A : Type u} {B : Type v}
    {A' : Type*} {B' : Type*}
    [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B']
    (L : Matrix A' A ℂ) (R : Matrix B' B ℂ)
    (z : A × B → ℂ) :
    (bipartiteAmplitudeMatrix
        ((Matrix.kronecker L R).mulVec z)).rank ≤
      (bipartiteAmplitudeMatrix z).rank := by
  rw [bipartiteAmplitudeMatrix_kronecker_mulVec]
  exact
    (Matrix.rank_mul_le_left _ _).trans
      (Matrix.rank_mul_le_right _ _)

/-- Every individual branch of a concrete `LOCCProtocol` preserves the
pure-state Schmidt-rank upper bound. -/
theorem LOCCProtocol.rank_branch_bipartiteAmplitudeMatrix_le
    {A : Type u} {B : Type v}
    {A' : Type*} {B' : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (P : LOCCProtocol A B A' B')
    (k : P.KrausIndex) (z : A × B → ℂ) :
    (bipartiteAmplitudeMatrix
        ((P.productKraus k).mulVec z)).rank ≤
      (bipartiteAmplitudeMatrix z).rank := by
  simpa [LOCCProtocol.productKraus] using
    rank_bipartiteAmplitudeMatrix_kronecker_mulVec_le
      (P.leftKraus k) (P.rightKraus k) z

private theorem mul_rankOneMatrix_mul_conjTranspose
    {I : Type u} {O : Type v}
    [Fintype I] [Fintype O]
    (K : Matrix O I ℂ) (z : I → ℂ) :
    K * rankOneMatrix z * Matrix.conjTranspose K =
      rankOneMatrix (K.mulVec z) := by
  unfold rankOneMatrix
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  exact (Matrix.star_mulVec K z).symm

/-- A product-Kraus protocol sends a pure input density matrix to the sum of
the rank-one branch output matrices. -/
theorem LOCCProtocol.applyState_pureVector_matrix_eq_sum_rankOne
    {A : Type u} {B : Type v}
    {A' : Type*} {B' : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (P : LOCCProtocol A B A' B')
    (φ : PureVector (A × B)) :
    (P.channel.applyState φ.state).matrix =
      (letI := P.fintypeKrausIndex
       ∑ k : P.KrausIndex,
        rankOneMatrix ((P.productKraus k).mulVec φ.amp)) := by
  letI := P.fintypeKrausIndex
  change
    (MatrixMap.ofKraus P.productKraus)
        (rankOneMatrix φ.amp) = _
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro k hk
  exact
    mul_rankOneMatrix_mul_conjTranspose
      (P.productKraus k) φ.amp

/-- The explicit IID Schmidt decomposition turns spectral truncation into the
one-shot LOCC fidelity envelope without choosing tensor-product eigenvalue
indices. -/
theorem LOCCProtocol.sqrt_sum_branch_maximallyEntangled_overlap_sq_le_iidTruncation
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (M : ℕ) (hM : 0 < M)
    (n : ℕ)
    (P : LOCCProtocol.{u, v, 0, 0, 0}
      (TensorPower A n) (TensorPower B n)
      (Fin M) (Fin M))
    (ψ : PureVector (A × B)) (T : ℝ) :
    let p : A → ℝ :=
      fun i => ψ.state.marginalA.pos.isHermitian.eigenvalues i
    letI := P.fintypeKrausIndex
    Real.sqrt
        (∑ k : P.KrausIndex,
          ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
            (P.productKraus k).mulVec
              (tensorPowerBipartitePureVector ψ n).amp‖ ^ 2) ≤
      Real.sqrt
          (((iidLowInformationSupport p T n).card : ℝ) / (M : ℝ)) +
        Real.sqrt (iidHighInformationMass p T n) := by
  let p : A → ℝ :=
    fun i => ψ.state.marginalA.pos.isHermitian.eigenvalues i
  let S : Finset (TensorPower A n) :=
    iidLowInformationSupport p T n
  letI := P.fintypeKrausIndex
  have hp : IsProbabilityDistribution p := by
    exact stateEigenvalues_isProbabilityDistribution ψ.state.marginalA
  have hsplit :=
    iidSchmidtTruncation_add_compl ψ n S
  have hminkowski :=
    LOCCProtocol.sqrt_sum_branch_overlap_sq_add_le
      P (maximallyEntangledVector M)
        (amplitudeSquaredNorm_maximallyEntangledVector M hM)
        (iidSchmidtTruncation ψ n S)
        (iidSchmidtTruncation ψ n (Finset.univ \ S))
  have hlowRaw :=
    LOCCProtocol.sum_branch_maximallyEntangled_overlap_sq_sum_product_le
      M hM P S
        (iidSchmidtLeftAmplitude ψ n)
        (iidSchmidtRightAmplitude ψ n)
  have hlow :
      (∑ k : P.KrausIndex,
        ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
          (P.productKraus k).mulVec
            (iidSchmidtTruncation ψ n S)‖ ^ 2) ≤
        (S.card : ℝ) / (M : ℝ) := by
    have hmass :
        (∑ xs ∈ S,
          amplitudeSquaredNorm (iidSchmidtComponent ψ n xs)) ≤
          1 := by
      calc
        (∑ xs ∈ S,
            amplitudeSquaredNorm (iidSchmidtComponent ψ n xs)) =
            ∑ xs ∈ S, iidSpectrumWeight p n xs := by
          apply Finset.sum_congr rfl
          intro xs hxs
          exact iidSchmidtComponent_amplitudeSquaredNorm ψ n xs
        _ ≤ ∑ xs : TensorPower A n, iidSpectrumWeight p n xs :=
          Finset.sum_le_univ_sum_of_nonneg
            (fun xs => iidSpectrumWeight_nonneg p hp n xs)
        _ = 1 := iidSpectrumWeight_sum p hp n
    have hmass' :
        (∑ xs ∈ S,
          amplitudeSquaredNorm
            (fun ab : TensorPower A n × TensorPower B n =>
              iidSchmidtLeftAmplitude ψ n xs ab.1 *
                iidSchmidtRightAmplitude ψ n xs ab.2)) ≤
          1 := by
      simpa only [iidSchmidtComponent] using hmass
    calc
      (∑ k : P.KrausIndex,
        ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
          (P.productKraus k).mulVec
            (iidSchmidtTruncation ψ n S)‖ ^ 2) ≤
          ((S.card : ℝ) / (M : ℝ)) *
            ∑ xs ∈ S,
              amplitudeSquaredNorm
                (fun ab : TensorPower A n × TensorPower B n =>
                  iidSchmidtLeftAmplitude ψ n xs ab.1 *
                    iidSchmidtRightAmplitude ψ n xs ab.2) := by
        simpa only [iidSchmidtTruncation, iidSchmidtComponent] using
          hlowRaw
      _ ≤ ((S.card : ℝ) / (M : ℝ)) * 1 := by
        exact
          mul_le_mul_of_nonneg_left hmass'
            (div_nonneg (Nat.cast_nonneg S.card) (Nat.cast_nonneg M))
      _ = (S.card : ℝ) / (M : ℝ) := mul_one _
  have hlowSqrt :
      Real.sqrt
          (∑ k : P.KrausIndex,
            ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
              (P.productKraus k).mulVec
                (iidSchmidtTruncation ψ n S)‖ ^ 2) ≤
        Real.sqrt ((S.card : ℝ) / (M : ℝ)) :=
    Real.sqrt_le_sqrt hlow
  calc
    Real.sqrt
        (∑ k : P.KrausIndex,
          ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
            (P.productKraus k).mulVec
              (tensorPowerBipartitePureVector ψ n).amp‖ ^ 2) =
        Real.sqrt
          (∑ k : P.KrausIndex,
            ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
              (P.productKraus k).mulVec
                (iidSchmidtTruncation ψ n S +
                  iidSchmidtTruncation ψ n
                    (Finset.univ \ S))‖ ^ 2) := by
      rw [hsplit]
      rfl
    _ ≤
        Real.sqrt
            (∑ k : P.KrausIndex,
              ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
                (P.productKraus k).mulVec
                  (iidSchmidtTruncation ψ n S)‖ ^ 2) +
          Real.sqrt
            (amplitudeSquaredNorm
              (iidSchmidtTruncation ψ n
                (Finset.univ \ S))) :=
      hminkowski
    _ ≤
        Real.sqrt ((S.card : ℝ) / (M : ℝ)) +
          Real.sqrt
            (amplitudeSquaredNorm
              (iidSchmidtTruncation ψ n
                (Finset.univ \ S))) :=
      add_le_add hlowSqrt le_rfl
    _ =
        Real.sqrt
            (((iidLowInformationSupport p T n).card : ℝ) / (M : ℝ)) +
          Real.sqrt (iidHighInformationMass p T n) := by
      dsimp [S]
      rw [iidSchmidtTruncation_compl_amplitudeSquaredNorm]

/-- If finite-round LOCC protocols concentrate `n` copies of a bipartite pure
state into rank-`M n` maximally entangled states with fidelity tending to one,
then their asymptotic concentration rate is at most the input entanglement
entropy.

`AsymptoticRateAtMost E M` is the Base-library eventual-upper-bound
formulation of `limsupₙ (1 / n) log₂ (M n) ≤ E`.
-/
theorem converse_entanglement_concentration
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B))
    (M : ℕ → ℕ)
    (hM : ∀ n : ℕ, 0 < M n)
    (Λ : (n : ℕ) →
      Channel
        (TensorPower A n × TensorPower B n)
        (Fin (M n) × Fin (M n)))
    (hLOCC : ∀ n : ℕ, IsFiniteRoundLOCC (Λ n))
    (ρ : (n : ℕ) → State (Fin (M n) × Fin (M n)))
    (hρ : ∀ n : ℕ,
      ρ n = (Λ n).applyState (ψ.state.tensorPowerBipartite n))
    (hF : Tendsto
      (fun n : ℕ =>
        quantumFidelity (ρ n).matrix (maximallyEntangledDensity (M n)))
      atTop (𝓝 1)) :
    AsymptoticRateAtMost (entanglementEntropy ψ) M := by
  let p : A → ℝ :=
    fun i => ψ.state.marginalA.pos.isHermitian.eigenvalues i
  have hp : IsProbabilityDistribution p :=
    stateEigenvalues_isProbabilityDistribution ψ.state.marginalA
  have hEntropy :
      entanglementEntropy ψ = schmidtEntropy p :=
    entanglementEntropy_eq_schmidtEntropy_eigenvalues ψ
  apply asymptoticRateAtMost_of_eventual_iidSpectralConverseEnvelope
    p hp (entanglementEntropy ψ) hEntropy M
    (fun n : ℕ =>
      quantumFidelity (ρ n).matrix (maximallyEntangledDensity (M n)))
    hF
  intro R hR
  let T : ℝ := (entanglementEntropy ψ + R) / 2
  have hTR : T < R := by
    dsimp [T]
    linarith
  have hSeparableOutput :
      ∀ n : ℕ,
        ∃ P : LOCCProtocol
            (TensorPower A n) (TensorPower B n)
            (Fin (M n)) (Fin (M n)),
          P.channel.applyState (ψ.state.tensorPowerBipartite n) = ρ n := by
    intro n
    obtain ⟨P, hP⟩ :=
      (hLOCC n).exists_separable_protocol_applyState_eq
        (ψ.state.tensorPowerBipartite n)
    exact ⟨P, hP.trans (hρ n).symm⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  intro hnRate
  have hnpos : 0 < n := by omega
  have hsupportRatio :
      ((iidLowInformationSupport p T n).card : ℝ) / (M n : ℝ) <
        Real.rpow 2 (-((n : ℝ) * (R - T))) :=
    iidLowInformationSupport_card_div_target_lt_exponential
      p hp M hM R T n hnpos hnRate
  obtain ⟨P, hP⟩ := hSeparableOutput n
  have hOutputMatrix :
      (ρ n).matrix =
        (letI := P.fintypeKrausIndex
         ∑ k : P.KrausIndex,
          rankOneMatrix
            ((P.productKraus k).mulVec
              (tensorPowerBipartitePureVector ψ n).amp)) := by
    calc
      (ρ n).matrix =
          (P.channel.applyState
            (ψ.state.tensorPowerBipartite n)).matrix :=
        congrArg State.matrix hP.symm
      _ =
          (P.channel.applyState
            (tensorPowerBipartitePureVector ψ n).state).matrix := by
        rw [tensorPowerBipartitePureVector_state]
      _ = _ :=
        LOCCProtocol.applyState_pureVector_matrix_eq_sum_rankOne
          P (tensorPowerBipartitePureVector ψ n)
  letI := P.fintypeKrausIndex
  have hIIDTruncationBound :
      Real.sqrt
          (∑ k : P.KrausIndex,
            ‖(fun i => star (maximallyEntangledVector (M n) i)) ⬝ᵥ
              (P.productKraus k).mulVec
                (tensorPowerBipartitePureVector ψ n).amp‖ ^ 2) ≤
        Real.sqrt
            (((iidLowInformationSupport p T n).card : ℝ) /
              (M n : ℝ)) +
          Real.sqrt (iidHighInformationMass p T n) :=
    LOCCProtocol.sqrt_sum_branch_maximallyEntangled_overlap_sq_le_iidTruncation
      (M n) (hM n) n P ψ T
  rw [maximallyEntangledDensity, hOutputMatrix,
    quantumFidelity_sum_rankOneMatrix]
  calc
    Real.sqrt
        (∑ k : P.KrausIndex,
          ‖(fun i => star (maximallyEntangledVector (M n) i)) ⬝ᵥ
              (P.productKraus k).mulVec
                (tensorPowerBipartitePureVector ψ n).amp‖ ^ 2) ≤
        Real.sqrt
            (((iidLowInformationSupport p T n).card : ℝ) /
              (M n : ℝ)) +
          Real.sqrt (iidHighInformationMass p T n) :=
      hIIDTruncationBound
    _ ≤
        Real.sqrt
            (Real.rpow 2 (-((n : ℝ) * (R - T)))) +
          Real.sqrt (iidHighInformationMass p T n) := by
      gcongr
    _ = iidSpectralConverseEnvelope p R T n := by
      rw [iidSpectralConverseEnvelope]
      ring

end

end QITFormalized.OneShotEntropiesAndHypothesisTesting.ConverseEntanglementConcentration
