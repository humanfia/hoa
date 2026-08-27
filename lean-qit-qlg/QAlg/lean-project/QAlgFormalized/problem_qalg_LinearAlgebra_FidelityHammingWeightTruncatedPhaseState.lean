import QAlgBench.Base
import Mathlib.Order.LiminfLimsup

/-!
# Fidelity of a Hamming-weight-truncated phase state

Computational basis labels for `Qubits n` are the integers below `2 ^ n`.
Accordingly, `Nat.testBit` identifies such a label with its binary string in
`{0,1}^n`.  The order chosen for the bits is immaterial to Hamming weight and
the binary inner product used below.
-/

open scoped BigOperators

namespace QAlgBench

namespace FidelityHammingWeightTruncatedPhaseState

noncomputable section

/-- The Hamming weight of the `n`-bit computational basis label `y`. -/
def hammingWeight {n : ℕ} (y : (Qubits n).Index) : ℕ :=
  ∑ i : Fin n, if y.val.testBit i.val then 1 else 0

/-- The inner product of two `n`-bit strings over `𝔽₂`, represented by its
canonical natural-number value `0` or `1`. -/
def binaryInnerProduct {n : ℕ} (x y : (Qubits n).Index) : ℕ :=
  (∑ i : Fin n, if x.val.testBit i.val && y.val.testBit i.val then 1 else 0) % 2

/-- `R_{n,r} = ∑_{i=0}^r (n choose i)`, the cardinality of the Hamming ball of
radius `r` in `{0,1}^n` (in particular when `r ≤ n`). -/
def hammingBallCard (n r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (r + 1), Nat.choose n i

/-- Append one bit above the `n` low bits of a computational-basis label. -/
private def appendHighBit {n : ℕ} (b : Fin 2) (y : Fin (2 ^ n)) :
    Fin (2 ^ (n + 1)) :=
  ⟨y.val + 2 ^ n * b.val, by
    have hb : b.val ≤ 1 := by omega
    rw [pow_succ]
    nlinarith [y.isLt, Nat.two_pow_pos n]⟩

/-- Splitting off the highest bit is an equivalence. -/
private def appendHighBitEquiv (n : ℕ) :
    Fin 2 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_succ]; omega))

private lemma appendHighBitEquiv_apply {n : ℕ} (z : Fin 2 × Fin (2 ^ n)) :
    appendHighBitEquiv n z = appendHighBit z.1 z.2 := by
  apply Fin.ext
  rfl

private lemma hammingWeight_appendHighBit {n : ℕ} (b : Fin 2) (y : Fin (2 ^ n)) :
    hammingWeight (appendHighBit b y) = hammingWeight y + b.val := by
  rw [hammingWeight, Fin.sum_univ_castSucc]
  have hy : y.val < 2 ^ n := y.isLt
  have ht (j : ℕ) :
      (y.val + 2 ^ n * b.val).testBit j =
        if j < n then y.val.testBit j else b.val.testBit (j - n) := by
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add b.val hy]
  change
    (∑ i : Fin n,
        if (y.val + 2 ^ n * b.val).testBit i.castSucc.val then 1 else 0) +
          (if (y.val + 2 ^ n * b.val).testBit (Fin.last n).val then 1 else 0) =
      hammingWeight y + b.val
  simp [ht, hammingWeight]
  fin_cases b <;> rfl

/-- There are `n.choose k` labels of Hamming weight exactly `k`. -/
private lemma sum_indicator_hammingWeight_eq_choose (n k : ℕ) :
    (∑ y : Fin (2 ^ n), if hammingWeight y = k then (1 : ℕ) else 0) =
      n.choose k := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [hammingWeight]
  | succ n ih =>
      rw [← (appendHighBitEquiv n).sum_comp]
      simp_rw [appendHighBitEquiv_apply, hammingWeight_appendHighBit]
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_one, Nat.add_one]
      cases k with
      | zero => simp [ih]
      | succ k =>
          rw [Nat.choose_succ_succ]
          simp only [Nat.succ.injEq]
          rw [ih (k + 1), ih k]
          simp [Nat.succ_eq_add_one, Nat.add_comm]

/-- Counting labels of Hamming weight at most `r` gives the cumulative
binomial sum. -/
private lemma sum_indicator_hammingWeight_le (n r : ℕ) :
    (∑ y : Fin (2 ^ n), if hammingWeight y ≤ r then (1 : ℕ) else 0) =
      hammingBallCard n r := by
  rw [hammingBallCard]
  calc
    (∑ y : Fin (2 ^ n), if hammingWeight y ≤ r then (1 : ℕ) else 0) =
        ∑ y : Fin (2 ^ n), ∑ k ∈ Finset.range (r + 1),
          if hammingWeight y = k then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      classical
      by_cases h : hammingWeight y ≤ r <;> simp [h]
    _ = ∑ k ∈ Finset.range (r + 1), ∑ y : Fin (2 ^ n),
          if hammingWeight y = k then (1 : ℕ) else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [sum_indicator_hammingWeight_eq_choose]

private lemma hammingBallCard_pos (n r : ℕ) : 0 < hammingBallCard n r := by
  rw [hammingBallCard]
  exact Finset.sum_pos' (fun i hi => Nat.zero_le _)
    ⟨0, by simp, by simp⟩

private lemma hammingBallCard_le_two_pow (n r : ℕ) :
    hammingBallCard n r ≤ 2 ^ n := by
  rw [← sum_indicator_hammingWeight_le]
  calc
    (∑ y : Fin (2 ^ n), if hammingWeight y ≤ r then (1 : ℕ) else 0) ≤
        ∑ _y : Fin (2 ^ n), (1 : ℕ) := by
      gcongr with y
      split <;> simp
    _ = 2 ^ n := by simp

/-- The exact variance numerator of the Hamming weight of a uniformly chosen
bit string. -/
private lemma centered_hammingWeight_sq_sum (n : ℕ) :
    (∑ y : Fin (2 ^ n),
        (((hammingWeight y : ℕ) : ℝ) - (n : ℝ) / 2) ^ 2) =
      (n : ℝ) * (2 : ℝ) ^ n / 4 := by
  induction n with
  | zero => simp [hammingWeight]
  | succ n ih =>
      rw [← (appendHighBitEquiv n).sum_comp]
      simp_rw [appendHighBitEquiv_apply, hammingWeight_appendHighBit]
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_one, Nat.add_one, Nat.cast_succ]
      rw [← Finset.sum_add_distrib]
      have hpoint (y : Fin (2 ^ n)) :
          (((hammingWeight y : ℕ) : ℝ) - ((n : ℝ) + 1) / 2) ^ 2 +
              ((((hammingWeight y : ℕ) : ℝ) + 1) - ((n : ℝ) + 1) / 2) ^ 2 =
            2 * ((((hammingWeight y : ℕ) : ℝ) - (n : ℝ) / 2) ^ 2) + 1 / 2 := by
        ring
      simp_rw [hpoint, Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul]
      push_cast
      rw [pow_succ]
      ring

/-- The raw vector
`2^{-n/2} ∑_y (-1)^{x · y} |y⟩`.

The coefficient is written as `1 / sqrt (2^n)`, which is equal to
`2^{-n/2}`. -/
def phaseStateVec {n : ℕ} (x : (Qubits n).Index) : StateVector (Qubits n) :=
  WithLp.toLp 2 fun y =>
    ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) * (-1 : ℂ) ^ binaryInnerProduct x y

/-- The full phase vector is normalized. -/
theorem norm_phaseStateVec {n : ℕ} (x : (Qubits n).Index) :
    ‖phaseStateVec x‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  change
    √(∑ y : (Qubits n).Index,
        ‖((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) *
            (-1 : ℂ) ^ binaryInnerProduct x y‖ ^ 2) = 1
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  have hp : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow]
  push_cast
  rw [Real.sq_sqrt (le_of_lt hp)]
  simp [ne_of_gt hp]

/-- The normalized phase state `|ψ_x⟩`. -/
def phaseState {n : ℕ} (x : (Qubits n).Index) : PureState (Qubits n) :=
  PureState.ofVec (phaseStateVec x) (norm_phaseStateVec x)

/-- The raw Hamming-weight-truncated vector
`R_{n,r}^{-1/2} ∑_{|y|≤r} (-1)^{x · y} |y⟩`. -/
def truncatedPhaseStateVec {n : ℕ} (x : (Qubits n).Index) (r : ℕ) :
    StateVector (Qubits n) :=
  WithLp.toLp 2 fun y =>
    if hammingWeight y ≤ r then
      ((Real.sqrt (hammingBallCard n r : ℝ))⁻¹ : ℂ) *
        (-1 : ℂ) ^ binaryInnerProduct x y
    else
      0

/-- The Hamming-weight-truncated phase vector is normalized. -/
theorem norm_truncatedPhaseStateVec {n : ℕ} (x : (Qubits n).Index) (r : ℕ) :
    ‖truncatedPhaseStateVec x r‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  change
    √(∑ y : (Qubits n).Index,
        ‖if hammingWeight y ≤ r then
            ((Real.sqrt (hammingBallCard n r : ℝ))⁻¹ : ℂ) *
              (-1 : ℂ) ^ binaryInnerProduct x y
          else 0‖ ^ 2) = 1
  simp_rw [apply_ite (fun z : ℂ => ‖z‖), ite_pow]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, norm_zero,
    zero_pow (by norm_num : 2 ≠ 0)]
  rw [← Finset.sum_filter, Finset.sum_const]
  simp only [nsmul_eq_mul]
  rw [Finset.card_filter, sum_indicator_hammingWeight_le]
  have hRnat : 0 < hammingBallCard n r := hammingBallCard_pos n r
  have hR : (0 : ℝ) < hammingBallCard n r := by exact_mod_cast hRnat
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow]
  rw [Real.sq_sqrt (le_of_lt hR)]
  simp [ne_of_gt hR]

/-- The normalized Hamming-weight-truncated phase state `|ψ_x^(r)⟩`. -/
def truncatedPhaseState {n : ℕ} (x : (Qubits n).Index) (r : ℕ) :
    PureState (Qubits n) :=
  PureState.ofVec (truncatedPhaseStateVec x r)
    (norm_truncatedPhaseStateVec x r)

/-- The squared fidelity between the full and truncated phase states is the
fraction of basis strings in the Hamming ball.  Since the right-hand side does
not contain `x`, this also states explicitly that the fidelity is independent
of the chosen phase string. -/
theorem fidelity_phaseState_truncatedPhaseState {n r : ℕ} (hr : r ≤ n)
    (x : (Qubits n).Index) :
    ‖inner ℂ (phaseState x) (truncatedPhaseState x r)‖ ^ 2 =
      (hammingBallCard n r : ℝ) / (2 : ℝ) ^ n := by
  have hsign (k : ℕ) : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hinner (y : (Qubits n).Index) :
      inner ℂ
          (((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) *
            (-1 : ℂ) ^ binaryInnerProduct x y)
          (((Real.sqrt (hammingBallCard n r : ℝ))⁻¹ : ℂ) *
            (-1 : ℂ) ^ binaryInnerProduct x y) =
        ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) *
          ((Real.sqrt (hammingBallCard n r : ℝ))⁻¹ : ℂ) := by
    rw [RCLike.inner_apply]
    simp only [map_mul, map_inv₀, Complex.conj_ofReal, map_pow, map_neg, map_one]
    calc
      _ = ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) *
          ((Real.sqrt (hammingBallCard n r : ℝ))⁻¹ : ℂ) *
          (((-1 : ℂ) ^ binaryInnerProduct x y) *
            ((-1 : ℂ) ^ binaryInnerProduct x y)) := by ring
      _ = _ := by rw [hsign]; ring
  have hoverlap :
      inner ℂ (phaseState x) (truncatedPhaseState x r) =
        ((hammingBallCard n r : ℝ) : ℂ) *
          ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) *
          ((Real.sqrt (hammingBallCard n r : ℝ))⁻¹ : ℂ) := by
    change
      inner ℂ (phaseStateVec x) (truncatedPhaseStateVec x r) =
        ((hammingBallCard n r : ℝ) : ℂ) *
          ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) *
          ((Real.sqrt (hammingBallCard n r : ℝ))⁻¹ : ℂ)
    rw [PiLp.inner_apply]
    change
      (∑ y : (Qubits n).Index,
          inner ℂ
            (((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) *
              (-1 : ℂ) ^ binaryInnerProduct x y)
            (if hammingWeight y ≤ r then
              ((Real.sqrt (hammingBallCard n r : ℝ))⁻¹ : ℂ) *
                (-1 : ℂ) ^ binaryInnerProduct x y
            else 0)) = _
    simp_rw [apply_ite, hinner, inner_zero_right]
    rw [← Finset.sum_filter, Finset.sum_const]
    simp only [nsmul_eq_mul]
    rw [Finset.card_filter, sum_indicator_hammingWeight_le]
    push_cast
    ring
  rw [hoverlap]
  have hA : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hRnat : 0 < hammingBallCard n r := hammingBallCard_pos n r
  have hR : (0 : ℝ) < hammingBallCard n r := by exact_mod_cast hRnat
  rw [norm_mul, norm_mul, Complex.norm_real, norm_inv, Complex.norm_real,
    norm_inv, Complex.norm_real]
  rw [Real.norm_of_nonneg (le_of_lt hR), Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt (le_of_lt hA),
    Real.sq_sqrt (le_of_lt hR)]
  field_simp

/-- The radius `⌊n/2 + c * sqrt n⌋` appearing in the asymptotic statement. -/
def truncationRadius (c : ℝ) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) / 2 + c * Real.sqrt n⌋₊

/-- A finite Chebyshev bound for the retained Hamming-ball fraction. -/
private lemma retained_fraction_lower_bound (c : ℝ) (hc : 0 < c) (n : ℕ)
    (hn : 0 < n) :
    (hammingBallCard n (truncationRadius c n) : ℝ) / (2 : ℝ) ^ n ≥
      1 - 1 / (4 * c ^ 2) := by
  let B : Finset (Fin (2 ^ n)) :=
    Finset.univ.filter fun y => truncationRadius c n < hammingWeight y
  have ht0 : 0 ≤ (n : ℝ) / 2 + c * Real.sqrt n := by positivity
  have hterm (y : Fin (2 ^ n)) (hy : y ∈ B) :
      c ^ 2 * (n : ℝ) ≤
        (((hammingWeight y : ℕ) : ℝ) - (n : ℝ) / 2) ^ 2 := by
    have hyr : truncationRadius c n < hammingWeight y :=
      (Finset.mem_filter.mp hy).2
    have hfloor :
        (n : ℝ) / 2 + c * Real.sqrt n < (hammingWeight y : ℕ) :=
      (Nat.floor_lt ht0).mp hyr
    have hnonneg : 0 ≤ c * Real.sqrt n :=
      mul_nonneg (le_of_lt hc) (Real.sqrt_nonneg _)
    have hdiff :
        c * Real.sqrt n ≤ ((hammingWeight y : ℕ) : ℝ) - (n : ℝ) / 2 := by
      linarith
    have hsquare := mul_self_le_mul_self hnonneg hdiff
    rw [← pow_two, ← pow_two] at hsquare
    calc
      c ^ 2 * (n : ℝ) = (c * Real.sqrt n) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      _ ≤ _ := hsquare
  have hsum :
      (B.card : ℝ) * (c ^ 2 * (n : ℝ)) ≤ (n : ℝ) * (2 : ℝ) ^ n / 4 := by
    calc
      (B.card : ℝ) * (c ^ 2 * (n : ℝ)) =
          ∑ y ∈ B, c ^ 2 * (n : ℝ) := by
        rw [Finset.sum_const]
        simp [mul_comm]
      _ ≤ ∑ y ∈ B,
          (((hammingWeight y : ℕ) : ℝ) - (n : ℝ) / 2) ^ 2 := by
        gcongr with y hy
        exact hterm y hy
      _ ≤ ∑ y : Fin (2 ^ n),
          (((hammingWeight y : ℕ) : ℝ) - (n : ℝ) / 2) ^ 2 := by
        apply Finset.sum_le_univ_sum_of_nonneg
        intro y
        positivity
      _ = _ := centered_hammingWeight_sq_sum n
  have hcard :
      hammingBallCard n (truncationRadius c n) + B.card = 2 ^ n := by
    have hp := Finset.card_filter_add_card_filter_not
      (s := Finset.univ)
      (fun y : Fin (2 ^ n) => hammingWeight y ≤ truncationRadius c n)
    rw [Finset.card_filter, sum_indicator_hammingWeight_le] at hp
    simpa [B, Nat.not_le] using hp
  have hcardR :
      (hammingBallCard n (truncationRadius c n) : ℝ) + (B.card : ℝ) =
        (2 : ℝ) ^ n := by
    exact_mod_cast hcard
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hbad : (B.card : ℝ) / (2 : ℝ) ^ n ≤ 1 / (4 * c ^ 2) := by
    rw [div_le_iff₀ hpow]
    rw [one_div, inv_mul_eq_div,
      le_div_iff₀ (by positivity : (0 : ℝ) < 4 * c ^ 2)]
    nlinarith [hsum]
  have hratio :
      (hammingBallCard n (truncationRadius c n) : ℝ) / (2 : ℝ) ^ n =
        1 - (B.card : ℝ) / (2 : ℝ) ^ n := by
    field_simp
    nlinarith [hcardR]
  rw [hratio]
  linarith

/-- For every error threshold `η ∈ (0,1)`, a positive constant offset of order
`sqrt n` makes the lower limit of the retained Hamming-ball fraction at least
`1 - η`. -/
theorem exists_positive_offset_for_hamming_ball (η : ℝ)
    (hη : η ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ cη : ℝ, 0 < cη ∧
      Filter.liminf
          (fun n : ℕ =>
            (hammingBallCard n (truncationRadius cη n) : ℝ) / (2 : ℝ) ^ n)
          Filter.atTop ≥
        1 - η := by
  refine ⟨η⁻¹, inv_pos.mpr hη.1, ?_⟩
  let f : ℕ → ℝ := fun n =>
    (hammingBallCard n (truncationRadius η⁻¹ n) : ℝ) / (2 : ℝ) ^ n
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, 1 - η ≤ f n := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hpoint :=
      retained_fraction_lower_bound η⁻¹ (inv_pos.mpr hη.1) n (by omega)
    have heta : 1 / (4 * (η⁻¹) ^ 2) ≤ η := by
      field_simp
      nlinarith [hη.1, hη.2]
    dsimp [f]
    linarith
  have hupp : ∀ n, f n ≤ 1 := by
    intro n
    dsimp [f]
    apply (div_le_iff₀ (pow_pos (by norm_num) n)).2
    norm_num
    exact_mod_cast hammingBallCard_le_two_pow n (truncationRadius η⁻¹ n)
  exact Filter.le_liminf_of_le
    (Filter.isCoboundedUnder_ge_of_le Filter.atTop hupp) hevent

end

end FidelityHammingWeightTruncatedPhaseState

end QAlgBench
