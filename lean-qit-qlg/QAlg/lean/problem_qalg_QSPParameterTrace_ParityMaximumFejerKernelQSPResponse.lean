import QAlgBench.Base

/-!
# Parity and maximum Fejér-kernel QSP responses

This file states two independent single-qubit claims.  The first concerns the
top-left response of an ordered QSP product.  The second identifies a weighted
Fourier sum with a normalized squared geometric sum and records its bounds.
-/

namespace QAlgFormalized.QSPParameterTrace.ParityMaximumFejerKernelQSPResponse

open QAlgBench

noncomputable section

/-- The Pauli `Z = diag(1, -1)` used by the processing rotations. -/
abbrev qspPauliZ : HilbertOperator (Qubits 1) := Gate.ZOp

/--
The single-qubit signal operator
`Wₓ(a) = [[a, i √(1-a²)], [i √(1-a²), a]]`.
-/
def qspSignalOperator (a : ℝ) : HilbertOperator (Qubits 1) :=
  !![(a : ℂ), Complex.I * (Real.sqrt (1 - a ^ 2) : ℂ);
     Complex.I * (Real.sqrt (1 - a ^ 2) : ℂ), (a : ℂ)]

/--
The ordered QSP product
`e^{i φ₀ Z} ∏_{j=1}^k (Wₓ(a) e^{i φⱼ Z})`.

`List.ofFn` lists `j = 0, ..., k-1` in increasing order, and `j.succ`
therefore supplies the phase indices `1, ..., k`.  Its noncommutative list
product fixes the multiplication order from the source.
-/
def qspSequenceOperator (k : ℕ) (φ : Fin (k + 1) → ℝ) (a : ℝ) :
    HilbertOperator (Qubits 1) :=
  rotZOp (φ 0) *
    (List.ofFn (fun j : Fin k =>
      qspSignalOperator a * rotZOp (φ j.succ))).prod

/-- The QSP response `A(a) = ⟨0|U_φ(a)|0⟩`. -/
def qspResponse (k : ℕ) (φ : Fin (k + 1) → ℝ) (a : ℝ) : ℂ :=
  qspSequenceOperator k φ a 0 0

private def qspTailProduct (phases : List ℝ) (a : ℝ) :
    HilbertOperator (Qubits 1) :=
  (phases.map fun phase => qspSignalOperator a * rotZOp phase).prod

private lemma qspPolyStep_firstDegree (n : ℕ) (p q : Polynomial ℂ)
    (hp : p.natDegree ≤ n) (hq : q = 0 ∨ q.natDegree < n) (α β : ℂ) :
    (Polynomial.C α * (Polynomial.X * p) +
      Polynomial.C (Complex.I * β) *
        ((1 - Polynomial.X ^ 2) * q)).natDegree ≤ n + 1 := by
  open Polynomial in
    have hXp : (X * p).natDegree ≤ n + 1 := by
      calc
        (X * p).natDegree ≤ X.natDegree + p.natDegree := natDegree_mul_le
        _ ≤ n + 1 := by rw [natDegree_X]; omega
    have hfirst : (C α * (X * p)).natDegree ≤ n + 1 :=
      le_trans (natDegree_C_mul_le α (X * p)) hXp
    have hsecond :
        (C (Complex.I * β) * ((1 - X ^ 2) * q)).natDegree ≤ n + 1 := by
      rcases hq with rfl | hq
      · simp
      · calc
          (C (Complex.I * β) * ((1 - X ^ 2) * q)).natDegree ≤
              ((1 - X ^ 2) * q).natDegree := natDegree_C_mul_le _ _
          _ ≤ (1 - X ^ 2 : Polynomial ℂ).natDegree + q.natDegree :=
            natDegree_mul_le
          _ ≤ n + 1 := by
            have hbase : (1 - X ^ 2 : Polynomial ℂ).natDegree ≤ 2 := by
              calc
                (1 - X ^ 2 : Polynomial ℂ).natDegree ≤
                    max (1 : Polynomial ℂ).natDegree (X ^ 2).natDegree :=
                  natDegree_sub_le _ _
                _ ≤ 2 := by
                  rw [natDegree_one]
                  have hh :=
                    natDegree_pow_le (p := (X : Polynomial ℂ)) (n := 2)
                  rw [natDegree_X] at hh
                  omega
            omega
    exact le_trans (natDegree_add_le _ _) (max_le hfirst hsecond)

private lemma qspPolyStep_secondDegree (n : ℕ) (p q : Polynomial ℂ)
    (hp : p.natDegree ≤ n) (hq : q = 0 ∨ q.natDegree < n) (α β : ℂ) :
    let q' :=
      Polynomial.C (Complex.I * α) * p +
        Polynomial.C β * (Polynomial.X * q)
    q' = 0 ∨ q'.natDegree < n + 1 := by
  open Polynomial in
    dsimp
    right
    have hfirst : (C (Complex.I * α) * p).natDegree ≤ n :=
      le_trans (natDegree_C_mul_le _ p) hp
    have hsecond : (C β * (X * q)).natDegree ≤ n := by
      rcases hq with rfl | hq
      · simp
      · calc
          (C β * (X * q)).natDegree ≤ (X * q).natDegree :=
            natDegree_C_mul_le _ _
          _ ≤ X.natDegree + q.natDegree := natDegree_mul_le
          _ ≤ n := by rw [natDegree_X]; omega
    have hh := le_trans (natDegree_add_le _ _) (max_le hfirst hsecond)
    omega

private lemma qspTailProduct_polynomials (phases : List ℝ) :
    ∃ p q : Polynomial ℂ,
      p.natDegree ≤ phases.length ∧
      (q = 0 ∨ q.natDegree < phases.length) ∧
      (∀ z : ℂ,
        Polynomial.eval (-z) p =
          (-1 : ℂ) ^ phases.length * Polynomial.eval z p) ∧
      (∀ z : ℂ,
        Polynomial.eval (-z) q =
          (-1 : ℂ) ^ (phases.length + 1) * Polynomial.eval z q) ∧
      ∀ a : ℝ, a ∈ Set.Icc (-1 : ℝ) 1 →
        qspTailProduct phases a 0 0 = Polynomial.eval (a : ℂ) p ∧
        qspTailProduct phases a 1 0 =
          (Real.sqrt (1 - a ^ 2) : ℂ) * Polynomial.eval (a : ℂ) q := by
  open Polynomial in
    induction phases with
    | nil =>
        refine ⟨1, 0, by simp, Or.inl rfl, ?_, ?_, ?_⟩
        · intro z
          simp
        · intro z
          simp
        · intro a ha
          simp [qspTailProduct]
    | cons phase phases ih =>
        rcases ih with ⟨p, q, hpdeg, hqdeg, hppar, hqpar, heval⟩
        let α := Complex.exp (phase * Complex.I)
        let β := Complex.exp (-(phase * Complex.I))
        let p' :=
          C α * (X * p) + C (Complex.I * β) * ((1 - X ^ 2) * q)
        let q' := C (Complex.I * α) * p + C β * (X * q)
        have hp'deg : p'.natDegree ≤ phases.length + 1 := by
          exact
            qspPolyStep_firstDegree phases.length p q hpdeg hqdeg α β
        have hq'deg : q' = 0 ∨ q'.natDegree < phases.length + 1 := by
          exact
            qspPolyStep_secondDegree phases.length p q hpdeg hqdeg α β
        refine ⟨p', q', ?_, ?_, ?_, ?_, ?_⟩
        · simpa using hp'deg
        · simpa using hq'deg
        · intro z
          dsimp [p']
          simp only [eval_add, eval_mul, eval_C, eval_X, eval_one, eval_sub,
            eval_pow]
          rw [hppar, hqpar]
          simp only [pow_succ]
          ring
        · intro z
          dsimp [q']
          simp only [eval_add, eval_mul, eval_C, eval_X]
          rw [hppar, hqpar]
          simp only [pow_succ]
          ring
        · intro a ha
          have htail := heval a ha
          change
            (((qspSignalOperator a * rotZOp phase) *
                qspTailProduct phases a) 0 0 = eval (a : ℂ) p') ∧
              (((qspSignalOperator a * rotZOp phase) *
                qspTailProduct phases a) 1 0 =
                  (Real.sqrt (1 - a ^ 2) : ℂ) * eval (a : ℂ) q')
          constructor
          · rw [show
                (((qspSignalOperator a * rotZOp phase) *
                    qspTailProduct phases a) 0 0) =
                  (a : ℂ) * α * qspTailProduct phases a 0 0 +
                    Complex.I * (Real.sqrt (1 - a ^ 2) : ℂ) * β *
                      qspTailProduct phases a 1 0 by
                simp [α, β, Matrix.mul_apply, qspSignalOperator, rotZOp]]
            rw [htail.1, htail.2]
            simp only [p', eval_add, eval_mul, eval_C, eval_X, eval_one,
              eval_sub, eval_pow]
            rw [show
              (1 : ℂ) - (a : ℂ) ^ 2 =
                  (Real.sqrt (1 - a ^ 2) : ℂ) ^ 2 by
                symm
                exact QAlgBench.sq_sqrt_one_sub_sq ha]
            ring
          · rw [show
                (((qspSignalOperator a * rotZOp phase) *
                    qspTailProduct phases a) 1 0) =
                  Complex.I * (Real.sqrt (1 - a ^ 2) : ℂ) * α *
                      qspTailProduct phases a 0 0 +
                    (a : ℂ) * β * qspTailProduct phases a 1 0 by
                simp [α, β, Matrix.mul_apply, qspSignalOperator, rotZOp]]
            rw [htail.1, htail.2]
            simp only [q', eval_add, eval_mul, eval_C, eval_X]
            ring

/--
On the signal domain, the QSP response is the evaluation of a complex
polynomial of degree at most `k`.
-/
theorem qspResponse_isPolynomial (k : ℕ) (φ : Fin (k + 1) → ℝ) :
    ∃ p : Polynomial ℂ,
      p.natDegree ≤ k ∧
      ∀ a : ℝ, a ∈ Set.Icc (-1 : ℝ) 1 →
        Polynomial.eval (a : ℂ) p = qspResponse k φ a := by
  let phases := List.ofFn (fun j : Fin k => φ j.succ)
  rcases qspTailProduct_polynomials phases with
    ⟨p, q, hpdeg, hqdeg, hppar, hqpar, heval⟩
  let α := Complex.exp (φ 0 * Complex.I)
  refine ⟨Polynomial.C α * p, ?_, ?_⟩
  · calc
      (Polynomial.C α * p).natDegree ≤ p.natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ ≤ k := by simpa [phases] using hpdeg
  · intro a ha
    have hseq :
        qspResponse k φ a = α * qspTailProduct phases a 0 0 := by
      simp [α, phases, qspResponse, qspSequenceOperator, qspTailProduct,
        List.map_ofFn, Function.comp_def, Matrix.mul_apply, rotZOp]
    rw [hseq, (heval a ha).1]
    simp

/-- The response has the parity of the QSP length `k`. -/
theorem qspResponse_parity (k : ℕ) (φ : Fin (k + 1) → ℝ) :
    ∀ a : ℝ, a ∈ Set.Icc (-1 : ℝ) 1 →
      qspResponse k φ (-a) = (-1 : ℂ) ^ k * qspResponse k φ a := by
  let phases := List.ofFn (fun j : Fin k => φ j.succ)
  rcases qspTailProduct_polynomials phases with
    ⟨p, q, hpdeg, hqdeg, hppar, hqpar, heval⟩
  let α := Complex.exp (φ 0 * Complex.I)
  have hseq (x : ℝ) :
      qspResponse k φ x = α * qspTailProduct phases x 0 0 := by
    simp [α, phases, qspResponse, qspSequenceOperator, qspTailProduct,
      List.map_ofFn, Function.comp_def, Matrix.mul_apply, rotZOp]
  intro a ha
  have hna : -a ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · nlinarith [ha.2]
    · nlinarith [ha.1]
  rw [hseq, hseq, (heval (-a) hna).1, (heval a ha).1]
  rw [show ((-a : ℝ) : ℂ) = -(a : ℂ) by norm_cast, hppar]
  simp only [phases, List.length_ofFn]
  ring

/-- The angle `θ = 2 arccos(a)` used in the Fejér-kernel formula. -/
def maximumFejerAngle (a : ℝ) : ℝ :=
  2 * Real.arccos a

/-- The coefficient `(k - |ℓ| + 1) / (k+1)²` for `-k ≤ ℓ ≤ k`. -/
def maximumFejerCoefficient (k : ℕ) (ℓ : ℤ) : ℝ :=
  ((k - ℓ.natAbs + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2)

/--
The weighted Fourier response
`P(a) = ∑_{ℓ=-k}^k (k-|ℓ|+1)/(k+1)² · exp(2 i ℓ arccos(a))`.
-/
def maximumFejerResponse (k : ℕ) (a : ℝ) : ℂ :=
  ∑ ℓ ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
    (maximumFejerCoefficient k ℓ : ℂ) *
      Complex.exp (((ℓ : ℝ) * maximumFejerAngle a) * Complex.I)

/-- The geometric sum `∑_{m=0}^k exp(i m θ)`. -/
def maximumFejerGeometricSum (k : ℕ) (a : ℝ) : ℂ :=
  ∑ m ∈ Finset.range (k + 1),
    Complex.exp (((m : ℝ) * maximumFejerAngle a) * Complex.I)

private lemma card_pairDifference (N : ℕ) (ℓ : ℤ)
    (hℓ : ℓ ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1)) :
    ((Finset.range N ×ˢ Finset.range N).filter
      (fun p : ℕ × ℕ => (p.2 : ℤ) - (p.1 : ℤ) = ℓ)).card =
        N - ℓ.natAbs := by
  rcases ℓ with d | d
  · change
      ((Finset.range N ×ˢ Finset.range N).filter
        (fun p : ℕ × ℕ => (p.2 : ℤ) - (p.1 : ℤ) = (d : ℤ))).card =
          N - d
    symm
    simpa using
      (Finset.card_bij
        (s := Finset.range (N - d))
        (t := (Finset.range N ×ˢ Finset.range N).filter
          (fun p : ℕ × ℕ => (p.2 : ℤ) - (p.1 : ℤ) = (d : ℤ)))
        (fun m _ => (m, m + d))
        (by
          intro m hm
          simp only [Finset.mem_range] at hm
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          constructor
          · omega
          · omega)
        (by
          intro m₁ hm₁ m₂ hm₂ h
          exact congrArg Prod.fst h)
        (by
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
          have heq : p.2 = p.1 + d := by omega
          refine ⟨p.1, ?_, ?_⟩
          · simp only [Finset.mem_range]
            apply Nat.lt_sub_of_add_lt
            omega
          · ext <;> simp [heq]))
  · change
      ((Finset.range N ×ˢ Finset.range N).filter
        (fun p : ℕ × ℕ =>
          (p.2 : ℤ) - (p.1 : ℤ) = Int.negSucc d)).card =
            N - (d + 1)
    symm
    simpa using
      (Finset.card_bij
        (s := Finset.range (N - (d + 1)))
        (t := (Finset.range N ×ˢ Finset.range N).filter
          (fun p : ℕ × ℕ =>
            (p.2 : ℤ) - (p.1 : ℤ) = Int.negSucc d))
        (fun m _ => (m + d + 1, m))
        (by
          intro m hm
          simp only [Finset.mem_range] at hm
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          constructor
          · omega
          · simp only [Int.negSucc_eq]
            push_cast
            ring)
        (by
          intro m₁ hm₁ m₂ hm₂ h
          exact congrArg Prod.snd h)
        (by
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
          simp only [Int.negSucc_eq] at hp
          have heq : p.1 = p.2 + d + 1 := by omega
          refine ⟨p.2, ?_, ?_⟩
          · simp only [Finset.mem_range]
            apply Nat.lt_sub_of_add_lt
            omega
          · ext <;> simp [heq]))

private lemma exp_conj_mul_exp_eq_exp_sub (m n : ℕ) (θ : ℝ) :
    starRingEnd ℂ (Complex.exp (((m : ℝ) * θ) * Complex.I)) *
        Complex.exp (((n : ℝ) * θ) * Complex.I) =
      Complex.exp
        (((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * θ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · push_cast
    simp
  · push_cast
    simp
    ring

private lemma fejerNumerator_eq_normSq (k : ℕ) (θ : ℝ) :
    (∑ ℓ ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
      (((k - ℓ.natAbs + 1 : ℕ) : ℝ) : ℂ) *
        Complex.exp (((ℓ : ℝ) * θ) * Complex.I)) =
      ((Complex.normSq
        (∑ m ∈ Finset.range (k + 1),
          Complex.exp (((m : ℝ) * θ) * Complex.I)) : ℝ) : ℂ) := by
  let s := Finset.range (k + 1) ×ˢ Finset.range (k + 1)
  let t := Finset.Icc (-(k : ℤ)) (k : ℤ)
  let d : ℕ × ℕ → ℤ := fun p => (p.2 : ℤ) - (p.1 : ℤ)
  have hd : ∀ p ∈ s, d p ∈ t := by
    intro p hp
    simp only [s, Finset.mem_product, Finset.mem_range] at hp
    simp only [d, t, Finset.mem_Icc]
    constructor <;> omega
  have hcard :
      ∀ ℓ ∈ t, (s.filter fun p => d p = ℓ).card =
        k - ℓ.natAbs + 1 := by
    intro ℓ hℓ
    have hℓ' :
        ℓ ∈ Finset.Icc (-((k + 1 : ℕ) : ℤ) + 1)
          (((k + 1 : ℕ) : ℤ) - 1) := by
      simpa [t] using hℓ
    rw [card_pairDifference (k + 1) ℓ hℓ']
    have habs : ℓ.natAbs ≤ k := by
      simp only [t, Finset.mem_Icc] at hℓ
      rcases ℓ with e | e
      · change e ≤ k
        exact Int.ofNat_le.mp hℓ.2
      · change e + 1 ≤ k
        apply Int.ofNat_le.mp
        simp only [Int.negSucc_eq] at hℓ
        push_cast
        omega
    omega
  calc
    _ = ∑ ℓ ∈ t, ∑ p ∈ s with d p = ℓ,
          Complex.exp (((ℓ : ℝ) * θ) * Complex.I) := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      rw [Finset.sum_const, nsmul_eq_mul, hcard ℓ hℓ]
      push_cast
      rfl
    _ = ∑ p ∈ s,
          Complex.exp ((((d p : ℤ) : ℝ) * θ) * Complex.I) :=
      Finset.sum_fiberwise_of_maps_to' hd _
    _ = starRingEnd ℂ
          (∑ m ∈ Finset.range (k + 1),
            Complex.exp (((m : ℝ) * θ) * Complex.I)) *
        (∑ n ∈ Finset.range (k + 1),
          Complex.exp (((n : ℝ) * θ) * Complex.I)) := by
      rw [map_sum, Finset.sum_mul_sum]
      simp only [s, Finset.sum_product, d]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact (exp_conj_mul_exp_eq_exp_sub m n θ).symm
    _ = ((Complex.normSq
        (∑ m ∈ Finset.range (k + 1),
          Complex.exp (((m : ℝ) * θ) * Complex.I)) : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]

/--
The weighted Fourier response is the normalized squared modulus of the
geometric sum.
-/
theorem maximumFejerResponse_eq_normSq (k : ℕ) :
    ∀ a : ℝ, a ∈ Set.Icc (-1 : ℝ) 1 →
      maximumFejerResponse k a =
        ((Complex.normSq (maximumFejerGeometricSum k a) /
          (((k + 1 : ℕ) : ℝ) ^ 2) : ℝ) : ℂ) := by
  intro a ha
  simp only [maximumFejerResponse, maximumFejerCoefficient,
    maximumFejerGeometricSum, Complex.ofReal_div, Complex.ofReal_pow]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  rw [fejerNumerator_eq_normSq]

/--
For every signal value, `P(a)` is a real number in the closed unit interval.
The real witness makes the source's inequalities meaningful for the
complex-valued Fourier sum.
-/
theorem maximumFejerResponse_mem_unitInterval (k : ℕ) :
    ∀ a : ℝ, a ∈ Set.Icc (-1 : ℝ) 1 →
      ∃ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 ∧
        maximumFejerResponse k a = (r : ℂ) := by
  intro a ha
  let r :=
    Complex.normSq (maximumFejerGeometricSum k a) /
      (((k + 1 : ℕ) : ℝ) ^ 2)
  refine ⟨r, ?_, ?_⟩
  · constructor
    · exact div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)
    · have hexp (m : ℕ) :
          ‖Complex.exp (((m : ℝ) * maximumFejerAngle a) * Complex.I)‖ =
            1 := by
        convert
          Complex.norm_exp_ofReal_mul_I
            ((m : ℝ) * maximumFejerAngle a) using 1
        congr 3
        norm_cast
      have hnorm :
          ‖maximumFejerGeometricSum k a‖ ≤ ((k + 1 : ℕ) : ℝ) := by
        calc
          ‖maximumFejerGeometricSum k a‖ ≤
              ∑ m ∈ Finset.range (k + 1),
                ‖Complex.exp
                  (((m : ℝ) * maximumFejerAngle a) * Complex.I)‖ := by
            exact norm_sum_le _ _
          _ = ((k + 1 : ℕ) : ℝ) := by
            simp_rw [hexp]
            simp
      dsimp [r]
      rw [div_le_one (by positivity), Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (maximumFejerGeometricSum k a)]
  · exact maximumFejerResponse_eq_normSq k a ha

/-- At the endpoint `a = 1`, the normalized Fejér response equals one. -/
theorem maximumFejerResponse_one (k : ℕ) :
    maximumFejerResponse k 1 = 1 := by
  rw [maximumFejerResponse_eq_normSq k 1 (by constructor <;> norm_num)]
  simp [maximumFejerGeometricSum, maximumFejerAngle, Complex.normSq]
  norm_cast
  field_simp
  simp [pow_two]

end

end QAlgFormalized.QSPParameterTrace.ParityMaximumFejerKernelQSPResponse
