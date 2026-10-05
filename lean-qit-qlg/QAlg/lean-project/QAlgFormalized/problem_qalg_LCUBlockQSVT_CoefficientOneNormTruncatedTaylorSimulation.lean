import QAlgBench.Base

/-!
# Coefficient one-norm for truncated-Taylor Hamiltonian simulation

This file formalizes the LCU expansion of the order-`K` Taylor polynomial for a
positive Pauli decomposition of a finite-dimensional Hamiltonian.  A tuple in
`J^k` is represented by a function `Fin k → J`.
-/

open scoped BigOperators

namespace QAlgFormalized.CoefficientOneNormTruncatedTaylorSimulation

open QAlgBench

/-- The four phase-free one-qubit Pauli operators. -/
inductive SingleQubitPauli where
  | I
  | X
  | Y
  | Z
  deriving DecidableEq

namespace SingleQubitPauli

/-- Interpret a one-qubit Pauli symbol as a unitary gate from `QAlgBench`. -/
noncomputable def toGate : SingleQubitPauli → Gate (Qubits 1)
  | .I => 1
  | .X => Gate.X
  | .Y => Gate.Y
  | .Z => Gate.Z

end SingleQubitPauli

/-- An `n`-qubit Pauli string, with no global phase. -/
abbrev PauliString (n : ℕ) := Fin n → SingleQubitPauli

namespace PauliString

/-- Interpret a Pauli string as the tensor product of its one-qubit factors. -/
noncomputable def toGate : (n : ℕ) → PauliString n → Gate (Qubits n)
  | 0, _ => 1
  | n + 1, p =>
      (toGate n (fun i => p i.castSucc)).tensor
        (SingleQubitPauli.toGate (p (Fin.last n)))

end PauliString

/-- A bundled unitary is a Pauli unitary when it is the gate of a Pauli string. -/
def IsPauliUnitary {n : ℕ} (P : Gate (Qubits n)) : Prop :=
  ∃ p : PauliString n, PauliString.toGate n p = P

/-- The operator `H = ∑ j, β j • P j` associated with a finite Pauli
decomposition.  The coefficients are embedded from `ℝ` into `ℂ`. -/
noncomputable def hamiltonian {J : Type} [Fintype J] {n : ℕ}
    (β : J → ℝ) (P : J → Gate (Qubits n)) : HilbertOperator (Qubits n) :=
  ∑ j, (β j : ℂ) • (P j : HilbertOperator (Qubits n))

/-- The order-`K` Taylor polynomial
`∑_{k=0}^K ((-i t)^k / k!) H^k` for `exp (-i H t)`. -/
noncomputable def truncatedTaylor {n : ℕ} (H : HilbertOperator (Qubits n))
    (t : ℝ) (K : ℕ) : HilbertOperator (Qubits n) :=
  ∑ k : Fin (K + 1),
    (((-Complex.I * (t : ℂ)) ^ (k : ℕ)) / (Nat.factorial (k : ℕ) : ℂ)) •
      H ^ (k : ℕ)

/-- The positive real coefficient attached to a tuple
`js = (j₁, ..., jₖ)` in the truncated-Taylor LCU. -/
noncomputable def taylorLCUCoefficient {J : Type} (t : ℝ) (β : J → ℝ)
    {k : ℕ} (js : Fin k → J) : ℝ :=
  t ^ k * (∏ i, β (js i)) / (Nat.factorial k : ℝ)

/-- The coefficient one-norm of the complete order-`K` truncated-Taylor LCU. -/
noncomputable def taylorCoefficientOneNorm {J : Type} [Fintype J]
    (t : ℝ) (β : J → ℝ) (K : ℕ) : ℝ :=
  ∑ k : Fin (K + 1),
    ∑ js : Fin (k : ℕ) → J, taylorLCUCoefficient t β js

/-- The Taylor polynomial has the stated LCU representation.  The phase
`(-i)^k` is absorbed into `P'`; its codomain `Gate` records that every resulting
operator is unitary. -/
theorem truncatedTaylor_has_lcu {J : Type} [Fintype J] {n : ℕ}
    (β : J → ℝ) (hβ : ∀ j, 0 < β j)
    (P : J → Gate (Qubits n)) (hP : ∀ j, IsPauliUnitary (P j))
    (t : ℝ) (ht : 0 ≤ t) (K : ℕ) :
    ∃ P' : (k : Fin (K + 1)) → (Fin (k : ℕ) → J) → Gate (Qubits n),
      (∀ (k : Fin (K + 1)) (js : Fin (k : ℕ) → J),
        0 ≤ taylorLCUCoefficient t β js) ∧
      (∀ (k : Fin (K + 1)) (js : Fin (k : ℕ) → J),
        (P' k js : HilbertOperator (Qubits n)) =
          ((-Complex.I) ^ (k : ℕ)) •
            ((((List.ofFn js).map P).prod : Gate (Qubits n)) :
              HilbertOperator (Qubits n))) ∧
      truncatedTaylor (hamiltonian β P) t K =
        ∑ k : Fin (K + 1),
          ∑ js : Fin (k : ℕ) → J,
            (taylorLCUCoefficient t β js : ℂ) •
              (P' k js : HilbertOperator (Qubits n)) := by
  classical
  have phase_unitary (k : ℕ) (G : Gate (Qubits n)) :
      ((-Complex.I : ℂ) ^ k) • (G : HilbertOperator (Qubits n)) ∈
        Matrix.unitaryGroup (Qubits n).Index ℂ := by
    have hphase :
        ((-Complex.I : ℂ) ^ k) * star ((-Complex.I : ℂ) ^ k) = 1 := by
      rw [star_pow, star_neg]
      rw [show star (Complex.I : ℂ) = -Complex.I by norm_num]
      rw [neg_neg, ← mul_pow]
      norm_num
    rw [Matrix.mem_unitaryGroup_iff, star_smul, smul_mul_smul_comm,
      Matrix.mem_unitaryGroup_iff.mp G.unitary, hphase]
    simp
  let P' : (k : Fin (K + 1)) → (Fin (k : ℕ) → J) → Gate (Qubits n) :=
    fun k js =>
      Gate.ofUnitary
        (((-Complex.I : ℂ) ^ (k : ℕ)) •
          ((((List.ofFn js).map P).prod : Gate (Qubits n)) :
            HilbertOperator (Qubits n)))
        (phase_unitary (k : ℕ) ((List.ofFn js).map P).prod)
  refine ⟨P', ?_, ?_, ?_⟩
  · intro k js
    unfold taylorLCUCoefficient
    exact div_nonneg
      (mul_nonneg (pow_nonneg ht _) (Finset.prod_nonneg fun i _ => (hβ (js i)).le))
      (Nat.cast_nonneg _)
  · intro k js
    rfl
  · have hpow (k : ℕ) :
        (hamiltonian β P) ^ k =
          ∑ js : Fin k → J,
            (∏ i, (β (js i) : ℂ)) •
              ((((List.ofFn js).map P).prod : Gate (Qubits n)) :
                HilbertOperator (Qubits n)) := by
      induction k with
      | zero =>
          simp [hamiltonian]
      | succ k ih =>
          rw [pow_succ', ih]
          simp only [hamiltonian, Finset.mul_sum, Finset.sum_mul]
          let e : (Fin (k + 1) → J) ≃ J × (Fin k → J) :=
            (Equiv.arrowCongr (finSuccEquiv k) (Equiv.refl J)).trans
              Equiv.piOptionEquivProd
          rw [Fintype.sum_equiv e
            (fun js : Fin (k + 1) → J =>
              (∏ i, (β (js i) : ℂ)) •
                ((((List.ofFn js).map P).prod : Gate (Qubits n)) :
                  HilbertOperator (Qubits n)))
            (fun pair : J × (Fin k → J) =>
              (β pair.1 : ℂ) • (P pair.1 : HilbertOperator (Qubits n)) *
                ((∏ i, (β (pair.2 i) : ℂ)) •
                  ((((List.ofFn pair.2).map P).prod : Gate (Qubits n)) :
                    HilbertOperator (Qubits n))))]
          · rw [Fintype.sum_prod_type]
            rw [Finset.sum_comm]
          · intro js
            rw [List.ofFn_succ]
            simp only [List.map_cons, List.prod_cons, Gate.coe_mul]
            rw [Fin.prod_univ_succ, smul_mul_smul_comm]
            simp [e, Equiv.arrowCongr]
    unfold truncatedTaylor
    apply Finset.sum_congr rfl
    intro k _
    rw [hpow (k : ℕ), Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro js _
    change
      (((-Complex.I * (t : ℂ)) ^ (k : ℕ)) /
            (Nat.factorial (k : ℕ) : ℂ)) •
          ((∏ i, (β (js i) : ℂ)) •
            ((((List.ofFn js).map P).prod : Gate (Qubits n)) :
              HilbertOperator (Qubits n))) =
        (taylorLCUCoefficient t β js : ℂ) •
          (((-Complex.I : ℂ) ^ (k : ℕ)) •
            ((((List.ofFn js).map P).prod : Gate (Qubits n)) :
              HilbertOperator (Qubits n)))
    rw [smul_smul, smul_smul]
    congr 1
    unfold taylorLCUCoefficient
    push_cast
    ring

/-- The coefficient one-norm is bounded by the full exponential series:
`∑_{k=0}^K ∑_{js : J^k} α_js ≤ exp (t ∑ j, β j)`. -/
theorem taylorCoefficientOneNorm_le_exp {J : Type} [Fintype J]
    (β : J → ℝ) (hβ : ∀ j, 0 < β j)
    (t : ℝ) (ht : 0 ≤ t) (K : ℕ) :
    taylorCoefficientOneNorm t β K ≤ Real.exp (t * ∑ j, β j) := by
  classical
  unfold taylorCoefficientOneNorm taylorLCUCoefficient
  calc
    (∑ k : Fin (K + 1),
        ∑ js : Fin (k : ℕ) → J,
          t ^ (k : ℕ) * (∏ i, β (js i)) /
            (Nat.factorial (k : ℕ) : ℝ)) =
        ∑ k : Fin (K + 1),
          (t * ∑ j, β j) ^ (k : ℕ) /
            (Nat.factorial (k : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_div, ← Finset.mul_sum, ← Fintype.sum_pow, mul_pow]
    _ ≤ Real.exp (t * ∑ j, β j) := by
      change
        (∑ k : Fin (K + 1),
          (fun i : ℕ =>
            (t * ∑ j, β j) ^ i / (Nat.factorial i : ℝ)) (k : ℕ)) ≤
          Real.exp (t * ∑ j, β j)
      calc
        _ = ∑ i ∈ Finset.range (K + 1),
              (t * ∑ j, β j) ^ i / (Nat.factorial i : ℝ) :=
          Fin.sum_univ_eq_sum_range
            (fun i : ℕ =>
              (t * ∑ j, β j) ^ i / (Nat.factorial i : ℝ)) (K + 1)
        _ ≤ Real.exp (t * ∑ j, β j) :=
          Real.sum_le_exp_of_nonneg
            (mul_nonneg ht (Finset.sum_nonneg fun j _ => (hβ j).le)) (K + 1)

/-- The canonical number of raw-LCU segments obtained by splitting evolution
into intervals of coefficient-one-norm time at most one.  The maximum makes the
definition total for arbitrary real time; at physical times `t ≥ 0` it is just
`⌈t ∑ j, β j⌉₊`. -/
noncomputable def rawLCUSegmentCount {J : Type} [Fintype J]
    (β : J → ℝ) (t : ℝ) : ℕ :=
  Nat.ceil (max 0 (t * ∑ j, β j))

/-- The raw-LCU segment count is `O(t ∑ j, β j)` as time tends to infinity. -/
theorem rawLCUSegmentCount_isBigO {J : Type} [Fintype J]
    (β : J → ℝ) (hβ : ∀ j, 0 < β j) :
    Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ => (rawLCUSegmentCount β t : ℝ))
      (fun t : ℝ => t * ∑ j, β j) := by
  classical
  let s : ℝ := ∑ j, β j
  have hs_nonneg : 0 ≤ s := Finset.sum_nonneg fun j _ => (hβ j).le
  by_cases hs_zero : s = 0
  · refine Asymptotics.IsBigO.of_bound 0 (Filter.Eventually.of_forall ?_)
    intro t
    simp [rawLCUSegmentCount, s, hs_zero]
  · have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg (Ne.symm hs_zero)
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [Filter.eventually_ge_atTop (1 / s)] with t ht
    have ht_nonneg : 0 ≤ t :=
      (div_nonneg zero_le_one hs_nonneg).trans ht
    have hts_nonneg : 0 ≤ t * s := mul_nonneg ht_nonneg hs_nonneg
    have hone_le : 1 ≤ t * s := by
      calc
        1 = (1 / s) * s := by field_simp
        _ ≤ t * s := mul_le_mul_of_nonneg_right ht hs_nonneg
    have hceil : (Nat.ceil (t * s) : ℝ) ≤ t * s + 1 :=
      (Nat.ceil_lt_add_one hts_nonneg).le
    change ‖(Nat.ceil (max 0 (t * s)) : ℝ)‖ ≤ 2 * ‖t * s‖
    rw [max_eq_right hts_nonneg]
    simp only [Real.norm_eq_abs, abs_of_nonneg hts_nonneg]
    rw [abs_of_nonneg (show 0 ≤ (Nat.ceil (t * s) : ℝ) by positivity)]
    linarith

end QAlgFormalized.CoefficientOneNormTruncatedTaylorSimulation
