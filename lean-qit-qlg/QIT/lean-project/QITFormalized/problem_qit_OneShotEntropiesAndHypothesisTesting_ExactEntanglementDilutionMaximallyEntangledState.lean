import QITBench.Base.OneShot

/-!
# Exact entanglement dilution to a maximally entangled state

This file formalizes the exact deterministic-LOCC conversion criterion for a
pure bipartite state whose Schmidt coefficients are given in descending order.
-/

namespace QITFormalized

open QITBench QITBench.OneShot

/-- Let `eta` be a normalized bipartite pure state on its `d`-dimensional
Schmidt support, with descending, strictly positive Schmidt coefficients `mu`.
For positive `M`, its exact deterministic conversion by LOCC to the standard
rank-`M` maximally entangled state `maximallyEntangledVector M` is possible
exactly when the largest Schmidt coefficient is at most `1 / M`.

The predicate `CanTransformDeterministicallyByLOCC` is the benchmark Base
encoding of Nielsen's majorization criterion. Its target Schmidt vector is
`maximallyEntangledSchmidtCoefficients M`, the ambiently padded coefficient
vector of `maximallyEntangledVector M`. -/
theorem exactEntanglementDilutionMaximallyEntangledState
    {d M : ℕ}
    (hd : 0 < d)
    (hM : 0 < M)
    (eta : PureVector (Fin d × Fin d))
    (mu : Fin d → ℝ)
    (heta : HasSchmidtCoefficients eta mu)
    (hmu : IsSchmidtProbabilityVector mu) :
    CanTransformDeterministicallyByLOCC mu M ↔
      largestSchmidtCoefficient mu hd ≤ (1 : ℝ) / (M : ℝ) := by
  have hle_top : ∀ i : Fin d, mu i ≤ largestSchmidtCoefficient mu hd := by
    intro i
    exact hmu.1 ⟨0, hd⟩ i (Nat.zero_le _)
  have hsumFirstOneMu : sumFirst 1 mu = largestSchmidtCoefficient mu hd := by
    unfold sumFirst largestSchmidtCoefficient
    cases d with
    | zero => omega
    | succ d =>
      rw [Fin.sum_univ_succ]
      simp
  have hsumFirstOneTarget :
      sumFirst 1 (maximallyEntangledSchmidtCoefficients (d := d) M) =
        (1 : ℝ) / (M : ℝ) := by
    unfold sumFirst maximallyEntangledSchmidtCoefficients
    cases d with
    | zero => omega
    | succ d =>
      rw [Fin.sum_univ_succ]
      simp [hM]
  constructor
  · intro h
    rcases h with ⟨_, _, _, hmajorized⟩
    have hone := hmajorized.1 1 (by omega)
    simpa [hsumFirstOneMu, hsumFirstOneTarget] using hone
  · intro htop
    have hMd : M ≤ d := by
      by_contra hnot
      have hdM : d < M := Nat.lt_of_not_ge hnot
      have hsum_le : (∑ i, mu i) ≤ ∑ _i : Fin d, (1 : ℝ) / (M : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hle_top i).trans htop
      have hMreal : (0 : ℝ) < (M : ℝ) := by
        exact_mod_cast hM
      have hdMreal : (d : ℝ) < (M : ℝ) := by
        exact_mod_cast hdM
      have hconst : (∑ _i : Fin d, (1 : ℝ) / (M : ℝ)) =
          (d : ℝ) / (M : ℝ) := by
        simp [div_eq_mul_inv]
      rw [hmu.2.2, hconst] at hsum_le
      have hlt : (d : ℝ) / (M : ℝ) < 1 :=
        (div_lt_one hMreal).mpr hdMreal
      linarith
    have hqsum :
        (∑ i : Fin d, maximallyEntangledSchmidtCoefficients (d := d) M i) = 1 := by
      unfold maximallyEntangledSchmidtCoefficients
      rw [Fin.sum_univ_eq_sum_range
        (fun n : ℕ => if n < M then (1 : ℝ) / (M : ℝ) else 0) d]
      rw [← Finset.sum_filter]
      have hf : (Finset.range d).filter (fun n => n < M) = Finset.range M := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [hf]
      simp [hM.ne']
    refine ⟨hmu, hM, hMd, ?_⟩
    refine ⟨?_, ?_⟩
    · intro k hk
      by_cases hkM : k ≤ M
      · unfold sumFirst
        apply Finset.sum_le_sum
        intro i hi
        by_cases hik : (i : ℕ) < k
        · have hiM : (i : ℕ) < M := lt_of_lt_of_le hik hkM
          simp only [hik, if_true, maximallyEntangledSchmidtCoefficients, hiM]
          exact (hle_top i).trans htop
        · simp [hik]
      · have hMk : M ≤ k := by omega
        calc
          sumFirst k mu ≤ ∑ i, mu i := by
            unfold sumFirst
            apply Finset.sum_le_sum
            intro i hi
            by_cases hik : (i : ℕ) < k
            · simp [hik]
            · simp [hik, le_of_lt (hmu.2.1 i)]
          _ = 1 := hmu.2.2
          _ = sumFirst k (maximallyEntangledSchmidtCoefficients (d := d) M) := by
            symm
            calc
              sumFirst k (maximallyEntangledSchmidtCoefficients (d := d) M) =
                  ∑ i : Fin d,
                    maximallyEntangledSchmidtCoefficients (d := d) M i := by
                unfold sumFirst
                apply Finset.sum_congr rfl
                intro i hi
                by_cases hiM : (i : ℕ) < M
                · have hik : (i : ℕ) < k := lt_of_lt_of_le hiM hMk
                  simp [maximallyEntangledSchmidtCoefficients, hiM, hik]
                · simp [maximallyEntangledSchmidtCoefficients, hiM]
              _ = 1 := hqsum
    · rw [hmu.2.2, hqsum]

end QITFormalized
