import Mathlib
set_option backward.isDefEq.respectTransparency false

/-- The predicate stating that `a : ℕ → ℕ` (0-indexed) is a sequence satisfying Definition 1:
each term exceeds `1`, and each subsequent term is the smallest integer strictly larger than the
previous one that shares a common factor with every earlier term. -/
def IsValidSeq (a : ℕ → ℕ) : Prop :=
  (∀ n, 1 < a n) ∧
  (∀ n, a n < a (n + 1) ∧
        (∀ i ≤ n, 1 < Nat.gcd (a (n + 1)) (a i)) ∧
        (∀ b, a n < b → b < a (n + 1) → ∃ i ≤ n, Nat.gcd b (a i) = 1))

/-- For any sequence satisfying Definition 1, there exist positive integers `T` and `L` such that
`a (n + T) = a n + L` for every `n`. Equivalently, the sequence of consecutive differences is
purely periodic. -/
theorem main_theorem (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  let IsCore : ℕ → Prop := fun n =>
    ∀ i < n, ¬(a i).primeFactors ⊆ (a n).primeFactors
  have valid_not_coprime (i j : ℕ) : ¬Nat.Coprime (a i) (a j) := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (i.zero_le.trans_lt hij))
      have hi : i ≤ k := Nat.lt_succ_iff.mp hij
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
      exact ne_of_gt ((ha.2 k).2.1 i hi)
    · rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_self]
      exact ne_of_gt (ha.1 i)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (j.zero_le.trans_lt hji))
      have hj : j ≤ k := Nat.lt_succ_iff.mp hji
      rw [Nat.coprime_iff_gcd_eq_one]
      exact ne_of_gt ((ha.2 k).2.1 j hj)
  have not_coprime_of_primeFactors_subset {b x y : ℕ}
      (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x.primeFactors ⊆ y.primeFactors)
      (h : ¬Nat.Coprime b x) : ¬Nat.Coprime b y := by
    obtain ⟨p, hp, hpb, hpx⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    apply Nat.Prime.not_coprime_iff_dvd.mpr
    refine ⟨p, hp, hpb, ?_⟩
    exact Nat.dvd_of_mem_primeFactors (hxy (hp.mem_primeFactors hpx hx))
  have exists_core_le (n : ℕ) :
      ∃ i ≤ n, IsCore i ∧ (a i).primeFactors ⊆ (a n).primeFactors := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hn : IsCore n
        · exact ⟨n, le_rfl, hn, Finset.Subset.rfl⟩
        · simp only [IsCore, not_forall, not_not] at hn
          obtain ⟨i, hin, hsub⟩ := hn
          obtain ⟨j, hji, hjcore, hjsub⟩ := ih i hin
          exact ⟨j, hji.trans hin.le, hjcore, hjsub.trans hsub⟩
  have skipped_has_coprime {n b : ℕ}
      (hab : a 0 ≤ b) (hbn : b < a n) (hneq : ∀ i < n, a i ≠ b) :
      ∃ i < n, Nat.Coprime b (a i) := by
    let m := Nat.find (show ∃ m, b < a m from ⟨n, hbn⟩)
    have hbm : b < a m := Nat.find_spec (show ∃ m, b < a m from ⟨n, hbn⟩)
    have hmn : m ≤ n := Nat.find_min' (show ∃ m, b < a m from ⟨n, hbn⟩) hbn
    have hm0 : m ≠ 0 := by
      intro hm
      have : b < a 0 := by simpa only [hm] using hbm
      exact (not_lt_of_ge hab) this
    obtain ⟨k, hmk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hkb : a k ≤ b := by
      exact le_of_not_gt
        (Nat.find_min (show ∃ m, b < a m from ⟨n, hbn⟩) (by omega))
    have hkn : k < n := by omega
    have hakb : a k < b := lt_of_le_of_ne hkb (hneq k hkn)
    have hbnext : b < a (k + 1) := by simpa only [hmk] using hbm
    obtain ⟨i, hik, hi⟩ := (ha.2 k).2.2 b hakb hbnext
    exact ⟨i, lt_of_le_of_lt hik hkn, by simpa [Nat.coprime_iff_gcd_eq_one] using hi⟩
  have erase_primeFactors_representative {A x q : ℕ} (hA : 1 < A) (hx : 1 < x)
      (hq : q ∈ x.primeFactors) (hAx : ¬Nat.Coprime A x)
      (hlarge : A ^ (A + 2) < ∏ p ∈ x.primeFactors, p) :
      ∃ b, A ≤ b ∧ b < ∏ p ∈ x.primeFactors, p ∧
        b.primeFactors = x.primeFactors.erase q := by
    let D := ∏ p ∈ x.primeFactors.erase q, p
    let R := ∏ p ∈ x.primeFactors, p
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hDpf : D.primeFactors = x.primeFactors.erase q := by
      apply Nat.primeFactors_prod
      intro p hp
      exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    have hqD : q * D = R := by
      simpa [D, R] using Finset.mul_prod_erase x.primeFactors (fun p => p) hq
    have hDpos : 0 < D := by
      exact Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    have hD1 : D ≠ 1 := by
      intro hDone
      obtain ⟨p, hp, hpA, hpx⟩ := Nat.Prime.not_coprime_iff_dvd.mp hAx
      have hps : p ∈ x.primeFactors :=
        hp.mem_primeFactors hpx (ne_of_gt (Nat.zero_lt_of_lt hx))
      have hpq : p = q := by
        by_contra hpq
        have : p ∈ D.primeFactors := by
          rw [hDpf]
          exact Finset.mem_erase.mpr ⟨hpq, hps⟩
        simp [hDone] at this
      subst p
      have hqA : q ≤ A := Nat.le_of_dvd (Nat.zero_lt_of_lt hA) hpA
      have hAB : A ≤ A ^ (A + 2) := by
        exact Nat.le_of_dvd (Nat.pow_pos (Nat.zero_lt_of_lt hA)) (dvd_pow_self A (by omega))
      rw [hDone, mul_one] at hqD
      omega
    by_cases hDA : A ≤ D
    · refine ⟨D, hDA, ?_, hDpf⟩
      change D < R
      calc
        D < q * D := lt_mul_of_one_lt_left hDpos hqprime.one_lt
        _ = R := hqD
    · have hDlt : D < A := lt_of_not_ge hDA
      have hqbig : A ^ A < q := by
        by_contra hqsmall
        have hqsmall' : q ≤ A ^ A := le_of_not_gt hqsmall
        have hmul : q * D < A ^ A * A :=
          (Nat.mul_le_mul_right D hqsmall').trans_lt
            ((Nat.mul_lt_mul_left (Nat.pow_pos (Nat.zero_lt_of_lt hA))).2 hDlt)
        have hpow : A ^ A * A = A ^ (A + 1) := by rw [Nat.pow_succ]
        have hmono : A ^ (A + 1) ≤ A ^ (A + 2) :=
          pow_le_pow_right' hA.le (by omega)
        rw [hqD, hpow] at hmul
        omega
      refine ⟨D ^ A, ?_, ?_, ?_⟩
      · exact (Nat.le_mul_of_pos_left A hDpos).trans (Nat.mul_le_pow hD1 A)
      · have hpowlt : D ^ A < A ^ A :=
          Nat.pow_lt_pow_left hDlt (ne_of_gt (Nat.zero_lt_of_lt hA))
        calc
          D ^ A < q := hpowlt.trans hqbig
          _ ≤ q * D := Nat.le_mul_of_pos_right q hDpos
          _ = R := hqD
      · exact (Nat.primeFactors_pow D (ne_of_gt (Nat.zero_lt_of_lt hA))).trans hDpf
  have core_prime_le (n : ℕ) (hncore : IsCore n) {q : ℕ}
      (hq : q ∈ (a n).primeFactors) : q ≤ (a 0) ^ (a 0 + 2) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        let R := ∏ p ∈ (a n).primeFactors, p
        have hRpos : 0 < R := by
          exact Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors hp
        by_cases hR : R ≤ (a 0) ^ (a 0 + 2)
        · have hqR : q ∣ R := Finset.dvd_prod_of_mem (fun p => p) hq
          exact (Nat.le_of_dvd hRpos hqR).trans hR
        · have hRlarge : (a 0) ^ (a 0 + 2) < R := lt_of_not_ge hR
          have hpair : ¬Nat.Coprime (a 0) (a n) := valid_not_coprime 0 n
          obtain ⟨b, hab, hbR, hbpf⟩ :=
            erase_primeFactors_representative (ha.1 0) (ha.1 n) hq hpair hRlarge
          have hRdvd : R ∣ a n := by simpa [R] using Nat.prod_primeFactors_dvd (a n)
          have hRle : R ≤ a n := Nat.le_of_dvd (Nat.zero_lt_of_lt (ha.1 n)) hRdvd
          have hbne : ∀ i < n, a i ≠ b := by
            intro i hi hib
            apply hncore i hi
            rw [hib, hbpf]
            exact Finset.erase_subset q (a n).primeFactors
          obtain ⟨k, hkn, hkcop⟩ := skipped_has_coprime hab (hbR.trans_le hRle) hbne
          obtain ⟨j, hjk, hjcore, hjsub⟩ := exists_core_le k
          have hjn : j < n := hjk.trans_lt hkn
          have hjpair : ¬Nat.Coprime (a j) (a n) := valid_not_coprime j n
          obtain ⟨p, hp, hpj, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hjpair
          have hpjmem : p ∈ (a j).primeFactors :=
            hp.mem_primeFactors hpj (ne_of_gt (Nat.zero_lt_of_lt (ha.1 j)))
          have hpnmem : p ∈ (a n).primeFactors :=
            hp.mem_primeFactors hpn (ne_of_gt (Nat.zero_lt_of_lt (ha.1 n)))
          have hpq : p = q := by
            by_contra hpq
            have hpbmem : p ∈ b.primeFactors := by
              rw [hbpf]
              exact Finset.mem_erase.mpr ⟨hpq, hpnmem⟩
            have hpkmem : p ∈ (a k).primeFactors := hjsub hpjmem
            exact (Nat.Prime.not_coprime_iff_dvd.mpr
              ⟨p, hp, Nat.dvd_of_mem_primeFactors hpbmem,
                Nat.dvd_of_mem_primeFactors hpkmem⟩) hkcop
          subst p
          exact ih j hjn hjcore hpjmem
  have finite_core : {n : ℕ | IsCore n}.Finite := by
    let B := (a 0) ^ (a 0 + 2)
    let f : ℕ → Set ℕ := fun n => (a n).primeFactors
    apply Set.Finite.of_finite_image (f := f)
    · apply (Set.finite_Iic B).powerset.subset
      rintro s ⟨n, hn, rfl⟩
      intro q hq
      exact core_prime_le n hn hq
    · intro n hn m hm hnm
      have hpf : (a n).primeFactors = (a m).primeFactors := Finset.coe_injective hnm
      rcases lt_trichotomy n m with hlt | heq | hgt
      · exact False.elim (hm n hlt (by rw [hpf]))
      · exact heq
      · exact False.elim (hn m hgt (by rw [hpf]))
  have valid_index_lt (n : ℕ) : n < a n := by
    induction n with
    | zero => exact Nat.zero_lt_of_lt (ha.1 0)
    | succ n ih => exact (Nat.succ_le_of_lt ih).trans_lt (ha.2 n).1
  have compatible_all_of_core {b : ℕ}
      (hb : ∀ i, IsCore i → ¬Nat.Coprime b (a i)) :
      ∀ n, ¬Nat.Coprime b (a n) := by
    intro n
    obtain ⟨i, hin, hicore, hisub⟩ := exists_core_le n
    exact not_coprime_of_primeFactors_subset
      (ne_of_gt (Nat.zero_lt_of_lt (ha.1 i)))
      (ne_of_gt (Nat.zero_lt_of_lt (ha.1 n))) hisub (hb i hicore)
  have compatible_mem_range {b : ℕ}
      (hab : a 0 ≤ b) (hb : ∀ i, ¬Nat.Coprime b (a i)) : ∃ n, a n = b := by
    by_contra hnot
    have hba : b < a (b + 1) := (Nat.lt_succ_self b).trans (valid_index_lt (b + 1))
    obtain ⟨i, hi, hicop⟩ := skipped_has_coprime hab hba (by
      intro i hi hai
      exact hnot ⟨i, hai⟩)
    exact hb i hicop
  let C : Finset ℕ := finite_core.toFinset
  let L : ℕ := ∏ i ∈ C, a i
  let Good : ℕ → Prop := fun b => ∀ i, IsCore i → ¬Nat.Coprime b (a i)
  have hmemC (i : ℕ) : i ∈ C ↔ IsCore i := by simp [C]
  have hLpos : 0 < L := by
    dsimp [L]
    exact Finset.prod_pos fun i hi => Nat.zero_lt_of_lt (ha.1 i)
  have hdvd (i : ℕ) (hi : IsCore i) : a i ∣ L := by
    dsimp [L]
    exact Finset.dvd_prod_of_mem (fun j => a j) ((hmemC i).2 hi)
  have hgood_term (n : ℕ) : Good (a n) := by
    intro i hi
    exact valid_not_coprime n i
  have hgood_add (b : ℕ) : Good (b + L) ↔ Good b := by
    constructor
    · intro hb i hi hcop
      apply hb i hi
      exact (Nat.add_coprime_iff_left (hdvd i hi)).2 hcop
    · intro hb i hi hcop
      apply hb i hi
      exact (Nat.add_coprime_iff_left (hdvd i hi)).1 hcop
  have hgood_all {b : ℕ} (hb : Good b) : ∀ i, ¬Nat.Coprime b (a i) := by
    exact compatible_all_of_core hb
  have hgood_start : Good (a 0 + L) := (hgood_add (a 0)).2 (hgood_term 0)
  obtain ⟨T, hT⟩ := compatible_mem_range (by omega) (hgood_all hgood_start)
  have hTpos : 0 < T := by
    by_contra h
    have : T = 0 := Nat.eq_zero_of_not_pos h
    subst T
    omega
  refine ⟨T, L, hTpos, hLpos, ?_⟩
  intro n
  induction n with
  | zero => simpa using hT
  | succ n ih =>
      have hshift_good : Good (a (n + 1) + L) :=
        (hgood_add (a (n + 1))).2 (hgood_term (n + 1))
      have hshift_all : ∀ i, ¬Nat.Coprime (a (n + 1) + L) (a i) := hgood_all hshift_good
      have hbase_lt : a (n + T) < a (n + 1) + L := by
        rw [ih]
        exact Nat.add_lt_add_right (ha.2 n).1 L
      have hle : a (n + T + 1) ≤ a (n + 1) + L := by
        by_contra h
        have hlt : a (n + 1) + L < a (n + T + 1) := lt_of_not_ge h
        obtain ⟨i, hi, hicop⟩ := (ha.2 (n + T)).2.2 (a (n + 1) + L) hbase_lt hlt
        exact hshift_all i (by simpa [Nat.coprime_iff_gcd_eq_one] using hicop)
      have hge : a (n + 1) + L ≤ a (n + T + 1) := by
        by_contra h
        have hlt : a (n + T + 1) < a (n + 1) + L := lt_of_not_ge h
        have hprev : a n + L < a (n + T + 1) := by
          rw [← ih]
          exact (ha.2 (n + T)).1
        have hLle : L ≤ a (n + T + 1) := by omega
        let c := a (n + T + 1) - L
        have hcadd : c + L = a (n + T + 1) := Nat.sub_add_cancel hLle
        have hnc : a n < c := by omega
        have hcn : c < a (n + 1) := by omega
        have hgoodc : Good c := by
          apply (hgood_add c).1
          rw [hcadd]
          exact hgood_term (n + T + 1)
        have hallc : ∀ i, ¬Nat.Coprime c (a i) := hgood_all hgoodc
        obtain ⟨i, hi, hicop⟩ := (ha.2 n).2.2 c hnc hcn
        exact hallc i (by simpa [Nat.coprime_iff_gcd_eq_one] using hicop)
      have heq : a (n + T + 1) = a (n + 1) + L := le_antisymm hle hge
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using heq
