import Mathlib
set_option backward.isDefEq.respectTransparency false

/-- A *board* is a finite multiset of natural numbers.  The full board discipline
(entries `≥ 1`, cardinality `2026`) is captured by the predicate `IsInitial`. -/
abbrev Board := Multiset ℕ

/-- An *initial board*: exactly `2026` entries, each strictly greater than `1`. -/
def IsInitial (B : Board) : Prop :=
  Multiset.card B = 2026 ∧ ∀ a ∈ B, 1 < a

/-- A single *move*: pick two entries `m, n` (from two distinct positions,
modelled as two separate elements of the multiset) both `> 1`, remove them and
insert `gcd(m, n)` and `lcm(m, n) / gcd(m, n)`.  Using `m ::ₘ n ::ₘ s` for the
source board automatically encodes that the two chosen positions are distinct
(they are two separate multiset elements, whose *values* may coincide). -/
def Move (B B' : Board) : Prop :=
  ∃ (m n : ℕ) (s : Board), 1 < m ∧ 1 < n ∧
    B = m ::ₘ n ::ₘ s ∧
    B' = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s

/-- A board is *terminal* when at most one entry is `> 1`, so no move is possible. -/
def IsTerminal (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) ≤ 1

/-- A board has a *unique large entry* when exactly one entry is `> 1`. -/
def HasUniqueLarge (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) = 1

/-- `Reachable B B'` : `B'` can be obtained from `B` by a finite sequence of moves
(the reflexive–transitive closure of `Move`).  A finite play from `B` to a
terminal board `B'` is precisely a witness of `Reachable B B'` with `IsTerminal B'`. -/
def Reachable (B B' : Board) : Prop := Relation.ReflTransGen Move B B'

/-- The exponent `g_p` for a prime `p` and board `B`: the `gcd` of the `p`-adic
valuations of the entries of `B`.  Since `gcd(a, 0) = a`, valuations equal to `0`
(entries not divisible by `p`) do not affect this gcd, so `gExp p B` is the gcd of
the *positive* `p`-adic valuations occurring in `B`. -/
noncomputable def gExp (p : ℕ) (B : Board) : ℕ :=
  (B.map (fun a => padicValNat p a)).gcd

/-- The claimed invariant terminal value
`M = ∏_{p ∣ ∏ B} p ^ gExp p B`, the product over all primes dividing some entry
of `B` of `p` raised to the gcd of the `p`-adic valuations. -/
noncomputable def Mval (B : Board) : ℕ :=
  ∏ p ∈ B.prod.primeFactors, p ^ gExp p B

/-- **Statement (a), part 1 — termination.**  There is no infinite play starting
from an initial board `B₀`: no infinite sequence of boards can start at `B₀` and
have every consecutive pair related by a `Move`. -/
theorem statement_a_termination (B₀ : Board) (hB₀ : IsInitial B₀) :
    ¬ ∃ f : ℕ → Board, f 0 = B₀ ∧ ∀ k, Move (f k) (f (k + 1)) := by
  let AllPos : Board → Prop := fun B => ∀ a ∈ B, 0 < a
  let countLarge : Board → ℕ := fun B => Multiset.card (B.filter (fun a => 1 < a))
  let measure : Board → ℕ := fun B => B.prod + countLarge B
  have initialPos : AllPos B₀ := by
    intro a ha
    exact (hB₀.2 a ha).trans' Nat.zero_lt_one
  have quotientPos {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
      0 < Nat.lcm m n / Nat.gcd m n := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd (Nat.lcm_pos hm hn) <|
        (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
    · exact Nat.gcd_pos_of_pos_left n hm
  have movePos {B B' : Board} (hB : AllPos B) (hmove : Move B B') : AllPos B' := by
    rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
    intro a ha
    simp only [Multiset.mem_cons] at ha
    rcases ha with rfl | rfl | ha
    · exact Nat.gcd_pos_of_pos_left n (Nat.zero_lt_one.trans hm)
    · exact quotientPos (Nat.zero_lt_one.trans hm) (Nat.zero_lt_one.trans hn)
    · exact hB a (by simp [ha])
  have countLarge_le {B B' : Board} (hmove : Move B B') :
      countLarge B' ≤ countLarge B := by
    rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
    simp only [countLarge, Multiset.filter_cons, Multiset.card_cons]
    split <;> split <;> simp_all <;> omega
  have measure_lt {B B' : Board} (hB : AllPos B) (hmove : Move B B') :
      measure B' < measure B := by
    rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have hspos : 0 < s.prod := by
      apply Multiset.prod_pos
      intro a ha
      exact hB a (by simp [ha])
    have hm0 : 0 < m := Nat.zero_lt_one.trans hm
    have hn0 : 0 < n := Nat.zero_lt_one.trans hn
    have hgpos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm0
    have hlpos : 0 < Nat.lcm m n := Nat.lcm_pos hm0 hn0
    have hprod :
        Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
      Nat.mul_div_cancel' ((Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n))
    by_cases hg : Nat.gcd m n = 1
    · have hq : 1 < Nat.lcm m n / Nat.gcd m n := by
        rw [hg, Nat.div_one]
        exact hm.trans_le (Nat.le_of_dvd hlpos (Nat.dvd_lcm_left m n))
      have hl : Nat.lcm m n = m * n := by
        simpa [hg] using (Nat.gcd_mul_lcm m n)
      have hmn : 1 < m * n := by nlinarith
      simp [measure, countLarge, hm, hn, hg, hl, hmn, Nat.mul_assoc]
    · have hg1 : 1 < Nat.gcd m n := by omega
      have hqpos : 0 < Nat.lcm m n / Nat.gcd m n := quotientPos hm0 hn0
      have hl_lt : Nat.lcm m n < m * n := by
        nlinarith [Nat.gcd_mul_lcm m n]
      have hc := countLarge_le
        (B := m ::ₘ n ::ₘ s)
        (B' := Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s)
        ⟨m, n, s, hm, hn, rfl, rfl⟩
      simp only [measure, Multiset.prod_cons] at *
      nlinarith
  rintro ⟨f, hf, hmove⟩
  have hpos : ∀ k, AllPos (f k) := by
    intro k
    induction k with
    | zero => simpa [hf] using initialPos
    | succ k ih => exact movePos ih (by simpa [Nat.succ_eq_add_one] using hmove k)
  have hdec : ∀ k, measure (f (k + 1)) < measure (f k) := by
    intro k
    exact measure_lt (hpos k) (hmove k)
  have hbound : ∀ k, measure (f k) + k ≤ measure (f 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hd := hdec k
        omega
  have := hbound (measure (f 0) + 1)
  omega

def AllPositive (B : Board) : Prop :=
  ∀ a ∈ B, 0 < a

def largeCount (B : Board) : ℕ :=
  Multiset.card (B.filter (fun a => 1 < a))

def boardMeasure (B : Board) : ℕ :=
  B.prod + largeCount B

lemma initial_allPositive {B : Board} (hB : IsInitial B) : AllPositive B := by
  intro a ha
  exact (hB.2 a ha).trans' Nat.zero_lt_one

lemma gcd_div_lcm_pos {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    0 < Nat.lcm m n / Nat.gcd m n := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd (Nat.lcm_pos hm hn) <|
      (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
  · exact Nat.gcd_pos_of_pos_left n hm

lemma move_allPositive {B B' : Board} (hB : AllPositive B) (hmove : Move B B') :
    AllPositive B' := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  intro a ha
  simp only [Multiset.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · exact Nat.gcd_pos_of_pos_left n (Nat.zero_lt_one.trans hm)
  · exact gcd_div_lcm_pos (Nat.zero_lt_one.trans hm) (Nat.zero_lt_one.trans hn)
  · exact hB a (by simp [ha])

lemma move_hasLarge {B B' : Board} (hmove : Move B B') :
    (∃ a ∈ B', 1 < a) := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  by_cases hg : Nat.gcd m n = 1
  · refine ⟨Nat.lcm m n / Nat.gcd m n, by simp, ?_⟩
    rw [hg, Nat.div_one]
    exact hm.trans_le (Nat.le_of_dvd (Nat.lcm_pos (by omega) (by omega)) (Nat.dvd_lcm_left m n))
  · refine ⟨Nat.gcd m n, by simp, ?_⟩
    have hpos := Nat.gcd_pos_of_pos_left n (Nat.zero_lt_one.trans hm)
    omega

lemma move_largeCount_le {B B' : Board} (hmove : Move B B') :
    largeCount B' ≤ largeCount B := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  simp only [largeCount, Multiset.filter_cons, Multiset.card_cons]
  split <;> split <;> simp_all <;> omega

lemma move_boardMeasure_lt {B B' : Board} (hB : AllPositive B) (hmove : Move B B') :
    boardMeasure B' < boardMeasure B := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  have hspos : 0 < s.prod := by
    apply Multiset.prod_pos
    intro a ha
    exact hB a (by simp [ha])
  have hm0 : 0 < m := Nat.zero_lt_one.trans hm
  have hn0 : 0 < n := Nat.zero_lt_one.trans hn
  have hgpos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm0
  have hlpos : 0 < Nat.lcm m n := Nat.lcm_pos hm0 hn0
  have hprod :
      Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
    Nat.mul_div_cancel' ((Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n))
  by_cases hg : Nat.gcd m n = 1
  · have hq : 1 < Nat.lcm m n / Nat.gcd m n := by
      rw [hg, Nat.div_one]
      exact hm.trans_le (Nat.le_of_dvd hlpos (Nat.dvd_lcm_left m n))
    have hl : Nat.lcm m n = m * n := by
      simpa [hg] using (Nat.gcd_mul_lcm m n)
    have hmn : 1 < m * n := by nlinarith
    simp [boardMeasure, largeCount, hm, hn, hg, hl, hmn, Nat.mul_assoc]
  · have hg1 : 1 < Nat.gcd m n := by omega
    have hqpos : 0 < Nat.lcm m n / Nat.gcd m n := gcd_div_lcm_pos hm0 hn0
    have hl_lt : Nat.lcm m n < m * n := by
      nlinarith [Nat.gcd_mul_lcm m n]
    have hc := move_largeCount_le
      (B := m ::ₘ n ::ₘ s)
      (B' := Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s)
      ⟨m, n, s, hm, hn, rfl, rfl⟩
    simp only [boardMeasure, Multiset.prod_cons] at *
    nlinarith

lemma reachable_allPositive {B B' : Board} (hB : AllPositive B)
    (hreach : Reachable B B') : AllPositive B' := by
  induction hreach with
  | refl => exact hB
  | tail _ hmove ih => exact move_allPositive ih hmove

lemma initial_hasLarge {B : Board} (hB : IsInitial B) : ∃ a ∈ B, 1 < a := by
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by rw [hB.1]; norm_num)
  exact ⟨a, ha, hB.2 a ha⟩

lemma reachable_hasLarge {B B' : Board} (hB : IsInitial B)
    (hreach : Reachable B B') : ∃ a ∈ B', 1 < a := by
  induction hreach with
  | refl => exact initial_hasLarge hB
  | tail _ hmove _ => exact move_hasLarge hmove

lemma gcd_min_max_sub (a b : ℕ) :
    Nat.gcd (min a b) (max a b - min a b) = Nat.gcd a b := by
  rcases le_total a b with hab | hba
  · simp [min_eq_left hab, max_eq_right hab, Nat.gcd_sub_self_right hab]
  · simp [min_eq_right hba, max_eq_left hba, Nat.gcd_sub_self_right hba, Nat.gcd_comm]

lemma padicValNat_gcd {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0) :
    padicValNat p (Nat.gcd m n) = min (padicValNat p m) (padicValNat p n) := by
  have h := DFunLike.congr_fun (Nat.factorization_gcd hm hn) p
  simpa [Nat.factorization_def _ hp] using h

lemma padicValNat_lcm {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0) :
    padicValNat p (Nat.lcm m n) = max (padicValNat p m) (padicValNat p n) := by
  have h := DFunLike.congr_fun (Nat.factorization_lcm hm hn) p
  simpa [Nat.factorization_def _ hp] using h

lemma padicValNat_lcm_div_gcd {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0) :
    padicValNat p (Nat.lcm m n / Nat.gcd m n) =
      max (padicValNat p m) (padicValNat p n) -
        min (padicValNat p m) (padicValNat p n) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.div_of_dvd
    ((Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n))]
  rw [padicValNat_lcm hp hm hn, padicValNat_gcd hp hm hn]

lemma move_gExp {B B' : Board} (hmove : Move B B') (p : ℕ) (hp : p.Prime) :
    gExp p B' = gExp p B := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  let a := padicValNat p m
  let b := padicValNat p n
  let r := (s.map fun x => padicValNat p x).gcd
  unfold gExp
  simp only [Multiset.map_cons, Multiset.gcd_cons]
  change Nat.gcd (padicValNat p (Nat.gcd m n))
      (Nat.gcd (padicValNat p (Nat.lcm m n / Nat.gcd m n)) r) =
    Nat.gcd a (Nat.gcd b r)
  rw [padicValNat_gcd hp hm0 hn0, padicValNat_lcm_div_gcd hp hm0 hn0]
  change Nat.gcd (min a b) (Nat.gcd (max a b - min a b) r) =
    Nat.gcd a (Nat.gcd b r)
  calc
    _ = Nat.gcd (Nat.gcd (min a b) (max a b - min a b)) r :=
      (Nat.gcd_assoc _ _ _).symm
    _ = Nat.gcd (Nat.gcd a b) r := by rw [gcd_min_max_sub]
    _ = _ := Nat.gcd_assoc _ _ _

lemma reachable_gExp {B B' : Board} (hreach : Reachable B B') (p : ℕ) (hp : p.Prime) :
    gExp p B' = gExp p B := by
  induction hreach with
  | refl => rfl
  | tail _ hmove ih => exact (move_gExp hmove p hp).trans ih

lemma terminal_filter_eq_singleton {B : Board} (huniq : HasUniqueLarge B)
    {M : ℕ} (hM : 1 < M) (hMem : M ∈ B) :
    B.filter (fun x => 1 < x) = {M} := by
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp huniq
  have hMf : M ∈ B.filter (fun x => 1 < x) := Multiset.mem_filter.mpr ⟨hMem, hM⟩
  rw [ha] at hMf
  have hMa : M = a := by simpa using hMf
  simpa [hMa] using ha

lemma terminal_erase_all_one {B : Board} (hpos : AllPositive B)
    (huniq : HasUniqueLarge B) {M : ℕ} (hM : 1 < M) (hMem : M ∈ B) :
    ∀ a ∈ B.erase M, a = 1 := by
  have hfilter := terminal_filter_eq_singleton huniq hM hMem
  have herase : (B.erase M).filter (fun x => 1 < x) = 0 := by
    rw [← Multiset.sub_singleton, Multiset.filter_sub, hfilter]
    simp [hM]
  intro a ha
  have haB : a ∈ B := Multiset.mem_of_mem_erase ha
  have ha0 := hpos a haB
  have ha1 : ¬1 < a := by
    intro h
    have : a ∈ (B.erase M).filter (fun x => 1 < x) :=
      Multiset.mem_filter.mpr ⟨ha, h⟩
    rw [herase] at this
    simp at this
  omega

lemma terminal_gExp_eq_padicValNat {B : Board} (hpos : AllPositive B)
    (huniq : HasUniqueLarge B) {M p : ℕ} (hM : 1 < M) (hMem : M ∈ B) :
    gExp p B = padicValNat p M := by
  have hone := terminal_erase_all_one hpos huniq hM hMem
  have htail : ((B.erase M).map fun x => padicValNat p x).gcd = 0 := by
    apply (Multiset.gcd_eq_zero_iff _).mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    rw [hone a ha]
    exact padicValNat_one_right p
  unfold gExp
  rw [← Multiset.cons_erase hMem]
  simp [htail]

lemma allPositive_prod_pos {B : Board} (hB : AllPositive B) : 0 < B.prod := by
  apply Multiset.prod_pos
  exact hB

lemma move_prod_primeFactors {B B' : Board} (hB : AllPositive B)
    (hmove : Move B B') : B'.prod.primeFactors = B.prod.primeFactors := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  have hm0 : 0 < m := Nat.zero_lt_one.trans hm
  have hn0 : 0 < n := Nat.zero_lt_one.trans hn
  have hs0 : 0 < s.prod := by
    apply Multiset.prod_pos
    intro a ha
    exact hB a (by simp [ha])
  have hpair :
      Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
    Nat.mul_div_cancel' ((Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n))
  have hnewprod :
      (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod =
        Nat.lcm m n * s.prod := by
    simp only [Multiset.prod_cons]
    rw [← Nat.mul_assoc, hpair]
  have hold0 : m * (n * s.prod) ≠ 0 := by positivity
  have hnew0 : Nat.lcm m n * s.prod ≠ 0 := by
    exact mul_ne_zero (Nat.lcm_pos hm0 hn0).ne' hs0.ne'
  rw [hnewprod]
  ext p
  simp only [Multiset.prod_cons, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hd, _⟩
    refine ⟨hp, ?_, hold0⟩
    simpa only [hp.dvd_mul, hp.dvd_lcm, or_assoc] using hd
  · rintro ⟨hp, hd, _⟩
    refine ⟨hp, ?_, hnew0⟩
    simpa only [hp.dvd_mul, hp.dvd_lcm, or_assoc] using hd

lemma reachable_prod_primeFactors {B B' : Board} (hB : AllPositive B)
    (hreach : Reachable B B') : B'.prod.primeFactors = B.prod.primeFactors := by
  have hpair : AllPositive B' ∧ B'.prod.primeFactors = B.prod.primeFactors := by
    induction hreach with
    | refl => exact ⟨hB, rfl⟩
    | tail _ hmove ih =>
        exact ⟨move_allPositive ih.1 hmove, (move_prod_primeFactors ih.1 hmove).trans ih.2⟩
  exact hpair.2

lemma terminal_prod_eq_large {B : Board} (hpos : AllPositive B)
    (huniq : HasUniqueLarge B) {M : ℕ} (hM : 1 < M) (hMem : M ∈ B) :
    B.prod = M := by
  have hone := terminal_erase_all_one hpos huniq hM hMem
  have htail : (B.erase M).prod = 1 := Multiset.prod_eq_one hone
  rw [← Multiset.cons_erase hMem]
  simp [htail]

/-- **Statement (a), part 2 — unique large entry.**  Any terminal board reachable
from an initial board `B₀` has exactly one entry `> 1`. -/
theorem statement_a_unique_large (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') :
    HasUniqueLarge B' := by
  obtain ⟨a, ha, ha1⟩ := reachable_hasLarge hB₀ hreach
  have hmem : a ∈ B'.filter (fun x => 1 < x) := Multiset.mem_filter.mpr ⟨ha, ha1⟩
  have hpos : 0 < Multiset.card (B'.filter (fun x => 1 < x)) :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨a, hmem⟩
  exact Nat.eq_one_of_dvd_one (by
    rw [Nat.dvd_one]
    exact Nat.le_antisymm hterm hpos)

/-- **Statement (b) — invariance of `M`.**  Any two terminal boards reachable from
the same initial board `B₀` have the same set of entries `> 1`; since (by (a)) each
has exactly one such entry, this says the terminal value `M` is the same for both. -/
theorem statement_b_invariance (B₀ : Board) (hB₀ : IsInitial B₀)
    (B₁ B₂ : Board) (h₁ : Reachable B₀ B₁) (h₂ : Reachable B₀ B₂)
    (t₁ : IsTerminal B₁) (t₂ : IsTerminal B₂) :
    ∀ M, (1 < M ∧ M ∈ B₁) ↔ (1 < M ∧ M ∈ B₂) := by
  have hp₁ := reachable_allPositive (initial_allPositive hB₀) h₁
  have hp₂ := reachable_allPositive (initial_allPositive hB₀) h₂
  have hu₁ := statement_a_unique_large B₀ hB₀ B₁ h₁ t₁
  have hu₂ := statement_a_unique_large B₀ hB₀ B₂ h₂ t₂
  have large_eq {M N : ℕ} (hM : 1 < M) (hm : M ∈ B₁)
      (hN : 1 < N) (hn : N ∈ B₂) : M = N := by
    apply (Nat.eq_iff_prime_padicValNat_eq M N (by omega) (by omega)).mpr
    intro p hp
    calc
      padicValNat p M = gExp p B₁ :=
        (terminal_gExp_eq_padicValNat hp₁ hu₁ hM hm).symm
      _ = gExp p B₀ := reachable_gExp h₁ p hp
      _ = gExp p B₂ := (reachable_gExp h₂ p hp).symm
      _ = padicValNat p N := terminal_gExp_eq_padicValNat hp₂ hu₂ hN hn
  intro M
  constructor
  · rintro ⟨hM, hm⟩
    obtain ⟨N, hn, hN⟩ := reachable_hasLarge hB₀ h₂
    have := large_eq hM hm hN hn
    simpa [this] using And.intro hN hn
  · rintro ⟨hM, hm⟩
    obtain ⟨N, hn, hN⟩ := reachable_hasLarge hB₀ h₁
    have hNM : N = M := large_eq hN hn hM hm
    simpa [hNM] using And.intro hN hn

/-- **Value of `M` (correctness of the explicit formula).**  For any terminal board
`B'` reachable from an initial board `B₀`, the unique entry `M > 1` of `B'` equals
the invariant `Mval B₀`. -/
theorem terminal_value_eq_Mval (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B')
    (M : ℕ) (hM : 1 < M) (hMem : M ∈ B') :
    M = Mval B₀ := by
  have hp₀ := initial_allPositive hB₀
  have hp' := reachable_allPositive hp₀ hreach
  have hu := statement_a_unique_large B₀ hB₀ B' hreach hterm
  have hprod := terminal_prod_eq_large hp' hu hM hMem
  have hpf : B₀.prod.primeFactors = M.primeFactors := by
    calc
      B₀.prod.primeFactors = B'.prod.primeFactors :=
        (reachable_prod_primeFactors hp₀ hreach).symm
      _ = M.primeFactors := by rw [hprod]
  unfold Mval
  rw [hpf]
  symm
  calc
    (∏ p ∈ M.primeFactors, p ^ gExp p B₀) =
        ∏ p ∈ M.primeFactors, p ^ padicValNat p M := by
      apply Finset.prod_congr rfl
      intro p hpMem
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
      congr 1
      calc
        gExp p B₀ = gExp p B' := (reachable_gExp hreach p hp).symm
        _ = padicValNat p M := terminal_gExp_eq_padicValNat hp' hu hM hMem
    _ = ∏ p ∈ M.primeFactors, p ^ M.factorization p := by
      apply Finset.prod_congr rfl
      intro p hpMem
      rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hpMem)]
    _ = M.factorization.prod (fun p e => p ^ e) :=
      (Nat.prod_factorization_eq_prod_primeFactors (n := M) (fun p e => p ^ e)).symm
    _ = M := Nat.prod_factorization_pow_eq_self (by omega)

/-- The invariant terminal value is itself `> 1`, since all initial entries exceed
`1`. -/
theorem Mval_gt_one (B₀ : Board) (hB₀ : IsInitial B₀) : 1 < Mval B₀ := by
  obtain ⟨a, ha, ha1⟩ := initial_hasLarge hB₀
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1.ne'
  letI : Fact p.Prime := ⟨hp⟩
  have ha0 : a ≠ 0 := by omega
  have hva : padicValNat p a ≠ 0 :=
    (dvd_iff_padicValNat_ne_zero ha0).mp hpa
  have hvMem : padicValNat p a ∈ B₀.map (fun x => padicValNat p x) :=
    Multiset.mem_map.mpr ⟨a, ha, rfl⟩
  have hg : gExp p B₀ ≠ 0 := by
    unfold gExp
    intro hzero
    exact hva ((Multiset.gcd_eq_zero_iff _).mp hzero _ hvMem)
  have hpMem : p ∈ B₀.prod.primeFactors := by
    apply hp.mem_primeFactors
    · exact hpa.trans (Multiset.dvd_prod ha)
    · exact (allPositive_prod_pos (initial_allPositive hB₀)).ne'
  unfold Mval
  apply (Finset.one_lt_prod_iff_of_one_le
    (fun q hq => Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hq).one_le)).mpr
  exact ⟨p, hpMem, one_lt_pow₀ hp.one_lt hg⟩
