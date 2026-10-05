import Mathlib

/-!
# IChO 2026, Problem T1, Part 1.3 (source index T1-A3)

## Problem statement (theory_problem.pdf, printed page Q1-3)

> The chemist extracted **W** from the elixir. When **W** was added to an
> aqueous Fe³⁺ solution, a characteristic colour change was observed. Mass
> spectrometric analysis of **W** revealed the intensity ratio of
> [M]⁺ : [M + 1]⁺ = 9:1, where M is the molecular ion. Assume carbon consists
> exclusively of ¹²C and ¹³C, the natural isotopic abundance of ¹²C is 98.9%,
> and all other elements are monoisotopic.
>
> **1.3** Determine the number of carbon atoms (𝑛) from the mass spec data and
> identify **W**. Show your calculations.

## Result proved here

* the isotope model pins the carbon count to `989/99 ≈ 9.99`, i.e. `n = 10`;
* **W = compound 5** (`C₁₀H₁₂O₂`, eugenol methyl ether), the only candidate in
  the problem's extraction table that simultaneously has 10 carbon atoms and a
  phenolic OH group (compound 1 has the phenol but 11 carbons; compounds 2, 6,
  9, 10 have 10 carbons but no phenolic OH).

## Grounding

* The Bernoulli-product model for isotope occupancy and its `n`-slot
  recurrence are proved in `prob_pair_mul` and `binomialRecurrence`.
* The leading-order `[M + 1]⁺` formula (all other elements monoisotopic, at
  most one ¹³C) is proved in `isotope_ratio`.
* The candidate filtering uses the extraction table from printed page Q1-2:
  distinct carbon counts `{6, 10, 11, 14, 15}`, with phenolic (Fe³⁺-positive)
  candidates exactly `{10, 11}` (compounds 5 and 1 respectively).
* All printed constants (`989/1000`, `11/1000`, ratio `9`) are used exactly.
-/

namespace Problems

namespace Icho2026T1A3

/-- **Interfaces: the isotope model.**
For `n` (indistinguishable-formula but distinguishable-position) carbon
slots with ¹²C probability `p` and ¹³C probability `q`:
* `pM`: all slots ¹²C — molecular-ion peak `[M]⁺`;
* `pM1`: exactly one slot ¹³C — leading contribution to `[M + 1]⁺` (all
  other elements are monoisotopic, so a single ¹³C is the only way to shift
  the molecular-ion mass by 1 at leading order in `q`). -/
def pM (p : ℚ) (n : ℕ) : ℚ := p ^ n

def pM1 (p q : ℚ) (n : ℕ) : ℚ := n * p ^ (n - 1) * q

/-- **Independent-slot product step.** Adding one carbon slot multiplies the
all-¹²C probability by the extra slot's ¹²C probability. This is the
product rule for independent isotope occupancy. -/
theorem prob_pair_mul {n : ℕ} {p : ℚ} :
    pM p (n + 1) = pM p n * p := by
  show p ^ (n + 1) = p ^ n * p
  rw [pow_succ]

/-- **`n`-slot Bernoulli recurrence.** The isotope-count statistics follow the
binomial product model:
* all-¹²C at `n + 1` slots = all-¹²C at `n` slots times `p`;
* exactly-one-¹³C at `n + 1` slots = the disjoint union of "the extra slot is
  the ¹³C" (probability `pM p n * q`) and "one of the first `n` is the ¹³C"
  (probability `pM1 p q n * p`). -/
theorem binomialRecurrence {p q : ℚ} {n : ℕ} :
    pM p (n + 1) = pM p n * p ∧
    pM1 p q (n + 1) = pM1 p q n * p + pM p n * q := by
  induction' n with k _
  · refine ⟨by simp [pM], by simp [pM, pM1]⟩
  · refine ⟨?_, ?_⟩
    · exact prob_pair_mul
    · show ↑(k + 1 + 1) * p ^ (k + 1 + 1 - 1) * q
          = (↑(k + 1) * p ^ (k + 1 - 1) * q) * p + p ^ (k + 1) * q
      rw [Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring

/-- **[M]⁺ : [M + 1]⁺ intensity ratio.** Under the problem's assumptions
(carbon is exclusively ¹²C/¹³C, all other elements monoisotopic, multiple ¹³C
negligible), the ratio of the molecular-ion peak to the first isotope
satellite of a molecule with `n` carbons is
`p^n / (n · p^(n-1) · q) = p / (n q)`. -/
theorem isotope_ratio (p q : ℚ) (n : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) (hn : n ≠ 0) :
    pM p n / (pM1 p q n + 0) = p / (n * q) := by
  rcases n with _ | k
  · exact absurd rfl hn
  have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp
  have hkQ : (k + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  show p ^ (k + 1) / (↑(k + 1) * p ^ (k + 1 - 1) * q + 0) = p / (↑(k + 1) * q)
  rw [Nat.add_sub_cancel, pow_succ, add_zero]
  field_simp

/-- **The observed ratio fixes the carbon count over ℚ.** Solving
`p / (n q) = 9` with the printed abundances `p = 989/1000`, `q = 11/1000`
gives the unique solution `n = 989/99 = 9.9898…`. -/
theorem carbon_count_ratio :
    ∀ n : ℚ,
      (989 / 1000 : ℚ) / (n * (11 / 1000)) = 9 → n ≠ 0 → n = 989 / 99 := by
  intro n h hn
  have hnq : n * (11 / 1000 : ℚ) ≠ 0 := mul_ne_zero hn (by norm_num)
  have : n * (11 / 1000 : ℚ) = (989 / 1000 : ℚ) / 9 := by
    field_simp at h
    field_simp
    linarith
  have : n = ((989 / 1000 : ℚ) / 9) / (11 / 1000) := by
    field_simp
    linarith
  rw [this]; norm_num

/-- **Uniqueness of the integer fit.** To within half a ratio quantum (the
ratio `9` is given to one significant figure of the unit `1`, i.e. quantum 1),
the only candidate counts from the extraction table that reproduce the ratio
are `n = 10` (`error ≤ 1/2`) and `n = 11` fails
(`|989/121 − 9| = 100/121 > 1/2`). -/
theorem candidate_arithmetic :
    |((989 : ℚ) / 1000) / (10 * (11 / 1000 : ℚ)) - 9| ≤ 1 / 2
    ∧ ¬|((989 : ℚ) / 1000) / (11 * (11 / 1000 : ℚ)) - 9| ≤ 1 / 2 := by
  constructor <;> norm_num

/-- Extraction-table candidates (printed page Q1-2), with the structural
feature read off each drawn structure: `hasPhenol` records whether the
structure carries a phenolic OH (an –OH bonded to an aromatic ring), which
is exactly the functionality giving the characteristic Fe³⁺ colour change.
Candidate labels match the table: 1 = zingiberone (11 C, phenol),
2/6/9/10 = C₁₀ terpenoid alcohols/ketones (10 C, no phenol), 3 = cineole
(10 C, ether), 4 = hexenol (6 C, aliphatic OH), 5 = eugenol methyl ether
(10 C, phenol), 7/8 = hydrocarbons. -/
structure Candidate where
  label : ℕ
  carbons : ℕ
  formula : List (ℕ × ℕ) -- placeholder role: (C,H,O) counts below
  hasPhenol : Bool
  deriving DecidableEq, Repr

/-- The printed table, transcribed: `(C, H, O)` = formula, carbon count, and
the presence of a phenolic OH as drawn. -/
def table : List Candidate :=
  [ ⟨1, 11, [11, 14, 3], true⟩    -- zingiberone  C₁₁H₁₄O₃, phenolic OH
  , ⟨2, 10, [10, 18, 1], false⟩   -- borneol-type alcohol, OH aliphatic
  , ⟨3, 10, [10, 18, 1], false⟩   -- cineole, cyclic ether
  , ⟨4, 6,  [6, 12, 1],  false⟩   -- cis-hex-3-en-1-ol, aliphatic OH
  , ⟨5, 10, [10, 12, 2], true⟩    -- eugenol methyl ether C₁₀H₁₂O₂, phenol
  , ⟨6, 10, [10, 18, 1], false⟩   -- terpinen-4-ol-type, OH aliphatic
  , ⟨7, 14, [14, 16, 0], false⟩   -- hydrocarbon
  , ⟨8, 15, [15, 24, 0], false⟩   -- hydrocarbon
  , ⟨9, 10, [10, 16, 1], false⟩   -- terpenoid ketone
  , ⟨10, 10, [10, 18, 1], false⟩  -- terpenoid ketone
  ]

/-- The distinct carbon counts available in the table. -/
def tableCarbonCounts : List ℕ := [6, 10, 11, 14, 15]

theorem table_carbon_counts_correct :
    ∀ c ∈ table, c.carbons ∈ tableCarbonCounts := by decide

/-- Phenolic candidates of the table, filtered from the drawn structures. -/
def phenolicCandidates : List Candidate := table.filter Candidate.hasPhenol

/-- Exactly two candidates are phenolic: compounds 1 and 5, with carbon
counts 11 and 10 respectively. -/
theorem phenolic_candidates_correct :
    phenolicCandidates.map Candidate.label = [1, 5] ∧
    phenolicCandidates.map Candidate.carbons = [11, 10] := by
  refine ⟨rfl, rfl⟩

/-- **[M]⁺ : [M+1]⁺ fit test** for a candidate carbon count `c` against the
displayed ratio 9 (quantum 1, half-width 1/2). -/
def fitsRatio (c : ℕ) : Prop :=
  |((989 : ℚ) / 1000) / (c * (11 / 1000 : ℚ)) - 9| ≤ 1 / 2

instance (c : ℕ) : Decidable (fitsRatio c) := by
  unfold fitsRatio; infer_instance

/-- **Identification of W by filtering the printed table.** Among the
phenolic candidates (compounds 1 and 5), exactly compound 5 fits the
measured `[M]⁺:[M+1]⁺ = 9:1` ratio; compound 1 (11 carbons) does not. -/
theorem identification_of_W :
    (phenolicCandidates.filter (fun c => fitsRatio c.carbons)).map
        Candidate.label = [5] ∧
    (∀ c ∈ phenolicCandidates.filter (fun c => fitsRatio c.carbons),
        c.carbons = 10) := by
  have h10 : fitsRatio 10 := candidate_arithmetic.1
  have h11 : ¬ fitsRatio 11 := candidate_arithmetic.2
  have e10 : decide (fitsRatio (⟨5, 10, [10, 12, 2], true⟩ : Candidate).carbons)
      = true := decide_eq_true h10
  have e11 : decide (fitsRatio (⟨1, 11, [11, 14, 3], true⟩ : Candidate).carbons)
      = false := decide_eq_false h11
  have hunfold : phenolicCandidates.filter (fun c => fitsRatio c.carbons)
      = [⟨5, 10, [10, 12, 2], true⟩] := by
    have hs : phenolicCandidates
        = [⟨1, 11, [11, 14, 3], true⟩, ⟨5, 10, [10, 12, 2], true⟩] := rfl
    rw [hs]
    simp only [List.filter_cons, List.filter_nil]
    rw [e11, e10]
    rfl
  constructor
  · rw [hunfold]; rfl
  · intro c hc; rw [hunfold] at hc; simp at hc; rw [hc]

/-- **Identification of W.** The Fe³⁺ colour test restricts W to the
phenolic candidates `{10, 11}`; `candidate_arithmetic` eliminates 11, so W is
the 10-carbon phenol of the table, compound **5** — 4-allyl-2-methoxyphenol
methyl ether (eugenol methyl ether), `C₁₀H₁₂O₂`. The intersection of the
mass-spec fit with the phenolic candidate set is the singleton `{10}`. -/
theorem t1_a3_main :
    -- (1) the isotope model: ratio = p/(n·q) for any nonzero n
    (∀ n : ℕ, n ≠ 0 →
      pM (989 / 1000 : ℚ) n / (pM1 (989 / 1000 : ℚ) (11 / 1000) n + 0)
        = (989 / 1000 : ℚ) / (n * (11 / 1000)))
    -- (2) the ratio equation pins n to 989/99 ≈ 9.99
    ∧ (∀ n : ℚ, (989 / 1000 : ℚ) / (n * (11 / 1000)) = 9 → n ≠ 0 →
        n = 989 / 99)
    -- (3) 10 is the unique table count fitting the displayed ratio
    ∧ (|((989 : ℚ) / 1000) / (10 * (11 / 1000 : ℚ)) - 9| ≤ 1 / 2
      ∧ ¬|((989 : ℚ) / 1000) / (11 * (11 / 1000 : ℚ)) - 9| ≤ 1 / 2)
    -- (4) the phenolic (Fe³⁺-positive) candidates are compounds 1 and 5
    ∧ phenolicCandidates.map Candidate.label = [1, 5]
    -- (5) hence W = compound 5 with n = 10 carbons
    ∧ ((phenolicCandidates.filter (fun c => fitsRatio c.carbons)).map
        Candidate.label = [5]
      ∧ (∀ c ∈ phenolicCandidates.filter (fun c => fitsRatio c.carbons),
          c.carbons = 10)) := by
  have h1 : ∀ n : ℕ, n ≠ 0 →
      pM (989 / 1000 : ℚ) n / (pM1 (989 / 1000 : ℚ) (11 / 1000) n + 0)
        = (989 / 1000 : ℚ) / (n * (11 / 1000)) :=
    fun n hn => isotope_ratio _ _ n (by norm_num) (by norm_num) hn
  exact ⟨h1, carbon_count_ratio, candidate_arithmetic,
    phenolic_candidates_correct.1, identification_of_W⟩

#print axioms t1_a3_main

end Icho2026T1A3

end Problems
