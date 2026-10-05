/-
Copyright (c) 2026 Archon answer-blind IChO formalization project. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon chemistry-formalize agent
-/
import IChO2026Chem

/-!
# IChO 2026, Problem T1, subquestion 1.3 (target `icho_2026_t1_a3`)

**Problem.** (Sealed problem bundle: T1 page 3 question 1.3, with the T1 page 2
table.)  The blue elixir consists of four different substances X, Y, Z and W
drawn from the compounds 1–10 extractable from the four listed plants
(Zingiber, Hypericum, Chamomilla, Artemisia); the ten structures and their
printed molecular formulas appear in the T1 page 2 table.  When W was added to
an aqueous Fe3+ solution, a characteristic colour change was observed.  Mass
spectrometric analysis of W gave the peak-intensity ratio
[M]+ : [M + 1]+ = 9 : 1, where M is the molecular ion.  Carbon consists
exclusively of 12C and 13C, the natural isotopic abundance of 12C is 98.9 %,
and all other elements are monoisotopic.

**Requested outputs.**  (i) the number `n` of carbon atoms of W, determined
from the mass-spec data (exact integer); (ii) the identity of W (exact
symbolic classification).

**Derivation.**  Under the stipulated two-isotope model the [M + 1]+ peak
arises only from molecules containing exactly one 13C nucleus, so
`I[M + 1] / I[M] = n * p13 / p12` with `p12 = 0.989` and `p13 = 0.011`.
Setting this equal to `1/9` gives the exact real solution
`n̂ = 989/99 = 9.98989...`, whose nearest integer is `n = 10`.  The
characteristic aqueous Fe3+ colour change is the standard phenol test; the
pinned offline rule `aqueous_feiii_phenol_colored_complex`
(Nature 165 (1950) 1012, DOI 10.1038/1651012b0; dataset
`ciaaw-abridged-2024 + ame2020-subset + archon-templates-v1 +
contest-interpretation-v1 + trusted-empirical-rules-v1`,
`dataset_sha256 = 11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`,
`record_sha256 = 67fd6f821dcb2c53846e3e084e6a336f170b5dfd9d5fe9584743c4b301f74faf`)
certifies that in aqueous media with available iron(III) an accessible
phenolic –OH forms a visibly coloured iron(III)–phenol complex.  Of the ten
drawn table structures only compounds 1 (C11H14O3) and 5 (C10H12O2) bear a
phenolic –OH, and only compound 5 has ten carbons.  Hence W is compound 5,
eugenol (4-allyl-2-methoxyphenol, C10H12O2).
-/

namespace IChO2026Problems.Icho2026T1A3

/-! ## Isotope model (problem-stipulated constants, T1 page 3) -/

/-- Stipulated natural abundance of 12C: 98.9 %, exact as printed. -/
noncomputable def p12 : ℝ := 989 / 1000

/-- Natural abundance of 13C: carbon consists exclusively of 12C and 13C, so
`p13 = 1 - p12 = 0.011`. -/
noncomputable def p13 : ℝ := 11 / 1000

/-- The two stipulated isotope abundances exhaust carbon. -/
theorem p12_add_p13 : p12 + p13 = 1 := by
  norm_num [p12, p13]

/-- Probability that exactly `k` of the `n` carbon atoms of a molecule are 13C
under the problem's model (independent carbon sites; every other element is
monoisotopic, so only carbon contributes to the [M + 1]+ peak). -/
noncomputable def isotopologueProb (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p13 ^ k * p12 ^ (n - k)

/-- Relative intensity `I[M + 1]+ / I[M]+` for a molecule with `n` carbons: the
probability ratio of the exactly-one-13C isotopologue to the all-12C one. -/
noncomputable def mPlus1OverM (n : ℕ) : ℝ := isotopologueProb n 1 / isotopologueProb n 0

/-- The isotope ratio simplifies to `n * p13 / p12`: `Nat.choose n 1 = n`,
`Nat.choose n 0 = 1`, and `p12 ^ (n - 1)` cancels against
`p12 ^ n = p12 ^ (n - 1) * p12` (using `p12 ≠ 0` and `1 ≤ n`). -/
theorem mPlus1OverM_eq (n : ℕ) (hn : 1 ≤ n) :
    mPlus1OverM n = n * p13 / p12 := by
  have hp12 : (p12 : ℝ) ≠ 0 := by norm_num [p12]
  have hp12pow : p12 ^ (n - 1) ≠ 0 := pow_ne_zero _ hp12
  unfold mPlus1OverM isotopologueProb
  simp only [Nat.choose_one_right, Nat.choose_zero_right, pow_one, pow_zero,
    Nat.sub_zero, Nat.cast_one, one_mul]
  have hpow : p12 ^ n = p12 ^ (n - 1) * p12 := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  rw [hpow, mul_comm ((n : ℝ) * p13) (p12 ^ (n - 1)), mul_div_mul_left _ _ hp12pow]

/-- Measured peak-intensity ratio from the mass spectrum (T1 page 3):
[M]+ : [M + 1]+ = 9 : 1. -/
noncomputable def measuredM1OverM : ℝ := 1 / 9

/-- The exact real-valued solution of the isotope-ratio equation
`n * p13 / p12 = 1 / 9`, namely `n̂ = (1/9) * p12 / p13`. -/
noncomputable def carbonCountReal : ℝ := measuredM1OverM * p12 / p13

/-- Numerical evaluation of the real solution: `n̂ = 989 / 99`. -/
theorem carbonCountReal_value : carbonCountReal = 989 / 99 := by
  norm_num [carbonCountReal, measuredM1OverM, p12, p13]

/-- The real solution is the unique real number consistent with the measured
ratio (the equation is linear with `p13 ≠ 0`). -/
theorem isotopeRatio_eq_iff (x : ℝ) :
    x * p13 / p12 = measuredM1OverM ↔ x = carbonCountReal := by
  have hp13 : p13 ≠ 0 := by norm_num [p13]
  have hp12 : p12 ≠ 0 := by norm_num [p12]
  constructor
  · intro h
    rw [div_eq_iff hp12] at h
    unfold carbonCountReal
    rw [eq_div_iff hp13]
    exact h
  · intro h
    rw [h]
    unfold carbonCountReal
    rw [div_mul_cancel₀ _ hp13, mul_div_cancel_right₀ _ hp12]

/-- Corollary: for a molecule with `1 ≤ n` carbons, matching the measured
ratio is equivalent to `(n : ℝ) = n̂`. -/
theorem mPlus1OverM_eq_measured_iff (n : ℕ) (hn : 1 ≤ n) :
    mPlus1OverM n = measuredM1OverM ↔ (n : ℝ) = carbonCountReal := by
  rw [mPlus1OverM_eq n hn]
  exact isotopeRatio_eq_iff _

/-- A carbon count consistent with the mass-spectrum datum: a positive integer
within half a unit of the real solution `n̂`.  Atom counts are integral and the
displayed ratio 9 : 1 is a stipulated exact datum, so the count is the nearest
integer to `n̂ = 989/99 ≈ 9.99`; the half-unit cell is the integer rounding
cell (the source reporting policy for this output is `exact_integer`). -/
def IsCarbonCount (n : ℕ) : Prop :=
  1 ≤ n ∧ |(n : ℝ) - carbonCountReal| < 1 / 2

/-- `n = 10` is consistent with the mass-spectrum datum:
`|10 - 989/99| = 1/99 < 1/2`. -/
theorem isCarbonCount_ten : IsCarbonCount 10 := by
  refine ⟨by norm_num, ?_⟩
  rw [carbonCountReal_value]
  apply abs_lt.mpr
  constructor <;> norm_num

/-- `n = 10` is the only consistent carbon count: the open interval
`(989/99 - 1/2, 989/99 + 1/2)` contains exactly one positive integer. -/
theorem isCarbonCount_unique {n : ℕ} (h : IsCarbonCount n) : n = 10 := by
  obtain ⟨-, h2⟩ := h
  rw [carbonCountReal_value] at h2
  obtain ⟨hlo, hhi⟩ := abs_lt.mp h2
  have hhi' : (n : ℝ) < 11 := by linarith
  have hlo' : (9 : ℝ) < n := by linarith
  have h3 : n < 11 := by exact_mod_cast hhi'
  have h4 : 9 < n := by exact_mod_cast hlo'
  omega

/-! ## The closed table domain (T1 page 2) -/

/-- Molecular formula as atom counts; the ten table compounds contain only
C, H and O. -/
structure MolFormula where
  C : ℕ
  H : ℕ
  O : ℕ
deriving DecidableEq, Repr

/-- The ten compounds printed in the T1 page 2 table, in printed numbering.
The problem states that the elixir consists of four different substances
X, Y, Z, W drawn from the listed plants' extractable compounds, so this finite
enumeration is the closed candidate domain for W (provenance: `problem_text`
and `problem_image`; no invented members). -/
inductive TableCompound where
  /-- 1 (C11H14O3), Zingiber: 4-(4-hydroxy-3-methoxyphenyl)butan-2-one
  (zingerone); phenolic –OH, methoxy group, side-chain ketone. -/
  | c1
  /-- 2 (C10H18O), Zingiber: bicyclic monoterpene secondary alcohol
  (borneol skeleton). -/
  | c2
  /-- 3 (C10H18O), Zingiber / Chamomilla / Artemisia: 1,8-cineole
  (bridged cyclic ether). -/
  | c3
  /-- 4 (C6H12O), Hypericum: hex-3-en-1-ol (aliphatic unsaturated primary
  alcohol). -/
  | c4
  /-- 5 (C10H12O2), Hypericum: 4-allyl-2-methoxyphenol (eugenol);
  phenolic –OH, methoxy group, allyl group. -/
  | c5
  /-- 6 (C10H18O), Hypericum: acyclic tertiary allylic alcohol
  (linalool skeleton). -/
  | c6
  /-- 7 (C14H16), Chamomilla: fused five/seven-membered-ring hydrocarbon
  (no oxygen). -/
  | c7
  /-- 8 (C15H24), Chamomilla: acyclic sesquiterpene hydrocarbon
  (farnesene skeleton, no oxygen). -/
  | c8
  /-- 9 (C10H16O), Artemisia: bicyclic monoterpene ketone (thujone
  skeleton). -/
  | c9
  /-- 10 (C10H18O), Artemisia: cyclopentanone fused to a cyclopropane ring,
  with methyl and isopropyl substituents. -/
  | c10
deriving DecidableEq, Repr

/-- Printed molecular formula of each table compound (T1 page 2 captions). -/
def TableCompound.formula : TableCompound → MolFormula
  | .c1  => ⟨11, 14, 3⟩
  | .c2  => ⟨10, 18, 1⟩
  | .c3  => ⟨10, 18, 1⟩
  | .c4  => ⟨6, 12, 1⟩
  | .c5  => ⟨10, 12, 2⟩
  | .c6  => ⟨10, 18, 1⟩
  | .c7  => ⟨14, 16, 0⟩
  | .c8  => ⟨15, 24, 0⟩
  | .c9  => ⟨10, 16, 1⟩
  | .c10 => ⟨10, 18, 1⟩

/-- Carbon count of each table compound (the C component of its printed
formula, factored out for the mass-spec filter). -/
def TableCompound.carbons : TableCompound → ℕ
  | .c1  => 11
  | .c2  => 10
  | .c3  => 10
  | .c4  => 6
  | .c5  => 10
  | .c6  => 10
  | .c7  => 14
  | .c8  => 15
  | .c9  => 10
  | .c10 => 10

/-- Coherence of the two formula readouts. -/
theorem TableCompound.carbons_eq_formula_C (c : TableCompound) :
    c.carbons = c.formula.C := by
  cases c <;> rfl

/-- Whether the drawn structure bears a phenolic hydroxy group (an –OH bonded
directly to an aromatic ring carbon), read from the T1 page 2 structural
drawings (provenance: `problem_image`).  Only 1 and 5 are phenols; 2, 4, 6 are
aliphatic alcohols, 3 is an ether, 9 and 10 are ketones, 7 and 8 are
hydrocarbons. -/
def TableCompound.hasPhenolicOH : TableCompound → Bool
  | .c1  => true
  | .c2  => false
  | .c3  => false
  | .c4  => false
  | .c5  => true
  | .c6  => false
  | .c7  => false
  | .c8  => false
  | .c9  => false
  | .c10 => false

/-! ## The Fe3+ test bridge and the candidate filter -/

/-- Domain-relative consistency with the observed characteristic colour change
of W with aqueous Fe3+ (T1 page 3).  Bridge authority: pinned offline rule
`aqueous_feiii_phenol_colored_complex` (Nature 165 (1950) 1012,
DOI 10.1038/1651012b0; `authority_kind = peer_reviewed_literature`;
`record_sha256 = 67fd6f821dcb2c53846e3e084e6a336f170b5dfd9d5fe9584743c4b301f74faf`;
`dataset_sha256 = 11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`):
in aqueous media with available iron(III), an accessible phenolic –OH forms a
visibly coloured iron(III)–phenol complex.  The applicability conditions are
met by the problem statement (aqueous Fe3+ medium; a colour change was
explicitly observed) and by the drawn structures (the phenolic –OH of 1 and 5
is directly accessible).  Within this closed ten-compound domain the compounds
bearing a phenolic –OH are exactly those that can produce the characteristic
test response; this is a finite-domain compatibility filter, not an open-world
inverse classification. -/
def PassesFe3PhenolTest (c : TableCompound) : Prop :=
  c.hasPhenolicOH = true

/-- A candidate for W: a table compound whose carbon count equals the
mass-spec count `n` and which is consistent with the Fe3+ phenol test. -/
def IsWCandidate (n : ℕ) (c : TableCompound) : Prop :=
  c.carbons = n ∧ PassesFe3PhenolTest c

/-- Filtering all ten table compounds by `n = 10` and the Fe3+ test leaves
exactly compound 5 (eugenol).  Compound 1, the only other phenol, fails the
carbon count (11 ≠ 10). -/
theorem isWCandidate_iff (c : TableCompound) :
    IsWCandidate 10 c ↔ c = .c5 := by
  cases c <;> simp [IsWCandidate, PassesFe3PhenolTest, TableCompound.carbons,
    TableCompound.hasPhenolicOH]

/-! ## Raw and reported result specifications -/

/-- Raw derivation spec covering both requested outputs, before any reporting
rounding: the exact unrounded real solution of the isotope equation
(`n̂ = 989/99`) with a certified non-degenerate enclosure
`499/50 ≤ n̂ ≤ 10`; the carbon count `n = 10` characterized as the unique
`IsCarbonCount` integer; and the identification of W as table compound 5,
unique within the closed table domain. -/
def RawResultSpec : Prop :=
  carbonCountReal = 989 / 99
  ∧ ((499 / 50 : ℝ) ≤ carbonCountReal ∧ carbonCountReal ≤ 10)
  ∧ IsCarbonCount 10
  ∧ (∀ n : ℕ, IsCarbonCount n → n = 10)
  ∧ IsWCandidate 10 .c5
  ∧ (∀ c : TableCompound, IsWCandidate 10 c → c = .c5)

/-- Reported (final) spec: the carbon count reported as the exact integer 10
(integer lattice, reporting quantum 1; the tie rule is irrelevant because
989/99 is not a half-integer), and W reported as table compound 5 with printed
formula C10H12O2, unique within the closed table domain. -/
def ReportedResultSpec : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum (10 : ℝ) 10 1
  ∧ IsWCandidate 10 .c5
  ∧ (∀ c : TableCompound, IsWCandidate 10 c → c = .c5)
  ∧ TableCompound.formula .c5 = ⟨10, 12, 2⟩

/-- Raw result certificate: binds the answer-blind raw-role payload digest to
`RawResultSpec`. -/
theorem rawResultCertificate :
    ("a272ead3cbaca17645b8d3cf685042d7d06a25acf0514be715f7110568ff8ea0" : String)
      = "a272ead3cbaca17645b8d3cf685042d7d06a25acf0514be715f7110568ff8ea0"
      ∧ RawResultSpec := by
  refine ⟨rfl, carbonCountReal_value, ?_, isCarbonCount_ten,
    fun _n hn => isCarbonCount_unique hn, (isWCandidate_iff .c5).mpr rfl,
    fun c hc => (isWCandidate_iff c).mp hc⟩
  rw [carbonCountReal_value]
  exact ⟨by norm_num, by norm_num⟩

/-- Reported result certificate: binds the answer-blind reported-role payload
digest to `ReportedResultSpec`. -/
theorem reportedResultCertificate :
    ("569fa0485041e65d54c2a10258569bc71b281ea9befa9b4e7c5be7434aa7bb26" : String)
      = "569fa0485041e65d54c2a10258569bc71b281ea9befa9b4e7c5be7434aa7bb26"
      ∧ ReportedResultSpec := by
  have h0 : (0 : ℝ) ≤ 10 := by norm_num
  refine ⟨rfl, ?_, (isWCandidate_iff .c5).mpr rfl,
    fun c hc => (isWCandidate_iff c).mp hc, rfl⟩
  refine ⟨one_pos, ⟨10, by norm_num⟩, ?_⟩
  rw [if_pos h0]
  exact ⟨by norm_num, by norm_num⟩

end IChO2026Problems.Icho2026T1A3
