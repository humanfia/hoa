import IChO2026Chem.Reporting

/-!
# IChO 2026, theory problem 1.3

This file formalizes both requested outputs:

* the carbon count obtained from the `[M]⁺ : [M+1]⁺ = 9 : 1` isotope pattern;
* the identification of `W` among the ten structures printed in the table.

The carbon-isotope abundances are the exact printed values.  The displayed
ratio `9 : 1` is treated according to the task's measurement contract: its
actual first component lies within one half of its last displayed quantum.
The candidate carbon counts and the locations of phenolic hydroxy groups are
read directly from the formulae and structures on problem page Q1-2.  The
standard ferric-ion colour test is represented by the proposition
`HasPhenolicOH`.
-/

namespace IChO2026T1A3

open IChO2026Chem.Reporting

noncomputable section

/-! ## Carbon-isotope calculation -/

/-- Printed natural abundance of carbon-12, `98.9 %`. -/
def carbon12Abundance : ℝ := 989 / 1000

/-- Since the problem says carbon contains only carbon-12 and carbon-13, the
printed carbon-13 abundance is `100 % - 98.9 % = 1.1 %`. -/
def carbon13Abundance : ℝ := 11 / 1000

theorem carbon_abundances_sum_to_one :
    carbon12Abundance + carbon13Abundance = 1 := by
  norm_num [carbon12Abundance, carbon13Abundance]

/-- Relative probability (and hence relative intensity) of the molecular-ion
peak containing only carbon-12 among its `n` carbon atoms.  Contributions from
the monoisotopic non-carbon atoms are common factors and cancel in a ratio. -/
def molecularIonWeight (n : ℕ) : ℝ := carbon12Abundance ^ n

/-- Relative probability of the `[M+1]⁺` isotopologue: choose one of the `n`
carbon atoms to be carbon-13, while all remaining carbon atoms are carbon-12. -/
def plusOneIonWeight (n : ℕ) : ℝ :=
  (n : ℝ) * carbon13Abundance * carbon12Abundance ^ (n - 1)

/-- The theoretical intensity ratio in the order printed in the question,
`[M]⁺/[M+1]⁺`. -/
def theoreticalPeakRatio (n : ℕ) : ℝ :=
  molecularIonWeight n / plusOneIonWeight n

/-- Cancellation of the common isotope-probability factors gives

`[M]⁺/[M+1]⁺ = 989/(11 n)`.

It is stated in cross-multiplied form, which is convenient for deriving the
unique integral carbon count without making any search-bound assumption. -/
theorem theoreticalPeakRatio_cross_mul {n : ℕ} (hn : 0 < n) :
    theoreticalPeakRatio n * (11 * (n : ℝ)) = 989 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hp : (carbon12Abundance : ℝ) ^ k ≠ 0 := by
    exact pow_ne_zero k (by norm_num [carbon12Abundance])
  norm_num [theoreticalPeakRatio, molecularIonWeight, plusOneIonWeight,
    carbon12Abundance, carbon13Abundance, pow_succ, hp]
  field_simp

/-- Direct substitution of the displayed central ratio `9` gives the unrounded
carbon-count estimate `989/99 = 9.9898...`. -/
theorem raw_carbon_estimate :
    (989 : ℝ) / (9 * 11) = 989 / 99 := by
  norm_num

/-- The raw estimate is strictly within half an integer of `10`. -/
theorem raw_carbon_estimate_nearest_integer :
    |(989 : ℝ) / 99 - 10| < 1 / 2 := by
  norm_num [abs_of_nonpos]

/-- For ten carbons, the unrounded theoretical peak ratio is
`989/110 = 8.9909...`. -/
theorem ten_carbons_peak_ratio :
    theoreticalPeakRatio 10 = (989 : ℝ) / 110 := by
  have h := theoreticalPeakRatio_cross_mul (n := 10) (by norm_num)
  norm_num at h ⊢
  linarith

/-- The ten-carbon prediction really is compatible with a ratio displayed as
`9 : 1` at unit resolution.  Together with `carbon_atom_count`, this proves
existence as well as uniqueness of the reported integral count. -/
theorem ten_carbons_matches_displayed_ratio :
    ConsistentMeasurement (theoreticalPeakRatio 10) 9 1 := by
  constructor
  · norm_num
  · rw [ten_carbons_peak_ratio]
    norm_num [abs_of_nonpos]

/-- The displayed `9 : 1` ratio, interpreted with the prescribed half-unit
measurement interval, determines the positive integral carbon count uniquely.

This proof does not assume an arbitrary upper search bound: the lower and
upper ends of the measurement interval imply `n < 11` and `9 < n`,
respectively. -/
theorem carbon_atom_count
    {n : ℕ} (hn : 0 < n)
    (hobs : ConsistentMeasurement (theoreticalPeakRatio n) 9 1) :
    n = 10 := by
  let r := theoreticalPeakRatio n
  have hcross : r * (11 * (n : ℝ)) = 989 := by
    simpa [r] using theoreticalPeakRatio_cross_mul hn
  have habs : |r - 9| ≤ (1 : ℝ) / 2 := by
    simpa [r] using hobs.2
  have hb := (abs_le.mp habs)
  have hlo : (17 : ℝ) / 2 ≤ r := by linarith [hb.1]
  have hhi : r ≤ (19 : ℝ) / 2 := by linarith [hb.2]
  have hfactor : 0 ≤ (11 : ℝ) * (n : ℝ) := by positivity
  have hlomul := mul_le_mul_of_nonneg_right hlo hfactor
  have hhimul := mul_le_mul_of_nonneg_right hhi hfactor
  have hnltReal : (n : ℝ) < 11 := by
    nlinarith [hlomul]
  have hnlt : n < 11 := by exact_mod_cast hnltReal
  have hnAboveReal : (9 : ℝ) < n := by
    nlinarith [hhimul]
  have hnAbove : 9 < n := by exact_mod_cast hnAboveReal
  omega

/-! ## Identification among the printed structures -/

/-- The ten numbered structures in the candidate table on Q1-2.  Compound 5
is named here because its drawn structure is
4-allyl-2-methoxyphenol (eugenol). -/
inductive Candidate where
  | compound1
  | compound2
  | compound3
  | compound4
  | compound5Eugenol
  | compound6
  | compound7
  | compound8
  | compound9
  | compound10
  deriving DecidableEq, Repr

/-- Carbon counts transcribed from the molecular formula printed under each
structure in the candidate table. -/
def candidateCarbonCount : Candidate → ℕ
  | .compound1 => 11
  | .compound2 => 10
  | .compound3 => 10
  | .compound4 => 6
  | .compound5Eugenol => 10
  | .compound6 => 10
  | .compound7 => 14
  | .compound8 => 15
  | .compound9 => 10
  | .compound10 => 10

/-- Inspection of the printed structures shows a phenolic hydroxy group only
in compounds 1 and 5.  Compound 4 has an aliphatic alcohol; compounds 2 and 6
also contain alcohol groups, but none is attached directly to an aromatic
ring. -/
def HasPhenolicOH : Candidate → Prop
  | .compound1 => True
  | .compound5Eugenol => True
  | _ => False

theorem phenolic_candidates_are_one_or_five
    {w : Candidate} (hphenol : HasPhenolicOH w) :
    w = .compound1 ∨ w = .compound5Eugenol := by
  cases w <;> simp_all [HasPhenolicOH]

/-- A candidate with the mass-spectrometrically established ten carbons and
the phenolic group signalled by the characteristic aqueous ferric-ion colour
test is necessarily compound 5, eugenol. -/
theorem compound_identity
    {w : Candidate}
    (hcarbon : candidateCarbonCount w = 10)
    (hFeIII : HasPhenolicOH w) :
    w = .compound5Eugenol := by
  rcases phenolic_candidates_are_one_or_five hFeIII with h1 | h5
  · subst w
    norm_num [candidateCarbonCount] at hcarbon
  · exact h5

/-- Compound 5 has exactly the two table properties used for identification. -/
theorem eugenol_matches_table_evidence :
    candidateCarbonCount .compound5Eugenol = 10 ∧
      HasPhenolicOH .compound5Eugenol := by
  simp [candidateCarbonCount, HasPhenolicOH]

/-! ## Combined source-to-answer theorem -/

/-- Data supplied by the problem after translating the mass-spectrum display
and ferric-ion observation into their standard chemical meanings.  The field
`sameCarbonCount` connects the molecular ion of `W` with its table entry. -/
structure ProblemData where
  carbonCount : ℕ
  positiveCarbonCount : 0 < carbonCount
  displayedPeakRatio :
    ConsistentMeasurement (theoreticalPeakRatio carbonCount) 9 1
  W : Candidate
  sameCarbonCount : candidateCarbonCount W = carbonCount
  ferricIonIndicatesPhenol : HasPhenolicOH W

/-- Both requested outputs for T1-A3: `n = 10` and `W` is compound 5
(eugenol). -/
theorem solve_t1_a3 (data : ProblemData) :
    data.carbonCount = 10 ∧ data.W = .compound5Eugenol := by
  have hn : data.carbonCount = 10 :=
    carbon_atom_count data.positiveCarbonCount data.displayedPeakRatio
  refine ⟨hn, ?_⟩
  apply compound_identity
  · simpa [hn] using data.sameCarbonCount
  · exact data.ferricIonIndicatesPhenol

#print axioms carbon_atom_count
#print axioms compound_identity
#print axioms solve_t1_a3

end

end IChO2026T1A3
