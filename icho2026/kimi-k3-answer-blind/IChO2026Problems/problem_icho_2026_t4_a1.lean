import IChO2026Chem

/-!
# IChO 2026, Problem T4 (Q4-1) — Atomic abundance of ²³⁵U in natural uranium

**Source contract** (problem_text, Q4-1 box on `T4_page-1.png`):

* Natural uranium consists primarily of the two isotopes ²³⁵U and ²³⁸U
  (shared context, T4 header).
* Q4-1 stipulates that natural uranium consists **only** of ²³⁵U and ²³⁸U,
  with isotopic masses 235.04 a.u. and 238.05 a.u. respectively (stipulated
  constants, exact as printed).
* The standard atomic weight of uranium is not printed in the problem; it is
  taken from the pinned offline chemistry reference
  (`chemistry-constant atomic_weight U` → 238.03, CIAAW abridged 2024;
  dataset `ciaaw-abridged-2024+…+trusted-empirical-rules-v1`,
  dataset_sha256 `11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`,
  record_sha256 `18330650985fd5a061184983d3884beb83604e75446c7ec00dd6f33766382767`).
  Per the source measurement policy it is treated as the exact conventional
  olympiad input (registry uncertainty metadata is not a source measurement).

**Governing relation** (trusted_general_law: conservation of the isotope
inventory of a two-component element).  If `x` is the atomic (mole) fraction
of ²³⁵U, then `1 - x` is the fraction of ²³⁸U and the abundance-weighted mean
of the isotopic masses is the standard atomic weight:

```
x * 235.04 + (1 - x) * 238.05 = 238.03
```

Since `238.05 - 235.04 = 3.01 ≠ 0`, this linear equation has the unique
solution `x = (238.05 - 238.03) / (238.05 - 235.04) = 2/301`, so the atomic
abundance of ²³⁵U is `100·x = 200/301 % = 0.6644518… %`.

**Reporting** (uniform blind evaluation default, no precision requested in
the problem): three significant figures, ties half away from zero.  For a
value in `[0.1, 1)` the quantum is `0.001 %`; `0.6635 ≤ 200/301 < 0.6645`,
so the reported atomic abundance is `0.664 %`.

The two result contracts at the end are the answer-blind certificates: the
raw contract carries the derivation spec together with a non-degenerate
certified rational interval for the unrounded value, and the reported
contract carries the `ReportsAtQuantum` certificate for `0.664 %`.
-/

namespace IChO2026.T4.A1

/-- Problem-stipulated isotopic mass of ²³⁵U in atomic mass units, exact as
printed (problem_text, Q4-1). -/
def isotopeMassU235 : ℝ := 235.04

/-- Problem-stipulated isotopic mass of ²³⁸U in atomic mass units, exact as
printed (problem_text, Q4-1). -/
def isotopeMassU238 : ℝ := 238.05

/-- Standard atomic weight of natural uranium from the pinned offline
chemistry reference (CIAAW abridged 2024, `atomic_weight U` → 238.03;
record_sha256
`18330650985fd5a061184983d3884beb83604e75446c7ec00dd6f33766382767`).
The problem does not print this value; the pinned nominal constant is the
exact conventional input for the olympiad central-value calculation. -/
def standardAtomicWeightU : ℝ := 238.03

/-- **Two-isotope mixture model** (problem_text: natural uranium "consists
only of isotopes ²³⁵U and ²³⁸U"): `x` is the atomic fraction of ²³⁵U, the
complementary fraction `1 - x` is ²³⁸U, and the abundance-weighted mean of
the stipulated isotopic masses equals the standard atomic weight. -/
def TwoIsotopeMixture (x : ℝ) : Prop :=
  x * isotopeMassU235 + (1 - x) * isotopeMassU238 = standardAtomicWeightU

/-- Atomic fraction of ²³⁵U obtained by solving the two-isotope mixture
equation: `x = (M(²³⁸U) - A_r(U)) / (M(²³⁸U) - M(²³⁵U))`. -/
noncomputable def u235AtomicFraction : ℝ :=
  (isotopeMassU238 - standardAtomicWeightU) / (isotopeMassU238 - isotopeMassU235)

/-- Raw (unrounded) atomic abundance of ²³⁵U in natural uranium, in percent:
one hundred times the atomic fraction. -/
noncomputable def u235AbundancePercentRaw : ℝ := 100 * u235AtomicFraction

/-- The closed form is the defining quotient (no intermediate rounding). -/
theorem u235AtomicFraction_eq_quotient :
    u235AtomicFraction =
      (isotopeMassU238 - standardAtomicWeightU) / (isotopeMassU238 - isotopeMassU235) :=
  rfl

/-- The derived fraction indeed satisfies the two-isotope mixture equation. -/
theorem twoIsotopeMixture_candidate : TwoIsotopeMixture u235AtomicFraction := by
  unfold TwoIsotopeMixture u235AtomicFraction isotopeMassU235 isotopeMassU238
    standardAtomicWeightU
  norm_num

/-- The mixture equation is linear with nonzero slope
`M(²³⁵U) - M(²³⁸U) = -3.01 ≠ 0`, so its solution is unique. -/
theorem twoIsotopeMixture_unique {x : ℝ} (h : TwoIsotopeMixture x) :
    x = u235AtomicFraction := by
  have hd : (isotopeMassU238 - isotopeMassU235 : ℝ) ≠ 0 := by
    norm_num [isotopeMassU238, isotopeMassU235]
  have h' : x * isotopeMassU235 + (1 - x) * isotopeMassU238 = standardAtomicWeightU := h
  unfold u235AtomicFraction
  rw [eq_div_iff hd]
  linarith

/-- Exact rational value of the atomic fraction: `x = 2/301`. -/
theorem u235AtomicFraction_value : u235AtomicFraction = (2 : ℝ) / 301 := by
  norm_num [u235AtomicFraction, isotopeMassU235, isotopeMassU238, standardAtomicWeightU]

/-- The atomic fraction is strictly positive. -/
theorem u235AtomicFraction_pos : (0 : ℝ) < u235AtomicFraction := by
  rw [u235AtomicFraction_value]
  norm_num

/-- The atomic fraction is strictly below one. -/
theorem u235AtomicFraction_lt_one : u235AtomicFraction < 1 := by
  rw [u235AtomicFraction_value]
  norm_num

/-- Exact rational value of the raw abundance: `100·x = 200/301` percent
(`= 0.6644518…`). -/
theorem u235AbundancePercentRaw_value : u235AbundancePercentRaw = (200 : ℝ) / 301 := by
  unfold u235AbundancePercentRaw
  rw [u235AtomicFraction_value]
  norm_num

/-- Certified non-degenerate rational interval for the raw abundance, fixed
before any rounding: `1661/2500 = 0.6644 ≤ 200/301 ≤ 0.6645 = 1329/2000`
(since `200·2500 = 500000 ≥ 499961 = 1661·301` and
`200·2000 = 400000 ≤ 400029 = 1329·301`). -/
theorem u235AbundancePercentRaw_bounds :
    ((1661 : ℝ) / 2500) ≤ u235AbundancePercentRaw ∧
      u235AbundancePercentRaw ≤ ((1329 : ℝ) / 2000) := by
  rw [u235AbundancePercentRaw_value]
  constructor <;> norm_num

/-- **Raw derivation specification** for the ²³⁵U abundance: the derived
atomic fraction satisfies — and is the *unique* solution of — the printed
two-isotope weighted-mean equation, it is a genuine fraction strictly
between 0 and 1, and the raw percentage is one hundred times the fraction. -/
def RawAbundanceSpec : Prop :=
  TwoIsotopeMixture u235AtomicFraction ∧
    (∀ x : ℝ, TwoIsotopeMixture x → x = u235AtomicFraction) ∧
    (0 : ℝ) < u235AtomicFraction ∧ u235AtomicFraction < 1 ∧
    u235AbundancePercentRaw = 100 * u235AtomicFraction

/-- The derivation specification is satisfied by the derived candidate. -/
theorem rawAbundanceSpec_holds : RawAbundanceSpec :=
  ⟨twoIsotopeMixture_candidate, fun _ h => twoIsotopeMixture_unique h,
    u235AtomicFraction_pos, u235AtomicFraction_lt_one, rfl⟩

/-- **Raw result contract** (answer-blind): the derivation specification
`RawAbundanceSpec` holds for the source-derived raw expression
`u235AbundancePercentRaw = 100·(238.05 - 238.03)/(238.05 - 235.04)`, together
with the certified non-degenerate interval `1661/2500 ≤ raw ≤ 1329/2000`. -/
theorem raw_result_contract :
    (IChO2026.T4.A1.RawAbundanceSpec) ∧
      (((1661 : ℝ) / 2500) ≤ (IChO2026.T4.A1.u235AbundancePercentRaw) ∧
        (IChO2026.T4.A1.u235AbundancePercentRaw) ≤ ((1329 : ℝ) / 2000)) :=
  ⟨rawAbundanceSpec_holds, u235AbundancePercentRaw_bounds⟩

/-- **Reported result contract** (answer-blind): at the three-significant-
figure quantum `0.001 %` (ties half away from zero), the raw value
`200/301 % = 0.6644518…` is reported as `0.664 %`, since
`0.6635 = 664/1000 - 1/2000 ≤ 200/301 < 664/1000 + 1/2000 = 0.6645`. -/
theorem reported_result_contract :
    IChO2026Chem.Reporting.ReportsAtQuantum (IChO2026.T4.A1.u235AbundancePercentRaw)
      ((664 : ℝ) / 1000) ((1 : ℝ) / 1000) := by
  have hraw : (0 : ℝ) ≤ IChO2026.T4.A1.u235AbundancePercentRaw := by
    rw [u235AbundancePercentRaw_value]
    norm_num
  refine ⟨by norm_num, ⟨664, by norm_num⟩, ?_⟩
  rw [if_pos hraw, u235AbundancePercentRaw_value]
  constructor <;> norm_num

end IChO2026.T4.A1
