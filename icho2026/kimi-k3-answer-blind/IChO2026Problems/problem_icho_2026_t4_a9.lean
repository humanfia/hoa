import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T4-A9 — Urtabulak explosion: total fissions and enriched-uranium mass

## Problem contract (answer-blind, from `T4_page-3.png` / `T4_page-2.png` and the source report)

**Shared context.** The Urtabulak gas leak was ended by detonating a 30-kiloton
TNT-equivalent underground nuclear explosion; 1 ton of TNT equivalent is 4.184 GJ.
The reactor fission reaction is ²³⁵U + n → X + Y + 3n (three additional neutrons
produced). Part 4.4 stipulates BE(²³⁵U) = 7.59 MeV/nucleon and an average fission-
fragment binding energy BE(fis.) = 8.45 MeV/nucleon, with the binding energy of
free neutrons neglected. Part 4.1 stipulates the isotope mass 235.04 a.u. for ²³⁵U.

**Current subquestion (4.9).** Using the value from 4.4, calculate the total number
of fissions TN during the explosion, and the mass m (in kg) of enriched uranium
used, assuming it contained 90 % by mass of ²³⁵U and that 33 % of the ²³⁵U
underwent fission. (The 4.4 fallback ΔE = 200 MeV is *not* used: the 4.4 value is
derived inline below, per the dependency policy
`derive_in_answer_blind_run_or_use_problem_stated_fallback`.)

## Assumption / target split

*Assumptions (problem-stipulated, exact as printed; provenance `problem_text`):*
explosion yield 30 000 t TNT; 1 t TNT = 4.184 × 10⁹ J; BE data of 4.4; the
three-neutron fission stoichiometry of the shared context; isotope mass
235.04 a.u. from the 4.1 data table; enrichment 90 % by mass (numerator: ²³⁵U
component mass; denominator: total enriched-uranium mixture mass); fissioned
fraction 33 % of the ²³⁵U nuclei.
*Trusted general laws (exact SI defining constants):* 1 eV = 1.602176634 × 10⁻¹⁹ J;
N_A = 6.02214076 × 10²³ mol⁻¹.

*Inline-derived previous-part result (4.4):* nucleon conservation in
²³⁵U + n → fragments + 3n leaves 235 + 1 − 3 = 233 bound fragment nucleons, so
ΔE = 233 × 8.45 − 235 × 7.59 = 185.2 MeV per fission.

*Targets:* the unrounded TN = E_explosion / ΔE and m = TN · M(²³⁵U) /
(0.33 · 0.90 · N_A), plus their 3-significant-figure reported values under the
source reporting policy (ties half away from zero, no intermediate rounding).
-/

namespace IChO2026T4A9

open IChO2026Chem.Reporting

/-- Problem-stipulated TNT equivalence: 1 ton TNT = 4.184 GJ, in joules. -/
noncomputable def tntJoulePerTon : ℝ := 4184 * 10 ^ 6

/-- Problem-stipulated explosion yield: 30 kilotons TNT, expressed in tons. -/
noncomputable def explosionYieldTons : ℝ := 30 * 1000

/-- Total energy released by the underground explosion, in joules:
    30 000 t × 4.184 GJ/t = 1.2552 × 10¹⁴ J. -/
noncomputable def explosionEnergyJoule : ℝ := explosionYieldTons * tntJoulePerTon

/-- Binding energy per nucleon of ²³⁵U, stipulated in 4.4: 7.59 MeV. -/
noncomputable def beU235PerNucleonMeV : ℝ := 759 / 100

/-- Average binding energy per nucleon of the fission fragments,
    stipulated in 4.4: 8.45 MeV. -/
noncomputable def beFragmentPerNucleonMeV : ℝ := 845 / 100

/-- Mass number of ²³⁵U (stipulated). -/
noncomputable def nucleonsU235 : ℝ := 235

/-- Nucleons bound in the fission fragments of the shared-context reaction
    ²³⁵U + n → X + Y + 3n: nucleon conservation gives 235 + 1 − 3 = 233.
    The three emitted neutrons are free; 4.4 instructs to neglect their
    binding energy. -/
noncomputable def fragmentNucleons : ℝ := 235 + 1 - 3

/-- Energy released per fission, in MeV — the inline blind derivation of the
    T4-A4 prerequisite:
    ΔE = BE(products) − BE(reactants) = 233 × 8.45 − 235 × 7.59
    (free-neutron binding energy neglected on both sides, as instructed). -/
noncomputable def fissionEnergyMeV : ℝ :=
  fragmentNucleons * beFragmentPerNucleonMeV - nucleonsU235 * beU235PerNucleonMeV

/-- Exact SI electronvolt in joules: 1.602176634 × 10⁻¹⁹ J. -/
noncomputable def electronVoltJoule : ℝ := 1602176634 / 10 ^ 28

/-- Exact SI Avogadro constant: 6.02214076 × 10²³ mol⁻¹. -/
noncomputable def avogadroConstant : ℝ := 602214076 * 10 ^ 15

/-- Molar mass of ²³⁵U in kg/mol, from the isotope mass 235.04 a.u. stipulated
    in the 4.1 data of the shared problem text (1 a.u. ↔ 1 g/mol numerically). -/
noncomputable def molarMassU235KgPerMol : ℝ := 23504 / 100000

/-- Enrichment stipulated in 4.9: the ²³⁵U component mass is 90 % of the total
    enriched-uranium mixture mass. -/
noncomputable def enrichmentMassFraction : ℝ := 90 / 100

/-- Stipulated in 4.9: 33 % of the ²³⁵U nuclei underwent fission. -/
noncomputable def fissionedFraction : ℝ := 33 / 100

/-- Raw (unrounded) total number of fissions: the explosion energy divided by the
    per-fission energy expressed in joules. -/
noncomputable def totalFissionsRaw : ℝ :=
  explosionEnergyJoule / (fissionEnergyMeV * 10 ^ 6 * electronVoltJoule)

/-- Raw (unrounded) mass of enriched uranium used, in kg.  From the problem's
    bookkeeping, TN = 0.33 · N(²³⁵U) and N(²³⁵U) = (0.90 · m) / M(²³⁵U) · N_A,
    so m = TN · M(²³⁵U) / (0.33 · 0.90 · N_A). -/
noncomputable def enrichedUraniumMassKgRaw : ℝ :=
  totalFissionsRaw * molarMassU235KgPerMol /
    (fissionedFraction * enrichmentMassFraction * avogadroConstant)

/-- Numeric evaluation of the inline 4.4 derivation: ΔE = 185.2 MeV per fission. -/
theorem fissionEnergyMeV_value : fissionEnergyMeV = 1852 / 10 := by
  norm_num [fissionEnergyMeV, fragmentNucleons, beFragmentPerNucleonMeV,
    nucleonsU235, beU235PerNucleonMeV]

/-- Exact rational evaluation of `totalFissionsRaw`, with no intermediate
    rounding: TN = 125520 × 10³² / 2967231126168 ≈ 4.2302064 × 10²⁴ fissions.
    Here 2967231126168 = 1852 × 1602176634 collects the exact per-fission
    joule factor 185.2 × 10⁶ × 1.602176634 × 10⁻¹⁹. -/
theorem totalFissionsRaw_value :
    totalFissionsRaw = 125520 * 10 ^ 32 / 2967231126168 := by
  norm_num [totalFissionsRaw, explosionEnergyJoule, explosionYieldTons,
    tntJoulePerTon, fissionEnergyMeV, fragmentNucleons, beFragmentPerNucleonMeV,
    nucleonsU235, beU235PerNucleonMeV, electronVoltJoule]

/-- Exact rational evaluation of `enrichedUraniumMassKgRaw`, with no
    intermediate rounding:
    m = 2950222080 × 10¹⁶ / (2967231126168 × 1788575805720) ≈ 5.55899 kg,
    where 2950222080 = 125520 × 23504 and 1788575805720 = 2970 × 602214076. -/
theorem enrichedUraniumMassKgRaw_value :
    enrichedUraniumMassKgRaw
      = 2950222080 * 10 ^ 16 / (2967231126168 * 1788575805720) := by
  norm_num [enrichedUraniumMassKgRaw, totalFissionsRaw, explosionEnergyJoule,
    explosionYieldTons, tntJoulePerTon, fissionEnergyMeV, fragmentNucleons,
    beFragmentPerNucleonMeV, nucleonsU235, beU235PerNucleonMeV, electronVoltJoule,
    molarMassU235KgPerMol, fissionedFraction, enrichmentMassFraction,
    avogadroConstant]

/-- Raw-result specification covering both requested outputs: the candidate
    (TN, m) satisfies the two governing balances of the problem — the explosion
    energy balance and the ²³⁵U fission bookkeeping — and both are positive. -/
noncomputable def RawResultSpec : Prop :=
  totalFissionsRaw * (fissionEnergyMeV * 10 ^ 6 * electronVoltJoule)
      = explosionEnergyJoule ∧
    totalFissionsRaw
      = fissionedFraction * (enrichmentMassFraction * enrichedUraniumMassKgRaw /
          molarMassU235KgPerMol) * avogadroConstant ∧
    0 < totalFissionsRaw ∧
    0 < enrichedUraniumMassKgRaw

/-- 3-significant-figure reporting certificate for `totalFissionsRaw`:
    the reported value 4.23 × 10²⁴ fissions sits on the reporting lattice of
    quantum 10²² fissions. -/
theorem total_fissions_reports :
    ReportsAtQuantum totalFissionsRaw (423 * 10 ^ 22) (10 ^ 22) := by
  have hpos : (0 : ℝ) ≤ totalFissionsRaw := by
    rw [totalFissionsRaw_value]; norm_num
  unfold ReportsAtQuantum
  rw [if_pos hpos]
  refine ⟨by norm_num, ⟨423, by norm_num⟩, ?_, ?_⟩ <;>
    rw [totalFissionsRaw_value] <;> norm_num

/-- 3-significant-figure reporting certificate for `enrichedUraniumMassKgRaw`:
    the reported value 5.56 kg sits on the reporting lattice of quantum 0.01 kg. -/
theorem enriched_uranium_mass_reports :
    ReportsAtQuantum enrichedUraniumMassKgRaw (556 / 100) (1 / 100) := by
  have hpos : (0 : ℝ) ≤ enrichedUraniumMassKgRaw := by
    rw [enrichedUraniumMassKgRaw_value]; norm_num
  unfold ReportsAtQuantum
  rw [if_pos hpos]
  refine ⟨by norm_num, ⟨556, by norm_num⟩, ?_, ?_⟩ <;>
    rw [enrichedUraniumMassKgRaw_value] <;> norm_num

/-- Reported-result specification covering both requested outputs: each raw
    value is reported at its 3-significant-figure quantum
    (ties half away from zero, per the source reporting policy). -/
noncomputable def ReportedResultSpec : Prop :=
  ReportsAtQuantum totalFissionsRaw (423 * 10 ^ 22) (10 ^ 22) ∧
    ReportsAtQuantum enrichedUraniumMassKgRaw (556 / 100) (1 / 100)

/-- Machine-readable raw-result contract for the answer-blind candidate
    `icho_2026_t4_a9`; the string equation binds this theorem to the exact
    candidate payload bytes, and `RawResultSpec` is the semantic content. -/
theorem raw_result_certificate :
    ("b38aaab5fbee3a7529c7e61a486756df9d79ecfcce6bbc5eff2d1d3599798ec1" : String)
      = "b38aaab5fbee3a7529c7e61a486756df9d79ecfcce6bbc5eff2d1d3599798ec1" ∧
      IChO2026T4A9.RawResultSpec := by
  constructor
  · rfl
  · -- Energy balance, fission bookkeeping, and positivity; discharged by
    -- exact rational evaluation of the defining expressions.
    unfold IChO2026T4A9.RawResultSpec
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [totalFissionsRaw_value]
      norm_num [fissionEnergyMeV, fragmentNucleons, beFragmentPerNucleonMeV,
        nucleonsU235, beU235PerNucleonMeV, electronVoltJoule, explosionEnergyJoule,
        explosionYieldTons, tntJoulePerTon]
    · rw [totalFissionsRaw_value, enrichedUraniumMassKgRaw_value]
      norm_num [fissionedFraction, enrichmentMassFraction, molarMassU235KgPerMol,
        avogadroConstant]
    · rw [totalFissionsRaw_value]; norm_num
    · rw [enrichedUraniumMassKgRaw_value]; norm_num

/-- Machine-readable reported-result contract for the answer-blind candidate
    `icho_2026_t4_a9`; the string equation binds this theorem to the exact
    candidate payload bytes, and `ReportedResultSpec` is the semantic content. -/
theorem reported_result_certificate :
    ("8915568fa53fa4657ee6c5c97ef5029ce62f23e89868607477c64b074b5d5cd6" : String)
      = "8915568fa53fa4657ee6c5c97ef5029ce62f23e89868607477c64b074b5d5cd6" ∧
      IChO2026T4A9.ReportedResultSpec := by
  constructor
  · rfl
  · -- Both `ReportsAtQuantum` certificates, proved above.
    unfold IChO2026T4A9.ReportedResultSpec
    exact ⟨total_fissions_reports, enriched_uranium_mass_reports⟩

end IChO2026T4A9
