import IChO2026Chem

/-!
# IChO 2026, Problem T7 (Nitrogen Fixation), Subquestion 7.2

Blueprint chapter: `blueprint/src/chapters/IChO2026Problems_problem_icho_2026_t7_a2.tex`.
Source report: `reports/icho_2026/problem_icho_2026_t7_a2.source.json`
(`blind_record_sha256 = bce0874242a9cecac02b32125dda24e3ee658c9115347a63bae9a7d4f281e309`).

## Problem data (problem text and problem image `T7_page-1.png`)

Fig. 1 ammonia synthesis plant; every reaction quantitative except NH₃ formation:

* air batch fed to the partial-oxidation box: `4 N₂ + 1 O₂`;
* steam-reforming box, feed `x CH₄ + y H₂O`: `CH₄ + H₂O → CO + 3H₂`; its
  effluent is labelled `CH₄, CO, H₂` — it carries methane but no steam, so in
  this box steam is fully consumed and methane is in excess (`y` mol CH₄ react
  per air batch, `x − y` mol pass through);
* partial-oxidation box: `2CH₄ + O₂ → 2CO + 4H₂`, consuming the 1 mol O₂ of
  the air batch and hence exactly 2 mol CH₄ (no CH₄/O₂ slip into M1);
* shift converter: `CO + H₂O → CO₂ + H₂`, converting all CO (`y + 2` mol);
* `Z` = CO₂ scrubber, `CLR` = cooler liquefying NH₃; unreacted `N₂, H₂`
  recycle to the synthesis box;
* synthesis: `N₂ + 3H₂ ⇌ 2NH₃`;
* Navoiazot complex: capacity `660 000` tons NH₃ per year, overall yield
  `97.0 %`.

## Assumption / target split

* **Assumptions.** The four printed stage reactions and the printed air feed;
  quantitative conversion everywhere except ammonia formation; steady state of
  the synthesis loop with full recycle, so the fresh synthesis gas is
  stoichiometric (`H₂ : N₂ = 3 : 1`); the overall yield `η = 0.970` scales the
  ammonia output obtained from the methane feed; molar masses from the pinned
  CIAAW-abridged-2024 dataset (`M(CH₄) = 16.043 g/mol`, record
  `15ac9ec311c79f4d4d38a92c35dd7afaacc40f08349f2c5b468767c77340a1a1`;
  `M(NH₃) = 17.031 g/mol`, record
  `6034a27c5509b211ae0fab81674be1d0d63ba9c3bb8cfe336ebe72e0ab33a0b9`).
  Pinned dataset version
  `ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1`,
  dataset sha256
  `11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`.
* **Target (numeric, tons).** The annual methane mass, raw and reported to
  three significant figures (uniform blind evaluation default; ties half away
  from zero).

## Previous part 7.1, derived inline from problem-only material

The flowsheet forces M1 = {N₂, CO, H₂}, M2 = {N₂, H₂, NH₃}, and `x = y + 2`
(`MethaneSplitCondition` below); only the last feeds the present calculation.

## Derivation carried by this file

Per air batch (4 mol N₂, 1 mol O₂), with `y` mol CH₄ steam-reformed, the
hydrogen ledger is `3y + 4 + (y + 2) = 4y + 6` mol H₂ delivered to the
synthesis loop, whose stoichiometric demand is `3 × 4 = 12` mol H₂; hence
`y = 3/2`, `x = 7/2`, and `n(CH₄) : n(NH₃) = (7/2) : 8 = 7 : 16`.  The raw
annual methane mass is
`(660000 / 0.970) × (7/16) × (16.043 / 17.031) = 280411.4177…` tons,
enclosed in `[280000, 281000]` tons and reported at the `10³`-ton quantum as
`2.80 × 10⁵` tons.
-/

namespace IChO2026.T7.A2

/-! ## Species and mixtures of Fig. 1 -/

/-- The eight chemical species appearing in Fig. 1. -/
inductive Species where
  | CH4 | H2O | CO | H2 | N2 | O2 | CO2 | NH3
  deriving DecidableEq

/-- Gases contained in mixture **M1** (effluent of the partial-oxidation box
under quantitative operation): nitrogen from the air feed, plus carbon monoxide
and hydrogen from both methane legs.  (Previous part 7.1 conclusion, derived
inline.) -/
def m1Species : Finset Species := {.N2, .CO, .H2}

/-- Gases contained in mixture **M2** (synthesis effluent entering the cooler):
unreacted nitrogen and hydrogen plus the ammonia product.  (Previous part 7.1
conclusion, derived inline.) -/
def m2Species : Finset Species := {.N2, .H2, .NH3}

/-- The four elements occurring in the Fig. 1 species. -/
inductive Element where
  | C | H | O | N
  deriving DecidableEq

/-- Atom content of each species (atoms per molecule). -/
def atomCount : Species → Element → ℝ
  | .CH4, .C => 1
  | .CH4, .H => 4
  | .H2O, .H => 2
  | .H2O, .O => 1
  | .CO, .C => 1
  | .CO, .O => 1
  | .H2, .H => 2
  | .N2, .N => 2
  | .O2, .O => 2
  | .CO2, .C => 1
  | .CO2, .O => 2
  | .NH3, .N => 1
  | .NH3, .H => 3
  | _, _ => 0

/-! ## The printed stage reactions as stoichiometric coefficient vectors -/

/-- Steam reforming `CH₄ + H₂O → CO + 3H₂` (products positive, reactants
negative), printed in the first box of Fig. 1. -/
def reformingVector : Species → ℝ
  | .CH4 => -1
  | .H2O => -1
  | .CO => 1
  | .H2 => 3
  | _ => 0

/-- Partial oxidation `2CH₄ + O₂ → 2CO + 4H₂`, printed in the second box of
Fig. 1. -/
def oxidationVector : Species → ℝ
  | .CH4 => -2
  | .O2 => -1
  | .CO => 2
  | .H2 => 4
  | _ => 0

/-- Water–gas shift `CO + H₂O → CO₂ + H₂`, printed in the third box of
Fig. 1. -/
def shiftVector : Species → ℝ
  | .CO => -1
  | .H2O => -1
  | .CO2 => 1
  | .H2 => 1
  | _ => 0

/-- Ammonia synthesis `N₂ + 3H₂ → 2NH₃`, printed in the fourth box of Fig. 1 —
the only reaction the problem exempts from being quantitative. -/
def synthesisVector : Species → ℝ
  | .N2 => -1
  | .H2 => -3
  | .NH3 => 2
  | _ => 0

/-- Atom conservation of a stage-coefficient vector over the eight Fig. 1
species: for every element, the coefficient-weighted atom count vanishes. -/
def AtomConserved (v : Species → ℝ) : Prop :=
  ∀ e : Element,
    v .CH4 * atomCount .CH4 e + v .H2O * atomCount .H2O e
      + v .CO * atomCount .CO e + v .H2 * atomCount .H2 e
      + v .N2 * atomCount .N2 e + v .O2 * atomCount .O2 e
      + v .CO2 * atomCount .CO2 e + v .NH3 * atomCount .NH3 e = 0

/-- The printed steam-reforming reaction is atom-balanced. -/
theorem reformingVector_conserved : AtomConserved reformingVector := by
  intro e
  cases e <;> norm_num [atomCount, reformingVector]

/-- The printed partial-oxidation reaction is atom-balanced. -/
theorem oxidationVector_conserved : AtomConserved oxidationVector := by
  intro e
  cases e <;> norm_num [atomCount, oxidationVector]

/-- The printed shift reaction is atom-balanced. -/
theorem shiftVector_conserved : AtomConserved shiftVector := by
  intro e
  cases e <;> norm_num [atomCount, shiftVector]

/-- The printed ammonia-synthesis reaction is atom-balanced. -/
theorem synthesisVector_conserved : AtomConserved synthesisVector := by
  intro e
  cases e <;> norm_num [atomCount, synthesisVector]

/-! ## Flowsheet stoichiometry per air batch (4 mol N₂ + 1 mol O₂) -/

/-- Hydrogen (mol H₂ per air batch) leaving the steam-reforming box when
`y` mol CH₄ are reformed: `CH₄ + H₂O → CO + 3H₂` delivers `3y`. -/
def h2FromReforming (y : ℝ) : ℝ := 3 * y

/-- Hydrogen (mol H₂ per air batch) from partial oxidation: the 1 mol O₂ of the
air batch converts 2 mol CH₄, and `2CH₄ + O₂ → 2CO + 4H₂` delivers `4`. -/
def h2FromOxidation : ℝ := 4

/-- Extra hydrogen (mol per air batch) from the shift converter acting on all
CO: `y` mol from reforming plus `2` mol from oxidation, so `y + 2`. -/
def h2FromShift (y : ℝ) : ℝ := y + 2

/-- Hydrogen demand of the synthesis loop per air batch: 4 mol N₂ require
`3 × 4 = 12` mol H₂ (steady state with full recycle; `N₂ + 3H₂ → 2NH₃`). -/
def h2SynthesisDemand : ℝ := 3 * 4

/-- The Fig. 1 hydrogen ledger at steady state: hydrogen delivered to the
synthesis loop equals the stoichiometric demand of the 4 mol N₂. -/
def HydrogenBalance (y : ℝ) : Prop :=
  h2FromReforming y + h2FromOxidation + h2FromShift y = h2SynthesisDemand

/-- Methane split (previous part 7.1, derived): of the `x` mol CH₄ fed per air
batch, `y` mol are steam-reformed and the remaining `x − y` mol must equal the
2 mol CH₄ consumed by the 1 mol O₂ of the air feed (quantitative conversion,
no CH₄ or O₂ slip into M1). -/
def MethaneSplitCondition (x y : ℝ) : Prop := x - y = 2

/-- The steam-reforming extent forced by the Fig. 1 hydrogen ledger, in mol
CH₄ per air batch.  `steamReformExtent_balance` and `steamReformExtent_unique`
show this is exactly the ledger's unique solution. -/
noncomputable def steamReformExtent : ℝ := 3 / 2

/-- The hydrogen ledger is linear with a unique solution. -/
theorem steamReformExtent_unique (y : ℝ) (h : HydrogenBalance y) :
    y = steamReformExtent := by
  unfold HydrogenBalance h2FromReforming h2FromOxidation h2FromShift
    h2SynthesisDemand at h
  unfold steamReformExtent
  linarith

/-- The candidate extent satisfies the hydrogen ledger. -/
theorem steamReformExtent_balance : HydrogenBalance steamReformExtent := by
  unfold HydrogenBalance h2FromReforming h2FromOxidation h2FromShift
    h2SynthesisDemand steamReformExtent
  norm_num

/-- The flowsheet feeds are forced: `x = 7/2` and `y = 3/2` per air batch. -/
theorem flowsheet_feeds_forced {x y : ℝ} :
    MethaneSplitCondition x y ∧ HydrogenBalance y ↔ x = 7 / 2 ∧ y = 3 / 2 := by
  constructor
  · rintro ⟨hxy, hy⟩
    have hy' : y = steamReformExtent := steamReformExtent_unique y hy
    refine ⟨?_, by rw [hy']; rfl⟩
    unfold MethaneSplitCondition at hxy
    rw [hy'] at hxy
    unfold steamReformExtent at hxy
    linarith
  · rintro ⟨hx, hy⟩
    rw [hx, hy]
    refine ⟨?_, ?_⟩
    · unfold MethaneSplitCondition; norm_num
    · rw [show (3 / 2 : ℝ) = steamReformExtent from rfl]
      exact steamReformExtent_balance

/-- Total methane feed per air batch: the steam-reformed part plus the 2 mol
CH₄ consumed by the air batch's oxygen. -/
noncomputable def methanePerAirBatch : ℝ := steamReformExtent + 2

/-- Theoretical ammonia per air batch: 4 mol N₂ give `2 × 4 = 8` mol NH₃. -/
def ammoniaPerAirBatch : ℝ := 2 * 4

/-- The methane : ammonia mole ratio forced by the Fig. 1 flowsheet. -/
noncomputable def methanePerAmmoniaMoleRatio : ℝ := methanePerAirBatch / ammoniaPerAirBatch

/-- The flowsheet forces `n(CH₄) : n(NH₃) = 7 : 16`. -/
theorem methanePerAmmoniaMoleRatio_value : methanePerAmmoniaMoleRatio = 7 / 16 := by
  unfold methanePerAmmoniaMoleRatio methanePerAirBatch ammoniaPerAirBatch
    steamReformExtent
  norm_num

/-! ## Problem-stipulated plant data and pinned molar masses -/

/-- Navoiazot capacity: `660 000` tons of ammonia per year (problem text). -/
def nh3AnnualCapacityTons : ℝ := 660000

/-- Overall yield of the complex: `97.0 %` (problem text). -/
def overallYield : ℝ := 0.970

/-- Molar mass of methane, `16.043 g/mol`, from the pinned CIAAW-abridged-2024
dataset (CLI record `15ac9ec311c79f4d4d38a92c35dd7afaacc40f08349f2c5b468767c77340a1a1`). -/
def molarMassCH4 : ℝ := 16.043

/-- Molar mass of ammonia, `17.031 g/mol`, from the pinned CIAAW-abridged-2024
dataset (CLI record `6034a27c5509b211ae0fab81674be1d0d63ba9c3bb8cfe336ebe72e0ab33a0b9`). -/
def molarMassNH3 : ℝ := 17.031

/-- Raw (unrounded) annual methane mass in tons: the ammonia capacity corrected
for the 97.0 % overall yield, converted by the forced 7 : 16 mole ratio and the
pinned molar-mass ratio. -/
noncomputable def rawAnnualMethaneMassTons : ℝ := nh3AnnualCapacityTons / overallYield * methanePerAmmoniaMoleRatio * (molarMassCH4 / molarMassNH3)

/-- Strict rational enclosure of the raw methane mass, fixed from the raw
formula before any rounding (width one reporting quantum, `10³` tons). -/
theorem rawAnnualMethaneMassTons_bounds :
    (280000 : ℝ) ≤ rawAnnualMethaneMassTons ∧ rawAnnualMethaneMassTons ≤ 281000 := by
  constructor <;>
    norm_num [rawAnnualMethaneMassTons, nh3AnnualCapacityTons, overallYield,
      methanePerAmmoniaMoleRatio, methanePerAirBatch, ammoniaPerAirBatch,
      steamReformExtent, molarMassCH4, molarMassNH3]

/-! ## Derivation specification and result contracts -/

/-- Raw-result derivation specification: the hydrogen ledger of the Fig. 1
flowsheet has the unique solution `steamReformExtent`; the methane : ammonia
mole ratio is exactly `7 : 16`; the raw carrier is assembled from the named
problem data (capacity, overall yield, mole ratio, pinned molar masses) without
intermediate rounding; and the problem-data constants are exactly as printed. -/
def AnnualMethaneMassSpec : Prop :=
  HydrogenBalance steamReformExtent
    ∧ (∀ y : ℝ, HydrogenBalance y → y = steamReformExtent)
    ∧ methanePerAmmoniaMoleRatio = 7 / 16
    ∧ rawAnnualMethaneMassTons =
        nh3AnnualCapacityTons / overallYield * methanePerAmmoniaMoleRatio *
          (molarMassCH4 / molarMassNH3)
    ∧ nh3AnnualCapacityTons = 660000
    ∧ overallYield = 0.970
    ∧ molarMassCH4 = 16.043
    ∧ molarMassNH3 = 17.031

/-- The derivation specification holds for the Fig. 1 model. -/
theorem annualMethaneMassSpec_holds : AnnualMethaneMassSpec :=
  ⟨steamReformExtent_balance, steamReformExtent_unique,
    methanePerAmmoniaMoleRatio_value, rfl, rfl, rfl, rfl, rfl⟩

/-- Raw-result contract: the derivation specification together with the
certified rational enclosure of the raw annual methane mass. -/
theorem annual_methane_mass_raw_contract :
    (IChO2026.T7.A2.AnnualMethaneMassSpec) ∧
      ((280000 : ℝ) ≤ (IChO2026.T7.A2.rawAnnualMethaneMassTons) ∧
        (IChO2026.T7.A2.rawAnnualMethaneMassTons) ≤ (281000 : ℝ)) :=
  ⟨annualMethaneMassSpec_holds, rawAnnualMethaneMassTons_bounds.1,
    rawAnnualMethaneMassTons_bounds.2⟩

/-- Reported-result contract: the raw annual methane mass reported at the
three-significant-figure quantum `10³` tons is `2.80 × 10⁵` tons (ties half
away from zero; `279500 ≤ raw < 280500`). -/
theorem annual_methane_mass_reported_contract :
    IChO2026Chem.Reporting.ReportsAtQuantum
      (IChO2026.T7.A2.rawAnnualMethaneMassTons) (280000 : ℝ) (1000 : ℝ) := by
  refine ⟨by norm_num, ⟨280, by norm_num⟩, ?_⟩
  have hraw_nonneg : (0 : ℝ) ≤ IChO2026.T7.A2.rawAnnualMethaneMassTons := by
    norm_num [rawAnnualMethaneMassTons, nh3AnnualCapacityTons, overallYield,
      methanePerAmmoniaMoleRatio, methanePerAirBatch, ammoniaPerAirBatch,
      steamReformExtent, molarMassCH4, molarMassNH3]
  rw [if_pos hraw_nonneg]
  constructor <;>
    norm_num [rawAnnualMethaneMassTons, nh3AnnualCapacityTons, overallYield,
      methanePerAmmoniaMoleRatio, methanePerAirBatch, ammoniaPerAirBatch,
      steamReformExtent, molarMassCH4, molarMassNH3]

end IChO2026.T7.A2
