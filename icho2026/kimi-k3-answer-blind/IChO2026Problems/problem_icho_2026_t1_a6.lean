import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T1, Part A6 — the mysterious stone: thermogravimetry

Source (problem-only inputs): `icho_2026_source/image/T1_page-3.png` (Part 2
statement and parts 1.4/1.5, scheme Stone → C·xH₂O, E → F → G) and
`icho_2026_source/image/T1_page-4.png` (thermogravimetric data and the text of
question 1.6).  Subquestion T1-A6 asks:

  "Determine the chemical formulae of the **stone** and compound **H** using
   thermogravimetric data."

## Problem evidence used (with locators)

* T1 page 3: the stone is a *stoichiometric compound*; it dissolves in dilute
  HNO₃ and, at pH ≈ 4 with added NaF, precipitates C·xH₂O containing 39.16 %
  water; anhydrous C with excess NaF gives D (32.85 % Na, 12.85 % metal Q),
  used in the industrial production of Q.
* T1 page 3: the stone was found in a *coal deposit*; it *contains the anion
  of a highly symmetrical acid F*; F is made by oxidising E (11.18 % H,
  six-fold symmetry axis) with acidic KMnO₄; F with P₂O₅ gives the binary
  compound G (49.98 % O, three-fold symmetry axis).
* T1 page 4: thermogravimetry in *open air* — a 10.00 g sample loses mass
  from ≈ 100 °C, the loss stops at 5.75 g at 200 °C, a second drop is
  observed at 400 °C, and a final mass of 1.50 g of compound H remains
  constant at higher temperatures.

## Certified prior-part results used (controller-bound typed exports)

Receipt `db7b4d1661baa0888084096ff824b0de43d40d6cf78dca570d9672634482673c`
(scope `one_a6_consumer_from_reviewed_a4_a5`, producers compiled with zero
sorry and both reviewer gates passed):

* T1-A4: metal Q is aluminium (Z = 13); C·xH₂O is AlF₃·3H₂O; D is Na₃AlF₆.
  Since Na and F enter only with the added NaF reagent, the stone itself is
  the aluminium source of the precipitate.
* T1-A5: acid F is benzene-1,2,3,4,5,6-hexacarboxylic (mellitic) acid
  C₆(COOH)₆ = C₁₂H₆O₁₂; its (fully deprotonated) anion is mellitate
  C₁₂O₁₂⁶⁻.  (E = C₁₂H₁₈ and G = C₁₂O₉ are contextual for A6.)

## Pinned constants (offline registry, no network)

Dataset version tag
`ciaaw-abridged-2024 + ame2020-subset + archon-templates-v1 +
contest-interpretation-v1 + trusted-empirical-rules-v1`, with pinned
`dataset_sha256 = 11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`:

* H = 1.0080 (record `8e5f2e512d11f6c3409197956a4f015f6144f43057a286107064436c64b4bce5`)
* C = 12.011 (record `0f558fc72d4299d061e9d29f394ebed43fc8246f7dbdb402bbb2a338cfbe4b8a`)
* O = 15.999 (record `d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588`)
* Al = 26.982 (record `bdb840d02b2eb42be07e27b58fc76501786c75d0a321d38f76dae129c84f5e7f`)

Cross-check receipts: molar mass Al₂C₁₂O₁₂ = 390.084 g/mol (record
`f6fd6bcb2ccf4e66cd56666b1bb0eb9edd902080c58ec0789a4ba02b6264d4ef`),
Al₂O₃ = 101.961 g/mol (record
`752c671ce5f307f0b0169c8629a2e47067ac86ce2e3d497bbc593fa9c9501186`).

## Staged-transformation classification

Both TGA stages are `quantitative_material_stage`s for this target: the
requested formulae consume the stage-1 water ledger and the stage-2
aluminium-retention ledger.  The problem supplies the closed contest-model
cues: one stoichiometric sample, stated temperature stages and atmosphere
(open air), a named single final compound H with a stable high-temperature
plateau, and an instruction to determine formulae from the TGA data.  The
species domain is closed to problem-evidenced constituents: Al³⁺ (from the
stone, via T1-A4), the mellitate anion C₁₂O₁₂⁶⁻ (the anion of F, via T1-A5),
hydration water (stage 1, ≈100–200 °C), atmospheric O₂/CO₂ (stage 2), and a
binary aluminium-oxide residue H.  No anonymous streams are introduced.

The baseline registry rule `mellite_ideal_stoichiometry` (record
`4c5ba1e520b8c34862ff33cbbcf98e47c7e4a20879bb8a6d5ad1394a93311e5e`, Acta
Cryst. B29 (1973) 26–31, DOI 10.1107/S0567740873001925) states ideal mellite
= Al₂[C₆(COO)₆]·16H₂O.  It is recorded here only as *post-derivation
corroboration*: its applicability condition "the phase has been independently
established as crystalline mellite" is not problem-evidenced (its own
exclusions forbid identification from coal-deposit occurrence alone), so the
derivation below stands on the TGA ledgers, charge neutrality and the
certified priors only.
-/

namespace IChO2026T1A6

/-- The elements tracked for the T1 Part 2 stone chemistry. -/
inductive StoneElement
  | H
  | C
  | O
  | Al

/-- Abridged standard atomic weights (CIAAW 2024) from the pinned offline
registry; see the module header for the dataset and record hashes. -/
def atomicWeight : StoneElement → ℝ
  | .H => 1.0080
  | .C => 12.011
  | .O => 15.999
  | .Al => 26.982

/-- A formula unit over the tracked elements, as atom counts. -/
structure Formula where
  numH : ℕ
  numC : ℕ
  numO : ℕ
  numAl : ℕ

/-- Count of a single element in a formula. -/
def Formula.count (f : Formula) : StoneElement → ℕ
  | .H => f.numH
  | .C => f.numC
  | .O => f.numO
  | .Al => f.numAl

/-- Molar mass (g mol⁻¹) from the pinned abridged standard atomic weights. -/
noncomputable def Formula.molarMass (f : Formula) : ℝ :=
  (f.numH : ℝ) * atomicWeight StoneElement.H +
    (f.numC : ℝ) * atomicWeight StoneElement.C +
      (f.numO : ℝ) * atomicWeight StoneElement.O +
        (f.numAl : ℝ) * atomicWeight StoneElement.Al

/-- Water, H₂O (hydration water of the stone; stage-1 volatile). -/
def water : Formula := ⟨2, 0, 1, 0⟩

/-- The mellitate anion C₁₂O₁₂, the fully deprotonated anion of the hexabasic
acid F = mellitic acid C₁₂H₆O₁₂ (certified prior T1-A5). -/
def mellitateAnion : Formula := ⟨0, 12, 12, 0⟩

/-- The charge-neutral anhydrous core of the stone, Al₂C₁₂O₁₂
(two Al³⁺ per mellitate C₁₂O₁₂⁶⁻). -/
def aluminiumMellitateCore : Formula := ⟨0, 12, 12, 2⟩

/-- Aluminium oxide Al₂O₃ (charge-neutral simplest binary oxide of Al³⁺/O²⁻). -/
def alumina : Formula := ⟨0, 0, 3, 2⟩

/-- Carbon dioxide, CO₂ (stage-2 volatile product of the mellitate carbon in
open air). -/
def carbonDioxide : Formula := ⟨0, 1, 2, 0⟩

/-- Dioxygen, O₂ (stage-2 reactant from the open-air atmosphere). -/
def dioxygen : Formula := ⟨0, 0, 2, 0⟩

/-- Charge of the aluminium(III) cation in units of the elementary charge
(ordinary group-13 valence). -/
def aluminiumCationCharge : ℕ := 3

/-- Charge magnitude of the mellitate anion C₁₂O₁₂⁶⁻, the fully deprotonated
anion of the hexabasic acid F. -/
def mellitateAnionCharge : ℕ := 6

/-- Charge magnitude of the oxide anion O²⁻. -/
def oxideAnionCharge : ℕ := 2

/-- Unfolded molar mass of an explicit formula constructor: the pinned
abridged atomic weights applied to the four atom counts. -/
private theorem molarMass_mk (h c o a : ℕ) :
    (Formula.mk h c o a).molarMass =
      (h : ℝ) * 1.0080 + (c : ℝ) * 12.011 + (o : ℝ) * 15.999 + (a : ℝ) * 26.982 :=
  rfl

/-- Molar mass of water equals the pinned value 18.015 g mol⁻¹. -/
theorem water_molarMass : water.molarMass = 18.015 := by
  rw [show water = ⟨2, 0, 1, 0⟩ from rfl, molarMass_mk]
  norm_num

/-- Molar mass of the anhydrous stone core equals the pinned registry
cross-check 390.084 g mol⁻¹. -/
theorem aluminiumMellitateCore_molarMass :
    aluminiumMellitateCore.molarMass = 390.084 := by
  rw [show aluminiumMellitateCore = ⟨0, 12, 12, 2⟩ from rfl, molarMass_mk]
  norm_num

/-- Molar mass of alumina equals the pinned registry cross-check
101.961 g mol⁻¹. -/
theorem alumina_molarMass : alumina.molarMass = 101.961 := by
  rw [show alumina = ⟨0, 0, 3, 2⟩ from rfl, molarMass_mk]
  norm_num

/-- Closed candidate domain for the stone (problem evidence only):
a stoichiometric hydrated salt of `al` aluminium(III) cations and `mel`
mellitate anions per formula unit with `wat` waters of crystallisation,
charge-neutral and written in the simplest cation : anion ratio. -/
structure StoneCandidate where
  al : ℕ
  mel : ℕ
  wat : ℕ
  al_pos : 1 ≤ al
  mel_pos : 1 ≤ mel
  wat_pos : 1 ≤ wat
  charge_neutral : aluminiumCationCharge * al = mellitateAnionCharge * mel
  simplest_ratio : Nat.Coprime al mel

/-- The anhydrous salt of a stone candidate. -/
def StoneCandidate.anhydrous (s : StoneCandidate) : Formula :=
  ⟨0, 12 * s.mel, 12 * s.mel, s.al⟩

/-- The full formula of a stone candidate, including hydration water. -/
def StoneCandidate.fullFormula (s : StoneCandidate) : Formula :=
  ⟨2 * s.wat, 12 * s.mel, 12 * s.mel + s.wat, s.al⟩

/-- Closed candidate domain for the final residue H (problem evidence only):
a binary aluminium oxide `Al_al O_ox`, charge-neutral, in the simplest
integer ratio; the stone's aluminium is fully retained in the residue while
the organic anion burns away in open air. -/
structure ResidueCandidate where
  al : ℕ
  ox : ℕ
  al_pos : 1 ≤ al
  charge_neutral : aluminiumCationCharge * al = oxideAnionCharge * ox
  simplest_ratio : Nat.Coprime al ox

/-- The formula of a residue candidate. -/
def ResidueCandidate.formula (r : ResidueCandidate) : Formula :=
  ⟨0, 0, r.ox, r.al⟩

/-- True masses of the thermogravimetric run on the stone in open air.
Stage labels (not quantitative inputs): onset ≈ 100 °C, first plateau at
200 °C, second drop at 400 °C, residue constant at higher temperatures. -/
structure TGARecord where
  initialMass : ℝ
  plateauMass : ℝ
  residueMass : ℝ

/-- The displayed masses of the run — 10.00 g, 5.75 g and 1.50 g, each with
last displayed quantum 0.01 g — constrain the true masses to the closed
half-quantum intervals (source measurement policy). -/
def TGARecord.MeasuredConsistent (t : TGARecord) : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement t.initialMass 10.00 0.01 ∧
    IChO2026Chem.Reporting.ConsistentMeasurement t.plateauMass 5.75 0.01 ∧
      IChO2026Chem.Reporting.ConsistentMeasurement t.residueMass 1.50 0.01

/-- Stage-1 ledger (≈100–200 °C, complete dehydration): the 200 °C plateau is
the anhydrous salt, and only the hydration water has left the sample.
Cross-multiplied form of `plateau = initial · M(anhydrous) / M(hydrate)`. -/
def Stage1Ledger (s : StoneCandidate) (t : TGARecord) : Prop :=
  t.plateauMass * s.fullFormula.molarMass = t.initialMass * s.anhydrous.molarMass

/-- Stage-2 ledger (≈400 °C, open air): the mellitate burns away and every
aluminium atom of the plateau solid is retained in the residue H.
Cross-multiplied form of
`residue = plateau · (s.al / r.al) · M(residue formula) / M(anhydrous)`. -/
def Stage2Ledger (s : StoneCandidate) (r : ResidueCandidate)
    (t : TGARecord) : Prop :=
  t.residueMass * (r.al : ℝ) * s.anhydrous.molarMass =
    t.plateauMass * (s.al : ℝ) * r.formula.molarMass

/-- The stage-2 open-air combustion of the anhydrous core in integer
coefficients, 2 Al₂C₁₂O₁₂ + 15 O₂ → 2 Al₂O₃ + 24 CO₂, balances on every
tracked element. -/
def Stage2CombustionBalanced : Prop :=
  ∀ e : StoneElement,
    2 * aluminiumMellitateCore.count e + 15 * dioxygen.count e =
      2 * alumina.count e + 24 * carbonDioxide.count e

/-- Charge neutrality and the simplest-ratio convention force the anhydrous
core of any stone candidate to Al₂C₁₂O₁₂ (two Al³⁺ per mellitate). -/
theorem stone_core_forced (s : StoneCandidate) : s.al = 2 ∧ s.mel = 1 := by
  have hcn : 3 * s.al = 6 * s.mel := s.charge_neutral
  have hal : s.al = 2 * s.mel := by omega
  have hcop := s.simplest_ratio
  rw [hal] at hcop
  have hdvd : s.mel ∣ Nat.gcd (2 * s.mel) s.mel :=
    Nat.dvd_gcd (dvd_mul_left s.mel 2) (dvd_refl _)
  rw [Nat.Coprime.gcd_eq_one hcop] at hdvd
  have hm1 : s.mel = 1 := Nat.dvd_one.mp hdvd
  exact ⟨by omega, hm1⟩

/-- The stage-1 dehydration ledger, applied uniformly over the displayed-mass
intervals, forces exactly 16 waters of crystallisation: the plateau fraction
`M(anhydrous) / M(hydrate)` is strictly antitone in `wat`, the measured ratio
interval `[5.745/10.005, 5.755/9.995]` contains its value at `wat = 16` but
excludes the values at `wat = 15` and `wat = 17`. -/
theorem stone_waters_forced (s : StoneCandidate) (t : TGARecord)
    (hm : t.MeasuredConsistent) (h1 : Stage1Ledger s t) : s.wat = 16 := by
  obtain ⟨hal, hmel⟩ := stone_core_forced s
  obtain ⟨⟨_, hi⟩, ⟨_, hp⟩, _⟩ := hm
  have hi_lo : (9.995 : ℝ) ≤ t.initialMass := by
    have h := (abs_le.mp hi).1
    linarith
  have hi_hi : t.initialMass ≤ (10.005 : ℝ) := by
    have h := (abs_le.mp hi).2
    linarith
  have hp_lo : (5.745 : ℝ) ≤ t.plateauMass := by
    have h := (abs_le.mp hp).1
    linarith
  have hp_hi : t.plateauMass ≤ (5.755 : ℝ) := by
    have h := (abs_le.mp hp).2
    linarith
  have hMfull : s.fullFormula.molarMass = 390.084 + 18.015 * (s.wat : ℝ) := by
    have hff : s.fullFormula = ⟨2 * s.wat, 12 * s.mel, 12 * s.mel + s.wat, s.al⟩ := rfl
    rw [hff, molarMass_mk, hmel, hal]
    push_cast
    linarith
  have hManh : s.anhydrous.molarMass = 390.084 := by
    have han : s.anhydrous = ⟨0, 12 * s.mel, 12 * s.mel, s.al⟩ := rfl
    rw [han, molarMass_mk, hmel, hal]
    norm_num
  unfold Stage1Ledger at h1
  rw [hMfull, hManh] at h1
  have hXpos : (0 : ℝ) < 390.084 + 18.015 * (s.wat : ℝ) := by
    have hw1 : (1 : ℝ) ≤ (s.wat : ℝ) := by exact_mod_cast s.wat_pos
    linarith
  have hle16 : s.wat ≤ 16 := by
    by_contra hcon
    have hw17 : (17 : ℝ) ≤ (s.wat : ℝ) := by exact_mod_cast (by omega : 17 ≤ s.wat)
    have hXge : (696.339 : ℝ) ≤ 390.084 + 18.015 * (s.wat : ℝ) := by
      have hmul : (18.015 : ℝ) * 17 ≤ 18.015 * (s.wat : ℝ) :=
        mul_le_mul_of_nonneg_left hw17 (by norm_num)
      linarith
    have hLHS : (5.745 : ℝ) * 696.339 ≤
        t.plateauMass * (390.084 + 18.015 * (s.wat : ℝ)) :=
      mul_le_mul hp_lo hXge (by norm_num) (le_trans (by norm_num) hp_lo)
    have hRHS : t.initialMass * 390.084 ≤ (10.005 : ℝ) * 390.084 :=
      mul_le_mul_of_nonneg_right hi_hi (by norm_num)
    have hc1 : (5.745 : ℝ) * 696.339 = 4000.467555 := by norm_num
    have hc2 : (10.005 : ℝ) * 390.084 = 3902.79042 := by norm_num
    linarith [h1, hLHS, hRHS]
  have hge16 : 16 ≤ s.wat := by
    by_contra hcon
    have hw15 : (s.wat : ℝ) ≤ 15 := by exact_mod_cast (by omega : s.wat ≤ 15)
    have hXle : (390.084 : ℝ) + 18.015 * (s.wat : ℝ) ≤ 660.309 := by
      have hmul : (18.015 : ℝ) * (s.wat : ℝ) ≤ 18.015 * 15 :=
        mul_le_mul_of_nonneg_left hw15 (by norm_num)
      linarith
    have hLHS : t.plateauMass * (390.084 + 18.015 * (s.wat : ℝ)) ≤
        (5.755 : ℝ) * 660.309 :=
      mul_le_mul hp_hi hXle hXpos.le (by norm_num)
    have hRHS : (9.995 : ℝ) * 390.084 ≤ t.initialMass * 390.084 :=
      mul_le_mul_of_nonneg_right hi_lo (by norm_num)
    have hc1 : (5.755 : ℝ) * 660.309 = 3800.078295 := by norm_num
    have hc2 : (9.995 : ℝ) * 390.084 = 3898.88958 := by norm_num
    linarith [h1, hLHS, hRHS]
  omega

/-- Charge neutrality (Al³⁺/O²⁻) and the simplest-ratio convention force any
residue candidate to Al₂O₃. -/
theorem residue_forced (r : ResidueCandidate) : r.al = 2 ∧ r.ox = 3 := by
  have hcn : 3 * r.al = 2 * r.ox := r.charge_neutral
  have h2 : 2 ∣ r.al := by
    have h : 2 ∣ 3 * r.al := by
      rw [hcn]
      exact dvd_mul_right 2 r.ox
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h23 | h2al
    · norm_num at h23
    · exact h2al
  obtain ⟨k, hk⟩ := h2
  have hox : r.ox = 3 * k := by omega
  have hcop := r.simplest_ratio
  rw [hk, hox] at hcop
  have hdvd : k ∣ Nat.gcd (2 * k) (3 * k) :=
    Nat.dvd_gcd (dvd_mul_left k 2) (dvd_mul_left k 3)
  rw [Nat.Coprime.gcd_eq_one hcop] at hdvd
  have hk1 : k = 1 := Nat.dvd_one.mp hdvd
  exact ⟨by omega, by omega⟩

/-- The stage-2 combustion equation balances on every tracked element. -/
theorem stage2_combustion_balanced : Stage2CombustionBalanced := by
  intro e
  cases e <;> decide

/-- The derived stone candidate Al₂C₁₂O₁₂·16H₂O. -/
def stoneCandidateDerived : StoneCandidate :=
  ⟨2, 1, 16, by decide, by decide, by decide, by decide, by decide⟩

/-- The derived residue candidate Al₂O₃. -/
def residueCandidateDerived : ResidueCandidate :=
  ⟨2, 3, by decide, by decide, by decide⟩

/-- Molar mass of the derived stone Al₂C₁₂O₁₂·16H₂O is 678.324 g mol⁻¹. -/
theorem stoneCandidateDerived_molarMass :
    stoneCandidateDerived.fullFormula.molarMass = 678.324 := by
  have h : stoneCandidateDerived.fullFormula = ⟨32, 12, 28, 2⟩ := rfl
  rw [h, molarMass_mk]
  norm_num

/-- Non-vacuity: some true-mass choice inside the displayed intervals realises
both stage ledgers for the derived candidates (equivalently, the displayed
masses 10.00 g, 5.75 g, 1.50 g are consistent with the ideal stoichiometric
predictions 5.7507 g and 1.5029 g up to the half-quantum intervals). -/
theorem consistent_run_exists :
    ∃ t : TGARecord, t.MeasuredConsistent ∧
      Stage1Ledger stoneCandidateDerived t ∧
        Stage2Ledger stoneCandidateDerived residueCandidateDerived t := by
  have hanh : stoneCandidateDerived.anhydrous.molarMass = 390.084 := by
    have h : stoneCandidateDerived.anhydrous = ⟨0, 12, 12, 2⟩ := rfl
    rw [h, molarMass_mk]
    norm_num
  have hres : residueCandidateDerived.formula.molarMass = 101.961 := by
    have h : residueCandidateDerived.formula = ⟨0, 0, 3, 2⟩ := rfl
    rw [h, molarMass_mk]
    norm_num
  refine ⟨⟨10, 10 * 390.084 / 678.324, 10 * 101.961 / 678.324⟩,
    ⟨⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩⟩, ?_, ?_⟩
  · change |(10 : ℝ) - 10.00| ≤ 0.01 / 2
    norm_num
  · change |10 * 390.084 / 678.324 - 5.75| ≤ 0.01 / 2
    rw [abs_le]
    constructor <;> norm_num
  · change |10 * 101.961 / 678.324 - 1.50| ≤ 0.01 / 2
    rw [abs_le]
    constructor <;> norm_num
  · change 10 * 390.084 / 678.324 * stoneCandidateDerived.fullFormula.molarMass =
      10 * stoneCandidateDerived.anhydrous.molarMass
    rw [stoneCandidateDerived_molarMass, hanh]
    norm_num
  · change 10 * 101.961 / 678.324 * ((2 : ℕ) : ℝ) *
        stoneCandidateDerived.anhydrous.molarMass =
      10 * 390.084 / 678.324 * ((2 : ℕ) : ℝ) *
        residueCandidateDerived.formula.molarMass
    rw [hanh, hres]
    norm_num

/-- Raw specification of both requested outputs of T1-A6, derived end-to-end
from the problem-only TGA model: every measurement-consistent stone candidate
is Al₂C₁₂O₁₂·16H₂O (two Al, one mellitate, sixteen waters), every residue
candidate is Al₂O₃, the stage-2 combustion balances, and the identification
is non-vacuous. -/
def T1A6RawSpec : Prop :=
  (∀ s : StoneCandidate, ∀ t : TGARecord, t.MeasuredConsistent →
      Stage1Ledger s t → s.al = 2 ∧ s.mel = 1 ∧ s.wat = 16) ∧
    (∀ r : ResidueCandidate, r.al = 2 ∧ r.ox = 3) ∧
      Stage2CombustionBalanced ∧
        ∃ t : TGARecord, t.MeasuredConsistent ∧
          Stage1Ledger stoneCandidateDerived t ∧
            Stage2Ledger stoneCandidateDerived residueCandidateDerived t

/-- Reported specification of both requested outputs of T1-A6: every
measurement-consistent stone candidate has the full formula
Al₂H₃₂C₁₂O₂₈ = Al₂C₁₂O₁₂·16H₂O, every residue candidate has the formula
Al₂O₃, and a measurement-consistent run realising both ledgers exists. -/
def T1A6ReportedSpec : Prop :=
  (∀ s : StoneCandidate, ∀ t : TGARecord, t.MeasuredConsistent →
      Stage1Ledger s t → s.fullFormula = ⟨32, 12, 28, 2⟩) ∧
    (∀ r : ResidueCandidate, r.formula = ⟨0, 0, 3, 2⟩) ∧
      ∃ t : TGARecord, t.MeasuredConsistent ∧
        Stage1Ledger stoneCandidateDerived t ∧
          Stage2Ledger stoneCandidateDerived residueCandidateDerived t

/-- The raw specification holds for the derived candidates (the proof is supplied by the theorem below). -/
theorem t1a6RawSpec_holds : T1A6RawSpec := by
  refine ⟨fun s t hm h1 => ?_, fun r => residue_forced r,
    stage2_combustion_balanced, consistent_run_exists⟩
  obtain ⟨hal, hmel⟩ := stone_core_forced s
  exact ⟨hal, hmel, stone_waters_forced s t hm h1⟩

/-- The reported specification holds for the derived candidates
(the proof is supplied by the theorem below). -/
theorem t1a6ReportedSpec_holds : T1A6ReportedSpec := by
  refine ⟨fun s t hm h1 => ?_, fun r => ?_, consistent_run_exists⟩
  · obtain ⟨hal, hmel⟩ := stone_core_forced s
    have hwat := stone_waters_forced s t hm h1
    have hff : s.fullFormula = ⟨2 * s.wat, 12 * s.mel, 12 * s.mel + s.wat, s.al⟩ := rfl
    rw [hff, hal, hmel, hwat]
    try rfl
  · obtain ⟨hal, hox⟩ := residue_forced r
    have hfr : r.formula = ⟨0, 0, r.ox, r.al⟩ := rfl
    rw [hfr, hal, hox]
    try rfl

/-- Answer-blind result contract, raw role: the payload digest binds the
candidate record, and the semantic specification is `T1A6RawSpec`. -/
theorem t1a6_raw_result_contract :
    ("90bea7c96eae280cb4ff2d36fa8d93f1ed8525402110a6447fe87f479a1920e8" : String)
      = "90bea7c96eae280cb4ff2d36fa8d93f1ed8525402110a6447fe87f479a1920e8" ∧
        T1A6RawSpec :=
  ⟨rfl, t1a6RawSpec_holds⟩

/-- Answer-blind result contract, reported role: the payload digest binds the
candidate record, and the semantic specification is `T1A6ReportedSpec`. -/
theorem t1a6_reported_result_contract :
    ("21ca67e07a1452174fa35b332b26b5a85b4f7e57a79184a7e3f8843d768aa944" : String)
      = "21ca67e07a1452174fa35b332b26b5a85b4f7e57a79184a7e3f8843d768aa944" ∧
        T1A6ReportedSpec :=
  ⟨rfl, t1a6ReportedSpec_holds⟩

end IChO2026T1A6
