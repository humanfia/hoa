import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T9-A1 — molar mass of β-cyclodextrin

## Problem contract (from the sealed source only)

* Shared context (T9): cyclodextrins (CD) are cyclic oligosaccharides of
  glucose subunits joined by α-1,4-glycosidic bonds; the common α-, β- and
  γ-cyclodextrins contain 6, 7 and 8 α-D-glucopyranoside units, respectively.
* Subquestion 9.1: "Calculate the molar mass of β-CD. Assume
  M_w(glucose) = 180.16 g mol⁻¹." (2.0 pt)
* Figure `T9_page-1.png` (sha256
  `c7f5114e9bb5d3e821a3df76d40c4ab86006fdb550992aa8013bc50b68a90608`):
  the bottom-right structural formula is labelled "n = 7, β-CD" and shows
  seven glucopyranose rings closed into a macrocycle by seven glycosidic
  oxygens; the bottom-left schematic marks 7 × CH₂OH and (OH)₁₄, i.e. seven
  C₆H₁₀O₅ residues on a closed ring.

## Assumption / target split

Assumptions (all problem-side or trusted pinned data):

* β-CD contains exactly 7 glucose units (problem text, shared context).
* A cyclic α-1,4 glucooligomer of `n` units closes with exactly `n`
  glycosidic linkages (each unit donates its anomeric C1 to one linkage and
  its O4 to the next); the figure shows the closed heptamer ring.
* Each glycosidic linkage forms by condensation, eliminating one H₂O
  (ordinary chemistry of glycosidic bond formation).
* `M_w(glucose) = 180.16 g mol⁻¹` — problem-stipulated, exact as printed.
  (Cross-check: pinned registry `molar_mass C6H12O6` = 180.156 g mol⁻¹,
  record_sha256
  `f0a273e3e1199bc5fb1cc94d63dc1447f03a1dfd4e44137c6761e8c6ef674e28`;
  the stipulated value governs.)
* `M_w(H₂O) = 18.015 g mol⁻¹` — pinned offline registry
  (`chemistry-constant molar_mass H2O`, CIAAW abridged 2024),
  dataset_sha256
  `11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`,
  record_sha256
  `01cc9b0eda3d829a3800deab0bc737cf1d6d4e9f9f1d3879a974ecfcfbe6b274`.

Target: the raw molar mass `M(β-CD) = 7 · M_w(glucose) − 7 · M_w(H₂O)` in
g mol⁻¹, certified in a non-degenerate rational interval, and its reported
value under the source-fixed reporting policy (three significant figures,
ties half away from zero; the reporting quantum at this magnitude is
10 g mol⁻¹).  There are no previous parts; nothing is imported from other
targets.
-/

namespace IChO2026T9A1

/-- Problem-stipulated molar mass of glucose, exact as printed:
`M_w(glucose) = 180.16 g mol⁻¹` (T9-A1 assumption). -/
def glucoseMolarMass : ℝ := 180.16

/-- Molar mass of water from the pinned offline registry
(`chemistry-constant molar_mass H2O`, CIAAW abridged 2024; 18.015 g mol⁻¹),
used as the exact conventional contest input per project policy. -/
def waterMolarMass : ℝ := 18.015

/-- Number of α-D-glucopyranoside units in α-cyclodextrin (shared context). -/
def alphaCDGlucoseUnitCount : ℕ := 6

/-- Number of α-D-glucopyranoside units in β-cyclodextrin (shared context:
"β-cyclodextrin contains 7 α-D-glucopyranoside units"; figure label
"n = 7, β-CD"). -/
def betaCDGlucoseUnitCount : ℕ := 7

/-- Number of α-D-glucopyranoside units in γ-cyclodextrin (shared context). -/
def gammaCDGlucoseUnitCount : ℕ := 8

/-- Glycosidic linkages in a cyclic α-1,4 glucooligomer: a ring of `n`
monosaccharide units closes with exactly `n` glycosidic bonds (each unit
contributes its anomeric C1 to one linkage and its O4 to another). -/
def cyclicGlycosidicBondCount (n : ℕ) : ℕ := n

theorem cyclicGlycosidicBondCount_eq (n : ℕ) :
    cyclicGlycosidicBondCount n = n := rfl

/-- Water molecules eliminated per glycosidic bond formed: condensation of
the anomeric hydroxyl with the O4–H hydroxyl releases one H₂O per linkage. -/
def waterEliminatedPerGlycosidicBond : ℕ := 1

/-- Total water eliminated when β-CD forms from 7 glucose monomers:
`n` linkages × 1 water each, with `n = 7`. -/
def betaCDWaterLossCount : ℕ :=
  cyclicGlycosidicBondCount betaCDGlucoseUnitCount * waterEliminatedPerGlycosidicBond

theorem betaCDWaterLossCount_eq : betaCDWaterLossCount = 7 := by decide

/-- Atom counts `(C, H, O)` of the glucose monomer C₆H₁₂O₆ (ordinary
chemical fact; consistent with the stipulated 180.16 g mol⁻¹). -/
def glucoseAtomCounts : ℕ × ℕ × ℕ := (6, 12, 6)

/-- Atom counts `(C, H, O)` of water H₂O. -/
def waterAtomCounts : ℕ × ℕ × ℕ := (0, 2, 1)

/-- Atom counts `(C, H, O)` of β-CD: seven glucose units minus the seven
condensation waters. -/
def betaCDAtomCounts : ℕ × ℕ × ℕ :=
  ( betaCDGlucoseUnitCount * 6 - betaCDWaterLossCount * 0
  , betaCDGlucoseUnitCount * 12 - betaCDWaterLossCount * 2
  , betaCDGlucoseUnitCount * 6 - betaCDWaterLossCount * 1 )

/-- β-CD has composition C₄₂H₇₀O₃₅ (equivalently seven C₆H₁₀O₅ residues,
matching the figure's 7 × CH₂OH and (OH)₁₄ substitution pattern). -/
theorem betaCD_composition_C42H70O35 : betaCDAtomCounts = (42, 70, 35) := by
  decide

/-- Raw molar mass of β-CD in g mol⁻¹: seven glucose units with the seven
condensation waters removed,
`M(β-CD) = 7 · M_w(glucose) − 7 · M_w(H₂O)`.
This is the unrounded, source-derived raw expression. -/
def betaCDMolarMassRaw : ℝ :=
  (betaCDGlucoseUnitCount : ℝ) * glucoseMolarMass
    - (betaCDWaterLossCount : ℝ) * waterMolarMass

/-- Exact value of the raw expression, by rational arithmetic:
`7 · 180.16 − 7 · 18.015 = 1135.015` g mol⁻¹. -/
theorem betaCDMolarMassRaw_value : betaCDMolarMassRaw = 1135.015 := by
  norm_num [betaCDMolarMassRaw, betaCDWaterLossCount, cyclicGlycosidicBondCount,
    betaCDGlucoseUnitCount, waterEliminatedPerGlycosidicBond, glucoseMolarMass,
    waterMolarMass]

/-- Derivation specification for the raw molar mass of β-CD: the unrounded
governing relation is exactly seven glucose molar masses minus seven water
molar masses (the cyclic heptamer loses one water per glycosidic linkage). -/
def BetaCDMolarMassDerivationSpec : Prop :=
  betaCDMolarMassRaw = 7 * glucoseMolarMass - 7 * waterMolarMass

/-- Raw-result contract: the governing relation holds and the raw value lies
in the certified non-degenerate interval `[1135.01, 1135.02]` g mol⁻¹
(interval width equal to the last displayed decimal quantum of the
problem-stipulated glucose molar mass, strictly enclosing the exact raw
value 1135.015). -/
theorem betaCDMolarMassRaw_contract :
    (IChO2026T9A1.BetaCDMolarMassDerivationSpec) ∧
      (((113501 : ℝ) / 100) ≤ (IChO2026T9A1.betaCDMolarMassRaw) ∧
        (IChO2026T9A1.betaCDMolarMassRaw) ≤ ((56751 : ℝ) / 50)) := by
  have h : betaCDMolarMassRaw = 1135.015 := betaCDMolarMassRaw_value
  refine ⟨?_, by rw [h]; norm_num, by rw [h]; norm_num⟩
  unfold BetaCDMolarMassDerivationSpec
  rw [h]
  norm_num [glucoseMolarMass, waterMolarMass]

/-- Reported-result contract: under the source-fixed reporting policy
(three significant figures, ties half away from zero — hence quantum
10 g mol⁻¹ at this magnitude), the raw molar mass of β-CD reports as
1140 g mol⁻¹, i.e. 1.14 × 10³ g mol⁻¹. -/
theorem betaCDMolarMassReported_contract :
    IChO2026Chem.Reporting.ReportsAtQuantum
      (IChO2026T9A1.betaCDMolarMassRaw) (1140 : ℝ) (10 : ℝ) := by
  have h : betaCDMolarMassRaw = 1135.015 := betaCDMolarMassRaw_value
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨114, by norm_num⟩, ?_⟩
  rw [h]
  split_ifs with hc
  · exact ⟨by norm_num, by norm_num⟩
  · exact absurd (by norm_num : (0 : ℝ) ≤ 1135.015) hc

/-- The solver-facing numeric submission carrier: raw value, reported value
and reporting quantum, tied together by the shared reporting contract. -/
def betaCDSubmission : IChO2026Chem.Reporting.NumericSubmission where
  rawValue := betaCDMolarMassRaw
  reportedValue := 1140
  reportingQuantum := 10

/-- The submission is valid for the raw β-CD molar-mass expression. -/
theorem betaCDSubmission_valid :
    IChO2026Chem.Reporting.ValidNumericSubmission betaCDMolarMassRaw betaCDSubmission := by
  refine ⟨rfl, ?_⟩
  exact betaCDMolarMassReported_contract

end IChO2026T9A1
