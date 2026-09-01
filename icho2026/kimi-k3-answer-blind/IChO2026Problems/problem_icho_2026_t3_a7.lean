import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T3 (Into Reticular Chemistry), part 3.7 — `icho_2026_t3_a7`

## Problem (answer-blind; sources: problem text and `T3_page-6.png`, `T3_page-7.png`)

COF-8 is a honeycomb (hcb) 2D covalent organic framework built from monomer
**D2** (2,4,6-tris(4-formylphenyl)-1,3,5-triazine, C₂₄H₁₅N₃O₃) and monomer
**E1** (1,3,5-tris(cyanomethyl)benzene, C₁₂H₉N₃) through Knoevenagel
condensation: each Ar–CHO + H₂C(CN)–Ar′ pair forms an Ar–CH=C(CN)–Ar′ link
and loses one H₂O.  Treatment of COF-8 with NH₂OH gives COF-9, in which every
nitrile C≡N is converted into an amidoxime C(=N–OH)NH₂ (net +NH₃O per
nitrile).

Experiment (problem text, part 3.7): a suspension of 5.000 mg COF-9 in
200.0 mL of 19.90 mg dm⁻³ UO₂²⁺ solution was filtered after equilibrium was
reached; the final UO₂²⁺ concentration was 9.225 mg dm⁻³.  Assume that all
uranium exists as UO₂²⁺ ions.

Requested outputs:

1. the equilibrium absorption capacity `qₑ` in mg g⁻¹ of COF-9;
2. the number of UO₂²⁺ ions absorbed per pore.

## Derivation carried by this file (problem-only evidence)

* Mass balance: `qₑ = (c₀ − cₑ)·V / m = (19.90 − 9.225) · 0.2000 / 0.005000
  = 427` mg g⁻¹ exactly (all inputs are stipulated terminating decimals).
* Honeycomb topology: a hexagonal pore is rimmed by 6 vertices (3 D2 and 3 E1,
  alternating), each shared by 3 pores, and by 6 edges, each shared by 2
  pores; hence one pore corresponds to 1 D2 + 1 E1 + 3 links, i.e. to the
  repeat unit C₃₆H₁₈N₆ for COF-8 and, after amidoximation of its 3 nitriles,
  to C₃₆H₂₇N₉O₃ for COF-9: exactly one pore per repeat unit.
* Pinned registry weights (CIAAW abridged 2024, dataset sha256
  `11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`):
  `M(UO₂²⁺) = 238.03 + 2·15.999 = 270.028 g mol⁻¹` and
  `M(C₃₆H₂₇N₉O₃) = 633.672 g mol⁻¹`.
* Ions per pore:
  `((c₀ − cₑ)·V / M(UO₂²⁺)) / (m / M(C₃₆H₂₇N₉O₃)) = 33822243/33753500
  ≈ 1.0020366`, reported to 3 significant figures as 1.00 ions pore⁻¹.

Reporting rule (source `reporting_policy`): three significant figures, ties
half away from zero, no intermediate rounding; the certified intervals are the
half-quantum windows of the reported values and contain the raw values.

The two `*Contract` theorems embed the controller-computed payload digests of
`blind_candidates/icho_2026_t3_a7.json` (answer-blind protocol
`icho-answer-blind-v1`); they bind the semantic specifications
`rawResultSpec` / `reportedResultSpec` to that frozen record.
-/

namespace IChO2026T3A7

open IChO2026Chem.Reporting

/-! ### Pinned atomic weights (archon offline chemistry registry) -/

/-- Pinned CIAAW-abridged-2024 standard atomic weight of carbon.
Lookup: `chemistry-constant atomic_weight C`;
dataset_sha256 `11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`;
record_sha256 `0f558fc72d4299d061e9d29f394ebed43fc8246f7dbdb402bbb2a338cfbe4b8a`. -/
def atomicWeightC : ℝ := 12.011

/-- Pinned CIAAW-abridged-2024 standard atomic weight of hydrogen;
record_sha256 `8e5f2e512d11f6c3409197956a4f015f6144f43057a286107064436c64b4bce5`. -/
def atomicWeightH : ℝ := 1.0080

/-- Pinned CIAAW-abridged-2024 standard atomic weight of nitrogen;
record_sha256 `5ca62d438a6594458420ed7f5d2072a583a9ae8c71a29d75b561edb28b6f065c`. -/
def atomicWeightN : ℝ := 14.007

/-- Pinned CIAAW-abridged-2024 standard atomic weight of oxygen;
record_sha256 `d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588`. -/
def atomicWeightO : ℝ := 15.999

/-- Pinned CIAAW-abridged-2024 standard atomic weight of uranium;
record_sha256 `18330650985fd5a061184983d3884beb83604e75446c7ec00dd6f33766382767`. -/
def atomicWeightU : ℝ := 238.03

/-! ### Problem-stated measurements (part 3.7, `T3_page-7.png`) -/

/-- Initial UO₂²⁺ concentration `c₀ = 19.90 mg dm⁻³`. -/
def cInitial : ℝ := 19.90

/-- Equilibrium UO₂²⁺ concentration `cₑ = 9.225 mg dm⁻³`. -/
def cEquilibrium : ℝ := 9.225

/-- Solution volume `V = 200.0 mL = 0.2000 dm³`. -/
def volumeSolution : ℝ := 0.2000

/-- COF-9 sorbent mass `m = 5.000 mg`. -/
def massCof9Mg : ℝ := 5.000

/-- COF-9 sorbent mass in grams. -/
noncomputable def massCof9G : ℝ := massCof9Mg / 1000

/-! ### COF-9 pore repeat unit (structures on `T3_page-6.png`, `T3_page-7.png`) -/

/-- Carbon count of monomer D2, C₂₄H₁₅N₃O₃ (structure on `T3_page-6.png`). -/
def d2C : ℕ := 24

/-- Hydrogen count of monomer D2, C₂₄H₁₅N₃O₃. -/
def d2H : ℕ := 15

/-- Nitrogen count of monomer D2, C₂₄H₁₅N₃O₃. -/
def d2N : ℕ := 3

/-- Oxygen count of monomer D2, C₂₄H₁₅N₃O₃. -/
def d2O : ℕ := 3

/-- Carbon count of monomer E1, C₁₂H₉N₃ (structure on `T3_page-6.png`). -/
def e1C : ℕ := 12

/-- Hydrogen count of monomer E1, C₁₂H₉N₃. -/
def e1H : ℕ := 9

/-- Nitrogen count of monomer E1, C₁₂H₉N₃. -/
def e1N : ℕ := 3

/-- Carbon count of the COF-9 pore repeat unit C₃₆H₂₇N₉O₃. -/
def poreRepeatC : ℕ := 36

/-- Hydrogen count of the COF-9 pore repeat unit C₃₆H₂₇N₉O₃. -/
def poreRepeatH : ℕ := 27

/-- Nitrogen count of the COF-9 pore repeat unit C₃₆H₂₇N₉O₃. -/
def poreRepeatN : ℕ := 9

/-- Oxygen count of the COF-9 pore repeat unit C₃₆H₂₇N₉O₃. -/
def poreRepeatO : ℕ := 3

/-- Assembly of the COF-9 pore repeat unit: one D2 + one E1, minus three
waters from the three Knoevenagel C=C links, plus three NH₃O from the
nitrile-to-amidoxime conversions — checked componentwise. -/
theorem poreRepeatUnit_assembly :
    poreRepeatC = d2C + e1C ∧
    poreRepeatH = d2H + e1H - 3 * 2 + 3 * 3 ∧
    poreRepeatN = d2N + e1N + 3 ∧
    poreRepeatO = d2O + 0 - 3 + 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Pores per repeat unit: in the honeycomb net each pore has 6 rim vertices
(each shared by 3 pores) and 6 rim edges (each shared by 2 pores), so one pore
corresponds to exactly one D2 + E1 repeat unit. -/
def poresPerRepeatUnit : ℕ := 1

/-- Molar mass of UO₂²⁺: `238.03 + 2·15.999 = 270.028 g mol⁻¹`.  The problem
stipulates that all uranium exists as UO₂²⁺ ions. -/
def molarMassUranyl : ℝ := atomicWeightU + 2 * atomicWeightO

/-- Molar mass of the COF-9 pore repeat unit C₃₆H₂₇N₉O₃:
`633.672 g mol⁻¹`. -/
def molarMassCof9PoreUnit : ℝ :=
  poreRepeatC * atomicWeightC + poreRepeatH * atomicWeightH +
    poreRepeatN * atomicWeightN + poreRepeatO * atomicWeightO

/-! ### Raw (unrounded) requested outputs -/

/-- Raw equilibrium absorption capacity `qₑ = (c₀ − cₑ)·V / m`, in mg g⁻¹. -/
noncomputable def qeRaw : ℝ := (cInitial - cEquilibrium) * volumeSolution / massCof9G

/-- Raw number of UO₂²⁺ ions absorbed per pore: moles of UO₂²⁺ absorbed
divided by moles of pores.  With masses in mg and molar masses in g mol⁻¹
(= mg mmol⁻¹) both mole counts come out in mmol and the ratio is
dimensionless. -/
noncomputable def uranylPerPoreRaw : ℝ :=
  ((cInitial - cEquilibrium) * volumeSolution / molarMassUranyl) /
    (massCof9Mg / molarMassCof9PoreUnit) * poresPerRepeatUnit

/-- The raw capacity is exactly `427 mg g⁻¹`. -/
theorem qeRaw_exact : qeRaw = 427 := by
  norm_num [qeRaw, cInitial, cEquilibrium, volumeSolution, massCof9G, massCof9Mg]

/-- The raw per-pore count is exactly `33822243/33753500 ≈ 1.0020366`. -/
theorem uranylPerPoreRaw_exact : uranylPerPoreRaw = 33822243 / 33753500 := by
  norm_num [uranylPerPoreRaw, molarMassUranyl, molarMassCof9PoreUnit,
    poreRepeatC, poreRepeatH, poreRepeatN, poreRepeatO,
    atomicWeightC, atomicWeightH, atomicWeightN, atomicWeightO, atomicWeightU,
    cInitial, cEquilibrium, volumeSolution, massCof9Mg, poresPerRepeatUnit]

/-! ### Source-to-Lean bridge (derivation specification) -/

/-- The governing relations used by the raw results, with provenance:
(S1) uranyl speciation — all uranium counted as UO₂²⁺ (problem text);
(S2) molar mass of the pore repeat unit C₃₆H₂₇N₉O₃ from pinned weights;
(S3) repeat-unit assembly 1 D2 + 1 E1 − 3 H₂O + 3 NH₃O per pore (monomer
     structures and the COF-8 → COF-9 scheme on the problem images);
(S4) one pore per repeat unit (honeycomb topology, problem images);
(S5) the mass-balance definition of `qₑ`;
(S6) the mole-ratio definition of ions per pore. -/
def derivationSpec : Prop :=
  molarMassUranyl = 238.03 + 2 * 15.999 ∧
  molarMassCof9PoreUnit = 36 * 12.011 + 27 * 1.0080 + 9 * 14.007 + 3 * 15.999 ∧
  (poreRepeatC = d2C + e1C ∧
   poreRepeatH = d2H + e1H - 3 * 2 + 3 * 3 ∧
   poreRepeatN = d2N + e1N + 3 ∧
   poreRepeatO = d2O + 0 - 3 + 3) ∧
  poresPerRepeatUnit = 1 ∧
  qeRaw = (cInitial - cEquilibrium) * volumeSolution / massCof9G ∧
  uranylPerPoreRaw = ((cInitial - cEquilibrium) * volumeSolution / molarMassUranyl) /
    (massCof9Mg / molarMassCof9PoreUnit) * poresPerRepeatUnit

theorem derivationSpec_holds : derivationSpec := by
  refine ⟨?_, ?_, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  · norm_num [molarMassUranyl, atomicWeightU, atomicWeightO]
  · norm_num [molarMassCof9PoreUnit, poreRepeatC, poreRepeatH, poreRepeatN,
      poreRepeatO, atomicWeightC, atomicWeightH, atomicWeightN, atomicWeightO]

/-! ### Result specifications and frozen payload contracts -/

/-- Raw-result specification: the derivation holds, both raw quantities have
the stated exact unrounded values, and both lie in their certified
non-degenerate half-quantum intervals. -/
def rawResultSpec : Prop :=
  derivationSpec ∧
  qeRaw = 427 ∧
  uranylPerPoreRaw = 33822243 / 33753500 ∧
  (426.5 ≤ qeRaw ∧ qeRaw ≤ 427.5) ∧
  (0.995 ≤ uranylPerPoreRaw ∧ uranylPerPoreRaw ≤ 1.005)

/-- Reported-result specification: both outputs are reported at the
3-significant-figure quanta (1 mg g⁻¹ and 0.01 ions pore⁻¹) with ties half
away from zero, per the source reporting policy. -/
def reportedResultSpec : Prop :=
  ReportsAtQuantum qeRaw 427 1 ∧ ReportsAtQuantum uranylPerPoreRaw 1 (0.01)

/-- Reporting certificate for `qₑ`: raw `427` is reported as `427` at quantum
`1 mg g⁻¹` (three significant figures). -/
theorem qeReportsAtQuantum : ReportsAtQuantum qeRaw 427 1 := by
  have h0 : (0 : ℝ) ≤ qeRaw := by rw [qeRaw_exact]; norm_num
  refine ⟨one_pos, ⟨427, by norm_num⟩, ?_⟩
  rw [if_pos h0, qeRaw_exact]
  constructor <;> norm_num

/-- Reporting certificate for the per-pore count: raw `33822243/33753500` is
reported as `1.00` at quantum `0.01 ions pore⁻¹` (three significant
figures). -/
theorem uranylPerPoreReportsAtQuantum :
    ReportsAtQuantum uranylPerPoreRaw 1 (0.01) := by
  have h0 : (0 : ℝ) ≤ uranylPerPoreRaw := by rw [uranylPerPoreRaw_exact]; norm_num
  refine ⟨by norm_num, ⟨100, by norm_num⟩, ?_⟩
  rw [if_pos h0, uranylPerPoreRaw_exact]
  constructor <;> norm_num

/-- Raw-result contract: embeds the payload digest of the frozen
`blind_candidates/icho_2026_t3_a7.json` record (role `raw_result`). -/
theorem rawResultContract :
    ("d22c05db5817fe45fe4762e93bd2512f1b182507ab9a63bdfaaf1afc9564d60d" : String) =
      "d22c05db5817fe45fe4762e93bd2512f1b182507ab9a63bdfaaf1afc9564d60d" ∧
    rawResultSpec := by
  refine ⟨rfl, derivationSpec_holds, qeRaw_exact, uranylPerPoreRaw_exact, ?_, ?_⟩
  · rw [qeRaw_exact]; constructor <;> norm_num
  · rw [uranylPerPoreRaw_exact]; constructor <;> norm_num

/-- Reported-result contract: embeds the payload digest of the frozen
`blind_candidates/icho_2026_t3_a7.json` record (role `reported_result`). -/
theorem reportedResultContract :
    ("aa8a01b2c045298aed5c46f78712653b59c59f0708392a0d2213fd8eef30534d" : String) =
      "aa8a01b2c045298aed5c46f78712653b59c59f0708392a0d2213fd8eef30534d" ∧
    reportedResultSpec :=
  ⟨rfl, qeReportsAtQuantum, uranylPerPoreReportsAtQuantum⟩

/-! ### Machine-checkable submission certificates -/

/-- Submission record for `qₑ`. -/
noncomputable def qeSubmission : NumericSubmission where
  rawValue := qeRaw
  reportedValue := 427
  reportingQuantum := 1

/-- Submission record for the per-pore uranyl count. -/
noncomputable def uranylPerPoreSubmission : NumericSubmission where
  rawValue := uranylPerPoreRaw
  reportedValue := 1
  reportingQuantum := 0.01

theorem qeSubmission_valid : ValidNumericSubmission qeRaw qeSubmission :=
  ⟨rfl, qeReportsAtQuantum⟩

theorem uranylPerPoreSubmission_valid :
    ValidNumericSubmission uranylPerPoreRaw uranylPerPoreSubmission :=
  ⟨rfl, uranylPerPoreReportsAtQuantum⟩

end IChO2026T3A7
