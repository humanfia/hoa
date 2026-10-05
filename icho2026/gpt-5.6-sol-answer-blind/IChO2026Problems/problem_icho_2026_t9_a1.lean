import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T9.1: molar mass of beta-cyclodextrin

The problem states that beta-cyclodextrin is a cyclic assembly of seven
glucose units joined by alpha-1,4-glycosidic bonds.  Closing a seven-vertex
cycle gives seven such bonds, and formation of each glycosidic bond removes
one water molecule.  Consequently the raw molar mass is computed from the
mass-conservation expression

`7 * M(glucose) - 7 * M(water)`.

All molar-mass scalars in this file are expressed in `g mol^-1`.
-/

namespace IChO2026Problems.ProblemIcho2026T9A1

/-- A molar mass whose scalar field is expressed in grams per mole. -/
structure MolarMassInGramsPerMole where
  gramsPerMole : ℝ

/-- The outcome-relevant topology of a cyclic glucose condensate. -/
structure CyclicGlucoseAssembly where
  glucoseUnitCount : ℕ
  alpha14GlycosidicBondCount : ℕ

/-- Problem-text and problem-image data for beta-cyclodextrin: seven glucose
units arranged in one closed alpha-1,4-linked ring. -/
def betaCDAssembly : CyclicGlucoseAssembly :=
  { glucoseUnitCount := 7
    alpha14GlycosidicBondCount := 7 }

/-- The problem-stipulated molar mass of glucose, exactly as printed. -/
def glucoseMolarMass : MolarMassInGramsPerMole :=
  { gramsPerMole := 180.16 }

/-- The nominal molar mass of water from the pinned Archon chemistry table.

Dataset version:
`ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1`.
Dataset SHA-256:
`11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`.
Record SHA-256:
`01cc9b0eda3d829a3800deab0bc737cf1d6d4e9f9f1d3879a974ecfcfbe6b274`.
-/
def waterMolarMass : MolarMassInGramsPerMole :=
  { gramsPerMole := 18.015 }

/-- Mass conservation for a glucose condensate when each glycosidic bond is
formed by loss of one water molecule. -/
def molarMassAfterGlycosidicCondensation
    (assembly : CyclicGlucoseAssembly)
    (glucose water : MolarMassInGramsPerMole) : MolarMassInGramsPerMole :=
  { gramsPerMole :=
      (assembly.glucoseUnitCount : ℝ) * glucose.gramsPerMole -
        (assembly.alpha14GlycosidicBondCount : ℝ) * water.gramsPerMole }

/-- The exact, unrounded source-derived molar-mass expression for beta-CD. -/
def betaCDMolarMassRaw : ℝ :=
  (molarMassAfterGlycosidicCondensation
    betaCDAssembly glucoseMolarMass waterMolarMass).gramsPerMole

/-- The assumption/derivation contract: the ring contains seven glucose units,
the closed cycle has one glycosidic bond (and hence one water loss) per unit,
the two input molar masses have their source-grounded values, and the raw
carrier is the resulting mass-conservation expression. -/
def BetaCDMolarMassDerivationSpec : Prop :=
  betaCDAssembly.glucoseUnitCount = 7 ∧
    betaCDAssembly.alpha14GlycosidicBondCount =
      betaCDAssembly.glucoseUnitCount ∧
    glucoseMolarMass.gramsPerMole = 180.16 ∧
    waterMolarMass.gramsPerMole = 18.015 ∧
    betaCDMolarMassRaw =
      (betaCDAssembly.glucoseUnitCount : ℝ) *
          glucoseMolarMass.gramsPerMole -
        (betaCDAssembly.alpha14GlycosidicBondCount : ℝ) *
          waterMolarMass.gramsPerMole

/-- Raw-result contract.  The non-degenerate interval is the interior of the
predeclared final reporting cell `1140 ± 5`; it is not a widened measurement
tolerance. -/
theorem betaCDMolarMassRaw_result :
    BetaCDMolarMassDerivationSpec ∧
      ((1135 : ℝ) ≤ betaCDMolarMassRaw ∧
        betaCDMolarMassRaw ≤ (1145 : ℝ)) := by
  norm_num [BetaCDMolarMassDerivationSpec, betaCDMolarMassRaw,
    molarMassAfterGlycosidicCondensation, betaCDAssembly,
    glucoseMolarMass, waterMolarMass]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"beta_cd_molar_mass","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"1140","reporting_quantum":"10","raw_declaration":"IChO2026Problems.ProblemIcho2026T9A1.betaCDMolarMassRaw","reporting_declaration":"IChO2026Problems.ProblemIcho2026T9A1.betaCDMolarMassReported_result"}
theorem betaCDMolarMassReported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      betaCDMolarMassRaw 1140 10 := by
  refine ⟨by norm_num, ⟨114, by norm_num⟩, ?_⟩
  norm_num [betaCDMolarMassRaw, molarMassAfterGlycosidicCondensation,
    betaCDAssembly, glucoseMolarMass, waterMolarMass]

end IChO2026Problems.ProblemIcho2026T9A1
