import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026 T9 A1: molar mass of beta-cyclodextrin

The problem describes cyclodextrins as cyclic assemblies of alpha-D-glucose
subunits joined by alpha-1,4-glycosidic bonds.  In particular, beta-CD has
seven subunits.  Closing a seven-vertex cycle gives seven glycosidic links, so
the molecular assembly is obtained from seven glucose molecules by removing
seven water molecules.

All molar-mass values below are numerical values in `g mol^-1`.  The glucose
value is stipulated by the problem.  The water value comes from the approved
offline chemistry registry query `molar_mass H2O` (CIAAW abridged 2024 data,
dataset SHA-256
`11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`,
record SHA-256
`01cc9b0eda3d829a3800deab0bc737cf1d6d4e9f9f1d3879a974ecfcfbe6b274`).
-/

namespace IChO2026Problems.T9A1

/-- The three cyclodextrins named in the shared problem context. -/
inductive CyclodextrinKind where
  | alpha
  | beta
  | gamma
  deriving DecidableEq, Repr

/-- The glucose-subunit counts printed in the problem, in alpha/beta/gamma
order. -/
def glucoseSubunitCount : CyclodextrinKind → ℕ
  | .alpha => 6
  | .beta => 7
  | .gamma => 8

/-- Chemical entities whose molar masses enter the calculation. -/
inductive ChemicalSpecies where
  | glucose
  | water
  | betaCyclodextrin
  deriving DecidableEq, Repr

/-- A source-bound scalar molar-mass datum, with its chemical entity retained.
The scalar is expressed in `g mol^-1`. -/
structure MolarMassDatum where
  species : ChemicalSpecies
  gramsPerMole : ℝ

/-- The problem-stipulated molar mass of glucose, in `g mol^-1`. -/
def glucoseMolarMass : MolarMassDatum :=
  { species := .glucose, gramsPerMole := 180.16 }

/-- The conventional molar mass of water, in `g mol^-1`, from the pinned
offline registry receipt recorded in the module docstring. -/
def waterMolarMass : MolarMassDatum :=
  { species := .water, gramsPerMole := 18.015 }

/-- Atom counts for a neutral molecular formula containing only C, H, and O. -/
structure CHOFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

/-- Molecular formula of glucose. -/
def glucoseFormula : CHOFormula :=
  { carbon := 6, hydrogen := 12, oxygen := 6 }

/-- Molecular formula of water. -/
def waterFormula : CHOFormula :=
  { carbon := 0, hydrogen := 2, oxygen := 1 }

/-- Formula obtained when `waterCount` waters are removed from
`glucoseCount` glucose molecules. -/
def condensationFormula (glucoseCount waterCount : ℕ) : CHOFormula :=
  { carbon := glucoseCount * glucoseFormula.carbon -
        waterCount * waterFormula.carbon
    hydrogen := glucoseCount * glucoseFormula.hydrogen -
        waterCount * waterFormula.hydrogen
    oxygen := glucoseCount * glucoseFormula.oxygen -
        waterCount * waterFormula.oxygen }

/-- Elementwise atom-balance ledger for glucose condensation. -/
def CondensationAtomBalance
    (glucoseCount waterCount : ℕ) (product : CHOFormula) : Prop :=
  glucoseCount * glucoseFormula.carbon =
      product.carbon + waterCount * waterFormula.carbon ∧
  glucoseCount * glucoseFormula.hydrogen =
      product.hydrogen + waterCount * waterFormula.hydrogen ∧
  glucoseCount * glucoseFormula.oxygen =
      product.oxygen + waterCount * waterFormula.oxygen

/-- The seven source-labelled positions in one beta-CD ring. -/
abbrev BetaCDUnit := Fin (glucoseSubunitCount .beta)

/-- The next glucopyranoside position around the closed beta-CD ring. -/
def betaCDNext (unit : BetaCDUnit) : BetaCDUnit :=
  ⟨(unit.val + 1) % glucoseSubunitCount .beta,
    Nat.mod_lt _ (by norm_num [glucoseSubunitCount])⟩

/-- The directed alpha-1,4 links traced once around the source's closed
seven-unit ring. -/
def betaCDGlycosidicLinks : Finset (BetaCDUnit × BetaCDUnit) :=
  Finset.univ.image fun unit => (unit, betaCDNext unit)

/-- Undirected incidence degree in the displayed cyclic glycosidic backbone. -/
def betaCDBackboneDegree (unit : BetaCDUnit) : ℕ :=
  (betaCDGlycosidicLinks.filter fun link =>
    link.1 = unit ∨ link.2 = unit).card

/-- Topology carrier: tracing the finite successor cycle gives one distinct
link per unit, and every unit has the two neighbors depicted in the ring. -/
theorem betaCDCycleTopology :
    betaCDGlycosidicLinks.card = glucoseSubunitCount .beta ∧
      ∀ unit : BetaCDUnit, betaCDBackboneDegree unit = 2 := by
  native_decide

/-- The component ledger for one cyclic beta-CD molecule. -/
structure CyclicGlycosidicAssembly where
  glucoseSubunits : ℕ
  glycosidicLinks : ℕ
  productFormula : CHOFormula
  deriving DecidableEq, Repr

/-- Candidate assembly computed from the source's beta-CD subunit count and
the one-link-per-vertex topology of a closed cycle. -/
def betaCDAssembly : CyclicGlycosidicAssembly :=
  let n := glucoseSubunitCount .beta
  let links := betaCDGlycosidicLinks.card
  { glucoseSubunits := n
    glycosidicLinks := links
    productFormula := condensationFormula n links }

/-- Non-opaque specification checked by the beta-CD assembly carrier: it has
the source-stated number of glucose units, a positive closed-cycle link count,
and a complete C/H/O condensation ledger. -/
def BetaCDAssemblySpec (assembly : CyclicGlycosidicAssembly) : Prop :=
  assembly.glucoseSubunits = glucoseSubunitCount .beta ∧
  0 < assembly.glucoseSubunits ∧
  assembly.glycosidicLinks = betaCDGlycosidicLinks.card ∧
  (∀ unit : BetaCDUnit, betaCDBackboneDegree unit = 2) ∧
  assembly.glycosidicLinks = assembly.glucoseSubunits ∧
  CondensationAtomBalance assembly.glucoseSubunits assembly.glycosidicLinks
    assembly.productFormula

/-- Source-to-Lean carrier for the cyclic component and atom accounting. -/
theorem betaCDAssembly_spec : BetaCDAssemblySpec betaCDAssembly := by
  unfold BetaCDAssemblySpec betaCDAssembly
  dsimp only
  refine ⟨rfl, by norm_num [glucoseSubunitCount], rfl,
    betaCDCycleTopology.2, betaCDCycleTopology.1, ?_⟩
  rw [betaCDCycleTopology.1]
  norm_num [CondensationAtomBalance, condensationFormula, glucoseFormula,
    waterFormula, glucoseSubunitCount]

/-- Explicit recombination check for the molecular formula represented by the
seven-unit cyclic component ledger. -/
theorem betaCDAssembly_formula :
    betaCDAssembly.productFormula =
      { carbon := 42, hydrogen := 70, oxygen := 35 } := by
  native_decide

/-- The exact, unrounded beta-CD molar-mass expression in `g mol^-1`.
It retains both the number of glucose inputs and the number of water losses. -/
def betaCDMolarMassRaw : ℝ :=
  (betaCDAssembly.glucoseSubunits : ℝ) * glucoseMolarMass.gramsPerMole -
    (betaCDAssembly.glycosidicLinks : ℝ) * waterMolarMass.gramsPerMole

/-- Problem-specific derivation specification for a proposed beta-CD molar
mass.  The candidate must satisfy the source topology and atom ledger and must
equal the end-to-end, unrounded condensation expression. -/
def BetaCDMolarMassDerivation (candidate : ℝ) : Prop :=
  BetaCDAssemblySpec betaCDAssembly ∧
  glucoseMolarMass.species = .glucose ∧
  glucoseMolarMass.gramsPerMole = 180.16 ∧
  waterMolarMass.species = .water ∧
  waterMolarMass.gramsPerMole = 18.015 ∧
  candidate =
    (betaCDAssembly.glucoseSubunits : ℝ) * glucoseMolarMass.gramsPerMole -
      (betaCDAssembly.glycosidicLinks : ℝ) * waterMolarMass.gramsPerMole

/-- Closed proposition used by the machine-readable raw-result contract.  It
specializes the candidate-independent derivation relation to the exact raw
expression, without replacing that expression by a submitted decimal. -/
def BetaCDMolarMassRawSpec : Prop :=
  BetaCDMolarMassDerivation betaCDMolarMassRaw

/-- Raw-result contract.  Besides the exact derivation specification, the
non-degenerate rational interval is a certified enclosure of the raw value;
it is not a measurement tolerance. -/
theorem betaCDMolarMass_raw_result :
    BetaCDMolarMassRawSpec ∧
      (1135 : ℝ) ≤ betaCDMolarMassRaw ∧
      betaCDMolarMassRaw ≤ (1136 : ℝ) := by
  constructor
  · unfold BetaCDMolarMassRawSpec BetaCDMolarMassDerivation
    exact ⟨betaCDAssembly_spec, rfl, rfl, rfl, rfl, rfl⟩
  · have hlinks : betaCDGlycosidicLinks.card = 7 := by
      simpa [glucoseSubunitCount] using betaCDCycleTopology.1
    norm_num [betaCDMolarMassRaw, betaCDAssembly, glucoseMolarMass,
      waterMolarMass, glucoseSubunitCount, hlinks]

/-- Reported-result contract.  Three significant figures at this magnitude
mean a reporting quantum of `10 g mol^-1`; the shared relation implements
nearest-quantum rounding with exact ties away from zero. -/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"beta_cd_molar_mass","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"1.14e3","reporting_quantum":"10","raw_declaration":"IChO2026Problems.T9A1.betaCDMolarMassRaw","reporting_declaration":"IChO2026Problems.T9A1.betaCDMolarMass_reported_result"}
theorem betaCDMolarMass_reported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      betaCDMolarMassRaw (1140 : ℝ) (10 : ℝ) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · exact ⟨114, by norm_num⟩
  · have hlinks : betaCDGlycosidicLinks.card = 7 := by
      simpa [glucoseSubunitCount] using betaCDCycleTopology.1
    norm_num [betaCDMolarMassRaw, betaCDAssembly, glucoseMolarMass,
      waterMolarMass, glucoseSubunitCount, hlinks]

end IChO2026Problems.T9A1
