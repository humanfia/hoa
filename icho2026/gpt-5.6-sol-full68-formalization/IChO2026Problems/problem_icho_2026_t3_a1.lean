import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026 T3-A1: composition and carbon mass fraction of COF-1

The molecular drawing on the bound problem page is used quantitatively.  A
honeycomb cell has six B3 cores, each shared by three cells, and six A2
linkers, each shared by two cells.  Thus its assembly inventory is computed
from sharing numbers rather than postulated as the desired formula.  The
boronate-ester condensation shown by the source removes two waters at each of
the six core--linker connections.

Atomic weights below are exact conventional central values from the pinned
offline CIAAW 2024 table.  They are not source measurements and no
rounding is performed before the final two-decimal reporting boundary.
-/

namespace IChO2026Problems.T3A1

noncomputable section

/-- The four elements that occur in the depicted COF-1 assembly. -/
inductive Element
  | carbon
  | hydrogen
  | boron
  | oxygen
  deriving DecidableEq, Repr

/-- An atom-count formula in the element domain visible in the COF-1 drawing. -/
structure Formula where
  carbon : ℕ
  hydrogen : ℕ
  boron : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

namespace Formula

/-- Componentwise addition of molecular formulae. -/
def add (x y : Formula) : Formula where
  carbon := x.carbon + y.carbon
  hydrogen := x.hydrogen + y.hydrogen
  boron := x.boron + y.boron
  oxygen := x.oxygen + y.oxygen

instance : Add Formula := ⟨add⟩

/-- Multiply every atom count by a stoichiometric multiplicity. -/
def scale (n : ℕ) (x : Formula) : Formula where
  carbon := n * x.carbon
  hydrogen := n * x.hydrogen
  boron := n * x.boron
  oxygen := n * x.oxygen

/-- Componentwise material removal.  A separate carrier proves that the
removed formula is bounded by the input formula in every component. -/
def subtract (x y : Formula) : Formula where
  carbon := x.carbon - y.carbon
  hydrogen := x.hydrogen - y.hydrogen
  boron := x.boron - y.boron
  oxygen := x.oxygen - y.oxygen

/-- All four component counts of `y` can be removed from `x`. -/
def CanSubtract (x y : Formula) : Prop :=
  y.carbon ≤ x.carbon ∧ y.hydrogen ≤ x.hydrogen ∧
    y.boron ≤ x.boron ∧ y.oxygen ≤ x.oxygen

/-- Greatest common divisor of all atom counts. -/
def countGCD (x : Formula) : ℕ :=
  Nat.gcd x.carbon (Nat.gcd x.hydrogen (Nat.gcd x.boron x.oxygen))

/-- The formula has at least one atom and has relatively prime atom counts. -/
def IsPrimitive (x : Formula) : Prop :=
  0 < x.carbon + x.hydrogen + x.boron + x.oxygen ∧ countGCD x = 1

/-- `candidate` is an empirical formula for `whole`: it is primitive and a
positive whole-number multiple gives the complete assembly formula. -/
def IsEmpiricalFormula (whole candidate : Formula) : Prop :=
  IsPrimitive candidate ∧
    ∃ multiplicity : ℕ, 0 < multiplicity ∧ whole = scale multiplicity candidate

end Formula

/-- Provenance vocabulary required for source-bounded image and chemistry
facts used in this target. -/
inductive FactProvenance
  | problemText
  | problemImage
  | trustedGeneralLaw
  | trustedOfflineConstant
  | derivedTheorem
  deriving DecidableEq, Repr

/-- The finite material domain used in the outcome-decisive assembly ledger. -/
inductive Species
  | B3
  | A2
  | water
  | cof1Cell
  deriving DecidableEq, Repr

/-- The source does not state material phases for this condensation. -/
inductive PhaseStatus
  | unspecified
  deriving DecidableEq, Repr

inductive MaterialSide
  | input
  | output
  deriving DecidableEq, Repr

inductive ComponentRole
  | core
  | linker
  | leavingGroup
  | repeatUnit
  deriving DecidableEq, Repr

/-- A source-traceable entry in the complete finite assembly ledger. -/
structure MaterialLedgerEntry where
  species : Species
  side : MaterialSide
  role : ComponentRole
  multiplicity : ℕ
  phase : PhaseStatus
  provenance : FactProvenance
  sourceLocator : String
  deriving DecidableEq, Repr

/-- Hexahydroxytriphenylene B3, read from the labeled source structure. -/
def b3Formula : Formula :=
  { carbon := 18, hydrogen := 12, boron := 0, oxygen := 6 }

/-- Benzene-1,4-diboronic acid A2, read from the labeled source structure. -/
def a2Formula : Formula :=
  { carbon := 6, hydrogen := 8, boron := 2, oxygen := 4 }

def waterFormula : Formula :=
  { carbon := 0, hydrogen := 2, boron := 0, oxygen := 1 }

/-- Sharing data read from the honeycomb topology on `T3_page-1.png`. -/
structure HoneycombSharing where
  cornersPerCell : ℕ
  cellsAtCore : ℕ
  edgesPerCell : ℕ
  cellsAtLinker : ℕ
  provenance : FactProvenance
  sourceLocator : String
  deriving DecidableEq, Repr

def cof1HoneycombSharing : HoneycombSharing where
  cornersPerCell := 6
  cellsAtCore := 3
  edgesPerCell := 6
  cellsAtLinker := 2
  provenance := .problemImage
  sourceLocator := "T3_page-1.png: COF-1 honeycomb topology and dashed repeat boundaries"

/-- Number of B3 core equivalents belonging to one honeycomb cell. -/
def cof1CoreMultiplicity : ℕ :=
  cof1HoneycombSharing.cornersPerCell / cof1HoneycombSharing.cellsAtCore

/-- Number of A2 linker equivalents belonging to one honeycomb cell. -/
def cof1LinkerMultiplicity : ℕ :=
  cof1HoneycombSharing.edgesPerCell / cof1HoneycombSharing.cellsAtLinker

/-- B3 visibly supplies three catechol connection sites. -/
def connectionSitesPerB3 : ℕ := 3

/-- A2 visibly supplies two boronic-acid connection sites. -/
def connectionSitesPerA2 : ℕ := 2

/-- Each cyclic boronate-ester connection removes two water molecules from one
catechol pair and one boronic-acid group. -/
def watersPerBoronateConnection : ℕ := 2

/-- Number of boronate-ester connections belonging to the cell assembly. -/
def cof1ConnectionMultiplicity : ℕ :=
  cof1CoreMultiplicity * connectionSitesPerB3

/-- Water multiplicity derived from the connection count. -/
def cof1WaterMultiplicity : ℕ :=
  watersPerBoronateConnection * cof1ConnectionMultiplicity

/-- Complete reactant atom inventory for one honeycomb-cell assembly. -/
def cof1ReactantFormula : Formula :=
  Formula.scale cof1CoreMultiplicity b3Formula +
    Formula.scale cof1LinkerMultiplicity a2Formula

/-- Explicit leaving-group inventory for that assembly. -/
def cof1WaterLossFormula : Formula :=
  Formula.scale cof1WaterMultiplicity waterFormula

/-- End-to-end atom-count formula after the depicted water loss. -/
def cof1CellFormula : Formula :=
  Formula.subtract cof1ReactantFormula cof1WaterLossFormula

/-- Source-derived finite species domain.  No anonymous material stream is
admitted because the requested formula calculation uses this complete ideal
condensation ledger. -/
def cof1StagedSpeciesDomain : Finset Species :=
  { .B3, .A2, .water, .cof1Cell }

/-- Quantitative-material-stage ledger for one honeycomb cell. -/
def cof1MaterialLedger : List MaterialLedgerEntry :=
  [ { species := .B3
      side := .input
      role := .core
      multiplicity := cof1CoreMultiplicity
      phase := .unspecified
      provenance := .problemImage
      sourceLocator := "T3_page-1.png: B3 structure and COF-1 core nodes" },
    { species := .A2
      side := .input
      role := .linker
      multiplicity := cof1LinkerMultiplicity
      phase := .unspecified
      provenance := .problemImage
      sourceLocator := "T3_page-1.png: A2 structure and COF-1 edge linkers" },
    { species := .water
      side := .output
      role := .leavingGroup
      multiplicity := cof1WaterMultiplicity
      phase := .unspecified
      provenance := .derivedTheorem
      sourceLocator := "T3_page-1.png: -H2O condensation arrows" },
    { species := .cof1Cell
      side := .output
      role := .repeatUnit
      multiplicity := 1
      phase := .unspecified
      provenance := .problemImage
      sourceLocator := "T3_page-1.png: connected COF-1 honeycomb assembly" } ]

/-- Nontrivial topology carrier: sharing and functionality independently give
the same six connections, from which the water count follows. -/
def Cof1TopologyAccounting : Prop :=
  cof1CoreMultiplicity * cof1HoneycombSharing.cellsAtCore =
      cof1HoneycombSharing.cornersPerCell ∧
    cof1LinkerMultiplicity * cof1HoneycombSharing.cellsAtLinker =
      cof1HoneycombSharing.edgesPerCell ∧
    cof1CoreMultiplicity * connectionSitesPerB3 =
      cof1LinkerMultiplicity * connectionSitesPerA2 ∧
    cof1WaterMultiplicity =
      watersPerBoronateConnection * cof1ConnectionMultiplicity

/-- Every entry used by the material calculation has a positive multiplicity. -/
def Cof1LedgerHasPositiveMultiplicities : Prop :=
  ∀ entry ∈ cof1MaterialLedger, 0 < entry.multiplicity

/-- Exact closure statement for the finite staged species domain. -/
def Cof1StagedSpeciesDomainSpec : Prop :=
  ∀ species : Species,
    species ∈ cof1StagedSpeciesDomain ↔
      species = .B3 ∨ species = .A2 ∨
        species = .water ∨ species = .cof1Cell

/-- No phase is supplied by the source, so every ledger entry preserves that
unknown rather than inventing a solid, liquid, or gas annotation. -/
def Cof1PhaseLedgerSpec : Prop :=
  ∀ entry ∈ cof1MaterialLedger, entry.phase = .unspecified

/-- None of the depicted structures carries a formal charge. -/
def speciesFormalCharge : Species → ℤ
  | .B3 => 0
  | .A2 => 0
  | .water => 0
  | .cof1Cell => 0

/-- Charge conservation for the complete staged species domain. -/
def Cof1ChargeBalance : Prop :=
  (cof1CoreMultiplicity : ℤ) * speciesFormalCharge .B3 +
      (cof1LinkerMultiplicity : ℤ) * speciesFormalCharge .A2 =
    speciesFormalCharge .cof1Cell +
      (cof1WaterMultiplicity : ℤ) * speciesFormalCharge .water

/-- The water stream fits componentwise inside the reactant inventory. -/
def Cof1WaterLossIsAdmissible : Prop :=
  Formula.CanSubtract cof1ReactantFormula cof1WaterLossFormula

/-- Outcome-decisive atom ledger for the quantitative condensation stage. -/
def Cof1AtomBalance : Prop :=
  cof1ReactantFormula =
    cof1CellFormula + cof1WaterLossFormula

/-- Concrete candidate obtained by primitive reduction of `cof1CellFormula`. -/
def cof1EmpiricalFormula : Formula :=
  { carbon := 9, hydrogen := 4, boron := 1, oxygen := 2 }

/-- Formula output contract, including uniqueness among primitive positive
whole-number divisors of the derived cell formula. -/
def Cof1EmpiricalFormulaSpec : Prop :=
  Formula.IsEmpiricalFormula cof1CellFormula cof1EmpiricalFormula ∧
    ∀ candidate : Formula,
      Formula.IsEmpiricalFormula cof1CellFormula candidate →
        candidate = cof1EmpiricalFormula

/-- A pinned conventional atomic-weight record. -/
structure AtomicWeightDatum where
  element : Element
  value : ℝ
  uncertaintyMetadata : String
  datasetVersion : String
  datasetSha256 : String
  recordSha256 : String

def atomicWeightDatum : Element → AtomicWeightDatum
  | .carbon =>
      { element := .carbon
        value := (12011 : ℝ) / 1000
        uncertaintyMetadata := "0.002"
        datasetVersion :=
          "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+" ++
            "contest-interpretation-v1+trusted-empirical-rules-v1"
        datasetSha256 :=
          "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"
        recordSha256 :=
          "0f558fc72d4299d061e9d29f394ebed43fc8246f7dbdb402bbb2a338cfbe4b8a" }
  | .hydrogen =>
      { element := .hydrogen
        value := (1008 : ℝ) / 1000
        uncertaintyMetadata := "0.0002"
        datasetVersion :=
          "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+" ++
            "contest-interpretation-v1+trusted-empirical-rules-v1"
        datasetSha256 :=
          "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"
        recordSha256 :=
          "8e5f2e512d11f6c3409197956a4f015f6144f43057a286107064436c64b4bce5" }
  | .boron =>
      { element := .boron
        value := (1081 : ℝ) / 100
        uncertaintyMetadata := "0.02"
        datasetVersion :=
          "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+" ++
            "contest-interpretation-v1+trusted-empirical-rules-v1"
        datasetSha256 :=
          "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"
        recordSha256 :=
          "1c5d40bfe965195b46bab8df18add6fbf178bdf4720dcba73b24c61c62038173" }
  | .oxygen =>
      { element := .oxygen
        value := (15999 : ℝ) / 1000
        uncertaintyMetadata := "0.001"
        datasetVersion :=
          "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+" ++
            "contest-interpretation-v1+trusted-empirical-rules-v1"
        datasetSha256 :=
          "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"
        recordSha256 :=
          "d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588" }

def atomicWeight (element : Element) : ℝ :=
  (atomicWeightDatum element).value

/-- Total conventional formula mass; the denominator includes every element,
not merely a carbon-free support or base mass. -/
def formulaMass (formula : Formula) : ℝ :=
  formula.carbon * atomicWeight .carbon +
    formula.hydrogen * atomicWeight .hydrogen +
    formula.boron * atomicWeight .boron +
    formula.oxygen * atomicWeight .oxygen

/-- Carbon mass in one primitive COF-1 empirical unit. -/
def cof1CarbonMass : ℝ :=
  cof1EmpiricalFormula.carbon * atomicWeight .carbon

/-- Exact, unrounded carbon mass percentage.  Its numerator is carbon mass and
its denominator is the total empirical-unit mass. -/
def cof1CarbonMassPercent : ℝ :=
  100 * cof1CarbonMass / formulaMass cof1EmpiricalFormula

/-- The atom ledger induces conservation of conventional formula mass across
the quantitative material stage. -/
def Cof1MassBalance : Prop :=
  formulaMass cof1ReactantFormula =
    formulaMass cof1CellFormula + formulaMass cof1WaterLossFormula

/-- End-to-end raw numerical specification before the reporting boundary. -/
def Cof1CarbonMassPercentDerivationSpec : Prop :=
  cof1CarbonMass = 9 * ((12011 : ℝ) / 1000) ∧
    formulaMass cof1EmpiricalFormula =
      9 * ((12011 : ℝ) / 1000) +
      4 * ((1008 : ℝ) / 1000) +
      ((1081 : ℝ) / 100) +
      2 * ((15999 : ℝ) / 1000) ∧
    0 < formulaMass cof1EmpiricalFormula ∧
    cof1CarbonMassPercent =
      100 * (9 * ((12011 : ℝ) / 1000)) /
        (9 * ((12011 : ℝ) / 1000) +
          4 * ((1008 : ℝ) / 1000) +
          ((1081 : ℝ) / 100) +
          2 * ((15999 : ℝ) / 1000)) ∧
    cof1CarbonMassPercent = (10809900 : ℝ) / 154939

/-- A fixed narrow rational certificate for the exact raw value. -/
def Cof1CarbonMassPercentInterval : Prop :=
  (697687 : ℝ) / 10000 < cof1CarbonMassPercent ∧
    cof1CarbonMassPercent < (697688 : ℝ) / 10000

/-- Raw mixed-output proposition: source topology, complete atom balance,
primitive empirical formula, and the exact unrounded percentage. -/
def RawResultSpec : Prop :=
  Cof1TopologyAccounting ∧
    Cof1LedgerHasPositiveMultiplicities ∧
    Cof1StagedSpeciesDomainSpec ∧
    Cof1PhaseLedgerSpec ∧
    Cof1ChargeBalance ∧
    Cof1WaterLossIsAdmissible ∧
    Cof1AtomBalance ∧
    Cof1MassBalance ∧
    Cof1EmpiricalFormulaSpec ∧
    Cof1CarbonMassPercentDerivationSpec ∧
    Cof1CarbonMassPercentInterval

/-- Reported mixed-output proposition.  The formula remains exact, while the
percentage is rounded once at quantum 0.01 percentage point. -/
def ReportedResultSpec : Prop :=
  Cof1EmpiricalFormulaSpec ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      cof1CarbonMassPercent ((6977 : ℝ) / 100) ((1 : ℝ) / 100)

theorem cof1TopologyAccounting : Cof1TopologyAccounting := by
  norm_num [Cof1TopologyAccounting, cof1ConnectionMultiplicity,
    cof1WaterMultiplicity, cof1CoreMultiplicity, cof1LinkerMultiplicity,
    cof1HoneycombSharing, connectionSitesPerB3, connectionSitesPerA2,
    watersPerBoronateConnection]

theorem cof1LedgerHasPositiveMultiplicities :
    Cof1LedgerHasPositiveMultiplicities := by
  intro entry hEntry
  simp only [cof1MaterialLedger, List.mem_cons, List.not_mem_nil,
    or_false] at hEntry
  rcases hEntry with rfl | rfl | rfl | rfl <;>
    norm_num [cof1CoreMultiplicity, cof1LinkerMultiplicity,
      cof1WaterMultiplicity, cof1ConnectionMultiplicity,
      cof1HoneycombSharing, connectionSitesPerB3,
      watersPerBoronateConnection]

theorem cof1StagedDomainPhaseAndCharge :
    Cof1StagedSpeciesDomainSpec ∧ Cof1PhaseLedgerSpec ∧ Cof1ChargeBalance := by
  constructor
  · intro species
    cases species <;>
      simp [cof1StagedSpeciesDomain]
  constructor
  · intro entry hEntry
    simp only [cof1MaterialLedger, List.mem_cons, List.not_mem_nil,
      or_false] at hEntry
    rcases hEntry with rfl | rfl | rfl | rfl <;> rfl
  · norm_num [Cof1ChargeBalance, cof1CoreMultiplicity,
      cof1LinkerMultiplicity, cof1WaterMultiplicity,
      cof1ConnectionMultiplicity, cof1HoneycombSharing,
      connectionSitesPerB3, watersPerBoronateConnection,
      speciesFormalCharge]

theorem cof1WaterLossIsAdmissible : Cof1WaterLossIsAdmissible := by
  change Formula.CanSubtract
    { carbon := 54, hydrogen := 48, boron := 6, oxygen := 24 }
    { carbon := 0, hydrogen := 24, boron := 0, oxygen := 12 }
  norm_num [Formula.CanSubtract]

theorem cof1AtomBalance : Cof1AtomBalance := by
  change
    ({ carbon := 54, hydrogen := 48, boron := 6, oxygen := 24 } : Formula) =
      { carbon := 54, hydrogen := 24, boron := 6, oxygen := 12 } +
        { carbon := 0, hydrogen := 24, boron := 0, oxygen := 12 }
  rfl

theorem cof1MassBalance : Cof1MassBalance := by
  change
    formulaMass { carbon := 54, hydrogen := 48, boron := 6, oxygen := 24 } =
      formulaMass { carbon := 54, hydrogen := 24, boron := 6, oxygen := 12 } +
        formulaMass { carbon := 0, hydrogen := 24, boron := 0, oxygen := 12 }
  norm_num [formulaMass, atomicWeight, atomicWeightDatum]

theorem cof1EmpiricalFormula_spec : Cof1EmpiricalFormulaSpec := by
  constructor
  · refine ⟨?_, 6, by norm_num, ?_⟩
    · norm_num [Formula.IsPrimitive, Formula.countGCD, cof1EmpiricalFormula]
    · native_decide
  · intro candidate hCandidate
    rcases hCandidate with ⟨⟨_, hPrimitive⟩, multiplicity,
      hMultiplicityPositive, hAssembly⟩
    rcases candidate with
      ⟨candidateCarbon, candidateHydrogen, candidateBoron, candidateOxygen⟩
    change
      ({ carbon := 54, hydrogen := 24, boron := 6, oxygen := 12 } : Formula) =
        Formula.scale multiplicity
          { carbon := candidateCarbon
            hydrogen := candidateHydrogen
            boron := candidateBoron
            oxygen := candidateOxygen } at hAssembly
    have hCarbon : 54 = multiplicity * candidateCarbon := by
      simpa [Formula.scale] using congrArg Formula.carbon hAssembly
    have hHydrogen : 24 = multiplicity * candidateHydrogen := by
      simpa [Formula.scale] using congrArg Formula.hydrogen hAssembly
    have hBoron : 6 = multiplicity * candidateBoron := by
      simpa [Formula.scale] using congrArg Formula.boron hAssembly
    have hOxygen : 12 = multiplicity * candidateOxygen := by
      simpa [Formula.scale] using congrArg Formula.oxygen hAssembly
    have hMultiplicityDivides : multiplicity ∣ 6 :=
      ⟨candidateBoron, hBoron⟩
    have hMultiplicityAtMost : multiplicity ≤ 6 :=
      Nat.le_of_dvd (by norm_num) hMultiplicityDivides
    interval_cases multiplicity
    · have hC : candidateCarbon = 54 := by omega
      have hH : candidateHydrogen = 24 := by omega
      have hB : candidateBoron = 6 := by omega
      have hO : candidateOxygen = 12 := by omega
      subst candidateCarbon
      subst candidateHydrogen
      subst candidateBoron
      subst candidateOxygen
      norm_num [Formula.countGCD] at hPrimitive
    · have hC : candidateCarbon = 27 := by omega
      have hH : candidateHydrogen = 12 := by omega
      have hB : candidateBoron = 3 := by omega
      have hO : candidateOxygen = 6 := by omega
      subst candidateCarbon
      subst candidateHydrogen
      subst candidateBoron
      subst candidateOxygen
      norm_num [Formula.countGCD] at hPrimitive
    · have hC : candidateCarbon = 18 := by omega
      have hH : candidateHydrogen = 8 := by omega
      have hB : candidateBoron = 2 := by omega
      have hO : candidateOxygen = 4 := by omega
      subst candidateCarbon
      subst candidateHydrogen
      subst candidateBoron
      subst candidateOxygen
      norm_num [Formula.countGCD] at hPrimitive
    · omega
    · omega
    · have hC : candidateCarbon = 9 := by omega
      have hH : candidateHydrogen = 4 := by omega
      have hB : candidateBoron = 1 := by omega
      have hO : candidateOxygen = 2 := by omega
      subst candidateCarbon
      subst candidateHydrogen
      subst candidateBoron
      subst candidateOxygen
      rfl

theorem cof1CarbonMassPercent_raw :
    Cof1CarbonMassPercentDerivationSpec ∧
      Cof1CarbonMassPercentInterval := by
  norm_num [Cof1CarbonMassPercentDerivationSpec,
    Cof1CarbonMassPercentInterval, cof1CarbonMassPercent, cof1CarbonMass,
    formulaMass, cof1EmpiricalFormula, atomicWeight, atomicWeightDatum]

theorem rawResultSpec : RawResultSpec := by
  rcases cof1StagedDomainPhaseAndCharge with
    ⟨hDomain, hPhase, hCharge⟩
  rcases cof1CarbonMassPercent_raw with ⟨hPercent, hInterval⟩
  exact ⟨cof1TopologyAccounting, cof1LedgerHasPositiveMultiplicities,
    hDomain, hPhase, hCharge, cof1WaterLossIsAdmissible, cof1AtomBalance,
    cof1MassBalance, cof1EmpiricalFormula_spec, hPercent, hInterval⟩

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"cof1_carbon_mass_percent","reporting_policy_kind":"decimal_places","reporting_policy_digits":2,"reported_value":"69.77","reporting_quantum":"0.01","raw_declaration":"IChO2026Problems.T3A1.cof1CarbonMassPercent","reporting_declaration":"IChO2026Problems.T3A1.cof1CarbonMassPercent_reportsAtQuantum"}
theorem cof1CarbonMassPercent_reportsAtQuantum :
    IChO2026Chem.Reporting.ReportsAtQuantum
      cof1CarbonMassPercent ((6977 : ℝ) / 100) ((1 : ℝ) / 100) := by
  rw [IChO2026Chem.Reporting.ReportsAtQuantum]
  refine ⟨by norm_num, ?_, ?_⟩
  · exact ⟨6977, by norm_num⟩
  · rw [if_pos]
    · constructor <;>
        norm_num [cof1CarbonMassPercent, cof1CarbonMass, formulaMass,
          cof1EmpiricalFormula, atomicWeight, atomicWeightDatum]
    · norm_num [cof1CarbonMassPercent, cof1CarbonMass, formulaMass,
        cof1EmpiricalFormula, atomicWeight, atomicWeightDatum]

theorem reportedResultSpec : ReportedResultSpec := by
  exact ⟨cof1EmpiricalFormula_spec,
    cof1CarbonMassPercent_reportsAtQuantum⟩

/-- Hash-bound solve-phase contract for the exact raw mixed result. -/
theorem blindRawResultContract :
    ("ec98d119a31fc9a3a1c161f485557f6733ab88d508155c0ea3927a7871cbb6be" : String) =
        "ec98d119a31fc9a3a1c161f485557f6733ab88d508155c0ea3927a7871cbb6be" ∧
      RawResultSpec := by
  exact ⟨rfl, rawResultSpec⟩

/-- Hash-bound solve-phase contract for the final exact formula and the
two-decimal carbon percentage. -/
theorem blindReportedResultContract :
    ("86aef1ec845c529ae15e175551f49149a2df2d78d6c9f89783caae51b3c843f1" : String) =
        "86aef1ec845c529ae15e175551f49149a2df2d78d6c9f89783caae51b3c843f1" ∧
      ReportedResultSpec := by
  exact ⟨rfl, reportedResultSpec⟩

end

end IChO2026Problems.T3A1
