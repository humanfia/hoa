import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem.Reporting

/-!
# IChO 2026 T7-A2: annual methane requirement

The source diagram is treated as a quantitative material train.  Its finite
species domain contains exactly methane, steam, carbon monoxide, hydrogen,
oxygen, nitrogen, carbon dioxide, and ammonia; no anonymous material stream is
introduced.  The steam-reforming, partial-oxidation, and water-gas-shift
reactions are quantitative as stipulated by the problem.  The synthesis loop
is instead closed by its steady-state fresh-feed balance and the source's 97.0%
overall yield, because ammonia formation itself is explicitly exempted from
the quantitative-reaction assumption.

The molar masses used at the final mass-conversion boundary come from the
task-authorized offline registry:

* dataset version
  `ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1`;
* dataset SHA-256
  `11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`;
* `CH4` record SHA-256
  `15ac9ec311c79f4d4d38a92c35dd7afaacc40f08349f2c5b468767c77340a1a1`;
* `NH3` record SHA-256
  `6034a27c5509b211ae0fab81674be1d0d63ba9c3bb8cfe336ebe72e0ab33a0b9`.

Registry uncertainty is metadata, not a source measurement.  Thus the nominal
values are conventional exact inputs here, in accordance with the bound
measurement policy.  All masses below use tons, while molar-mass ratios use
the common unit g mol⁻¹ and are therefore dimensionless.
-/

namespace IChO2026Problems.IChO2026T7A2

/-! ## Finite chemical and process domains -/

/-- Every chemical species used in the source diagram and in the requested
mass balance.  There is deliberately no catch-all constructor. -/
inductive Species where
  | methane
  | water
  | carbonMonoxide
  | hydrogen
  | oxygen
  | nitrogen
  | carbonDioxide
  | ammonia
  deriving DecidableEq, Fintype, Repr

/-- Elements occurring in the finite species domain. -/
inductive Element where
  | carbon
  | hydrogen
  | oxygen
  | nitrogen
  deriving DecidableEq, Fintype, Repr

/-- Source-relevant phase information.  The question calls M1 and M2 gas
mixtures; the phase of the separated final ammonia stream is not printed. -/
inductive SourcePhase where
  | gas
  | sourceUnspecified
  deriving DecidableEq, Repr

/-- Named process streams visible in Fig. 1. -/
inductive PlantStream where
  | methaneSteamFeed
  | reformerOutlet
  | airFeed
  | mixture1
  | shiftWaterFeed
  | shiftOutlet
  | scrubberOutlet
  | mixture2
  | ammoniaProduct
  | recycle
  deriving DecidableEq, Fintype, Repr

/-- The target uses the depicted transformations quantitatively: reaction
coefficients and cross-stage material balances determine the requested mass. -/
inductive TransformationUse where
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

/-- Classification required for every depicted transformation used by A2. -/
def targetTransformationUse : TransformationUse :=
  .quantitativeMaterialStage

/-- Atom count in one molecule of each named species. -/
def atomCount : Species → Element → ℕ
  | .methane, .carbon => 1
  | .methane, .hydrogen => 4
  | .water, .hydrogen => 2
  | .water, .oxygen => 1
  | .carbonMonoxide, .carbon => 1
  | .carbonMonoxide, .oxygen => 1
  | .hydrogen, .hydrogen => 2
  | .oxygen, .oxygen => 2
  | .nitrogen, .nitrogen => 2
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .oxygen => 2
  | .ammonia, .nitrogen => 1
  | .ammonia, .hydrogen => 3
  | _, _ => 0

/-- Every molecular species drawn in Fig. 1 is neutral. -/
def formalCharge (_ : Species) : ℤ := 0

/-- The two labeled mixtures are gaseous.  The diagram does not state the
phase of the separated product, so it remains explicitly unspecified. -/
def sourcePhase : PlantStream → SourcePhase
  | .mixture1 | .mixture2 | .recycle => .gas
  | .ammoniaProduct => .sourceUnspecified
  | _ => .gas

/-! ## Reactions transcribed from Fig. 1 -/

/-- `CH4 + H2O -> CO + 3 H2`, the leftmost displayed reaction. -/
def steamReforming : CRNT.Reaction Species where
  source
    | .methane | .water => 1
    | _ => 0
  target
    | .carbonMonoxide => 1
    | .hydrogen => 3
    | _ => 0

/-- `2 CH4 + O2 -> 2 CO + 4 H2`, with the `4 N2 + O2` air feed shown above it. -/
def partialOxidation : CRNT.Reaction Species where
  source
    | .methane => 2
    | .oxygen => 1
    | _ => 0
  target
    | .carbonMonoxide => 2
    | .hydrogen => 4
    | _ => 0

/-- `CO + H2O -> CO2 + H2`, the water-gas-shift reaction. -/
def waterGasShift : CRNT.Reaction Species where
  source
    | .carbonMonoxide | .water => 1
    | _ => 0
  target
    | .carbonDioxide | .hydrogen => 1
    | _ => 0

/-- `N2 + 3 H2 <-> 2 NH3`, whose nonquantitative status is preserved. -/
def ammoniaFormation : CRNT.Reaction Species where
  source
    | .nitrogen => 1
    | .hydrogen => 3
    | _ => 0
  target
    | .ammonia => 2
    | _ => 0

/-- Atom-level conservation ledger for a reaction. -/
def AtomBalanced (reaction : CRNT.Reaction Species) : Prop :=
  ∀ element : Element,
    (∑ species : Species,
        reaction.source species * atomCount species element) =
      ∑ species : Species,
        reaction.target species * atomCount species element

/-- Charge-level conservation ledger for a reaction. -/
def ChargeBalanced (reaction : CRNT.Reaction Species) : Prop :=
  (∑ species : Species,
      (reaction.source species : ℤ) * formalCharge species) =
    ∑ species : Species,
      (reaction.target species : ℤ) * formalCharge species

/-- The four displayed reaction equations pass their atom ledgers. -/
theorem displayedReactions_atomBalanced :
    AtomBalanced steamReforming ∧
      AtomBalanced partialOxidation ∧
      AtomBalanced waterGasShift ∧
      AtomBalanced ammoniaFormation := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    intro element <;>
    fin_cases element <;>
    native_decide

/-- The four displayed reaction equations pass their charge ledgers. -/
theorem displayedReactions_chargeBalanced :
    ChargeBalanced steamReforming ∧
      ChargeBalanced partialOxidation ∧
      ChargeBalanced waterGasShift ∧
      ChargeBalanced ammoniaFormation := by
  simp [ChargeBalanced, formalCharge]

/-! ## Quantitative fresh-gas train and the inline T7-A1 derivation -/

/-- A stream amount is a molar amount for each member of the finite species
domain, all on one common process basis. -/
abbrev StreamAmount := Species → ℝ

/-- Pointwise addition of a named external feed to a stream. -/
def addStream (first second : StreamAmount) : StreamAmount :=
  fun species => first species + second species

/-- Initial feed labeled `x CH4 + y H2O`. -/
def methaneSteamFeedAmount (x y : ℝ) : StreamAmount
  | .methane => x
  | .water => y
  | _ => 0

/-- Outlet after the water-limited quantitative steam-reforming reaction. -/
def reformerOutletAmount (x y : ℝ) : StreamAmount
  | .methane => x - y
  | .carbonMonoxide => y
  | .hydrogen => 3 * y
  | _ => 0

/-- Air feed required by the quantitative partial oxidation of the methane
remaining after reforming.  Its nitrogen-to-oxygen ratio is the displayed 4:1. -/
noncomputable def airFeedAmount (x y : ℝ) : StreamAmount
  | .oxygen => (x - y) / 2
  | .nitrogen => 4 * ((x - y) / 2)
  | _ => 0

/-- Mixture M1 after quantitative partial oxidation. -/
def mixture1Amount (x y : ℝ) : StreamAmount
  | .carbonMonoxide => x
  | .hydrogen => 2 * x + y
  | .nitrogen => 2 * (x - y)
  | _ => 0

/-- The separately drawn water feed needed to shift all `x` moles of CO. -/
def shiftWaterFeedAmount (x : ℝ) : StreamAmount
  | .water => x
  | _ => 0

/-- Outlet after the quantitative water-gas-shift reaction. -/
def shiftOutletAmount (x y : ℝ) : StreamAmount
  | .hydrogen => 3 * x + y
  | .nitrogen => 2 * (x - y)
  | .carbonDioxide => x
  | _ => 0

/-- Fresh synthesis gas after the CO2 scrubber. -/
def scrubberOutletAmount (x y : ℝ) : StreamAmount
  | .hydrogen => 3 * x + y
  | .nitrogen => 2 * (x - y)
  | _ => 0

/-- One quantitative firing of a CRNT reaction at a real extent. -/
def ReactionExtentStep
    (before after : StreamAmount) (reaction : CRNT.Reaction Species)
    (extent : ℝ) : Prop :=
  ∀ species : Species,
    after species = before species + extent * reaction.vector species

/-- The scrubber removes exactly the named carbon-dioxide stream and no other
member of the finite domain. -/
def CarbonDioxideScrubberStep
    (before after : StreamAmount) (removed : ℝ) : Prop :=
  removed ≥ 0 ∧
    before .carbonDioxide = after .carbonDioxide + removed ∧
    after .carbonDioxide = 0 ∧
    ∀ species : Species, species ≠ .carbonDioxide →
      after species = before species

/-- Every amount in a physical stream is nonnegative. -/
def StreamNonnegative (amount : StreamAmount) : Prop :=
  ∀ species : Species, 0 ≤ amount species

/-- Source-side domain conditions for the water-limited first reaction and the
positive partial-oxidation branch visible in the diagram. -/
def FreshTrainAdmissible (x y : ℝ) : Prop :=
  0 < y ∧ y < x

/-- Complete quantitative stage ledger from the labeled feed through the CO2
scrubber.  Every external material stream is named explicitly. -/
def FreshTrainQuantitativeLedger (x y : ℝ) : Prop :=
  ReactionExtentStep
      (methaneSteamFeedAmount x y) (reformerOutletAmount x y)
      steamReforming y ∧
    ReactionExtentStep
      (addStream (reformerOutletAmount x y) (airFeedAmount x y))
      (mixture1Amount x y) partialOxidation ((x - y) / 2) ∧
    ReactionExtentStep
      (addStream (mixture1Amount x y) (shiftWaterFeedAmount x))
      (shiftOutletAmount x y) waterGasShift x ∧
    CarbonDioxideScrubberStep
      (shiftOutletAmount x y) (scrubberOutletAmount x y) x ∧
    StreamNonnegative (methaneSteamFeedAmount x y) ∧
    StreamNonnegative (reformerOutletAmount x y) ∧
    StreamNonnegative (airFeedAmount x y) ∧
    StreamNonnegative (mixture1Amount x y) ∧
    StreamNonnegative (shiftOutletAmount x y) ∧
    StreamNonnegative (scrubberOutletAmount x y)

/-- The recycle loop has no drawn purge or other material outlet.  On an
annual steady-state basis, the fresh nitrogen and hydrogen therefore leave the
loop only in ammonia.  The two equations are respectively the N-atom and
H-atom ledgers; they do not assert quantitative single-pass conversion. -/
def ClosedRecycleSteadyStateLedger (x y ammoniaMoles : ℝ) : Prop :=
  0 < ammoniaMoles ∧
    ammoniaMoles = 2 * scrubberOutletAmount x y .nitrogen ∧
    3 * ammoniaMoles = 2 * scrubberOutletAmount x y .hydrogen

/-- Complete source model for one arbitrary positive fresh-feed basis. -/
def PlantFreshFeedModel (x y ammoniaMoles : ℝ) : Prop :=
  FreshTrainAdmissible x y ∧
    FreshTrainQuantitativeLedger x y ∧
    ClosedRecycleSteadyStateLedger x y ammoniaMoles

/-- Gas presence in a stream is positive molar amount. -/
def GasPresent (amount : StreamAmount) (species : Species) : Prop :=
  0 < amount species

/-- M1 contains exactly the three gases identified by the source-first stage
balance: CO, H2, and N2.  This derives rather than assumes the relevant A1 fact. -/
def Mixture1GasConclusion (x y : ℝ) : Prop :=
  GasPresent (mixture1Amount x y) .carbonMonoxide ∧
    GasPresent (mixture1Amount x y) .hydrogen ∧
    GasPresent (mixture1Amount x y) .nitrogen ∧
    ∀ species : Species,
      GasPresent (mixture1Amount x y) species →
        species = .carbonMonoxide ∨ species = .hydrogen ∨ species = .nitrogen

/-- Parameters for a nonzero but incomplete pass through the equilibrium
ammonia reactor drawn in Fig. 1. -/
structure AmmoniaLoopPass where
  nitrogenIn : ℝ
  hydrogenIn : ℝ
  extent : ℝ
  nitrogenIn_pos : 0 < nitrogenIn
  stoichiometricFeed : hydrogenIn = 3 * nitrogenIn
  extent_pos : 0 < extent
  extent_lt_nitrogen : extent < nitrogenIn

/-- Mixture M2, immediately after the nonquantitative ammonia reaction and
before the cooler. -/
def mixture2Amount (pass : AmmoniaLoopPass) : StreamAmount
  | .nitrogen => pass.nitrogenIn - pass.extent
  | .hydrogen => pass.hydrogenIn - 3 * pass.extent
  | .ammonia => 2 * pass.extent
  | _ => 0

/-- M2 contains exactly unreacted N2, unreacted H2, and formed NH3. -/
def Mixture2GasConclusion (pass : AmmoniaLoopPass) : Prop :=
  GasPresent (mixture2Amount pass) .nitrogen ∧
    GasPresent (mixture2Amount pass) .hydrogen ∧
    GasPresent (mixture2Amount pass) .ammonia ∧
    ∀ species : Species,
      GasPresent (mixture2Amount pass) species →
        species = .nitrogen ∨ species = .hydrogen ∨ species = .ammonia

/-- Inline derivation of the M1 gas conclusion from the quantitative stages. -/
theorem a1_mixture1_gases
    {x y : ℝ} (h : FreshTrainAdmissible x y) :
    Mixture1GasConclusion x y := by
  rcases h with ⟨hy, hyx⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 < x
    linarith
  · change 0 < 2 * x + y
    linarith
  · change 0 < 2 * (x - y)
    linarith
  · intro species hs
    fin_cases species <;>
      simp_all [GasPresent, mixture1Amount]

/-- Inline derivation of the M2 gas conclusion from a genuine incomplete
equilibrium pass; no quantitative ammonia-conversion premise is used. -/
theorem a1_mixture2_gases (pass : AmmoniaLoopPass) :
    Mixture2GasConclusion pass := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 < pass.nitrogenIn - pass.extent
    linarith [pass.extent_lt_nitrogen]
  · change 0 < pass.hydrogenIn - 3 * pass.extent
    rw [pass.stoichiometricFeed]
    linarith [pass.extent_lt_nitrogen]
  · change 0 < 2 * pass.extent
    linarith [pass.extent_pos]
  · intro species hs
    fin_cases species <;>
      simp_all [GasPresent, mixture2Amount]

/-- The A1 relationship forced by the upstream balances and the closed-loop
steady-state atom ledgers. -/
theorem a1_methane_steam_relation
    {x y ammoniaMoles : ℝ} (h : PlantFreshFeedModel x y ammoniaMoles) :
    7 * y = 3 * x := by
  rcases h.2.2 with ⟨_, hnitrogen, hhydrogen⟩
  simp only [scrubberOutletAmount] at hnitrogen hhydrogen
  linarith

/-- Equivalent quotient form of the A1 relationship. -/
theorem a1_methane_steam_ratio
    {x y ammoniaMoles : ℝ} (h : PlantFreshFeedModel x y ammoniaMoles) :
    x / y = (7 : ℝ) / 3 := by
  have hy : y ≠ 0 := ne_of_gt h.1.1
  apply (div_eq_iff hy).2
  have hrelation := a1_methane_steam_relation h
  linarith

/-- Cross-stage mole ledger used by A2: every admissible fresh-feed basis has
16 moles of ammonia per 7 moles of methane. -/
theorem ideal_ammonia_methane_mole_ledger
    {x y ammoniaMoles : ℝ} (h : PlantFreshFeedModel x y ammoniaMoles) :
    7 * ammoniaMoles = 16 * x := by
  have hrelation := a1_methane_steam_relation h
  rcases h.2.2 with ⟨_, hnitrogen, _⟩
  simp only [scrubberOutletAmount] at hnitrogen
  linarith

/-- The source model is inhabited independently of the requested annual
quantity, so its universal stoichiometric conclusion is nonvacuous. -/
theorem plantFreshFeedModel_nonempty :
    ∃ x y ammoniaMoles : ℝ, PlantFreshFeedModel x y ammoniaMoles := by
  refine ⟨7, 3, 16, ?_⟩
  refine ⟨by norm_num [FreshTrainAdmissible], ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro species
      fin_cases species <;>
        norm_num [ReactionExtentStep, methaneSteamFeedAmount,
          reformerOutletAmount, steamReforming, CRNT.Reaction.vector]
    · intro species
      fin_cases species <;>
        norm_num [ReactionExtentStep, addStream, reformerOutletAmount,
          airFeedAmount, mixture1Amount, partialOxidation,
          CRNT.Reaction.vector]
    · intro species
      fin_cases species <;>
        norm_num [ReactionExtentStep, addStream, mixture1Amount,
          shiftWaterFeedAmount, shiftOutletAmount, waterGasShift,
          CRNT.Reaction.vector]
    · refine ⟨by norm_num, by norm_num [shiftOutletAmount,
        scrubberOutletAmount], by norm_num [scrubberOutletAmount], ?_⟩
      intro species hspecies
      fin_cases species <;>
        simp_all [shiftOutletAmount, scrubberOutletAmount]
    · intro species
      fin_cases species <;>
        norm_num [methaneSteamFeedAmount]
    · intro species
      fin_cases species <;>
        norm_num [reformerOutletAmount]
    · intro species
      fin_cases species <;>
        norm_num [airFeedAmount]
    · intro species
      fin_cases species <;>
        norm_num [mixture1Amount]
    · intro species
      fin_cases species <;>
        norm_num [shiftOutletAmount]
    · intro species
      fin_cases species <;>
        norm_num [scrubberOutletAmount]
  · norm_num [ClosedRecycleSteadyStateLedger, scrubberOutletAmount]

/-- Nonvacuous, source-derived stoichiometric specification used at the mass
conversion boundary. -/
def SourceStoichiometricRatioSpec : Prop :=
  (∃ x y ammoniaMoles : ℝ, PlantFreshFeedModel x y ammoniaMoles) ∧
    ∀ x y ammoniaMoles : ℝ,
      PlantFreshFeedModel x y ammoniaMoles →
        7 * ammoniaMoles = 16 * x

theorem sourceStoichiometricRatioSpec_holds :
    SourceStoichiometricRatioSpec := by
  refine ⟨plantFreshFeedModel_nonempty, ?_⟩
  intro x y ammoniaMoles h
  exact ideal_ammonia_methane_mole_ledger h

/-! ## Registry data and annual mass balance -/

/-- Auditable record for a nominal molar mass supplied by the pinned offline
registry. -/
structure MolarMassRegistryRecord where
  formula : String
  valueGramsPerMole : ℝ
  datasetVersion : String
  datasetSHA256 : String
  recordSHA256 : String

/-- Pinned registry record for methane. -/
noncomputable def methaneMolarMassRecord : MolarMassRegistryRecord :=
  { formula := "CH4"
    valueGramsPerMole := (16043 : ℝ) / 1000
    datasetVersion :=
      "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1"
    datasetSHA256 :=
      "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"
    recordSHA256 :=
      "15ac9ec311c79f4d4d38a92c35dd7afaacc40f08349f2c5b468767c77340a1a1" }

/-- Pinned registry record for ammonia. -/
noncomputable def ammoniaMolarMassRecord : MolarMassRegistryRecord :=
  { formula := "NH3"
    valueGramsPerMole := (17031 : ℝ) / 1000
    datasetVersion :=
      "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1"
    datasetSHA256 :=
      "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"
    recordSHA256 :=
      "6034a27c5509b211ae0fab81674be1d0d63ba9c3bb8cfe336ebe72e0ab33a0b9" }

/-- Conventional nominal methane molar mass, in g mol⁻¹. -/
noncomputable def methaneMolarMass : ℝ :=
  methaneMolarMassRecord.valueGramsPerMole

/-- Conventional nominal ammonia molar mass, in g mol⁻¹. -/
noncomputable def ammoniaMolarMass : ℝ :=
  ammoniaMolarMassRecord.valueGramsPerMole

/-- Requested actual ammonia production, in tons per year. -/
def annualAmmoniaMass : ℝ := 660000

/-- Problem-stipulated overall yield `97.0%`, used exactly as printed. -/
noncomputable def overallYield : ℝ := (97 : ℝ) / 100

/-- A common-batch mass ledger.  Dividing each mass by its molar mass gives a
mole amount in the same scaled mass unit; both sides equal the number of
source-model reaction batches. -/
noncomputable def BatchScaledMassLedger
    (methaneMass theoreticalAmmoniaMass x ammoniaMoles : ℝ) : Prop :=
  0 < x ∧ 0 < ammoniaMoles ∧
    (methaneMass / methaneMolarMass) / x =
      (theoreticalAmmoniaMass / ammoniaMolarMass) / ammoniaMoles

/-- Full annual material and yield model.  The numerator of the yield is the
actual 660,000-ton ammonia product; its denominator is the theoretical ammonia
mass from the same methane feed. -/
def AnnualProductionBalance
    (methaneMass theoreticalAmmoniaMass actualAmmoniaMass : ℝ) : Prop :=
  0 < methaneMass ∧ 0 < theoreticalAmmoniaMass ∧
    (∃ x y ammoniaMoles : ℝ,
      PlantFreshFeedModel x y ammoniaMoles ∧
        BatchScaledMassLedger
          methaneMass theoreticalAmmoniaMass x ammoniaMoles) ∧
    actualAmmoniaMass = overallYield * theoreticalAmmoniaMass

/-- Exact, end-to-end methane requirement in tons per year.  No intermediate
rounding occurs. -/
noncomputable def annualMethaneMassRaw : ℝ :=
  annualAmmoniaMass / overallYield *
    ((7 : ℝ) * methaneMolarMass) /
      ((16 : ℝ) * ammoniaMolarMass)

/-- Problem-specific raw derivation specification.  It binds the universal,
nonvacuous source stoichiometry, the annual mass/yield balance, and uniqueness
of the positive methane input satisfying that same source model. -/
def AnnualMethaneMassDerivationSpec (methaneMass : ℝ) : Prop :=
  SourceStoichiometricRatioSpec ∧
    (∃ theoreticalAmmoniaMass : ℝ,
      AnnualProductionBalance
        methaneMass theoreticalAmmoniaMass annualAmmoniaMass) ∧
    ∀ candidateMass theoreticalAmmoniaMass : ℝ,
      AnnualProductionBalance
          candidateMass theoreticalAmmoniaMass annualAmmoniaMass →
        candidateMass = methaneMass

/-- Zero-argument proposition named for the answer-blind raw result contract. -/
def AnnualMethaneMassRawDerivationSpec : Prop :=
  AnnualMethaneMassDerivationSpec annualMethaneMassRaw

/-- Exact rational evaluation, useful to the later proof without changing the
source-level definition of the raw quantity. -/
theorem annualMethaneMassRaw_eq :
    annualMethaneMassRaw = (22059125000 : ℝ) / 78667 := by
  norm_num [annualMethaneMassRaw, annualAmmoniaMass, overallYield,
    methaneMolarMass, methaneMolarMassRecord, ammoniaMolarMass,
    ammoniaMolarMassRecord]

/-- Raw answer-blind result contract.  The one-ton-wide rational enclosure is
an independently fixed certificate interval, not a source measurement error or
an equality to a rounded decimal. -/
theorem annualMethaneMass_raw_result :
    AnnualMethaneMassRawDerivationSpec ∧
      ((280411 : ℝ) ≤ annualMethaneMassRaw ∧
        annualMethaneMassRaw ≤ (280412 : ℝ)) := by
  constructor
  · unfold AnnualMethaneMassRawDerivationSpec
    unfold AnnualMethaneMassDerivationSpec
    refine ⟨sourceStoichiometricRatioSpec_holds, ?_, ?_⟩
    · obtain ⟨x, y, ammoniaMoles, hmodel⟩ :=
        plantFreshFeedModel_nonempty
      have hx : 0 < x := lt_trans hmodel.1.1 hmodel.1.2
      have hammonia : 0 < ammoniaMoles := hmodel.2.2.1
      have hstoich := ideal_ammonia_methane_mole_ledger hmodel
      have hx_formula : x = (7 / 16 : ℝ) * ammoniaMoles := by
        linarith
      refine ⟨annualAmmoniaMass / overallYield, ?_⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [annualMethaneMassRaw_eq]
        norm_num
      · norm_num [annualAmmoniaMass, overallYield]
      · refine ⟨x, y, ammoniaMoles, hmodel, ?_⟩
        refine ⟨hx, hammonia, ?_⟩
        rw [hx_formula]
        dsimp [annualMethaneMassRaw, annualAmmoniaMass, overallYield,
          methaneMolarMass, methaneMolarMassRecord, ammoniaMolarMass,
          ammoniaMolarMassRecord]
        field_simp [ne_of_gt hammonia]
      · norm_num [annualAmmoniaMass, overallYield]
    · intro candidateMass theoreticalAmmoniaMass hbalance
      rcases hbalance with
        ⟨_, _, ⟨x, y, ammoniaMoles, hmodel, hbatch⟩, hyield⟩
      rcases hbatch with ⟨hx, hammonia, hbatch⟩
      have hstoich := ideal_ammonia_methane_mole_ledger hmodel
      have hx_formula : x = (7 / 16 : ℝ) * ammoniaMoles := by
        linarith
      have htheoretical :
          theoreticalAmmoniaMass = annualAmmoniaMass / overallYield := by
        norm_num [annualAmmoniaMass, overallYield] at hyield ⊢
        linarith
      subst theoreticalAmmoniaMass
      rw [hx_formula] at hbatch
      dsimp [annualAmmoniaMass, overallYield, methaneMolarMass,
        methaneMolarMassRecord, ammoniaMolarMass,
        ammoniaMolarMassRecord] at hbatch
      field_simp [ne_of_gt hammonia] at hbatch
      rw [annualMethaneMassRaw_eq]
      norm_num at hbatch ⊢
      linarith
  · rw [annualMethaneMassRaw_eq]
    constructor <;> norm_num

/-- Three significant figures at this magnitude have a 1000-ton reporting
quantum.  `ReportsAtQuantum` supplies the project-wide half-away-from-zero tie
rule at the final boundary only. -/
def AnnualMethaneMassReportedSpec : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum
    annualMethaneMassRaw (280000 : ℝ) (1000 : ℝ)

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"annual_methane_mass","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"2.80e5","reporting_quantum":"1000","raw_declaration":"IChO2026Problems.IChO2026T7A2.annualMethaneMassRaw","reporting_declaration":"IChO2026Problems.IChO2026T7A2.annualMethaneMass_reported_result"}
theorem annualMethaneMass_reported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      annualMethaneMassRaw (280000 : ℝ) (1000 : ℝ) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨(280 : ℤ), by norm_num⟩, ?_⟩
  have hbounds := annualMethaneMass_raw_result.2
  have hnonnegative : 0 ≤ annualMethaneMassRaw := by
    linarith [hbounds.1]
  rw [if_pos hnonnegative]
  constructor <;> norm_num <;> linarith

end IChO2026Problems.IChO2026T7A2
