import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem.Reporting

/-!
# IChO 2026 T7-A2: annual methane requirement

The material-flow diagram is formalized on the basis printed beside the air
feed: one mole of `O₂` together with four moles of `N₂`.  Every species that
occurs in an outcome-relevant stream is represented below; there is no
anonymous residual stream.  The three reforming/shift reactions are treated as
quantitative, whereas ammonia formation is represented by an incomplete pass
followed by product removal and recycle.

The requested numerical answer is kept as an exact real expression until the
single final three-significant-figure reporting boundary.
-/

namespace IChO2026Problems.T7A2

noncomputable section

/-- The complete species domain used in the quantitative plant balance. -/
inductive PlantSpecies
  | methane
  | water
  | carbonMonoxide
  | hydrogen
  | oxygen
  | nitrogen
  | carbonDioxide
  | ammonia
  deriving DecidableEq, Fintype

/-- Elements whose conservation is outcome-relevant in the depicted plant. -/
inductive Element
  | carbon
  | hydrogen
  | oxygen
  | nitrogen
  deriving DecidableEq, Fintype

/-- All depicted reaction-stage species are gases; the source does not specify
the phase of the ammonia after the cooler. -/
inductive Phase
  | gas
  | sourceUnspecified
  deriving DecidableEq

/-- The hot reaction-stage phase shown by the gas-stream diagram. -/
def hotStagePhase (_ : PlantSpecies) : Phase := .gas

/-- The product phase after `CLR` is deliberately left at the source's level of
specificity. -/
def cooledAmmoniaPhase : Phase := .sourceUnspecified

/-- Atom count of one molecule of each species.  All eight species are neutral. -/
def atomCount : PlantSpecies → Element → ℕ
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

/-- Formal charge of every molecular species in the source diagram. -/
def formalCharge (_ : PlantSpecies) : ℤ := 0

/-- The finite, source-derived species domain used by every stage ledger. -/
def stageSpeciesDomain : Finset PlantSpecies := Finset.univ

/-- Stoichiometric complex `CH₄ + H₂O`. -/
def steamReformingSource : CRNT.Complex PlantSpecies
  | .methane => 1
  | .water => 1
  | _ => 0

/-- Stoichiometric complex `CO + 3 H₂`. -/
def steamReformingTarget : CRNT.Complex PlantSpecies
  | .carbonMonoxide => 1
  | .hydrogen => 3
  | _ => 0

/-- The primary steam-reforming reaction printed in Fig. 1. -/
def steamReforming : CRNT.Reaction PlantSpecies where
  source := steamReformingSource
  target := steamReformingTarget

/-- Stoichiometric complex `2 CH₄ + O₂`. -/
def partialOxidationSource : CRNT.Complex PlantSpecies
  | .methane => 2
  | .oxygen => 1
  | _ => 0

/-- Stoichiometric complex `2 CO + 4 H₂`. -/
def partialOxidationTarget : CRNT.Complex PlantSpecies
  | .carbonMonoxide => 2
  | .hydrogen => 4
  | _ => 0

/-- The secondary reforming/partial-oxidation reaction printed in Fig. 1. -/
def partialOxidation : CRNT.Reaction PlantSpecies where
  source := partialOxidationSource
  target := partialOxidationTarget

/-- Stoichiometric complex `CO + H₂O`. -/
def waterGasShiftSource : CRNT.Complex PlantSpecies
  | .carbonMonoxide => 1
  | .water => 1
  | _ => 0

/-- Stoichiometric complex `CO₂ + H₂`. -/
def waterGasShiftTarget : CRNT.Complex PlantSpecies
  | .carbonDioxide => 1
  | .hydrogen => 1
  | _ => 0

/-- The quantitative water-gas-shift reaction printed in Fig. 1. -/
def waterGasShift : CRNT.Reaction PlantSpecies where
  source := waterGasShiftSource
  target := waterGasShiftTarget

/-- Stoichiometric complex `N₂ + 3 H₂`. -/
def ammoniaSynthesisSource : CRNT.Complex PlantSpecies
  | .nitrogen => 1
  | .hydrogen => 3
  | _ => 0

/-- Stoichiometric complex `2 NH₃`. -/
def ammoniaSynthesisTarget : CRNT.Complex PlantSpecies
  | .ammonia => 2
  | _ => 0

/-- The forward direction of the reversible ammonia-synthesis reaction. -/
def ammoniaSynthesis : CRNT.Reaction PlantSpecies where
  source := ammoniaSynthesisSource
  target := ammoniaSynthesisTarget

/-- A stream gives the molar amount of every species on the fixed air basis. -/
abbrev AmountStream := PlantSpecies → ℝ

/-- Nonnegativity condition for every member of the complete species domain. -/
def NonnegativeStream (s : AmountStream) : Prop :=
  ∀ species, 0 ≤ s species

/-- Total amount of an element in a stream, in moles of atoms. -/
def atomTotal (s : AmountStream) (element : Element) : ℝ :=
  ∑ species, s species * atomCount species element

/-- Total formal charge in a stream. -/
def chargeTotal (s : AmountStream) : ℝ :=
  ∑ species, s species * formalCharge species

/-- Unknown feed amounts and quantitative reaction extents on the source's
`1 O₂ + 4 N₂` basis. -/
structure PlantBasis where
  methaneFeed : ℝ
  steamFeed : ℝ
  steamReformingExtent : ℝ
  partialOxidationExtent : ℝ
  waterGasShiftExtent : ℝ

/-- The named external methane/steam feed at the top left of Fig. 1. -/
def primaryFeed (b : PlantBasis) : AmountStream
  | .methane => b.methaneFeed
  | .water => b.steamFeed
  | _ => 0

/-- Stream after quantitative primary reforming. -/
def afterPrimaryReformer (b : PlantBasis) : AmountStream
  | .methane => b.methaneFeed - b.steamReformingExtent
  | .water => b.steamFeed - b.steamReformingExtent
  | .carbonMonoxide => b.steamReformingExtent
  | .hydrogen => 3 * b.steamReformingExtent
  | _ => 0

/-- The explicitly printed air packet `4 N₂ + 1 O₂`. -/
def airFeed : AmountStream
  | .oxygen => 1
  | .nitrogen => 4
  | _ => 0

/-- Mixture M1 after quantitative partial oxidation. -/
def afterSecondaryReformer (b : PlantBasis) : AmountStream
  | .methane =>
      b.methaneFeed - b.steamReformingExtent - 2 * b.partialOxidationExtent
  | .water => b.steamFeed - b.steamReformingExtent
  | .carbonMonoxide =>
      b.steamReformingExtent + 2 * b.partialOxidationExtent
  | .hydrogen =>
      3 * b.steamReformingExtent + 4 * b.partialOxidationExtent
  | .oxygen => 1 - b.partialOxidationExtent
  | .nitrogen => 4
  | .carbonDioxide => 0
  | .ammonia => 0

/-- Named water input to the water-gas-shift reactor. -/
def shiftWaterFeed (b : PlantBasis) : AmountStream
  | .water => b.waterGasShiftExtent
  | _ => 0

/-- Stream sent from the shift reactor to the CO₂ scrubber. -/
def afterWaterGasShift (b : PlantBasis) : AmountStream
  | .methane =>
      b.methaneFeed - b.steamReformingExtent - 2 * b.partialOxidationExtent
  | .water => b.steamFeed - b.steamReformingExtent
  | .carbonMonoxide =>
      b.steamReformingExtent + 2 * b.partialOxidationExtent -
        b.waterGasShiftExtent
  | .hydrogen =>
      3 * b.steamReformingExtent + 4 * b.partialOxidationExtent +
        b.waterGasShiftExtent
  | .oxygen => 1 - b.partialOxidationExtent
  | .nitrogen => 4
  | .carbonDioxide => b.waterGasShiftExtent
  | .ammonia => 0

/-- Carbon dioxide removed by scrubber `Z`; no catch-all removal stream is used. -/
def scrubbedCarbonDioxide (b : PlantBasis) : AmountStream
  | .carbonDioxide => b.waterGasShiftExtent
  | _ => 0

/-- The `N₂, H₂` synthesis feed obtained after quantitative CO₂ scrubbing. -/
def synthesisFeed (b : PlantBasis) : AmountStream
  | .hydrogen => afterWaterGasShift b .hydrogen
  | .nitrogen => afterWaterGasShift b .nitrogen
  | _ => 0

/-- The explicitly source-supported gas set in mixture M1. -/
def m1GasSet : Finset PlantSpecies :=
  {.nitrogen, .carbonMonoxide, .hydrogen}

/-- An incomplete ammonia-synthesis pass, left unspecified quantitatively. -/
structure SynthesisPass where
  extent : ℝ

/-- "Except NH₃ formation" is represented by positive but incomplete forward
conversion on the four-mole nitrogen basis. -/
def IncompleteSynthesisPass (p : SynthesisPass) : Prop :=
  0 < p.extent ∧ p.extent < 4

/-- Mixture M2 between the synthesis reactor and cooler. -/
def mixtureM2 (p : SynthesisPass) : AmountStream
  | .nitrogen => 4 - p.extent
  | .hydrogen => 12 - 3 * p.extent
  | .ammonia => 2 * p.extent
  | _ => 0

/-- The explicitly source-supported gas set in mixture M2. -/
def m2GasSet : Finset PlantSpecies :=
  {.nitrogen, .hydrogen, .ammonia}

/-- Source assumptions and quantitative material balances for Fig. 1.

The vanishing components spell out the depicted stream labels.  The last
equation is the `N₂ + 3 H₂` synthesis-feed ratio printed in the reactor. -/
def OperatesAccordingToFigure (b : PlantBasis) : Prop :=
  0 ≤ b.methaneFeed ∧
  0 ≤ b.steamFeed ∧
  0 ≤ b.steamReformingExtent ∧
  0 ≤ b.partialOxidationExtent ∧
  0 ≤ b.waterGasShiftExtent ∧
  NonnegativeStream (primaryFeed b) ∧
  NonnegativeStream (afterPrimaryReformer b) ∧
  NonnegativeStream (afterSecondaryReformer b) ∧
  NonnegativeStream (afterWaterGasShift b) ∧
  b.steamReformingExtent = b.steamFeed ∧
  b.partialOxidationExtent = 1 ∧
  afterSecondaryReformer b .methane = 0 ∧
  afterSecondaryReformer b .water = 0 ∧
  afterSecondaryReformer b .oxygen = 0 ∧
  b.waterGasShiftExtent = afterSecondaryReformer b .carbonMonoxide ∧
  afterWaterGasShift b .carbonMonoxide = 0 ∧
  afterWaterGasShift b .water = 0 ∧
  afterWaterGasShift b .oxygen = 0 ∧
  synthesisFeed b .hydrogen = 3 * synthesisFeed b .nitrogen

/-- Atom-level conservation ledger for the primary reformer. -/
def PrimaryAtomLedger (b : PlantBasis) : Prop :=
  ∀ element, atomTotal (afterPrimaryReformer b) element =
    atomTotal (primaryFeed b) element

/-- Atom-level conservation ledger for secondary reforming, including the
named air input. -/
def SecondaryAtomLedger (b : PlantBasis) : Prop :=
  ∀ element, atomTotal (afterSecondaryReformer b) element =
    atomTotal (afterPrimaryReformer b) element + atomTotal airFeed element

/-- Atom-level conservation ledger for the shift stage and its named water input. -/
def ShiftAtomLedger (b : PlantBasis) : Prop :=
  ∀ element, atomTotal (afterWaterGasShift b) element =
    atomTotal (afterSecondaryReformer b) element + atomTotal (shiftWaterFeed b) element

/-- Atom-level partition ledger for quantitative CO₂ scrubbing. -/
def ScrubberAtomLedger (b : PlantBasis) : Prop :=
  ∀ element, atomTotal (afterWaterGasShift b) element =
    atomTotal (synthesisFeed b) element + atomTotal (scrubbedCarbonDioxide b) element

/-- Charge conservation ledger for all outcome-relevant quantitative stages. -/
def QuantitativeChargeLedgers (b : PlantBasis) : Prop :=
  chargeTotal (afterPrimaryReformer b) = chargeTotal (primaryFeed b) ∧
  chargeTotal (afterSecondaryReformer b) =
    chargeTotal (afterPrimaryReformer b) + chargeTotal airFeed ∧
  chargeTotal (afterWaterGasShift b) =
    chargeTotal (afterSecondaryReformer b) + chargeTotal (shiftWaterFeed b) ∧
  chargeTotal (afterWaterGasShift b) =
    chargeTotal (synthesisFeed b) + chargeTotal (scrubbedCarbonDioxide b)

/-- Expansion of a species sum over the fixed eight-member plant domain. -/
private lemma sum_plantSpecies (f : PlantSpecies → ℝ) :
    ∑ species, f species =
      f .methane + f .water + f .carbonMonoxide + f .hydrogen +
        f .oxygen + f .nitrogen + f .carbonDioxide + f .ammonia := by
  classical
  rw [show (Finset.univ : Finset PlantSpecies) =
    {.methane, .water, .carbonMonoxide, .hydrogen, .oxygen, .nitrogen,
      .carbonDioxide, .ammonia} by decide]
  simp
  ring

/-- Under the depicted zero-residual stream conditions, the explicit formulas
in the stream definitions satisfy all atom ledgers. -/
theorem quantitative_stage_atom_ledgers
    (b : PlantBasis) (h : OperatesAccordingToFigure b) :
    PrimaryAtomLedger b ∧ SecondaryAtomLedger b ∧ ShiftAtomLedger b ∧
      ScrubberAtomLedger b := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hSecondaryMethane,
      _, _, _, hShiftCarbonMonoxide, hShiftWater, hShiftOxygen, _⟩
  have hSecondaryMethane' :
      b.methaneFeed - b.steamReformingExtent -
          2 * b.partialOxidationExtent = 0 := by
    simpa [afterSecondaryReformer] using hSecondaryMethane
  have hShiftCarbonMonoxide' :
      b.steamReformingExtent + 2 * b.partialOxidationExtent -
          b.waterGasShiftExtent = 0 := by
    simpa [afterWaterGasShift] using hShiftCarbonMonoxide
  have hShiftWater' : b.steamFeed - b.steamReformingExtent = 0 := by
    simpa [afterWaterGasShift] using hShiftWater
  have hShiftOxygen' : 1 - b.partialOxidationExtent = 0 := by
    simpa [afterWaterGasShift] using hShiftOxygen
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro element
    cases element <;>
      simp [atomTotal, sum_plantSpecies, afterPrimaryReformer, primaryFeed,
        atomCount]
    all_goals ring
  · intro element
    cases element <;>
      simp [atomTotal, sum_plantSpecies, afterSecondaryReformer,
        afterPrimaryReformer, airFeed, atomCount] <;> ring
  · intro element
    cases element <;>
      simp [atomTotal, sum_plantSpecies, afterWaterGasShift,
        afterSecondaryReformer, shiftWaterFeed, atomCount] <;> ring
  · intro element
    cases element <;>
      simp [atomTotal, sum_plantSpecies, afterWaterGasShift, synthesisFeed,
        scrubbedCarbonDioxide, atomCount] <;>
      linarith [hSecondaryMethane', hShiftCarbonMonoxide', hShiftWater',
        hShiftOxygen']

/-- All depicted neutral-species stages satisfy the charge ledgers. -/
theorem quantitative_stage_charge_ledgers (b : PlantBasis) :
    QuantitativeChargeLedgers b := by
  simp [QuantitativeChargeLedgers, chargeTotal, formalCharge]

/-- Linear solution of the outcome-relevant figure balances. -/
private lemma solve_figure_basis
    (b : PlantBasis) (h : OperatesAccordingToFigure b) :
    b.methaneFeed = 7 / 2 ∧
    b.steamFeed = 3 / 2 ∧
    b.steamReformingExtent = 3 / 2 ∧
    b.partialOxidationExtent = 1 ∧
    b.waterGasShiftExtent = 7 / 2 ∧
    synthesisFeed b .nitrogen = 4 ∧
    synthesisFeed b .hydrogen = 12 := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, hSteamReforming, hPartialOxidation,
      hMethaneResidual, _, _, hShiftExtent, _, _, _, hSynthesisRatio⟩
  simp [afterSecondaryReformer] at hMethaneResidual hShiftExtent
  simp [synthesisFeed, afterWaterGasShift] at hSynthesisRatio
  have hSteamReformingExtent : b.steamReformingExtent = 3 / 2 := by
    linarith
  have hSteamFeed : b.steamFeed = 3 / 2 := by
    linarith
  have hMethaneFeed : b.methaneFeed = 7 / 2 := by
    linarith
  have hWaterGasShiftExtent : b.waterGasShiftExtent = 7 / 2 := by
    linarith
  refine ⟨hMethaneFeed, hSteamFeed, hSteamReformingExtent,
    hPartialOxidation, hWaterGasShiftExtent, ?_, ?_⟩
  · simp [synthesisFeed, afterWaterGasShift]
  · norm_num [synthesisFeed, afterWaterGasShift, hSteamReformingExtent,
      hPartialOxidation, hWaterGasShiftExtent]

/-- Inline derivation of the previous-part information required here: exact M1
and M2 gas supports and `x > y`.  No result from another generated target is
imported. -/
theorem previous_part_derived_inline
    (b : PlantBasis) (p : SynthesisPass)
    (hb : OperatesAccordingToFigure b) (hp : IncompleteSynthesisPass p) :
    (∀ species, 0 < afterSecondaryReformer b species ↔ species ∈ m1GasSet) ∧
    (∀ species, 0 < mixtureM2 p species ↔ species ∈ m2GasSet) ∧
    b.steamFeed < b.methaneFeed := by
  rcases solve_figure_basis b hb with
    ⟨hMethaneFeed, hSteamFeed, hSteamReformingExtent,
      hPartialOxidationExtent, _, _, _⟩
  rcases hp with ⟨hExtentPositive, hExtentIncomplete⟩
  refine ⟨?_, ?_, ?_⟩
  · intro species
    cases species <;>
      simp [afterSecondaryReformer, m1GasSet, hMethaneFeed, hSteamFeed,
        hSteamReformingExtent, hPartialOxidationExtent] <;>
      norm_num
  · intro species
    cases species <;>
      simp [mixtureM2, m2GasSet] <;>
      linarith
  · linarith

/-- Solving the source balances determines the feed and reaction extents on
the printed air basis. -/
theorem figure_basis_is_determined
    (b : PlantBasis) (h : OperatesAccordingToFigure b) :
    b.methaneFeed = 7 / 2 ∧
    b.steamFeed = 3 / 2 ∧
    b.steamReformingExtent = 3 / 2 ∧
    b.partialOxidationExtent = 1 ∧
    b.waterGasShiftExtent = 7 / 2 ∧
    synthesisFeed b .nitrogen = 4 ∧
    synthesisFeed b .hydrogen = 12 := by
  exact solve_figure_basis b h

/-- Methane moles per mole of theoretical ammonia, derived from the fixed
plant basis (`7/2` methane and `2·4 = 8` ammonia). -/
def methanePerAmmoniaMolarRatio : ℝ :=
  (7 / 2) / (2 * 4)

/-- The ratio carrier is specified against every source-admissible plant basis,
not assumed as an answer-shaped premise. -/
theorem methane_per_ammonia_ratio_spec
    (b : PlantBasis) (h : OperatesAccordingToFigure b) :
    methanePerAmmoniaMolarRatio =
      b.methaneFeed / (2 * synthesisFeed b .nitrogen) := by
  rcases figure_basis_is_determined b h with
    ⟨hMethaneFeed, _, _, _, _, hNitrogenFeed, _⟩
  norm_num [methanePerAmmoniaMolarRatio, hMethaneFeed, hNitrogenFeed]

/-! ## Pinned molar-mass data

Both values below were obtained from the permitted offline registry.  Dataset:
`ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1`,
SHA-256 `11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`.

* CH₄ record SHA-256:
  `15ac9ec311c79f4d4d38a92c35dd7afaacc40f08349f2c5b468767c77340a1a1`.
* NH₃ record SHA-256:
  `6034a27c5509b211ae0fab81674be1d0d63ba9c3bb8cfe336ebe72e0ab33a0b9`.
-/

def chemistryDatasetVersion : String :=
  "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1"

def chemistryDatasetSHA256 : String :=
  "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"

def methaneMolarMassRecordSHA256 : String :=
  "15ac9ec311c79f4d4d38a92c35dd7afaacc40f08349f2c5b468767c77340a1a1"

def ammoniaMolarMassRecordSHA256 : String :=
  "6034a27c5509b211ae0fab81674be1d0d63ba9c3bb8cfe336ebe72e0ab33a0b9"

/-- Pinned conventional molar mass of CH₄, in `g mol⁻¹`. -/
def methaneMolarMass : ℝ := 16043 / 1000

/-- Pinned conventional molar mass of NH₃, in `g mol⁻¹`. -/
def ammoniaMolarMass : ℝ := 17031 / 1000

/-- Requested annual ammonia output, in tons. -/
def annualAmmoniaOutputTons : ℝ := 660000

/-- Problem-stipulated overall yield `97.0%`, exact as printed. -/
def overallYield : ℝ := 970 / 1000

/-- Exact, unrounded annual methane requirement in tons.

The molar-mass quotient is dimensionless, so multiplying the ammonia mass in
tons leaves this expression in tons. -/
def annualMethaneMassRaw : ℝ :=
  annualAmmoniaOutputTons / overallYield *
    methanePerAmmoniaMolarRatio *
    (methaneMolarMass / ammoniaMolarMass)

/-- Source-to-result specification.  It asserts existence of a figure-admissible
basis and ties the candidate expression uniformly to every such basis. -/
def AnnualMethaneMassDerivationSpec : Prop :=
  (∃ b : PlantBasis, OperatesAccordingToFigure b) ∧
  ∀ b : PlantBasis, OperatesAccordingToFigure b →
    annualMethaneMassRaw =
      annualAmmoniaOutputTons / overallYield *
        (b.methaneFeed / (2 * synthesisFeed b .nitrogen)) *
        (methaneMolarMass / ammoniaMolarMass)

/-- Raw result contract: the exact expression reduces to the displayed rational
and lies strictly inside the non-degenerate reporting cell.  The cell endpoints
are mechanically fixed by the three-significant-figure quantum `1000`. -/
theorem annualMethaneMass_raw_result :
    AnnualMethaneMassDerivationSpec ∧
    annualMethaneMassRaw = 22059125000 / 78667 ∧
    (279500 : ℝ) < annualMethaneMassRaw ∧
    annualMethaneMassRaw < (280500 : ℝ) ∧
    (279500 : ℝ) < 280500 := by
  let b₀ : PlantBasis :=
    { methaneFeed := 7 / 2
      steamFeed := 3 / 2
      steamReformingExtent := 3 / 2
      partialOxidationExtent := 1
      waterGasShiftExtent := 7 / 2 }
  have hb₀ : OperatesAccordingToFigure b₀ := by
    refine ⟨by norm_num [b₀], by norm_num [b₀], by norm_num [b₀],
      by norm_num [b₀], by norm_num [b₀], ?_, ?_, ?_, ?_,
      by norm_num [b₀], by norm_num [b₀],
      by norm_num [b₀, afterSecondaryReformer],
      by norm_num [b₀, afterSecondaryReformer],
      by norm_num [b₀, afterSecondaryReformer],
      by norm_num [b₀, afterSecondaryReformer],
      by norm_num [b₀, afterWaterGasShift],
      by norm_num [b₀, afterWaterGasShift],
      by norm_num [b₀, afterWaterGasShift],
      by norm_num [b₀, synthesisFeed, afterWaterGasShift]⟩
    · intro species
      cases species <;> norm_num [b₀, primaryFeed]
    · intro species
      cases species <;> norm_num [b₀, afterPrimaryReformer]
    · intro species
      cases species <;> norm_num [b₀, afterSecondaryReformer]
    · intro species
      cases species <;> norm_num [b₀, afterWaterGasShift]
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩
  · refine ⟨⟨b₀, hb₀⟩, ?_⟩
    intro b hb
    unfold annualMethaneMassRaw
    rw [methane_per_ammonia_ratio_spec b hb]
  all_goals
    norm_num [annualMethaneMassRaw, annualAmmoniaOutputTons, overallYield,
      methanePerAmmoniaMolarRatio, methaneMolarMass, ammoniaMolarMass]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"annual_methane_mass","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"280000","reporting_quantum":"1000","raw_declaration":"IChO2026Problems.T7A2.annualMethaneMassRaw","reporting_declaration":"IChO2026Problems.T7A2.annualMethaneMass_reported"}
theorem annualMethaneMass_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      annualMethaneMassRaw 280000 1000 := by
  rcases annualMethaneMass_raw_result with
    ⟨_, _, hLower, hUpper, _⟩
  have hNonnegative : 0 ≤ annualMethaneMassRaw := by
    linarith
  refine ⟨by norm_num, ⟨280, by norm_num⟩, ?_⟩
  rw [if_pos hNonnegative]
  constructor
  · norm_num
    exact le_of_lt hLower
  · norm_num
    exact hUpper

end

end IChO2026Problems.T7A2
