import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem T7.1: gases in M1 and M2

This file formalizes the material-flow information in Fig. 1.  Amounts are
molar amounts on the batch basis printed in the figure (`4 N₂ + 1 O₂` for the
air feed).  The source assumptions are kept in `PlantModel`; in particular,
the requested compositions of `M1` and `M2`, and the comparison of `x` and
`y`, are not fields of that structure.

The finite gas domain is exactly the set of molecular species named in the
figure.  Each reaction is represented by a `CRNT.Reaction`, while `ReactsBy`
is the quantitative, componentwise extent ledger used at a plant stage.
-/

namespace IChO2026Problems.T7A1

/-- Gas-phase molecular species that occur in Fig. 1. -/
inductive Gas where
  | methane
  | waterVapor
  | carbonMonoxide
  | hydrogen
  | nitrogen
  | oxygen
  | carbonDioxide
  | ammonia
  deriving DecidableEq, Fintype, Repr

/-- A componentwise molar-amount vector over the source-derived gas domain. -/
abbrev Amounts := Gas → ℝ

/-- All component amounts in a physical stream are nonnegative. -/
def Nonnegative (a : Amounts) : Prop :=
  ∀ g, 0 ≤ a g

/-- Pointwise addition of two named material inputs. -/
def addAmounts (a b : Amounts) : Amounts :=
  fun g => a g + b g

/-- The gases whose molar amount is strictly positive in a stream. -/
noncomputable def presentGases (a : Amounts) : Finset Gas :=
  Finset.univ.filter fun g => 0 < a g

/-- A precise carrier for an exhaustive gas label printed beside a stream. -/
def HasExactlyGases (a : Amounts) (listed : Finset Gas) : Prop :=
  ∀ g, 0 < a g ↔ g ∈ listed

/-- The source feed `x CH₄ + y H₂O`. -/
def methaneSteamFeed (x y : ℝ) : Amounts
  | .methane => x
  | .waterVapor => y
  | _ => 0

/-- The source air feed `4 N₂ + 1 O₂`. -/
def airFeed : Amounts
  | .nitrogen => 4
  | .oxygen => 1
  | _ => 0

/-- The separately drawn water input to the shift converter. -/
def shiftWaterFeed (waterAmount : ℝ) : Amounts
  | .waterVapor => waterAmount
  | _ => 0

/-- Steam reforming as printed: `CH₄ + H₂O ⟶ CO + 3 H₂`. -/
def steamReforming : CRNT.Reaction Gas where
  source := fun
    | .methane | .waterVapor => 1
    | _ => 0
  target := fun
    | .carbonMonoxide => 1
    | .hydrogen => 3
    | _ => 0

/-- Secondary reforming as printed: `2 CH₄ + O₂ ⟶ 2 CO + 4 H₂`. -/
def partialOxidation : CRNT.Reaction Gas where
  source := fun
    | .methane => 2
    | .oxygen => 1
    | _ => 0
  target := fun
    | .carbonMonoxide => 2
    | .hydrogen => 4
    | _ => 0

/-- Water-gas shift as printed: `CO + H₂O ⟶ CO₂ + H₂`. -/
def waterGasShift : CRNT.Reaction Gas where
  source := fun
    | .carbonMonoxide | .waterVapor => 1
    | _ => 0
  target := fun
    | .carbonDioxide | .hydrogen => 1
    | _ => 0

/-- Ammonia formation as printed: `N₂ + 3 H₂ ⟶ 2 NH₃`.
The source marks this as the only non-quantitative reaction. -/
def ammoniaFormation : CRNT.Reaction Gas where
  source := fun
    | .nitrogen => 1
    | .hydrogen => 3
    | _ => 0
  target := fun
    | .ammonia => 2
    | _ => 0

/-- Componentwise material ledger for one reaction extent.  This exposes the
stoichiometric equation rather than hiding it behind an opaque process
predicate. -/
def ReactsBy (input output : Amounts) (reaction : CRNT.Reaction Gas)
    (extent : ℝ) : Prop :=
  ∀ g, output g = input g + extent * reaction.vector g

/-- The quantitative CO₂ scrubber removes the CO₂ component and leaves every
other gas amount unchanged. -/
def ScrubsCarbonDioxide (input output : Amounts) : Prop :=
  ∀ g, output g = if g = .carbonDioxide then 0 else input g

/-- Source-side plant contract read from Fig. 1.

The exact-label fields concern streams whose labels are explicitly printed:
the outlet between the first two reformers, the outlet after the shift
converter, and the two cooler outlets.  Neither requested stream (`m1`, `m2`)
has its composition inserted as a premise. -/
structure PlantModel where
  x : ℝ
  y : ℝ
  shiftWaterAmount : ℝ
  steamExtent : ℝ
  oxidationExtent : ℝ
  shiftExtent : ℝ
  ammoniaExtent : ℝ
  steamOutlet : Amounts
  m1 : Amounts
  shiftedOutlet : Amounts
  synthesisFeed : Amounts
  m2 : Amounts
  ammoniaProduct : Amounts
  recycle : Amounts
  x_nonnegative : 0 ≤ x
  y_nonnegative : 0 ≤ y
  shiftWaterAmount_nonnegative : 0 ≤ shiftWaterAmount
  steamExtent_nonnegative : 0 ≤ steamExtent
  oxidationExtent_nonnegative : 0 ≤ oxidationExtent
  shiftExtent_nonnegative : 0 ≤ shiftExtent
  ammoniaExtent_nonnegative : 0 ≤ ammoniaExtent
  steamOutlet_nonnegative : Nonnegative steamOutlet
  m1_nonnegative : Nonnegative m1
  shiftedOutlet_nonnegative : Nonnegative shiftedOutlet
  synthesisFeed_nonnegative : Nonnegative synthesisFeed
  m2_nonnegative : Nonnegative m2
  ammoniaProduct_nonnegative : Nonnegative ammoniaProduct
  recycle_nonnegative : Nonnegative recycle
  steam_ledger :
    ReactsBy (methaneSteamFeed x y) steamOutlet steamReforming steamExtent
  /-- Figure label on the first interstage stream: `CH₄, CO, H₂`. -/
  steam_outlet_label :
    HasExactlyGases steamOutlet
      {.methane, .carbonMonoxide, .hydrogen}
  oxidation_ledger :
    ReactsBy (addAmounts steamOutlet airFeed) m1 partialOxidation oxidationExtent
  shift_ledger :
    ReactsBy (addAmounts m1 (shiftWaterFeed shiftWaterAmount))
      shiftedOutlet waterGasShift shiftExtent
  /-- Figure label on the stream leaving the shift converter: `N₂, CO₂, H₂`. -/
  shifted_outlet_label :
    HasExactlyGases shiftedOutlet
      {.nitrogen, .carbonDioxide, .hydrogen}
  scrubber_ledger : ScrubsCarbonDioxide shiftedOutlet synthesisFeed
  ammonia_ledger :
    ReactsBy synthesisFeed m2 ammoniaFormation ammoniaExtent
  /-- CLR has exactly the two named outlets drawn in the figure. -/
  cooler_split : ∀ g, m2 g = ammoniaProduct g + recycle g
  /-- The side outlet of CLR is labeled `NH₃`. -/
  ammonia_product_label : HasExactlyGases ammoniaProduct {.ammonia}
  /-- The recycle outlet of CLR is labeled `N₂, H₂`. -/
  recycle_label : HasExactlyGases recycle {.nitrogen, .hydrogen}

/-- Outcome-decisive M1 amount ledger obtained from the two reforming balances,
the air feed, and the unchanged CH₄/O₂ components across the shift reaction. -/
theorem m1AmountLedger (p : PlantModel) :
    p.m1 .methane = 0 ∧
    p.m1 .waterVapor = 0 ∧
    p.m1 .carbonMonoxide = p.y + 2 ∧
    p.m1 .hydrogen = 3 * p.y + 4 ∧
    p.m1 .nitrogen = 4 ∧
    p.m1 .oxygen = 0 ∧
    p.m1 .carbonDioxide = 0 ∧
    p.m1 .ammonia = 0 := by
  have hSteamWaterNotPositive : ¬ 0 < p.steamOutlet .waterVapor := by
    rw [p.steam_outlet_label .waterVapor]
    simp
  have hSteamWaterZero : p.steamOutlet .waterVapor = 0 := by
    exact le_antisymm (le_of_not_gt hSteamWaterNotPositive)
      (p.steamOutlet_nonnegative .waterVapor)
  have hShiftedMethaneNotPositive : ¬ 0 < p.shiftedOutlet .methane := by
    rw [p.shifted_outlet_label .methane]
    simp
  have hShiftedMethaneZero : p.shiftedOutlet .methane = 0 := by
    exact le_antisymm (le_of_not_gt hShiftedMethaneNotPositive)
      (p.shiftedOutlet_nonnegative .methane)
  have hShiftedOxygenNotPositive : ¬ 0 < p.shiftedOutlet .oxygen := by
    rw [p.shifted_outlet_label .oxygen]
    simp
  have hShiftedOxygenZero : p.shiftedOutlet .oxygen = 0 := by
    exact le_antisymm (le_of_not_gt hShiftedOxygenNotPositive)
      (p.shiftedOutlet_nonnegative .oxygen)
  have hSteamWater := p.steam_ledger .waterVapor
  have hSteamMethane := p.steam_ledger .methane
  have hSteamCarbonMonoxide := p.steam_ledger .carbonMonoxide
  have hSteamHydrogen := p.steam_ledger .hydrogen
  have hSteamNitrogen := p.steam_ledger .nitrogen
  have hSteamOxygen := p.steam_ledger .oxygen
  have hSteamCarbonDioxide := p.steam_ledger .carbonDioxide
  have hSteamAmmonia := p.steam_ledger .ammonia
  have hOxidationMethane := p.oxidation_ledger .methane
  have hOxidationWater := p.oxidation_ledger .waterVapor
  have hOxidationCarbonMonoxide := p.oxidation_ledger .carbonMonoxide
  have hOxidationHydrogen := p.oxidation_ledger .hydrogen
  have hOxidationNitrogen := p.oxidation_ledger .nitrogen
  have hOxidationOxygen := p.oxidation_ledger .oxygen
  have hOxidationCarbonDioxide := p.oxidation_ledger .carbonDioxide
  have hOxidationAmmonia := p.oxidation_ledger .ammonia
  have hShiftMethane := p.shift_ledger .methane
  have hShiftOxygen := p.shift_ledger .oxygen
  simp [methaneSteamFeed, steamReforming, CRNT.Reaction.vector] at hSteamWater hSteamMethane hSteamCarbonMonoxide hSteamHydrogen hSteamNitrogen hSteamOxygen hSteamCarbonDioxide hSteamAmmonia
  simp [partialOxidation, addAmounts, airFeed, CRNT.Reaction.vector] at hOxidationMethane hOxidationWater hOxidationCarbonMonoxide hOxidationHydrogen hOxidationNitrogen hOxidationOxygen hOxidationCarbonDioxide hOxidationAmmonia
  simp [waterGasShift, addAmounts, shiftWaterFeed, CRNT.Reaction.vector] at hShiftMethane hShiftOxygen
  have hSteamExtent : p.steamExtent = p.y := by
    linarith
  have hM1Oxygen : p.m1 .oxygen = 0 := by
    linarith
  have hOxidationExtent : p.oxidationExtent = 1 := by
    linarith
  have hM1Methane : p.m1 .methane = 0 := by
    linarith
  constructor
  · exact hM1Methane
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · exact hM1Oxygen
  constructor <;> linarith

/-- The same balances determine a positive two-mole methane excess after the
first reformer, hence the exact relation `x - y = 2`. -/
theorem xyDifferenceLedger (p : PlantModel) :
    p.x - p.y = 2 := by
  rcases m1AmountLedger p with
    ⟨hM1Methane, _, _, _, _, hM1Oxygen, _, _⟩
  have hSteamWaterNotPositive : ¬ 0 < p.steamOutlet .waterVapor := by
    rw [p.steam_outlet_label .waterVapor]
    simp
  have hSteamWaterZero : p.steamOutlet .waterVapor = 0 := by
    exact le_antisymm (le_of_not_gt hSteamWaterNotPositive)
      (p.steamOutlet_nonnegative .waterVapor)
  have hSteamWater := p.steam_ledger .waterVapor
  have hSteamMethane := p.steam_ledger .methane
  have hSteamOxygen := p.steam_ledger .oxygen
  have hOxidationMethane := p.oxidation_ledger .methane
  have hOxidationOxygen := p.oxidation_ledger .oxygen
  simp [methaneSteamFeed, steamReforming, CRNT.Reaction.vector] at hSteamWater hSteamMethane hSteamOxygen
  simp [partialOxidation, addAmounts, airFeed, CRNT.Reaction.vector] at hOxidationMethane hOxidationOxygen
  linarith

/-- Outcome-decisive synthesis-feed ledger after quantitative shift and CO₂
scrubbing. -/
theorem synthesisFeedAmountLedger (p : PlantModel) :
    p.synthesisFeed .methane = 0 ∧
    p.synthesisFeed .waterVapor = 0 ∧
    p.synthesisFeed .carbonMonoxide = 0 ∧
    p.synthesisFeed .hydrogen = 4 * p.y + 6 ∧
    p.synthesisFeed .nitrogen = 4 ∧
    p.synthesisFeed .oxygen = 0 ∧
    p.synthesisFeed .carbonDioxide = 0 ∧
    p.synthesisFeed .ammonia = 0 := by
  rcases m1AmountLedger p with
    ⟨hM1Methane, hM1Water, hM1CarbonMonoxide, hM1Hydrogen,
      hM1Nitrogen, hM1Oxygen, hM1CarbonDioxide, hM1Ammonia⟩
  have hShiftedMethaneNotPositive : ¬ 0 < p.shiftedOutlet .methane := by
    rw [p.shifted_outlet_label .methane]
    simp
  have hShiftedMethaneZero : p.shiftedOutlet .methane = 0 := by
    exact le_antisymm (le_of_not_gt hShiftedMethaneNotPositive)
      (p.shiftedOutlet_nonnegative .methane)
  have hShiftedWaterNotPositive : ¬ 0 < p.shiftedOutlet .waterVapor := by
    rw [p.shifted_outlet_label .waterVapor]
    simp
  have hShiftedWaterZero : p.shiftedOutlet .waterVapor = 0 := by
    exact le_antisymm (le_of_not_gt hShiftedWaterNotPositive)
      (p.shiftedOutlet_nonnegative .waterVapor)
  have hShiftedCarbonMonoxideNotPositive :
      ¬ 0 < p.shiftedOutlet .carbonMonoxide := by
    rw [p.shifted_outlet_label .carbonMonoxide]
    simp
  have hShiftedCarbonMonoxideZero :
      p.shiftedOutlet .carbonMonoxide = 0 := by
    exact le_antisymm (le_of_not_gt hShiftedCarbonMonoxideNotPositive)
      (p.shiftedOutlet_nonnegative .carbonMonoxide)
  have hShiftedOxygenNotPositive : ¬ 0 < p.shiftedOutlet .oxygen := by
    rw [p.shifted_outlet_label .oxygen]
    simp
  have hShiftedOxygenZero : p.shiftedOutlet .oxygen = 0 := by
    exact le_antisymm (le_of_not_gt hShiftedOxygenNotPositive)
      (p.shiftedOutlet_nonnegative .oxygen)
  have hShiftedAmmoniaNotPositive : ¬ 0 < p.shiftedOutlet .ammonia := by
    rw [p.shifted_outlet_label .ammonia]
    simp
  have hShiftedAmmoniaZero : p.shiftedOutlet .ammonia = 0 := by
    exact le_antisymm (le_of_not_gt hShiftedAmmoniaNotPositive)
      (p.shiftedOutlet_nonnegative .ammonia)
  have hShiftMethane := p.shift_ledger .methane
  have hShiftWater := p.shift_ledger .waterVapor
  have hShiftCarbonMonoxide := p.shift_ledger .carbonMonoxide
  have hShiftHydrogen := p.shift_ledger .hydrogen
  have hShiftNitrogen := p.shift_ledger .nitrogen
  have hShiftOxygen := p.shift_ledger .oxygen
  have hShiftAmmonia := p.shift_ledger .ammonia
  simp [waterGasShift, addAmounts, shiftWaterFeed, CRNT.Reaction.vector] at hShiftMethane hShiftWater hShiftCarbonMonoxide hShiftHydrogen hShiftNitrogen hShiftOxygen hShiftAmmonia
  have hShiftExtent : p.shiftExtent = p.y + 2 := by
    linarith
  have hScrubMethane := p.scrubber_ledger .methane
  have hScrubWater := p.scrubber_ledger .waterVapor
  have hScrubCarbonMonoxide := p.scrubber_ledger .carbonMonoxide
  have hScrubHydrogen := p.scrubber_ledger .hydrogen
  have hScrubNitrogen := p.scrubber_ledger .nitrogen
  have hScrubOxygen := p.scrubber_ledger .oxygen
  have hScrubCarbonDioxide := p.scrubber_ledger .carbonDioxide
  have hScrubAmmonia := p.scrubber_ledger .ammonia
  simp at hScrubMethane hScrubWater hScrubCarbonMonoxide hScrubHydrogen hScrubNitrogen hScrubOxygen hScrubCarbonDioxide hScrubAmmonia
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Outcome-decisive M2 amount ledger for the non-quantitative ammonia
formation stage.  Positivity of the three surviving entries follows from the
two explicitly labeled cooler outlets. -/
theorem m2AmountLedger (p : PlantModel) :
    p.m2 .methane = 0 ∧
    p.m2 .waterVapor = 0 ∧
    p.m2 .carbonMonoxide = 0 ∧
    p.m2 .hydrogen = 4 * p.y + 6 - 3 * p.ammoniaExtent ∧
    p.m2 .nitrogen = 4 - p.ammoniaExtent ∧
    p.m2 .oxygen = 0 ∧
    p.m2 .carbonDioxide = 0 ∧
    p.m2 .ammonia = 2 * p.ammoniaExtent := by
  rcases synthesisFeedAmountLedger p with
    ⟨hFeedMethane, hFeedWater, hFeedCarbonMonoxide, hFeedHydrogen,
      hFeedNitrogen, hFeedOxygen, hFeedCarbonDioxide, hFeedAmmonia⟩
  have hAmmoniaMethane := p.ammonia_ledger .methane
  have hAmmoniaWater := p.ammonia_ledger .waterVapor
  have hAmmoniaCarbonMonoxide := p.ammonia_ledger .carbonMonoxide
  have hAmmoniaHydrogen := p.ammonia_ledger .hydrogen
  have hAmmoniaNitrogen := p.ammonia_ledger .nitrogen
  have hAmmoniaOxygen := p.ammonia_ledger .oxygen
  have hAmmoniaCarbonDioxide := p.ammonia_ledger .carbonDioxide
  have hAmmoniaProduct := p.ammonia_ledger .ammonia
  simp [ammoniaFormation, CRNT.Reaction.vector] at hAmmoniaMethane hAmmoniaWater hAmmoniaCarbonMonoxide hAmmoniaHydrogen hAmmoniaNitrogen hAmmoniaOxygen hAmmoniaCarbonDioxide hAmmoniaProduct
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Exact symbolic candidate for the gases in M1. -/
def expectedM1Gases : Finset Gas :=
  {.nitrogen, .carbonMonoxide, .hydrogen}

/-- Exact symbolic candidate for the gases in M2. -/
def expectedM2Gases : Finset Gas :=
  {.nitrogen, .hydrogen, .ammonia}

/-- The finite classification requested for the relation between `x` and `y`. -/
inductive XYRelation where
  | xLessThanY
  | xEqualsY
  | xGreaterThanY
  deriving DecidableEq, Repr

/-- Mathematical meaning of each comparison option. -/
def XYRelation.Holds (r : XYRelation) (x y : ℝ) : Prop :=
  match r with
  | .xLessThanY => x < y
  | .xEqualsY => x = y
  | .xGreaterThanY => x > y

/-- Requested-output carrier `gases_m1`. -/
def GasesM1Result (p : PlantModel) : Prop :=
  presentGases p.m1 = expectedM1Gases

/-- Requested-output carrier `gases_m2`. -/
def GasesM2Result (p : PlantModel) : Prop :=
  presentGases p.m2 = expectedM2Gases

/-- Requested-output carrier `xy_relation`. -/
def XYRelationResult (p : PlantModel) : Prop :=
  XYRelation.Holds .xGreaterThanY p.x p.y

theorem gases_m1 (p : PlantModel) : GasesM1Result p := by
  unfold GasesM1Result
  rcases m1AmountLedger p with
    ⟨hMethane, hWater, hCarbonMonoxide, hHydrogen,
      hNitrogen, hOxygen, hCarbonDioxide, hAmmonia⟩
  have hCarbonMonoxidePositive : 0 < p.m1 .carbonMonoxide := by
    rw [hCarbonMonoxide]
    linarith [p.y_nonnegative]
  have hHydrogenPositive : 0 < p.m1 .hydrogen := by
    rw [hHydrogen]
    linarith [p.y_nonnegative]
  have hNitrogenPositive : 0 < p.m1 .nitrogen := by
    rw [hNitrogen]
    norm_num
  apply Finset.ext
  intro g
  cases g <;>
    simp [presentGases, expectedM1Gases, hMethane, hWater,
      hCarbonMonoxidePositive, hHydrogenPositive, hNitrogenPositive,
      hOxygen, hCarbonDioxide, hAmmonia]

theorem gases_m2 (p : PlantModel) : GasesM2Result p := by
  unfold GasesM2Result
  rcases m2AmountLedger p with
    ⟨hMethane, hWater, hCarbonMonoxide, _, _, hOxygen,
      hCarbonDioxide, _⟩
  have hProductAmmoniaPositive : 0 < p.ammoniaProduct .ammonia :=
    (p.ammonia_product_label .ammonia).2 (by simp)
  have hRecycleNitrogenPositive : 0 < p.recycle .nitrogen :=
    (p.recycle_label .nitrogen).2 (by simp)
  have hRecycleHydrogenPositive : 0 < p.recycle .hydrogen :=
    (p.recycle_label .hydrogen).2 (by simp)
  have hM2NitrogenPositive : 0 < p.m2 .nitrogen := by
    have hSplit := p.cooler_split .nitrogen
    have hProductNonnegative := p.ammoniaProduct_nonnegative .nitrogen
    linarith
  have hM2HydrogenPositive : 0 < p.m2 .hydrogen := by
    have hSplit := p.cooler_split .hydrogen
    have hProductNonnegative := p.ammoniaProduct_nonnegative .hydrogen
    linarith
  have hM2AmmoniaPositive : 0 < p.m2 .ammonia := by
    have hSplit := p.cooler_split .ammonia
    have hRecycleNonnegative := p.recycle_nonnegative .ammonia
    linarith
  apply Finset.ext
  intro g
  cases g <;>
    simp [presentGases, expectedM2Gases, hMethane, hWater,
      hCarbonMonoxide, hM2HydrogenPositive, hM2NitrogenPositive,
      hOxygen, hCarbonDioxide, hM2AmmoniaPositive]

theorem xy_relation (p : PlantModel) : XYRelationResult p := by
  unfold XYRelationResult XYRelation.Holds
  linarith [xyDifferenceLedger p]

/-- Unrounded/source-derived result contract.  This is symbolic, so it contains
all three requested outputs rather than forcing them into a scalar schema. -/
def RawResult (p : PlantModel) : Prop :=
  GasesM1Result p ∧ GasesM2Result p ∧ XYRelationResult p

/-- Exact-symbolic reporting contract.  No rounding or tolerance is applicable
to any of the three outputs. -/
def ReportedResult (p : PlantModel) : Prop :=
  GasesM1Result p ∧ GasesM2Result p ∧ XYRelationResult p

theorem raw_result (p : PlantModel) : RawResult p := by
  exact ⟨gases_m1 p, gases_m2 p, xy_relation p⟩

theorem reported_result (p : PlantModel) : ReportedResult p := by
  exact ⟨gases_m1 p, gases_m2 p, xy_relation p⟩

end IChO2026Problems.T7A1
