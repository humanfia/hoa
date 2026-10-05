import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem.Reporting

/-!
# IChO 2026 T7-A3: an open cyclic ammonia-synthesis loop

The source describes a fresh stoichiometric `N₂ : H₂ = 1 : 3` feed added
before every reactor pass, a constant net forward yield of `0.150`, complete
liquefaction/separation of the ammonia formed in that pass, and recycle of the
unreacted nitrogen and hydrogen.  Consequently the amount at the boundary
after cycle `n` is not the decay of one closed batch: it is the sum of all `n`
fresh portions after their different numbers of passes.

This is a `quantitative_material_stage`.  The finite material domain contains
exactly the three species printed in Fig. 2, and every external input and
separated stream used below is named.  The overall-yield numerator is the
cumulative separated ammonia; its denominator is the theoretical ammonia from
all fresh nitrogen admitted through the same cycle boundary.
-/

noncomputable section

namespace IChO2026Problems.IChO2026T7A3

/-! ## Source domain and provenance -/

/-- The complete source-bounded species domain of the cyclic loop in Fig. 2. -/
inductive Species where
  | nitrogen
  | hydrogen
  | ammonia
  deriving DecidableEq, Fintype, Repr

/-- Elements needed for the outcome-decisive atom ledgers. -/
inductive Element where
  | nitrogen
  | hydrogen
  deriving DecidableEq, Fintype, Repr

/-- Source phases used by the cooler/separator ledger. -/
inductive Phase where
  | gas
  | liquefied
  deriving DecidableEq, Repr

/-- Sources allowed by the problem's candidate-domain policy. -/
inductive Provenance where
  | problemText
  | problemImage
  | problemStatedFallback
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- Exact locations in the two inspected source pages. -/
inductive SourceLocator where
  | page1AmmoniaReaction
  | page1Mixture2Tag
  | page1CoolerTag
  | page1AmmoniaProduct
  | page1RecycleLabel
  | page2FreshFeedStep
  | page2YieldStep
  | page2LiquefactionStep
  | page2RecycleStep
  | page2Mixture2Arrow
  | page2AmmoniaProduct
  | page2RecycleLabel
  | questionPartA
  | questionPartB
  deriving DecidableEq, Repr

/-- This target consumes exact cross-stage material balances and yields. -/
inductive StagedTransformationClass where
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

def stagedTransformationClass : StagedTransformationClass :=
  .quantitativeMaterialStage

/-- Molecular atom counts read directly from `N₂`, `H₂`, and `NH₃`. -/
def atomCount : Species → Element → ℕ
  | .nitrogen, .nitrogen => 2
  | .hydrogen, .hydrogen => 2
  | .ammonia, .nitrogen => 1
  | .ammonia, .hydrogen => 3
  | _, _ => 0

/-- Every molecular species in the displayed loop is neutral. -/
def formalCharge (_ : Species) : ℤ := 0

/-- The net forward stoichiometry `N₂ + 3 H₂ → 2 NH₃` used by a pass.
The equilibrium arrow in the figure is respected by treating the printed
single-pass yield as the net forward extent, rather than claiming irreversibility. -/
def ammoniaFormation : CRNT.Reaction Species where
  source
    | .nitrogen => 1
    | .hydrogen => 3
    | .ammonia => 0
  target
    | .ammonia => 2
    | _ => 0

/-- Atom conservation for a stoichiometric complex. -/
def AtomBalanced (reaction : CRNT.Reaction Species) : Prop :=
  ∀ element : Element,
    (∑ species : Species,
        reaction.source species * atomCount species element) =
      ∑ species : Species,
        reaction.target species * atomCount species element

/-- Charge conservation for a stoichiometric complex. -/
def ChargeBalanced (reaction : CRNT.Reaction Species) : Prop :=
  (∑ species : Species,
      (reaction.source species : ℤ) * formalCharge species) =
    ∑ species : Species,
      (reaction.target species : ℤ) * formalCharge species

theorem ammoniaFormation_atomBalanced :
    AtomBalanced ammoniaFormation := by
  intro element
  cases element <;> decide

theorem ammoniaFormation_chargeBalanced :
    ChargeBalanced ammoniaFormation := by
  simp [ChargeBalanced, formalCharge]

/-! ## Inline reconstruction of the needed T7-A1 fact -/

/-- A complete comma-separated species label transcribed from a source image. -/
structure SourcedSpeciesListing where
  species : Finset Species
  provenance : Provenance
  locator : SourceLocator

/-- M2 contains the three formulae shown across the reactor/cooler stage. -/
def mixture2Listing : SourcedSpeciesListing where
  species := {.nitrogen, .hydrogen, .ammonia}
  provenance := .problemImage
  locator := .page2Mixture2Arrow

/-- The return line is explicitly labelled `N₂, H₂`. -/
def recycleListing : SourcedSpeciesListing where
  species := {.nitrogen, .hydrogen}
  provenance := .problemImage
  locator := .page2RecycleLabel

/-- The cooler's separated outlet is explicitly labelled `NH₃`. -/
def ammoniaProductListing : SourcedSpeciesListing where
  species := {.ammonia}
  provenance := .problemImage
  locator := .page2AmmoniaProduct

/-- Only the M2/recycle conclusion of T7-A1 is needed here.  It is rederived
inline from both bound figures rather than imported as an uncertified result. -/
def InlineA1RecycleConclusion : Prop :=
  mixture2Listing.species = {.nitrogen, .hydrogen, .ammonia} ∧
    recycleListing.species = {.nitrogen, .hydrogen} ∧
    ammoniaProductListing.species = {.ammonia} ∧
    mixture2Listing.provenance = .problemImage ∧
    recycleListing.provenance = .problemImage ∧
    ammoniaProductListing.provenance = .problemImage

theorem inlineA1RecycleConclusion : InlineA1RecycleConclusion := by
  simp [InlineA1RecycleConclusion, mixture2Listing, recycleListing,
    ammoniaProductListing]

/-! ## Source quantities and exact stream ledgers -/

/-- Units that occur in the present subquestion. -/
inductive QuantityUnit where
  | mole
  | dimensionless
  deriving DecidableEq, Repr

/-- A scalar together with its problem-side provenance. -/
structure SourcedQuantity where
  value : ℝ
  unit : QuantityUnit
  provenance : Provenance
  locator : SourceLocator

/-- The stipulated total amount `n₀ = 4 mol` in every fresh portion. -/
def freshFeedTotal : SourcedQuantity where
  value := 4
  unit := .mole
  provenance := .problemText
  locator := .questionPartA

/-- The stipulated constant single-pass yield `η = 0.150`. -/
def singlePassYield : SourcedQuantity where
  value := (150 : ℝ) / 1000
  unit := .dimensionless
  provenance := .problemText
  locator := .page2YieldStep

/-- The explicitly named starting overall yield `15.0%`. -/
def startingOverallYield : SourcedQuantity where
  value := (15 : ℝ) / 100
  unit := .dimensionless
  provenance := .problemText
  locator := .questionPartB

/-- The requested target overall yield `97.0%`. -/
def targetOverallYield : SourcedQuantity where
  value := (97 : ℝ) / 100
  unit := .dimensionless
  provenance := .problemText
  locator := .questionPartB

/-- The unreacted fraction returned after every pass. -/
def retentionFactor : ℝ :=
  1 - singlePassYield.value

/-- A phase-indexed molar stream on the complete finite species domain. -/
structure Stream (phase : Phase) where
  amount : Species → ℝ

abbrev GasStream := Stream .gas
abbrev LiquefiedStream := Stream .liquefied

/-- Physical stream amounts are nonnegative. -/
def NonnegativeStream {phase : Phase} (stream : Stream phase) : Prop :=
  ∀ species : Species, 0 ≤ stream.amount species

/-- Species occur in a stream exactly when their molar amounts are positive. -/
def speciesPresent {phase : Phase} (stream : Stream phase) : Finset Species :=
  Finset.univ.filter fun species => 0 < stream.amount species

/-- A stream realizes every and only the species in a complete source label. -/
def RealizesListing {phase : Phase} (stream : Stream phase)
    (listing : SourcedSpeciesListing) : Prop :=
  NonnegativeStream stream ∧ speciesPresent stream = listing.species

private theorem realizesListing_amount_eq_zero_of_not_mem
    {phase : Phase} {stream : Stream phase}
    {listing : SourcedSpeciesListing} {species : Species}
    (hlisting : RealizesListing stream listing)
    (hnot : species ∉ listing.species) :
    stream.amount species = 0 := by
  have hnotpos : ¬ 0 < stream.amount species := by
    intro hpos
    have hmem : species ∈ speciesPresent stream := by
      simp [speciesPresent, hpos]
    rw [hlisting.2] at hmem
    exact hnot hmem
  exact le_antisymm (le_of_not_gt hnotpos) (hlisting.1 species)

/-- Pointwise stream addition, used for both mixers and cumulative product. -/
def addStreams {phase : Phase} (first second : Stream phase) : Stream phase where
  amount := fun species => first.amount species + second.amount species

/-- The empty stream. -/
def emptyStream (phase : Phase) : Stream phase where
  amount := fun _ => 0

private theorem stream_eq {phase : Phase} {first second : Stream phase}
    (h : ∀ species, first.amount species = second.amount species) :
    first = second := by
  cases first with
  | mk firstAmount =>
      cases second with
      | mk secondAmount =>
          congr
          funext species
          exact h species

/-- One fresh stoichiometric portion.  Its nitrogen amount is `n₀/4` and
its hydrogen amount is `3 n₀/4`, so the three-to-one ratio and total `n₀`
are represented simultaneously. -/
def freshFeed : GasStream where
  amount
    | .nitrogen => freshFeedTotal.value / 4
    | .hydrogen => 3 * freshFeedTotal.value / 4
    | .ammonia => 0

/-- Nitrogen supplied in one fresh portion, in mol. -/
def freshNitrogenAmount : ℝ :=
  freshFeed.amount .nitrogen

/-- Named carrier for the complete fresh-feed composition: the two positive
reactant amounts sum to `n₀`, have ratio 1:3, and contain no ammonia. -/
def FreshFeedStoichiometricSpec : Prop :=
  0 < freshFeed.amount .nitrogen ∧
    0 < freshFeed.amount .hydrogen ∧
    freshFeed.amount .hydrogen = 3 * freshFeed.amount .nitrogen ∧
    freshFeed.amount .nitrogen + freshFeed.amount .hydrogen =
      freshFeedTotal.value ∧
    freshFeed.amount .ammonia = 0

theorem freshFeed_stoichiometric : FreshFeedStoichiometricSpec := by
  norm_num [FreshFeedStoichiometricSpec, freshFeed, freshFeedTotal]

/-- Exact consistency of the two printed yield notations and the retained
fraction used in every recurrence step. -/
def SourceYieldSpec : Prop :=
  singlePassYield.value = (3 : ℝ) / 20 ∧
    startingOverallYield.value = singlePassYield.value ∧
    retentionFactor = (17 : ℝ) / 20 ∧
    0 < singlePassYield.value ∧ singlePassYield.value < 1

theorem sourceYieldSpec_holds : SourceYieldSpec := by
  norm_num [SourceYieldSpec, singlePassYield, startingOverallYield,
    retentionFactor]

/-- All source-level facts used by the quantitative cycle ledger. -/
def CoreProcessSourceSpec : Prop :=
  InlineA1RecycleConclusion ∧
    FreshFeedStoichiometricSpec ∧
    SourceYieldSpec ∧
    AtomBalanced ammoniaFormation ∧
    ChargeBalanced ammoniaFormation

theorem coreProcessSourceSpec_holds : CoreProcessSourceSpec := by
  exact ⟨inlineA1RecycleConclusion, freshFeed_stoichiometric,
    sourceYieldSpec_holds, ammoniaFormation_atomBalanced,
    ammoniaFormation_chargeBalanced⟩

/-- Exact component balance at the reactor-input mixer. -/
def MixingStage (recycle fresh combined : GasStream) : Prop :=
  NonnegativeStream recycle ∧
    NonnegativeStream fresh ∧
    NonnegativeStream combined ∧
    combined = addStreams recycle fresh

/-- Exact net-forward reaction step at a nonnegative extent. -/
def ReactionStage (input output : GasStream) (extent : ℝ) : Prop :=
  0 ≤ extent ∧
    NonnegativeStream input ∧
    NonnegativeStream output ∧
    ∀ species : Species,
      output.amount species =
        input.amount species + extent * ammoniaFormation.vector species

/-- Exact cooler split across gas and liquefied phases. -/
def CoolerSplit (input recycle : GasStream)
    (newProduct : LiquefiedStream) : Prop :=
  NonnegativeStream input ∧
    NonnegativeStream recycle ∧
    NonnegativeStream newProduct ∧
    ∀ species : Species,
      input.amount species =
        recycle.amount species + newProduct.amount species

/-- Exact accumulation of the newly liquefied ammonia product. -/
def ProductAccumulation (previous increment next : LiquefiedStream) : Prop :=
  NonnegativeStream previous ∧
    NonnegativeStream increment ∧
    NonnegativeStream next ∧
    next = addStreams previous increment

/-- State at the boundary after a completed pass and before the next fresh
portion is added. -/
structure CycleState where
  recycle : GasStream
  cumulativeProduct : LiquefiedStream

private theorem cycleState_eq {first second : CycleState}
    (hrecycle : first.recycle = second.recycle)
    (hproduct : first.cumulativeProduct = second.cumulativeProduct) :
    first = second := by
  cases first
  cases second
  simp_all

/-- One complete source cycle: fresh-feed mixing, net reaction at yield `η`,
complete ammonia separation, and return of exactly N₂/H₂. -/
def CycleStep (previous next : CycleState) : Prop :=
  ∃ reactorInput reactorOutput : GasStream,
    ∃ newProduct : LiquefiedStream,
      ∃ extent : ℝ,
        MixingStage previous.recycle freshFeed reactorInput ∧
        extent = singlePassYield.value * reactorInput.amount .nitrogen ∧
        ReactionStage reactorInput reactorOutput extent ∧
        CoolerSplit reactorOutput next.recycle newProduct ∧
        RealizesListing reactorOutput mixture2Listing ∧
        RealizesListing next.recycle recycleListing ∧
        RealizesListing newProduct ammoniaProductListing ∧
        ProductAccumulation
          previous.cumulativeProduct newProduct next.cumulativeProduct

/-- A complete run begins empty and performs the source cycle for every
natural-numbered pass. -/
structure ProcessRun where
  state : ℕ → CycleState
  initiallyEmpty :
    state 0 =
      { recycle := emptyStream .gas
        cumulativeProduct := emptyStream .liquefied }
  step : ∀ cycle : ℕ, CycleStep (state cycle) (state (cycle + 1))

/-- The exact nitrogen amount at the named cycle boundary. -/
def boundaryNitrogen (run : ProcessRun) (cycles : ℕ) : ℝ :=
  (run.state cycles).recycle.amount .nitrogen

/-- The exact recurrence forced by the cycle's nitrogen component ledger. -/
def NitrogenBoundaryRecurrence (amount : ℕ → ℝ) : Prop :=
  amount 0 = 0 ∧
    ∀ cycle : ℕ,
      amount (cycle + 1) =
        retentionFactor * (amount cycle + freshNitrogenAmount)

/-! The following canonical ledger is used only to witness that the exact
source cycle model is nonempty.  It is defined recursively, so no desired
cycle-58 value is built into the witness. -/

private def canonicalNitrogen : ℕ → ℝ
  | 0 => 0
  | cycle + 1 =>
      retentionFactor * (canonicalNitrogen cycle + freshNitrogenAmount)

private def canonicalAmmonia : ℕ → ℝ
  | 0 => 0
  | cycle + 1 =>
      canonicalAmmonia cycle +
        2 * singlePassYield.value *
          (canonicalNitrogen cycle + freshNitrogenAmount)

private def canonicalState (cycles : ℕ) : CycleState where
  recycle.amount
    | .nitrogen => canonicalNitrogen cycles
    | .hydrogen => 3 * canonicalNitrogen cycles
    | .ammonia => 0
  cumulativeProduct.amount
    | .ammonia => canonicalAmmonia cycles
    | _ => 0

private def canonicalReactorInput (cycle : ℕ) : GasStream :=
  addStreams (canonicalState cycle).recycle freshFeed

private def canonicalExtent (cycle : ℕ) : ℝ :=
  singlePassYield.value *
    (canonicalReactorInput cycle).amount .nitrogen

private def canonicalReactorOutput (cycle : ℕ) : GasStream where
  amount := fun species =>
    (canonicalReactorInput cycle).amount species +
      canonicalExtent cycle * ammoniaFormation.vector species

private def canonicalNewProduct (cycle : ℕ) : LiquefiedStream where
  amount
    | .ammonia => (canonicalReactorOutput cycle).amount .ammonia
    | _ => 0

private theorem canonicalNitrogen_nonnegative (cycles : ℕ) :
    0 ≤ canonicalNitrogen cycles := by
  induction cycles with
  | zero => simp [canonicalNitrogen]
  | succ cycles ih =>
      simp only [canonicalNitrogen]
      have hret : (0 : ℝ) ≤ retentionFactor := by
        norm_num [retentionFactor, singlePassYield]
      have hfresh : (0 : ℝ) ≤ freshNitrogenAmount := by
        norm_num [freshNitrogenAmount, freshFeed, freshFeedTotal]
      positivity

private theorem canonicalNitrogen_positive_succ (cycles : ℕ) :
    0 < canonicalNitrogen (cycles + 1) := by
  simp only [canonicalNitrogen]
  have hret : (0 : ℝ) < retentionFactor := by
    norm_num [retentionFactor, singlePassYield]
  have hfresh : (0 : ℝ) < freshNitrogenAmount := by
    norm_num [freshNitrogenAmount, freshFeed, freshFeedTotal]
  have hn := canonicalNitrogen_nonnegative cycles
  positivity

private theorem canonicalAmmonia_nonnegative (cycles : ℕ) :
    0 ≤ canonicalAmmonia cycles := by
  induction cycles with
  | zero => simp [canonicalAmmonia]
  | succ cycles ih =>
      simp only [canonicalAmmonia]
      have hyield : (0 : ℝ) ≤ singlePassYield.value := by
        norm_num [singlePassYield]
      have hfresh : (0 : ℝ) ≤ freshNitrogenAmount := by
        norm_num [freshNitrogenAmount, freshFeed, freshFeedTotal]
      have hn := canonicalNitrogen_nonnegative cycles
      positivity

private theorem canonicalState_recycle_nonnegative (cycles : ℕ) :
    NonnegativeStream (canonicalState cycles).recycle := by
  intro species
  cases species <;>
    simp [canonicalState, canonicalNitrogen_nonnegative]

private theorem canonicalState_product_nonnegative (cycles : ℕ) :
    NonnegativeStream (canonicalState cycles).cumulativeProduct := by
  intro species
  cases species <;>
    simp [canonicalState, canonicalAmmonia_nonnegative]

private theorem freshFeed_nonnegative : NonnegativeStream freshFeed := by
  intro species
  cases species <;> norm_num [freshFeed, freshFeedTotal]

private theorem canonicalReactorInput_nonnegative (cycle : ℕ) :
    NonnegativeStream (canonicalReactorInput cycle) := by
  intro species
  exact add_nonneg (canonicalState_recycle_nonnegative cycle species)
    (freshFeed_nonnegative species)

private theorem canonicalExtent_positive (cycle : ℕ) :
    0 < canonicalExtent cycle := by
  have hn := canonicalNitrogen_nonnegative cycle
  norm_num [canonicalExtent, canonicalReactorInput, addStreams,
    canonicalState, freshFeed, freshFeedTotal, singlePassYield]
  positivity

private theorem canonicalReactorOutput_nonnegative (cycle : ℕ) :
    NonnegativeStream (canonicalReactorOutput cycle) := by
  have hn := canonicalNitrogen_nonnegative cycle
  intro species
  cases species
  · norm_num [canonicalReactorOutput, canonicalReactorInput, canonicalExtent,
      addStreams, canonicalState, freshFeed, freshFeedTotal, singlePassYield,
      ammoniaFormation, CRNT.Reaction.vector]
    nlinarith
  · norm_num [canonicalReactorOutput, canonicalReactorInput, canonicalExtent,
      addStreams, canonicalState, freshFeed, freshFeedTotal, singlePassYield,
      ammoniaFormation, CRNT.Reaction.vector]
    nlinarith
  · norm_num [canonicalReactorOutput, canonicalReactorInput, canonicalExtent,
      addStreams, canonicalState, freshFeed, freshFeedTotal, singlePassYield,
      ammoniaFormation, CRNT.Reaction.vector]
    nlinarith

private theorem canonicalReactorOutput_positive (cycle : ℕ)
    (species : Species) :
    0 < (canonicalReactorOutput cycle).amount species := by
  have hn := canonicalNitrogen_nonnegative cycle
  cases species
  · norm_num [canonicalReactorOutput, canonicalReactorInput, canonicalExtent,
      addStreams, canonicalState, freshFeed, freshFeedTotal, singlePassYield,
      ammoniaFormation, CRNT.Reaction.vector]
    nlinarith
  · norm_num [canonicalReactorOutput, canonicalReactorInput, canonicalExtent,
      addStreams, canonicalState, freshFeed, freshFeedTotal, singlePassYield,
      ammoniaFormation, CRNT.Reaction.vector]
    nlinarith
  · norm_num [canonicalReactorOutput, canonicalReactorInput, canonicalExtent,
      addStreams, canonicalState, freshFeed, freshFeedTotal, singlePassYield,
      ammoniaFormation, CRNT.Reaction.vector]
    nlinarith

private theorem canonicalNewProduct_nonnegative (cycle : ℕ) :
    NonnegativeStream (canonicalNewProduct cycle) := by
  intro species
  cases species
  · simp [canonicalNewProduct]
  · simp [canonicalNewProduct]
  · simpa [canonicalNewProduct] using
      canonicalReactorOutput_nonnegative cycle Species.ammonia

/-- The source cycle model is nonvacuous. -/
theorem processRun_nonempty : Nonempty ProcessRun := by
  refine ⟨{
    state := canonicalState
    initiallyEmpty := ?_
    step := ?_ }⟩
  · apply cycleState_eq
    · apply stream_eq
      intro species
      cases species <;>
        simp [canonicalState, canonicalNitrogen, emptyStream]
    · apply stream_eq
      intro species
      cases species <;>
        simp [canonicalState, canonicalAmmonia, emptyStream]
  · intro cycle
    refine ⟨canonicalReactorInput cycle, canonicalReactorOutput cycle,
      canonicalNewProduct cycle, canonicalExtent cycle, ?_, rfl, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · exact ⟨canonicalState_recycle_nonnegative cycle,
        freshFeed_nonnegative, canonicalReactorInput_nonnegative cycle, rfl⟩
    · exact ⟨(canonicalExtent_positive cycle).le,
        canonicalReactorInput_nonnegative cycle,
        canonicalReactorOutput_nonnegative cycle, fun _ => rfl⟩
    · refine ⟨canonicalReactorOutput_nonnegative cycle,
        canonicalState_recycle_nonnegative (cycle + 1),
        canonicalNewProduct_nonnegative cycle, ?_⟩
      intro species
      cases species <;>
        norm_num [canonicalReactorOutput, canonicalReactorInput,
          canonicalExtent, canonicalNewProduct, canonicalState,
          canonicalNitrogen, addStreams, freshFeed, freshFeedTotal,
          freshNitrogenAmount, singlePassYield, retentionFactor, ammoniaFormation,
          CRNT.Reaction.vector] <;>
        ring
    · refine ⟨canonicalReactorOutput_nonnegative cycle, ?_⟩
      ext species
      simp only [speciesPresent, mixture2Listing, Finset.mem_filter,
        Finset.mem_univ, true_and]
      cases species <;> simp [canonicalReactorOutput_positive]
    · refine ⟨canonicalState_recycle_nonnegative (cycle + 1), ?_⟩
      ext species
      cases species <;>
        simp [speciesPresent, recycleListing, canonicalState,
          canonicalNitrogen_positive_succ]
    · refine ⟨canonicalNewProduct_nonnegative cycle, ?_⟩
      ext species
      simp only [speciesPresent, ammoniaProductListing, Finset.mem_filter,
        Finset.mem_univ, true_and]
      cases species <;>
        simp [canonicalNewProduct, canonicalReactorOutput_positive]
    · refine ⟨canonicalState_product_nonnegative cycle,
        canonicalNewProduct_nonnegative cycle,
        canonicalState_product_nonnegative (cycle + 1), ?_⟩
      apply stream_eq
      intro species
      cases species <;>
        norm_num [canonicalState, canonicalAmmonia, canonicalNewProduct,
          canonicalReactorOutput, canonicalReactorInput, canonicalExtent,
          addStreams, freshFeed, freshFeedTotal, freshNitrogenAmount,
          singlePassYield,
          ammoniaFormation, CRNT.Reaction.vector];
        ring

/-- Every complete material run induces the same nitrogen recurrence. -/
theorem processRun_nitrogenRecurrence (run : ProcessRun) :
    NitrogenBoundaryRecurrence (boundaryNitrogen run) := by
  constructor
  · simp [boundaryNitrogen, run.initiallyEmpty, emptyStream]
  · intro cycle
    rcases run.step cycle with
      ⟨reactorInput, reactorOutput, newProduct, extent,
        hmix, hextent, hreaction, hcooler, _houtputListing,
        _hrecycleListing, hproductListing, _haccumulation⟩
    have hnewProductN : newProduct.amount .nitrogen = 0 :=
      realizesListing_amount_eq_zero_of_not_mem hproductListing (by
        simp [ammoniaProductListing])
    have hinputN :
        reactorInput.amount .nitrogen =
          (run.state cycle).recycle.amount .nitrogen +
            freshNitrogenAmount := by
      rw [hmix.2.2.2]
      rfl
    have houtputN :
        reactorOutput.amount .nitrogen =
          reactorInput.amount .nitrogen - extent := by
      rw [hreaction.2.2.2 .nitrogen]
      norm_num [ammoniaFormation, CRNT.Reaction.vector]
      ring
    have hcooledN :
        reactorOutput.amount .nitrogen =
          (run.state (cycle + 1)).recycle.amount .nitrogen := by
      rw [hcooler.2.2.2 .nitrogen, hnewProductN, add_zero]
    change (run.state (cycle + 1)).recycle.amount .nitrogen =
      retentionFactor *
        ((run.state cycle).recycle.amount .nitrogen + freshNitrogenAmount)
    rw [hcooledN] at houtputN
    rw [hextent, hinputN] at houtputN
    unfold retentionFactor
    linarith

/-! ## Part (a): exact amount and four-decimal reporting -/

/-- The source-derived unrounded boundary amount after `n` cycles.  The
`i`th term is one fresh nitrogen portion retained through `i+1` passes. -/
def nitrogenAfterCyclesRaw (cycles : ℕ) : ℝ :=
  freshNitrogenAmount *
    ∑ i ∈ Finset.range cycles, retentionFactor ^ (i + 1)

private theorem shiftedPowerSum_eq_mul_geomSum (ratio : ℝ) (cycles : ℕ) :
    (∑ i ∈ Finset.range cycles, ratio ^ (i + 1)) =
      ratio * ∑ i ∈ Finset.range cycles, ratio ^ i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [pow_succ]
  ring

/-- The requested unrounded amount after cycle 58 and before feed 59. -/
def nitrogenAfter58Raw : ℝ :=
  nitrogenAfterCyclesRaw 58

/-- A geometric sum is the unique solution of the source recurrence. -/
theorem nitrogenBoundaryRecurrence_solution
    (amount : ℕ → ℝ) (h : NitrogenBoundaryRecurrence amount) :
    ∀ cycles : ℕ, amount cycles = nitrogenAfterCyclesRaw cycles := by
  intro cycles
  induction cycles with
  | zero =>
      simpa [nitrogenAfterCyclesRaw] using h.1
  | succ cycles ih =>
      rw [h.2, ih]
      simp only [nitrogenAfterCyclesRaw]
      rw [shiftedPowerSum_eq_mul_geomSum,
        shiftedPowerSum_eq_mul_geomSum, geom_sum_succ]
      ring

/-- Closed form of the exact geometric sum, with no intermediate rounding. -/
theorem nitrogenAfterCyclesRaw_closedForm (cycles : ℕ) :
    nitrogenAfterCyclesRaw cycles =
      freshNitrogenAmount * retentionFactor *
        (1 - retentionFactor ^ cycles) / (1 - retentionFactor) := by
  rw [nitrogenAfterCyclesRaw,
    shiftedPowerSum_eq_mul_geomSum retentionFactor cycles]
  have hdenom : (1 : ℝ) - retentionFactor ≠ 0 := by
    norm_num [retentionFactor, singlePassYield]
  apply (eq_div_iff hdenom).2
  calc
    freshNitrogenAmount *
          (retentionFactor * ∑ i ∈ Finset.range cycles, retentionFactor ^ i) *
        (1 - retentionFactor) =
        freshNitrogenAmount * retentionFactor *
          ((∑ i ∈ Finset.range cycles, retentionFactor ^ i) *
            (1 - retentionFactor)) := by ring
    _ = freshNitrogenAmount * retentionFactor *
          (1 - retentionFactor ^ cycles) := by
        rw [geom_sum_mul_neg]

/-- Source-to-result specification: a run exists, all admissible runs give the
same cycle-58 amount, and the candidate has the exact geometric closed form. -/
def NitrogenAfter58DerivationSpec : Prop :=
  CoreProcessSourceSpec ∧
    Nonempty ProcessRun ∧
    (∀ run : ProcessRun,
      boundaryNitrogen run 58 = nitrogenAfter58Raw) ∧
    nitrogenAfter58Raw =
      freshNitrogenAmount * retentionFactor *
        (1 - retentionFactor ^ (58 : ℕ)) / (1 - retentionFactor)

/-- A nondegenerate exact rational enclosure of the unrounded amount.  It is a
calculation certificate, not a widened source-measurement tolerance. -/
def NitrogenAfter58RawResult : Prop :=
  NitrogenAfter58DerivationSpec ∧
    ((5666209 : ℝ) / 1000000 ≤ nitrogenAfter58Raw ∧
      nitrogenAfter58Raw ≤ (566621 : ℝ) / 100000)

theorem nitrogenAfter58_raw_result : NitrogenAfter58RawResult := by
  refine ⟨⟨coreProcessSourceSpec_holds, processRun_nonempty, ?_, ?_⟩, ?_⟩
  · intro run
    exact nitrogenBoundaryRecurrence_solution
      (boundaryNitrogen run) (processRun_nitrogenRecurrence run) 58
  · exact nitrogenAfterCyclesRaw_closedForm 58
  · change (5666209 : ℝ) / 1000000 ≤ nitrogenAfterCyclesRaw 58 ∧
      nitrogenAfterCyclesRaw 58 ≤ (566621 : ℝ) / 100000
    rw [nitrogenAfterCyclesRaw_closedForm]
    norm_num [freshNitrogenAmount, freshFeed, freshFeedTotal,
      retentionFactor, singlePassYield]

/-- Four decimal places give the fixed reporting quantum `10⁻⁴ mol`. -/
def nitrogenReportingQuantum : ℝ := (1 : ℝ) / 10000

/-- The displayed amount `5.6662 mol`, kept separate from the raw expression. -/
def nitrogenAfter58Reported : ℝ := (28331 : ℝ) / 5000

/-- Reported carrier for part (a), including both derivation and rounding. -/
def NitrogenAfter58ReportedResult : Prop :=
  NitrogenAfter58RawResult ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      nitrogenAfter58Raw nitrogenAfter58Reported nitrogenReportingQuantum

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"nitrogen_after_58_cycles","reporting_policy_kind":"decimal_places","reporting_policy_digits":4,"reported_value":"5.6662","reporting_quantum":"1/10000","raw_declaration":"IChO2026Problems.IChO2026T7A3.nitrogenAfter58Raw","reporting_declaration":"IChO2026Problems.IChO2026T7A3.nitrogenAfter58_reported_result"}
theorem nitrogenAfter58_reported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      nitrogenAfter58Raw nitrogenAfter58Reported nitrogenReportingQuantum := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [nitrogenReportingQuantum]
  · refine ⟨(56662 : ℤ), ?_⟩
    norm_num [nitrogenAfter58Reported, nitrogenReportingQuantum]
  · have hbounds := nitrogenAfter58_raw_result.2
    rw [if_pos (by linarith [hbounds.1] : 0 ≤ nitrogenAfter58Raw)]
    constructor
    · norm_num [nitrogenAfter58Reported, nitrogenReportingQuantum]
      linarith [hbounds.1]
    · norm_num [nitrogenAfter58Reported, nitrogenReportingQuantum]
      linarith [hbounds.2]

/-! ## Part (b): cumulative overall yield and its least cycle -/

/-- Total fresh nitrogen admitted through a cycle boundary, in mol. -/
def totalFreshNitrogen (cycles : ℕ) : ℝ :=
  (cycles : ℝ) * freshNitrogenAmount

/-- The exact overall yield from the source material balance.  The numerator
is fresh nitrogen already converted to separated ammonia (in N₂-equivalent
moles); the denominator is all fresh nitrogen admitted. -/
def overallYieldAfterCycles (cycles : ℕ) : ℝ :=
  if cycles = 0 then 0
  else
    (totalFreshNitrogen cycles - nitrogenAfterCyclesRaw cycles) /
      totalFreshNitrogen cycles

/-- The corresponding product-based yield of a concrete run: cumulative
separated NH₃ divided by the theoretical `2 mol NH₃` per fresh `mol N₂`. -/
def runOverallAmmoniaYield (run : ProcessRun) (cycles : ℕ) : ℝ :=
  if cycles = 0 then 0
  else
    (run.state cycles).cumulativeProduct.amount .ammonia /
      (2 * totalFreshNitrogen cycles)

/-- The atom/reaction/separation ledgers identify the concrete product ratio
with the residual-nitrogen formula used for the threshold calculation. -/
def OverallYieldMaterialBalanceSpec : Prop :=
  ∀ run : ProcessRun, ∀ cycles : ℕ, 0 < cycles →
    runOverallAmmoniaYield run cycles = overallYieldAfterCycles cycles

private theorem processRun_recycle_ammonia_zero
    (run : ProcessRun) (cycles : ℕ) :
    (run.state cycles).recycle.amount .ammonia = 0 := by
  cases cycles with
  | zero =>
      rw [run.initiallyEmpty]
      rfl
  | succ cycle =>
      rcases run.step cycle with
        ⟨_reactorInput, _reactorOutput, _newProduct, _extent,
          _hmix, _hextent, _hreaction, _hcooler, _houtputListing,
          hrecycleListing, _hproductListing, _haccumulation⟩
      exact realizesListing_amount_eq_zero_of_not_mem hrecycleListing (by
        simp [recycleListing])

private theorem processRun_product_nitrogen_balance
    (run : ProcessRun) (cycles : ℕ) :
    (run.state cycles).cumulativeProduct.amount .ammonia +
        2 * (run.state cycles).recycle.amount .nitrogen =
      2 * totalFreshNitrogen cycles := by
  induction cycles with
  | zero =>
      rw [run.initiallyEmpty]
      norm_num [emptyStream, totalFreshNitrogen]
  | succ cycle ih =>
      rcases run.step cycle with
        ⟨reactorInput, reactorOutput, newProduct, extent,
          hmix, _hextent, hreaction, hcooler, _houtputListing,
          hrecycleListing, hproductListing, haccumulation⟩
      have hpreviousA := processRun_recycle_ammonia_zero run cycle
      have hnextA := processRun_recycle_ammonia_zero run (cycle + 1)
      have hnewProductN : newProduct.amount .nitrogen = 0 :=
        realizesListing_amount_eq_zero_of_not_mem hproductListing (by
          simp [ammoniaProductListing])
      have hinputN :
          reactorInput.amount .nitrogen =
            (run.state cycle).recycle.amount .nitrogen +
              freshNitrogenAmount := by
        rw [hmix.2.2.2]
        rfl
      have hinputA : reactorInput.amount .ammonia = 0 := by
        rw [hmix.2.2.2]
        simp [addStreams, hpreviousA, freshFeed]
      have houtputN :
          reactorOutput.amount .nitrogen =
            reactorInput.amount .nitrogen - extent := by
        rw [hreaction.2.2.2 .nitrogen]
        norm_num [ammoniaFormation, CRNT.Reaction.vector]
        ring
      have houtputA :
          reactorOutput.amount .ammonia = 2 * extent := by
        rw [hreaction.2.2.2 .ammonia, hinputA]
        norm_num [ammoniaFormation, CRNT.Reaction.vector]
        ring
      have hcooledN :
          reactorOutput.amount .nitrogen =
            (run.state (cycle + 1)).recycle.amount .nitrogen := by
        rw [hcooler.2.2.2 .nitrogen, hnewProductN, add_zero]
      have hcooledA :
          reactorOutput.amount .ammonia = newProduct.amount .ammonia := by
        rw [hcooler.2.2.2 .ammonia, hnextA, zero_add]
      have hnextN :
          (run.state (cycle + 1)).recycle.amount .nitrogen =
            (run.state cycle).recycle.amount .nitrogen +
              freshNitrogenAmount - extent := by
        linarith [hinputN, houtputN, hcooledN]
      have hnewProductA : newProduct.amount .ammonia = 2 * extent := by
        linarith [houtputA, hcooledA]
      have hproductAcc :
          (run.state (cycle + 1)).cumulativeProduct.amount .ammonia =
            (run.state cycle).cumulativeProduct.amount .ammonia +
              newProduct.amount .ammonia := by
        rw [haccumulation.2.2.2]
        rfl
      rw [hproductAcc, hnewProductA, hnextN]
      simp only [totalFreshNitrogen, Nat.cast_add, Nat.cast_one] at ih ⊢
      ring_nf at ih ⊢
      linarith

theorem overallYield_materialBalance : OverallYieldMaterialBalanceSpec := by
  intro run cycles hcycles
  have hcyclesNe : cycles ≠ 0 := Nat.ne_of_gt hcycles
  have hfresh : freshNitrogenAmount = 1 := by
    norm_num [freshNitrogenAmount, freshFeed, freshFeedTotal]
  have htotalPos : 0 < totalFreshNitrogen cycles := by
    simp [totalFreshNitrogen, hfresh, hcycles]
  have hboundary := nitrogenBoundaryRecurrence_solution
    (boundaryNitrogen run) (processRun_nitrogenRecurrence run) cycles
  have hbalance := processRun_product_nitrogen_balance run cycles
  rw [runOverallAmmoniaYield, overallYieldAfterCycles,
    if_neg hcyclesNe, if_neg hcyclesNe]
  change (run.state cycles).cumulativeProduct.amount .ammonia /
      (2 * totalFreshNitrogen cycles) =
    (totalFreshNitrogen cycles - nitrogenAfterCyclesRaw cycles) /
      totalFreshNitrogen cycles
  rw [← hboundary]
  change (run.state cycles).cumulativeProduct.amount .ammonia /
      (2 * totalFreshNitrogen cycles) =
    (totalFreshNitrogen cycles -
      (run.state cycles).recycle.amount .nitrogen) /
      totalFreshNitrogen cycles
  field_simp
  linarith

/-- After the first cycle, the overall yield is the stipulated `15.0%`. -/
theorem overallYieldAfterOne :
    overallYieldAfterCycles 1 = startingOverallYield.value ∧
      startingOverallYield.value = singlePassYield.value := by
  constructor
  · norm_num [overallYieldAfterCycles, totalFreshNitrogen,
      nitrogenAfterCyclesRaw, freshNitrogenAmount, freshFeed, freshFeedTotal,
      retentionFactor, singlePassYield, startingOverallYield]
  · exact sourceYieldSpec_holds.2.1

/-- The residual fraction is the average of an initial segment of the
decreasing positive sequence `(17/20)^i`; hence overall yield cannot decrease. -/
def OverallYieldMonotonicitySpec : Prop :=
  ∀ earlier later : ℕ,
    0 < earlier → earlier ≤ later →
      overallYieldAfterCycles earlier ≤ overallYieldAfterCycles later

private theorem shiftedPowerSum_lowerBound (cycles : ℕ) :
    (cycles : ℝ) * retentionFactor ^ (cycles + 1) ≤
      ∑ i ∈ Finset.range cycles, retentionFactor ^ (i + 1) := by
  have hratioNonnegative : (0 : ℝ) ≤ retentionFactor := by
    norm_num [retentionFactor, singlePassYield]
  have hratioLeOne : retentionFactor ≤ (1 : ℝ) := by
    norm_num [retentionFactor, singlePassYield]
  calc
    (cycles : ℝ) * retentionFactor ^ (cycles + 1) =
        ∑ _i ∈ Finset.range cycles, retentionFactor ^ (cycles + 1) := by
          simp
    _ ≤ ∑ i ∈ Finset.range cycles, retentionFactor ^ (i + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply pow_le_pow_of_le_one hratioNonnegative hratioLeOne
      have hi : i < cycles := Finset.mem_range.mp hi
      omega

private theorem overallYield_le_succ (cycles : ℕ) :
    overallYieldAfterCycles cycles ≤ overallYieldAfterCycles (cycles + 1) := by
  by_cases hzero : cycles = 0
  · subst cycles
    norm_num [overallYieldAfterCycles, totalFreshNitrogen,
      nitrogenAfterCyclesRaw, freshNitrogenAmount, freshFeed, freshFeedTotal,
      retentionFactor, singlePassYield]
  · have hcyclesNat : 0 < cycles := Nat.pos_of_ne_zero hzero
    have hcyclesReal : (0 : ℝ) < (cycles : ℝ) := by exact_mod_cast hcyclesNat
    have hnextReal : (0 : ℝ) < (cycles + 1 : ℕ) := by positivity
    have hbound := shiftedPowerSum_lowerBound cycles
    simp only [overallYieldAfterCycles, if_neg hzero,
      if_neg (Nat.add_one_ne_zero cycles)]
    simp only [totalFreshNitrogen, nitrogenAfterCyclesRaw]
    have hfresh : freshNitrogenAmount = 1 := by
      norm_num [freshNitrogenAmount, freshFeed, freshFeedTotal]
    rw [hfresh]
    simp only [mul_one, one_mul, Finset.sum_range_succ]
    apply (div_le_div_iff₀ hcyclesReal hnextReal).2
    norm_num [Nat.cast_add, Nat.cast_one] at hbound ⊢
    nlinarith

theorem overallYield_monotone : OverallYieldMonotonicitySpec := by
  intro earlier later _hearlier hle
  exact (monotone_nat_of_le_succ overallYield_le_succ) hle

/-- Positive cycle counts whose cumulative yield has reached `97.0%`. -/
def ReachesTargetOverallYield (cycles : ℕ) : Prop :=
  0 < cycles ∧
    targetOverallYield.value ≤ overallYieldAfterCycles cycles

private theorem reachesTargetOverallYield_189 :
    ReachesTargetOverallYield 189 := by
  constructor
  · norm_num
  · change (97 : ℝ) / 100 ≤ overallYieldAfterCycles 189
    rw [overallYieldAfterCycles, if_neg (by norm_num : (189 : ℕ) ≠ 0),
      nitrogenAfterCyclesRaw_closedForm]
    norm_num [totalFreshNitrogen, freshNitrogenAmount, freshFeed,
      freshFeedTotal, retentionFactor, singlePassYield]

private theorem not_reachesTargetOverallYield_188 :
    ¬ ReachesTargetOverallYield 188 := by
  intro hreach
  have htarget := hreach.2
  change (97 : ℝ) / 100 ≤ overallYieldAfterCycles 188 at htarget
  rw [overallYieldAfterCycles, if_neg (by norm_num : (188 : ℕ) ≠ 0),
    nitrogenAfterCyclesRaw_closedForm] at htarget
  norm_num [totalFreshNitrogen, freshNitrogenAmount, freshFeed,
    freshFeedTotal, retentionFactor, singlePassYield] at htarget

/-- The source recurrence eventually reaches the requested cumulative yield. -/
theorem targetOverallYield_reachable :
    ∃ cycles : ℕ, ReachesTargetOverallYield cycles := by
  exact ⟨189, reachesTargetOverallYield_189⟩

/-- The least source-derived cycle count reaching 97.0%; no finite search bound
is injected into its definition. -/
noncomputable def cyclesFor97Raw : ℕ := by
  classical
  exact Nat.find targetOverallYield_reachable

/-- Exact-integer result specification.  Minimality is over every positive
natural cycle count, and evaluation of that minimum gives cycle 189. -/
def CyclesFor97DerivationSpec : Prop :=
  CoreProcessSourceSpec ∧
    Nonempty ProcessRun ∧
    OverallYieldMaterialBalanceSpec ∧
    OverallYieldMonotonicitySpec ∧
    overallYieldAfterCycles 1 = startingOverallYield.value ∧
    startingOverallYield.value = singlePassYield.value ∧
    ReachesTargetOverallYield cyclesFor97Raw ∧
    (∀ candidate : ℕ,
      ReachesTargetOverallYield candidate → cyclesFor97Raw ≤ candidate) ∧
    cyclesFor97Raw = 189

/-- Raw exact-integer carrier for requested output `cycles_for_97_percent`. -/
def CyclesFor97RawResult : Prop :=
  CyclesFor97DerivationSpec

theorem cyclesFor97_raw_result : CyclesFor97RawResult := by
  classical
  have hrawReaches : ReachesTargetOverallYield cyclesFor97Raw := by
    exact Nat.find_spec targetOverallYield_reachable
  have hminimal : ∀ candidate : ℕ,
      ReachesTargetOverallYield candidate → cyclesFor97Raw ≤ candidate := by
    intro candidate hcandidate
    exact Nat.find_min' targetOverallYield_reachable hcandidate
  have hvalue : cyclesFor97Raw = 189 := by
    apply Nat.le_antisymm
    · exact hminimal 189 reachesTargetOverallYield_189
    · by_contra hnot
      have hle188 : cyclesFor97Raw ≤ 188 := by omega
      have hyieldLe :
          overallYieldAfterCycles cyclesFor97Raw ≤
            overallYieldAfterCycles 188 :=
        overallYield_monotone cyclesFor97Raw 188 hrawReaches.1 hle188
      apply not_reachesTargetOverallYield_188
      exact ⟨by norm_num,
        hrawReaches.2.trans hyieldLe⟩
  exact ⟨coreProcessSourceSpec_holds, processRun_nonempty,
    overallYield_materialBalance, overallYield_monotone,
    overallYieldAfterOne.1, overallYieldAfterOne.2, hrawReaches,
    hminimal, hvalue⟩

/-- Exact integers are reported without a rounding transformation. -/
def CyclesFor97ReportedResult : Prop :=
  CyclesFor97RawResult ∧ cyclesFor97Raw = 189

theorem cyclesFor97_reported_result : CyclesFor97ReportedResult := by
  exact ⟨cyclesFor97_raw_result, cyclesFor97_raw_result.2.2.2.2.2.2.2.2⟩

/-! ## Mixed answer-blind result contracts -/

/-- Both raw requested outputs, in controller-fixed source order. -/
def RawResult : Prop :=
  NitrogenAfter58RawResult ∧ CyclesFor97RawResult

/-- Four-place numerical reporting followed by the exact integer output. -/
def ReportedResult : Prop :=
  NitrogenAfter58ReportedResult ∧ CyclesFor97ReportedResult

theorem rawResult_semantics : RawResult := by
  exact ⟨nitrogenAfter58_raw_result, cyclesFor97_raw_result⟩

theorem reportedResult_semantics : ReportedResult := by
  exact ⟨⟨nitrogenAfter58_raw_result, nitrogenAfter58_reported_result⟩,
    cyclesFor97_reported_result⟩

/-- Payload-bound raw symbolic-result contract. -/
theorem raw_result :
    ("37979ddbbb1e3aeb1aae361be7fff9850e3547d43b4956a7fc653978b5fff804" : String) =
      "37979ddbbb1e3aeb1aae361be7fff9850e3547d43b4956a7fc653978b5fff804" ∧
    IChO2026Problems.IChO2026T7A3.RawResult := by
  exact ⟨rfl, rawResult_semantics⟩

/-- Payload-bound reported symbolic-result contract. -/
theorem reported_result :
    ("6e4a5eaf88829251e7d0f603c7a8393e8e64eeaeb19d65a7787c04d311507ef7" : String) =
      "6e4a5eaf88829251e7d0f603c7a8393e8e64eeaeb19d65a7787c04d311507ef7" ∧
    IChO2026Problems.IChO2026T7A3.ReportedResult := by
  exact ⟨rfl, reportedResult_semantics⟩

end IChO2026Problems.IChO2026T7A3
