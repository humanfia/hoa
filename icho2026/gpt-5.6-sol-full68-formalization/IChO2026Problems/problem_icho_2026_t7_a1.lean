import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T7-A1: material-flow reconstruction of M1 and M2

The source is Fig. 1 on `T7_page-1.png`.  This is a
`quantitative_material_stage` formalization: the requested complete gas sets
and the comparison of the feed coefficients depend on exact reaction,
mixing, separation, and recycle ledgers.

In particular, the recycle labelled `N₂, H₂` is mixed with the freshly
scrubbed gas before the ammonia reaction.  It is not silently discarded from
the reactor inlet.  The only finite species domain is the eight formulae
printed in the figure, and no anonymous `other` stream is available.
-/

namespace IChO2026Problems
namespace ProblemIcho2026T7A1

/-- The complete species domain printed in Fig. 1. -/
inductive Species where
  | methane
  | water
  | carbonMonoxide
  | hydrogen
  | nitrogen
  | oxygen
  | carbonDioxide
  | ammonia
  deriving DecidableEq, Fintype, Repr

/-- Elements needed for the atom ledgers of the four displayed reactions. -/
inductive Element where
  | carbon
  | hydrogen
  | nitrogen
  | oxygen
  deriving DecidableEq, Fintype, Repr

/-- Permitted provenance classes from the problem-only source contract. -/
inductive Provenance where
  | problemText
  | problemImage
  | problemStatedFallback
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- Exact source locations in the single bound figure and its caption/text. -/
inductive SourceLocator where
  | wholeFigure
  | freshFeedLabel
  | steamReformingArrow
  | reformerOutletLabel
  | airFeedLabel
  | partialOxidationArrow
  | mixture1Tag
  | shiftWaterLabel
  | waterGasShiftArrow
  | shiftedOutletLabel
  | scrubberTag
  | scrubbedOutletLabel
  | ammoniaFormationArrow
  | mixture2Tag
  | coolerTag
  | ammoniaProductLabel
  | recycleLabel
  | quantitativeReactionsSentence
  deriving DecidableEq, Repr

/-- The requested results consume exact material ledgers. -/
inductive StagedTransformationClass where
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

def stagedTransformationClass : StagedTransformationClass :=
  .quantitativeMaterialStage

/-- The figure explicitly treats M1, M2, reactor interconnects, and recycle as
gas streams.  The phase of material leaving a separator is not printed. -/
inductive Phase where
  | gas
  | unspecifiedAfterSeparation
  deriving DecidableEq, Repr

/-- A phase-indexed stream of molar amounts in one common amount unit. -/
structure Stream (phase : Phase) where
  amount : Species → ℝ

abbrev GasStream := Stream .gas
abbrev SeparatedStream := Stream .unspecifiedAfterSeparation

/-- Every amount in a physical stream is nonnegative. -/
def NonnegativeStream {phase : Phase} (q : Stream phase) : Prop :=
  ∀ s, 0 ≤ q.amount s

/-- The exact finite set of species present in a stream. -/
noncomputable def speciesPresent {phase : Phase} (q : Stream phase) : Finset Species :=
  Finset.univ.filter fun s => 0 < q.amount s

/-- Pointwise addition is the component ledger for a mixer. -/
def addGasStreams (a b : GasStream) : GasStream where
  amount := fun s => a.amount s + b.amount s

/-- A source-observed complete comma-separated stream label. -/
structure SourcedSpeciesSet where
  species : Finset Species
  provenance : Provenance
  locator : SourceLocator

/-- A stream realizes every and only the species in a printed label. -/
def RealizesListing {phase : Phase} (q : Stream phase)
    (listing : SourcedSpeciesSet) : Prop :=
  NonnegativeStream q ∧ speciesPresent q = listing.species

/-- A gas feed together with the precise figure label from which it came. -/
structure SourcedGasStream where
  stream : GasStream
  provenance : Provenance
  locator : SourceLocator

/-- Molecular atom counts read from the eight displayed formulae. -/
def atomCount : Species → Element → ℕ
  | .methane, .carbon => 1
  | .methane, .hydrogen => 4
  | .water, .hydrogen => 2
  | .water, .oxygen => 1
  | .carbonMonoxide, .carbon => 1
  | .carbonMonoxide, .oxygen => 1
  | .hydrogen, .hydrogen => 2
  | .nitrogen, .nitrogen => 2
  | .oxygen, .oxygen => 2
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .oxygen => 2
  | .ammonia, .nitrogen => 1
  | .ammonia, .hydrogen => 3
  | _, _ => 0

/-- Every molecular species displayed in Fig. 1 is neutral. -/
def formalCharge (_ : Species) : ℤ := 0

/-- A reaction paired with the printed arrow that supplies its stoichiometry. -/
structure SourcedReaction where
  reaction : CRNT.Reaction Species
  provenance : Provenance
  locator : SourceLocator

/-- `CH₄ + H₂O → CO + 3 H₂`, copied coefficient-for-coefficient. -/
def steamReforming : SourcedReaction where
  reaction := {
    source := fun
      | .methane => 1
      | .water => 1
      | _ => 0
    target := fun
      | .carbonMonoxide => 1
      | .hydrogen => 3
      | _ => 0 }
  provenance := .problemImage
  locator := .steamReformingArrow

/-- `2 CH₄ + O₂ → 2 CO + 4 H₂`, copied coefficient-for-coefficient. -/
def partialOxidation : SourcedReaction where
  reaction := {
    source := fun
      | .methane => 2
      | .oxygen => 1
      | _ => 0
    target := fun
      | .carbonMonoxide => 2
      | .hydrogen => 4
      | _ => 0 }
  provenance := .problemImage
  locator := .partialOxidationArrow

/-- `CO + H₂O → CO₂ + H₂`, copied coefficient-for-coefficient. -/
def waterGasShift : SourcedReaction where
  reaction := {
    source := fun
      | .carbonMonoxide => 1
      | .water => 1
      | _ => 0
    target := fun
      | .carbonDioxide => 1
      | .hydrogen => 1
      | _ => 0 }
  provenance := .problemImage
  locator := .waterGasShiftArrow

/-- `N₂ + 3 H₂ ⇌ 2 NH₃`; the real extent is a net forward extent. -/
def ammoniaFormation : SourcedReaction where
  reaction := {
    source := fun
      | .nitrogen => 1
      | .hydrogen => 3
      | _ => 0
    target := fun
      | .ammonia => 2
      | _ => 0 }
  provenance := .problemImage
  locator := .ammoniaFormationArrow

/-- Atom count of a stoichiometric complex. -/
def complexAtomCount (c : CRNT.Complex Species) (e : Element) : ℕ :=
  ∑ s, c s * atomCount s e

/-- Formal charge of a stoichiometric complex. -/
def complexCharge (c : CRNT.Complex Species) : ℤ :=
  ∑ s, (c s : ℤ) * formalCharge s

def AtomBalanced (r : CRNT.Reaction Species) : Prop :=
  ∀ e, complexAtomCount r.source e = complexAtomCount r.target e

def ChargeBalanced (r : CRNT.Reaction Species) : Prop :=
  complexCharge r.source = complexCharge r.target

/-- Formula-derived molar mass with arbitrary elemental masses.  No external
atomic-weight values are needed for this exact-symbolic question. -/
def formulaMass (atomicMass : Element → ℝ) (s : Species) : ℝ :=
  ∑ e, (atomCount s e : ℝ) * atomicMass e

def complexMass (atomicMass : Element → ℝ) (c : CRNT.Complex Species) : ℝ :=
  ∑ s, (c s : ℝ) * formulaMass atomicMass s

/-- Total amount of one element in any phase-indexed stream. -/
def streamAtomAmount {phase : Phase} (q : Stream phase) (e : Element) : ℝ :=
  ∑ s, q.amount s * (atomCount s e : ℝ)

/-- Exact species update caused by a reaction extent. -/
def reactionStep (input : GasStream) (r : CRNT.Reaction Species)
    (extent : ℝ) : GasStream where
  amount := fun s => input.amount s + extent * r.vector s

/-- A reaction-stage component ledger, including physical nonnegativity. -/
def ReactionStage (input output : GasStream) (r : CRNT.Reaction Species)
    (extent : ℝ) : Prop :=
  0 ≤ extent ∧
    NonnegativeStream input ∧
    NonnegativeStream output ∧
    output = reactionStep input r extent

/-- The source sentence that a reaction is quantitative is represented as a
positive exact reaction extent for which at least one printed reactant is
exhausted.  No limiting reactant is selected in advance. -/
def QuantitativeReactionStage (input output : GasStream)
    (r : CRNT.Reaction Species) (extent : ℝ) : Prop :=
  ReactionStage input output r extent ∧
    0 < extent ∧
    ∃ s ∈ CRNT.Complex.support r.source, output.amount s = 0

/-- Exact component balance at a gas-stream mixer. -/
def MixingStage (left right combined : GasStream) : Prop :=
  NonnegativeStream left ∧
    NonnegativeStream right ∧
    NonnegativeStream combined ∧
    combined = addGasStreams left right

/-- Exact component balance at a separator.  The phase indices deliberately
allow the removed product phase to remain unspecified. -/
def ComponentSplit {inputPhase leftPhase rightPhase : Phase}
    (input : Stream inputPhase) (left : Stream leftPhase)
    (right : Stream rightPhase) : Prop :=
  NonnegativeStream input ∧
    NonnegativeStream left ∧
    NonnegativeStream right ∧
    ∀ s, input.amount s = left.amount s + right.amount s

/-- Every printed reaction conserves atoms. -/
theorem steamReforming_atomBalanced :
    AtomBalanced steamReforming.reaction := by
  unfold AtomBalanced
  intro e
  cases e <;> native_decide

theorem partialOxidation_atomBalanced :
    AtomBalanced partialOxidation.reaction := by
  unfold AtomBalanced
  intro e
  cases e <;> native_decide

theorem waterGasShift_atomBalanced :
    AtomBalanced waterGasShift.reaction := by
  unfold AtomBalanced
  intro e
  cases e <;> native_decide

theorem ammoniaFormation_atomBalanced :
    AtomBalanced ammoniaFormation.reaction := by
  unfold AtomBalanced
  intro e
  cases e <;> native_decide

/-- Every printed reaction also conserves formal charge. -/
theorem steamReforming_chargeBalanced :
    ChargeBalanced steamReforming.reaction := by
  simp [ChargeBalanced, complexCharge, formalCharge]

theorem partialOxidation_chargeBalanced :
    ChargeBalanced partialOxidation.reaction := by
  simp [ChargeBalanced, complexCharge, formalCharge]

theorem waterGasShift_chargeBalanced :
    ChargeBalanced waterGasShift.reaction := by
  simp [ChargeBalanced, complexCharge, formalCharge]

theorem ammoniaFormation_chargeBalanced :
    ChargeBalanced ammoniaFormation.reaction := by
  simp [ChargeBalanced, complexCharge, formalCharge]

/-- Atom balance also yields a generic mass balance for every assignment of
elemental masses; no numerical atomic-weight premise is hidden here. -/
theorem atomBalanced_implies_massBalanced
    (r : CRNT.Reaction Species) (h : AtomBalanced r)
    (atomicMass : Element → ℝ) :
    complexMass atomicMass r.source = complexMass atomicMass r.target := by
  classical
  unfold AtomBalanced at h
  unfold complexMass formulaMass
  have hreal (e : Element) :
      (∑ s, (r.source s : ℝ) * (atomCount s e : ℝ)) =
        ∑ s, (r.target s : ℝ) * (atomCount s e : ℝ) := by
    exact_mod_cast h e
  have rearrange (c : CRNT.Complex Species) :
      (∑ s, (c s : ℝ) * ∑ e, (atomCount s e : ℝ) * atomicMass e) =
        ∑ e, (∑ s, (c s : ℝ) * (atomCount s e : ℝ)) * atomicMass e := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [rearrange r.source, rearrange r.target]
  apply Finset.sum_congr rfl
  intro e _
  rw [hreal e]

/-- An exact reaction stage preserves each elemental stream ledger. -/
theorem reactionStage_preserves_atoms
    {input output : GasStream} {r : CRNT.Reaction Species} {extent : ℝ}
    (hstage : ReactionStage input output r extent)
    (hbalanced : AtomBalanced r) :
    ∀ e, streamAtomAmount output e = streamAtomAmount input e := by
  classical
  rcases hstage with ⟨_, _, _, rfl⟩
  intro e
  have hreal :
      (∑ s, (r.source s : ℝ) * (atomCount s e : ℝ)) =
        ∑ s, (r.target s : ℝ) * (atomCount s e : ℝ) := by
    exact_mod_cast hbalanced e
  have hzero :
      (∑ s, extent * r.vector s * (atomCount s e : ℝ)) = 0 := by
    calc
      (∑ s, extent * r.vector s * (atomCount s e : ℝ)) =
          extent *
            ((∑ s, (r.target s : ℝ) * (atomCount s e : ℝ)) -
              ∑ s, (r.source s : ℝ) * (atomCount s e : ℝ)) := by
                rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
                  ← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro s _
                simp only [CRNT.Reaction.vector_apply]
                ring
      _ = 0 := by rw [← hreal]; ring
  unfold streamAtomAmount reactionStep
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, hzero, add_zero]

/-- A pointwise separator balance preserves every elemental amount. -/
theorem componentSplit_preserves_atoms
    {inputPhase leftPhase rightPhase : Phase}
    {input : Stream inputPhase} {left : Stream leftPhase}
    {right : Stream rightPhase}
    (hsplit : ComponentSplit input left right) :
    ∀ e, streamAtomAmount input e =
      streamAtomAmount left e + streamAtomAmount right e := by
  classical
  rcases hsplit with ⟨_, _, _, hcomponent⟩
  intro e
  unfold streamAtomAmount
  calc
    (∑ s, input.amount s * (atomCount s e : ℝ)) =
        ∑ s, (left.amount s + right.amount s) * (atomCount s e : ℝ) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [hcomponent s]
    _ = (∑ s, left.amount s * (atomCount s e : ℝ)) +
          ∑ s, right.amount s * (atomCount s e : ℝ) := by
            simp_rw [add_mul]
            rw [Finset.sum_add_distrib]

/-- The fresh feed printed as `x CH₄ + y H₂O`. -/
def freshFeedObservation (x y : ℝ) : SourcedGasStream where
  stream := {
    amount := fun
      | .methane => x
      | .water => y
      | _ => 0 }
  provenance := .problemImage
  locator := .freshFeedLabel

/-- The air feed printed as `4 N₂ + 1 O₂`. -/
def airFeedObservation : SourcedGasStream where
  stream := {
    amount := fun
      | .nitrogen => 4
      | .oxygen => 1
      | _ => 0 }
  provenance := .problemImage
  locator := .airFeedLabel

/-- The separately drawn water feed into the shift reactor. -/
def shiftWaterObservation (amount : ℝ) : SourcedGasStream where
  stream := {
    amount := fun
      | .water => amount
      | _ => 0 }
  provenance := .problemImage
  locator := .shiftWaterLabel

/-- Complete eight-species staged domain, fixed before deriving an answer. -/
def processSpeciesDomain : SourcedSpeciesSet where
  species := Finset.univ
  provenance := .problemImage
  locator := .wholeFigure

def reformerOutletListing : SourcedSpeciesSet where
  species := {.methane, .carbonMonoxide, .hydrogen}
  provenance := .problemImage
  locator := .reformerOutletLabel

def shiftedOutletListing : SourcedSpeciesSet where
  species := {.nitrogen, .carbonDioxide, .hydrogen}
  provenance := .problemImage
  locator := .shiftedOutletLabel

def capturedCarbonDioxideListing : SourcedSpeciesSet where
  species := {.carbonDioxide}
  provenance := .problemImage
  locator := .scrubberTag

def scrubbedOutletListing : SourcedSpeciesSet where
  species := {.nitrogen, .hydrogen}
  provenance := .problemImage
  locator := .scrubbedOutletLabel

def recycleListing : SourcedSpeciesSet where
  species := {.nitrogen, .hydrogen}
  provenance := .problemImage
  locator := .recycleLabel

def ammoniaProductListing : SourcedSpeciesSet where
  species := {.ammonia}
  provenance := .problemImage
  locator := .ammoniaProductLabel

/-- Full closed-loop material model read from Fig. 1.

No field states the composition of M1, the composition of M2, or a relation
between `x` and `y`.  The labelled streams are the neighboring source
observations.  The ammonia inlet is explicitly the mixer output of fresh
scrubbed gas and cooler recycle. -/
structure PlantModel where
  x : ℝ
  y : ℝ
  shiftWaterAmount : ℝ
  reformingExtent : ℝ
  oxidationExtent : ℝ
  shiftExtent : ℝ
  ammoniaExtent : ℝ

  freshFeed : GasStream
  reformerOutlet : GasStream
  air : GasStream
  oxidationInput : GasStream
  mixture1 : GasStream
  shiftWater : GasStream
  shiftInput : GasStream
  shiftedOutlet : GasStream
  scrubbedFeed : GasStream
  capturedCarbonDioxide : SeparatedStream
  ammoniaInput : GasStream
  mixture2 : GasStream
  recycle : GasStream
  ammoniaProduct : SeparatedStream

  x_positive : 0 < x
  y_positive : 0 < y
  shiftWater_positive : 0 < shiftWaterAmount

  freshFeed_source : freshFeed = (freshFeedObservation x y).stream
  reforming_quantitative :
    QuantitativeReactionStage freshFeed reformerOutlet
      steamReforming.reaction reformingExtent
  reformerOutlet_label :
    RealizesListing reformerOutlet reformerOutletListing

  air_source : air = airFeedObservation.stream
  oxidation_mixer : MixingStage reformerOutlet air oxidationInput
  oxidation_quantitative :
    QuantitativeReactionStage oxidationInput mixture1
      partialOxidation.reaction oxidationExtent

  shiftWater_source :
    shiftWater = (shiftWaterObservation shiftWaterAmount).stream
  shift_mixer : MixingStage mixture1 shiftWater shiftInput
  shift_quantitative :
    QuantitativeReactionStage shiftInput shiftedOutlet
      waterGasShift.reaction shiftExtent
  shiftedOutlet_label :
    RealizesListing shiftedOutlet shiftedOutletListing

  scrubber_split :
    ComponentSplit shiftedOutlet scrubbedFeed capturedCarbonDioxide
  scrubbedOutlet_label :
    RealizesListing scrubbedFeed scrubbedOutletListing
  capturedCarbonDioxide_label :
    RealizesListing capturedCarbonDioxide capturedCarbonDioxideListing

  ammonia_mixer : MixingStage scrubbedFeed recycle ammoniaInput
  ammonia_stage :
    ReactionStage ammoniaInput mixture2
      ammoniaFormation.reaction ammoniaExtent

  cooler_split : ComponentSplit mixture2 recycle ammoniaProduct
  recycle_label : RealizesListing recycle recycleListing
  ammoniaProduct_label :
    RealizesListing ammoniaProduct ammoniaProductListing

/-- Requested output carrier `gases_m1`, introduced only as a proposed answer
to be checked against every `PlantModel`. -/
def gasesM1Output : Finset Species :=
  {.nitrogen, .carbonMonoxide, .hydrogen}

/-- Requested output carrier `gases_m2`. -/
def gasesM2Output : Finset Species :=
  {.nitrogen, .hydrogen, .ammonia}

/-- The three mutually exclusive comparison classifications for `x` and `y`. -/
inductive XYRelation where
  | xLessThanY
  | xEqualsY
  | xGreaterThanY
  deriving DecidableEq, Repr

/-- Requested output carrier `xy_relation`. -/
def xyRelationOutput : XYRelation := .xGreaterThanY

/-- Numerical meaning of each comparison classification. -/
def XYRelation.Holds (relation : XYRelation) (x y : ℝ) : Prop :=
  match relation with
  | .xLessThanY => x < y
  | .xEqualsY => x = y
  | .xGreaterThanY => y < x

/-- The source constraints are jointly satisfiable.  A concrete witness may
use `x = 7/2`, `y = 3/2`, fresh post-scrubber flow `4 N₂ + 12 H₂`, and a
positive `N₂/H₂` recycle; those values are a consistency witness, not fields
of the source assumptions or requested outputs. -/
theorem plantModel_nonempty : Nonempty PlantModel := by
  classical
  let fresh : GasStream := {
    amount := fun
      | .methane => 7 / 2
      | .water => 3 / 2
      | _ => 0 }
  let reformer : GasStream := {
    amount := fun
      | .methane => 2
      | .carbonMonoxide => 3 / 2
      | .hydrogen => 9 / 2
      | _ => 0 }
  let air : GasStream := {
    amount := fun
      | .nitrogen => 4
      | .oxygen => 1
      | _ => 0 }
  let oxidationInput : GasStream := {
    amount := fun
      | .methane => 2
      | .carbonMonoxide => 3 / 2
      | .hydrogen => 9 / 2
      | .nitrogen => 4
      | .oxygen => 1
      | _ => 0 }
  let mixture1 : GasStream := {
    amount := fun
      | .carbonMonoxide => 7 / 2
      | .hydrogen => 17 / 2
      | .nitrogen => 4
      | _ => 0 }
  let shiftWater : GasStream := {
    amount := fun
      | .water => 7 / 2
      | _ => 0 }
  let shiftInput : GasStream := {
    amount := fun
      | .water => 7 / 2
      | .carbonMonoxide => 7 / 2
      | .hydrogen => 17 / 2
      | .nitrogen => 4
      | _ => 0 }
  let shifted : GasStream := {
    amount := fun
      | .hydrogen => 12
      | .nitrogen => 4
      | .carbonDioxide => 7 / 2
      | _ => 0 }
  let scrubbed : GasStream := {
    amount := fun
      | .hydrogen => 12
      | .nitrogen => 4
      | _ => 0 }
  let captured : SeparatedStream := {
    amount := fun
      | .carbonDioxide => 7 / 2
      | _ => 0 }
  let recycle : GasStream := {
    amount := fun
      | .hydrogen => 3
      | .nitrogen => 1
      | _ => 0 }
  let ammoniaInput : GasStream := {
    amount := fun
      | .hydrogen => 15
      | .nitrogen => 5
      | _ => 0 }
  let mixture2 : GasStream := {
    amount := fun
      | .hydrogen => 3
      | .nitrogen => 1
      | .ammonia => 8
      | _ => 0 }
  let product : SeparatedStream := {
    amount := fun
      | .ammonia => 8
      | _ => 0 }
  have fresh_nonnegative : NonnegativeStream fresh := by
    intro s
    cases s <;> norm_num [fresh]
  have reformer_nonnegative : NonnegativeStream reformer := by
    intro s
    cases s <;> norm_num [reformer]
  have air_nonnegative : NonnegativeStream air := by
    intro s
    cases s <;> norm_num [air]
  have oxidationInput_nonnegative : NonnegativeStream oxidationInput := by
    intro s
    cases s <;> norm_num [oxidationInput]
  have mixture1_nonnegative : NonnegativeStream mixture1 := by
    intro s
    cases s <;> norm_num [mixture1]
  have shiftWater_nonnegative : NonnegativeStream shiftWater := by
    intro s
    cases s <;> norm_num [shiftWater]
  have shiftInput_nonnegative : NonnegativeStream shiftInput := by
    intro s
    cases s <;> norm_num [shiftInput]
  have shifted_nonnegative : NonnegativeStream shifted := by
    intro s
    cases s <;> norm_num [shifted]
  have scrubbed_nonnegative : NonnegativeStream scrubbed := by
    intro s
    cases s <;> norm_num [scrubbed]
  have captured_nonnegative : NonnegativeStream captured := by
    intro s
    cases s <;> norm_num [captured]
  have recycle_nonnegative : NonnegativeStream recycle := by
    intro s
    cases s <;> norm_num [recycle]
  have ammoniaInput_nonnegative : NonnegativeStream ammoniaInput := by
    intro s
    cases s <;> norm_num [ammoniaInput]
  have mixture2_nonnegative : NonnegativeStream mixture2 := by
    intro s
    cases s <;> norm_num [mixture2]
  have product_nonnegative : NonnegativeStream product := by
    intro s
    cases s <;> norm_num [product]
  have stream_eq {phase : Phase} (q₁ q₂ : Stream phase)
      (h : ∀ s, q₁.amount s = q₂.amount s) : q₁ = q₂ := by
    cases q₁ with
    | mk a =>
      cases q₂ with
      | mk b =>
        have hab : a = b := funext h
        cases hab
        rfl
  have reforming_quantitative :
      QuantitativeReactionStage fresh reformer steamReforming.reaction
        (3 / 2) := by
    refine ⟨⟨by norm_num, fresh_nonnegative, reformer_nonnegative, ?_⟩,
      by norm_num, ?_⟩
    · apply stream_eq
      intro s
      cases s <;>
        norm_num [fresh, reformer, reactionStep, steamReforming,
          CRNT.Reaction.vector]
    · refine ⟨.water, ?_, ?_⟩
      · simp [CRNT.Complex.support, steamReforming]
      · norm_num [reformer]
  have reformer_listing : RealizesListing reformer reformerOutletListing := by
    refine ⟨reformer_nonnegative, ?_⟩
    apply Finset.ext
    intro s
    cases s <;>
      norm_num [speciesPresent, reformer, reformerOutletListing] <;> simp
  have oxidation_mixer : MixingStage reformer air oxidationInput := by
    refine ⟨reformer_nonnegative, air_nonnegative,
      oxidationInput_nonnegative, ?_⟩
    apply stream_eq
    intro s
    cases s <;> norm_num [reformer, air, oxidationInput, addGasStreams]
  have oxidation_quantitative :
      QuantitativeReactionStage oxidationInput mixture1
        partialOxidation.reaction 1 := by
    refine ⟨⟨by norm_num, oxidationInput_nonnegative,
      mixture1_nonnegative, ?_⟩, by norm_num, ?_⟩
    · apply stream_eq
      intro s
      cases s <;>
        norm_num [oxidationInput, mixture1, reactionStep, partialOxidation,
          CRNT.Reaction.vector]
    · refine ⟨.oxygen, ?_, ?_⟩
      · simp [CRNT.Complex.support, partialOxidation]
      · norm_num [mixture1]
  have shift_mixer : MixingStage mixture1 shiftWater shiftInput := by
    refine ⟨mixture1_nonnegative, shiftWater_nonnegative,
      shiftInput_nonnegative, ?_⟩
    apply stream_eq
    intro s
    cases s <;> norm_num [mixture1, shiftWater, shiftInput, addGasStreams]
  have shift_quantitative :
      QuantitativeReactionStage shiftInput shifted waterGasShift.reaction
        (7 / 2) := by
    refine ⟨⟨by norm_num, shiftInput_nonnegative, shifted_nonnegative, ?_⟩,
      by norm_num, ?_⟩
    · apply stream_eq
      intro s
      cases s <;>
        norm_num [shiftInput, shifted, reactionStep, waterGasShift,
          CRNT.Reaction.vector]
    · refine ⟨.carbonMonoxide, ?_, ?_⟩
      · simp [CRNT.Complex.support, waterGasShift]
      · norm_num [shifted]
  have shifted_listing : RealizesListing shifted shiftedOutletListing := by
    refine ⟨shifted_nonnegative, ?_⟩
    apply Finset.ext
    intro s
    cases s <;>
      norm_num [speciesPresent, shifted, shiftedOutletListing] <;> simp
  have scrubber_split : ComponentSplit shifted scrubbed captured := by
    refine ⟨shifted_nonnegative, scrubbed_nonnegative,
      captured_nonnegative, ?_⟩
    intro s
    cases s <;> norm_num [shifted, scrubbed, captured]
  have scrubbed_listing : RealizesListing scrubbed scrubbedOutletListing := by
    refine ⟨scrubbed_nonnegative, ?_⟩
    apply Finset.ext
    intro s
    cases s <;>
      norm_num [speciesPresent, scrubbed, scrubbedOutletListing] <;> simp
  have captured_listing :
      RealizesListing captured capturedCarbonDioxideListing := by
    refine ⟨captured_nonnegative, ?_⟩
    apply Finset.ext
    intro s
    cases s <;>
      norm_num [speciesPresent, captured, capturedCarbonDioxideListing] <;> simp
  have ammonia_mixer : MixingStage scrubbed recycle ammoniaInput := by
    refine ⟨scrubbed_nonnegative, recycle_nonnegative,
      ammoniaInput_nonnegative, ?_⟩
    apply stream_eq
    intro s
    cases s <;>
      norm_num [scrubbed, recycle, ammoniaInput, addGasStreams]
  have ammonia_stage :
      ReactionStage ammoniaInput mixture2 ammoniaFormation.reaction 4 := by
    refine ⟨by norm_num, ammoniaInput_nonnegative,
      mixture2_nonnegative, ?_⟩
    apply stream_eq
    intro s
    cases s <;>
      norm_num [ammoniaInput, mixture2, reactionStep, ammoniaFormation,
        CRNT.Reaction.vector]
  have cooler_split : ComponentSplit mixture2 recycle product := by
    refine ⟨mixture2_nonnegative, recycle_nonnegative,
      product_nonnegative, ?_⟩
    intro s
    cases s <;> norm_num [mixture2, recycle, product]
  have recycle_listing : RealizesListing recycle recycleListing := by
    refine ⟨recycle_nonnegative, ?_⟩
    apply Finset.ext
    intro s
    cases s <;>
      norm_num [speciesPresent, recycle, recycleListing] <;> simp
  have product_listing : RealizesListing product ammoniaProductListing := by
    refine ⟨product_nonnegative, ?_⟩
    apply Finset.ext
    intro s
    cases s <;>
      norm_num [speciesPresent, product, ammoniaProductListing] <;> simp
  refine ⟨{
    x := 7 / 2
    y := 3 / 2
    shiftWaterAmount := 7 / 2
    reformingExtent := 3 / 2
    oxidationExtent := 1
    shiftExtent := 7 / 2
    ammoniaExtent := 4
    freshFeed := fresh
    reformerOutlet := reformer
    air := air
    oxidationInput := oxidationInput
    mixture1 := mixture1
    shiftWater := shiftWater
    shiftInput := shiftInput
    shiftedOutlet := shifted
    scrubbedFeed := scrubbed
    capturedCarbonDioxide := captured
    ammoniaInput := ammoniaInput
    mixture2 := mixture2
    recycle := recycle
    ammoniaProduct := product
    x_positive := by norm_num
    y_positive := by norm_num
    shiftWater_positive := by norm_num
    freshFeed_source := by
      apply stream_eq
      intro s
      cases s <;> norm_num [fresh, freshFeedObservation]
    reforming_quantitative := reforming_quantitative
    reformerOutlet_label := reformer_listing
    air_source := by
      apply stream_eq
      intro s
      cases s <;> norm_num [air, airFeedObservation]
    oxidation_mixer := oxidation_mixer
    oxidation_quantitative := oxidation_quantitative
    shiftWater_source := by
      apply stream_eq
      intro s
      cases s <;> norm_num [shiftWater, shiftWaterObservation]
    shift_mixer := shift_mixer
    shift_quantitative := shift_quantitative
    shiftedOutlet_label := shifted_listing
    scrubber_split := scrubber_split
    scrubbedOutlet_label := scrubbed_listing
    capturedCarbonDioxide_label := captured_listing
    ammonia_mixer := ammonia_mixer
    ammonia_stage := ammonia_stage
    cooler_split := cooler_split
    recycle_label := recycle_listing
    ammoniaProduct_label := product_listing }⟩

/-- Requested output `gases_m1`: precisely N₂, CO, and H₂ occur in M1. -/
theorem gases_m1 (p : PlantModel) :
    speciesPresent p.mixture1 = gasesM1Output := by
  classical
  have href_stage := p.reforming_quantitative.1.2.2.2
  have hoxidation_mix := p.oxidation_mixer.2.2.2
  have hoxidation_stage := p.oxidation_quantitative.1.2.2.2
  have hshift_mix := p.shift_mixer.2.2.2
  have hshift_stage := p.shift_quantitative.1.2.2.2
  have href_ledger (s : Species) :
      p.reformerOutlet.amount s = p.freshFeed.amount s +
        p.reformingExtent * steamReforming.reaction.vector s :=
    congrArg (fun q : GasStream => q.amount s) href_stage
  have hoxidation_input_ledger (s : Species) :
      p.oxidationInput.amount s =
        p.reformerOutlet.amount s + p.air.amount s :=
    congrArg (fun q : GasStream => q.amount s) hoxidation_mix
  have hm1_ledger (s : Species) :
      p.mixture1.amount s =
        (p.reformerOutlet.amount s + p.air.amount s) +
          p.oxidationExtent * partialOxidation.reaction.vector s := by
    calc
      p.mixture1.amount s = p.oxidationInput.amount s +
          p.oxidationExtent * partialOxidation.reaction.vector s :=
        congrArg (fun q : GasStream => q.amount s) hoxidation_stage
      _ = (p.reformerOutlet.amount s + p.air.amount s) +
          p.oxidationExtent * partialOxidation.reaction.vector s := by
        rw [hoxidation_input_ledger s]
  have hm1_full_ledger (s : Species) :
      p.mixture1.amount s =
        (((freshFeedObservation p.x p.y).stream.amount s +
            p.reformingExtent * steamReforming.reaction.vector s) +
          airFeedObservation.stream.amount s) +
          p.oxidationExtent * partialOxidation.reaction.vector s := by
    calc
      p.mixture1.amount s =
          (p.reformerOutlet.amount s + p.air.amount s) +
            p.oxidationExtent * partialOxidation.reaction.vector s := hm1_ledger s
      _ = ((p.freshFeed.amount s +
            p.reformingExtent * steamReforming.reaction.vector s) +
          p.air.amount s) +
          p.oxidationExtent * partialOxidation.reaction.vector s := by
            rw [href_ledger s]
      _ = (((freshFeedObservation p.x p.y).stream.amount s +
            p.reformingExtent * steamReforming.reaction.vector s) +
          airFeedObservation.stream.amount s) +
          p.oxidationExtent * partialOxidation.reaction.vector s := by
            rw [p.freshFeed_source, p.air_source]
  have hshift_input_ledger (s : Species) :
      p.shiftInput.amount s = p.mixture1.amount s + p.shiftWater.amount s :=
    congrArg (fun q : GasStream => q.amount s) hshift_mix
  have hshifted_ledger (s : Species) :
      p.shiftedOutlet.amount s =
        (p.mixture1.amount s + p.shiftWater.amount s) +
          p.shiftExtent * waterGasShift.reaction.vector s := by
    calc
      p.shiftedOutlet.amount s = p.shiftInput.amount s +
          p.shiftExtent * waterGasShift.reaction.vector s :=
        congrArg (fun q : GasStream => q.amount s) hshift_stage
      _ = (p.mixture1.amount s + p.shiftWater.amount s) +
          p.shiftExtent * waterGasShift.reaction.vector s := by
        rw [hshift_input_ledger s]
  have hreformer_listing (s : Species) :
      0 < p.reformerOutlet.amount s ↔
        s ∈ reformerOutletListing.species := by
    rw [← p.reformerOutlet_label.2]
    simp [speciesPresent]
  have hshifted_listing (s : Species) :
      0 < p.shiftedOutlet.amount s ↔
        s ∈ shiftedOutletListing.species := by
    rw [← p.shiftedOutlet_label.2]
    simp [speciesPresent]
  have hreformer_water_zero : p.reformerOutlet.amount .water = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hpositive
      have := (hreformer_listing .water).1 hpositive
      simpa [reformerOutletListing] using this
    · exact p.reformerOutlet_label.1 .water
  have hshifted_methane_zero : p.shiftedOutlet.amount .methane = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hpositive
      have := (hshifted_listing .methane).1 hpositive
      simpa [shiftedOutletListing] using this
    · exact p.shiftedOutlet_label.1 .methane
  have hshifted_oxygen_zero : p.shiftedOutlet.amount .oxygen = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hpositive
      have := (hshifted_listing .oxygen).1 hpositive
      simpa [shiftedOutletListing] using this
    · exact p.shiftedOutlet_label.1 .oxygen
  have hmethane_ledger := hshifted_ledger .methane
  have hoxygen_ledger := hshifted_ledger .oxygen
  rw [p.shiftWater_source] at hmethane_ledger hoxygen_ledger
  norm_num [shiftWaterObservation, waterGasShift, CRNT.Reaction.vector] at hmethane_ledger hoxygen_ledger
  have hmethane_zero : p.mixture1.amount .methane = 0 := by
    linarith
  have hoxygen_zero : p.mixture1.amount .oxygen = 0 := by
    linarith
  have hwater_ledger := hm1_ledger .water
  rw [p.air_source] at hwater_ledger
  norm_num [airFeedObservation, partialOxidation, CRNT.Reaction.vector] at hwater_ledger
  have hwater_zero : p.mixture1.amount .water = 0 := by
    linarith
  have hnitrogen_ledger := hm1_full_ledger .nitrogen
  have hcarbonMonoxide_ledger := hm1_full_ledger .carbonMonoxide
  have hhydrogen_ledger := hm1_full_ledger .hydrogen
  have hcarbonDioxide_ledger := hm1_full_ledger .carbonDioxide
  have hammonia_ledger := hm1_full_ledger .ammonia
  norm_num [freshFeedObservation, airFeedObservation, steamReforming,
    partialOxidation, CRNT.Reaction.vector] at hnitrogen_ledger hcarbonMonoxide_ledger hhydrogen_ledger hcarbonDioxide_ledger hammonia_ledger
  have hnitrogen_positive : 0 < p.mixture1.amount .nitrogen := by
    linarith
  have hcarbonMonoxide_positive :
      0 < p.mixture1.amount .carbonMonoxide := by
    linarith [p.reforming_quantitative.2.1,
      p.oxidation_quantitative.2.1]
  have hhydrogen_positive : 0 < p.mixture1.amount .hydrogen := by
    linarith [p.reforming_quantitative.2.1,
      p.oxidation_quantitative.2.1]
  have hcarbonDioxide_zero : p.mixture1.amount .carbonDioxide = 0 := by
    linarith
  have hammonia_zero : p.mixture1.amount .ammonia = 0 := by
    linarith
  apply Finset.ext
  intro s
  simp only [speciesPresent, Finset.mem_filter, Finset.mem_univ, true_and]
  cases s <;>
    simp [gasesM1Output, hmethane_zero, hwater_zero,
      hcarbonMonoxide_positive, hhydrogen_positive, hnitrogen_positive,
      hoxygen_zero, hcarbonDioxide_zero, hammonia_zero]

/-- Requested output `gases_m2`: the cooler input contains its complete
N₂/H₂ recycle together with its complete NH₃ product stream. -/
theorem gases_m2 (p : PlantModel) :
    speciesPresent p.mixture2 = gasesM2Output := by
  classical
  rcases p.cooler_split with ⟨_, hrecycle_nonnegative,
    hproduct_nonnegative, hcomponent⟩
  apply Finset.ext
  intro s
  simp only [speciesPresent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hcomponent s]
  have hrecycle :
      0 < p.recycle.amount s ↔ s ∈ recycleListing.species := by
    rw [← p.recycle_label.2]
    simp [speciesPresent]
  have hproduct :
      0 < p.ammoniaProduct.amount s ↔
        s ∈ ammoniaProductListing.species := by
    rw [← p.ammoniaProduct_label.2]
    simp [speciesPresent]
  have hr0 := hrecycle_nonnegative s
  have hp0 := hproduct_nonnegative s
  cases s <;>
    simp [recycleListing, ammoniaProductListing] at hrecycle hproduct <;>
    simp [gasesM2Output] <;>
    linarith

/-- Requested output `xy_relation`: the reformer outlet contains CH₄ but no
H₂O, so quantitative 1:1 reforming forces `x > y`. -/
theorem xy_relation (p : PlantModel) :
    XYRelation.Holds xyRelationOutput p.x p.y := by
  classical
  have hlisting (s : Species) :
      0 < p.reformerOutlet.amount s ↔
        s ∈ reformerOutletListing.species := by
    rw [← p.reformerOutlet_label.2]
    simp [speciesPresent]
  have hmethane_positive : 0 < p.reformerOutlet.amount .methane := by
    apply (hlisting .methane).2
    simp [reformerOutletListing]
  have hwater_not_positive : ¬ 0 < p.reformerOutlet.amount .water := by
    intro hwater
    have := (hlisting .water).1 hwater
    simpa [reformerOutletListing] using this
  have hwater_zero : p.reformerOutlet.amount .water = 0 :=
    le_antisymm (le_of_not_gt hwater_not_positive)
      (p.reformerOutlet_label.1 .water)
  have hstage := p.reforming_quantitative.1.2.2.2
  have hmethane_ledger :=
    congrArg (fun q : GasStream => q.amount .methane) hstage
  have hwater_ledger :=
    congrArg (fun q : GasStream => q.amount .water) hstage
  change (p.reformerOutlet.amount .methane =
    p.freshFeed.amount .methane +
      p.reformingExtent * steamReforming.reaction.vector .methane) at hmethane_ledger
  change (p.reformerOutlet.amount .water =
    p.freshFeed.amount .water +
      p.reformingExtent * steamReforming.reaction.vector .water) at hwater_ledger
  rw [p.freshFeed_source] at hmethane_ledger hwater_ledger
  norm_num [freshFeedObservation, steamReforming, CRNT.Reaction.vector] at hmethane_ledger hwater_ledger
  change p.y < p.x
  linarith

/-- Problem-specific semantic carrier for requested output `gases_m1`. -/
def GasesM1Result : Prop :=
  ∀ p : PlantModel, speciesPresent p.mixture1 = gasesM1Output

/-- Problem-specific semantic carrier for requested output `gases_m2`. -/
def GasesM2Result : Prop :=
  ∀ p : PlantModel, speciesPresent p.mixture2 = gasesM2Output

/-- Problem-specific semantic carrier for requested output `xy_relation`. -/
def XYRelationResult : Prop :=
  ∀ p : PlantModel, XYRelation.Holds xyRelationOutput p.x p.y

/-- Raw exact-symbolic result.  Nonemptiness rules out vacuous universal
conclusions; the remaining conjuncts follow source-request order. -/
def RawResult : Prop :=
  Nonempty PlantModel ∧ GasesM1Result ∧ GasesM2Result ∧ XYRelationResult

/-- No rounding applies, so reporting preserves the same three semantic
claims in the same order. -/
def ReportedResult : Prop :=
  Nonempty PlantModel ∧ GasesM1Result ∧ GasesM2Result ∧ XYRelationResult

theorem rawResult_semantics : RawResult := by
  exact ⟨plantModel_nonempty, gases_m1, gases_m2, xy_relation⟩

theorem reportedResult_semantics : ReportedResult := by
  exact rawResult_semantics

/-- Payload-bound raw-result contract.  The digest is regenerated from the
answer-blind candidate whenever its semantics change. -/
theorem rawResultContract :
    ("eb8a80affb94095bc94df8458e6d57a237ed8b4b99811abf93f9f3f0d4025caf" : String) =
        "eb8a80affb94095bc94df8458e6d57a237ed8b4b99811abf93f9f3f0d4025caf" ∧
      RawResult := by
  exact ⟨rfl, rawResult_semantics⟩

/-- Payload-bound reported-result contract. -/
theorem reportedResultContract :
    ("f429048da30669866fc00d722a2a1736b04ffeccdc5eecbb502e0199b895774f" : String) =
        "f429048da30669866fc00d722a2a1736b04ffeccdc5eecbb502e0199b895774f" ∧
      ReportedResult := by
  exact ⟨rfl, reportedResult_semantics⟩

end ProblemIcho2026T7A1
end IChO2026Problems
