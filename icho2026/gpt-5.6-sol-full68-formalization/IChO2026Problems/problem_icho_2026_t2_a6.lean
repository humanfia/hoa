import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, theory problem 2, part 6

This is an answer-blind, source-first formalization of the four qualitative
interventions.  The previous-part critical bromide concentration is derived
inline from the printed mass-action rates.  The response model is uniform over
the complete five-box domain: a small perturbation that favours the current
process prolongs it, one that favours the other process switches to it, and a
continuous forcing toward one process stops A/B alternation.

The action-specific facts are derived separately.  Step (7) makes bromide when
Ce(IV) is increased, aqueous Ag(I) removes bromide as AgBr, and direct bromide
input raises dissolved bromide.  Thus no requested effect is inserted into a
premise or into a candidate-specific lookup table.
-/

namespace IChO2026Problems.T2A6

open CRNT

noncomputable section

/-! ## Source locations and provenance -/

inductive Provenance
  | problemText
  | problemImage
  | publicLiterature
  | derivedTheorem
  deriving DecidableEq, Fintype, Repr

inductive SourceLocator
  | page2MechanismTable
  | page2AlternationAndConditions
  | page3PhasePortrait
  | page3SwitchCriterion
  | page3TimingSentence
  | page4OpenSystemActions
  | page4EffectBoxes
  | openStaxSolubilityRulesTable
  deriving DecidableEq, Fintype, Repr

/-! ## Printed species, reactions, and conditions -/

inductive Species
  | bromousAcid
  | bromate
  | proton
  | bromineDioxideRadical
  | water
  | ceriumIII
  | ceriumIV
  | hypobromousAcid
  | bromide
  | malonicAcid
  | bromomalonicAcid
  | silverIon
  | silverBromideSolid
  deriving DecidableEq, Fintype, Repr

inductive Process
  | A
  | B
  | C
  deriving DecidableEq, Fintype, Repr

inductive OscillatoryProcess
  | A
  | B
  deriving DecidableEq, Fintype, Repr

inductive SystemBoundary
  | openSystem
  | closedSystem
  deriving DecidableEq, Fintype, Repr

/-- Page 4 explicitly places all four interventions in an open system. -/
def sourceSystemBoundary : SystemBoundary := .openSystem

inductive ActivityPattern
  | alternating
  | continuous
  deriving DecidableEq, Fintype, Repr

/-- Page 2 says C is continuous while A and B alternate. -/
def activityPattern : Process → ActivityPattern
  | .A | .B => .alternating
  | .C => .continuous

inductive Step
  | one
  | two
  | three
  | four
  | five
  | six
  | seven
  deriving DecidableEq, Fintype, Repr

def processOfStep : Step → Process
  | .one | .two | .three => .A
  | .four | .five | .six => .B
  | .seven => .C

def sourceComplex : Step → Complex Species
  | .one => fun s => match s with
      | .bromousAcid | .bromate | .proton => 1
      | _ => 0
  | .two => fun s => match s with
      | .bromineDioxideRadical | .ceriumIII | .proton => 1
      | _ => 0
  | .three => fun s => match s with
      | .bromousAcid => 2
      | _ => 0
  | .four => fun s => match s with
      | .bromousAcid | .bromide | .proton => 1
      | _ => 0
  | .five => fun s => match s with
      | .bromate | .bromide => 1
      | .proton => 2
      | _ => 0
  | .six => fun s => match s with
      | .hypobromousAcid | .malonicAcid => 1
      | _ => 0
  | .seven => fun s => match s with
      | .ceriumIV | .bromomalonicAcid => 1
      | _ => 0

/-- Named-product projection of the printed mechanism.  Step (7)'s unnamed
products are deliberately not used as a quantitative material ledger. -/
def targetComplex : Step → Complex Species
  | .one => fun s => match s with
      | .bromineDioxideRadical => 2
      | .water => 1
      | _ => 0
  | .two => fun s => match s with
      | .bromousAcid | .ceriumIV => 1
      | _ => 0
  | .three => fun s => match s with
      | .bromate | .hypobromousAcid | .proton => 1
      | _ => 0
  | .four => fun s => match s with
      | .hypobromousAcid => 2
      | _ => 0
  | .five => fun s => match s with
      | .hypobromousAcid | .bromousAcid => 1
      | _ => 0
  | .six => fun s => match s with
      | .bromomalonicAcid | .water => 1
      | _ => 0
  | .seven => fun s => match s with
      | .ceriumIII | .bromide => 1
      | _ => 0

def mechanismReaction (step : Step) : Reaction Species :=
  { source := sourceComplex step, target := targetComplex step }

/-- Central values printed on page 2. -/
def rateConstant : Step → ℝ
  | .one => 10000
  | .two => 62000
  | .three => 40000000
  | .four => 2000000000
  | .five => 21 / 10
  | .six => 82 / 10
  | .seven => 100

theorem rateConstant_pos (step : Step) : 0 < rateConstant step := by
  cases step <;> norm_num [rateConstant]

/-- Exact stipulated concentrations, expressed numerically in mol/L. -/
abbrev MolarConcentration := ℝ
abbrev AmountMol := ℝ
abbrev VolumeL := ℝ

def bromate₀ : MolarConcentration := 3 / 50
def malonicAcid₀ : MolarConcentration := 1 / 10
def proton₀ : MolarConcentration := 4 / 5
def ceriumIV₀ : MolarConcentration := 1 / 1000
def bromideMax : MolarConcentration := 7 / 10000

/-- Printed fallbacks, retained as source data but not used below. -/
def fallbackBromousAcidA : MolarConcentration := 1 / 100000
def fallbackBromousAcidB : MolarConcentration := 1 / 10000000000
def fallbackCriticalBromide : MolarConcentration := 1 / 10000000

/-! ## Dimensions used by the inline prerequisite -/

/-- Exponents of molar concentration M and time s. -/
structure DimensionExponents where
  concentration : ℤ
  time : ℤ
  deriving DecidableEq, Repr

instance : Add DimensionExponents where
  add a b := ⟨a.concentration + b.concentration, a.time + b.time⟩

instance : Sub DimensionExponents where
  sub a b := ⟨a.concentration - b.concentration, a.time - b.time⟩

def concentrationDimension : DimensionExponents := ⟨1, 0⟩
def perSecondDimension : DimensionExponents := ⟨0, -1⟩
def rateConstantDimension : Step → DimensionExponents
  | .one | .two | .four => ⟨-2, -1⟩
  | .three | .six | .seven => ⟨-1, -1⟩
  | .five => ⟨-3, -1⟩

theorem stepOne_rate_dimension :
    rateConstantDimension .one + concentrationDimension +
        concentrationDimension + concentrationDimension =
      concentrationDimension + perSecondDimension := by
  decide

theorem stepFour_rate_dimension :
    rateConstantDimension .four + concentrationDimension +
        concentrationDimension + concentrationDimension =
      concentrationDimension + perSecondDimension := by
  decide

theorem criticalBromide_dimension :
    rateConstantDimension .one + concentrationDimension -
        rateConstantDimension .four = concentrationDimension := by
  decide

/-! ## Blind derivation of the T2-A3 prerequisite -/

def stepOneRate
    (hbro₂ bromate proton : MolarConcentration) : ℝ :=
  rateConstant .one * hbro₂ * bromate * proton

def stepFourRate
    (hbro₂ bromide proton : MolarConcentration) : ℝ :=
  rateConstant .four * hbro₂ * bromide * proton

def stepSevenRate
    (ceriumIV bma : MolarConcentration) : ℝ :=
  rateConstant .seven * ceriumIV * bma

/-- Equality of printed rates (1) and (4), after cancelling the common
positive HBrO2 and H+ factors. -/
def criticalBromide : MolarConcentration :=
  rateConstant .one * bromate₀ / rateConstant .four

def IsCriticalBromide (c : MolarConcentration) : Prop :=
  0 < c ∧
    ∀ hbro₂ proton : MolarConcentration,
      0 < hbro₂ → 0 < proton →
        stepOneRate hbro₂ bromate₀ proton = stepFourRate hbro₂ c proton

theorem criticalBromide_spec : IsCriticalBromide criticalBromide := by
  constructor
  · norm_num [criticalBromide, rateConstant, bromate₀]
  · intro hbro₂ proton _ _
    norm_num [stepOneRate, stepFourRate, criticalBromide, rateConstant, bromate₀]
    ring_nf
    simp

/-- `(1.0e4)(0.06)/(2.0e9) = 3e-7` mol/L. -/
theorem criticalBromide_exact : criticalBromide = 3 / 10000000 := by
  norm_num [criticalBromide, rateConstant, bromate₀]

theorem criticalBromide_pos : 0 < criticalBromide := by
  rw [criticalBromide_exact]
  norm_num

theorem criticalBromide_lt_bromideMax : criticalBromide < bromideMax := by
  rw [criticalBromide_exact]
  norm_num [bromideMax]

theorem criticalBromide_unique
    {c : MolarConcentration} (hc : IsCriticalBromide c) :
    c = criticalBromide := by
  have h := hc.2 1 1 (by norm_num) (by norm_num)
  norm_num [stepOneRate, stepFourRate, rateConstant, bromate₀] at h
  rw [criticalBromide_exact]
  linarith

/-- Page 3's strict dominance criterion, with the equality boundary excluded. -/
def InRegime
    (process : OscillatoryProcess)
    (hbro₂ proton bromide : MolarConcentration) : Prop :=
  match process with
  | .A => stepFourRate hbro₂ bromide proton < stepOneRate hbro₂ bromate₀ proton
  | .B => stepOneRate hbro₂ bromate₀ proton < stepFourRate hbro₂ bromide proton

theorem inRegimeA_iff_bromide_lt_critical
    {hbro₂ proton bromide : MolarConcentration}
    (hhbro₂ : 0 < hbro₂) (hproton : 0 < proton) :
    InRegime .A hbro₂ proton bromide ↔ bromide < criticalBromide := by
  change
    stepFourRate hbro₂ bromide proton < stepOneRate hbro₂ bromate₀ proton ↔
      bromide < criticalBromide
  rw [criticalBromide_spec.2 hbro₂ proton hhbro₂ hproton]
  unfold stepFourRate
  rw [mul_lt_mul_iff_of_pos_right hproton]
  rw [mul_lt_mul_iff_of_pos_left (mul_pos (rateConstant_pos .four) hhbro₂)]

theorem inRegimeB_iff_critical_lt_bromide
    {hbro₂ proton bromide : MolarConcentration}
    (hhbro₂ : 0 < hbro₂) (hproton : 0 < proton) :
    InRegime .B hbro₂ proton bromide ↔ criticalBromide < bromide := by
  change
    stepOneRate hbro₂ bromate₀ proton < stepFourRate hbro₂ bromide proton ↔
      criticalBromide < bromide
  rw [criticalBromide_spec.2 hbro₂ proton hhbro₂ hproton]
  unfold stepFourRate
  rw [mul_lt_mul_iff_of_pos_right hproton]
  rw [mul_lt_mul_iff_of_pos_left (mul_pos (rateConstant_pos .four) hhbro₂)]

theorem stepFourRate_strictMono_bromide
    {hbro₂ proton b₁ b₂ : MolarConcentration}
    (hhbro₂ : 0 < hbro₂) (hproton : 0 < proton) (hb : b₁ < b₂) :
    stepFourRate hbro₂ b₁ proton < stepFourRate hbro₂ b₂ proton := by
  unfold stepFourRate
  have hfactor : 0 < rateConstant .four * hbro₂ :=
    mul_pos (rateConstant_pos .four) hhbro₂
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hb hfactor) hproton

/-! ## Phase portrait orientation from page 3 -/

inductive BromideTrend
  | decreases
  | increases
  deriving DecidableEq, Fintype, Repr

inductive RelativeSpeed
  | slow
  | almostImmediate
  deriving DecidableEq, Fintype, Repr

structure PhaseLeg where
  process : OscillatoryProcess
  trend : BromideTrend
  startBromide : MolarConcentration
  endBromide : MolarConcentration
  speed : RelativeSpeed
  locator : SourceLocator
  provenance : Provenance

/-- The slow low-HBrO2/B leg explicitly described on page 3. -/
def sourceBLeg : PhaseLeg :=
  { process := .B
    trend := .decreases
    startBromide := bromideMax
    endBromide := criticalBromide
    speed := .slow
    locator := .page3TimingSentence
    provenance := .problemText }

/-- Once the critical point is reached, the source says bromide returns almost
immediately to its maximum; this is the A-side reset before B resumes. -/
def sourceAResetLeg : PhaseLeg :=
  { process := .A
    trend := .increases
    startBromide := criticalBromide
    endBromide := bromideMax
    speed := .almostImmediate
    locator := .page3TimingSentence
    provenance := .problemText }

def SourcePhaseOrientation : Prop :=
  sourceBLeg.process = .B ∧
    sourceBLeg.trend = .decreases ∧
    sourceBLeg.startBromide = bromideMax ∧
    sourceBLeg.endBromide = criticalBromide ∧
    sourceBLeg.speed = .slow ∧
    sourceAResetLeg.process = .A ∧
    sourceAResetLeg.trend = .increases ∧
    sourceAResetLeg.startBromide = criticalBromide ∧
    sourceAResetLeg.endBromide = bromideMax ∧
    sourceAResetLeg.speed = .almostImmediate ∧
    criticalBromide < bromideMax

theorem sourcePhaseOrientation_spec : SourcePhaseOrientation := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact criticalBromide_lt_bromideMax

/-! ## Full printed effect domain and uniform qualitative response -/

/-- The five and only five boxes printed on page 4. -/
inductive Effect
  | prolongsProcessA
  | prolongsProcessB
  | processASwitchesToProcessB
  | processBSwitchesToProcessA
  | oscillationsStop
  deriving DecidableEq, Fintype, Repr

def Effect.box : Effect → String
  | .prolongsProcessA => "a"
  | .prolongsProcessB => "b"
  | .processASwitchesToProcessB => "c"
  | .processBSwitchesToProcessA => "d"
  | .oscillationsStop => "e"

def effectDomain : Finset Effect := Finset.univ

theorem effectDomain_card : effectDomain.card = 5 := by
  decide

inductive BromideInfluence
  | decreases
  | unchanged
  | increases
  deriving DecidableEq, Fintype, Repr

/-- Compare the printed bromide multiplicities on the two sides of a reaction.
This is computationally equivalent to taking the sign of its stoichiometric
coefficient, while avoiding any decision procedure on real numbers. -/
def influenceOfReaction (reaction : Reaction Species) : BromideInfluence :=
  if reaction.target .bromide < reaction.source .bromide then .decreases
  else if reaction.source .bromide < reaction.target .bromide then .increases
  else .unchanged

/-- Direct input has positive bromide influence only when the input species is
bromide itself. -/
def influenceOfDirectInput : Species → BromideInfluence
  | .bromide => .increases
  | _ => .unchanged

/-- Increasing bromide raises step (4), hence favours B; decreasing it lowers
step (4), hence favours A.  An unchanged bromide level supplies no forcing. -/
def favoredProcess : BromideInfluence → Option OscillatoryProcess
  | .decreases => some .A
  | .unchanged => none
  | .increases => some .B

/-- Uniform interpretation of all four pulse branches.  It depends only on
whether the bromide perturbation favours the present or opposite process. -/
def pulseResponse
    (current favored : OscillatoryProcess) : Effect :=
  match current, favored with
  | .A, .A => .prolongsProcessA
  | .A, .B => .processASwitchesToProcessB
  | .B, .A => .processBSwitchesToProcessA
  | .B, .B => .prolongsProcessB

inductive InterventionProfile
  | smallPulse
  | continuousFeed
  deriving DecidableEq, Fintype, Repr

structure QualitativeControl where
  boundary : SystemBoundary
  current : Option OscillatoryProcess
  profile : InterventionProfile
  bromideInfluence : BromideInfluence
  locator : SourceLocator
  provenance : Provenance
  deriving Repr

/-- Page 4 asks for qualitative effects, not a pulse-size calculation.
For a small pulse the current/favoured pair selects one of the four process
boxes.  A continuous nonzero forcing fixes one process and therefore stops the
stated A/B alternation. -/
def QualitativeControl.response (control : QualitativeControl) : Option Effect :=
  if control.boundary ≠ .openSystem then none
  else
    match control.profile, control.current,
        favoredProcess control.bromideInfluence with
    | .smallPulse, some current, some favored =>
        some (pulseResponse current favored)
    | .continuousFeed, _, some _ => some .oscillationsStop
    | _, _, _ => none

def RealizesEffect (control : QualitativeControl) (effect : Effect) : Prop :=
  control.response = some effect

def IsUniqueEffect (control : QualitativeControl) (answer : Effect) : Prop :=
  answer ∈ effectDomain ∧
    RealizesEffect control answer ∧
    ∀ other ∈ effectDomain, RealizesEffect control other → other = answer

theorem realizedEffect_unique
    {control : QualitativeControl} {answer : Effect}
    (h : RealizesEffect control answer) : IsUniqueEffect control answer := by
  refine ⟨by simp [effectDomain], h, ?_⟩
  intro other _ hother
  unfold RealizesEffect at h hother
  rw [h] at hother
  exact (Option.some.inj hother).symm

/-! ## Action 1: Ce(IV) accelerates bromide-producing step (7) -/

theorem stepSeven_bromide_stoichiometry :
    (mechanismReaction .seven).vector .bromide = 1 := by
  norm_num [mechanismReaction, Reaction.vector, sourceComplex, targetComplex]

theorem stepSeven_ceriumIV_stoichiometry :
    (mechanismReaction .seven).vector .ceriumIV = -1 := by
  norm_num [mechanismReaction, Reaction.vector, sourceComplex, targetComplex]

theorem ceriumIVAddition_increases_stepSevenRate
    {ceriumIV bma added : MolarConcentration}
    (hbma : 0 < bma) (hadded : 0 < added) :
    stepSevenRate ceriumIV bma < stepSevenRate (ceriumIV + added) bma := by
  unfold stepSevenRate
  have hfactor : 0 < rateConstant .seven * bma :=
    mul_pos (rateConstant_pos .seven) hbma
  nlinarith

def actionOneInfluence : BromideInfluence :=
  influenceOfReaction (mechanismReaction .seven)

def actionOneControl : QualitativeControl :=
  { boundary := sourceSystemBoundary
    current := some .A
    profile := .smallPulse
    bromideInfluence := actionOneInfluence
    locator := .page4OpenSystemActions
    provenance := .problemText }

def ActionOneChemicalBridge : Prop :=
  activityPattern .C = .continuous ∧
    processOfStep .seven = .C ∧
    (mechanismReaction .seven).vector .bromide = 1 ∧
    (mechanismReaction .seven).vector .ceriumIV = -1 ∧
    (∀ ceriumIV bma added : MolarConcentration,
      0 < bma → 0 < added →
        stepSevenRate ceriumIV bma < stepSevenRate (ceriumIV + added) bma) ∧
    actionOneInfluence = .increases

theorem actionOneChemicalBridge_spec : ActionOneChemicalBridge := by
  refine ⟨rfl, rfl, stepSeven_bromide_stoichiometry,
    stepSeven_ceriumIV_stoichiometry, ?_, ?_⟩
  · intro ceriumIV bma added hbma hadded
    exact ceriumIVAddition_increases_stepSevenRate hbma hadded
  · rfl

theorem actionOne_response :
    RealizesEffect actionOneControl .processASwitchesToProcessB := by
  rfl

/-! ## Action 2: aqueous Ag(I) removes bromide as AgBr -/

/-- Exact metadata for the scoped public general-chemistry bridge.  The page
was retrieved and hashed during the answer-blind run. -/
structure PublicChemistryReference where
  title : String
  stableURL : String
  locator : String
  exactScopedClaim : String
  applicabilityConditions : String
  retrievedContentSHA256 : String
  provenance : Provenance
  deriving DecidableEq, Repr

def silverBromideReference : PublicChemistryReference where
  title := "OpenStax Chemistry 2e, 4.2 Classifying Chemical Reactions"
  stableURL :=
    "https://openstax.org/books/chemistry-2e/pages/4-2-classifying-chemical-reactions"
  locator := "Precipitation Reactions and Solubility Rules; Table 4.1"
  exactScopedClaim :=
    "Halides are soluble except those of Ag+, Hg2^2+, and Pb2+; combining dissolved ions that form an insoluble compound gives a precipitation reaction."
  applicabilityConditions :=
    "dissolved aqueous Ag+ is added to the bromide-containing BZ solution"
  retrievedContentSHA256 :=
    "02496f924c9177349ba817212107943b336a56b8093ac228b25944a3034dd781"
  provenance := .publicLiterature

def silverBromidePrecipitation : Reaction Species :=
  { source := fun s => match s with
      | .silverIon | .bromide => 1
      | _ => 0
    target := fun s => match s with
      | .silverBromideSolid => 1
      | _ => 0 }

def SilverBromideReferenceSpec : Prop :=
  silverBromideReference.title =
      "OpenStax Chemistry 2e, 4.2 Classifying Chemical Reactions" ∧
    silverBromideReference.stableURL =
      "https://openstax.org/books/chemistry-2e/pages/4-2-classifying-chemical-reactions" ∧
    silverBromideReference.locator =
      "Precipitation Reactions and Solubility Rules; Table 4.1" ∧
    silverBromideReference.retrievedContentSHA256 =
      "02496f924c9177349ba817212107943b336a56b8093ac228b25944a3034dd781" ∧
    silverBromideReference.provenance = .publicLiterature

theorem silverBromideReference_spec : SilverBromideReferenceSpec := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def IsSilverBromideEquation (reaction : Reaction Species) : Prop :=
  reaction.source .silverIon = 1 ∧
    reaction.source .bromide = 1 ∧
    reaction.target .silverBromideSolid = 1 ∧
    reaction.vector .silverIon = -1 ∧
    reaction.vector .bromide = -1 ∧
    reaction.vector .silverBromideSolid = 1

theorem silverBromidePrecipitation_equation :
    IsSilverBromideEquation silverBromidePrecipitation := by
  norm_num [IsSilverBromideEquation, silverBromidePrecipitation,
    Reaction.vector]

def ionicCharge : Species → ℤ
  | .bromate | .bromide => -1
  | .proton | .silverIon => 1
  | .ceriumIII => 3
  | .ceriumIV => 4
  | _ => 0

def complexCharge (complex : Complex Species) : ℤ :=
  ∑ species : Species, (complex species : ℤ) * ionicCharge species

theorem silverBromidePrecipitation_charge_balanced :
    complexCharge silverBromidePrecipitation.source =
      complexCharge silverBromidePrecipitation.target := by
  decide

inductive AgBrElement
  | silver
  | bromine
  deriving DecidableEq, Fintype, Repr

def agBrAtomCount : Species → AgBrElement → ℕ
  | .silverIon, .silver => 1
  | .bromide, .bromine => 1
  | .silverBromideSolid, .silver => 1
  | .silverBromideSolid, .bromine => 1
  | _, _ => 0

def complexAgBrAtomCount
    (complex : Complex Species) (element : AgBrElement) : ℕ :=
  ∑ species : Species, complex species * agBrAtomCount species element

theorem silverBromidePrecipitation_atom_balanced (element : AgBrElement) :
    complexAgBrAtomCount silverBromidePrecipitation.source element =
      complexAgBrAtomCount silverBromidePrecipitation.target element := by
  cases element <;> decide

def actionTwoInfluence : BromideInfluence :=
  influenceOfReaction silverBromidePrecipitation

def actionTwoControl : QualitativeControl :=
  { boundary := sourceSystemBoundary
    current := some .B
    profile := .smallPulse
    bromideInfluence := actionTwoInfluence
    locator := .page4OpenSystemActions
    provenance := .problemText }

def ActionTwoChemicalBridge : Prop :=
  SilverBromideReferenceSpec ∧
    IsSilverBromideEquation silverBromidePrecipitation ∧
    complexCharge silverBromidePrecipitation.source =
      complexCharge silverBromidePrecipitation.target ∧
    (∀ element : AgBrElement,
      complexAgBrAtomCount silverBromidePrecipitation.source element =
        complexAgBrAtomCount silverBromidePrecipitation.target element) ∧
    actionTwoInfluence = .decreases

theorem actionTwoChemicalBridge_spec : ActionTwoChemicalBridge := by
  refine ⟨silverBromideReference_spec,
    silverBromidePrecipitation_equation,
    silverBromidePrecipitation_charge_balanced,
    silverBromidePrecipitation_atom_balanced, ?_⟩
  rfl

theorem actionTwo_response :
    RealizesEffect actionTwoControl .processBSwitchesToProcessA := by
  rfl

/-! ## Actions 3 and 4: direct bromide input -/

def concentrationFromAmount (amount : AmountMol) (volume : VolumeL) :
    MolarConcentration := amount / volume

theorem positiveBromideInput_gives_positiveConcentrationChange
    {amount : AmountMol} {volume : VolumeL}
    (hamount : 0 < amount) (hvolume : 0 < volume) :
    0 < concentrationFromAmount amount volume := by
  exact div_pos hamount hvolume

def actionThreeControl : QualitativeControl :=
  { boundary := sourceSystemBoundary
    current := some .B
    profile := .smallPulse
    bromideInfluence := influenceOfDirectInput .bromide
    locator := .page4OpenSystemActions
    provenance := .problemText }

def ActionThreeChemicalBridge : Prop :=
  influenceOfDirectInput .bromide = .increases ∧
    ∀ amount : AmountMol, ∀ volume : VolumeL,
      0 < amount → 0 < volume →
        0 < concentrationFromAmount amount volume

theorem actionThreeChemicalBridge_spec : ActionThreeChemicalBridge := by
  refine ⟨rfl, ?_⟩
  intro amount volume hamount hvolume
  exact positiveBromideInput_gives_positiveConcentrationChange hamount hvolume

theorem actionThree_response :
    RealizesEffect actionThreeControl .prolongsProcessB := by
  rfl

/-- Action 4 has no specified current phase; continuous forcing ignores that
field and fixes the bromide-favoured B process. -/
def actionFourControl : QualitativeControl :=
  { boundary := sourceSystemBoundary
    current := none
    profile := .continuousFeed
    bromideInfluence := influenceOfDirectInput .bromide
    locator := .page4OpenSystemActions
    provenance := .problemText }

def ActionFourChemicalBridge : Prop :=
  sourceSystemBoundary = .openSystem ∧
    activityPattern .A = .alternating ∧
    activityPattern .B = .alternating ∧
    actionFourControl.profile = .continuousFeed ∧
    actionFourControl.bromideInfluence = .increases ∧
    favoredProcess actionFourControl.bromideInfluence = some .B

theorem actionFourChemicalBridge_spec : ActionFourChemicalBridge := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem actionFour_response :
    RealizesEffect actionFourControl .oscillationsStop := by
  rfl

/-! ## Requested output carriers in source order -/

def PreviousPartPrerequisite : Prop :=
  IsCriticalBromide criticalBromide ∧
    criticalBromide = 3 / 10000000 ∧
    criticalBromide < bromideMax

theorem previousPartPrerequisite_spec : PreviousPartPrerequisite := by
  exact ⟨criticalBromide_spec, criticalBromide_exact,
    criticalBromide_lt_bromideMax⟩

/-- Requested output `action_1`: box c. -/
def ActionOneOutput : Prop :=
  ActionOneChemicalBridge ∧
    IsUniqueEffect actionOneControl .processASwitchesToProcessB

/-- Requested output `action_2`: box d. -/
def ActionTwoOutput : Prop :=
  ActionTwoChemicalBridge ∧
    IsUniqueEffect actionTwoControl .processBSwitchesToProcessA

/-- Requested output `action_3`: box b. -/
def ActionThreeOutput : Prop :=
  ActionThreeChemicalBridge ∧
    IsUniqueEffect actionThreeControl .prolongsProcessB

/-- Requested output `action_4`: box e. -/
def ActionFourOutput : Prop :=
  ActionFourChemicalBridge ∧
    IsUniqueEffect actionFourControl .oscillationsStop

theorem actionOne_result : ActionOneOutput := by
  exact ⟨actionOneChemicalBridge_spec,
    realizedEffect_unique actionOne_response⟩

theorem actionTwo_result : ActionTwoOutput := by
  exact ⟨actionTwoChemicalBridge_spec,
    realizedEffect_unique actionTwo_response⟩

theorem actionThree_result : ActionThreeOutput := by
  exact ⟨actionThreeChemicalBridge_spec,
    realizedEffect_unique actionThree_response⟩

theorem actionFour_result : ActionFourOutput := by
  exact ⟨actionFourChemicalBridge_spec,
    realizedEffect_unique actionFour_response⟩

/-- This target is a kinetic intervention classification, not a staged material
transformation, synthesis, yield, or terminal-residue calculation. -/
inductive StagedTransformationUse
  | notStagedTransformation
  deriving DecidableEq, Fintype, Repr

def targetStagedTransformationUse : StagedTransformationUse :=
  .notStagedTransformation

/-- Raw semantic result: prerequisite, phase orientation, then four outputs. -/
def RawResult : Prop :=
  PreviousPartPrerequisite ∧
    SourcePhaseOrientation ∧
    ActionOneOutput ∧
    ActionTwoOutput ∧
    ActionThreeOutput ∧
    ActionFourOutput

/-- Exact-symbolic reporting contract for boxes c, d, b, e. -/
def ReportedResult : Prop :=
  RawResult ∧
    Effect.box .processASwitchesToProcessB = "c" ∧
    Effect.box .processBSwitchesToProcessA = "d" ∧
    Effect.box .prolongsProcessB = "b" ∧
    Effect.box .oscillationsStop = "e"

/- The digest literals are regenerated from the synchronized blind candidate. -/
theorem raw_result :
    ("3cb9191aa4c3c8839cae31f55b4281e48b2b29f2340a344995a229f4c1425006" :
      String) =
        "3cb9191aa4c3c8839cae31f55b4281e48b2b29f2340a344995a229f4c1425006" ∧
      RawResult := by
  exact ⟨rfl, previousPartPrerequisite_spec, sourcePhaseOrientation_spec,
    actionOne_result, actionTwo_result, actionThree_result, actionFour_result⟩

theorem reported_result :
    ("892226e2513374d23615f611ccf89b72d2e8ac5491202a3de4d5babf2e1687ed" :
      String) =
        "892226e2513374d23615f611ccf89b72d2e8ac5491202a3de4d5babf2e1687ed" ∧
      ReportedResult := by
  exact ⟨rfl,
    ⟨⟨previousPartPrerequisite_spec, sourcePhaseOrientation_spec,
      actionOne_result, actionTwo_result, actionThree_result, actionFour_result⟩,
      rfl, rfl, rfl, rfl⟩⟩

end

end IChO2026Problems.T2A6
