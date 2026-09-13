import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T8, part A8

This file formalizes the controller-bound, assumption-augmented T8-A8 task.
The original pages do not state a wavelength-resolved selectivity law. The
single additional premise is therefore kept as the explicitly named theorem
hypothesis `t8_a8_finite_led_hydrogen_share_order_user_axiom`; it says only
that, for the three LEDs in this experiment, a larger photon energy implies a
larger H₂ mole fraction.

The classification theorem ranges over every source-compatible experiment
model. In particular, no bar-to-condition assignment is a premise. The page-4
data are represented by actual real-valued mole percentages, the dark control
follows from a transparent zero-light photocatalytic gate, and the
red/green/blue photon-energy order is derived from positive wavelengths and
the ordinary visible-colour wavelength order. The four requested outputs are
stated in the same bar-to-condition direction as the question.
-/

namespace IChO2026Problems.T8A8

noncomputable section

/-! ## Source and supplement provenance -/

inductive EvidenceOrigin where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | explicitUserSupplement
  | derivedTheorem
  deriving DecidableEq, Repr

structure SourceLocator where
  path : String
  sha256 : String
  region : String
  origin : EvidenceOrigin
  deriving DecidableEq, Repr

def page3GibbsLocator : SourceLocator where
  path := "icho_2026_source/image/T8_page-3.png"
  sha256 :=
    "d6431350f32953011648ffe537d8d51ed7dc9dfb5a437a6f1c94620d6041055f"
  region := "lower Gibbs-energy diagram for the two competing reductions"
  origin := .problemImage

def page4CompositionLocator : SourceLocator where
  path := "icho_2026_source/image/T8_page-4.png"
  sha256 :=
    "55fc19db05fe771eb0403d5fcf611d83ff5a22882b1221129ef689bd8704285a"
  region := "N/R/G/B paragraph, bars a-d, axes, and H2/CO legend"
  origin := .problemImage

def BoundImageProvenance : Prop :=
  page3GibbsLocator.path = "icho_2026_source/image/T8_page-3.png" ∧
  page3GibbsLocator.sha256 =
    "d6431350f32953011648ffe537d8d51ed7dc9dfb5a437a6f1c94620d6041055f" ∧
  page3GibbsLocator.origin = .problemImage ∧
  page4CompositionLocator.path = "icho_2026_source/image/T8_page-4.png" ∧
  page4CompositionLocator.sha256 =
    "55fc19db05fe771eb0403d5fcf611d83ff5a22882b1221129ef689bd8704285a" ∧
  page4CompositionLocator.origin = .problemImage

theorem boundImageProvenance : BoundImageProvenance := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

structure SupplementalAssumption where
  assumptionId : String
  recordPath : String
  recordSha256 : String
  sourceBundleSha256 : String
  sourceRecordSha256 : String
  evaluationBasis : String
  originalProblemUnchanged : Bool
  finiteScope : String
  leanRepresentation : String
  relation : String
  deriving DecidableEq, Repr

def finiteLedHydrogenShareOrderSupplement : SupplementalAssumption where
  assumptionId := "t8_a8_finite_led_hydrogen_share_order_user_axiom"
  recordPath := ".archon/user_input_assumptions/icho_2026_t8_a8.json"
  recordSha256 :=
    "6096df7a40e64828945c594c34ff652835d58296f6aeba16b46b6807b380edc1"
  sourceBundleSha256 :=
    "865b4417565ec94097e4287aa7746ee08fb527c80f72b7c15378fa0db9fd8ddc"
  sourceRecordSha256 :=
    "aa35a9fbcee09e5ffaa9a3991eccaa4443a7fbbc5a034ec9088012d26f0e9e6e"
  evaluationBasis := "user_assumption_augmented"
  originalProblemUnchanged := true
  finiteScope := "only red, green, and blue LED conditions in T8-A8"
  leanRepresentation :=
    "explicit hypothesis of a universally quantified conditional theorem"
  relation :=
    "for LEDs u,v in this experiment, E_photon(u)<E_photon(v) implies chi_H2(u)<chi_H2(v)"

def UserSupplementProvenance : Prop :=
  finiteLedHydrogenShareOrderSupplement.assumptionId =
      "t8_a8_finite_led_hydrogen_share_order_user_axiom" ∧
  finiteLedHydrogenShareOrderSupplement.recordPath =
      ".archon/user_input_assumptions/icho_2026_t8_a8.json" ∧
  finiteLedHydrogenShareOrderSupplement.recordSha256 =
      "6096df7a40e64828945c594c34ff652835d58296f6aeba16b46b6807b380edc1" ∧
  finiteLedHydrogenShareOrderSupplement.sourceBundleSha256 =
      "865b4417565ec94097e4287aa7746ee08fb527c80f72b7c15378fa0db9fd8ddc" ∧
  finiteLedHydrogenShareOrderSupplement.sourceRecordSha256 =
      "aa35a9fbcee09e5ffaa9a3991eccaa4443a7fbbc5a034ec9088012d26f0e9e6e" ∧
  finiteLedHydrogenShareOrderSupplement.evaluationBasis =
      "user_assumption_augmented" ∧
  finiteLedHydrogenShareOrderSupplement.originalProblemUnchanged = true ∧
  finiteLedHydrogenShareOrderSupplement.finiteScope =
      "only red, green, and blue LED conditions in T8-A8" ∧
  finiteLedHydrogenShareOrderSupplement.leanRepresentation =
      "explicit hypothesis of a universally quantified conditional theorem" ∧
  finiteLedHydrogenShareOrderSupplement.relation =
      "for LEDs u,v in this experiment, E_photon(u)<E_photon(v) implies chi_H2(u)<chi_H2(v)"

theorem userSupplementProvenance : UserSupplementProvenance := by
  simp [UserSupplementProvenance, finiteLedHydrogenShareOrderSupplement]

/-! ## Complete finite domains named by the source -/

/-- The four conditions explicitly enumerated in the page-4 paragraph. -/
inductive IlluminationCondition where
  | noIrradiation
  | red
  | green
  | blue
  deriving DecidableEq, Repr

/-- The four anonymous bars explicitly printed on the page-4 horizontal axis. -/
inductive DiagramBar where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Repr

/-- The three illuminated conditions, with no dark-control constructor. -/
inductive LedColor where
  | red
  | green
  | blue
  deriving DecidableEq, Repr

def conditionOfLed : LedColor → IlluminationCondition
  | .red => .red
  | .green => .green
  | .blue => .blue

def conditionDomainOrigin : EvidenceOrigin := .problemText
def barDomainOrigin : EvidenceOrigin := .problemImage
def visibleColourOrderOrigin : EvidenceOrigin := .trustedGeneralLaw

def FiniteDomainProvenance : Prop :=
  conditionDomainOrigin = .problemText ∧
  barDomainOrigin = .problemImage ∧
  visibleColourOrderOrigin = .trustedGeneralLaw ∧
  (∀ condition : IlluminationCondition,
    condition = .noIrradiation ∨ condition = .red ∨
      condition = .green ∨ condition = .blue) ∧
  (∀ bar : DiagramBar,
    bar = .a ∨ bar = .b ∨ bar = .c ∨ bar = .d) ∧
  (∀ colour : LedColor,
    colour = .red ∨ colour = .green ∨ colour = .blue)

theorem finiteDomainProvenance : FiniteDomainProvenance := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro condition
    cases condition <;> simp
  · intro bar
    cases bar <;> simp
  · intro colour
    cases colour <;> simp

/-! ## Page-3 source readout and staged-transformation audit -/

inductive Species where
  | carbonDioxide
  | carbonMonoxide
  | proton
  | electron
  | hydrogen
  | water
  deriving DecidableEq, Repr

inductive GibbsEvent where
  | add (species : Species)
  | bind (species : Species)
  | release (species : Species)
  | addProtonReleaseWater
  deriving DecidableEq, Repr

structure GibbsStep where
  event : GibbsEvent
  deltaG_eV : ℚ
  deriving DecidableEq, Repr

def commonElectronStep : GibbsStep :=
  ⟨.add .electron, -(4 : ℚ) / 100⟩

def hydrogenBranchSteps : List GibbsStep :=
  [⟨.add .proton, (756 : ℚ) / 1000⟩,
   ⟨.add .electron, (1832 : ℚ) / 1000⟩,
   ⟨.add .proton, -(168 : ℚ) / 1000⟩,
   ⟨.release .hydrogen, -(114 : ℚ) / 100⟩]

def carbonMonoxideBranchSteps : List GibbsStep :=
  [⟨.bind .carbonDioxide, (2 : ℚ) / 100⟩,
   ⟨.add .electron, (16 : ℚ) / 100⟩,
   ⟨.add .proton, -(36 : ℚ) / 100⟩,
   ⟨.addProtonReleaseWater, -(22 : ℚ) / 100⟩,
   ⟨.release .carbonMonoxide, (1 : ℚ) / 10⟩]

/-- Exact signed eV labels, including the combined
`+H+; -H2O, -0.22 eV` event exactly as printed. -/
def Page3GibbsFigureReadout : Prop :=
  commonElectronStep.deltaG_eV = -(4 : ℚ) / 100 ∧
  hydrogenBranchSteps.map GibbsStep.deltaG_eV =
    [(756 : ℚ) / 1000, (1832 : ℚ) / 1000,
      -(168 : ℚ) / 1000, -(114 : ℚ) / 100] ∧
  carbonMonoxideBranchSteps.map GibbsStep.deltaG_eV =
    [(2 : ℚ) / 100, (16 : ℚ) / 100, -(36 : ℚ) / 100,
      -(22 : ℚ) / 100, (1 : ℚ) / 10] ∧
  hydrogenBranchSteps.map GibbsStep.event =
    [.add .proton, .add .electron, .add .proton, .release .hydrogen] ∧
  carbonMonoxideBranchSteps.map GibbsStep.event =
    [.bind .carbonDioxide, .add .electron, .add .proton,
      .addProtonReleaseWater, .release .carbonMonoxide]

theorem page3GibbsFigureReadout : Page3GibbsFigureReadout := by
  norm_num [Page3GibbsFigureReadout, commonElectronStep,
    hydrogenBranchSteps, carbonMonoxideBranchSteps]

def hydrogenHighIntermediate_eV : ℚ :=
  commonElectronStep.deltaG_eV + (756 : ℚ) / 1000 + (1832 : ℚ) / 1000

def carbonMonoxideHighIntermediate_eV : ℚ :=
  commonElectronStep.deltaG_eV + (2 : ℚ) / 100 + (16 : ℚ) / 100

def Page3IntermediateComparison : Prop :=
  hydrogenHighIntermediate_eV = (2548 : ℚ) / 1000 ∧
  carbonMonoxideHighIntermediate_eV = (14 : ℚ) / 100 ∧
  carbonMonoxideHighIntermediate_eV < hydrogenHighIntermediate_eV

theorem page3IntermediateComparison : Page3IntermediateComparison := by
  norm_num [Page3IntermediateComparison, hydrogenHighIntermediate_eV,
    carbonMonoxideHighIntermediate_eV, commonElectronStep,
    hydrogenBranchSteps, carbonMonoxideBranchSteps]

inductive TransformationDirection where
  | forward
  deriving DecidableEq, Repr

/-- The Gibbs paths are used only as source-named compatibility context. The
problem does not provide a complete protocol or a material-stage ledger here. -/
structure NamedTransformation where
  direction : TransformationDirection
  namedInputs : List Species
  namedOutputs : List Species
  depictedSteps : List GibbsStep
  source : SourceLocator
  protocolDetails : Option String
  netStoichiometricCoefficients : Option (List ℕ)
  phases : Option (List String)
  completeByproductSpecification : Option (List Species)
  completeMaterialStreamSpecification : Option (List Species)
  deriving DecidableEq, Repr

def hydrogenRoute : NamedTransformation where
  direction := .forward
  namedInputs := [.proton, .electron]
  namedOutputs := [.hydrogen]
  depictedSteps := commonElectronStep :: hydrogenBranchSteps
  source := page3GibbsLocator
  protocolDetails := none
  netStoichiometricCoefficients := none
  phases := none
  completeByproductSpecification := none
  completeMaterialStreamSpecification := none

def carbonMonoxideRoute : NamedTransformation where
  direction := .forward
  namedInputs := [.carbonDioxide, .proton, .electron]
  namedOutputs := [.carbonMonoxide, .water]
  depictedSteps := commonElectronStep :: carbonMonoxideBranchSteps
  source := page3GibbsLocator
  protocolDetails := none
  netStoichiometricCoefficients := none
  phases := none
  completeByproductSpecification := none
  completeMaterialStreamSpecification := none

def stagedTransformationClassification : String :=
  "qualitative_named_transform_only"

def QualitativeNamedTransformOnlyAudit : Prop :=
  stagedTransformationClassification = "qualitative_named_transform_only" ∧
  hydrogenRoute.direction = .forward ∧
  hydrogenRoute.namedInputs = [.proton, .electron] ∧
  hydrogenRoute.namedOutputs = [.hydrogen] ∧
  hydrogenRoute.source = page3GibbsLocator ∧
  carbonMonoxideRoute.direction = .forward ∧
  carbonMonoxideRoute.namedInputs = [.carbonDioxide, .proton, .electron] ∧
  carbonMonoxideRoute.namedOutputs = [.carbonMonoxide, .water] ∧
  carbonMonoxideRoute.source = page3GibbsLocator ∧
  hydrogenRoute.protocolDetails = none ∧
  hydrogenRoute.netStoichiometricCoefficients = none ∧
  hydrogenRoute.phases = none ∧
  hydrogenRoute.completeByproductSpecification = none ∧
  hydrogenRoute.completeMaterialStreamSpecification = none ∧
  carbonMonoxideRoute.protocolDetails = none ∧
  carbonMonoxideRoute.netStoichiometricCoefficients = none ∧
  carbonMonoxideRoute.phases = none ∧
  carbonMonoxideRoute.completeByproductSpecification = none ∧
  carbonMonoxideRoute.completeMaterialStreamSpecification = none

theorem qualitativeNamedTransformOnlyAudit :
    QualitativeNamedTransformOnlyAudit := by
  simp [QualitativeNamedTransformOnlyAudit, stagedTransformationClassification,
    hydrogenRoute, carbonMonoxideRoute]

/-! ## Page-4 source-first composition model -/

inductive HatchPattern where
  | blueDiagonal
  | redVertical
  deriving DecidableEq, Repr

def legendSpecies : HatchPattern → Species
  | .blueDiagonal => .hydrogen
  | .redVertical => .carbonMonoxide

def Page4LegendFacts : Prop :=
  legendSpecies .blueDiagonal = .hydrogen ∧
  legendSpecies .redVertical = .carbonMonoxide

theorem page4LegendFacts : Page4LegendFacts := by
  exact ⟨rfl, rfl⟩

structure ProductMolePercent where
  hydrogen : ℝ
  carbonMonoxide : ℝ

def totalMolePercent (composition : ProductMolePercent) : ℝ :=
  composition.hydrogen + composition.carbonMonoxide

/-- This relation records only robust facts visible in the page-4 plot. The
unlabelled internal boundaries are not assigned invented numerical values. -/
structure Page4CompositionFigure
    (composition : DiagramBar → ProductMolePercent) : Prop where
  physicalBounds : ∀ bar,
    0 ≤ (composition bar).hydrogen ∧
    (composition bar).hydrogen ≤ 100 ∧
    0 ≤ (composition bar).carbonMonoxide ∧
    (composition bar).carbonMonoxide ≤ 100
  aHydrogenZero : (composition .a).hydrogen = 0
  aCarbonMonoxideZero : (composition .a).carbonMonoxide = 0
  bTotal : totalMolePercent (composition .b) = 100
  cTotal : totalMolePercent (composition .c) = 100
  dTotal : totalMolePercent (composition .d) = 100
  dHydrogenPositive : 0 < (composition .d).hydrogen
  hydrogenOrderDC : (composition .d).hydrogen < (composition .c).hydrogen
  hydrogenOrderCB : (composition .c).hydrogen < (composition .b).hydrogen

theorem page4_unique_zero_total
    {composition : DiagramBar → ProductMolePercent}
    (figure : Page4CompositionFigure composition) (bar : DiagramBar) :
    totalMolePercent (composition bar) = 0 ↔ bar = .a := by
  cases bar
  · simp [totalMolePercent, figure.aHydrogenZero,
      figure.aCarbonMonoxideZero]
  · constructor
    · intro hzero
      linarith [figure.bTotal]
    · simp
  · constructor
    · intro hzero
      linarith [figure.cTotal]
    · simp
  · constructor
    · intro hzero
      linarith [figure.dTotal]
    · simp

/-! ## Ordinary photon physics and the dark photocatalytic control -/

/-- No representative wavelengths are selected. A model may use any positive
wavelengths satisfying the ordinary visible-colour order
`lambda_blue < lambda_green < lambda_red`. -/
structure VisibleLedOptics where
  energyScale : ℝ
  wavelength : LedColor → ℝ
  energyScalePositive : 0 < energyScale
  wavelengthPositive : ∀ colour, 0 < wavelength colour
  blueWavelengthShorterGreen : wavelength .blue < wavelength .green
  greenWavelengthShorterRed : wavelength .green < wavelength .red

def photonEnergy (optics : VisibleLedOptics) (colour : LedColor) : ℝ :=
  optics.energyScale / optics.wavelength colour

theorem photonEnergy_increases_when_wavelength_decreases
    (energyScale shortWavelength longWavelength : ℝ)
    (hScale : 0 < energyScale)
    (hShort : 0 < shortWavelength)
    (hOrder : shortWavelength < longWavelength) :
    energyScale / longWavelength < energyScale / shortWavelength := by
  rw [div_lt_div_iff₀ (lt_trans hShort hOrder) hShort]
  nlinarith

def VisiblePhotonEnergyOrder (optics : VisibleLedOptics) : Prop :=
  photonEnergy optics .red < photonEnergy optics .green ∧
  photonEnergy optics .green < photonEnergy optics .blue

theorem visiblePhotonEnergyOrder (optics : VisibleLedOptics) :
    VisiblePhotonEnergyOrder optics := by
  constructor
  · exact photonEnergy_increases_when_wavelength_decreases
      optics.energyScale (optics.wavelength .green) (optics.wavelength .red)
      optics.energyScalePositive (optics.wavelengthPositive .green)
      optics.greenWavelengthShorterRed
  · exact photonEnergy_increases_when_wavelength_decreases
      optics.energyScale (optics.wavelength .blue) (optics.wavelength .green)
      optics.energyScalePositive (optics.wavelengthPositive .blue)
      optics.blueWavelengthShorterGreen

/-- A dimensionless on/off factor used only to derive the zero-light result.
It is not a photon flux and supplies no numerical product yield. -/
def incidentLightGate : IlluminationCondition → ℝ
  | .noIrradiation => 0
  | .red => 1
  | .green => 1
  | .blue => 1

/-- A source-compatible model is formed before filtering from all equivalences
between the complete source condition and bar domains, all real composition
readouts, all positive ordered LED wavelengths, and all nonnegative response
amplitudes. The light-gate equation is the transparent ordinary meaning used
for the explicitly photocatalytic products: zero incident light multiplies any
response amplitude to zero. -/
structure ExperimentModel where
  assignment : IlluminationCondition ≃ DiagramBar
  composition : DiagramBar → ProductMolePercent
  compositionFigure : Page4CompositionFigure composition
  optics : VisibleLedOptics
  responseAmplitude : IlluminationCondition → ℝ
  responseAmplitudeNonnegative : ∀ condition, 0 ≤ responseAmplitude condition
  photocatalyticLightGate : ∀ condition,
    totalMolePercent (composition (assignment condition)) =
      incidentLightGate condition * responseAmplitude condition

def hydrogenMolePercentForCondition
    (model : ExperimentModel) (condition : IlluminationCondition) : ℝ :=
  (model.composition (model.assignment condition)).hydrogen

/-- Exact finite scope of the sole user-authorized scientific model premise. -/
def FiniteLedHydrogenShareOrder (model : ExperimentModel) : Prop :=
  ∀ u v : LedColor,
    photonEnergy model.optics u < photonEnergy model.optics v →
      hydrogenMolePercentForCondition model (conditionOfLed u) <
        hydrogenMolePercentForCondition model (conditionOfLed v)

theorem sourceModel_assigns_noIrradiation_to_a (model : ExperimentModel) :
    model.assignment .noIrradiation = .a := by
  have hzero :
      totalMolePercent
          (model.composition (model.assignment .noIrradiation)) = 0 := by
    simpa [incidentLightGate] using
      model.photocatalyticLightGate .noIrradiation
  exact (page4_unique_zero_total model.compositionFigure
    (model.assignment .noIrradiation)).mp hzero

/-! ## Universal classification under the named supplement -/

def ClassificationFor (model : ExperimentModel) : Prop :=
  model.assignment.symm .a = .noIrradiation ∧
  model.assignment.symm .b = .blue ∧
  model.assignment.symm .c = .green ∧
  model.assignment.symm .d = .red

/-- The required result is proved for every source-compatible model and not for
a preselected assignment. The sole experimental premise is explicitly named
exactly as required by the controller-bound user supplement. -/
theorem classify_every_source_compatible_model
    (model : ExperimentModel)
    (t8_a8_finite_led_hydrogen_share_order_user_axiom :
      FiniteLedHydrogenShareOrder model) :
    ClassificationFor model := by
  have hN : model.assignment .noIrradiation = .a :=
    sourceModel_assigns_noIrradiation_to_a model
  have hRedGreen :
      hydrogenMolePercentForCondition model .red <
        hydrogenMolePercentForCondition model .green :=
    t8_a8_finite_led_hydrogen_share_order_user_axiom .red .green
      (visiblePhotonEnergyOrder model.optics).1
  have hGreenBlue :
      hydrogenMolePercentForCondition model .green <
        hydrogenMolePercentForCondition model .blue :=
    t8_a8_finite_led_hydrogen_share_order_user_axiom .green .blue
      (visiblePhotonEnergyOrder model.optics).2
  have hRedNeA : model.assignment .red ≠ .a := by
    intro hRed
    have hEqual :
        model.assignment .red = model.assignment .noIrradiation :=
      hRed.trans hN.symm
    have : IlluminationCondition.red = .noIrradiation :=
      model.assignment.injective hEqual
    cases this
  have hGreenNeA : model.assignment .green ≠ .a := by
    intro hGreen
    have hEqual :
        model.assignment .green = model.assignment .noIrradiation :=
      hGreen.trans hN.symm
    have : IlluminationCondition.green = .noIrradiation :=
      model.assignment.injective hEqual
    cases this
  have hBlueNeA : model.assignment .blue ≠ .a := by
    intro hBlue
    have hEqual :
        model.assignment .blue = model.assignment .noIrradiation :=
      hBlue.trans hN.symm
    have : IlluminationCondition.blue = .noIrradiation :=
      model.assignment.injective hEqual
    cases this
  have hDC := model.compositionFigure.hydrogenOrderDC
  have hCB := model.compositionFigure.hydrogenOrderCB
  have hForward :
      model.assignment .red = .d ∧
      model.assignment .green = .c ∧
      model.assignment .blue = .b := by
    cases hRed : model.assignment .red <;>
      cases hGreen : model.assignment .green <;>
        cases hBlue : model.assignment .blue <;>
          simp_all [hydrogenMolePercentForCondition] <;> linarith
  have hAInverse : model.assignment.symm .a = .noIrradiation := by
    simpa using (congrArg model.assignment.symm hN).symm
  have hBInverse : model.assignment.symm .b = .blue := by
    simpa using (congrArg model.assignment.symm hForward.2.2).symm
  have hCInverse : model.assignment.symm .c = .green := by
    simpa using (congrArg model.assignment.symm hForward.2.1).symm
  have hDInverse : model.assignment.symm .d = .red := by
    simpa using (congrArg model.assignment.symm hForward.1).symm
  exact ⟨hAInverse, hBInverse, hCInverse, hDInverse⟩

/-! ## One bar-to-condition carrier for every requested output -/

def conditionA : Prop :=
  ∀ model : ExperimentModel,
    FiniteLedHydrogenShareOrder model →
      model.assignment.symm .a = .noIrradiation

def conditionB : Prop :=
  ∀ model : ExperimentModel,
    FiniteLedHydrogenShareOrder model →
      model.assignment.symm .b = .blue

def conditionC : Prop :=
  ∀ model : ExperimentModel,
    FiniteLedHydrogenShareOrder model →
      model.assignment.symm .c = .green

def conditionD : Prop :=
  ∀ model : ExperimentModel,
    FiniteLedHydrogenShareOrder model →
      model.assignment.symm .d = .red

theorem conditionA_spec : conditionA := by
  intro model hUser
  exact (classify_every_source_compatible_model model hUser).1

theorem conditionB_spec : conditionB := by
  intro model hUser
  exact (classify_every_source_compatible_model model hUser).2.1

theorem conditionC_spec : conditionC := by
  intro model hUser
  exact (classify_every_source_compatible_model model hUser).2.2.1

theorem conditionD_spec : conditionD := by
  intro model hUser
  exact (classify_every_source_compatible_model model hUser).2.2.2

def ConditionalClassification : Prop :=
  ∀ model : ExperimentModel,
    FiniteLedHydrogenShareOrder model → ClassificationFor model

theorem conditionalClassification : ConditionalClassification := by
  intro model hUser
  exact classify_every_source_compatible_model model hUser

/-- Any two models satisfying all source constraints and the supplement give
the same bar-to-condition classification, although their unprinted numerical
readouts and wavelengths may differ. -/
def ClassificationUnique : Prop :=
  ∀ first second : ExperimentModel,
    FiniteLedHydrogenShareOrder first →
    FiniteLedHydrogenShareOrder second →
      first.assignment.symm = second.assignment.symm

theorem classificationUnique : ClassificationUnique := by
  intro first second hFirstUser hSecondUser
  have hFirst := classify_every_source_compatible_model first hFirstUser
  have hSecond := classify_every_source_compatible_model second hSecondUser
  apply Equiv.ext
  intro bar
  cases bar
  · exact hFirst.1.trans hSecond.1.symm
  · exact hFirst.2.1.trans hSecond.2.1.symm
  · exact hFirst.2.2.1.trans hSecond.2.2.1.symm
  · exact hFirst.2.2.2.trans hSecond.2.2.2.symm

/-- The augmented constraints are satisfiable. The concrete ordinal witness is
local to this proof, occurs only after the universal classification, and is not
available as an output-selecting definition or premise. -/
def AugmentedExperimentNonempty : Prop :=
  ∃ model : ExperimentModel, FiniteLedHydrogenShareOrder model

theorem augmentedExperimentNonempty : AugmentedExperimentNonempty := by
  let assignment : IlluminationCondition ≃ DiagramBar := {
    toFun := fun condition => match condition with
      | .noIrradiation => .a
      | .red => .d
      | .green => .c
      | .blue => .b
    invFun := fun bar => match bar with
      | .a => .noIrradiation
      | .b => .blue
      | .c => .green
      | .d => .red
    left_inv := by intro condition; cases condition <;> rfl
    right_inv := by intro bar; cases bar <;> rfl
  }
  let composition : DiagramBar → ProductMolePercent := fun bar =>
    match bar with
    | .a => ⟨0, 0⟩
    | .b => ⟨3, 97⟩
    | .c => ⟨2, 98⟩
    | .d => ⟨1, 99⟩
  let optics : VisibleLedOptics := {
    energyScale := 1
    wavelength := fun colour => match colour with
      | .red => 3
      | .green => 2
      | .blue => 1
    energyScalePositive := by norm_num
    wavelengthPositive := by intro colour; cases colour <;> norm_num
    blueWavelengthShorterGreen := by norm_num
    greenWavelengthShorterRed := by norm_num
  }
  let response : IlluminationCondition → ℝ := fun condition =>
    match condition with
    | .noIrradiation => 0
    | .red => 100
    | .green => 100
    | .blue => 100
  let model : ExperimentModel := {
    assignment := assignment
    composition := composition
    compositionFigure := by
      refine {
        physicalBounds := ?_
        aHydrogenZero := by norm_num [composition]
        aCarbonMonoxideZero := by norm_num [composition]
        bTotal := by norm_num [totalMolePercent, composition]
        cTotal := by norm_num [totalMolePercent, composition]
        dTotal := by norm_num [totalMolePercent, composition]
        dHydrogenPositive := by norm_num [composition]
        hydrogenOrderDC := by norm_num [composition]
        hydrogenOrderCB := by norm_num [composition]
      }
      intro bar
      cases bar <;> norm_num [composition]
    optics := optics
    responseAmplitude := response
    responseAmplitudeNonnegative := by
      intro condition
      cases condition <;> norm_num [response]
    photocatalyticLightGate := by
      intro condition
      cases condition <;>
        norm_num [totalMolePercent, composition, assignment,
          incidentLightGate, response]
  }
  refine ⟨model, ?_⟩
  intro u v hEnergy
  cases u <;> cases v
  · norm_num [photonEnergy, model, optics] at hEnergy
  · norm_num [photonEnergy, model, optics,
      hydrogenMolePercentForCondition, conditionOfLed, assignment, composition]
  · norm_num [photonEnergy, model, optics,
      hydrogenMolePercentForCondition, conditionOfLed, assignment, composition]
  · norm_num [photonEnergy, model, optics] at hEnergy
  · norm_num [photonEnergy, model, optics] at hEnergy
  · norm_num [photonEnergy, model, optics,
      hydrogenMolePercentForCondition, conditionOfLed, assignment, composition]
  · norm_num [photonEnergy, model, optics] at hEnergy
  · norm_num [photonEnergy, model, optics] at hEnergy
  · norm_num [photonEnergy, model, optics] at hEnergy

/-! ## Exact-symbolic reporting bound to the derived classification -/

/-- Source abbreviations from the page-4 paragraph, independent of bar labels. -/
def conditionCode : IlluminationCondition → String
  | .noIrradiation => "N"
  | .red => "R"
  | .green => "G"
  | .blue => "B"

def conditionAReported : Prop :=
  ∀ model : ExperimentModel,
    FiniteLedHydrogenShareOrder model →
      conditionCode (model.assignment.symm .a) = "N"

def conditionBReported : Prop :=
  ∀ model : ExperimentModel,
    FiniteLedHydrogenShareOrder model →
      conditionCode (model.assignment.symm .b) = "B"

def conditionCReported : Prop :=
  ∀ model : ExperimentModel,
    FiniteLedHydrogenShareOrder model →
      conditionCode (model.assignment.symm .c) = "G"

def conditionDReported : Prop :=
  ∀ model : ExperimentModel,
    FiniteLedHydrogenShareOrder model →
      conditionCode (model.assignment.symm .d) = "R"

theorem conditionA_reported : conditionAReported := by
  intro model hUser
  rw [conditionA_spec model hUser]
  rfl

theorem conditionB_reported : conditionBReported := by
  intro model hUser
  rw [conditionB_spec model hUser]
  rfl

theorem conditionC_reported : conditionCReported := by
  intro model hUser
  rw [conditionC_spec model hUser]
  rfl

theorem conditionD_reported : conditionDReported := by
  intro model hUser
  rw [conditionD_spec model hUser]
  rfl

structure RawResult : Prop where
  boundImages : BoundImageProvenance
  finiteDomains : FiniteDomainProvenance
  page3Readout : Page3GibbsFigureReadout
  page3Comparison : Page3IntermediateComparison
  qualitativeStage : QualitativeNamedTransformOnlyAudit
  page4Legend : Page4LegendFacts
  supplement : UserSupplementProvenance
  allCompatibleModels : ConditionalClassification
  conditionAResult : conditionA
  conditionBResult : conditionB
  conditionCResult : conditionC
  conditionDResult : conditionD
  classificationUnique : ClassificationUnique
  augmentedModelNonempty : AugmentedExperimentNonempty

structure ReportedResult : Prop where
  raw : RawResult
  conditionAResult : conditionAReported
  conditionBResult : conditionBReported
  conditionCResult : conditionCReported
  conditionDResult : conditionDReported
  evaluationBasis :
    finiteLedHydrogenShareOrderSupplement.evaluationBasis =
      "user_assumption_augmented"
  originalProblemUnchanged :
    finiteLedHydrogenShareOrderSupplement.originalProblemUnchanged = true
  conditionalScope :
    finiteLedHydrogenShareOrderSupplement.assumptionId =
      "t8_a8_finite_led_hydrogen_share_order_user_axiom"

theorem raw_semantics : RawResult := by
  exact {
    boundImages := boundImageProvenance
    finiteDomains := finiteDomainProvenance
    page3Readout := page3GibbsFigureReadout
    page3Comparison := page3IntermediateComparison
    qualitativeStage := qualitativeNamedTransformOnlyAudit
    page4Legend := page4LegendFacts
    supplement := userSupplementProvenance
    allCompatibleModels := conditionalClassification
    conditionAResult := conditionA_spec
    conditionBResult := conditionB_spec
    conditionCResult := conditionC_spec
    conditionDResult := conditionD_spec
    classificationUnique := classificationUnique
    augmentedModelNonempty := augmentedExperimentNonempty
  }

theorem reported_semantics : ReportedResult := by
  exact {
    raw := raw_semantics
    conditionAResult := conditionA_reported
    conditionBResult := conditionB_reported
    conditionCResult := conditionC_reported
    conditionDResult := conditionD_reported
    evaluationBasis := rfl
    originalProblemUnchanged := rfl
    conditionalScope := rfl
  }

/- The two payload markers are regenerated from the synchronized blind
candidate after every semantic redraft. -/

theorem raw_result :
    ("896925007aa99b7b4e5538546d13a51767da5cc8bee53ad28b768bf21b0bf38a" :
      String) =
        "896925007aa99b7b4e5538546d13a51767da5cc8bee53ad28b768bf21b0bf38a" ∧
      IChO2026Problems.T8A8.RawResult := by
  exact ⟨rfl, raw_semantics⟩

theorem reported_result :
    ("51aa8524579c811f807c3a1a7547cff392cad2c902cbfcd517ea7cf81c00d9d4" :
      String) =
        "51aa8524579c811f807c3a1a7547cff392cad2c902cbfcd517ea7cf81c00d9d4" ∧
      IChO2026Problems.T8A8.ReportedResult := by
  exact ⟨rfl, reported_semantics⟩

end

end IChO2026Problems.T8A8
