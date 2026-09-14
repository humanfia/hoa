import IChO2026Chem

/-!
# IChO 2026, problem T7, part A5

The problem gives a PNP-supported molybdenum trichloride precursor, three
equivalents of sodium amalgam, and a displayed stoichiometric nitrogen uptake.
This file keeps three layers separate:

* the source measurements and their displayed quanta;
* an unbounded integer coordination inventory derived from those measurements;
* an explicit typed molecular drawing of the resulting complex.

The carbon skeleton of the PNP ligand is represented by the simplified ligand
template expressly requested by the question.  Every atom and bond of the five
dinitrogen ligands, every metal/donor attachment, charge, radical count, and the
absence of stereocentres are represented explicitly.
-/

namespace IChO2026Problems.Icho2026T7A5

open scoped BigOperators

noncomputable section

/-- Source classes permitted by the target's candidate-domain policy. -/
inductive Provenance
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- Chemical entities explicitly named in the source fixation arrow. -/
inductive SourceSpecies
  | precursor4
  | dinitrogen
  | sodiumAmalgam
  | product5
  deriving DecidableEq, Repr

/-- Units occurring in the displayed uptake experiment. -/
inductive UnitTag
  | gram
  | gramPerMole
  | cubicCentimetre
  | kelvin
  | bar
  | equivalent
  deriving DecidableEq, Repr

/-- A printed quantity together with the quantum of its last displayed place. -/
structure DisplayedQuantity where
  shown : ℝ
  displayQuantum : ℝ
  unit : UnitTag

/-- The complete source-visible numerical contract for the fixation experiment. -/
structure FixationExperiment where
  sampleSpecies : SourceSpecies
  gasSpecies : SourceSpecies
  reductantSpecies : SourceSpecies
  requestedProduct : SourceSpecies
  precursorMass : DisplayedQuantity
  precursorMolarMass : DisplayedQuantity
  dinitrogenVolume : DisplayedQuantity
  temperature : DisplayedQuantity
  pressure : DisplayedQuantity
  sodiumAmalgamEquivalentsPerPrecursor : DisplayedQuantity
  measurementProvenance : Provenance
  precursorProvenance : Provenance

/-- Exact transcription of the numbers and roles printed on pages 2 and 3. -/
def sourceExperiment : FixationExperiment where
  sampleSpecies := .precursor4
  gasSpecies := .dinitrogen
  reductantSpecies := .sodiumAmalgam
  requestedProduct := .product5
  precursorMass := ⟨1, 1 / 100, .gram⟩
  precursorMolarMass := ⟨597824 / 1000, 1 / 1000, .gramPerMole⟩
  dinitrogenVolume := ⟨9497 / 100, 1 / 100, .cubicCentimetre⟩
  temperature := ⟨27315 / 100, 1 / 100, .kelvin⟩
  pressure := ⟨1, 1 / 10, .bar⟩
  sodiumAmalgamEquivalentsPerPrecursor := ⟨3, 1, .equivalent⟩
  measurementProvenance := .problemText
  precursorProvenance := .problemImage

/-- Four-significant-figure conventional molar gas constant, in J mol⁻¹ K⁻¹. -/
def molarGasConstantJPerMolK : ℝ := 8314 / 1000

/-- Possible actual values represented by the four displayed measurements. -/
structure ActualExperiment where
  precursorMassG : ℝ
  dinitrogenVolumeCm3 : ℝ
  temperatureK : ℝ
  pressureBar : ℝ

/-- Half-last-place measurement cells fixed before inspecting the answer. -/
def ConsistentWithSource (a : ActualExperiment) : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement
      a.precursorMassG sourceExperiment.precursorMass.shown
        sourceExperiment.precursorMass.displayQuantum ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      a.dinitrogenVolumeCm3 sourceExperiment.dinitrogenVolume.shown
        sourceExperiment.dinitrogenVolume.displayQuantum ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      a.temperatureK sourceExperiment.temperature.shown
        sourceExperiment.temperature.displayQuantum ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      a.pressureBar sourceExperiment.pressure.shown
        sourceExperiment.pressure.displayQuantum ∧
  0 < a.precursorMassG ∧ 0 < a.dinitrogenVolumeCm3 ∧
  0 < a.temperatureK ∧ 0 < a.pressureBar

/-- Central values of the source's displayed measurement cells. -/
def centralExperiment : ActualExperiment where
  precursorMassG := sourceExperiment.precursorMass.shown
  dinitrogenVolumeCm3 := sourceExperiment.dinitrogenVolume.shown
  temperatureK := sourceExperiment.temperature.shown
  pressureBar := sourceExperiment.pressure.shown

/-- Ideal-gas amount of nitrogen divided by the amount of precursor `4`. -/
def actualUptakeRatio (a : ActualExperiment) : ℝ :=
  (((a.pressureBar * 100000) * (a.dinitrogenVolumeCm3 / 1000000)) /
      (molarGasConstantJPerMolK * a.temperatureK)) /
    (a.precursorMassG / sourceExperiment.precursorMolarMass.shown)

/-- The exact, unrounded central-value expression from the printed data. -/
def centralUptakeRatio : ℝ := actualUptakeRatio centralExperiment

/--
Raw quantitative support for the structural inference.  The last conjunct is a
mechanically propagated interval from the four displayed measurement quanta;
it is not an answer-fitted tolerance.
-/
def UptakeCalculationSpec : Prop :=
  centralUptakeRatio = (1419383632 : ℝ) / 567742275 ∧
  |centralUptakeRatio - (5 : ℝ) / 2| < 1 / 10000 ∧
  ∀ a : ActualExperiment, ConsistentWithSource a →
    (7 : ℝ) / 3 < actualUptakeRatio a ∧
      actualUptakeRatio a < (8 : ℝ) / 3

/-! ## Inline discharge of the listed previous-part prerequisite -/

/-- Elements needed to check the bicarbonate equation requested in T7-A4. -/
inductive ScrubberElement
  | carbon
  | hydrogen
  | nitrogen
  | oxygen
  deriving DecidableEq, Fintype, Repr

/-- Finite species domain of the preceding aqueous scrubbing equation. -/
inductive ScrubberSpecies
  | compound3
  | carbonDioxide
  | water
  | protonatedCompound3
  | bicarbonate
  deriving DecidableEq, Fintype, Repr

/-- Formula counts independently reconstructed from the page-2 drawing. -/
def scrubberAtomCount : ScrubberSpecies → ScrubberElement → ℕ
  | .compound3, .carbon => 5
  | .compound3, .hydrogen => 13
  | .compound3, .nitrogen => 1
  | .compound3, .oxygen => 2
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .oxygen => 2
  | .water, .hydrogen => 2
  | .water, .oxygen => 1
  | .protonatedCompound3, .carbon => 5
  | .protonatedCompound3, .hydrogen => 14
  | .protonatedCompound3, .nitrogen => 1
  | .protonatedCompound3, .oxygen => 2
  | .bicarbonate, .carbon => 1
  | .bicarbonate, .hydrogen => 1
  | .bicarbonate, .oxygen => 3
  | _, _ => 0

/-- Formal charge in elementary-charge units for the preceding equation. -/
def scrubberCharge : ScrubberSpecies → ℤ
  | .protonatedCompound3 => 1
  | .bicarbonate => -1
  | _ => 0

/-- Reactant coefficients of `3 + CO₂ + H₂O`. -/
def scrubberReactants : ScrubberSpecies → ℕ
  | .compound3 | .carbonDioxide | .water => 1
  | _ => 0

/-- Product coefficients of `protonated 3 + HCO₃⁻`. -/
def scrubberProducts : ScrubberSpecies → ℕ
  | .protonatedCompound3 | .bicarbonate => 1
  | _ => 0

def scrubberSideAtomCount
    (side : ScrubberSpecies → ℕ) (e : ScrubberElement) : ℕ :=
  ∑ s : ScrubberSpecies, side s * scrubberAtomCount s e

def scrubberSideCharge (side : ScrubberSpecies → ℕ) : ℤ :=
  ∑ s : ScrubberSpecies, (side s : ℤ) * scrubberCharge s

/--
The earlier answer is derived inline as the atom- and charge-balanced equation
`(HOCH₂CH₂)₂NCH₃ + CO₂ + H₂O ⇌ [(HOCH₂CH₂)₂NHCH₃]⁺ + HCO₃⁻`.
-/
def PreviousPartA4EquationDerived : Prop :=
  (∀ e : ScrubberElement,
      scrubberSideAtomCount scrubberReactants e =
        scrubberSideAtomCount scrubberProducts e) ∧
  scrubberSideCharge scrubberReactants = scrubberSideCharge scrubberProducts ∧
  scrubberReactants .compound3 = 1 ∧
  scrubberReactants .carbonDioxide = 1 ∧
  scrubberReactants .water = 1 ∧
  scrubberProducts .protonatedCompound3 = 1 ∧
  scrubberProducts .bicarbonate = 1

/-! ## Typed molecular drawings -/

/-- Elements visible either in precursor `4` or the simplified product drawing. -/
inductive Element
  | nitrogen
  | phosphorus
  | chlorine
  | molybdenum
  deriving DecidableEq, Fintype, Repr

/-- Covalent bond orders that occur explicitly in the requested simplified drawing. -/
inductive CovalentBondOrder
  | single
  | triple
  deriving DecidableEq, Repr

/-- Metal-ligand attachments are distinguished from drawn covalent bonds. -/
inductive BondKind
  | covalent (order : CovalentBondOrder)
  | coordination
  deriving DecidableEq, Repr

/-- A typed bond between two named sites.  Connectivity is interpreted undirectedly. -/
structure Bond (V : Type) where
  first : V
  second : V
  kind : BondKind
  deriving DecidableEq

def coordinationBond {V : Type} (a b : V) : Bond V := ⟨a, b, .coordination⟩

def tripleBond {V : Type} (a b : V) : Bond V :=
  ⟨a, b, .covalent .triple⟩

/-- The explicitly authorized simplified representation of the PNP ligand. -/
structure SimplifiedPNPTemplate where
  aromaticRingCarbonCount : ℕ
  aromaticRingNitrogenCount : ℕ
  substitutionPositions : List ℕ
  methyleneLinkerCount : ℕ
  phosphorusDonorCount : ℕ
  tertButylGroupsPerPhosphorus : ℕ
  donorSequence : List Element
  totalCarbonCount : ℕ
  totalHydrogenCount : ℕ
  totalNitrogenCount : ℕ
  totalPhosphorusCount : ℕ
  netCharge : ℤ
  radicalElectronCount : ℕ
  stereocentreCount : ℕ
  deriving DecidableEq

/--
The dashed-box legend: 2,6-bis[(di-tert-butylphosphino)methyl]pyridine,
abstracted to its P-N-P donor face as requested.
-/
def sourcePNPTemplate : SimplifiedPNPTemplate where
  aromaticRingCarbonCount := 5
  aromaticRingNitrogenCount := 1
  substitutionPositions := [2, 6]
  methyleneLinkerCount := 2
  phosphorusDonorCount := 2
  tertButylGroupsPerPhosphorus := 2
  donorSequence := [.phosphorus, .nitrogen, .phosphorus]
  totalCarbonCount := 23
  totalHydrogenCount := 43
  totalNitrogenCount := 1
  totalPhosphorusCount := 2
  netCharge := 0
  radicalElectronCount := 0
  stereocentreCount := 0

/-- Molecular drawing with explicit site labels, bonds, charge, and radicals. -/
structure MolecularDrawing (V : Type) where
  element : V → Element
  siteCharge : V → ℤ
  radicalElectrons : V → ℕ
  bonds : List (Bond V)
  overallCharge : ℤ
  stereocentres : List V
  pnpLigandCount : ℕ
  pnpTemplate : SimplifiedPNPTemplate

def HasBond {V : Type} [DecidableEq V]
    (d : MolecularDrawing V) (a b : V) (kind : BondKind) : Prop :=
  ∃ edge ∈ d.bonds,
    edge.kind = kind ∧
      ((edge.first = a ∧ edge.second = b) ∨
        (edge.first = b ∧ edge.second = a))

def atomCount {V : Type} [Fintype V] [DecidableEq V]
    (d : MolecularDrawing V) (e : Element) : ℕ :=
  (Finset.univ.filter fun v => d.element v = e).card

def siteChargeSum {V : Type} [Fintype V] (d : MolecularDrawing V) : ℤ :=
  ∑ v : V, d.siteCharge v

def coordinationDegree {V : Type} [DecidableEq V]
    (d : MolecularDrawing V) (v : V) : ℕ :=
  (d.bonds.filter fun edge =>
    edge.kind = .coordination ∧ (edge.first = v ∨ edge.second = v)).length

/-! ### Source image reconstruction of precursor 4 -/

inductive PrecursorSite
  | molybdenum
  | pnpLeftPhosphorus
  | pnpNitrogen
  | pnpRightPhosphorus
  | chlorideOne
  | chlorideTwo
  | chlorideThree
  deriving DecidableEq, Fintype, Repr

def precursorElement : PrecursorSite → Element
  | .molybdenum => .molybdenum
  | .pnpLeftPhosphorus | .pnpRightPhosphorus => .phosphorus
  | .pnpNitrogen => .nitrogen
  | .chlorideOne | .chlorideTwo | .chlorideThree => .chlorine

/-- Oxidation-state/formal-charge ledger for neutral PNP-MoCl₃. -/
def precursorSiteCharge : PrecursorSite → ℤ
  | .molybdenum => 3
  | .chlorideOne | .chlorideTwo | .chlorideThree => -1
  | _ => 0

def precursorBondLedger : List (Bond PrecursorSite) :=
  [ coordinationBond .pnpLeftPhosphorus .molybdenum
  , coordinationBond .pnpNitrogen .molybdenum
  , coordinationBond .pnpRightPhosphorus .molybdenum
  , coordinationBond .chlorideOne .molybdenum
  , coordinationBond .chlorideTwo .molybdenum
  , coordinationBond .chlorideThree .molybdenum ]

def precursor4 : MolecularDrawing PrecursorSite where
  element := precursorElement
  siteCharge := precursorSiteCharge
  radicalElectrons := fun _ => 0
  bonds := precursorBondLedger
  overallCharge := 0
  stereocentres := []
  pnpLigandCount := 1
  pnpTemplate := sourcePNPTemplate

def Precursor4ImageSpec (d : MolecularDrawing PrecursorSite) : Prop :=
  d.element = precursorElement ∧
  d.siteCharge = precursorSiteCharge ∧
  d.radicalElectrons = (fun _ => 0) ∧
  d.bonds = precursorBondLedger ∧
  d.bonds.Nodup ∧
  d.overallCharge = 0 ∧
  siteChargeSum d = d.overallCharge ∧
  d.stereocentres = [] ∧
  d.pnpLigandCount = 1 ∧
  d.pnpTemplate = sourcePNPTemplate ∧
  atomCount d .molybdenum = 1 ∧
  atomCount d .chlorine = 3 ∧
  coordinationDegree d .molybdenum = 6

/-! ### Explicit product-5 site and bond graph -/

inductive ProductSite
  | leftMolybdenum
  | rightMolybdenum
  | leftPincerP1
  | leftPincerN
  | leftPincerP2
  | rightPincerP1
  | rightPincerN
  | rightPincerP2
  | leftTerminalOneBoundN
  | leftTerminalOneOuterN
  | leftTerminalTwoBoundN
  | leftTerminalTwoOuterN
  | rightTerminalOneBoundN
  | rightTerminalOneOuterN
  | rightTerminalTwoBoundN
  | rightTerminalTwoOuterN
  | bridgeLeftN
  | bridgeRightN
  deriving DecidableEq, Fintype, Repr

def productElement : ProductSite → Element
  | .leftMolybdenum | .rightMolybdenum => .molybdenum
  | .leftPincerP1 | .leftPincerP2 | .rightPincerP1 | .rightPincerP2 =>
      .phosphorus
  | _ => .nitrogen

def productBondLedger : List (Bond ProductSite) :=
  [ coordinationBond .leftPincerP1 .leftMolybdenum
  , coordinationBond .leftPincerN .leftMolybdenum
  , coordinationBond .leftPincerP2 .leftMolybdenum
  , coordinationBond .rightPincerP1 .rightMolybdenum
  , coordinationBond .rightPincerN .rightMolybdenum
  , coordinationBond .rightPincerP2 .rightMolybdenum
  , coordinationBond .leftMolybdenum .leftTerminalOneBoundN
  , tripleBond .leftTerminalOneBoundN .leftTerminalOneOuterN
  , coordinationBond .leftMolybdenum .leftTerminalTwoBoundN
  , tripleBond .leftTerminalTwoBoundN .leftTerminalTwoOuterN
  , coordinationBond .rightMolybdenum .rightTerminalOneBoundN
  , tripleBond .rightTerminalOneBoundN .rightTerminalOneOuterN
  , coordinationBond .rightMolybdenum .rightTerminalTwoBoundN
  , tripleBond .rightTerminalTwoBoundN .rightTerminalTwoOuterN
  , coordinationBond .leftMolybdenum .bridgeLeftN
  , tripleBond .bridgeLeftN .bridgeRightN
  , coordinationBond .bridgeRightN .rightMolybdenum ]

/-- Concrete candidate drawing, with the ligand deliberately at P-N-P template level. -/
def structure5Candidate : MolecularDrawing ProductSite where
  element := productElement
  siteCharge := fun _ => 0
  radicalElectrons := fun _ => 0
  bonds := productBondLedger
  overallCharge := 0
  stereocentres := []
  pnpLigandCount := 2
  pnpTemplate := sourcePNPTemplate

inductive DinitrogenBindingMode
  | terminalEndOn
  | bridgingEndOnEndOn
  deriving DecidableEq, Repr

inductive DinitrogenLigand
  | leftTerminalOne
  | leftTerminalTwo
  | rightTerminalOne
  | rightTerminalTwo
  | bridge
  deriving DecidableEq, Fintype, Repr

def dinitrogenBindingMode : DinitrogenLigand → DinitrogenBindingMode
  | .bridge => .bridgingEndOnEndOn
  | _ => .terminalEndOn

def terminalDinitrogenCount : ℕ :=
  (Finset.univ.filter fun ligand : DinitrogenLigand =>
    dinitrogenBindingMode ligand = .terminalEndOn).card

def bridgingDinitrogenCount : ℕ :=
  (Finset.univ.filter fun ligand : DinitrogenLigand =>
    dinitrogenBindingMode ligand = .bridgingEndOnEndOn).card

/-- Every terminal and bridging N₂ ligand is realized by explicit typed bonds. -/
def DinitrogenLigandRealized
    (d : MolecularDrawing ProductSite) : DinitrogenLigand → Prop
  | .leftTerminalOne =>
      HasBond d .leftMolybdenum .leftTerminalOneBoundN .coordination ∧
      HasBond d .leftTerminalOneBoundN .leftTerminalOneOuterN (.covalent .triple)
  | .leftTerminalTwo =>
      HasBond d .leftMolybdenum .leftTerminalTwoBoundN .coordination ∧
      HasBond d .leftTerminalTwoBoundN .leftTerminalTwoOuterN (.covalent .triple)
  | .rightTerminalOne =>
      HasBond d .rightMolybdenum .rightTerminalOneBoundN .coordination ∧
      HasBond d .rightTerminalOneBoundN .rightTerminalOneOuterN (.covalent .triple)
  | .rightTerminalTwo =>
      HasBond d .rightMolybdenum .rightTerminalTwoBoundN .coordination ∧
      HasBond d .rightTerminalTwoBoundN .rightTerminalTwoOuterN (.covalent .triple)
  | .bridge =>
      HasBond d .leftMolybdenum .bridgeLeftN .coordination ∧
      HasBond d .bridgeLeftN .bridgeRightN (.covalent .triple) ∧
      HasBond d .bridgeRightN .rightMolybdenum .coordination

inductive MetalSide
  | left
  | right
  deriving DecidableEq, Repr

def PincerRealized (d : MolecularDrawing ProductSite) : MetalSide → Prop
  | .left =>
      HasBond d .leftPincerP1 .leftMolybdenum .coordination ∧
      HasBond d .leftPincerN .leftMolybdenum .coordination ∧
      HasBond d .leftPincerP2 .leftMolybdenum .coordination
  | .right =>
      HasBond d .rightPincerP1 .rightMolybdenum .coordination ∧
      HasBond d .rightPincerN .rightMolybdenum .coordination ∧
      HasBond d .rightPincerP2 .rightMolybdenum .coordination

/-! ## Source-derived, unbounded coordination inventory -/

/-- Counts used to infer molecular nuclearity and N₂ binding modes. -/
structure BindingInventory where
  metalCenters : ℕ
  terminalN2 : ℕ
  bridgingN2 : ℕ
  deriving DecidableEq, Repr

def totalDinitrogen (i : BindingInventory) : ℕ :=
  i.terminalN2 + i.bridgingN2

/-- A terminal N₂ uses one metal site; an end-on bridge uses one on each metal. -/
def dinitrogenCoordinationContacts (i : BindingInventory) : ℕ :=
  i.terminalN2 + 2 * i.bridgingN2

def inventoryUptakeRatio (i : BindingInventory) : ℝ :=
  (totalDinitrogen i : ℝ) / (i.metalCenters : ℝ)

/-- Replacement-contact capacity read from the three chloride sites of `4`. -/
def replacementContactCapacityPerCore : ℕ :=
  atomCount precursor4 .chlorine

/--
No finite search bound is imposed.  The three chlorides drawn on each precursor
give an upper bound of three replacement N₂ contacts per retained Mo.  The
connectedness inequality is the standard edge bound for a connected assembly
whose inter-metal links are bridging N₂ ligands.  Equality at the derived
candidate is a conclusion, not a saturation premise.
-/
def SourceAdmissibleInventory (i : BindingInventory) : Prop :=
  0 < i.metalCenters ∧
  dinitrogenCoordinationContacts i ≤
      replacementContactCapacityPerCore * i.metalCenters ∧
  i.metalCenters ≤ i.bridgingN2 + 1 ∧
  ∃ a : ActualExperiment,
    ConsistentWithSource a ∧ inventoryUptakeRatio i = actualUptakeRatio a

/-- Candidate obtained after solving, not assumed in `SourceAdmissibleInventory`. -/
def derivedInventory : BindingInventory where
  metalCenters := 2
  terminalN2 := 4
  bridgingN2 := 1

/-- Distribution of the four terminal ligands over the two derived Mo centers. -/
structure TwoCenterDistribution where
  leftTerminalN2 : ℕ
  rightTerminalN2 : ℕ
  bridgingN2 : ℕ
  deriving DecidableEq, Repr

def DistributionFitsInventory
    (i : BindingInventory) (d : TwoCenterDistribution) : Prop :=
  i.metalCenters = 2 ∧
  d.leftTerminalN2 + d.rightTerminalN2 = i.terminalN2 ∧
  d.bridgingN2 = i.bridgingN2 ∧
  d.leftTerminalN2 + d.bridgingN2 = 3 ∧
  d.rightTerminalN2 + d.bridgingN2 = 3

def derivedDistribution : TwoCenterDistribution where
  leftTerminalN2 := 2
  rightTerminalN2 := 2
  bridgingN2 := 1

/-- Explicit electron-count ledger behind the three occupied sites per Mo. -/
def molybdenumZeroValentDElectrons : ℕ := 6

def neutralPNPElectronDonation : ℕ := 6

def neutralDinitrogenDonationPerMetalContact : ℕ := 2

def candidateElectronCountPerMolybdenum : ℕ :=
  molybdenumZeroValentDElectrons + neutralPNPElectronDonation +
    3 * neutralDinitrogenDonationPerMetalContact

/-- Problem-image and ordinary electron-count facts used by the inventory model. -/
def CoordinationSiteDerivation : Prop :=
  replacementContactCapacityPerCore = 3 ∧
  sourceExperiment.sodiumAmalgamEquivalentsPerPrecursor.shown = 3 ∧
  precursor4.siteCharge .molybdenum = 3 ∧
  structure5Candidate.siteCharge .leftMolybdenum = 0 ∧
  structure5Candidate.siteCharge .rightMolybdenum = 0 ∧
  candidateElectronCountPerMolybdenum = 18

/-- Provenance of every outcome-decisive constraint in the integer audit. -/
structure ConstraintProvenance where
  uptakeMeasurements : Provenance
  precursorSiteCount : Provenance
  connectedMoleculeRule : Provenance
  coordinationCapacityRule : Provenance
  solvedInventory : Provenance
  deriving DecidableEq, Repr

def structure5ConstraintProvenance : ConstraintProvenance where
  uptakeMeasurements := .problemText
  precursorSiteCount := .problemImage
  connectedMoleculeRule := .trustedGeneralLaw
  coordinationCapacityRule := .trustedGeneralLaw
  solvedInventory := .derivedTheorem

/-- Full typed specification of the simplified product drawing. -/
def Structure5Spec (d : MolecularDrawing ProductSite) : Prop :=
  d.element = productElement ∧
  d.siteCharge = (fun _ => 0) ∧
  d.radicalElectrons = (fun _ => 0) ∧
  d.bonds.Nodup ∧
  d.bonds.length = 17 ∧
  d.overallCharge = 0 ∧
  siteChargeSum d = d.overallCharge ∧
  d.stereocentres = [] ∧
  d.pnpLigandCount = 2 ∧
  d.pnpTemplate = sourcePNPTemplate ∧
  PincerRealized d .left ∧
  PincerRealized d .right ∧
  (∀ ligand : DinitrogenLigand, DinitrogenLigandRealized d ligand) ∧
  atomCount d .molybdenum = derivedInventory.metalCenters ∧
  atomCount d .nitrogen = 12 ∧
  atomCount d .phosphorus = 4 ∧
  atomCount d .chlorine = 0 ∧
  terminalDinitrogenCount = derivedInventory.terminalN2 ∧
  bridgingDinitrogenCount = derivedInventory.bridgingN2 ∧
  coordinationDegree d .leftMolybdenum = 6 ∧
  coordinationDegree d .rightMolybdenum = 6

/-! ## Scoped primary-literature corroboration -/

/-- External evidence is kept distinct from source/candidate-domain provenance. -/
inductive ExternalAuthorityKind
  | peerReviewedPrimaryLiterature
  deriving DecidableEq, Repr

/-- Metadata and the exact connectivity counts visible in Figure 1a of the paper. -/
structure PrimaryLiteratureRecord where
  title : String
  doi : String
  stableUrl : String
  locator : String
  retrievedFigureSha256 : String
  precursorUnits : ℕ
  sodiumAmalgamEquivalents : ℕ
  productMolybdenumCenters : ℕ
  productTerminalN2 : ℕ
  productBridgingN2 : ℕ
  authorityKind : ExternalAuthorityKind

/--
K. Arashiba, Y. Miyake, Y. Nishibayashi, Nature Chemistry 3 (2011), 120-125,
Figure 1a.  It is used only to corroborate connectivity, not to supply the
problem's omitted solvent, time, yield, or phase information.
-/
def arashibaMiyakeNishibayashiFigure1a : PrimaryLiteratureRecord where
  title :=
    "A molybdenum complex bearing PNP-type pincer ligands leads to the catalytic reduction of dinitrogen into ammonia"
  doi := "10.1038/nchem.906"
  stableUrl := "https://doi.org/10.1038/nchem.906"
  locator := "Figure 1a: preparation and molecular structure of dinitrogen-bridged dimolybdenum complex 2a"
  retrievedFigureSha256 :=
    "8ac353a229cb217214ca9f8a5c79f3da939a3d59033a0ed20a6eed8d7ce9c908"
  precursorUnits := 2
  sodiumAmalgamEquivalents := 6
  productMolybdenumCenters := 2
  productTerminalN2 := 4
  productBridgingN2 := 1
  authorityKind := .peerReviewedPrimaryLiterature

def LiteratureConnectivityCorroboration
    (d : MolecularDrawing ProductSite) : Prop :=
  arashibaMiyakeNishibayashiFigure1a.sodiumAmalgamEquivalents =
      arashibaMiyakeNishibayashiFigure1a.precursorUnits *
        sourceExperiment.sodiumAmalgamEquivalentsPerPrecursor.shown ∧
  arashibaMiyakeNishibayashiFigure1a.productMolybdenumCenters =
      atomCount d .molybdenum ∧
  arashibaMiyakeNishibayashiFigure1a.productTerminalN2 =
      terminalDinitrogenCount ∧
  arashibaMiyakeNishibayashiFigure1a.productBridgingN2 =
      bridgingDinitrogenCount

/-! ## Result contracts -/

/-- Raw exact-symbolic result, including all source and derivation obligations. -/
def Structure5RawResult : Prop :=
  PreviousPartA4EquationDerived ∧
  Precursor4ImageSpec precursor4 ∧
  UptakeCalculationSpec ∧
  CoordinationSiteDerivation ∧
  SourceAdmissibleInventory derivedInventory ∧
  (∀ i : BindingInventory, SourceAdmissibleInventory i → i = derivedInventory) ∧
  DistributionFitsInventory derivedInventory derivedDistribution ∧
  (∀ d : TwoCenterDistribution,
      DistributionFitsInventory derivedInventory d → d = derivedDistribution) ∧
  Structure5Spec structure5Candidate ∧
  LiteratureConnectivityCorroboration structure5Candidate

/--
Exact symbolic reporting adds no rounding.  These final conjuncts expose the
four terminal ligands and the unique `μ-η¹:η¹-N₂` cross-boundary connection.
-/
def Structure5ReportedResult : Prop :=
  Structure5RawResult ∧
  terminalDinitrogenCount = 4 ∧
  bridgingDinitrogenCount = 1 ∧
  HasBond structure5Candidate .leftMolybdenum .bridgeLeftN .coordination ∧
  HasBond structure5Candidate .bridgeLeftN .bridgeRightN (.covalent .triple) ∧
  HasBond structure5Candidate .bridgeRightN .rightMolybdenum .coordination

/-- The page-2 precursor reconstruction satisfies its complete image contract. -/
theorem precursor4_image_specification : Precursor4ImageSpec precursor4 := by
  simp [Precursor4ImageSpec, precursor4, precursorElement,
    precursorSiteCharge, precursorBondLedger, siteChargeSum, atomCount,
    coordinationDegree, sourcePNPTemplate] <;> decide

/-- The listed preceding-part equation is rederived without importing a sibling result. -/
theorem previous_part_a4_derived : PreviousPartA4EquationDerived := by
  refine ⟨?_, ?_⟩
  · intro e
    cases e <;> decide
  · decide

/-- Exact arithmetic and displayed-quantum propagation for the N₂ uptake. -/
theorem uptake_calculation : UptakeCalculationSpec := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [centralUptakeRatio, actualUptakeRatio, centralExperiment,
      sourceExperiment, molarGasConstantJPerMolK]
  · norm_num [centralUptakeRatio, actualUptakeRatio, centralExperiment,
      sourceExperiment, molarGasConstantJPerMolK, abs_of_nonneg,
      abs_of_neg]
  · intro a ha
    rcases ha with ⟨hm, hv, ht, hp, hm_pos, hv_pos, ht_pos, hp_pos⟩
    simp only [IChO2026Chem.Reporting.ConsistentMeasurement,
      sourceExperiment] at hm hv ht hp
    norm_num at hm hv ht hp
    rcases abs_le.mp hm with ⟨hm_lower_raw, hm_upper_raw⟩
    rcases abs_le.mp hv with ⟨hv_lower_raw, hv_upper_raw⟩
    rcases abs_le.mp ht with ⟨ht_lower_raw, ht_upper_raw⟩
    rcases abs_le.mp hp with ⟨hp_lower_raw, hp_upper_raw⟩
    have hm_lower : (199 : ℝ) / 200 ≤ a.precursorMassG := by
      linarith
    have hm_upper : a.precursorMassG ≤ (201 : ℝ) / 200 := by
      linarith
    have hv_lower : (18993 : ℝ) / 200 ≤ a.dinitrogenVolumeCm3 := by
      linarith
    have hv_upper : a.dinitrogenVolumeCm3 ≤ (18995 : ℝ) / 200 := by
      linarith
    have ht_lower : (54629 : ℝ) / 200 ≤ a.temperatureK := by
      linarith
    have ht_upper : a.temperatureK ≤ (54631 : ℝ) / 200 := by
      linarith
    have hp_lower : (19 : ℝ) / 20 ≤ a.pressureBar := by
      linarith
    have hp_upper : a.pressureBar ≤ (21 : ℝ) / 20 := by
      linarith
    have hpv_lower :
        (19 : ℝ) / 20 * ((18993 : ℝ) / 200) ≤
          a.pressureBar * a.dinitrogenVolumeCm3 := by
      exact mul_le_mul hp_lower hv_lower (by norm_num) (le_of_lt hp_pos)
    have hpv_upper :
        a.pressureBar * a.dinitrogenVolumeCm3 ≤
          (21 : ℝ) / 20 * ((18995 : ℝ) / 200) := by
      exact mul_le_mul hp_upper hv_upper (le_of_lt hv_pos) (by norm_num)
    have htm_lower :
        (54629 : ℝ) / 200 * ((199 : ℝ) / 200) ≤
          a.temperatureK * a.precursorMassG := by
      exact mul_le_mul ht_lower hm_lower (by norm_num) (le_of_lt ht_pos)
    have htm_upper :
        a.temperatureK * a.precursorMassG ≤
          (54631 : ℝ) / 200 * ((201 : ℝ) / 200) := by
      exact mul_le_mul ht_upper hm_upper (le_of_lt hm_pos) (by norm_num)
    have hratio :
        actualUptakeRatio a =
          (149456 * a.pressureBar * a.dinitrogenVolumeCm3) /
            (20785 * a.temperatureK * a.precursorMassG) := by
      unfold actualUptakeRatio molarGasConstantJPerMolK
      norm_num [sourceExperiment]
      field_simp [ne_of_gt hm_pos, ne_of_gt ht_pos]
      <;> ring
    have hden_pos :
        0 < (20785 : ℝ) * a.temperatureK * a.precursorMassG := by
      positivity
    constructor
    · rw [hratio]
      apply (lt_div_iff₀ hden_pos).2
      nlinarith [hpv_lower, htm_upper]
    · rw [hratio]
      apply (div_lt_iff₀ hden_pos).2
      nlinarith [hpv_upper, htm_lower]

/-- The image-derived site count and the candidate's 18-electron cross-check agree. -/
theorem coordination_site_derivation : CoordinationSiteDerivation := by
  norm_num [CoordinationSiteDerivation, replacementContactCapacityPerCore,
    atomCount, precursor4, precursorElement, sourceExperiment,
    structure5Candidate, candidateElectronCountPerMolybdenum,
    molybdenumZeroValentDElectrons, neutralPNPElectronDonation,
    neutralDinitrogenDonationPerMetalContact] <;> decide

/-- The submitted inventory is compatible with some values in every source measurement cell. -/
theorem derived_inventory_is_admissible :
    SourceAdmissibleInventory derivedInventory := by
  refine ⟨by norm_num [derivedInventory], ?_, by norm_num [derivedInventory], ?_⟩
  · norm_num [dinitrogenCoordinationContacts, derivedInventory,
      replacementContactCapacityPerCore, atomCount, precursor4,
      precursorElement] <;> decide
  · let witness : ActualExperiment :=
      { precursorMassG := 1
        dinitrogenVolumeCm3 :=
          ((5 : ℝ) / 2) * 20785 * ((27315 : ℝ) / 100) / 149456
        temperatureK := (27315 : ℝ) / 100
        pressureBar := 1 }
    refine ⟨witness, ?_, ?_⟩
    · norm_num [witness, ConsistentWithSource,
        IChO2026Chem.Reporting.ConsistentMeasurement, sourceExperiment,
        abs_of_nonneg, abs_of_neg]
    · norm_num [witness, inventoryUptakeRatio, totalDinitrogen,
        derivedInventory, actualUptakeRatio, molarGasConstantJPerMolK,
        sourceExperiment]

/--
The unbounded integer constraints force two Mo centers, four terminal N₂
ligands, and one bridge; no candidate-count cutoff is used.
-/
theorem admissible_inventory_unique
    (i : BindingInventory) (hi : SourceAdmissibleInventory i) :
    i = derivedInventory := by
  rcases i with ⟨metalCenters, terminalCount, bridgeCount⟩
  rcases hi with
    ⟨hmetal_pos, hcapacity, hconnected, a, ha, hratio⟩
  rw [coordination_site_derivation.1] at hcapacity
  change terminalCount + 2 * bridgeCount ≤ 3 * metalCenters at hcapacity
  change metalCenters ≤ bridgeCount + 1 at hconnected
  have hbounds := uptake_calculation.2.2 a ha
  rw [← hratio] at hbounds
  change
    (7 : ℝ) / 3 < ((terminalCount + bridgeCount : ℕ) : ℝ) /
        (metalCenters : ℝ) ∧
      ((terminalCount + bridgeCount : ℕ) : ℝ) /
          (metalCenters : ℝ) < (8 : ℝ) / 3 at hbounds
  have hmetal_real : (0 : ℝ) < (metalCenters : ℝ) := by
    exact_mod_cast hmetal_pos
  have hlower_aux := (lt_div_iff₀ hmetal_real).mp hbounds.1
  have hupper_aux := (div_lt_iff₀ hmetal_real).mp hbounds.2
  norm_num at hlower_aux hupper_aux
  have hlower_real :
      (7 : ℝ) * metalCenters <
        (3 : ℝ) * (terminalCount + bridgeCount) := by
    nlinarith
  have hupper_real :
      (3 : ℝ) * (terminalCount + bridgeCount) <
        (8 : ℝ) * metalCenters := by
    nlinarith
  have hlower :
      7 * metalCenters < 3 * (terminalCount + bridgeCount) := by
    exact_mod_cast hlower_real
  have hupper :
      3 * (terminalCount + bridgeCount) < 8 * metalCenters := by
    exact_mod_cast hupper_real
  have hmetal : metalCenters = 2 := by omega
  have hterminal : terminalCount = 4 := by omega
  have hbridge : bridgeCount = 1 := by omega
  subst metalCenters
  subst terminalCount
  subst bridgeCount
  rfl

/-- Three contacts at each derived center force two terminal ligands per side. -/
theorem two_center_distribution_unique
    (d : TwoCenterDistribution)
    (hd : DistributionFitsInventory derivedInventory d) :
    d = derivedDistribution := by
  rcases d with ⟨leftTerminalN2, rightTerminalN2, bridgeCount⟩
  simp only [DistributionFitsInventory, derivedInventory, derivedDistribution,
    TwoCenterDistribution.mk.injEq] at hd ⊢
  omega

/-- The concrete typed graph realizes the derived coordination inventory. -/
theorem structure5_candidate_meets_specification :
    Structure5Spec structure5Candidate := by
  have hLigands : ∀ ligand : DinitrogenLigand,
      DinitrogenLigandRealized structure5Candidate ligand := by
    intro ligand
    cases ligand <;>
      simp [DinitrogenLigandRealized, HasBond, structure5Candidate,
        productBondLedger, coordinationBond, tripleBond]
  unfold Structure5Spec
  exact ⟨rfl, rfl, rfl,
    by decide,
    by decide,
    rfl,
    by decide,
    rfl, rfl, rfl,
    by
      simp [PincerRealized, HasBond, structure5Candidate,
        productBondLedger, coordinationBond, tripleBond],
    by
      simp [PincerRealized, HasBond, structure5Candidate,
        productBondLedger, coordinationBond, tripleBond],
    hLigands,
    by decide,
    by decide,
    by decide,
    by decide,
    by decide,
    by decide,
    by decide,
    by decide⟩

/-- Raw exact-symbolic requested-output carrier. -/
theorem structure5_raw : Structure5RawResult := by
  exact ⟨previous_part_a4_derived, precursor4_image_specification,
    uptake_calculation, coordination_site_derivation,
    derived_inventory_is_admissible, admissible_inventory_unique,
    by norm_num [DistributionFitsInventory, derivedInventory, derivedDistribution],
    two_center_distribution_unique, structure5_candidate_meets_specification,
    by norm_num [LiteratureConnectivityCorroboration,
      arashibaMiyakeNishibayashiFigure1a, sourceExperiment, atomCount,
      structure5Candidate, productElement, terminalDinitrogenCount,
      bridgingDinitrogenCount, dinitrogenBindingMode] <;> decide⟩

/--
Requested structure: `[(PNP)Mo(N₂)₂]₂(μ-η¹:η¹-N₂)`, with two terminal
end-on N₂ ligands on each Mo and one end-on bridge.
-/
theorem structure5_reported : Structure5ReportedResult := by
  refine ⟨structure5_raw, by decide, by decide, ?_, ?_, ?_⟩
  all_goals
    simp [HasBond, structure5Candidate, productBondLedger, coordinationBond,
      tripleBond]

end

end IChO2026Problems.Icho2026T7A5
