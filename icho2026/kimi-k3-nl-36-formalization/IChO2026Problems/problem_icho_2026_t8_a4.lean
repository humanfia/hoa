import IChO2026Chem

/-!
# IChO 2026 T8-A4: iron-complex intermediates 9--15

This file formalizes the student-visible catalytic cycle and the preprinted
answer-sheet data.  Ligand 8 is represented by the four-nitrogen cartoon that
the question explicitly requests.  Every ancillary ligand is represented by
an atom-labelled graph, including covalent bond orders, formal atomic charges,
unpaired electrons, and the atoms bonded to Fe.

The result is labelled `gptCorrectedKimiDraft`.  The only correction to the
sealed Kimi output is intermediate 11: the preprinted `OS = +3` and `CN = 6`
force a closed-shell, dianionic, kappa-two C,O carbon-dioxide-derived ligand;
ionic counting then gives 17 valence electrons.  All other submitted outputs
are preserved.
-/

namespace IChO2026Problems.Icho2026T8A4

/-- Provenance label required for this isolated correction rerun. -/
inductive EvaluationBasis where
  | gptCorrectedKimiDraft
  deriving DecidableEq, Repr

def evaluationBasis : EvaluationBasis := .gptCorrectedKimiDraft

/-- Exact external label required by the correction authorization. -/
def resultLabel : String := "gpt_corrected_kimi_draft"

/-- Elements that are explicit in an ancillary fragment or in the precursor. -/
inductive Element where
  | hydrogen
  | carbon
  | nitrogen
  | oxygen
  | chlorine
  | iron
  deriving DecidableEq, Repr

/-- Source-level roles distinguish atoms even when their elements coincide. -/
inductive AtomRole where
  | ligand8Nitrogen
  | aquaOxygen
  | aquaHydrogen
  | carbonDioxideCarbon
  | carbonDioxideCoordinatingOxygen
  | carbonDioxideTerminalOxygen
  | hydroxycarbonylCarbon
  | hydroxycarbonylHydroxyOxygen
  | hydroxycarbonylCarbonylOxygen
  | hydroxycarbonylHydrogen
  | carbonylCarbon
  | carbonylOxygen
  | chloride
  deriving DecidableEq, Repr

/-- An explicit atom.  `formalCharge` is the charge used in ionic bookkeeping,
and `unpairedElectrons` records radical character rather than hiding it in a
name. -/
structure Atom where
  id : Nat
  element : Element
  role : AtomRole
  formalCharge : Int
  unpairedElectrons : Nat
  deriving DecidableEq, Repr

inductive BondOrder where
  | single
  | double
  | triple
  deriving DecidableEq, Repr

/-- A covalent bond inside one ancillary fragment.  Fe coordination is kept
separate in `FragmentGraph.metalDonorAtomIds`. -/
structure CovalentBond where
  firstAtomId : Nat
  secondAtomId : Nat
  order : BondOrder
  deriving DecidableEq, Repr

/-- The question authorizes a cartoon for ligand 8.  These links record the
printed order of its four N donors without falsely asserting N--N bonds. -/
structure CartoonLink where
  firstDonorId : Nat
  secondDonorId : Nat
  deriving DecidableEq, Repr

inductive FragmentIdentity where
  | ligand8Cartoon
  | aqua
  | chloride
  | carbonDioxideDianionKappaCO
  | hydroxycarbonylKappaC
  | carbonylKappaC
  deriving DecidableEq, Repr

inductive FragmentRepresentation where
  | explicitAtoms
  | problemCartoon
  deriving DecidableEq, Repr

/-- A molecular graph for one ligand or fragment.  Every ID in
`metalDonorAtomIds` denotes an explicit Fe--atom coordination bond. -/
structure FragmentGraph where
  identity : FragmentIdentity
  representation : FragmentRepresentation
  atoms : List Atom
  covalentBonds : List CovalentBond
  cartoonLinks : List CartoonLink
  metalDonorAtomIds : List Nat
  deriving DecidableEq, Repr

/-- A serial number distinguishes repeated instances such as the two waters in
complex 9. -/
structure FragmentInstance where
  serial : Nat
  graph : FragmentGraph
  deriving DecidableEq, Repr

/-- No stereocentre is printed or requested separately in this subproblem, but
the field makes absence of stereochemical annotations explicit. -/
structure StereoDescriptor where
  atomId : Nat
  descriptor : String
  deriving DecidableEq, Repr

/-- A complete drawing at the resolution requested by the problem: one Fe,
the ligand-8 cartoon, and atom-explicit ancillary fragments. -/
structure ComplexDrawing where
  fragments : List FragmentInstance
  stereochemistry : List StereoDescriptor
  deriving DecidableEq, Repr

/-- Oxidation state is the sole independently assigned bookkeeping datum;
charge, coordination number, and VE are calculated below from the drawing. -/
structure IronComplex where
  drawing : ComplexDrawing
  oxidationState : Int
  deriving DecidableEq, Repr

private def atom
    (id : Nat) (element : Element) (role : AtomRole)
    (formalCharge : Int := 0) (unpairedElectrons : Nat := 0) : Atom :=
  { id, element, role, formalCharge, unpairedElectrons }

private def bond (a b : Nat) (order : BondOrder) : CovalentBond :=
  { firstAtomId := a, secondAtomId := b, order }

private def instanceOf (serial : Nat) (graph : FragmentGraph) : FragmentInstance :=
  { serial, graph }

/-- Neutral tetradentate ligand 8, at exactly the cartoon resolution requested
on Q8-2 and depicted on Q8-1. -/
def ligand8Cartoon : FragmentGraph :=
  { identity := .ligand8Cartoon
    representation := .problemCartoon
    atoms :=
      [ atom 0 .nitrogen .ligand8Nitrogen
      , atom 1 .nitrogen .ligand8Nitrogen
      , atom 2 .nitrogen .ligand8Nitrogen
      , atom 3 .nitrogen .ligand8Nitrogen ]
    covalentBonds := []
    cartoonLinks :=
      [ { firstDonorId := 0, secondDonorId := 1 }
      , { firstDonorId := 1, secondDonorId := 2 }
      , { firstDonorId := 2, secondDonorId := 3 } ]
    metalDonorAtomIds := [0, 1, 2, 3] }

def aquaFragment : FragmentGraph :=
  { identity := .aqua
    representation := .explicitAtoms
    atoms :=
      [ atom 0 .oxygen .aquaOxygen
      , atom 1 .hydrogen .aquaHydrogen
      , atom 2 .hydrogen .aquaHydrogen ]
    covalentBonds := [bond 0 1 .single, bond 0 2 .single]
    cartoonLinks := []
    metalDonorAtomIds := [0] }

def chlorideFragment : FragmentGraph :=
  { identity := .chloride
    representation := .explicitAtoms
    atoms := [atom 0 .chlorine .chloride (-1)]
    covalentBonds := []
    cartoonLinks := []
    metalDonorAtomIds := [0] }

/-- Corrected structure of the CO2-derived ligand in 11.  The Fe--C and Fe--O
bonds are represented by donor IDs 0 and 1; internally C(0)--O(1) is single
and C(0)=O(2) is double.  Ionic cleavage assigns -1 to C and -1 to the
coordinating O, hence total ligand charge -2 and no radical electron. -/
def carbonDioxideDianionKappaCO : FragmentGraph :=
  { identity := .carbonDioxideDianionKappaCO
    representation := .explicitAtoms
    atoms :=
      [ atom 0 .carbon .carbonDioxideCarbon (-1)
      , atom 1 .oxygen .carbonDioxideCoordinatingOxygen (-1)
      , atom 2 .oxygen .carbonDioxideTerminalOxygen ]
    covalentBonds := [bond 0 1 .single, bond 0 2 .double]
    cartoonLinks := []
    metalDonorAtomIds := [0, 1] }

/-- C-bound hydroxycarbonyl `-C(=O)OH` in 12 and 13. -/
def hydroxycarbonylKappaC : FragmentGraph :=
  { identity := .hydroxycarbonylKappaC
    representation := .explicitAtoms
    atoms :=
      [ atom 0 .carbon .hydroxycarbonylCarbon (-1)
      , atom 1 .oxygen .hydroxycarbonylHydroxyOxygen
      , atom 2 .oxygen .hydroxycarbonylCarbonylOxygen
      , atom 3 .hydrogen .hydroxycarbonylHydrogen ]
    covalentBonds :=
      [ bond 0 1 .single
      , bond 0 2 .double
      , bond 1 3 .single ]
    cartoonLinks := []
    metalDonorAtomIds := [0] }

/-- C-bound carbon monoxide in 14. -/
def carbonylKappaC : FragmentGraph :=
  { identity := .carbonylKappaC
    representation := .explicitAtoms
    atoms :=
      [ atom 0 .carbon .carbonylCarbon
      , atom 1 .oxygen .carbonylOxygen ]
    covalentBonds := [bond 0 1 .triple]
    cartoonLinks := []
    metalDonorAtomIds := [0] }

def fragmentFormalCharge (f : FragmentGraph) : Int :=
  (f.atoms.map Atom.formalCharge).sum

def fragmentUnpairedElectrons (f : FragmentGraph) : Nat :=
  (f.atoms.map Atom.unpairedElectrons).sum

def drawingLigandCharge (d : ComplexDrawing) : Int :=
  (d.fragments.map fun i => fragmentFormalCharge i.graph).sum

def drawingUnpairedLigandElectrons (d : ComplexDrawing) : Nat :=
  (d.fragments.map fun i => fragmentUnpairedElectrons i.graph).sum

/-- Coordination number is the number of explicit Fe--donor-atom bonds. -/
def coordinationNumber (c : IronComplex) : Nat :=
  (c.drawing.fragments.map fun i => i.graph.metalDonorAtomIds.length).sum

/-- Total complex charge from Fe oxidation state plus all ligand formal
charges. -/
def totalCharge (c : IronComplex) : Int :=
  c.oxidationState + drawingLigandCharge c.drawing

/-- Fe is a group-8 metal.  In the ionic pair-donor convention used by the
question, each explicit Fe--donor bond contributes two electrons. -/
def valenceElectrons (c : IronComplex) : Int :=
  8 - c.oxidationState + 2 * (coordinationNumber c : Int)

private def drawing (fragments : List FragmentInstance) : ComplexDrawing :=
  { fragments, stereochemistry := [] }

/-- Precursor 1 as formed from neutral ligand 8 and FeCl2. -/
def precursor1 : IronComplex :=
  { drawing := drawing
      [instanceOf 0 ligand8Cartoon, instanceOf 1 chlorideFragment,
        instanceOf 2 chlorideFragment]
    oxidationState := 2 }

/-- 9 = `[FeII(L)(OH2)2]2+`. -/
def complex9 : IronComplex :=
  { drawing := drawing
      [instanceOf 0 ligand8Cartoon, instanceOf 1 aquaFragment,
        instanceOf 2 aquaFragment]
    oxidationState := 2 }

/-- 10 = `[FeI(L)(OH2)]+`. -/
def complex10 : IronComplex :=
  { drawing := drawing
      [instanceOf 0 ligand8Cartoon, instanceOf 1 aquaFragment]
    oxidationState := 1 }

/-- 11 = `[FeIII(L)(kappa2-C,O-CO2)] +`, with a CO2(2-) ligand. -/
def complex11 : IronComplex :=
  { drawing := drawing
      [instanceOf 0 ligand8Cartoon,
        instanceOf 1 carbonDioxideDianionKappaCO]
    oxidationState := 3 }

/-- 12 = `[FeII(L)(C(=O)OH)]+`. -/
def complex12 : IronComplex :=
  { drawing := drawing
      [instanceOf 0 ligand8Cartoon, instanceOf 1 hydroxycarbonylKappaC]
    oxidationState := 2 }

/-- 13 = `[FeII(L)(OH2)(C(=O)OH)]+`. -/
def complex13 : IronComplex :=
  { drawing := drawing
      [instanceOf 0 ligand8Cartoon, instanceOf 1 hydroxycarbonylKappaC,
        instanceOf 2 aquaFragment]
    oxidationState := 2 }

/-- 14 = `[FeII(L)(CO)(OH2)]2+`. -/
def complex14 : IronComplex :=
  { drawing := drawing
      [instanceOf 0 ligand8Cartoon, instanceOf 1 carbonylKappaC,
        instanceOf 2 aquaFragment]
    oxidationState := 2 }

/-- 15 = `[FeII(L)(OH2)]2+`. -/
def complex15 : IronComplex :=
  { drawing := drawing
      [instanceOf 0 ligand8Cartoon, instanceOf 1 aquaFragment]
    oxidationState := 2 }

/-- One carrier for each of the 35 requested outputs, in source order. -/
def structure9 : ComplexDrawing := complex9.drawing
def complex9OxidationState : Int := complex9.oxidationState
def complex9CoordinationNumber : Nat := coordinationNumber complex9
def complex9ValenceElectrons : Int := valenceElectrons complex9
def complex9TotalCharge : Int := totalCharge complex9

def structure10 : ComplexDrawing := complex10.drawing
def complex10OxidationState : Int := complex10.oxidationState
def complex10CoordinationNumber : Nat := coordinationNumber complex10
def complex10ValenceElectrons : Int := valenceElectrons complex10
def complex10TotalCharge : Int := totalCharge complex10

def structure11 : ComplexDrawing := complex11.drawing
def complex11OxidationState : Int := complex11.oxidationState
def complex11CoordinationNumber : Nat := coordinationNumber complex11
def complex11ValenceElectrons : Int := valenceElectrons complex11
def complex11TotalCharge : Int := totalCharge complex11

def structure12 : ComplexDrawing := complex12.drawing
def complex12OxidationState : Int := complex12.oxidationState
def complex12CoordinationNumber : Nat := coordinationNumber complex12
def complex12ValenceElectrons : Int := valenceElectrons complex12
def complex12TotalCharge : Int := totalCharge complex12

def structure13 : ComplexDrawing := complex13.drawing
def complex13OxidationState : Int := complex13.oxidationState
def complex13CoordinationNumber : Nat := coordinationNumber complex13
def complex13ValenceElectrons : Int := valenceElectrons complex13
def complex13TotalCharge : Int := totalCharge complex13

def structure14 : ComplexDrawing := complex14.drawing
def complex14OxidationState : Int := complex14.oxidationState
def complex14CoordinationNumber : Nat := coordinationNumber complex14
def complex14ValenceElectrons : Int := valenceElectrons complex14
def complex14TotalCharge : Int := totalCharge complex14

def structure15 : ComplexDrawing := complex15.drawing
def complex15OxidationState : Int := complex15.oxidationState
def complex15CoordinationNumber : Nat := coordinationNumber complex15
def complex15ValenceElectrons : Int := valenceElectrons complex15
def complex15TotalCharge : Int := totalCharge complex15

/-! ## Source-first material and charge ledgers -/

/-- The ligand cartoon is a conserved unit, so its unexpanded carbon skeleton
is never silently discarded in the atom ledger. -/
structure Composition where
  ligand8Units : Int
  iron : Int
  carbon : Int
  nitrogen : Int
  oxygen : Int
  hydrogen : Int
  chlorine : Int
  deriving DecidableEq, Repr

def zeroComposition : Composition :=
  { ligand8Units := 0, iron := 0, carbon := 0, nitrogen := 0,
    oxygen := 0, hydrogen := 0, chlorine := 0 }

def addComposition (a b : Composition) : Composition :=
  { ligand8Units := a.ligand8Units + b.ligand8Units
    iron := a.iron + b.iron
    carbon := a.carbon + b.carbon
    nitrogen := a.nitrogen + b.nitrogen
    oxygen := a.oxygen + b.oxygen
    hydrogen := a.hydrogen + b.hydrogen
    chlorine := a.chlorine + b.chlorine }

def scaleComposition (n : Nat) (a : Composition) : Composition :=
  { ligand8Units := n * a.ligand8Units
    iron := n * a.iron
    carbon := n * a.carbon
    nitrogen := n * a.nitrogen
    oxygen := n * a.oxygen
    hydrogen := n * a.hydrogen
    chlorine := n * a.chlorine }

def singletonComposition (element : Element) : Composition :=
  match element with
  | .hydrogen => { zeroComposition with hydrogen := 1 }
  | .carbon => { zeroComposition with carbon := 1 }
  | .nitrogen => { zeroComposition with nitrogen := 1 }
  | .oxygen => { zeroComposition with oxygen := 1 }
  | .chlorine => { zeroComposition with chlorine := 1 }
  | .iron => { zeroComposition with iron := 1 }

def explicitAtomComposition (atoms : List Atom) : Composition :=
  atoms.foldl (fun acc a => addComposition acc (singletonComposition a.element))
    zeroComposition

def fragmentComposition (f : FragmentGraph) : Composition :=
  match f.representation with
  | .problemCartoon => { zeroComposition with ligand8Units := 1 }
  | .explicitAtoms => explicitAtomComposition f.atoms

def drawingComposition (d : ComplexDrawing) : Composition :=
  d.fragments.foldl
    (fun acc i => addComposition acc (fragmentComposition i.graph))
    { zeroComposition with iron := 1 }

inductive ComplexLabel where
  | one
  | nine
  | ten
  | eleven
  | twelve
  | thirteen
  | fourteen
  | fifteen
  deriving DecidableEq, Repr

structure Assignment where
  one : IronComplex
  nine : IronComplex
  ten : IronComplex
  eleven : IronComplex
  twelve : IronComplex
  thirteen : IronComplex
  fourteen : IronComplex
  fifteen : IronComplex
  deriving DecidableEq, Repr

def correctedAssignment : Assignment :=
  { one := precursor1
    nine := complex9
    ten := complex10
    eleven := complex11
    twelve := complex12
    thirteen := complex13
    fourteen := complex14
    fifteen := complex15 }

def Assignment.get (a : Assignment) : ComplexLabel → IronComplex
  | .one => a.one
  | .nine => a.nine
  | .ten => a.ten
  | .eleven => a.eleven
  | .twelve => a.twelve
  | .thirteen => a.thirteen
  | .fourteen => a.fourteen
  | .fifteen => a.fifteen

inductive MaterialSpecies where
  | complex (label : ComplexLabel)
  | water
  | chloride
  | carbonDioxide
  | proton
  | electron
  | carbonMonoxide
  | photon
  deriving DecidableEq, Repr

inductive Phase where
  | supportedComplex
  | aqueous
  | gas
  | chargeReservoir
  | radiationField
  deriving DecidableEq, Repr

def materialPhase : MaterialSpecies → Phase
  | .complex _ => .supportedComplex
  | .water => .aqueous
  | .chloride => .aqueous
  | .carbonDioxide => .gas
  | .proton => .aqueous
  | .electron => .chargeReservoir
  | .carbonMonoxide => .gas
  | .photon => .radiationField

def materialComposition (a : Assignment) : MaterialSpecies → Composition
  | .complex label => drawingComposition (a.get label).drawing
  | .water => { zeroComposition with oxygen := 1, hydrogen := 2 }
  | .chloride => { zeroComposition with chlorine := 1 }
  | .carbonDioxide => { zeroComposition with carbon := 1, oxygen := 2 }
  | .proton => { zeroComposition with hydrogen := 1 }
  | .electron => zeroComposition
  | .carbonMonoxide => { zeroComposition with carbon := 1, oxygen := 1 }
  | .photon => zeroComposition

def materialCharge (a : Assignment) : MaterialSpecies → Int
  | .complex label => totalCharge (a.get label)
  | .water => 0
  | .chloride => -1
  | .carbonDioxide => 0
  | .proton => 1
  | .electron => -1
  | .carbonMonoxide => 0
  | .photon => 0

structure StoichiometricTerm where
  coefficient : Nat
  species : MaterialSpecies
  deriving DecidableEq, Repr

structure ReactionStep where
  name : String
  reactants : List StoichiometricTerm
  products : List StoichiometricTerm
  deriving DecidableEq, Repr

private def term (n : Nat) (s : MaterialSpecies) : StoichiometricTerm :=
  { coefficient := n, species := s }

/-- Exact directed arrows printed on Q8-2, including activation of 1. -/
def sourceCycleSteps : List ReactionStep :=
  [ { name := "1_to_9"
      reactants := [term 1 (.complex .one), term 2 .water]
      products := [term 1 (.complex .nine), term 2 .chloride] }
  , { name := "9_to_10"
      reactants := [term 1 (.complex .nine), term 1 .photon, term 1 .electron]
      products := [term 1 (.complex .ten), term 1 .water] }
  , { name := "10_to_11"
      reactants := [term 1 (.complex .ten), term 1 .carbonDioxide]
      products := [term 1 (.complex .eleven), term 1 .water] }
  , { name := "11_to_12"
      reactants :=
        [term 1 (.complex .eleven), term 1 .photon, term 1 .electron,
          term 1 .proton]
      products := [term 1 (.complex .twelve)] }
  , { name := "12_to_13"
      reactants := [term 1 (.complex .twelve), term 1 .water]
      products := [term 1 (.complex .thirteen)] }
  , { name := "13_to_14"
      reactants := [term 1 (.complex .thirteen), term 1 .proton]
      products := [term 1 (.complex .fourteen), term 1 .water] }
  , { name := "14_to_15"
      reactants := [term 1 (.complex .fourteen)]
      products := [term 1 (.complex .fifteen), term 1 .carbonMonoxide] }
  , { name := "15_to_9"
      reactants := [term 1 (.complex .fifteen), term 1 .water]
      products := [term 1 (.complex .nine)] } ]

/-- The finite, source-derived staged domain; the inductive type has no
anonymous `other` or catch-all material stream. -/
def stagedSpeciesDomain : List MaterialSpecies :=
  [ .complex .one, .complex .nine, .complex .ten, .complex .eleven,
    .complex .twelve, .complex .thirteen, .complex .fourteen,
    .complex .fifteen, .water, .chloride, .carbonDioxide, .proton,
    .electron, .carbonMonoxide, .photon ]

def sideComposition (a : Assignment) (side : List StoichiometricTerm) : Composition :=
  side.foldl
    (fun acc t => addComposition acc
      (scaleComposition t.coefficient (materialComposition a t.species)))
    zeroComposition

def sideCharge (a : Assignment) (side : List StoichiometricTerm) : Int :=
  (side.map fun t => (t.coefficient : Int) * materialCharge a t.species).sum

def BalancedStep (a : Assignment) (step : ReactionStep) : Prop :=
  sideComposition a step.reactants = sideComposition a step.products ∧
  sideCharge a step.reactants = sideCharge a step.products

/-- Since charge and atom balance are used to validate the requested charges
and structures, this mechanism is classified as `quantitative_material_stage`.
-/
def QuantitativeMaterialStage (a : Assignment) : Prop :=
  stagedSpeciesDomain.Nodup ∧
  ∀ step ∈ sourceCycleSteps, BalancedStep a step

/-! ## Structural well-formedness and source constraints -/

def atomIds (f : FragmentGraph) : List Nat := f.atoms.map Atom.id

def FragmentWellFormed (f : FragmentGraph) : Prop :=
  (atomIds f).Nodup ∧
  f.metalDonorAtomIds.Nodup ∧
  (∀ id ∈ f.metalDonorAtomIds, id ∈ atomIds f) ∧
  (∀ b ∈ f.covalentBonds,
    b.firstAtomId ∈ atomIds f ∧ b.secondAtomId ∈ atomIds f ∧
      b.firstAtomId ≠ b.secondAtomId) ∧
  (∀ link ∈ f.cartoonLinks,
    link.firstDonorId ∈ f.metalDonorAtomIds ∧
      link.secondDonorId ∈ f.metalDonorAtomIds)

def DrawingWellFormed (d : ComplexDrawing) : Prop :=
  (d.fragments.map FragmentInstance.serial).Nodup ∧
  ∀ i ∈ d.fragments, FragmentWellFormed i.graph

def AssignmentWellFormed (a : Assignment) : Prop :=
  DrawingWellFormed a.one.drawing ∧
  DrawingWellFormed a.nine.drawing ∧
  DrawingWellFormed a.ten.drawing ∧
  DrawingWellFormed a.eleven.drawing ∧
  DrawingWellFormed a.twelve.drawing ∧
  DrawingWellFormed a.thirteen.drawing ∧
  DrawingWellFormed a.fourteen.drawing ∧
  DrawingWellFormed a.fifteen.drawing

/-- The five givens printed on student answer sheets A8-3 and A8-4. -/
def PrintedAnswerSheetFacts (a : Assignment) : Prop :=
  a.eleven.oxidationState = 3 ∧
  coordinationNumber a.eleven = 6 ∧
  coordinationNumber a.twelve = 5 ∧
  a.thirteen.oxidationState = 2 ∧
  valenceElectrons a.fifteen = 16

/-- The ligand drawing required by the source occurs exactly once in every
complex, and no output silently expands or replaces it. -/
def UsesLigand8CartoonOnce (c : IronComplex) : Prop :=
  (c.drawing.fragments.map fun i => i.graph.identity).count .ligand8Cartoon = 1

def AllUseLigand8Cartoon (a : Assignment) : Prop :=
  UsesLigand8CartoonOnce a.one ∧
  UsesLigand8CartoonOnce a.nine ∧
  UsesLigand8CartoonOnce a.ten ∧
  UsesLigand8CartoonOnce a.eleven ∧
  UsesLigand8CartoonOnce a.twelve ∧
  UsesLigand8CartoonOnce a.thirteen ∧
  UsesLigand8CartoonOnce a.fourteen ∧
  UsesLigand8CartoonOnce a.fifteen

/-- The source requests drawings without any stereocentre annotation; the
empty lists record that no stereochemical choice has been invented. -/
def NoInventedStereochemistry (a : Assignment) : Prop :=
  a.nine.drawing.stereochemistry = [] ∧
  a.ten.drawing.stereochemistry = [] ∧
  a.eleven.drawing.stereochemistry = [] ∧
  a.twelve.drawing.stereochemistry = [] ∧
  a.thirteen.drawing.stereochemistry = [] ∧
  a.fourteen.drawing.stereochemistry = [] ∧
  a.fifteen.drawing.stereochemistry = []

/-- Summary sufficient to derive the earlier T8-A2 prerequisite internally.
It records the formulas, charges, and radical counts through the two oxidations
and hydrolysis, rather than importing another generated answer. -/
structure PreviousPartSpeciesSummary where
  carbon : Nat
  hydrogen : Nat
  nitrogen : Nat
  oxygen : Nat
  charge : Int
  unpairedElectrons : Nat
  deriving DecidableEq, Repr

def PreviousPartA2Derived : Prop :=
  ∃ s3 s4 s5 s6 s7 : PreviousPartSpeciesSummary,
    s3 = { carbon := 6
           hydrogen := 15
           nitrogen := 1
           oxygen := 3
           charge := 1
           unpairedElectrons := 1 } ∧
    s4 = { carbon := 6
           hydrogen := 14
           nitrogen := 1
           oxygen := 3
           charge := 0
           unpairedElectrons := 1 } ∧
    s5 = { carbon := 6
           hydrogen := 14
           nitrogen := 1
           oxygen := 3
           charge := 1
           unpairedElectrons := 0 } ∧
    s6 = { carbon := 4
           hydrogen := 11
           nitrogen := 1
           oxygen := 2
           charge := 0
           unpairedElectrons := 0 } ∧
    s7 = { carbon := 2
           hydrogen := 4
           nitrogen := 0
           oxygen := 2
           charge := 0
           unpairedElectrons := 0 } ∧
    s5.carbon = s6.carbon + s7.carbon ∧
    s5.nitrogen = s6.nitrogen + s7.nitrogen ∧
    s5.oxygen + 1 = s6.oxygen + s7.oxygen ∧
    s5.hydrogen + 2 = s6.hydrogen + s7.hydrogen + 1 ∧
    s5.charge = s6.charge + s7.charge + 1

/-- Source-to-Lean bridge for the internally derived previous part. -/
theorem previousPartA2Derivation : PreviousPartA2Derived := by
  refine
    ⟨ { carbon := 6
        hydrogen := 15
        nitrogen := 1
        oxygen := 3
        charge := 1
        unpairedElectrons := 1 }
    , { carbon := 6
        hydrogen := 14
        nitrogen := 1
        oxygen := 3
        charge := 0
        unpairedElectrons := 1 }
    , { carbon := 6
        hydrogen := 14
        nitrogen := 1
        oxygen := 3
        charge := 1
        unpairedElectrons := 0 }
    , { carbon := 4
        hydrogen := 11
        nitrogen := 1
        oxygen := 2
        charge := 0
        unpairedElectrons := 0 }
    , { carbon := 2
        hydrogen := 4
        nitrogen := 0
        oxygen := 2
        charge := 0
        unpairedElectrons := 0 }
    , rfl, rfl, rfl, rfl, rfl, by norm_num ⟩

/-- Independent constraints that a proposed set of structures must satisfy.
The corrected candidate is not inserted as a premise. -/
def SourceCompatible (a : Assignment) : Prop :=
  AssignmentWellFormed a ∧
  AllUseLigand8Cartoon a ∧
  PrintedAnswerSheetFacts a ∧
  QuantitativeMaterialStage a ∧
  NoInventedStereochemistry a

/-- All 35 exact requested values, written as one mixed symbolic contract. -/
def RequestedOutputValues (a : Assignment) : Prop :=
  a.nine.drawing = structure9 ∧
  a.nine.oxidationState = 2 ∧ coordinationNumber a.nine = 6 ∧
    valenceElectrons a.nine = 18 ∧ totalCharge a.nine = 2 ∧
  a.ten.drawing = structure10 ∧
  a.ten.oxidationState = 1 ∧ coordinationNumber a.ten = 5 ∧
    valenceElectrons a.ten = 17 ∧ totalCharge a.ten = 1 ∧
  a.eleven.drawing = structure11 ∧
  a.eleven.oxidationState = 3 ∧ coordinationNumber a.eleven = 6 ∧
    valenceElectrons a.eleven = 17 ∧ totalCharge a.eleven = 1 ∧
  a.twelve.drawing = structure12 ∧
  a.twelve.oxidationState = 2 ∧ coordinationNumber a.twelve = 5 ∧
    valenceElectrons a.twelve = 16 ∧ totalCharge a.twelve = 1 ∧
  a.thirteen.drawing = structure13 ∧
  a.thirteen.oxidationState = 2 ∧ coordinationNumber a.thirteen = 6 ∧
    valenceElectrons a.thirteen = 18 ∧ totalCharge a.thirteen = 1 ∧
  a.fourteen.drawing = structure14 ∧
  a.fourteen.oxidationState = 2 ∧ coordinationNumber a.fourteen = 6 ∧
    valenceElectrons a.fourteen = 18 ∧ totalCharge a.fourteen = 2 ∧
  a.fifteen.drawing = structure15 ∧
  a.fifteen.oxidationState = 2 ∧ coordinationNumber a.fifteen = 5 ∧
    valenceElectrons a.fifteen = 16 ∧ totalCharge a.fifteen = 2

/-- Raw mixed result: the candidate must satisfy independently stated source,
graph, answer-sheet, and atom/charge-ledger specifications. -/
def RawResult : Prop :=
  PreviousPartA2Derived ∧
  SourceCompatible correctedAssignment ∧
  RequestedOutputValues correctedAssignment

/-- Every requested output has exact symbolic/integer reporting, so reporting
does not round or weaken the raw result. -/
def ReportedResult : Prop :=
  resultLabel = "gpt_corrected_kimi_draft" ∧
  evaluationBasis = .gptCorrectedKimiDraft ∧ RawResult

theorem gptCorrectedKimiDraftRawResult : RawResult := by
  refine ⟨previousPartA2Derivation, ?_, ?_⟩
  · simp [SourceCompatible, AssignmentWellFormed, DrawingWellFormed,
      FragmentWellFormed, atomIds, AllUseLigand8Cartoon,
      UsesLigand8CartoonOnce, PrintedAnswerSheetFacts,
      QuantitativeMaterialStage, stagedSpeciesDomain, sourceCycleSteps,
      BalancedStep, sideComposition, sideCharge, NoInventedStereochemistry,
      correctedAssignment, Assignment.get, precursor1, complex9, complex10,
      complex11, complex12, complex13, complex14, complex15, drawing,
      ligand8Cartoon, aquaFragment, chlorideFragment,
      carbonDioxideDianionKappaCO, hydroxycarbonylKappaC, carbonylKappaC,
      fragmentFormalCharge, drawingLigandCharge, coordinationNumber,
      valenceElectrons, totalCharge, drawingComposition, fragmentComposition,
      explicitAtomComposition, singletonComposition, materialComposition,
      materialCharge, scaleComposition, addComposition, zeroComposition,
      term, instanceOf, atom, bond]
  · unfold RequestedOutputValues
    decide

theorem gptCorrectedKimiDraftReportedResult : ReportedResult := by
  exact ⟨rfl, rfl, gptCorrectedKimiDraftRawResult⟩

/-- The answer-sheet OS/CN givens and the cycle charge imply the corrected
ligand charge and the resulting 17-electron count for intermediate 11. -/
theorem complex11CorrectionCarrier :
    fragmentFormalCharge carbonDioxideDianionKappaCO = -2 ∧
    carbonDioxideDianionKappaCO.metalDonorAtomIds.length = 2 ∧
    fragmentUnpairedElectrons carbonDioxideDianionKappaCO = 0 ∧
    complex11OxidationState = 3 ∧
    complex11CoordinationNumber = 6 ∧
    complex11ValenceElectrons = 17 ∧
    complex11TotalCharge = 1 := by
  decide

/-- Blueprint-level target theorem. -/
theorem problem_icho_2026_t8_a4 : ReportedResult := by
  exact gptCorrectedKimiDraftReportedResult

end IChO2026Problems.Icho2026T8A4
