import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T9-A7: sodium-adduct peaks of the degradation products from L

This file is an answer-blind formalization of the two mass-spectrometric
outputs.  In particular, the formula `C₂₇H₂₈O₅` printed below the first pair
of square brackets on page 4 is the formula of one intact, fully benzylated
glucopyranosyl repeat.  It is not the formula of a whole degradation product.

The page-3 directing rule is replayed locally: after the first primary
debenzylation at source-labelled unit 1, the still-available preferred site is
unit 4.  Cutting the outgoing glycosidic boundary at units 1 and 4 resolves
the two wavy boundaries in the generic page-4 degradation drawing into the
paths `2-3-4` and `5-6-7-1`.  Thus the complete first product contains an
acetyl cap, two intact repeats, and a degraded terminus; the second contains
an acetyl cap, three intact repeats, and a degraded terminus.  One sodium
adduct is then associated with each neutral product.

The degradation arrow is used as `qualitativeNamedTransformOnly`: its depicted
connectivity and product-fragment formulas are used, but no yield, completion,
sole-product, phase balance, or omitted-stream claim is made.  The quantitative
calculation is a static formula/mass audit of each explicitly assembled ion.
-/

namespace IChO2026Problems
namespace T9A7

/-! ## Source and transformation inventory -/

/-- Provenance classes admitted by the source contract. -/
inductive Provenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
deriving DecidableEq, Repr

/-- Exact problem-local regions used below. -/
inductive SourceLocator where
  | page3DirectingParagraph
  | page3BetaCDTemplate
  | page3ArrowToL
  | page4DegradationArrow
  | page4IntactRepeatFormula
  | page4DegradedTerminusFormula
  | page4AcetylatedBoundary
  | partA7SodiumAdductRequest
deriving DecidableEq, Repr

/-- The reaction drawing supplies a qualitative, non-exclusive topology and
formula constraint; it is not used as a complete material balance. -/
inductive StagedTransformationUse where
  | qualitativeNamedTransformOnly
deriving DecidableEq, Repr

def stagedTransformationUse : StagedTransformationUse :=
  .qualitativeNamedTransformOnly

/-- Species/reagents explicitly printed in the degradation sequence. -/
inductive DegradationReagent where
  | iodine
  | triphenylphosphine
  | zinc
  | propan1ol
  | sodiumBorohydride
  | aceticAnhydride
  | pyridine
deriving DecidableEq, Fintype, Repr

/-- The four ordered operations printed over and under the page-4 arrow. -/
def degradationSchedule : List (List DegradationReagent) :=
  [ [.iodine, .triphenylphosphine],
    [.zinc, .propan1ol],
    [.sodiumBorohydride],
    [.aceticAnhydride, .pyridine] ]

/-- Source-facing arrow data.  Deliberately absent are coefficients, phases,
yield, exclusivity, and any assertion that unpictured streams are empty. -/
structure QualitativeSourceArrow where
  reactantRole : String
  productRole : String
  directionLeftToRight : Bool
  schedule : List (List DegradationReagent)
  locator : SourceLocator
  useClass : StagedTransformationUse
deriving DecidableEq, Repr

def degradationArrow : QualitativeSourceArrow :=
  { reactantRole := "L with a free primary OH at the locally drawn unit"
    productRole := "two glycosidic-chain termini shown on page 4"
    directionLeftToRight := true
    schedule := degradationSchedule
    locator := .page4DegradationArrow
    useClass := .qualitativeNamedTransformOnly }

def SourceArrowSpec : Prop :=
  degradationArrow.reactantRole =
      "L with a free primary OH at the locally drawn unit" ∧
  degradationArrow.productRole =
      "two glycosidic-chain termini shown on page 4" ∧
  degradationArrow.directionLeftToRight = true ∧
  degradationArrow.schedule =
    [ [.iodine, .triphenylphosphine],
      [.zinc, .propan1ol],
      [.sodiumBorohydride],
      [.aceticAnhydride, .pyridine] ] ∧
  degradationArrow.locator = .page4DegradationArrow ∧
  degradationArrow.useClass = .qualitativeNamedTransformOnly

theorem sourceArrow_spec : SourceArrowSpec := by
  unfold SourceArrowSpec
  native_decide

/-! ## Inline derivation of the previous-part structure L -/

/-- The seven glucopyranoside units of beta-cyclodextrin.  Lean index zero is
source label 1, and so on. -/
abbrev BetaCDUnit := Fin 7

def unit1 : BetaCDUnit := ⟨0, by omega⟩
def unit2 : BetaCDUnit := ⟨1, by omega⟩
def unit3 : BetaCDUnit := ⟨2, by omega⟩
def unit4 : BetaCDUnit := ⟨3, by omega⟩
def unit5 : BetaCDUnit := ⟨4, by omega⟩
def unit6 : BetaCDUnit := ⟨5, by omega⟩
def unit7 : BetaCDUnit := ⟨6, by omega⟩

def betaUnits : List BetaCDUnit :=
  [unit1, unit2, unit3, unit4, unit5, unit6, unit7]

/-- Clockwise offset in the source-labelled seven-cycle. -/
def unitAtOffset (unit : BetaCDUnit) (offset : ℕ) : BetaCDUnit :=
  ⟨(unit.val + offset) % 7, Nat.mod_lt _ (by omega)⟩

inductive PrimarySubstituent where
  | hydroxy
  | benzyl
deriving DecidableEq, Fintype, Repr

abbrev PrimaryPattern := BetaCDUnit → PrimarySubstituent

def fullyBenzylatedPrimaryPattern : PrimaryPattern := fun _ => .benzyl

def reductivelyDebenzylate
    (before : PrimaryPattern) (unit : BetaCDUnit) : PrimaryPattern :=
  fun candidate => if candidate = unit then .hydroxy else before candidate

def PrimaryPositionAvailable
    (pattern : PrimaryPattern) (unit : BetaCDUnit) : Prop :=
  pattern unit = .benzyl

/-- The source paragraph's preferred unit-4 branch and unit-3 fallback,
expressed as offsets from its unit-1 anchor. -/
def directedNextTarget
    (pattern : PrimaryPattern) (anchor : BetaCDUnit) : BetaCDUnit :=
  if pattern (unitAtOffset anchor 3) == .benzyl then
    unitAtOffset anchor 3
  else
    unitAtOffset anchor 2

/-- Candidate L is generated by the source-directed trace, rather than by
placing the two requested degradation cuts into a premise. -/
def lPrimaryPattern : PrimaryPattern :=
  let afterFirst := reductivelyDebenzylate fullyBenzylatedPrimaryPattern unit1
  reductivelyDebenzylate afterFirst (directedNextTarget afterFirst unit1)

/-- Full previous-part obligation needed here.  All fourteen secondary sites
stay O-benzylated; the primary sites are hydroxy exactly at units 1 and 4. -/
def PreviousPartLSpec : Prop :=
  directedNextTarget
      (reductivelyDebenzylate fullyBenzylatedPrimaryPattern unit1) unit1 =
        unit4 ∧
  (∀ unit : BetaCDUnit,
    lPrimaryPattern unit = .hydroxy ↔ unit = unit1 ∨ unit = unit4) ∧
  (betaUnits.filter fun unit => lPrimaryPattern unit = .hydroxy) =
    [unit1, unit4]

theorem previousPartL_derived : PreviousPartLSpec := by
  unfold PreviousPartLSpec
  native_decide

/-! ## The two cuts and resolution of every wavy boundary -/

structure DirectedRingEdge where
  tail : BetaCDUnit
  head : BetaCDUnit
deriving DecidableEq, Repr

/-- The local degradation drawing cuts the outgoing alpha-1,4 boundary of a
unit bearing the free primary hydroxyl group. -/
def cutAfter (unit : BetaCDUnit) : DirectedRingEdge :=
  ⟨unit, unitAtOffset unit 1⟩

/-- All seven directed alpha-1,4 boundaries before degradation. -/
def sourceRingEdges : List DirectedRingEdge := betaUnits.map cutAfter

def sourceDerivedCutEdges : List DirectedRingEdge :=
  (betaUnits.filter fun unit => lPrimaryPattern unit = .hydroxy).map cutAfter

/-- Canonical traversal after the unit-1 cut reaches the unit-4 degraded
terminus. -/
def firstProductUnitPath : List BetaCDUnit := [unit2, unit3, unit4]

/-- The complementary traversal after the unit-4 cut reaches the unit-1
degraded terminus. -/
def secondProductUnitPath : List BetaCDUnit := [unit5, unit6, unit7, unit1]

/-- Source-first cyclic topology audit.  It records all seven nodes, seven
clockwise bonds, the two derived cuts, and the two connected paths after those
cuts. -/
def CutTopologySpec : Prop :=
  betaUnits.length = 7 ∧
  betaUnits.Nodup ∧
  sourceRingEdges =
    [ ⟨unit1, unit2⟩, ⟨unit2, unit3⟩, ⟨unit3, unit4⟩,
      ⟨unit4, unit5⟩, ⟨unit5, unit6⟩, ⟨unit6, unit7⟩,
      ⟨unit7, unit1⟩ ] ∧
  sourceRingEdges.length = 7 ∧
  sourceDerivedCutEdges =
    [⟨unit1, unit2⟩, ⟨unit4, unit5⟩] ∧
  firstProductUnitPath = [unit2, unit3, unit4] ∧
  secondProductUnitPath = [unit5, unit6, unit7, unit1] ∧
  firstProductUnitPath.length = 3 ∧
  secondProductUnitPath.length = 4 ∧
  (firstProductUnitPath ++ secondProductUnitPath).length = 7 ∧
  (firstProductUnitPath ++ secondProductUnitPath).Nodup

theorem cutTopology_spec : CutTopologySpec := by
  unfold CutTopologySpec
  native_decide

/-! ## Formula data transcribed from the complete page-4 product drawing -/

/-- Elemental composition, with sodium separated because it is an adduct. -/
structure Formula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  sodium : ℕ
deriving DecidableEq, Repr

namespace Formula

def zero : Formula := ⟨0, 0, 0, 0⟩

def add (a b : Formula) : Formula :=
  ⟨a.carbon + b.carbon, a.hydrogen + b.hydrogen,
    a.oxygen + b.oxygen, a.sodium + b.sodium⟩

def scale (n : ℕ) (a : Formula) : Formula :=
  ⟨n * a.carbon, n * a.hydrogen, n * a.oxygen, n * a.sodium⟩

end Formula

/-- Formula printed below one intact square-bracketed repeat on page 4. -/
def intactRepeatFormula : Formula := ⟨27, 28, 5, 0⟩

/-- Formula printed below the square-bracketed degraded terminus on page 4. -/
def degradedTerminusFormula : Formula := ⟨22, 25, 4, 0⟩

/-- The separately visible `AcO` group terminating the other boundary.  Here
`AcO = CH3-C(=O)-O`, hence `C2H3O2`. -/
def acetylCapFormula : Formula := ⟨2, 3, 2, 0⟩

/-- One sodium atom in the explicitly requested `[M+Na]+` adduct. -/
def sodiumAdductFormula : Formula := ⟨0, 0, 0, 1⟩

/-- Nontrivial image-to-formula bridge.  The first two equalities transcribe
the labels, while the third checks every atom in the visibly separate AcO cap. -/
def SourceImageFormulaSpec : Prop :=
  intactRepeatFormula = ⟨27, 28, 5, 0⟩ ∧
  degradedTerminusFormula = ⟨22, 25, 4, 0⟩ ∧
  acetylCapFormula = ⟨2, 3, 2, 0⟩ ∧
  sodiumAdductFormula = ⟨0, 0, 0, 1⟩

theorem sourceImageFormula_spec : SourceImageFormulaSpec := by
  unfold SourceImageFormulaSpec
  native_decide

/-! ## Mandatory whole-product component ledger -/

/-- Roles use the controller's fixed component-accounting vocabulary. -/
inductive ComponentRole where
  | core
  | repeatUnit
  | linker
  | substituent
  | terminalGroup
  | guest
  | adduct
  | leavingGroup
  | productFragment
deriving DecidableEq, Repr

inductive AssemblyConnection where
  | covalentAcetoxyBoundary
  | alpha14Glycosidic
  | covalentDegradedBoundary
  | sodiumAdductAssociation
deriving DecidableEq, Repr

/-- Every physical node in the first assembled ion. -/
inductive FirstProductNode where
  | acetylCap
  | intactUnit2
  | intactUnit3
  | degradedUnit4
  | sodiumAdduct
deriving DecidableEq, Fintype, Repr

/-- Every physical node in the second assembled ion. -/
inductive SecondProductNode where
  | acetylCap
  | intactUnit5
  | intactUnit6
  | intactUnit7
  | degradedUnit1
  | sodiumAdduct
deriving DecidableEq, Fintype, Repr

structure LedgerEntry (Node : Type) where
  node : Node
  sourceLocalLabel : String
  formula : Formula
  multiplicity : ℕ
  role : ComponentRole
deriving Repr

structure AssemblyEdge (Node : Type) where
  tail : Node
  head : Node
  connection : AssemblyConnection
deriving Repr

def firstNodeFormula : FirstProductNode → Formula
  | .acetylCap => acetylCapFormula
  | .intactUnit2 => intactRepeatFormula
  | .intactUnit3 => intactRepeatFormula
  | .degradedUnit4 => degradedTerminusFormula
  | .sodiumAdduct => sodiumAdductFormula

def firstNodeRole : FirstProductNode → ComponentRole
  | .acetylCap => .terminalGroup
  | .intactUnit2 => .repeatUnit
  | .intactUnit3 => .repeatUnit
  | .degradedUnit4 => .terminalGroup
  | .sodiumAdduct => .adduct

def secondNodeFormula : SecondProductNode → Formula
  | .acetylCap => acetylCapFormula
  | .intactUnit5 => intactRepeatFormula
  | .intactUnit6 => intactRepeatFormula
  | .intactUnit7 => intactRepeatFormula
  | .degradedUnit1 => degradedTerminusFormula
  | .sodiumAdduct => sodiumAdductFormula

def secondNodeRole : SecondProductNode → ComponentRole
  | .acetylCap => .terminalGroup
  | .intactUnit5 => .repeatUnit
  | .intactUnit6 => .repeatUnit
  | .intactUnit7 => .repeatUnit
  | .degradedUnit1 => .terminalGroup
  | .sodiumAdduct => .adduct

/-- Each visually distinct physical component appears once; repeated chemical
types are separate topology nodes, so every entry has positive multiplicity 1. -/
def firstProductLedger : List (LedgerEntry FirstProductNode) :=
  [ ⟨.acetylCap, "AcO cap on unit 2", acetylCapFormula, 1, .terminalGroup⟩,
    ⟨.intactUnit2, "intact C27H28O5 unit 2", intactRepeatFormula, 1, .repeatUnit⟩,
    ⟨.intactUnit3, "intact C27H28O5 unit 3", intactRepeatFormula, 1, .repeatUnit⟩,
    ⟨.degradedUnit4, "C22H25O4 degraded unit 4", degradedTerminusFormula,
      1, .terminalGroup⟩,
    ⟨.sodiumAdduct, "one sodium adduct", sodiumAdductFormula, 1, .adduct⟩ ]

def secondProductLedger : List (LedgerEntry SecondProductNode) :=
  [ ⟨.acetylCap, "AcO cap on unit 5", acetylCapFormula, 1, .terminalGroup⟩,
    ⟨.intactUnit5, "intact C27H28O5 unit 5", intactRepeatFormula, 1, .repeatUnit⟩,
    ⟨.intactUnit6, "intact C27H28O5 unit 6", intactRepeatFormula, 1, .repeatUnit⟩,
    ⟨.intactUnit7, "intact C27H28O5 unit 7", intactRepeatFormula, 1, .repeatUnit⟩,
    ⟨.degradedUnit1, "C22H25O4 degraded unit 1", degradedTerminusFormula,
      1, .terminalGroup⟩,
    ⟨.sodiumAdduct, "one sodium adduct", sodiumAdductFormula, 1, .adduct⟩ ]

/-- All assembly edges, including each formerly wavy cross-boundary bond and
the noncovalent sodium association, for the first ion. -/
def firstAssemblyEdges : List (AssemblyEdge FirstProductNode) :=
  [ ⟨.acetylCap, .intactUnit2, .covalentAcetoxyBoundary⟩,
    ⟨.intactUnit2, .intactUnit3, .alpha14Glycosidic⟩,
    ⟨.intactUnit3, .degradedUnit4, .covalentDegradedBoundary⟩,
    ⟨.sodiumAdduct, .degradedUnit4, .sodiumAdductAssociation⟩ ]

/-- All assembly edges for the complementary ion. -/
def secondAssemblyEdges : List (AssemblyEdge SecondProductNode) :=
  [ ⟨.acetylCap, .intactUnit5, .covalentAcetoxyBoundary⟩,
    ⟨.intactUnit5, .intactUnit6, .alpha14Glycosidic⟩,
    ⟨.intactUnit6, .intactUnit7, .alpha14Glycosidic⟩,
    ⟨.intactUnit7, .degradedUnit1, .covalentDegradedBoundary⟩,
    ⟨.sodiumAdduct, .degradedUnit1, .sodiumAdductAssociation⟩ ]

def LedgerCoversEveryNodeExactlyOnce
    {Node : Type} [DecidableEq Node]
    (formulaOf : Node → Formula) (roleOf : Node → ComponentRole)
    (ledger : List (LedgerEntry Node)) : Prop :=
  (∀ node : Node,
    (ledger.filter fun entry => entry.node = node).length = 1) ∧
  (∀ entry ∈ ledger,
    0 < entry.multiplicity ∧
    entry.multiplicity = 1 ∧
    entry.formula = formulaOf entry.node ∧
    entry.role = roleOf entry.node)

def FirstComponentLedgerSpec : Prop :=
  Fintype.card FirstProductNode = 5 ∧
  firstProductLedger.length = 5 ∧
  LedgerCoversEveryNodeExactlyOnce
    firstNodeFormula firstNodeRole firstProductLedger ∧
  firstAssemblyEdges =
    [ ⟨.acetylCap, .intactUnit2, .covalentAcetoxyBoundary⟩,
      ⟨.intactUnit2, .intactUnit3, .alpha14Glycosidic⟩,
      ⟨.intactUnit3, .degradedUnit4, .covalentDegradedBoundary⟩,
      ⟨.sodiumAdduct, .degradedUnit4, .sodiumAdductAssociation⟩ ] ∧
  firstAssemblyEdges.length = 4

def SecondComponentLedgerSpec : Prop :=
  Fintype.card SecondProductNode = 6 ∧
  secondProductLedger.length = 6 ∧
  LedgerCoversEveryNodeExactlyOnce
    secondNodeFormula secondNodeRole secondProductLedger ∧
  secondAssemblyEdges =
    [ ⟨.acetylCap, .intactUnit5, .covalentAcetoxyBoundary⟩,
      ⟨.intactUnit5, .intactUnit6, .alpha14Glycosidic⟩,
      ⟨.intactUnit6, .intactUnit7, .alpha14Glycosidic⟩,
      ⟨.intactUnit7, .degradedUnit1, .covalentDegradedBoundary⟩,
      ⟨.sodiumAdduct, .degradedUnit1, .sodiumAdductAssociation⟩ ] ∧
  secondAssemblyEdges.length = 5

theorem firstComponentLedger_spec : FirstComponentLedgerSpec := by
  unfold FirstComponentLedgerSpec LedgerCoversEveryNodeExactlyOnce
  refine ⟨by native_decide, by native_decide, ?_, by rfl,
    by native_decide⟩
  constructor
  · intro node
    cases node <;> native_decide
  · simp [firstProductLedger, firstNodeFormula, firstNodeRole]

theorem secondComponentLedger_spec : SecondComponentLedgerSpec := by
  unfold SecondComponentLedgerSpec LedgerCoversEveryNodeExactlyOnce
  refine ⟨by native_decide, by native_decide, ?_, by rfl,
    by native_decide⟩
  constructor
  · intro node
    cases node <;> native_decide
  · simp [secondProductLedger, secondNodeFormula, secondNodeRole]

def ledgerFormula {Node : Type} (ledger : List (LedgerEntry Node)) : Formula :=
  ledger.foldr
    (fun entry total =>
      Formula.add (Formula.scale entry.multiplicity entry.formula) total)
    Formula.zero

/-- Full ion formula, after all physical nodes in the first ledger are
recombined. -/
def firstIonFormula : Formula := ledgerFormula firstProductLedger

/-- Full ion formula for the complementary ledger. -/
def secondIonFormula : Formula := ledgerFormula secondProductLedger

/-- The whole-product recombinations.  These equalities are deliberately
separate from the final mass calculation. -/
def FormulaRecombinationSpec : Prop :=
  firstIonFormula =
      Formula.add sodiumAdductFormula
        (Formula.add acetylCapFormula
          (Formula.add (Formula.scale 2 intactRepeatFormula)
            degradedTerminusFormula)) ∧
  firstIonFormula = ⟨78, 84, 16, 1⟩ ∧
  secondIonFormula =
      Formula.add sodiumAdductFormula
        (Formula.add acetylCapFormula
          (Formula.add (Formula.scale 3 intactRepeatFormula)
            degradedTerminusFormula)) ∧
  secondIonFormula = ⟨105, 112, 21, 1⟩

theorem formulaRecombination_spec : FormulaRecombinationSpec := by
  unfold FormulaRecombinationSpec
  native_decide

/-! ## Integer atomic masses and the mass-to-charge calculation -/

inductive Element where
  | carbon
  | hydrogen
  | oxygen
  | sodium
deriving DecidableEq, Fintype, Repr

/-- Versioned offline reference record used only to obtain the conventional
atomic weight that is rounded to the integer requested by the problem. -/
structure AtomicWeightReceipt where
  element : Element
  nominalWeight : ℚ
  integerWeight : ℕ
  datasetVersion : String
  datasetSha256 : String
  recordSha256 : String
deriving DecidableEq, Repr

def atomicWeightDatasetVersion : String :=
  "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1"

def atomicWeightDatasetSha256 : String :=
  "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"

def carbonMassReceipt : AtomicWeightReceipt :=
  { element := .carbon
    nominalWeight := 12011 / 1000
    integerWeight := 12
    datasetVersion := atomicWeightDatasetVersion
    datasetSha256 := atomicWeightDatasetSha256
    recordSha256 :=
      "0f558fc72d4299d061e9d29f394ebed43fc8246f7dbdb402bbb2a338cfbe4b8a" }

def hydrogenMassReceipt : AtomicWeightReceipt :=
  { element := .hydrogen
    nominalWeight := 1008 / 1000
    integerWeight := 1
    datasetVersion := atomicWeightDatasetVersion
    datasetSha256 := atomicWeightDatasetSha256
    recordSha256 :=
      "8e5f2e512d11f6c3409197956a4f015f6144f43057a286107064436c64b4bce5" }

def oxygenMassReceipt : AtomicWeightReceipt :=
  { element := .oxygen
    nominalWeight := 15999 / 1000
    integerWeight := 16
    datasetVersion := atomicWeightDatasetVersion
    datasetSha256 := atomicWeightDatasetSha256
    recordSha256 :=
      "d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588" }

def sodiumMassReceipt : AtomicWeightReceipt :=
  { element := .sodium
    nominalWeight := 22990 / 1000
    integerWeight := 23
    datasetVersion := atomicWeightDatasetVersion
    datasetSha256 := atomicWeightDatasetSha256
    recordSha256 :=
      "14234e37d6ac93ded8d1d6f1883bd01f1855b92c90a61fb1370b0bb83f736417" }

def atomicMassReceipt : Element → AtomicWeightReceipt
  | .carbon => carbonMassReceipt
  | .hydrogen => hydrogenMassReceipt
  | .oxygen => oxygenMassReceipt
  | .sodium => sodiumMassReceipt

/-- Nearest-integer characterization fixed before either molecular formula is
substituted. -/
def IsNearestIntegerMass (receipt : AtomicWeightReceipt) : Prop :=
  |receipt.nominalWeight - receipt.integerWeight| < (1 : ℚ) / 2 ∧
  ∀ candidate : ℕ,
    |receipt.nominalWeight - candidate| < (1 : ℚ) / 2 →
      candidate = receipt.integerWeight

def AtomicMassReceiptSpec : Prop :=
  (∀ element : Element,
    (atomicMassReceipt element).element = element ∧
    (atomicMassReceipt element).datasetVersion = atomicWeightDatasetVersion ∧
    (atomicMassReceipt element).datasetSha256 = atomicWeightDatasetSha256 ∧
    IsNearestIntegerMass (atomicMassReceipt element)) ∧
  carbonMassReceipt.nominalWeight = 12011 / 1000 ∧
  hydrogenMassReceipt.nominalWeight = 1008 / 1000 ∧
  oxygenMassReceipt.nominalWeight = 15999 / 1000 ∧
  sodiumMassReceipt.nominalWeight = 22990 / 1000

theorem atomicMassReceipt_spec : AtomicMassReceiptSpec := by
  unfold AtomicMassReceiptSpec
  constructor
  · intro element
    cases element <;>
      norm_num [atomicMassReceipt, carbonMassReceipt, hydrogenMassReceipt,
        oxygenMassReceipt, sodiumMassReceipt, IsNearestIntegerMass,
        abs_lt] at *
    · intro candidate hUpper hLower
      have hUpperNat : candidate < 13 := by
        exact_mod_cast (show (candidate : ℚ) < 13 by linarith)
      have hLowerNat : 11 < candidate := by
        exact_mod_cast (show (11 : ℚ) < (candidate : ℚ) by linarith)
      omega
    · intro candidate hUpper hLower
      have hUpperNat : candidate < 2 := by
        exact_mod_cast (show (candidate : ℚ) < 2 by linarith)
      have hLowerNat : 0 < candidate := by
        exact_mod_cast (show (0 : ℚ) < (candidate : ℚ) by linarith)
      omega
    · intro candidate hUpper hLower
      have hUpperNat : candidate < 17 := by
        exact_mod_cast (show (candidate : ℚ) < 17 by linarith)
      have hLowerNat : 15 < candidate := by
        exact_mod_cast (show (15 : ℚ) < (candidate : ℚ) by linarith)
      omega
    · intro candidate hUpper hLower
      have hUpperNat : candidate < 24 := by
        exact_mod_cast (show (candidate : ℚ) < 24 by linarith)
      have hLowerNat : 22 < candidate := by
        exact_mod_cast (show (22 : ℚ) < (candidate : ℚ) by linarith)
      omega
  · norm_num [carbonMassReceipt, hydrogenMassReceipt, oxygenMassReceipt,
      sodiumMassReceipt]

def integerAtomicMass (element : Element) : ℕ :=
  (atomicMassReceipt element).integerWeight

/-- Integer nominal mass of a complete formula, including the sodium adduct. -/
def integerFormulaMass (formula : Formula) : ℕ :=
  formula.carbon * integerAtomicMass .carbon +
  formula.hydrogen * integerAtomicMass .hydrogen +
  formula.oxygen * integerAtomicMass .oxygen +
  formula.sodium * integerAtomicMass .sodium

inductive AnalysisPhase where
  | massSpectrometerIon
deriving DecidableEq, Repr

structure SodiumAdductIon where
  formula : Formula
  charge : ℤ
  phase : AnalysisPhase
deriving DecidableEq, Repr

def firstFragmentIon : SodiumAdductIon :=
  ⟨firstIonFormula, 1, .massSpectrometerIon⟩

def secondFragmentIon : SodiumAdductIon :=
  ⟨secondIonFormula, 1, .massSpectrometerIon⟩

/-- Exact raw m/z expression; the denominator retains the ion charge rather
than silently assuming it away. -/
noncomputable def massToChargeRaw (ion : SodiumAdductIon) : ℝ :=
  (integerFormulaMass ion.formula : ℝ) / (Int.natAbs ion.charge : ℝ)

noncomputable def firstFragmentMzRaw : ℝ := massToChargeRaw firstFragmentIon

noncomputable def secondFragmentMzRaw : ℝ := massToChargeRaw secondFragmentIon

/-- Source-to-Lean derivation specification for the first requested peak. -/
def FirstFragmentMzDerivationSpec : Prop :=
  FirstComponentLedgerSpec ∧
  FormulaRecombinationSpec ∧
  firstFragmentIon.formula = ⟨78, 84, 16, 1⟩ ∧
  firstFragmentIon.charge = 1 ∧
  Int.natAbs firstFragmentIon.charge = 1 ∧
  firstFragmentMzRaw =
    (((78 : ℝ) * 12 + 84 * 1 + 16 * 16 + 1 * 23) / 1) ∧
  firstFragmentMzRaw = 1299

/-- Source-to-Lean derivation specification for the second requested peak. -/
def SecondFragmentMzDerivationSpec : Prop :=
  SecondComponentLedgerSpec ∧
  FormulaRecombinationSpec ∧
  secondFragmentIon.formula = ⟨105, 112, 21, 1⟩ ∧
  secondFragmentIon.charge = 1 ∧
  Int.natAbs secondFragmentIon.charge = 1 ∧
  secondFragmentMzRaw =
    (((105 : ℝ) * 12 + 112 * 1 + 21 * 16 + 1 * 23) / 1) ∧
  secondFragmentMzRaw = 1731

/-- Requested-output carrier for `first_fragment_mz`. -/
theorem first_fragment_mz_raw_result : FirstFragmentMzDerivationSpec := by
  unfold FirstFragmentMzDerivationSpec
  refine ⟨firstComponentLedger_spec, formulaRecombination_spec, ?_, rfl, rfl,
    ?_, ?_⟩
  · simpa [firstFragmentIon] using formulaRecombination_spec.2.1
  · norm_num [firstFragmentMzRaw, massToChargeRaw, firstFragmentIon,
      integerFormulaMass, integerAtomicMass, atomicMassReceipt,
      carbonMassReceipt, hydrogenMassReceipt, oxygenMassReceipt,
      sodiumMassReceipt, formulaRecombination_spec.2.1]
  · norm_num [firstFragmentMzRaw, massToChargeRaw, firstFragmentIon,
      integerFormulaMass, integerAtomicMass, atomicMassReceipt,
      carbonMassReceipt, hydrogenMassReceipt, oxygenMassReceipt,
      sodiumMassReceipt, formulaRecombination_spec.2.1]

/-- Requested-output carrier for `second_fragment_mz`. -/
theorem second_fragment_mz_raw_result : SecondFragmentMzDerivationSpec := by
  unfold SecondFragmentMzDerivationSpec
  refine ⟨secondComponentLedger_spec, formulaRecombination_spec, ?_, rfl, rfl,
    ?_, ?_⟩
  · simpa [secondFragmentIon] using formulaRecombination_spec.2.2.2
  · norm_num [secondFragmentMzRaw, massToChargeRaw, secondFragmentIon,
      integerFormulaMass, integerAtomicMass, atomicMassReceipt,
      carbonMassReceipt, hydrogenMassReceipt, oxygenMassReceipt,
      sodiumMassReceipt, formulaRecombination_spec.2.2.2]
  · norm_num [secondFragmentMzRaw, massToChargeRaw, secondFragmentIon,
      integerFormulaMass, integerAtomicMass, atomicMassReceipt,
      carbonMassReceipt, hydrogenMassReceipt, oxygenMassReceipt,
      sodiumMassReceipt, formulaRecombination_spec.2.2.2]

/-! ## Exact-integer reporting and combined answer-blind contracts -/

/-- Exact-integer reporting is the identity on the unrounded raw expression. -/
noncomputable def firstFragmentMzReported : ℝ := firstFragmentMzRaw

noncomputable def secondFragmentMzReported : ℝ := secondFragmentMzRaw

def FirstFragmentMzReportedSpec : Prop :=
  firstFragmentMzReported = firstFragmentMzRaw ∧
  firstFragmentMzReported = 1299 ∧
  IChO2026Chem.Reporting.ReportsAtQuantum
    firstFragmentMzRaw firstFragmentMzReported 1

def SecondFragmentMzReportedSpec : Prop :=
  secondFragmentMzReported = secondFragmentMzRaw ∧
  secondFragmentMzReported = 1731 ∧
  IChO2026Chem.Reporting.ReportsAtQuantum
    secondFragmentMzRaw secondFragmentMzReported 1

theorem first_fragment_mz_reportsAtQuantum :
    IChO2026Chem.Reporting.ReportsAtQuantum
      firstFragmentMzRaw firstFragmentMzReported 1 := by
  have hRaw : firstFragmentMzRaw = (1299 : ℝ) :=
    first_fragment_mz_raw_result.2.2.2.2.2.2
  have hReported : firstFragmentMzReported = (1299 : ℝ) := by
    simpa [firstFragmentMzReported] using hRaw
  rw [IChO2026Chem.Reporting.ReportsAtQuantum, hRaw, hReported]
  refine ⟨by norm_num, ⟨1299, by norm_num⟩, ?_⟩
  norm_num

theorem second_fragment_mz_reportsAtQuantum :
    IChO2026Chem.Reporting.ReportsAtQuantum
      secondFragmentMzRaw secondFragmentMzReported 1 := by
  have hRaw : secondFragmentMzRaw = (1731 : ℝ) :=
    second_fragment_mz_raw_result.2.2.2.2.2.2
  have hReported : secondFragmentMzReported = (1731 : ℝ) := by
    simpa [secondFragmentMzReported] using hRaw
  rw [IChO2026Chem.Reporting.ReportsAtQuantum, hRaw, hReported]
  refine ⟨by norm_num, ⟨1731, by norm_num⟩, ?_⟩
  norm_num

theorem first_fragment_mz_reported_result : FirstFragmentMzReportedSpec := by
  unfold FirstFragmentMzReportedSpec
  refine ⟨rfl, ?_, first_fragment_mz_reportsAtQuantum⟩
  simpa [firstFragmentMzReported] using
    first_fragment_mz_raw_result.2.2.2.2.2.2

theorem second_fragment_mz_reported_result : SecondFragmentMzReportedSpec := by
  unfold SecondFragmentMzReportedSpec
  refine ⟨rfl, ?_, second_fragment_mz_reportsAtQuantum⟩
  simpa [secondFragmentMzReported] using
    second_fragment_mz_raw_result.2.2.2.2.2.2

/-- Assumptions/source evidence and both exact unrounded targets. -/
def RawResultSpec : Prop :=
  SourceArrowSpec ∧
  stagedTransformationUse = .qualitativeNamedTransformOnly ∧
  PreviousPartLSpec ∧
  CutTopologySpec ∧
  SourceImageFormulaSpec ∧
  AtomicMassReceiptSpec ∧
  FirstFragmentMzDerivationSpec ∧
  SecondFragmentMzDerivationSpec

/-- The reporting contract covers both requested outputs in source order. -/
def ReportedResultSpec : Prop :=
  RawResultSpec ∧
  FirstFragmentMzReportedSpec ∧
  SecondFragmentMzReportedSpec

theorem raw_result : RawResultSpec := by
  unfold RawResultSpec
  exact ⟨sourceArrow_spec, rfl, previousPartL_derived, cutTopology_spec,
    sourceImageFormula_spec, atomicMassReceipt_spec,
    first_fragment_mz_raw_result, second_fragment_mz_raw_result⟩

theorem reported_result : ReportedResultSpec := by
  exact ⟨raw_result, first_fragment_mz_reported_result,
    second_fragment_mz_reported_result⟩

/- Contract hashes are filled from the solve artifact after its exact payload
is finalized. -/

theorem blindRawResultContract :
    ("9d2496db078f59c49fbaa769110df68d6631d06a88c51aab60fa1512d8b56d77" : String) =
        "9d2496db078f59c49fbaa769110df68d6631d06a88c51aab60fa1512d8b56d77" ∧
      IChO2026Problems.T9A7.RawResultSpec := by
  exact ⟨rfl, raw_result⟩

theorem blindReportedResultContract :
    ("fe7af89220fad31596646ba2cebbeff4f947e3e831a8e7e492ea27eb638757f8" : String) =
        "fe7af89220fad31596646ba2cebbeff4f947e3e831a8e7e492ea27eb638757f8" ∧
      IChO2026Problems.T9A7.ReportedResultSpec := by
  exact ⟨rfl, reported_result⟩

end T9A7
end IChO2026Problems
