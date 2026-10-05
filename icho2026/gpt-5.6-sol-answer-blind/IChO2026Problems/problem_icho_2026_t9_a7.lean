import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T9, part A7

This file formalizes the two nominal-mass sodium-adduct peaks shown in the
problem-only images.  In particular, the formula printed under either bracket
on page 4 is treated as a *component contribution*, not as a whole product.

The previous-part structure of `L` is derived locally: the seven-membered
β-cyclodextrin ring has primary hydroxy groups at units 1 and 4.  Cutting the
two indicated outgoing glycosidic boundaries gives a three-residue arc and a
four-residue arc.  Each degradation product therefore has one acetoxy cap, one
terminal `C₂₂H₂₅O₄` product fragment, and respectively two or three
`C₂₇H₂₈O₅` repeat residues.  A sodium component and charge `+1` are then added
for `[M+Na]⁺`.

The staged reaction is used only as the source-depicted qualitative named
transformation (`qualitative_named_transform_only`): no yield, completeness,
sole-product claim, phase balance, or omitted-stream claim is made here.
-/

namespace IChO2026Problems
namespace ProblemIcho2026T9A7

inductive EvidenceProvenance where
  | problemText
  | problemImage
  | problemStatedFallback
  | trustedGeneralLaw
  | derivedTheorem
deriving DecidableEq, Repr

/-- Provenance of every finite topology/count or image readout used below. -/
structure SourceProvenanceAudit where
  precursorUnitCount : List EvidenceProvenance
  previousPartStructure : List EvidenceProvenance
  precursorRingTopology : List EvidenceProvenance
  degradationCuts : List EvidenceProvenance
  productArcPartition : List EvidenceProvenance
  componentFormulaReadouts : List EvidenceProvenance
  acetoxyAtomCount : List EvidenceProvenance
  sodiumAdductAndCharge : List EvidenceProvenance
  integerAtomicMasses : List EvidenceProvenance

def sourceProvenanceAudit : SourceProvenanceAudit :=
  { precursorUnitCount := [.problemText]
    previousPartStructure := [.problemText, .problemImage, .derivedTheorem]
    precursorRingTopology := [.problemText, .problemImage]
    degradationCuts := [.problemImage, .derivedTheorem]
    productArcPartition := [.derivedTheorem]
    componentFormulaReadouts := [.problemImage]
    acetoxyAtomCount := [.problemImage, .trustedGeneralLaw]
    sodiumAdductAndCharge := [.problemText, .problemImage]
    integerAtomicMasses := [.problemText, .trustedGeneralLaw] }

def SourceProvenanceAuditComplete : Prop :=
  sourceProvenanceAudit.precursorUnitCount ≠ [] ∧
  sourceProvenanceAudit.previousPartStructure ≠ [] ∧
  sourceProvenanceAudit.precursorRingTopology ≠ [] ∧
  sourceProvenanceAudit.degradationCuts ≠ [] ∧
  sourceProvenanceAudit.productArcPartition ≠ [] ∧
  sourceProvenanceAudit.componentFormulaReadouts ≠ [] ∧
  sourceProvenanceAudit.acetoxyAtomCount ≠ [] ∧
  sourceProvenanceAudit.sodiumAdductAndCharge ≠ [] ∧
  sourceProvenanceAudit.integerAtomicMasses ≠ []

theorem sourceProvenanceAuditComplete : SourceProvenanceAuditComplete := by
  unfold SourceProvenanceAuditComplete
  decide

/-! ## Small target-local formula interface -/

/-- Atom-count formula sufficient for the C/H/O/Na species in this target. -/
structure NominalFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  sodium : ℕ
deriving DecidableEq, Repr

namespace NominalFormula

def zero : NominalFormula := ⟨0, 0, 0, 0⟩

def add (a b : NominalFormula) : NominalFormula :=
  ⟨a.carbon + b.carbon,
   a.hydrogen + b.hydrogen,
   a.oxygen + b.oxygen,
   a.sodium + b.sodium⟩

instance : Add NominalFormula where
  add := add

def scale (n : ℕ) (f : NominalFormula) : NominalFormula :=
  ⟨n * f.carbon, n * f.hydrogen, n * f.oxygen, n * f.sodium⟩

/- The problem requests integer atomic masses.  These are the mass numbers
   from the pinned AME2020 subset: C-12, H-1, O-16, and Na-23. -/
def carbonIntegerMass : ℕ := 12
def hydrogenIntegerMass : ℕ := 1
def oxygenIntegerMass : ℕ := 16
def sodiumIntegerMass : ℕ := 23

/-- Nominal mass obtained end-to-end from atom counts and integer masses. -/
def massNumber (f : NominalFormula) : ℕ :=
  f.carbon * carbonIntegerMass +
  f.hydrogen * hydrogenIntegerMass +
  f.oxygen * oxygenIntegerMass +
  f.sodium * sodiumIntegerMass

end NominalFormula

/-! ## Inline derivation of the previous-part structure `L` -/

inductive LUnit where
  | u1 | u2 | u3 | u4 | u5 | u6 | u7
deriving DecidableEq, Fintype, Repr

inductive PrimarySubstituent where
  | hydroxy
  | benzyloxy
deriving DecidableEq, Repr

/-- The source-stated directing relation, normalized so unit 1 directs unit 4. -/
def directedPrimaryTarget : LUnit → LUnit
  | .u1 => .u4
  | .u2 => .u5
  | .u3 => .u6
  | .u4 => .u7
  | .u5 => .u1
  | .u6 => .u2
  | .u7 => .u3

/-- Primary-rim substitution in the locally derived candidate `L`. -/
def lPrimarySubstituent : LUnit → PrimarySubstituent
  | .u1 | .u4 => .hydroxy
  | _ => .benzyloxy

/-- All fourteen secondary hydroxy groups were benzylated by the source arrow. -/
def lSecondaryBenzyloxyCount : ℕ := 14

def lFreePrimaryUnits : List LUnit := [.u1, .u4]

/-- Nontrivial specification of the locally derived answer to prerequisite A5. -/
def LStructureSpec : Prop :=
  lFreePrimaryUnits.Nodup ∧
  lFreePrimaryUnits.length = 2 ∧
  directedPrimaryTarget .u1 = .u4 ∧
  lPrimarySubstituent .u1 = .hydroxy ∧
  lPrimarySubstituent .u4 = .hydroxy ∧
  (∀ u ∈ ([.u2, .u3, .u5, .u6, .u7] : List LUnit),
    lPrimarySubstituent u = .benzyloxy) ∧
  lSecondaryBenzyloxyCount = 14

theorem lStructureSpec : LStructureSpec := by
  simp [LStructureSpec, lFreePrimaryUnits, directedPrimaryTarget,
    lPrimarySubstituent, lSecondaryBenzyloxyCount]

abbrev UnitBoundary := LUnit × LUnit

/-- The seven directed α-1,4 boundaries of the precursor ring. -/
def precursorRingBoundaries : Finset UnitBoundary :=
  [(.u1, .u2), (.u2, .u3), (.u3, .u4), (.u4, .u5),
   (.u5, .u6), (.u6, .u7), (.u7, .u1)].toFinset

/-- The two outgoing cross-boundary bonds cut at hydroxy units 1 and 4. -/
def degradationCutBoundaries : Finset UnitBoundary :=
  [(.u1, .u2), (.u4, .u5)].toFinset

/-- Retained precursor boundaries in the three-node product. -/
def firstRetainedBoundaries : Finset UnitBoundary :=
  [(.u2, .u3), (.u3, .u4)].toFinset

/-- Retained precursor boundaries in the four-node product. -/
def secondRetainedBoundaries : Finset UnitBoundary :=
  [(.u5, .u6), (.u6, .u7), (.u7, .u1)].toFinset

def firstProductPrecursorUnits : Finset LUnit := [.u2, .u3, .u4].toFinset
def secondProductPrecursorUnits : Finset LUnit := [.u5, .u6, .u7, .u1].toFinset

/-- The cuts partition every precursor ring boundary into exactly one class. -/
theorem precursorBoundaryPartition :
    precursorRingBoundaries =
      degradationCutBoundaries ∪
        (firstRetainedBoundaries ∪ secondRetainedBoundaries) := by
  decide

/-- The source-derived arcs contain three and four nodes and cover the ring. -/
theorem productArcPartition :
    firstProductPrecursorUnits.card = 3 ∧
    secondProductPrecursorUnits.card = 4 ∧
    Disjoint firstProductPrecursorUnits secondProductPrecursorUnits ∧
    firstProductPrecursorUnits ∪ secondProductPrecursorUnits = Finset.univ := by
  decide

/-! ## Source-image components and whole-product ledgers -/

/-- Formula printed under a protected repeat residue on page 4. -/
def protectedRepeatFormula : NominalFormula := ⟨27, 28, 5, 0⟩

/-- Formula printed under the terminal degradation fragment on page 4. -/
def terminalFragmentFormula : NominalFormula := ⟨22, 25, 4, 0⟩

/-- Atom ledger of the visually separate `AcO` terminal cap. -/
def acetoxyCapFormula : NominalFormula := ⟨2, 3, 2, 0⟩

/-- Atom ledger for the sodium adduct component. -/
def sodiumAdductFormula : NominalFormula := ⟨0, 0, 0, 1⟩

inductive SourceImageLocator where
  | page3LPrecursor
  | page4Hexo5EnoseArrow
deriving DecidableEq, Repr

inductive ReactionDirection where
  | forward
deriving DecidableEq, Repr

inductive StagedTransformationUse where
  | qualitativeNamedTransformOnly
deriving DecidableEq, Repr

inductive NamedChemicalRole where
  | precursorL
  | protectedRepeatResidue
  | terminalDegradationFragment
  | acetoxyTerminalCap
  | sodiumAdductIon
deriving DecidableEq, Repr

/-- Source-bound carrier for the depicted transformation.  It records only
    the roles, direction, cuts, and formula contributions actually used by
    this calculation; omitted protocol, phases, yields, and byproducts remain
    unspecified. -/
structure DepictedDegradationArrow where
  precursorLocator : SourceImageLocator
  arrowLocator : SourceImageLocator
  useClassification : StagedTransformationUse
  direction : ReactionDirection
  reactantRole : NamedChemicalRole
  degradationProductRoles : List NamedChemicalRole
  cutBoundaries : Finset UnitBoundary
  repeatContribution : NominalFormula
  terminalContribution : NominalFormula
  capContribution : NominalFormula
  analysedAdductRole : NamedChemicalRole
  analysedAdductContribution : NominalFormula

def depictedDegradationArrow : DepictedDegradationArrow :=
  { precursorLocator := .page3LPrecursor
    arrowLocator := .page4Hexo5EnoseArrow
    useClassification := .qualitativeNamedTransformOnly
    direction := .forward
    reactantRole := .precursorL
    degradationProductRoles :=
      [.protectedRepeatResidue, .terminalDegradationFragment,
       .acetoxyTerminalCap]
    cutBoundaries := degradationCutBoundaries
    repeatContribution := protectedRepeatFormula
    terminalContribution := terminalFragmentFormula
    capContribution := acetoxyCapFormula
    analysedAdductRole := .sodiumAdductIon
    analysedAdductContribution := sodiumAdductFormula }

/-- Compatibility contract for the exact page-3/page-4 source arrow. -/
def DepictedDegradationCompatibility : Prop :=
  depictedDegradationArrow.precursorLocator = .page3LPrecursor ∧
  depictedDegradationArrow.arrowLocator = .page4Hexo5EnoseArrow ∧
  depictedDegradationArrow.useClassification =
    .qualitativeNamedTransformOnly ∧
  depictedDegradationArrow.direction = .forward ∧
  depictedDegradationArrow.reactantRole = .precursorL ∧
  depictedDegradationArrow.cutBoundaries = degradationCutBoundaries ∧
  depictedDegradationArrow.repeatContribution = ⟨27, 28, 5, 0⟩ ∧
  depictedDegradationArrow.terminalContribution = ⟨22, 25, 4, 0⟩ ∧
  depictedDegradationArrow.capContribution = ⟨2, 3, 2, 0⟩ ∧
  depictedDegradationArrow.analysedAdductRole = .sodiumAdductIon ∧
  depictedDegradationArrow.analysedAdductContribution = ⟨0, 0, 0, 1⟩

theorem depictedDegradationCompatibility :
    DepictedDegradationCompatibility := by
  unfold DepictedDegradationCompatibility
  decide

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

structure ComponentLedgerEntry (Node : Type) where
  node : Node
  formula : NominalFormula
  multiplicity : ℕ
  multiplicityPositive : 0 < multiplicity
  role : ComponentRole

inductive AssemblyBondKind where
  | covalentAssembly
  | sodiumAssociation
deriving DecidableEq, Repr

structure AssemblyEdge (Node : Type) where
  left : Node
  right : Node
  kind : AssemblyBondKind
deriving DecidableEq, Repr

inductive FirstProductNode where
  | acetoxyCapAtU2
  | repeatU2
  | repeatU3
  | terminalU4
  | sodiumAdduct
deriving DecidableEq, Fintype, Repr

inductive SecondProductNode where
  | acetoxyCapAtU5
  | repeatU5
  | repeatU6
  | repeatU7
  | terminalU1
  | sodiumAdduct
deriving DecidableEq, Fintype, Repr

def firstProductLedger : List (ComponentLedgerEntry FirstProductNode) :=
  [ { node := .acetoxyCapAtU2
      formula := acetoxyCapFormula
      multiplicity := 1
      multiplicityPositive := by decide
      role := .terminalGroup },
    { node := .repeatU2
      formula := protectedRepeatFormula
      multiplicity := 1
      multiplicityPositive := by decide
      role := .repeatUnit },
    { node := .repeatU3
      formula := protectedRepeatFormula
      multiplicity := 1
      multiplicityPositive := by decide
      role := .repeatUnit },
    { node := .terminalU4
      formula := terminalFragmentFormula
      multiplicity := 1
      multiplicityPositive := by decide
      role := .productFragment },
    { node := .sodiumAdduct
      formula := sodiumAdductFormula
      multiplicity := 1
      multiplicityPositive := by decide
      role := .adduct } ]

def secondProductLedger : List (ComponentLedgerEntry SecondProductNode) :=
  [ { node := .acetoxyCapAtU5
      formula := acetoxyCapFormula
      multiplicity := 1
      multiplicityPositive := by decide
      role := .terminalGroup },
    { node := .repeatU5
      formula := protectedRepeatFormula
      multiplicity := 1
      multiplicityPositive := by decide
      role := .repeatUnit },
    { node := .repeatU6
      formula := protectedRepeatFormula
      multiplicity := 1
      multiplicityPositive := by decide
      role := .repeatUnit },
    { node := .repeatU7
      formula := protectedRepeatFormula
      multiplicity := 1
      multiplicityPositive := by decide
      role := .repeatUnit },
    { node := .terminalU1
      formula := terminalFragmentFormula
      multiplicity := 1
      multiplicityPositive := by decide
      role := .productFragment },
    { node := .sodiumAdduct
      formula := sodiumAdductFormula
      multiplicity := 1
      multiplicityPositive := by decide
      role := .adduct } ]

/-- Every visual/ionic component is connected: cap → repeats → terminal,
    together with the noncovalent sodium-adduct association. -/
def firstProductAssemblyEdges : List (AssemblyEdge FirstProductNode) :=
  [ ⟨.acetoxyCapAtU2, .repeatU2, .covalentAssembly⟩,
    ⟨.repeatU2, .repeatU3, .covalentAssembly⟩,
    ⟨.repeatU3, .terminalU4, .covalentAssembly⟩,
    ⟨.sodiumAdduct, .terminalU4, .sodiumAssociation⟩ ]

def secondProductAssemblyEdges : List (AssemblyEdge SecondProductNode) :=
  [ ⟨.acetoxyCapAtU5, .repeatU5, .covalentAssembly⟩,
    ⟨.repeatU5, .repeatU6, .covalentAssembly⟩,
    ⟨.repeatU6, .repeatU7, .covalentAssembly⟩,
    ⟨.repeatU7, .terminalU1, .covalentAssembly⟩,
    ⟨.sodiumAdduct, .terminalU1, .sodiumAssociation⟩ ]

/-- Recombine each individual ledger node exactly once. -/
def ledgerFormula {Node : Type} (ledger : List (ComponentLedgerEntry Node)) :
    NominalFormula :=
  ledger.foldl
    (fun total entry =>
      total + NominalFormula.scale entry.multiplicity entry.formula)
    NominalFormula.zero

def firstProductAdductFormula : NominalFormula := ledgerFormula firstProductLedger
def secondProductAdductFormula : NominalFormula := ledgerFormula secondProductLedger

/-- Each first-product node occurs exactly once, with multiplicity one. -/
theorem firstLedgerComponentAccounting :
    (firstProductLedger.map (fun e => e.node)).Nodup ∧
    (firstProductLedger.map (fun e => e.node)).toFinset = Finset.univ ∧
    firstProductLedger.map (fun e => e.multiplicity) = [1, 1, 1, 1, 1] := by
  decide

/-- Each second-product node occurs exactly once, with multiplicity one. -/
theorem secondLedgerComponentAccounting :
    (secondProductLedger.map (fun e => e.node)).Nodup ∧
    (secondProductLedger.map (fun e => e.node)).toFinset = Finset.univ ∧
    secondProductLedger.map (fun e => e.multiplicity) = [1, 1, 1, 1, 1, 1] := by
  decide

/-- Whole-product formula after the first ledger is recombined. -/
theorem firstAssemblyRecombination :
    firstProductAdductFormula = ⟨78, 84, 16, 1⟩ := by
  decide

/-- Whole-product formula after the second ledger is recombined. -/
theorem secondAssemblyRecombination :
    secondProductAdductFormula = ⟨105, 112, 21, 1⟩ := by
  decide

/-! ## Singly charged sodium adducts and requested outputs -/

structure NominalIon where
  formula : NominalFormula
  charge : ℤ
  chargeNonzero : charge ≠ 0

def NominalIon.mz (ion : NominalIon) : ℕ :=
  NominalFormula.massNumber ion.formula / ion.charge.natAbs

def firstProductSodiumAdduct : NominalIon :=
  ⟨firstProductAdductFormula, 1, by decide⟩

def secondProductSodiumAdduct : NominalIon :=
  ⟨secondProductAdductFormula, 1, by decide⟩

/-- Requested output carrier: nominal `m/z` of the three-residue `[M+Na]⁺`. -/
def firstFragmentMZ : ℕ := firstProductSodiumAdduct.mz

/-- Requested output carrier: nominal `m/z` of the four-residue `[M+Na]⁺`. -/
def secondFragmentMZ : ℕ := secondProductSodiumAdduct.mz

/-- Exact real carrier used at the reporting boundary. -/
def firstFragmentRawMZ : ℝ := firstFragmentMZ

/-- Exact real carrier used at the reporting boundary. -/
def secondFragmentRawMZ : ℝ := secondFragmentMZ

/-- The raw first output exposes all component and integer-mass arithmetic. -/
def FirstFragmentRawDerivation : Prop :=
  firstFragmentMZ =
    (2 * (27 * 12 + 28 * 1 + 5 * 16) +
       (22 * 12 + 25 * 1 + 4 * 16) +
       (2 * 12 + 3 * 1 + 2 * 16) + 23) / 1

/-- The raw second output exposes all component and integer-mass arithmetic. -/
def SecondFragmentRawDerivation : Prop :=
  secondFragmentMZ =
    (3 * (27 * 12 + 28 * 1 + 5 * 16) +
       (22 * 12 + 25 * 1 + 4 * 16) +
       (2 * 12 + 3 * 1 + 2 * 16) + 23) / 1

theorem firstFragmentRawDerivation : FirstFragmentRawDerivation := by
  unfold FirstFragmentRawDerivation
  decide

theorem secondFragmentRawDerivation : SecondFragmentRawDerivation := by
  unfold SecondFragmentRawDerivation
  decide

/-- Exact-integer first peak derived from the whole-product ledger. -/
theorem firstFragmentMZ_value : firstFragmentMZ = 1299 := by
  decide

/-- Exact-integer second peak derived from the whole-product ledger. -/
theorem secondFragmentMZ_value : secondFragmentMZ = 1731 := by
  decide

/-- Joint raw result contract, because the source requests two scalars. -/
def RawPeakResult : Prop :=
  FirstFragmentRawDerivation ∧ SecondFragmentRawDerivation

theorem rawPeakResult : RawPeakResult := by
  exact ⟨firstFragmentRawDerivation, secondFragmentRawDerivation⟩

/-- Joint exact reported-result contract covering both requested outputs. -/
def ReportedPeakResult : Prop :=
  firstFragmentMZ = 1299 ∧ secondFragmentMZ = 1731

theorem reportedPeakResult : ReportedPeakResult := by
  exact ⟨firstFragmentMZ_value, secondFragmentMZ_value⟩

/- The controller declares these outputs as `kind = integer` with policy
   `exact_integer`, so they are certified primarily by the exact equalities
   above rather than by a decimal/significant-figure certificate.  Quantum 1
   below is an additional compatibility theorem for the shared relation. -/
theorem firstFragmentReporting :
    IChO2026Chem.Reporting.ReportsAtQuantum
      firstFragmentRawMZ 1299 1 := by
  have hraw : firstFragmentRawMZ = (1299 : ℝ) := by
    norm_num [firstFragmentRawMZ, firstFragmentMZ_value]
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  rw [hraw]
  refine ⟨by norm_num, ⟨1299, by norm_num⟩, ?_⟩
  norm_num

theorem secondFragmentReporting :
    IChO2026Chem.Reporting.ReportsAtQuantum
      secondFragmentRawMZ 1731 1 := by
  have hraw : secondFragmentRawMZ = (1731 : ℝ) := by
    norm_num [secondFragmentRawMZ, secondFragmentMZ_value]
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  rw [hraw]
  refine ⟨by norm_num, ⟨1731, by norm_num⟩, ?_⟩
  norm_num

end ProblemIcho2026T9A7
end IChO2026Problems
