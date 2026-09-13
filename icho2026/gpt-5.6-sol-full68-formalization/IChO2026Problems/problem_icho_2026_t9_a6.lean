import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, theory problem 9, part 6

The source asks for the number of constitutional linkage isomers of the
depicted beta-cyclodextrin homodimer.  The previous part is not imported: its
needed conclusion is reconstructed below from the seven-unit source diagram,
the two successive DIBAL-H debenzylations, and the stated unit-1-to-unit-4
directing rule.

Assumption/target split:

* source side: beta-CD has seven directionally ordered glucose units; after the
  first primary debenzylation at unit 1, the available unit 4 is the site of the
  directed second debenzylation; the product diagram has one linker ether and
  one remaining primary alcohol on each otherwise benzylated beta-CD half;
* target side: count the linkage connectivities after identifying products
  that differ only by swapping the two identical ends of the saturated linker.

The transformation arrows are used only as qualitative named transformations.
No yield, sole-product, material-balance, or omitted-stream assertion is made.
-/

namespace IChO2026Problems.ProblemIcho2026T9A6

/-- Permitted origins for the finite domains used in this source-bound count. -/
inductive CandidateDomainProvenance where
  | problemText
  | problemImage
  | derivedTheorem
  deriving DecidableEq, Repr

/-- How a depicted staged transformation is used by this formalization. -/
inductive StagedTransformationUse where
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
  | notStagedTransformation
  deriving DecidableEq, Repr

/-- The DIBAL-H/alkylation/metathesis/hydrogenation scheme is used only to
retain the identity of an attachment site through the depicted arrows. -/
def stagedTransformationUse : StagedTransformationUse :=
  .qualitativeNamedTransformOnly

/-- The problem text states that beta-CD contains seven glucose units. -/
def betaCDUnitCount : ℕ := 7

/-- A directionally numbered glucose unit of beta-CD.  Lean indices `0` and
`3` below represent the problem's one-based units 1 and 4. -/
abbrev BetaCDUnit := Fin betaCDUnitCount

def unit1 : BetaCDUnit := ⟨0, by decide⟩

def unit4 : BetaCDUnit := ⟨3, by decide⟩

/-- The two directed cyclic offsets occurring after one of L's alcohols is
chosen for linkage. -/
def offset3 : BetaCDUnit := ⟨3, by decide⟩

def offset4 : BetaCDUnit := ⟨4, by decide⟩

/-- The source image shows one primary hydroxyl position per glucose unit. -/
def betaCDPrimaryPositionCount : ℕ := betaCDUnitCount

/-- The source image groups the two secondary positions per unit as `(OH)₁₄`. -/
def betaCDSecondaryPositionCount : ℕ := 2 * betaCDUnitCount

/-- Substitution states needed to recount the primary-rim boxes in the figure. -/
inductive PrimarySubstituent where
  | benzylEther
  | alcohol
  | linkerEther
  deriving DecidableEq, Repr

/-- A complete assignment of one primary-rim substituent to each of the seven
beta-CD glucose units. -/
structure PrimaryRimPattern where
  substituent : BetaCDUnit → PrimarySubstituent

/-- The intermediate immediately before the two depicted DIBAL-H events has a
benzyl ether at every primary position. -/
def perbenzylatedPrimaryRim : PrimaryRimPattern where
  substituent := fun _ => .benzylEther

/-- The qualitative effect of one reductive debenzylation at a named primary
site; all other primary substituents are retained. -/
def deprotectPrimaryAt (p : PrimaryRimPattern) (site : BetaCDUnit) :
    PrimaryRimPattern where
  substituent := fun u => if u = site then .alcohol else p.substituent u

/-- The first of the two DIBAL-H equivalents creates the initiating protic
group.  Rotational symmetry lets that unit be named unit 1 as in the source. -/
def afterFirstDebenzylation : PrimaryRimPattern :=
  deprotectPrimaryAt perbenzylatedPrimaryRim unit1

/-- Inline reconstruction of compound L from part 9.5: because unit 4 is still
available, the unit-1 alcohol directs the next debenzylation there. -/
def sinayLPrimaryRim : PrimaryRimPattern :=
  deprotectPrimaryAt afterFirstDebenzylation unit4

def alcoholSites (p : PrimaryRimPattern) : Finset BetaCDUnit :=
  Finset.univ.filter fun u => p.substituent u = .alcohol

def benzylEtherSites (p : PrimaryRimPattern) : Finset BetaCDUnit :=
  Finset.univ.filter fun u => p.substituent u = .benzylEther

/-- The two source-derived primary alcohol sites of L. -/
def sinayLAlcoholSites : Finset BetaCDUnit := {unit1, unit4}

/-- Provenance for the attachment-site domain: the two-site carrier is derived
from the problem text and image through `sinayLPrimaryRim`, rather than assumed
as an answer-shaped candidate set. -/
def sinayLAlcoholSiteDomainProvenance : CandidateDomainProvenance :=
  .derivedTheorem

/-- A site at which the mono-alkylation shown in the dimer scheme can attach
the linker to one molecule of L. -/
abbrev LAttachmentSite := {u : BetaCDUnit // u ∈ alcoholSites sinayLPrimaryRim}

def attachmentAtUnit1 : LAttachmentSite :=
  ⟨unit1, by decide⟩

def attachmentAtUnit4 : LAttachmentSite :=
  ⟨unit4, by decide⟩

/-- If one of L's two primary alcohols is converted to the linker ether, this
is the primary alcohol left free in the depicted dimer. -/
def remainingAlcohol (linked : LAttachmentSite) : BetaCDUnit :=
  if linked.1 = unit1 then unit4 else unit1

/-- Directed cyclic displacement from the linker-bearing site to the remaining
free alcohol.  Addition/subtraction on `Fin 7` is modulo seven. -/
def attachmentOrientation (linked : LAttachmentSite) : BetaCDUnit :=
  remainingAlcohol linked - linked.1

/-- Full inline A5 specification needed by A6.  Besides the two alcohol sites,
it records the five remaining primary benzyl ethers, all fourteen secondary
benzyl ethers, and the two unequal directed offsets distinguishing attachment
at unit 1 from attachment at unit 4. -/
def SinayLStructureSpec : Prop :=
  alcoholSites afterFirstDebenzylation = {unit1} ∧
  alcoholSites sinayLPrimaryRim = sinayLAlcoholSites ∧
  (benzylEtherSites sinayLPrimaryRim).card = 5 ∧
  betaCDSecondaryPositionCount = 14 ∧
  Fintype.card LAttachmentSite = 2 ∧
  attachmentOrientation attachmentAtUnit1 = offset3 ∧
  attachmentOrientation attachmentAtUnit4 = offset4 ∧
  attachmentAtUnit1 ≠ attachmentAtUnit4

/-- Problem-only reconstruction of the previous-part structure of L. -/
theorem sinayLStructure_inline : SinayLStructureSpec := by
  unfold SinayLStructureSpec
  decide

/-- The source-derived two attachment choices on a single L molecule. -/
theorem lAttachmentSite_card : Fintype.card LAttachmentSite = 2 := by
  exact sinayLStructure_inline.2.2.2.2.1

/-- The two choices are constitutionally distinct on the directed seven-cycle:
their linker-to-free-OH offsets are respectively three and four. -/
theorem lAttachmentSite_orientations :
    attachmentOrientation attachmentAtUnit1 = offset3 ∧
      attachmentOrientation attachmentAtUnit4 = offset4 ∧
      attachmentOrientation attachmentAtUnit1 ≠
        attachmentOrientation attachmentAtUnit4 := by
  decide

/-- A final homodimer connectivity is an unordered pair of single-molecule
attachment choices.  `Sym2` exactly quotients the ordered choices by swapping
the two identical beta-CD/linker ends while allowing the two choices to agree. -/
abbrev DimerLinkageIsomer := Sym2 LAttachmentSite

/-- Provenance for the exhaustive dimer domain.  It is derived from the two
source-bounded L choices and the end-swap quotient embodied by `Sym2`. -/
def dimerLinkageDomainProvenance : CandidateDomainProvenance :=
  .derivedTheorem

/-- Exact, unreported count carrier requested by part 9.6. -/
def rawDimerIsomerCount : ℕ := Fintype.card DimerLinkageIsomer

/-- Stars-and-bars expression for unordered pairs with repetition. -/
def rawDimerIsomerCountFormula : ℕ :=
  Nat.choose (Fintype.card LAttachmentSite + 1) 2

/-- Source-to-Lean raw-result proposition.  It keeps the inline A5 conclusion,
the general `Sym2` cardinality formula, and its exact evaluation together. -/
def DimerIsomerCountRawSpec : Prop :=
  SinayLStructureSpec ∧
  rawDimerIsomerCount = rawDimerIsomerCountFormula ∧
  rawDimerIsomerCountFormula = Nat.choose (2 + 1) 2 ∧
  rawDimerIsomerCount = 3

/-- The unordered-pair carrier has the standard stars-and-bars cardinality. -/
theorem dimerLinkage_starsAndBars :
    rawDimerIsomerCount = rawDimerIsomerCountFormula := by
  simpa [rawDimerIsomerCount, rawDimerIsomerCountFormula] using
    (Sym2.card (α := LAttachmentSite))

/-- Raw exact-integer result, derived from the problem-defined carrier. -/
theorem dimer_isomer_count_raw_result : DimerIsomerCountRawSpec := by
  have formula_eq :
      rawDimerIsomerCountFormula = Nat.choose (2 + 1) 2 := by
    change Nat.choose (Fintype.card LAttachmentSite + 1) 2 =
      Nat.choose (2 + 1) 2
    rw [lAttachmentSite_card]
  refine ⟨sinayLStructure_inline, dimerLinkage_starsAndBars, ?_, ?_⟩
  · exact formula_eq
  · calc
      rawDimerIsomerCount = rawDimerIsomerCountFormula :=
        dimerLinkage_starsAndBars
      _ = Nat.choose (2 + 1) 2 := formula_eq
      _ = 3 := by norm_num

/-- The exact-integer reporting operation is identity; it performs no decimal
rounding and does not insert a selected value independently of the raw count. -/
def reportedDimerIsomerCount : ℕ := rawDimerIsomerCount

def DimerIsomerCountReportedSpec : Prop :=
  reportedDimerIsomerCount = rawDimerIsomerCount ∧
  reportedDimerIsomerCount = 3

/-- Requested output carrier: the exact reported number of constitutional
linkage isomers. -/
theorem dimer_isomer_count_reported_result :
    DimerIsomerCountReportedSpec := by
  constructor
  · rfl
  · exact dimer_isomer_count_raw_result.2.2.2

/-- Real-valued views used solely by the shared deterministic reporting API. -/
def rawDimerIsomerCountReal : ℝ := rawDimerIsomerCount

def reportedDimerIsomerCountReal : ℝ := reportedDimerIsomerCount

/-- Machine-checkable reporting certificate at the exact-integer quantum 1. -/
theorem dimer_isomer_count_reportsAtQuantum :
    IChO2026Chem.Reporting.ReportsAtQuantum
      rawDimerIsomerCountReal reportedDimerIsomerCountReal 1 := by
  rw [show rawDimerIsomerCountReal = (3 : ℝ) by
    norm_num [rawDimerIsomerCountReal,
      dimer_isomer_count_raw_result.2.2.2]]
  rw [show reportedDimerIsomerCountReal = (3 : ℝ) by
    norm_num [reportedDimerIsomerCountReal,
      dimer_isomer_count_reported_result.2]]
  refine ⟨by norm_num, ⟨3, by norm_num⟩, ?_⟩
  norm_num

end IChO2026Problems.ProblemIcho2026T9A6
