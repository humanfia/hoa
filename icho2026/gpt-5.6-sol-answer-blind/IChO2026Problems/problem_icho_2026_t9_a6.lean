import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T9-A6

This file formalizes the source-side structural count for the constitutional
linkage isomers of the Sinay β-cyclodextrin dimer.  It derives the intermediate
`L` needed from T9-A5 inside this file, as required by the answer-blind
dependency policy.

The seven glucopyranoside units form a *directed* cycle: the direction records
the α1,4-glycosidic connectivity.  Thus cyclic rotation is harmless, while
reflection is not silently imposed as a structural symmetry.
-/

namespace IChO2026Problems
namespace T9A6

/-- A unit of β-cyclodextrin.  The source states that β-CD has seven units. -/
abbrev BetaCDUnit := Fin 7

/-- Unit 1 after fixing the first reductively debenzylated unit as the cyclic
origin. -/
def unitOne : BetaCDUnit := 0

/-- Unit 3 relative to a directing unit, represented on the directed
seven-membered cycle. -/
def unitThreeFrom (u : BetaCDUnit) : BetaCDUnit := u + 2

/-- Unit 4 relative to a directing unit, represented on the directed
seven-membered cycle. -/
def unitFourFrom (u : BetaCDUnit) : BetaCDUnit := u + 3

/-- The primary substituent states that are relevant to the depicted
synthesis.  No claim about omitted products, yields, or material streams is
encoded here. -/
inductive PrimarySubstituent
  | hydroxymethyl
  | benzylEther
  | linkerEther
  deriving DecidableEq, Repr

/-- The seven primary positions on one β-CD ring. -/
abbrev PrimaryPattern := BetaCDUnit → PrimarySubstituent

/-- The structural information used from one β-CD component.  The source image
also displays fourteen secondary substituents, all benzylated in `L` and in the
dimer. -/
structure BetaCDPattern where
  primary : PrimaryPattern
  secondaryBenzylEtherCount : ℕ

/-- Primary positions after exhaustive benzylation and before the two directed
reductive debenzylations. -/
def perbenzylatedPrimary : PrimaryPattern := fun _ => .benzylEther

/-- Reductive debenzylation at one named primary site. -/
def debenzylateAt (p : PrimaryPattern) (u : BetaCDUnit) : PrimaryPattern :=
  Function.update p u .hydroxymethyl

/-- The source directing rule: try unit 4; if that position is unavailable,
use unit 3.  Here availability means that the primary position still carries
the benzyl ether that the reductive step can remove. -/
def nextDirectedSite (p : PrimaryPattern) (directingUnit : BetaCDUnit) :
    BetaCDUnit :=
  if p (unitFourFrom directingUnit) = .benzylEther then
    unitFourFrom directingUnit
  else
    unitThreeFrom directingUnit

/-- Pattern after the first, symmetry-fixing primary debenzylation. -/
def afterFirstDebenzylation (anchor : BetaCDUnit) : PrimaryPattern :=
  debenzylateAt perbenzylatedPrimary anchor

/-- The primary pattern of intermediate `L`, obtained by applying the printed
unit-4/unit-3 directing rule after the first deprotection. -/
def intermediateLPrimary (anchor : BetaCDUnit) : PrimaryPattern :=
  let p := afterFirstDebenzylation anchor
  debenzylateAt p (nextDirectedSite p anchor)

/-- A rotationally normalized candidate for `L`.  Its specification below is
proved from the transformation definitions rather than assumed as a premise. -/
def intermediateL : BetaCDPattern where
  primary := intermediateLPrimary unitOne
  secondaryBenzylEtherCount := 14

/-- All sites carrying a primary hydroxymethyl group in a pattern. -/
def hydroxymethylSites (p : PrimaryPattern) : Finset BetaCDUnit :=
  Finset.univ.filter fun u => p u = .hydroxymethyl

/-- Count the occurrences of a named primary substituent. -/
def primarySubstituentCount (p : PrimaryPattern) (s : PrimarySubstituent) : ℕ :=
  (Finset.univ.filter fun u => p u = s).card

/-- In the current substrate, unit 4 remains a benzyl ether after the first
debenzylation, so the fallback to unit 3 is not activated. -/
theorem unitFour_available_after_first :
    (afterFirstDebenzylation unitOne) (unitFourFrom unitOne) =
      .benzylEther := by
  decide

/-- Consequently the source directing rule selects unit 4 in this synthesis. -/
theorem nextDirectedSite_eq_unitFour :
    nextDirectedSite (afterFirstDebenzylation unitOne) unitOne =
      unitFourFrom unitOne := by
  decide

/-- Inline derivation of the T9-A5 intermediate: `L` has primary hydroxymethyl
groups precisely at normalized units 1 and 4. -/
theorem intermediateL_hydroxymethylSites :
    hydroxymethylSites intermediateL.primary =
      {unitOne, unitFourFrom unitOne} := by
  decide

/-- The primary/secondary substituent ledger for `L` read from the scheme and
obtained after the two directed primary debenzylations. -/
theorem intermediateL_substituentLedger :
    primarySubstituentCount intermediateL.primary .hydroxymethyl = 2 ∧
    primarySubstituentCount intermediateL.primary .benzylEther = 5 ∧
    primarySubstituentCount intermediateL.primary .linkerEther = 0 ∧
    intermediateL.secondaryBenzylEtherCount = 14 := by
  decide

/-- The two source-derived primary OH sites of normalized `L`. -/
def normalizedLHydroxymethylSites : Finset BetaCDUnit :=
  hydroxymethylSites intermediateL.primary

/-- In the depicted mono-alkylation, exactly one of the two primary OH sites of
`L` receives the alkenyl linker precursor. -/
abbrev MonomerAttachmentChoice :=
  {u : BetaCDUnit // u ∈ normalizedLHydroxymethylSites}

/-- The other site remains a primary OH in the depicted dimer component. -/
def remainingHydroxymethylSite (choice : MonomerAttachmentChoice) : BetaCDUnit :=
  if choice.1 = unitOne then unitFourFrom unitOne else unitOne

/-- Directed cyclic displacement from the surviving primary OH to the linker
site.  Subtraction on `Fin 7` is modulo seven. -/
def cyclicOffset (fromSite toSite : BetaCDUnit) : BetaCDUnit :=
  toSite - fromSite

/-- Rotation-invariant constitutional class of a mono-alkylated component. -/
def linkerOffset (choice : MonomerAttachmentChoice) : BetaCDUnit :=
  cyclicOffset (remainingHydroxymethylSite choice) choice.1

/-- The finite offset domain is computed as the image of the two actual OH
choices of `L`; it is not postulated as an answer-shaped candidate set. -/
def monomerLinkageOffsets : Finset BetaCDUnit :=
  (Finset.univ : Finset MonomerAttachmentChoice).image linkerOffset

/-- A constitutional linkage class of one β-CD component, modulo cyclic
rotation but not reflection of the directed glycosidic cycle. -/
abbrev MonomerLinkageClass :=
  {d : BetaCDUnit // d ∈ monomerLinkageOffsets}

/-- Mono-alkylation turns one of the two OH sites into linker ether and leaves
the other one untouched. -/
def monoalkylatedPrimary (choice : MonomerAttachmentChoice) : PrimaryPattern :=
  Function.update intermediateL.primary choice.1 .linkerEther

/-- The substituent pattern on one component of the depicted dimer. -/
def monoalkylatedComponent (choice : MonomerAttachmentChoice) : BetaCDPattern where
  primary := monoalkylatedPrimary choice
  secondaryBenzylEtherCount := intermediateL.secondaryBenzylEtherCount

/-- Source-first component ledger for either ring of the product drawing. -/
theorem monoalkylated_componentLedger (choice : MonomerAttachmentChoice) :
    primarySubstituentCount (monoalkylatedComponent choice).primary
        .hydroxymethyl = 1 ∧
    primarySubstituentCount (monoalkylatedComponent choice).primary
        .benzylEther = 5 ∧
    primarySubstituentCount (monoalkylatedComponent choice).primary
        .linkerEther = 1 ∧
    (monoalkylatedComponent choice).secondaryBenzylEtherCount = 14 := by
  revert choice
  decide

/-- There are exactly two attachment choices before passing to the invariant
offset description. -/
theorem monomerAttachmentChoice_card :
    Fintype.card MonomerAttachmentChoice = 2 := by
  decide

/-- The two choices have directed offsets 3 and 4.  These are distinct because
the α1,4-linked glucose cycle is directed; a reflection is not a permitted
cyclic relabeling. -/
theorem monomerLinkageOffsets_eq :
    monomerLinkageOffsets = {(3 : BetaCDUnit), (4 : BetaCDUnit)} := by
  decide

/-- Hence the source-derived monomer linkage-class domain has two elements. -/
theorem monomerLinkageClass_card :
    Fintype.card MonomerLinkageClass = 2 := by
  decide

/-- The final saturated linker joins two identical β-CD components.  Swapping
the two ends does not make a new constitutional isomer, so the dimer classes
are unordered pairs (`Sym2`) of component classes. -/
abbrev DimerLinkageIsomer := Sym2 MonomerLinkageClass

/-- Raw exact count generated by the source-derived finite structural model. -/
def dimerIsomerCount : ℕ := Fintype.card DimerLinkageIsomer

/-- Stage-use classification: `qualitative_named_transform_only`.  This
contract records only structural compatibility along the printed arrows; it
does not assert yield, completion, a sole product, or an exhaustive material
balance. -/
def SinayQualitativeTransformContract : Prop :=
  Fintype.card BetaCDUnit = 7 ∧
  hydroxymethylSites intermediateL.primary =
    {unitOne, unitFourFrom unitOne} ∧
  primarySubstituentCount intermediateL.primary .hydroxymethyl = 2 ∧
  monomerLinkageOffsets = {(3 : BetaCDUnit), (4 : BetaCDUnit)} ∧
  Fintype.card MonomerLinkageClass = 2

theorem sinayQualitativeTransformContract :
    SinayQualitativeTransformContract := by
  refine ⟨rfl, intermediateL_hydroxymethylSites,
    intermediateL_substituentLedger.1, monomerLinkageOffsets_eq,
    monomerLinkageClass_card⟩

/-- Unrounded/exact derivation contract.  `Sym2.card` is the stars-and-bars
count of unordered pairs with repetition. -/
def RawDimerIsomerCountSpec : Prop :=
  SinayQualitativeTransformContract ∧
  dimerIsomerCount =
    Nat.choose (Fintype.card MonomerLinkageClass + 1) 2

/-- Raw result carrier for the requested output `dimer_isomer_count`. -/
theorem rawDimerIsomerCount : RawDimerIsomerCountSpec := by
  exact ⟨sinayQualitativeTransformContract, Sym2.card⟩

/-- Exact-integer reporting contract for the requested count. -/
def ReportedDimerIsomerCountSpec : Prop :=
  RawDimerIsomerCountSpec ∧ dimerIsomerCount = 3

/-- Reported result carrier for the requested output `dimer_isomer_count`. -/
theorem reportedDimerIsomerCount : ReportedDimerIsomerCountSpec := by
  refine ⟨rawDimerIsomerCount, ?_⟩
  rw [dimerIsomerCount, Sym2.card, monomerLinkageClass_card]
  decide

end T9A6
end IChO2026Problems
