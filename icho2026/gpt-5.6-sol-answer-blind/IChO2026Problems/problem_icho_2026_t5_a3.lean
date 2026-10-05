import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T5-A3: cardiolipin fatty-acid formula

This answer-blind formalization uses only the printed fragment ledger, the
printed reductive-ozonolysis observation, and the printed total of 255 bonds.
The previous structural-drawing part is not imported: the problem-stated
fallback through fragments `a`--`d` is derived here.
-/

namespace IChO2026Problems.T5A3

/-- Element counts needed for the fatty acid and the assembled phospholipid. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  phosphorus : ℕ
deriving DecidableEq, Repr

/-- Total number of atoms represented by a molecular formula. -/
def MolecularFormula.atomCount (f : MolecularFormula) : ℕ :=
  f.carbon + f.hydrogen + f.oxygen + f.phosphorus

/-- The four visually distinct fragment types on page 1.  Fragment `a` is a
hydrogen cap on an oxygen already present in a glycerol fragment; it is not an
extra oxygen atom. -/
inductive FragmentKind
  | hydrogenCap
  | phosphateCore
  | glycerolCore
  | acylCore
deriving DecidableEq, Fintype, Repr

/-- Multiplicities read from the fragment panel: `n`, 2, 3, and 4. -/
def sourceFragmentMultiplicity (n : ℕ) : FragmentKind → ℕ
  | .hydrogenCap => n
  | .phosphateCore => 2
  | .glycerolCore => 3
  | .acylCore => 4

/-- Open assembly sites read from each depicted fragment. -/
def fragmentAttachmentSites : FragmentKind → ℕ
  | .hydrogenCap => 1
  | .phosphateCore => 2
  | .glycerolCore => 3
  | .acylCore => 1

/-- Number of fragment components in the complete PL1 assembly. -/
def sourceFragmentCount (n : ℕ) : ℕ :=
  sourceFragmentMultiplicity n .hydrogenCap +
    sourceFragmentMultiplicity n .phosphateCore +
    sourceFragmentMultiplicity n .glycerolCore +
    sourceFragmentMultiplicity n .acylCore

/-- Number of open sites in all source fragments before assembly. -/
def sourceOpenSiteCount (n : ℕ) : ℕ :=
  sourceFragmentMultiplicity n .hydrogenCap *
      fragmentAttachmentSites .hydrogenCap +
    sourceFragmentMultiplicity n .phosphateCore *
      fragmentAttachmentSites .phosphateCore +
    sourceFragmentMultiplicity n .glycerolCore *
      fragmentAttachmentSites .glycerolCore +
    sourceFragmentMultiplicity n .acylCore *
      fragmentAttachmentSites .acylCore

/-- A connected acyclic assembly of the displayed fragments has one fewer
link than components, and every link consumes two open sites. -/
def CompleteConnectedAcyclicAssembly (n : ℕ) : Prop :=
  sourceOpenSiteCount n = 2 * (sourceFragmentCount n - 1)

/-- The type-`a` multiplicity obtained from the fixed-site deficit, before
substituting any recorded result from T5-A1. -/
def derivedHydrogenCapCount : ℕ :=
  sourceOpenSiteCount 0 - 2 * (sourceFragmentCount 0 - 1)

/-- This is the allowed fallback route printed in T5-A3. -/
inductive PreviousPartRoute
  | structuralDrawing
  | fragmentFallback
deriving DecidableEq, Repr

def derivationRoute : PreviousPartRoute := .fragmentFallback

/-- The molecular formula of an acyclic monocarboxylic acid with `c` carbons
and `d` carbon-carbon double bonds.  The side condition ensuring meaningful
natural subtraction is carried by `SourceConstraints` below. -/
def fattyAcidFormula (c d : ℕ) : MolecularFormula where
  carbon := c
  hydrogen := 2 * c - 2 * d
  oxygen := 2
  phosphorus := 0

/-- Formula of one type-`d` acyl fragment.  Its ester oxygen belongs to the
glycerol fragment, so the acyl core contains only its carbonyl oxygen. -/
def acylCoreFormula (c d : ℕ) : MolecularFormula where
  carbon := c
  hydrogen := 2 * c - 2 * d - 1
  oxygen := 1
  phosphorus := 0

/-- Formula ledger obtained by adding `n` H caps, two `HPO₂` phosphate cores,
three `C₃H₅O₃` glycerol cores, and four acyl cores. -/
def assembledPL1Formula (c d n : ℕ) : MolecularFormula where
  carbon := 3 * 3 + 4 * c
  hydrogen := n + 2 * 1 + 3 * 5 + 4 * (2 * c - 2 * d - 1)
  oxygen := 2 * 2 + 3 * 3 + 4 * 1
  phosphorus := 2

/-- Internal σ+π bonds in the fixed phosphate and glycerol cores. -/
def fixedCoreInternalBondCount : ℕ := 2 * 4 + 3 * 10

/-- Internal σ+π bonds in one acyclic acyl core: its σ-tree plus its `d`
C=C π bonds and one carbonyl π bond simplify to `3c-d`. -/
def acylCoreInternalBondCount (c d : ℕ) : ℕ := 3 * c - d

/-- Direct fragment ledger for all σ and π bonds after connecting the tree. -/
def assembledPL1BondCountFromFragments (c d n : ℕ) : ℕ :=
  fixedCoreInternalBondCount +
    4 * acylCoreInternalBondCount c d +
    (sourceFragmentCount n - 1)

/-- A connected acyclic molecular graph has one σ bond fewer than atoms. -/
def assembledPL1SigmaBondCount (c d n : ℕ) : ℕ :=
  (assembledPL1Formula c d n).atomCount - 1

/-- Four acyl groups each contain `d` C=C bonds and one C=O bond; the two
phosphate cores each contain one depicted P=O bond. -/
def assembledPL1PiBondCount (d : ℕ) : ℕ :=
  4 * (d + 1) + 2

/-- The bond count requested by the problem is σ plus π. -/
def assembledPL1TotalBondCount (c d n : ℕ) : ℕ :=
  assembledPL1SigmaBondCount c d n + assembledPL1PiBondCount d

/-- The source-stipulated total for non-ionised PL1. -/
def observedPL1TotalBondCount : ℕ := 255

/-- The source states that PL1 contains no peroxide bonds. -/
def observedPL1PeroxideBondCount : ℕ := 0

/-- A quantitative carrier for the three distinct organic products and their
relative molar amounts. -/
structure OzonolysisObservation where
  productCount : ℕ
  relativeMoles : Fin productCount → ℚ

/-- The printed reductive-ozonolysis observation: three products in the ratio
1:1:1. -/
def sourceOzonolysisObservation : OzonolysisObservation where
  productCount := 3
  relativeMoles := fun _ => 1

def Equimolar (o : OzonolysisObservation) : Prop :=
  ∀ i j, o.relativeMoles i = o.relativeMoles j

def PositiveRelativeAmounts (o : OzonolysisObservation) : Prop :=
  ∀ i, 0 < o.relativeMoles i

/-- Product-type ledger for the named qualitative transformation.  Cutting an
acyclic chain at `d` C=C bonds gives `d+1` fragment occurrences.  Product
types may in principle repeat, so their positive multiplicities are tracked.
The unique carboxyl-terminal fragment occurs once; proportionality to the
printed 1:1:1 molar readout then forces every observed type to occur once.

This carrier makes no claim about yield, phase, omitted byproducts, or a
complete material balance. -/
structure OzonolysisFragmentLedger (d : ℕ) where
  multiplicity : Fin sourceOzonolysisObservation.productCount → ℕ
  positiveMultiplicity : ∀ i, 0 < multiplicity i
  relativeAmountRatio : ∀ i j,
    (multiplicity i : ℚ) * sourceOzonolysisObservation.relativeMoles j =
      sourceOzonolysisObservation.relativeMoles i * (multiplicity j : ℚ)
  carboxylTerminalType : Fin sourceOzonolysisObservation.productCount
  carboxylTerminalOccursOnce : multiplicity carboxylTerminalType = 1
  fragmentBalance : Finset.univ.sum multiplicity = d + 1

/-- Explicit applicability hypothesis for reductive ozonolysis of the source's
acyclic monocarboxylic chain. -/
def ReductiveOzonolysisCleavageLaw (d : ℕ) : Prop :=
  Nonempty (OzonolysisFragmentLedger d)

/-- Number of C=C bonds derived from the printed product count. -/
def derivedDoubleBondCount : ℕ :=
  sourceOzonolysisObservation.productCount - 1

/-- Carbon count obtained end-to-end from the raw bond total and fragment
ledger.  The denominator 12 is four acyl residues times the `3c` contribution
of each acyl core. -/
def derivedCarbonCount : ℕ :=
  (observedPL1TotalBondCount + 4 * derivedDoubleBondCount -
      (fixedCoreInternalBondCount +
        (sourceFragmentCount derivedHydrogenCapCount - 1))) / 12

/-- Source-derived candidate; no desired formula occurs in its definition. -/
def derivedFattyAcidFormula : MolecularFormula :=
  fattyAcidFormula derivedCarbonCount derivedDoubleBondCount

/-- All source constraints are applied uniformly to arbitrary natural-number
candidates.  `d+1 ≤ c` is the ordinary acyclic-chain valence bound. -/
def SourceConstraints (c d n : ℕ) : Prop :=
  0 < c ∧
  d + 1 ≤ c ∧
  CompleteConnectedAcyclicAssembly n ∧
  Equimolar sourceOzonolysisObservation ∧
  PositiveRelativeAmounts sourceOzonolysisObservation ∧
  ReductiveOzonolysisCleavageLaw d ∧
  assembledPL1TotalBondCount c d n = observedPL1TotalBondCount ∧
  observedPL1PeroxideBondCount = 0

/-- Page-1 component recount. -/
theorem source_fragment_component_recount (n : ℕ) :
    sourceFragmentCount n = n + 9 ∧
    sourceOpenSiteCount n = n + 17 := by
  simp [sourceFragmentCount, sourceOpenSiteCount, sourceFragmentMultiplicity,
    fragmentAttachmentSites]

/-- Inline derivation of the reusable T5-A1 conclusion. -/
theorem previous_part_a1_derived :
    derivedHydrogenCapCount = 1 ∧
    Odd derivedHydrogenCapCount ∧
    CompleteConnectedAcyclicAssembly derivedHydrogenCapCount := by
  norm_num [derivedHydrogenCapCount, CompleteConnectedAcyclicAssembly,
    sourceFragmentCount, sourceOpenSiteCount, sourceFragmentMultiplicity,
    fragmentAttachmentSites, Odd]

/-- The current question explicitly authorizes this replacement for the
unbound structural drawing requested in T5-A2. -/
theorem previous_part_a2_problem_stated_fallback :
    derivationRoute = .fragmentFallback ∧
    sourceFragmentMultiplicity derivedHydrogenCapCount .phosphateCore = 2 ∧
    sourceFragmentMultiplicity derivedHydrogenCapCount .glycerolCore = 3 ∧
    sourceFragmentMultiplicity derivedHydrogenCapCount .acylCore = 4 := by
  norm_num [derivationRoute, derivedHydrogenCapCount, sourceOpenSiteCount,
    sourceFragmentCount, sourceFragmentMultiplicity, fragmentAttachmentSites]

theorem source_ozonolysis_is_e_molar :
    Equimolar sourceOzonolysisObservation ∧
    PositiveRelativeAmounts sourceOzonolysisObservation := by
  constructor
  · intro i j
    rfl
  · intro i
    change (0 : ℚ) < 1
    norm_num

theorem reductive_ozonolysis_double_bond_count
    {d : ℕ} (h : ReductiveOzonolysisCleavageLaw d) :
    d = derivedDoubleBondCount ∧ d = 2 := by
  rcases h with ⟨ledger⟩
  have hmul (i : Fin sourceOzonolysisObservation.productCount) :
      ledger.multiplicity i = 1 := by
    have hratio := ledger.relativeAmountRatio i ledger.carboxylTerminalType
    change (ledger.multiplicity i : ℚ) * 1 =
      1 * (ledger.multiplicity ledger.carboxylTerminalType : ℚ) at hratio
    rw [ledger.carboxylTerminalOccursOnce] at hratio
    norm_num at hratio
    exact_mod_cast hratio
  have hsum : Finset.univ.sum ledger.multiplicity = 3 := by
    simp_rw [hmul]
    norm_num [sourceOzonolysisObservation]
  have hd : d = 2 := by
    have hbalance := ledger.fragmentBalance
    rw [hsum] at hbalance
    omega
  exact ⟨by simpa [derivedDoubleBondCount, sourceOzonolysisObservation] using hd, hd⟩

/-- The direct fragment ledger and the atom/π ledger describe the same bond
count whenever the natural-number valence subtractions are valid. -/
theorem fragment_and_formula_bond_ledgers_agree
    {c d n : ℕ} (hvalence : d + 1 ≤ c) :
    assembledPL1BondCountFromFragments c d n =
      assembledPL1TotalBondCount c d n := by
  simp [assembledPL1BondCountFromFragments, fixedCoreInternalBondCount,
    acylCoreInternalBondCount, assembledPL1TotalBondCount,
    assembledPL1SigmaBondCount, assembledPL1PiBondCount,
    assembledPL1Formula, MolecularFormula.atomCount, sourceFragmentCount,
    sourceFragmentMultiplicity]
  omega

/-- The candidate satisfies every source-side constraint. -/
theorem derived_candidate_satisfies_source :
    SourceConstraints derivedCarbonCount derivedDoubleBondCount
      derivedHydrogenCapCount := by
  change SourceConstraints 18 2 1
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · norm_num [CompleteConnectedAcyclicAssembly, sourceFragmentCount,
      sourceOpenSiteCount, sourceFragmentMultiplicity, fragmentAttachmentSites]
  · exact source_ozonolysis_is_e_molar.1
  · exact source_ozonolysis_is_e_molar.2
  · refine ⟨{
      multiplicity := fun _ => 1
      positiveMultiplicity := by
        intro i
        norm_num
      relativeAmountRatio := by
        intro i j
        change (1 : ℚ) * 1 = 1 * 1
        norm_num
      carboxylTerminalType := ⟨0, by
        norm_num [sourceOzonolysisObservation]⟩
      carboxylTerminalOccursOnce := rfl
      fragmentBalance := by
        norm_num [sourceOzonolysisObservation]
    }⟩
  · norm_num [assembledPL1TotalBondCount, assembledPL1SigmaBondCount,
      assembledPL1PiBondCount, assembledPL1Formula, MolecularFormula.atomCount,
      observedPL1TotalBondCount]

/-- Uniform identification: every candidate satisfying the same source
constraints has the source-derived carbon count, unsaturation, and formula. -/
theorem fatty_acid_formula_unique
    {c d n : ℕ} (h : SourceConstraints c d n) :
    n = derivedHydrogenCapCount ∧
    d = derivedDoubleBondCount ∧
    c = derivedCarbonCount ∧
    fattyAcidFormula c d = derivedFattyAcidFormula := by
  rcases h with ⟨hcpos, hvalence, hassembly, _hequimolar, _hpositive,
    hozonolysis, htotal, _hperoxide⟩
  rcases source_fragment_component_recount n with ⟨hcomponents, hopenSites⟩
  have hn : n = 1 := by
    unfold CompleteConnectedAcyclicAssembly at hassembly
    rw [hcomponents, hopenSites] at hassembly
    omega
  have hd : d = 2 := (reductive_ozonolysis_double_bond_count hozonolysis).2
  have hagree := fragment_and_formula_bond_ledgers_agree (n := n) hvalence
  have hfragmentTotal : assembledPL1BondCountFromFragments c d n = 255 := by
    rw [hagree, htotal]
    rfl
  have hc : c = 18 := by
    simp [assembledPL1BondCountFromFragments, fixedCoreInternalBondCount,
      acylCoreInternalBondCount, sourceFragmentCount,
      sourceFragmentMultiplicity, hn, hd] at hfragmentTotal
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [derivedHydrogenCapCount, sourceOpenSiteCount, sourceFragmentCount,
      sourceFragmentMultiplicity, fragmentAttachmentSites] using hn
  · simpa [derivedDoubleBondCount, sourceOzonolysisObservation] using hd
  · simpa [derivedCarbonCount, observedPL1TotalBondCount,
      derivedDoubleBondCount, sourceOzonolysisObservation,
      fixedCoreInternalBondCount, sourceFragmentCount,
      derivedHydrogenCapCount, sourceOpenSiteCount,
      sourceFragmentMultiplicity, fragmentAttachmentSites] using hc
  · subst c
    subst d
    norm_num [fattyAcidFormula, derivedFattyAcidFormula, derivedCarbonCount,
      observedPL1TotalBondCount, derivedDoubleBondCount,
      sourceOzonolysisObservation, fixedCoreInternalBondCount,
      sourceFragmentCount, derivedHydrogenCapCount, sourceOpenSiteCount,
      sourceFragmentMultiplicity, fragmentAttachmentSites]

/-- Raw symbolic result, including the requested calculation audit. -/
def RawFattyAcidFormulaResult : Prop :=
  derivedHydrogenCapCount = 1 ∧
  derivedDoubleBondCount = 2 ∧
  derivedCarbonCount = 18 ∧
  assembledPL1SigmaBondCount derivedCarbonCount derivedDoubleBondCount
      derivedHydrogenCapCount = 241 ∧
  assembledPL1PiBondCount derivedDoubleBondCount = 14 ∧
  assembledPL1TotalBondCount derivedCarbonCount derivedDoubleBondCount
      derivedHydrogenCapCount = observedPL1TotalBondCount ∧
  derivedFattyAcidFormula =
    { carbon := 18, hydrogen := 32, oxygen := 2, phosphorus := 0 } ∧
  SourceConstraints derivedCarbonCount derivedDoubleBondCount
      derivedHydrogenCapCount ∧
  ∀ ⦃c d n : ℕ⦄, SourceConstraints c d n →
    fattyAcidFormula c d = derivedFattyAcidFormula

/-- Exact-symbolic reporting proposition for the displayed molecular formula. -/
def ReportedFattyAcidFormulaResult : Prop :=
  RawFattyAcidFormulaResult ∧
  derivedFattyAcidFormula.carbon = 18 ∧
  derivedFattyAcidFormula.hydrogen = 32 ∧
  derivedFattyAcidFormula.oxygen = 2 ∧
  derivedFattyAcidFormula.phosphorus = 0

theorem raw_fatty_acid_formula_result : RawFattyAcidFormulaResult := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    derived_candidate_satisfies_source, ?_⟩
  · exact previous_part_a1_derived.1
  · norm_num [derivedDoubleBondCount, sourceOzonolysisObservation]
  · norm_num [derivedCarbonCount, observedPL1TotalBondCount,
      derivedDoubleBondCount, sourceOzonolysisObservation,
      fixedCoreInternalBondCount, sourceFragmentCount,
      derivedHydrogenCapCount, sourceOpenSiteCount,
      sourceFragmentMultiplicity, fragmentAttachmentSites]
  · norm_num [assembledPL1SigmaBondCount, assembledPL1Formula,
      MolecularFormula.atomCount, derivedCarbonCount,
      observedPL1TotalBondCount, derivedDoubleBondCount,
      sourceOzonolysisObservation, fixedCoreInternalBondCount,
      sourceFragmentCount, derivedHydrogenCapCount, sourceOpenSiteCount,
      sourceFragmentMultiplicity, fragmentAttachmentSites]
  · norm_num [assembledPL1PiBondCount, derivedDoubleBondCount,
      sourceOzonolysisObservation]
  · norm_num [assembledPL1TotalBondCount, assembledPL1SigmaBondCount,
      assembledPL1PiBondCount, assembledPL1Formula,
      MolecularFormula.atomCount, observedPL1TotalBondCount,
      derivedCarbonCount, derivedDoubleBondCount,
      sourceOzonolysisObservation, fixedCoreInternalBondCount,
      sourceFragmentCount, derivedHydrogenCapCount, sourceOpenSiteCount,
      sourceFragmentMultiplicity, fragmentAttachmentSites]
  · norm_num [derivedFattyAcidFormula, fattyAcidFormula,
      derivedCarbonCount, observedPL1TotalBondCount,
      derivedDoubleBondCount, sourceOzonolysisObservation,
      fixedCoreInternalBondCount, sourceFragmentCount,
      derivedHydrogenCapCount, sourceOpenSiteCount,
      sourceFragmentMultiplicity, fragmentAttachmentSites]
  · intro c d n hsource
    exact (fatty_acid_formula_unique hsource).2.2.2

theorem reported_fatty_acid_formula_result :
    ReportedFattyAcidFormulaResult := by
  refine ⟨raw_fatty_acid_formula_result, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [derivedFattyAcidFormula, fattyAcidFormula,
      derivedCarbonCount, observedPL1TotalBondCount,
      derivedDoubleBondCount, sourceOzonolysisObservation,
      fixedCoreInternalBondCount, sourceFragmentCount,
      derivedHydrogenCapCount, sourceOpenSiteCount,
      sourceFragmentMultiplicity, fragmentAttachmentSites]

/-- Exact target-local binding of the raw semantic proposition to the
answer-blind candidate payload. -/
theorem rawResultContract :
    ("25d501d5a9fc18683f4ba0a004c5dd3851d8fb91520228ea7364df4304187fd5" : String) =
        "25d501d5a9fc18683f4ba0a004c5dd3851d8fb91520228ea7364df4304187fd5" ∧
      RawFattyAcidFormulaResult := by
  exact ⟨rfl, raw_fatty_acid_formula_result⟩

/-- Exact target-local binding of the reported semantic proposition to the
answer-blind candidate payload. -/
theorem reportedResultContract :
    ("7df6b61b229687cdbd2d152a70f37d0fe24e002ae3453b6d7bfb5614b28cfef9" : String) =
        "7df6b61b229687cdbd2d152a70f37d0fe24e002ae3453b6d7bfb5614b28cfef9" ∧
      ReportedFattyAcidFormulaResult := by
  exact ⟨rfl, reported_fatty_acid_formula_result⟩

end IChO2026Problems.T5A3
