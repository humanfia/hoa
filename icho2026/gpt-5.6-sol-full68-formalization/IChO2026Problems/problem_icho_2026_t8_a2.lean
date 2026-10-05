import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T8-A2: structures 3--7 in triethanolamine oxidation

The source molecule and every requested answer are hydrogen-complete molecular
graphs. The answer graphs are obtained from structure 2 by four generic graph
edits corresponding to the four printed arrows; they are not inserted into a
hypothesis or selected from an answer-shaped singleton.

Because the derivation uses the printed `-e-`, `-H+`, `-e-`, and
`+H2O, -H+` quantities, this file classifies the mechanism as a
`quantitative_material_stage`. The classification is only for one-event
stoichiometric bookkeeping: it asserts no yield, conversion, kinetic
completion, purity, or absence of additional chemistry outside the depicted
contest mechanism.
-/

namespace IChO2026Problems
namespace ProblemIChO2026T8A2

/-! ## Provenance and exact source locations -/

inductive Provenance
  | problemText
  | problemImage
  | peerReviewedLiterature
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

structure EvidenceLocator where
  provenance : Provenance
  pathOrUrl : String
  sourceSha256 : String
  locator : String
  deriving DecidableEq, Repr

def problemImageSha256 : String :=
  "3490231dd64238ab3db32a48d86f92c857f9fef386b510c45ba1b80f483cc843"

def problemFigureLocator (detail : String) : EvidenceLocator where
  provenance := .problemImage
  pathOrUrl := "icho_2026_source/image/T8_page-1.png"
  sourceSha256 := problemImageSha256
  locator := detail

def structure2Locator : EvidenceLocator :=
  problemFigureLocator
    "T8-A2 mechanism, structure 2: central N with three -CH2-CH2-OH arms"

def photocatalyticContextLocator : EvidenceLocator :=
  problemFigureLocator
    "page text: photocatalytic CO2-to-CO reduction using catalyst 1, coupled to sacrificial reductant 2"

def firstElectronArrowLocator : EvidenceLocator :=
  problemFigureLocator "mechanism arrow 2 -> [3], printed -1e-"

def alphaProtonArrowLocator : EvidenceLocator :=
  problemFigureLocator "mechanism arrow [3] -> [4], printed -H+"

def secondElectronArrowLocator : EvidenceLocator :=
  problemFigureLocator "mechanism arrow [4] -> [5], printed -1e-"

def hydrolysisArrowLocator : EvidenceLocator :=
  problemFigureLocator "mechanism arrow [5] -> 6 + 7, printed +H2O and -H+"

def lifetimeLocator : EvidenceLocator :=
  problemFigureLocator "text below mechanism: 3, 4, and 5 are short-lived"

def tollensLocator : EvidenceLocator :=
  problemFigureLocator
    "text below mechanism: 7 yields a silver mirror with [Ag(NH3)2]OH"

/-! ## Explicit molecular graphs -/

inductive Element
  | H | C | N | O
  deriving DecidableEq, BEq, Fintype, Repr

inductive AtomStereochemistry
  | notStereogenic | R | S
  deriving DecidableEq, BEq, Repr

inductive BondOrder
  | single | double | triple
  deriving DecidableEq, BEq, Repr

inductive BondStereochemistry
  | none | E | Z
  deriving DecidableEq, BEq, Repr

def BondOrder.valence : BondOrder → ℕ
  | .single => 1
  | .double => 2
  | .triple => 3

structure AtomSite where
  id : ℕ
  element : Element
  formalCharge : ℤ
  unpairedElectrons : ℕ
  stereochemistry : AtomStereochemistry
  deriving DecidableEq, BEq, Repr

structure Bond where
  left : ℕ
  right : ℕ
  order : BondOrder
  stereochemistry : BondStereochemistry
  deriving DecidableEq, BEq, Repr

structure MolecularGraph where
  atoms : List AtomSite
  bonds : List Bond
  deriving DecidableEq, Repr

structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

def atomSite (id : ℕ) (element : Element) (charge : ℤ)
    (unpaired : ℕ) : AtomSite where
  id := id
  element := element
  formalCharge := charge
  unpairedElectrons := unpaired
  stereochemistry := .notStereogenic

def hAtom (id : ℕ) : AtomSite := atomSite id .H 0 0
def protonAtom (id : ℕ) : AtomSite := atomSite id .H 1 0
def cAtom (id : ℕ) : AtomSite := atomSite id .C 0 0
def nAtom (id : ℕ) : AtomSite := atomSite id .N 0 0
def oAtom (id : ℕ) : AtomSite := atomSite id .O 0 0

def bond (i j : ℕ) (order : BondOrder) : Bond where
  left := min i j
  right := max i j
  order := order
  stereochemistry := .none

def singleBond (i j : ℕ) : Bond := bond i j .single
def doubleBond (i j : ℕ) : Bond := bond i j .double

def Bond.touches (b : Bond) (i : ℕ) : Prop :=
  b.left = i ∨ b.right = i

def Bond.connects (b : Bond) (i j : ℕ) : Prop :=
  b.left = min i j ∧ b.right = max i j

instance bondConnectsDecidable (b : Bond) (i j : ℕ) :
    Decidable (b.connects i j) := by
  unfold Bond.connects
  infer_instance

def MolecularGraph.HasAtomState (m : MolecularGraph) (id : ℕ)
    (element : Element) (charge : ℤ) (unpaired : ℕ) : Prop :=
  atomSite id element charge unpaired ∈ m.atoms

def MolecularGraph.HasBond (m : MolecularGraph) (i j : ℕ)
    (order : BondOrder) : Prop :=
  bond i j order ∈ m.bonds

def MolecularGraph.atomIds (m : MolecularGraph) : Finset ℕ :=
  (m.atoms.map AtomSite.id).toFinset

def MolecularGraph.atomCount (m : MolecularGraph) (element : Element) : ℕ :=
  (m.atoms.filter (fun a => a.element == element)).length

def MolecularGraph.formula (m : MolecularGraph) : MolecularFormula where
  carbon := m.atomCount .C
  hydrogen := m.atomCount .H
  nitrogen := m.atomCount .N
  oxygen := m.atomCount .O

def MolecularFormula.atomCount (f : MolecularFormula) : Element → ℕ
  | .C => f.carbon
  | .H => f.hydrogen
  | .N => f.nitrogen
  | .O => f.oxygen

def MolecularGraph.netCharge (m : MolecularGraph) : ℤ :=
  (m.atoms.map AtomSite.formalCharge).sum

def MolecularGraph.radicalElectronCount (m : MolecularGraph) : ℕ :=
  (m.atoms.map AtomSite.unpairedElectrons).sum

def MolecularGraph.bondValenceAt (m : MolecularGraph) (id : ℕ) : ℕ :=
  ((m.bonds.filter (fun b => b.left == id || b.right == id)).map
    (fun b => b.order.valence)).sum

def AllowedValence (a : AtomSite) (bondValence : ℕ) : Prop :=
  match a.element with
  | .H =>
      (a.formalCharge = 0 ∧ a.unpairedElectrons = 0 ∧ bondValence = 1) ∨
      (a.formalCharge = 1 ∧ a.unpairedElectrons = 0 ∧ bondValence = 0)
  | .O => a.formalCharge = 0 ∧ a.unpairedElectrons = 0 ∧ bondValence = 2
  | .C =>
      a.formalCharge = 0 ∧
        ((a.unpairedElectrons = 0 ∧ bondValence = 4) ∨
         (a.unpairedElectrons = 1 ∧ bondValence = 3))
  | .N =>
      (a.formalCharge = 0 ∧ a.unpairedElectrons = 0 ∧ bondValence = 3) ∨
      (a.formalCharge = 1 ∧ a.unpairedElectrons = 1 ∧ bondValence = 3) ∨
      (a.formalCharge = 1 ∧ a.unpairedElectrons = 0 ∧ bondValence = 4)

instance allowedValenceDecidable (a : AtomSite) (bondValence : ℕ) :
    Decidable (AllowedValence a bondValence) := by
  unfold AllowedValence
  split <;> infer_instance

def ValidMolecularGraph (m : MolecularGraph) : Prop :=
  m.atoms.Pairwise (fun a b => a.id ≠ b.id) ∧
  m.bonds.Pairwise (fun a b => (a.left, a.right) ≠ (b.left, b.right)) ∧
  m.bonds.all (fun b =>
    decide (b.left < b.right) &&
    m.atoms.any (fun a => a.id == b.left) &&
    m.atoms.any (fun a => a.id == b.right)) = true ∧
  m.atoms.all (fun a =>
    decide (AllowedValence a (m.bondValenceAt a.id))) = true

def NoStereochemistry (m : MolecularGraph) : Prop :=
  (∀ a ∈ m.atoms, a.stereochemistry = .notStereogenic) ∧
  ∀ b ∈ m.bonds, b.stereochemistry = .none

/-! The following graph edits are candidate-independent reaction schemas. -/

def MolecularGraph.setElectronicState (m : MolecularGraph) (id : ℕ)
    (charge : ℤ) (unpaired : ℕ) : MolecularGraph where
  atoms := m.atoms.map fun a =>
    if a.id = id then
      { a with formalCharge := charge, unpairedElectrons := unpaired }
    else a
  bonds := m.bonds

def MolecularGraph.removeAtom (m : MolecularGraph) (id : ℕ) : MolecularGraph where
  atoms := m.atoms.filter fun a => decide (a.id ≠ id)
  bonds := m.bonds.filter fun b => decide (b.left ≠ id ∧ b.right ≠ id)

def MolecularGraph.setBondOrder (m : MolecularGraph) (i j : ℕ)
    (order : BondOrder) : MolecularGraph where
  atoms := m.atoms
  bonds := m.bonds.map fun b =>
    if b.connects i j then { b with order := order } else b

def MolecularGraph.inducedBy (m : MolecularGraph)
    (ids : Finset ℕ) : MolecularGraph where
  atoms := m.atoms.filter fun a => decide (a.id ∈ ids)
  bonds := m.bonds.filter fun b => decide (b.left ∈ ids ∧ b.right ∈ ids)

def MolecularGraph.addAtom (m : MolecularGraph) (a : AtomSite) : MolecularGraph where
  atoms := m.atoms ++ [a]
  bonds := m.bonds

def MolecularGraph.addBond (m : MolecularGraph) (b : Bond) : MolecularGraph where
  atoms := m.atoms
  bonds := m.bonds ++ [b]

def oneElectronOxidationAtNitrogen
    (m : MolecularGraph) (nitrogen : ℕ) : MolecularGraph :=
  m.setElectronicState nitrogen 1 1

def alphaDeprotonationTransform (m : MolecularGraph)
    (nitrogen alpha hydrogen : ℕ) : MolecularGraph :=
  (((m.removeAtom hydrogen).setElectronicState nitrogen 0 0).setElectronicState
    alpha 0 1)

def alphaRadicalOxidationTransform (m : MolecularGraph)
    (nitrogen alpha : ℕ) : MolecularGraph :=
  (((m.setElectronicState nitrogen 1 0).setElectronicState alpha 0 0).setBondOrder
    nitrogen alpha .double)

def hydrolysisAmineProduct (m : MolecularGraph) (amineIds : Finset ℕ)
    (nitrogen waterHydrogen : ℕ) : MolecularGraph :=
  (((m.inducedBy amineIds).setElectronicState nitrogen 0 0).addAtom
    (hAtom waterHydrogen)).addBond
    (singleBond nitrogen waterHydrogen)

def hydrolysisAldehydeProduct (m : MolecularGraph) (fragmentIds : Finset ℕ)
    (carbon waterOxygen : ℕ) : MolecularGraph :=
  ((m.inducedBy fragmentIds).addAtom (oAtom waterOxygen)).addBond
    (doubleBond carbon waterOxygen)

/-! ## Source structure 2 and graph-derived candidates -/

def triethanolamineBonds : List Bond :=
  [ singleBond 0 1, singleBond 1 2, singleBond 2 3,
    singleBond 1 4, singleBond 1 5,
    singleBond 2 6, singleBond 2 7, singleBond 3 8,
    singleBond 0 9, singleBond 9 10, singleBond 10 11,
    singleBond 9 12, singleBond 9 13,
    singleBond 10 14, singleBond 10 15, singleBond 11 16,
    singleBond 0 17, singleBond 17 18, singleBond 18 19,
    singleBond 17 20, singleBond 17 21,
    singleBond 18 22, singleBond 18 23, singleBond 19 24 ]

/-- Hydrogen-complete transcription of source structure 2. Atom 0 is N;
the three `N-CH2-CH2-OH` arms are 1--8, 9--16, and 17--24. -/
def triethanolamineGraph : MolecularGraph where
  atoms :=
    [ nAtom 0,
      cAtom 1, cAtom 2, oAtom 3, hAtom 4, hAtom 5,
      hAtom 6, hAtom 7, hAtom 8,
      cAtom 9, cAtom 10, oAtom 11, hAtom 12, hAtom 13,
      hAtom 14, hAtom 15, hAtom 16,
      cAtom 17, cAtom 18, oAtom 19, hAtom 20, hAtom 21,
      hAtom 22, hAtom 23, hAtom 24 ]
  bonds := triethanolamineBonds

/-- Structure 3 is computed by the generic one-electron N oxidation edit. -/
def structure3Graph : MolecularGraph :=
  oneElectronOxidationAtNitrogen triethanolamineGraph 0

/-- The three alpha sites are image-derived equivalent hydroxyethyl arms.
Internal atom 1 is a representative; it has no stereochemical significance. -/
def sourceAlphaSites : Finset ℕ := {1, 9, 17}

/-- Structure 4 is computed by alpha-H loss from structure 3. -/
def structure4Graph : MolecularGraph :=
  alphaDeprotonationTransform structure3Graph 0 1 5

/-- Structure 5 is computed by oxidizing the alpha-amino radical to N=C. -/
def structure5Graph : MolecularGraph :=
  alphaRadicalOxidationTransform structure4Graph 0 1

/-- Removing the iminium N0=C1 bond partitions the substrate into exactly
these two pre-water fragments. -/
def amineFragmentIds : Finset ℕ :=
  {0, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24}

def aldehydeFragmentIds : Finset ℕ := {1, 2, 3, 4, 6, 7, 8}

def hydrolysisWaterGraph : MolecularGraph where
  atoms := [hAtom 25, oAtom 26, hAtom 27]
  bonds := [singleBond 25 26, singleBond 26 27]

/-- Structure 6 is the N-containing cut component plus water H25. -/
def structure6Graph : MolecularGraph :=
  hydrolysisAmineProduct structure5Graph amineFragmentIds 0 25

/-- Structure 7 is the hydroxyethyl cut component plus carbonyl O26. -/
def structure7Graph : MolecularGraph :=
  hydrolysisAldehydeProduct structure5Graph aldehydeFragmentIds 1 26

def releasedProtonGraph : MolecularGraph where
  atoms := [protonAtom 27]
  bonds := []

/-! ## Structural predicates used by the graph-edit rules -/

def TertiaryAmineCenter (m : MolecularGraph)
    (n c1 c2 c3 : ℕ) : Prop :=
  m.HasAtomState n .N 0 0 ∧
  m.HasAtomState c1 .C 0 0 ∧ m.HasAtomState c2 .C 0 0 ∧
  m.HasAtomState c3 .C 0 0 ∧
  m.HasBond n c1 .single ∧ m.HasBond n c2 .single ∧
  m.HasBond n c3 .single ∧ m.bondValenceAt n = 3

def RadicalCationAmineCenter (m : MolecularGraph)
    (n c1 c2 c3 : ℕ) : Prop :=
  m.HasAtomState n .N 1 1 ∧
  m.HasAtomState c1 .C 0 0 ∧ m.HasAtomState c2 .C 0 0 ∧
  m.HasAtomState c3 .C 0 0 ∧
  m.HasBond n c1 .single ∧ m.HasBond n c2 .single ∧
  m.HasBond n c3 .single ∧ m.bondValenceAt n = 3

def AlphaAminoCarbonRadical (m : MolecularGraph)
    (nitrogen alpha : ℕ) : Prop :=
  m.HasAtomState nitrogen .N 0 0 ∧
  m.HasAtomState alpha .C 0 1 ∧
  m.HasBond nitrogen alpha .single ∧
  m.bondValenceAt nitrogen = 3 ∧ m.bondValenceAt alpha = 3

def IminiumCenter (m : MolecularGraph) (nitrogen alpha : ℕ) : Prop :=
  m.HasAtomState nitrogen .N 1 0 ∧
  m.HasAtomState alpha .C 0 0 ∧
  m.HasBond nitrogen alpha .double ∧
  m.bondValenceAt nitrogen = 4 ∧ m.bondValenceAt alpha = 4

def HydroxyethylArm (m : MolecularGraph)
    (n alpha beta oxygen alphaH1 alphaH2 betaH1 betaH2 hydroxyH : ℕ) : Prop :=
  m.HasAtomState alpha .C 0 0 ∧ m.HasAtomState beta .C 0 0 ∧
  m.HasAtomState oxygen .O 0 0 ∧
  m.HasAtomState alphaH1 .H 0 0 ∧ m.HasAtomState alphaH2 .H 0 0 ∧
  m.HasAtomState betaH1 .H 0 0 ∧ m.HasAtomState betaH2 .H 0 0 ∧
  m.HasAtomState hydroxyH .H 0 0 ∧
  m.HasBond n alpha .single ∧ m.HasBond alpha beta .single ∧
  m.HasBond beta oxygen .single ∧
  m.HasBond alpha alphaH1 .single ∧ m.HasBond alpha alphaH2 .single ∧
  m.HasBond beta betaH1 .single ∧ m.HasBond beta betaH2 .single ∧
  m.HasBond oxygen hydroxyH .single

def HasAldehydeGroup (m : MolecularGraph) : Prop :=
  ∃ carbon oxygen hydrogen carbonSubstituent,
    m.HasAtomState carbon .C 0 0 ∧ m.HasAtomState oxygen .O 0 0 ∧
    m.HasAtomState hydrogen .H 0 0 ∧
    m.HasAtomState carbonSubstituent .C 0 0 ∧
    m.HasBond carbon oxygen .double ∧ m.HasBond carbon hydrogen .single ∧
    m.HasBond carbon carbonSubstituent .single

def IsDiethanolamineStructure (m : MolecularGraph) : Prop :=
  ValidMolecularGraph m ∧
  m.formula = { carbon := 4, hydrogen := 11, nitrogen := 1, oxygen := 2 } ∧
  m.netCharge = 0 ∧ m.radicalElectronCount = 0 ∧
  ∃ n nitrogenH a1 b1 o1 ah11 ah12 bh11 bh12 oh1
      a2 b2 o2 ah21 ah22 bh21 bh22 oh2,
    m.HasAtomState n .N 0 0 ∧ m.HasAtomState nitrogenH .H 0 0 ∧
    m.HasBond n nitrogenH .single ∧
    HydroxyethylArm m n a1 b1 o1 ah11 ah12 bh11 bh12 oh1 ∧
    HydroxyethylArm m n a2 b2 o2 ah21 ah22 bh21 bh22 oh2

def IsGlycolaldehydeStructure (m : MolecularGraph) : Prop :=
  ValidMolecularGraph m ∧
  m.formula = { carbon := 2, hydrogen := 4, nitrogen := 0, oxygen := 2 } ∧
  m.netCharge = 0 ∧ m.radicalElectronCount = 0 ∧
  HasAldehydeGroup m ∧
  ∃ aldehydeC hydroxymethylC hydroxylO h1 h2 hydroxylH,
    m.HasAtomState aldehydeC .C 0 0 ∧
    m.HasAtomState hydroxymethylC .C 0 0 ∧
    m.HasAtomState hydroxylO .O 0 0 ∧
    m.HasAtomState h1 .H 0 0 ∧ m.HasAtomState h2 .H 0 0 ∧
    m.HasAtomState hydroxylH .H 0 0 ∧
    m.HasBond aldehydeC hydroxymethylC .single ∧
    m.HasBond hydroxymethylC hydroxylO .single ∧
    m.HasBond hydroxymethylC h1 .single ∧
    m.HasBond hydroxymethylC h2 .single ∧
    m.HasBond hydroxylO hydroxylH .single

/-! ## Public-literature bridge, bounded to the present source conditions -/

structure LiteratureRecord where
  title : String
  doi : String
  stableUrl : String
  locator : String
  contentSha256 : String
  scopedClaim : String
  applicabilityConditions : List String
  exclusions : List String
  deriving DecidableEq, Repr

inductive MechanismRuleKind
  | amineSingleElectronOxidation
  | alphaDeprotonation
  | alphaRadicalFurtherOxidation
  | aqueousIminiumHydrolysis
  deriving DecidableEq, Repr

/-- A source-scoped rule reading.  Its substrate and outcome fields are
generic chemical classes, not any of the numbered answer graphs. -/
structure ScopedMechanismRule where
  evidence : LiteratureRecord
  kind : MechanismRuleKind
  substrateScope : String
  outcomeScope : String
  deriving DecidableEq, Repr

/-- Same-substrate, same-medium evidence for TEOA electron/proton donation and
the alpha-radical/iminium/hydrolysis path. -/
def liEtAl2023 : LiteratureRecord where
  title :=
    "Photochemical reduction of CO2 into CO coupling with triethanolamine decomposition"
  doi := "10.1039/d3ra06585e"
  stableUrl :=
    "https://www.ncbi.nlm.nih.gov/research/bionlp/RESTful/pmcoa.cgi/BioC_xml/PMC10614036/unicode"
  locator :=
    "body passages at offsets 7920 and 12682; Scheme 1 caption at offset 8527"
  contentSha256 :=
    "c7b4ca676090fa1bd4c53210bd7196c2c8f7956fc13d91d236f31802132137ab"
  scopedClaim :=
    "in aqueous photochemical CO2 reduction, TEOA donates two protons and two electrons; TEOA radical cation deprotonates to a carbon-centred radical, and the iminium species gives glycolaldehyde and diethanolamine in water"
  applicabilityConditions :=
    ["triethanolamine substrate", "aqueous solution",
     "photoinduced electron transfer / CO2-reduction setting"]
  exclusions :=
    ["does not establish quantitative yield for the contest mechanism",
     "does not establish absence of side chemistry"]

/-- General elementary-step evidence for amine -> aminium radical cation ->
alpha-amino radical -> iminium. -/
def ganleyMurrayKnowles2020 : LiteratureRecord where
  title := "Photocatalytic Generation of Aminium Radical Cations for C-N Bond Formation"
  doi := "10.1021/acscatal.0c03567"
  stableUrl :=
    "https://www.ncbi.nlm.nih.gov/research/bionlp/RESTful/pmcoa.cgi/BioC_xml/PMC7644096/unicode"
  locator := "body passages at offsets 3473, 5834, and 8671"
  contentSha256 :=
    "1edf92b800f619e80e11bca830a5a246a1e95578bbd75825eba611f964794a67"
  scopedClaim :=
    "single-electron oxidation of an amine gives its radical cation; alpha C-H bonds are acidified and deprotonate; the resulting alpha-amino radical is readily further oxidized to an iminium ion"
  applicabilityConditions :=
    ["unfunctionalized aliphatic amine", "an alpha C-H bond",
     "single-electron oxidation followed by alpha-deprotonation and further oxidation"]
  exclusions :=
    ["does not select a unique alpha site when several are inequivalent",
     "does not establish yield or exclusive product formation"]

def amineSETRule : ScopedMechanismRule where
  evidence := ganleyMurrayKnowles2020
  kind := .amineSingleElectronOxidation
  substrateScope := "neutral unfunctionalized aliphatic tertiary amine"
  outcomeScope := "same sigma skeleton with an aminium radical-cation center"

def alphaDeprotonationRule : ScopedMechanismRule where
  evidence := ganleyMurrayKnowles2020
  kind := .alphaDeprotonation
  substrateScope := "aminium radical cation bearing an alpha C-H bond"
  outcomeScope := "loss of the alpha proton and formation of an alpha-amino carbon radical"

def alphaRadicalOxidationRule : ScopedMechanismRule where
  evidence := ganleyMurrayKnowles2020
  kind := .alphaRadicalFurtherOxidation
  substrateScope := "alpha-amino carbon radical"
  outcomeScope := "one-electron oxidation to the corresponding iminium N=C unit"

def aqueousIminiumHydrolysisRule : ScopedMechanismRule where
  evidence := liEtAl2023
  kind := .aqueousIminiumHydrolysis
  substrateScope := "triethanolamine-derived iminium species in water"
  outcomeScope := "N-C cleavage to diethanolamine and glycolaldehyde"

def LiteratureBridgeMatchesBoundSource : Prop :=
  liEtAl2023.doi = "10.1039/d3ra06585e" ∧
  liEtAl2023.contentSha256 =
    "c7b4ca676090fa1bd4c53210bd7196c2c8f7956fc13d91d236f31802132137ab" ∧
  ganleyMurrayKnowles2020.doi = "10.1021/acscatal.0c03567" ∧
  ganleyMurrayKnowles2020.contentSha256 =
    "1edf92b800f619e80e11bca830a5a246a1e95578bbd75825eba611f964794a67" ∧
  amineSETRule.evidence = ganleyMurrayKnowles2020 ∧
  amineSETRule.kind = .amineSingleElectronOxidation ∧
  alphaDeprotonationRule.evidence = ganleyMurrayKnowles2020 ∧
  alphaDeprotonationRule.kind = .alphaDeprotonation ∧
  alphaRadicalOxidationRule.evidence = ganleyMurrayKnowles2020 ∧
  alphaRadicalOxidationRule.kind = .alphaRadicalFurtherOxidation ∧
  aqueousIminiumHydrolysisRule.evidence = liEtAl2023 ∧
  aqueousIminiumHydrolysisRule.kind = .aqueousIminiumHydrolysis ∧
  TertiaryAmineCenter triethanolamineGraph 0 1 9 17 ∧
  1 ∈ sourceAlphaSites ∧ 9 ∈ sourceAlphaSites ∧ 17 ∈ sourceAlphaSites

/-! ## Explicit graph-edit semantics of the four arrows -/

def FirstElectronStep (before after : MolecularGraph) (nitrogen : ℕ) : Prop :=
  (∃ c1 c2 c3, TertiaryAmineCenter before nitrogen c1 c2 c3) ∧
  after = oneElectronOxidationAtNitrogen before nitrogen

def AlphaDeprotonationStep (before after : MolecularGraph)
    (nitrogen alpha hydrogen : ℕ) : Prop :=
  (∃ c2 c3, RadicalCationAmineCenter before nitrogen alpha c2 c3) ∧
  before.HasAtomState hydrogen .H 0 0 ∧
  before.HasBond alpha hydrogen .single ∧
  after = alphaDeprotonationTransform before nitrogen alpha hydrogen

def SecondElectronStep (before after : MolecularGraph)
    (nitrogen alpha : ℕ) : Prop :=
  AlphaAminoCarbonRadical before nitrogen alpha ∧
  after = alphaRadicalOxidationTransform before nitrogen alpha

def IsCutPartition (m : MolecularGraph) (nitrogen alpha : ℕ)
    (amineIds carbonylIds : Finset ℕ) : Prop :=
  Disjoint amineIds carbonylIds ∧
  amineIds ∪ carbonylIds = m.atomIds ∧
  nitrogen ∈ amineIds ∧ alpha ∈ carbonylIds ∧
  m.HasBond nitrogen alpha .double ∧
  ∀ b ∈ m.bonds, ¬ b.connects nitrogen alpha →
    ((b.left ∈ amineIds ∧ b.right ∈ amineIds) ∨
     (b.left ∈ carbonylIds ∧ b.right ∈ carbonylIds))

def IsWaterAt (m : MolecularGraph) (h1 oxygen h2 : ℕ) : Prop :=
  m.atoms = [hAtom h1, oAtom oxygen, hAtom h2] ∧
  m.bonds = [singleBond h1 oxygen, singleBond oxygen h2]

def IsProtonAt (m : MolecularGraph) (h : ℕ) : Prop :=
  m.atoms = [protonAtom h] ∧ m.bonds = []

def IminiumHydrolysisStep
    (before water amine aldehyde proton : MolecularGraph)
    (nitrogen alpha waterH waterO protonH : ℕ)
    (amineIds aldehydeIds : Finset ℕ) : Prop :=
  IminiumCenter before nitrogen alpha ∧
  IsCutPartition before nitrogen alpha amineIds aldehydeIds ∧
  IsWaterAt water waterH waterO protonH ∧
  amine = hydrolysisAmineProduct before amineIds nitrogen waterH ∧
  aldehyde = hydrolysisAldehydeProduct before aldehydeIds alpha waterO ∧
  IsProtonAt proton protonH

inductive TransformationClass
  | qualitativeNamedTransformOnly
  | quantitativeMaterialStage
  deriving DecidableEq, Repr

def selectedTransformationClass : TransformationClass :=
  .quantitativeMaterialStage

inductive Medium
  | acidic
  | aqueous
  deriving DecidableEq, Repr

inductive LifetimeClass
  | shortLived
  | stableOrUnspecified
  deriving DecidableEq, Repr

inductive ArrowOperation
  | losesOneElectron
  | losesOneProton
  | addsWaterLosesProton
  deriving DecidableEq, Repr

structure SourceArrowCue where
  operation : ArrowOperation
  medium : Medium
  locator : EvidenceLocator
  tailLifetime : LifetimeClass
  headLifetime : LifetimeClass
  deriving DecidableEq, Repr

def arrow2to3 : SourceArrowCue where
  operation := .losesOneElectron
  medium := .aqueous
  locator := firstElectronArrowLocator
  tailLifetime := .stableOrUnspecified
  headLifetime := .shortLived

def arrow3to4 : SourceArrowCue where
  operation := .losesOneProton
  medium := .aqueous
  locator := alphaProtonArrowLocator
  tailLifetime := .shortLived
  headLifetime := .shortLived

def arrow4to5 : SourceArrowCue where
  operation := .losesOneElectron
  medium := .aqueous
  locator := secondElectronArrowLocator
  tailLifetime := .shortLived
  headLifetime := .shortLived

def arrow5to6plus7 : SourceArrowCue where
  operation := .addsWaterLosesProton
  medium := .aqueous
  locator := hydrolysisArrowLocator
  tailLifetime := .shortLived
  headLifetime := .stableOrUnspecified

def SourceArrowCueAudit : Prop :=
  arrow2to3.operation = .losesOneElectron ∧
  arrow3to4.operation = .losesOneProton ∧
  arrow4to5.operation = .losesOneElectron ∧
  arrow5to6plus7.operation = .addsWaterLosesProton ∧
  arrow2to3.medium = .aqueous ∧ arrow3to4.medium = .aqueous ∧
  arrow4to5.medium = .aqueous ∧ arrow5to6plus7.medium = .aqueous ∧
  arrow2to3.locator = firstElectronArrowLocator ∧
  arrow3to4.locator = alphaProtonArrowLocator ∧
  arrow4to5.locator = secondElectronArrowLocator ∧
  arrow5to6plus7.locator = hydrolysisArrowLocator ∧
  arrow2to3.headLifetime = .shortLived ∧
  arrow3to4.tailLifetime = .shortLived ∧
  arrow3to4.headLifetime = .shortLived ∧
  arrow4to5.tailLifetime = .shortLived ∧
  arrow4to5.headLifetime = .shortLived ∧
  arrow5to6plus7.tailLifetime = .shortLived ∧
  lifetimeLocator.sourceSha256 = problemImageSha256

def ProblemContextAudit : Prop :=
  photocatalyticContextLocator.provenance = .problemImage ∧
  photocatalyticContextLocator.pathOrUrl =
    "icho_2026_source/image/T8_page-1.png" ∧
  photocatalyticContextLocator.sourceSha256 = problemImageSha256 ∧
  structure2Locator.sourceSha256 = problemImageSha256

/-- Every applicability condition used from the two papers is paired here
with the bound substrate/context and the exact aqueous arrow cues. -/
def LiteratureApplicabilityAudit : Prop :=
  LiteratureBridgeMatchesBoundSource ∧ ProblemContextAudit ∧
  SourceArrowCueAudit ∧
  liEtAl2023.applicabilityConditions =
    ["triethanolamine substrate", "aqueous solution",
     "photoinduced electron transfer / CO2-reduction setting"] ∧
  ganleyMurrayKnowles2020.applicabilityConditions =
    ["unfunctionalized aliphatic amine", "an alpha C-H bond",
     "single-electron oxidation followed by alpha-deprotonation and further oxidation"] ∧
  TertiaryAmineCenter triethanolamineGraph 0 1 9 17 ∧
  triethanolamineGraph.HasAtomState 5 .H 0 0 ∧
  triethanolamineGraph.HasBond 1 5 .single ∧
  arrow2to3.medium = .aqueous ∧ arrow3to4.medium = .aqueous ∧
  arrow4to5.medium = .aqueous ∧ arrow5to6plus7.medium = .aqueous

def EvidenceBackedFirstElectronStep
    (before after : MolecularGraph) (nitrogen : ℕ) : Prop :=
  amineSETRule.kind = .amineSingleElectronOxidation ∧
  amineSETRule.evidence = ganleyMurrayKnowles2020 ∧
  FirstElectronStep before after nitrogen

def EvidenceBackedAlphaDeprotonationStep
    (before after : MolecularGraph) (nitrogen alpha hydrogen : ℕ) : Prop :=
  alphaDeprotonationRule.kind = .alphaDeprotonation ∧
  alphaDeprotonationRule.evidence = ganleyMurrayKnowles2020 ∧
  AlphaDeprotonationStep before after nitrogen alpha hydrogen

def EvidenceBackedSecondElectronStep
    (before after : MolecularGraph) (nitrogen alpha : ℕ) : Prop :=
  alphaRadicalOxidationRule.kind = .alphaRadicalFurtherOxidation ∧
  alphaRadicalOxidationRule.evidence = ganleyMurrayKnowles2020 ∧
  SecondElectronStep before after nitrogen alpha

def EvidenceBackedHydrolysisStep
    (before water amine aldehyde proton : MolecularGraph)
    (nitrogen alpha waterH waterO protonH : ℕ)
    (amineIds aldehydeIds : Finset ℕ) : Prop :=
  aqueousIminiumHydrolysisRule.kind = .aqueousIminiumHydrolysis ∧
  aqueousIminiumHydrolysisRule.evidence = liEtAl2023 ∧
  IminiumHydrolysisStep before water amine aldehyde proton
    nitrogen alpha waterH waterO protonH amineIds aldehydeIds

/-- This is deliberately one-way: the candidate aldehyde is compatible with
the printed positive test; the test is not used as an inverse classifier. -/
def TollensObservationCompatibility (m : MolecularGraph) : Prop :=
  tollensLocator.provenance = .problemImage ∧
  tollensLocator.sourceSha256 = problemImageSha256 ∧
  HasAldehydeGroup m

def MechanismGraphPath : Prop :=
  LiteratureApplicabilityAudit ∧
  EvidenceBackedFirstElectronStep triethanolamineGraph structure3Graph 0 ∧
  EvidenceBackedAlphaDeprotonationStep structure3Graph structure4Graph 0 1 5 ∧
  EvidenceBackedSecondElectronStep structure4Graph structure5Graph 0 1 ∧
  EvidenceBackedHydrolysisStep structure5Graph hydrolysisWaterGraph
    structure6Graph structure7Graph releasedProtonGraph
    0 1 25 26 27 amineFragmentIds aldehydeFragmentIds ∧
  TollensObservationCompatibility structure7Graph

/-! ## Complete finite species domain and conservation ledgers -/

inductive Species
  | carbonDioxide
  | proton
  | electron
  | carbonMonoxide
  | water
  | reductant2
  | intermediate3
  | intermediate4
  | intermediate5
  | product6
  | product7
  deriving DecidableEq, Fintype, Repr

def speciesFormula : Species → MolecularFormula
  | .carbonDioxide => { carbon := 1, hydrogen := 0, nitrogen := 0, oxygen := 2 }
  | .proton => { carbon := 0, hydrogen := 1, nitrogen := 0, oxygen := 0 }
  | .electron => { carbon := 0, hydrogen := 0, nitrogen := 0, oxygen := 0 }
  | .carbonMonoxide => { carbon := 1, hydrogen := 0, nitrogen := 0, oxygen := 1 }
  | .water => { carbon := 0, hydrogen := 2, nitrogen := 0, oxygen := 1 }
  | .reductant2 => triethanolamineGraph.formula
  | .intermediate3 => structure3Graph.formula
  | .intermediate4 => structure4Graph.formula
  | .intermediate5 => structure5Graph.formula
  | .product6 => structure6Graph.formula
  | .product7 => structure7Graph.formula

def speciesCharge : Species → ℤ
  | .proton => 1
  | .electron => -1
  | .reductant2 => triethanolamineGraph.netCharge
  | .intermediate3 => structure3Graph.netCharge
  | .intermediate4 => structure4Graph.netCharge
  | .intermediate5 => structure5Graph.netCharge
  | .product6 => structure6Graph.netCharge
  | .product7 => structure7Graph.netCharge
  | _ => 0

def complexAtomCount (c : CRNT.Complex Species) (e : Element) : ℕ :=
  ∑ s : Species, c s * (speciesFormula s).atomCount e

def complexCharge (c : CRNT.Complex Species) : ℤ :=
  ∑ s : Species, (c s : ℤ) * speciesCharge s

def AtomBalanced (r : CRNT.Reaction Species) : Prop :=
  ∀ e : Element, complexAtomCount r.source e = complexAtomCount r.target e

def ChargeBalanced (r : CRNT.Reaction Species) : Prop :=
  complexCharge r.source = complexCharge r.target

def firstOxidationReaction : CRNT.Reaction Species where
  source
    | .reductant2 => 1
    | _ => 0
  target
    | .intermediate3 => 1
    | .electron => 1
    | _ => 0

def alphaDeprotonationReaction : CRNT.Reaction Species where
  source
    | .intermediate3 => 1
    | _ => 0
  target
    | .intermediate4 => 1
    | .proton => 1
    | _ => 0

def secondOxidationReaction : CRNT.Reaction Species where
  source
    | .intermediate4 => 1
    | _ => 0
  target
    | .intermediate5 => 1
    | .electron => 1
    | _ => 0

def hydrolysisReaction : CRNT.Reaction Species where
  source
    | .intermediate5 => 1
    | .water => 1
    | _ => 0
  target
    | .product6 => 1
    | .product7 => 1
    | .proton => 1
    | _ => 0

/-! Closed source-derived domain for balancing the previous acidic half
reaction. Proton and electron coefficients are deliberately not fixed. -/
def acidHalfAllowedSource : Finset Species :=
  {.carbonDioxide, .proton, .electron}

def acidHalfAllowedTarget : Finset Species :=
  {.carbonMonoxide, .water}

def UsesOnly (c : CRNT.Complex Species) (allowed : Finset Species) : Prop :=
  ∀ s : Species, s ∉ allowed → c s = 0

def IsCO2ToCOInAcid (r : CRNT.Reaction Species) : Prop :=
  r.source .carbonDioxide = 1 ∧
  r.target .carbonMonoxide = 1 ∧
  UsesOnly r.source acidHalfAllowedSource ∧
  UsesOnly r.target acidHalfAllowedTarget ∧
  AtomBalanced r ∧ ChargeBalanced r

def co2ReductionHalfReaction : CRNT.Reaction Species where
  source
    | .carbonDioxide => 1
    | .proton => 2
    | .electron => 2
    | _ => 0
  target
    | .carbonMonoxide => 1
    | .water => 1
    | _ => 0

/-- After cancellation of the two electrons, two protons, and one water
between the two half processes, this is the one-event coupled ledger. -/
def coupledRedoxReaction : CRNT.Reaction Species where
  source
    | .reductant2 => 1
    | .carbonDioxide => 1
    | _ => 0
  target
    | .product6 => 1
    | .product7 => 1
    | .carbonMonoxide => 1
    | _ => 0

def stagedSpeciesDomain : Finset Species := Finset.univ

inductive MaterialClaimScope
  | oneEventStoichiometryOnly
  deriving DecidableEq, Repr

def materialClaimScope : MaterialClaimScope :=
  .oneEventStoichiometryOnly

def PreviousPartDerived : Prop :=
  IsCO2ToCOInAcid co2ReductionHalfReaction ∧
  co2ReductionHalfReaction.source .proton = 2 ∧
  co2ReductionHalfReaction.source .electron = 2 ∧
  co2ReductionHalfReaction.target .water = 1

def ElectronProtonCoupling : Prop :=
  firstOxidationReaction.target .electron = 1 ∧
  secondOxidationReaction.target .electron = 1 ∧
  alphaDeprotonationReaction.target .proton = 1 ∧
  hydrolysisReaction.target .proton = 1 ∧
  co2ReductionHalfReaction.source .electron =
    firstOxidationReaction.target .electron +
      secondOxidationReaction.target .electron ∧
  co2ReductionHalfReaction.source .proton =
    alphaDeprotonationReaction.target .proton +
      hydrolysisReaction.target .proton

/-- Named carrier for every outcome-decisive conservation dimension. The
finite inductive species type forbids anonymous residual or catch-all streams. -/
def StagedSpeciesDomainAudit : Prop :=
  selectedTransformationClass = .quantitativeMaterialStage ∧
  materialClaimScope = .oneEventStoichiometryOnly ∧
  stagedSpeciesDomain = Finset.univ ∧
  AtomBalanced firstOxidationReaction ∧
  ChargeBalanced firstOxidationReaction ∧
  AtomBalanced alphaDeprotonationReaction ∧
  ChargeBalanced alphaDeprotonationReaction ∧
  AtomBalanced secondOxidationReaction ∧
  ChargeBalanced secondOxidationReaction ∧
  AtomBalanced hydrolysisReaction ∧
  ChargeBalanced hydrolysisReaction ∧
  AtomBalanced co2ReductionHalfReaction ∧
  ChargeBalanced co2ReductionHalfReaction ∧
  AtomBalanced coupledRedoxReaction ∧
  ChargeBalanced coupledRedoxReaction ∧
  ElectronProtonCoupling

/-! ## Source structure and representative-arm audits -/

def SourceStructure2Spec : Prop :=
  structure2Locator.provenance = .problemImage ∧
  structure2Locator.pathOrUrl = "icho_2026_source/image/T8_page-1.png" ∧
  structure2Locator.sourceSha256 = problemImageSha256 ∧
  ValidMolecularGraph triethanolamineGraph ∧
  triethanolamineGraph.formula =
    { carbon := 6, hydrogen := 15, nitrogen := 1, oxygen := 3 } ∧
  TertiaryAmineCenter triethanolamineGraph 0 1 9 17 ∧
  HydroxyethylArm triethanolamineGraph 0 1 2 3 4 5 6 7 8 ∧
  HydroxyethylArm triethanolamineGraph 0 9 10 11 12 13 14 15 16 ∧
  HydroxyethylArm triethanolamineGraph 0 17 18 19 20 21 22 23 24 ∧
  sourceAlphaSites = {1, 9, 17}

def GraphInventoryAudit : Prop :=
  ValidMolecularGraph structure3Graph ∧
  ValidMolecularGraph structure4Graph ∧
  ValidMolecularGraph structure5Graph ∧
  ValidMolecularGraph hydrolysisWaterGraph ∧
  ValidMolecularGraph structure6Graph ∧
  ValidMolecularGraph structure7Graph ∧
  ValidMolecularGraph releasedProtonGraph ∧
  NoStereochemistry structure3Graph ∧
  NoStereochemistry structure4Graph ∧
  NoStereochemistry structure5Graph ∧
  NoStereochemistry structure6Graph ∧
  NoStereochemistry structure7Graph

def DerivationContext : Prop :=
  SourceStructure2Spec ∧
  LiteratureBridgeMatchesBoundSource ∧
  SourceArrowCueAudit ∧
  PreviousPartDerived ∧
  MechanismGraphPath ∧
  GraphInventoryAudit ∧
  StagedSpeciesDomainAudit

/-! ## One explicit requested-output carrier per structure -/

def Structure3Output : Prop :=
  DerivationContext ∧
  structure3Graph = oneElectronOxidationAtNitrogen triethanolamineGraph 0 ∧
  ValidMolecularGraph structure3Graph ∧ NoStereochemistry structure3Graph ∧
  structure3Graph.formula =
    { carbon := 6, hydrogen := 15, nitrogen := 1, oxygen := 3 } ∧
  structure3Graph.netCharge = 1 ∧
  structure3Graph.radicalElectronCount = 1 ∧
  RadicalCationAmineCenter structure3Graph 0 1 9 17

def Structure4Output : Prop :=
  DerivationContext ∧
  structure4Graph = alphaDeprotonationTransform structure3Graph 0 1 5 ∧
  ValidMolecularGraph structure4Graph ∧ NoStereochemistry structure4Graph ∧
  structure4Graph.formula =
    { carbon := 6, hydrogen := 14, nitrogen := 1, oxygen := 3 } ∧
  structure4Graph.netCharge = 0 ∧
  structure4Graph.radicalElectronCount = 1 ∧
  AlphaAminoCarbonRadical structure4Graph 0 1

def Structure5Output : Prop :=
  DerivationContext ∧
  structure5Graph = alphaRadicalOxidationTransform structure4Graph 0 1 ∧
  ValidMolecularGraph structure5Graph ∧ NoStereochemistry structure5Graph ∧
  structure5Graph.formula =
    { carbon := 6, hydrogen := 14, nitrogen := 1, oxygen := 3 } ∧
  structure5Graph.netCharge = 1 ∧
  structure5Graph.radicalElectronCount = 0 ∧
  IminiumCenter structure5Graph 0 1

def Structure6Output : Prop :=
  DerivationContext ∧
  structure6Graph =
    hydrolysisAmineProduct structure5Graph amineFragmentIds 0 25 ∧
  NoStereochemistry structure6Graph ∧
  IsDiethanolamineStructure structure6Graph

def Structure7Output : Prop :=
  DerivationContext ∧
  structure7Graph =
    hydrolysisAldehydeProduct structure5Graph aldehydeFragmentIds 1 26 ∧
  NoStereochemistry structure7Graph ∧
  IsGlycolaldehydeStructure structure7Graph ∧
  HasAldehydeGroup structure7Graph

/-! ## Autoformalization proof obligations -/

lemma noStereochemistry_setElectronicState
    {m : MolecularGraph} (h : NoStereochemistry m)
    (id : ℕ) (charge : ℤ) (unpaired : ℕ) :
    NoStereochemistry (m.setElectronicState id charge unpaired) := by
  constructor
  · intro a ha
    change a ∈ m.atoms.map (fun a' =>
      if a'.id = id then
        { a' with formalCharge := charge, unpairedElectrons := unpaired }
      else a') at ha
    rcases List.mem_map.mp ha with ⟨a', ha', rfl⟩
    split <;> simpa using h.1 a' ha'
  · simpa [MolecularGraph.setElectronicState] using h.2

lemma noStereochemistry_removeAtom
    {m : MolecularGraph} (h : NoStereochemistry m) (id : ℕ) :
    NoStereochemistry (m.removeAtom id) := by
  constructor
  · intro a ha
    exact h.1 a (List.mem_filter.mp ha).1
  · intro b hb
    exact h.2 b (List.mem_filter.mp hb).1

lemma noStereochemistry_setBondOrder
    {m : MolecularGraph} (h : NoStereochemistry m)
    (i j : ℕ) (order : BondOrder) :
    NoStereochemistry (m.setBondOrder i j order) := by
  constructor
  · simpa [MolecularGraph.setBondOrder] using h.1
  · intro b hb
    change b ∈ m.bonds.map (fun b' =>
      if b'.connects i j then { b' with order := order } else b') at hb
    rcases List.mem_map.mp hb with ⟨b', hb', rfl⟩
    split <;> simpa using h.2 b' hb'

lemma noStereochemistry_inducedBy
    {m : MolecularGraph} (h : NoStereochemistry m) (ids : Finset ℕ) :
    NoStereochemistry (m.inducedBy ids) := by
  constructor
  · intro a ha
    exact h.1 a (List.mem_filter.mp ha).1
  · intro b hb
    exact h.2 b (List.mem_filter.mp hb).1

lemma noStereochemistry_addAtom
    {m : MolecularGraph} (h : NoStereochemistry m) (a : AtomSite)
    (ha : a.stereochemistry = .notStereogenic) :
    NoStereochemistry (m.addAtom a) := by
  constructor
  · intro a' ha'
    change a' ∈ m.atoms ++ [a] at ha'
    rcases List.mem_append.mp ha' with ha' | ha'
    · exact h.1 a' ha'
    · rw [List.mem_singleton] at ha'
      subst a'
      exact ha
  · simpa [MolecularGraph.addAtom] using h.2

lemma noStereochemistry_addBond
    {m : MolecularGraph} (h : NoStereochemistry m) (b : Bond)
    (hb : b.stereochemistry = .none) :
    NoStereochemistry (m.addBond b) := by
  constructor
  · simpa [MolecularGraph.addBond] using h.1
  · intro b' hb'
    change b' ∈ m.bonds ++ [b] at hb'
    rcases List.mem_append.mp hb' with hb' | hb'
    · exact h.2 b' hb'
    · rw [List.mem_singleton] at hb'
      subst b'
      exact hb

lemma triethanolamine_noStereochemistry :
    NoStereochemistry triethanolamineGraph := by
  simp [NoStereochemistry, triethanolamineGraph, triethanolamineBonds,
    atomSite, hAtom, cAtom, nAtom, oAtom, singleBond, bond]

lemma structure3_noStereochemistry : NoStereochemistry structure3Graph := by
  exact noStereochemistry_setElectronicState
    triethanolamine_noStereochemistry 0 1 1

lemma structure4_noStereochemistry : NoStereochemistry structure4Graph := by
  exact noStereochemistry_setElectronicState
    (noStereochemistry_setElectronicState
      (noStereochemistry_removeAtom structure3_noStereochemistry 5) 0 0 0)
    1 0 1

lemma structure5_noStereochemistry : NoStereochemistry structure5Graph := by
  exact noStereochemistry_setBondOrder
    (noStereochemistry_setElectronicState
      (noStereochemistry_setElectronicState structure4_noStereochemistry
        0 1 0)
      1 0 0)
    0 1 .double

lemma structure6_noStereochemistry : NoStereochemistry structure6Graph := by
  exact noStereochemistry_addBond
    (noStereochemistry_addAtom
      (noStereochemistry_setElectronicState
        (noStereochemistry_inducedBy structure5_noStereochemistry
          amineFragmentIds)
        0 0 0)
      (hAtom 25) rfl)
    (singleBond 0 25) rfl

lemma structure7_noStereochemistry : NoStereochemistry structure7Graph := by
  exact noStereochemistry_addBond
    (noStereochemistry_addAtom
      (noStereochemistry_inducedBy structure5_noStereochemistry
        aldehydeFragmentIds)
      (oAtom 26) rfl)
    (doubleBond 1 26) rfl

theorem sourceStructure2_spec : SourceStructure2Spec := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · unfold ValidMolecularGraph
    native_decide
  · native_decide
  · simp [TertiaryAmineCenter, MolecularGraph.HasAtomState,
      MolecularGraph.HasBond, MolecularGraph.bondValenceAt,
      triethanolamineGraph, triethanolamineBonds, atomSite, hAtom, cAtom,
      nAtom, oAtom, singleBond, bond, BondOrder.valence]
  · simp [HydroxyethylArm, MolecularGraph.HasAtomState,
      MolecularGraph.HasBond, triethanolamineGraph, triethanolamineBonds,
      atomSite, hAtom, cAtom, nAtom, oAtom, singleBond, bond]
  · simp [HydroxyethylArm, MolecularGraph.HasAtomState,
      MolecularGraph.HasBond, triethanolamineGraph, triethanolamineBonds,
      atomSite, hAtom, cAtom, nAtom, oAtom, singleBond, bond]
  · simp [HydroxyethylArm, MolecularGraph.HasAtomState,
      MolecularGraph.HasBond, triethanolamineGraph, triethanolamineBonds,
      atomSite, hAtom, cAtom, nAtom, oAtom, singleBond, bond]

theorem literatureBridge_matches : LiteratureBridgeMatchesBoundSource := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_, ?_, ?_⟩
  · exact sourceStructure2_spec.2.2.2.2.2.1
  all_goals native_decide

theorem sourceArrowCueAudit_spec : SourceArrowCueAudit := by
  unfold SourceArrowCueAudit
  native_decide

theorem graphInventoryAudit_spec : GraphInventoryAudit := by
  have hvalid3 : ValidMolecularGraph structure3Graph := by
    unfold ValidMolecularGraph
    native_decide
  have hvalid4 : ValidMolecularGraph structure4Graph := by
    unfold ValidMolecularGraph
    native_decide
  have hvalid5 : ValidMolecularGraph structure5Graph := by
    unfold ValidMolecularGraph
    native_decide
  have hvalidWater : ValidMolecularGraph hydrolysisWaterGraph := by
    unfold ValidMolecularGraph
    native_decide
  have hvalid6 : ValidMolecularGraph structure6Graph := by
    unfold ValidMolecularGraph
    native_decide
  have hvalid7 : ValidMolecularGraph structure7Graph := by
    unfold ValidMolecularGraph
    native_decide
  have hvalidProton : ValidMolecularGraph releasedProtonGraph := by
    unfold ValidMolecularGraph
    native_decide
  exact ⟨hvalid3, hvalid4, hvalid5, hvalidWater, hvalid6, hvalid7,
    hvalidProton,
    structure3_noStereochemistry, structure4_noStereochemistry,
    structure5_noStereochemistry, structure6_noStereochemistry,
    structure7_noStereochemistry⟩

lemma structure3_radicalCationCenter :
    RadicalCationAmineCenter structure3Graph 0 1 9 17 := by
  simp [RadicalCationAmineCenter, MolecularGraph.HasAtomState,
    MolecularGraph.HasBond, MolecularGraph.bondValenceAt, structure3Graph,
    oneElectronOxidationAtNitrogen, MolecularGraph.setElectronicState,
    triethanolamineGraph, triethanolamineBonds, atomSite, hAtom, cAtom,
    nAtom, oAtom, singleBond, bond, BondOrder.valence]

lemma structure4_alphaAminoCarbonRadical :
    AlphaAminoCarbonRadical structure4Graph 0 1 := by
  simp [AlphaAminoCarbonRadical, MolecularGraph.HasAtomState,
    MolecularGraph.HasBond, MolecularGraph.bondValenceAt, structure4Graph,
    alphaDeprotonationTransform, structure3Graph,
    oneElectronOxidationAtNitrogen, MolecularGraph.removeAtom,
    MolecularGraph.setElectronicState, triethanolamineGraph,
    triethanolamineBonds, atomSite, hAtom, cAtom, nAtom, oAtom, singleBond,
    bond, BondOrder.valence]

lemma structure5_iminiumCenter : IminiumCenter structure5Graph 0 1 := by
  simp [IminiumCenter, MolecularGraph.HasAtomState, MolecularGraph.HasBond,
    MolecularGraph.bondValenceAt, structure5Graph,
    alphaRadicalOxidationTransform, structure4Graph,
    alphaDeprotonationTransform, structure3Graph,
    oneElectronOxidationAtNitrogen, MolecularGraph.setBondOrder,
    MolecularGraph.removeAtom, MolecularGraph.setElectronicState,
    triethanolamineGraph, triethanolamineBonds, atomSite, hAtom, cAtom,
    nAtom, oAtom, singleBond, doubleBond, bond, Bond.connects,
    BondOrder.valence]

lemma structure5_cutPartition :
    IsCutPartition structure5Graph 0 1 amineFragmentIds
      aldehydeFragmentIds := by
  refine ⟨?_, ?_, ?_, ?_, structure5_iminiumCenter.2.2.1, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · simp [structure5Graph, alphaRadicalOxidationTransform, structure4Graph,
      alphaDeprotonationTransform, structure3Graph,
      oneElectronOxidationAtNitrogen, MolecularGraph.setBondOrder,
      MolecularGraph.removeAtom, MolecularGraph.setElectronicState,
      triethanolamineGraph, triethanolamineBonds, amineFragmentIds,
      aldehydeFragmentIds, Bond.connects, singleBond, doubleBond, bond]

lemma structure7_hasAldehydeGroup : HasAldehydeGroup structure7Graph := by
  refine ⟨1, 26, 4, 2, ?_⟩
  simp [MolecularGraph.HasAtomState, MolecularGraph.HasBond, structure7Graph,
    hydrolysisAldehydeProduct, MolecularGraph.addBond,
    MolecularGraph.addAtom, MolecularGraph.inducedBy, structure5Graph,
    alphaRadicalOxidationTransform, structure4Graph,
    alphaDeprotonationTransform, structure3Graph,
    oneElectronOxidationAtNitrogen, MolecularGraph.setBondOrder,
    MolecularGraph.removeAtom, MolecularGraph.setElectronicState,
    triethanolamineGraph, triethanolamineBonds, aldehydeFragmentIds,
    atomSite, hAtom, cAtom, nAtom, oAtom, singleBond, doubleBond, bond,
    Bond.connects]

lemma literatureApplicabilityAudit_spec : LiteratureApplicabilityAudit := by
  refine ⟨literatureBridge_matches, ?_, sourceArrowCueAudit_spec, rfl, rfl,
    sourceStructure2_spec.2.2.2.2.2.1, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · unfold ProblemContextAudit
    native_decide
  · simp [MolecularGraph.HasAtomState, triethanolamineGraph, atomSite, hAtom,
      cAtom, nAtom, oAtom]
  · simp [MolecularGraph.HasBond, triethanolamineGraph,
      triethanolamineBonds, singleBond, bond]

theorem mechanismGraphPath_spec : MechanismGraphPath := by
  refine ⟨literatureApplicabilityAudit_spec, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, ?_⟩
    exact ⟨⟨1, 9, 17, sourceStructure2_spec.2.2.2.2.2.1⟩, rfl⟩
  · refine ⟨rfl, rfl, ?_⟩
    refine ⟨⟨9, 17, structure3_radicalCationCenter⟩, ?_, ?_, rfl⟩
    · simp [MolecularGraph.HasAtomState, structure3Graph,
        oneElectronOxidationAtNitrogen, MolecularGraph.setElectronicState,
        triethanolamineGraph, atomSite, hAtom, cAtom, nAtom, oAtom]
    · simp [MolecularGraph.HasBond, structure3Graph,
        oneElectronOxidationAtNitrogen, MolecularGraph.setElectronicState,
        triethanolamineGraph, triethanolamineBonds, singleBond, bond]
  · exact ⟨rfl, rfl, structure4_alphaAminoCarbonRadical, rfl⟩
  · have hwater : IsWaterAt hydrolysisWaterGraph 25 26 27 := by
      simp [IsWaterAt, hydrolysisWaterGraph, hAtom, oAtom, atomSite,
        singleBond, bond]
    have hproton : IsProtonAt releasedProtonGraph 27 := by
      simp [IsProtonAt, releasedProtonGraph, protonAtom, atomSite]
    exact ⟨rfl, rfl, structure5_iminiumCenter, structure5_cutPartition,
      hwater, rfl, rfl, hproton⟩
  · exact ⟨rfl, rfl, structure7_hasAldehydeGroup⟩

theorem co2ReductionHalfReaction_spec :
    IsCO2ToCOInAcid co2ReductionHalfReaction := by
  unfold IsCO2ToCOInAcid UsesOnly AtomBalanced ChargeBalanced
  native_decide

private theorem species_univ :
    (Finset.univ : Finset Species) =
      {.carbonDioxide, .proton, .electron, .carbonMonoxide, .water,
       .reductant2, .intermediate3, .intermediate4, .intermediate5,
       .product6, .product7} := by
  native_decide

theorem co2ReductionHalfReaction_unique
    (r : CRNT.Reaction Species) (h : IsCO2ToCOInAcid r) :
    r = co2ReductionHalfReaction := by
  rcases h with ⟨hCO2, hCO, hSource, hTarget, hAtoms, hCharge⟩
  have hsCO : r.source .carbonMonoxide = 0 :=
    hSource .carbonMonoxide (by native_decide)
  have hsWater : r.source .water = 0 :=
    hSource .water (by native_decide)
  have hsR2 : r.source .reductant2 = 0 :=
    hSource .reductant2 (by native_decide)
  have hs3 : r.source .intermediate3 = 0 :=
    hSource .intermediate3 (by native_decide)
  have hs4 : r.source .intermediate4 = 0 :=
    hSource .intermediate4 (by native_decide)
  have hs5 : r.source .intermediate5 = 0 :=
    hSource .intermediate5 (by native_decide)
  have hs6 : r.source .product6 = 0 :=
    hSource .product6 (by native_decide)
  have hs7 : r.source .product7 = 0 :=
    hSource .product7 (by native_decide)
  have htCO2 : r.target .carbonDioxide = 0 :=
    hTarget .carbonDioxide (by native_decide)
  have htProton : r.target .proton = 0 :=
    hTarget .proton (by native_decide)
  have htElectron : r.target .electron = 0 :=
    hTarget .electron (by native_decide)
  have htR2 : r.target .reductant2 = 0 :=
    hTarget .reductant2 (by native_decide)
  have ht3 : r.target .intermediate3 = 0 :=
    hTarget .intermediate3 (by native_decide)
  have ht4 : r.target .intermediate4 = 0 :=
    hTarget .intermediate4 (by native_decide)
  have ht5 : r.target .intermediate5 = 0 :=
    hTarget .intermediate5 (by native_decide)
  have ht6 : r.target .product6 = 0 :=
    hTarget .product6 (by native_decide)
  have ht7 : r.target .product7 = 0 :=
    hTarget .product7 (by native_decide)
  have hO := hAtoms .O
  simp [complexAtomCount, species_univ, speciesFormula,
    MolecularFormula.atomCount, hCO2, hCO, hsCO, hsWater, hsR2, hs3, hs4,
    hs5, hs6, hs7, htCO2, htProton, htElectron, htR2, ht3, ht4, ht5,
    ht6, ht7] at hO
  have hWater : r.target .water = 1 := by omega
  have hH := hAtoms .H
  simp [complexAtomCount, species_univ, speciesFormula,
    MolecularFormula.atomCount, hCO2, hCO, hsCO, hsWater, hsR2, hs3, hs4,
    hs5, hs6, hs7, htCO2, htProton, htElectron, htR2, ht3, ht4, ht5,
    ht6, ht7, hWater] at hH
  have hProton : r.source .proton = 2 := by omega
  simp [ChargeBalanced, complexCharge, species_univ, speciesCharge, hCO2,
    hCO, hsCO,
    hsWater, hsR2, hs3, hs4, hs5, hs6, hs7, htCO2, htProton, htElectron,
    htR2, ht3, ht4, ht5, ht6, ht7, hWater, hProton] at hCharge
  have hElectron : r.source .electron = 2 := by omega
  cases r with
  | mk source target =>
      have hSourceEq : source = co2ReductionHalfReaction.source := by
        funext s
        cases s <;> simp [co2ReductionHalfReaction] <;> assumption
      have hTargetEq : target = co2ReductionHalfReaction.target := by
        funext s
        cases s <;> simp [co2ReductionHalfReaction] <;> assumption
      cases hSourceEq
      cases hTargetEq
      rfl

theorem previousPartDerived_spec : PreviousPartDerived := by
  exact ⟨co2ReductionHalfReaction_spec, rfl, rfl, rfl⟩

theorem stagedSpeciesDomainAudit_spec : StagedSpeciesDomainAudit := by
  unfold StagedSpeciesDomainAudit AtomBalanced ChargeBalanced
    ElectronProtonCoupling
  native_decide

theorem derivationContext_spec : DerivationContext := by
  exact ⟨sourceStructure2_spec, literatureBridge_matches,
    sourceArrowCueAudit_spec, previousPartDerived_spec,
    mechanismGraphPath_spec, graphInventoryAudit_spec,
    stagedSpeciesDomainAudit_spec⟩

lemma structure6_isDiethanolamine :
    IsDiethanolamineStructure structure6Graph := by
  refine ⟨graphInventoryAudit_spec.2.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · refine ⟨0, 25, 9, 10, 11, 12, 13, 14, 15, 16,
      17, 18, 19, 20, 21, 22, 23, 24, ?_⟩
    simp [MolecularGraph.HasAtomState, MolecularGraph.HasBond,
      HydroxyethylArm, structure6Graph, hydrolysisAmineProduct,
      MolecularGraph.addBond, MolecularGraph.addAtom,
      MolecularGraph.inducedBy, MolecularGraph.setElectronicState,
      structure5Graph, alphaRadicalOxidationTransform, structure4Graph,
      alphaDeprotonationTransform, structure3Graph,
      oneElectronOxidationAtNitrogen, MolecularGraph.setBondOrder,
      MolecularGraph.removeAtom, triethanolamineGraph,
      triethanolamineBonds, amineFragmentIds, atomSite, hAtom, cAtom,
      nAtom, oAtom, singleBond, bond, Bond.connects]

lemma structure7_isGlycolaldehyde :
    IsGlycolaldehydeStructure structure7Graph := by
  refine ⟨graphInventoryAudit_spec.2.2.2.2.2.1, ?_, ?_, ?_,
    structure7_hasAldehydeGroup, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · refine ⟨1, 2, 3, 6, 7, 8, ?_⟩
    simp [MolecularGraph.HasAtomState, MolecularGraph.HasBond,
      structure7Graph, hydrolysisAldehydeProduct, MolecularGraph.addBond,
      MolecularGraph.addAtom, MolecularGraph.inducedBy, structure5Graph,
      alphaRadicalOxidationTransform, structure4Graph,
      alphaDeprotonationTransform, structure3Graph,
      oneElectronOxidationAtNitrogen, MolecularGraph.setBondOrder,
      MolecularGraph.removeAtom, MolecularGraph.setElectronicState,
      triethanolamineGraph, triethanolamineBonds, aldehydeFragmentIds,
      atomSite, hAtom, cAtom, nAtom, oAtom, singleBond, doubleBond, bond,
      Bond.connects]

theorem structure3Output_spec : Structure3Output := by
  refine ⟨derivationContext_spec, rfl, graphInventoryAudit_spec.1,
    structure3_noStereochemistry, ?_, ?_, ?_,
    structure3_radicalCationCenter⟩
  all_goals native_decide

theorem structure4Output_spec : Structure4Output := by
  refine ⟨derivationContext_spec, rfl, graphInventoryAudit_spec.2.1,
    structure4_noStereochemistry, ?_, ?_, ?_,
    structure4_alphaAminoCarbonRadical⟩
  all_goals native_decide

theorem structure5Output_spec : Structure5Output := by
  refine ⟨derivationContext_spec, rfl, graphInventoryAudit_spec.2.2.1,
    structure5_noStereochemistry, ?_, ?_, ?_, structure5_iminiumCenter⟩
  all_goals native_decide

theorem structure6Output_spec : Structure6Output := by
  exact ⟨derivationContext_spec, rfl, structure6_noStereochemistry,
    structure6_isDiethanolamine⟩

theorem structure7Output_spec : Structure7Output := by
  exact ⟨derivationContext_spec, rfl, structure7_noStereochemistry,
    structure7_isGlycolaldehyde, structure7_hasAldehydeGroup⟩

/-! ## Answer-blind raw and exact-symbolic reported contracts -/

def RawResult : Prop :=
  DerivationContext ∧
  Structure3Output ∧ Structure4Output ∧ Structure5Output ∧
  Structure6Output ∧ Structure7Output

def ReportedResult : Prop :=
  Structure3Output ∧ Structure4Output ∧ Structure5Output ∧
  Structure6Output ∧ Structure7Output ∧
  selectedTransformationClass = .quantitativeMaterialStage ∧
  materialClaimScope = .oneEventStoichiometryOnly

theorem rawResult_spec : RawResult := by
  exact ⟨derivationContext_spec, structure3Output_spec,
    structure4Output_spec, structure5Output_spec,
    structure6Output_spec, structure7Output_spec⟩

theorem reportedResult_spec : ReportedResult := by
  exact ⟨structure3Output_spec, structure4Output_spec,
    structure5Output_spec, structure6Output_spec,
    structure7Output_spec, rfl, rfl⟩

/-- Hash-bound raw solve-phase result contract. The payload literal is
regenerated from `blind_candidates/icho_2026_t8_a2.json`. -/
theorem rawResultContract :
    ("ef57f459d5c5de48a8820b0bacfe799576832ec2876d37dc1b82b84ad58b0224" : String) =
      "ef57f459d5c5de48a8820b0bacfe799576832ec2876d37dc1b82b84ad58b0224" ∧
    RawResult := by
  exact ⟨rfl, rawResult_spec⟩

/-- Hash-bound exact-symbolic reported result contract. -/
theorem reportedResultContract :
    ("0dadf2ad109287d1257ef414bf3977bc6714aa1d2fd64a514832dbf5e3977ea4" : String) =
      "0dadf2ad109287d1257ef414bf3977bc6714aa1d2fd64a514832dbf5e3977ea4" ∧
    ReportedResult := by
  exact ⟨rfl, reportedResult_spec⟩

end ProblemIChO2026T8A2
end IChO2026Problems
