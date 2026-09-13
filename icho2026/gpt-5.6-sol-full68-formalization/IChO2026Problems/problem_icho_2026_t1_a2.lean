import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T1-A2: the blue constituent

This file is an answer-blind formalization of the three requested symbolic
outputs.  Molecular structures are finite, fully labelled Lewis graphs: every
carbon and hydrogen atom is a vertex, every displayed or implicit bond is in
the bond list, and charge, radical, atom-stereo, and bond-stereo fields are
explicit.  The structure read from the problem figure and the independently
named database structure are kept separate and related by an isomorphism
obligation.
-/

set_option autoImplicit false

namespace IChO2026Problems.T1A2

/-! ## Provenance and source locations -/

inductive EvidenceProvenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
deriving DecidableEq, Repr

inductive SourceLocator where
  | page2PlantCompoundTable
  | page2CompoundSevenPanel
  | page3OpeningParagraph
  | page3Question12
deriving DecidableEq, Repr

inductive StagedTransformationUse where
  | qualitativeNamedTransformOnly
  | quantitativeMaterialStage
deriving DecidableEq, Repr

structure ExternalReference where
  title : String
  stableURL : String
  doi : Option String
  locator : String
  scopedClaim : String
  applicabilityConditions : List String
deriving DecidableEq, Repr

/-! ## Formulae, atoms, bonds, and complete molecular structures -/

structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  chlorine : ℕ
deriving DecidableEq, Repr

inductive Element where
  | hydrogen
  | carbon
  | oxygen
  | chlorine
deriving DecidableEq, Fintype, Repr

def MolecularFormula.atomCount (formula : MolecularFormula) : Element → ℕ
  | .hydrogen => formula.hydrogen
  | .carbon => formula.carbon
  | .oxygen => formula.oxygen
  | .chlorine => formula.chlorine

def zeroFormula : MolecularFormula := ⟨0, 0, 0, 0⟩

inductive AtomStereo where
  | notStereogenic
  | rectus
  | sinister
deriving DecidableEq, Repr

inductive BondStereo where
  | notStereogenic
  | together
  | opposite
deriving DecidableEq, Repr

inductive BondOrder where
  | single
  | double
  | triple
deriving DecidableEq, Repr

def BondOrder.valence : BondOrder → ℕ
  | .single => 1
  | .double => 2
  | .triple => 3

structure AtomSpec where
  element : Element
  isotopeMassNumber : Option ℕ
  formalCharge : ℤ
  radicalElectrons : ℕ
  stereo : AtomStereo
deriving DecidableEq, Repr

def neutralAtom (element : Element) : AtomSpec where
  element := element
  isotopeMassNumber := none
  formalCharge := 0
  radicalElectrons := 0
  stereo := .notStereogenic

/-- Every atom is an explicit vertex.  Vertices `0, ..., c-1` are carbon and
the remaining `h` vertices are hydrogen. -/
def hydrocarbonAtoms (c h : ℕ) : Fin (c + h) → AtomSpec := fun i =>
  if i.val < c then neutralAtom .carbon else neutralAtom .hydrogen

structure Bond (n : ℕ) where
  left : Fin n
  right : Fin n
  order : BondOrder
  stereo : BondStereo
deriving DecidableEq, Repr

def mkBond {n : ℕ} (left right : Fin n) (order : BondOrder) : Bond n where
  left := left
  right := right
  order := order
  stereo := .notStereogenic

structure MolecularStructure where
  atomCount : ℕ
  atoms : Fin atomCount → AtomSpec
  bonds : List (Bond atomCount)

def Bond.connects {n : ℕ} (b : Bond n) (i j : Fin n) : Bool :=
  (b.left == i && b.right == j) || (b.left == j && b.right == i)

def MolecularStructure.bondOrderAt
    (m : MolecularStructure) (i j : Fin m.atomCount) : ℕ :=
  (m.bonds.map fun b => if b.connects i j then b.order.valence else 0).sum

def MolecularStructure.valenceAt
    (m : MolecularStructure) (i : Fin m.atomCount) : ℕ :=
  (m.bonds.map fun b =>
    if b.left = i ∨ b.right = i then b.order.valence else 0).sum

def MolecularStructure.elementCount
    (m : MolecularStructure) (element : Element) : ℕ :=
  (Finset.univ.filter fun i => (m.atoms i).element = element).card

def MolecularStructure.formula (m : MolecularStructure) : MolecularFormula where
  carbon := m.elementCount .carbon
  hydrogen := m.elementCount .hydrogen
  oxygen := m.elementCount .oxygen
  chlorine := m.elementCount .chlorine

def MolecularStructure.netFormalCharge (m : MolecularStructure) : ℤ :=
  ∑ i : Fin m.atomCount, (m.atoms i).formalCharge

def MolecularStructure.totalRadicalElectrons (m : MolecularStructure) : ℕ :=
  ∑ i : Fin m.atomCount, (m.atoms i).radicalElectrons

def expectedValence : Element → ℕ
  | .hydrogen => 1
  | .carbon => 4
  | .oxygen => 2
  | .chlorine => 1

def MolecularStructure.bonded
    (m : MolecularStructure) (i j : Fin m.atomCount) : Prop :=
  m.bondOrderAt i j > 0

def MolecularStructure.connected (m : MolecularStructure) : Prop :=
  ∀ i j : Fin m.atomCount, Relation.ReflTransGen m.bonded i j

def MolecularStructure.wellFormedLewis (m : MolecularStructure) : Prop :=
  m.bonds.Nodup ∧
  (∀ b ∈ m.bonds, b.left ≠ b.right) ∧
  (∀ i : Fin m.atomCount,
    m.valenceAt i = expectedValence (m.atoms i).element) ∧
  m.netFormalCharge = 0 ∧
  m.totalRadicalElectrons = 0 ∧
  m.connected

def MolecularStructure.noSpecifiedStereochemistry
    (m : MolecularStructure) : Prop :=
  (∀ i : Fin m.atomCount, (m.atoms i).stereo = .notStereogenic) ∧
  (∀ b ∈ m.bonds, b.stereo = .notStereogenic)

structure MolecularIsomorphism
    (first second : MolecularStructure) where
  atomEquiv : Fin first.atomCount ≃ Fin second.atomCount
  preservesAtom : ∀ i : Fin first.atomCount,
    first.atoms i = second.atoms (atomEquiv i)
  /-- Constitutional identity of an aromatic molecule is independent of which
  localized Kekulé contributor was used to draw its delocalized π system. -/
  preservesAdjacency : ∀ i j : Fin first.atomCount,
    first.bonded i j ↔ second.bonded (atomEquiv i) (atomEquiv j)

abbrev CarbonSite (m : MolecularStructure) :=
  {i : Fin m.atomCount // (m.atoms i).element = .carbon}

structure CarbonSkeletonEmbedding
    (core derivative : MolecularStructure) where
  toFun : CarbonSite core → CarbonSite derivative
  injective : Function.Injective toFun
  /-- The carbon skeleton is a topological carrier; alternating aromatic bond
  localization is deliberately not frozen by the embedding. -/
  preservesAdjacency : ∀ i j : CarbonSite core,
    core.bonded i.1 j.1 ↔ derivative.bonded (toFun i).1 (toFun j).1

def MolecularStructure.hydrogenNeighbourCount
    (m : MolecularStructure) (i : Fin m.atomCount) : ℕ :=
  (Finset.univ.filter fun j : Fin m.atomCount =>
    (m.atoms j).element = .hydrogen ∧ m.bondOrderAt i j = 1).card

/-! ## The ten source-table candidates and the isotope/mass filter -/

inductive TableCompound where
  | compound1
  | compound2
  | compound3
  | compound4
  | compound5
  | compound6
  | compound7
  | compound8
  | compound9
  | compound10
deriving DecidableEq, Fintype, Repr

/-- Formulae printed under the ten distinct numbered drawings on source page 2.
Compound 3 is drawn in three plant rows but is one numbered candidate. -/
def tableFormula : TableCompound → MolecularFormula
  | .compound1 => ⟨11, 14, 3, 0⟩
  | .compound2 => ⟨10, 18, 1, 0⟩
  | .compound3 => ⟨10, 18, 1, 0⟩
  | .compound4 => ⟨6, 12, 1, 0⟩
  | .compound5 => ⟨10, 12, 2, 0⟩
  | .compound6 => ⟨10, 18, 1, 0⟩
  | .compound7 => ⟨14, 16, 0, 0⟩
  | .compound8 => ⟨15, 24, 0, 0⟩
  | .compound9 => ⟨10, 16, 1, 0⟩
  | .compound10 => ⟨10, 18, 1, 0⟩

def tableCandidateDomain : Finset TableCompound := Finset.univ

structure CandidateDomainCertificate where
  provenance : EvidenceProvenance
  locator : SourceLocator
  distinctNumberedEntries : ℕ
  domain : Finset TableCompound

def tableCandidateDomainCertificate : CandidateDomainCertificate where
  provenance := .problemImage
  locator := .page2PlantCompoundTable
  distinctNumberedEntries := 10
  domain := tableCandidateDomain

structure IsotopeMassReference where
  element : Element
  massNumber : ℕ
  massValueDa : String
  uncertaintyDa : String
  datasetVersion : String
  datasetSha256 : String
  recordSha256 : String
  sourceURL : String
deriving DecidableEq, Repr

def pinnedDatasetVersion : String :=
  "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+" ++
    "contest-interpretation-v1+trusted-empirical-rules-v1"

def pinnedDatasetSha256 : String :=
  "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"

def carbon12Reference : IsotopeMassReference where
  element := .carbon
  massNumber := 12
  massValueDa := "12.000000000000"
  uncertaintyDa := "0"
  datasetVersion := pinnedDatasetVersion
  datasetSha256 := pinnedDatasetSha256
  recordSha256 :=
    "2c212258b787c2459da3b2f29c00882f3d8183c37528ace98a83ece308a2decc"
  sourceURL := "https://amdc.impcas.ac.cn/masstables/Ame2020/mass_1.mas20"

def hydrogen1Reference : IsotopeMassReference where
  element := .hydrogen
  massNumber := 1
  massValueDa := "1.007825031898"
  uncertaintyDa := "0.000000000014"
  datasetVersion := pinnedDatasetVersion
  datasetSha256 := pinnedDatasetSha256
  recordSha256 :=
    "32ec098d6ab9366a09311d83b4923d0f0120b126eeaacb7cfa4bbd0fa1497ff8"
  sourceURL := "https://amdc.impcas.ac.cn/masstables/Ame2020/mass_1.mas20"

def oxygen16Reference : IsotopeMassReference where
  element := .oxygen
  massNumber := 16
  massValueDa := "15.99491461926"
  uncertaintyDa := "0.00000000032"
  datasetVersion := pinnedDatasetVersion
  datasetSha256 := pinnedDatasetSha256
  recordSha256 :=
    "e3c31feaf7f8262947f9ffa8f4047dfd5f5c123ff0c136cab1f0fcca919e9c69"
  sourceURL := "https://amdc.impcas.ac.cn/masstables/Ame2020/mass_1.mas20"

def chlorine35Reference : IsotopeMassReference where
  element := .chlorine
  massNumber := 35
  massValueDa := "34.968852694"
  uncertaintyDa := "0.000000038"
  datasetVersion := pinnedDatasetVersion
  datasetSha256 := pinnedDatasetSha256
  recordSha256 :=
    "5512b5cef1486fbba46b48681bff5bd38a6c8b8e4726027bd83455e7eb1e7020"
  sourceURL := "https://amdc.impcas.ac.cn/masstables/Ame2020/mass_1.mas20"

def chlorine37Reference : IsotopeMassReference where
  element := .chlorine
  massNumber := 37
  massValueDa := "36.965902573"
  uncertaintyDa := "0.000000055"
  datasetVersion := pinnedDatasetVersion
  datasetSha256 := pinnedDatasetSha256
  recordSha256 :=
    "ce6cd511c8d354c00a1c822f36cf83d72524f472f1c87a0ed511ecc3dde299e7"
  sourceURL := "https://amdc.impcas.ac.cn/masstables/Ame2020/mass_1.mas20"

structure NaturalIsotopeAbundanceReference where
  isotope : IsotopeMassReference
  abundance : ℚ
  source : ExternalReference

def nistChlorine35Abundance : NaturalIsotopeAbundanceReference where
  isotope := chlorine35Reference
  abundance := 7576 / 10000
  source := {
    title := "Atomic Weights and Isotopic Compositions for Chlorine"
    stableURL :=
      "https://physics.nist.gov/cgi-bin/Compositions/stand_alone.pl?ele=Cl&ascii=ascii2&isotype=some"
    doi := none
    locator := "preformatted table, mass number 35, Isotopic Composition"
    scopedClaim := "Natural chlorine-35 isotopic composition is 0.7576(10)."
    applicabilityConditions := ["natural terrestrial chlorine"] }

def nistChlorine37Abundance : NaturalIsotopeAbundanceReference where
  isotope := chlorine37Reference
  abundance := 2424 / 10000
  source := {
    title := "Atomic Weights and Isotopic Compositions for Chlorine"
    stableURL :=
      "https://physics.nist.gov/cgi-bin/Compositions/stand_alone.pl?ele=Cl&ascii=ascii2&isotype=some"
    doi := none
    locator := "preformatted table, mass number 37, Isotopic Composition"
    scopedClaim := "Natural chlorine-37 isotopic composition is 0.2424(10)."
    applicabilityConditions := ["natural terrestrial chlorine"] }

/-- A public source is kept together with a content digest of the exact page
used.  The digest is not an authority by itself; it only makes the scoped
literature claim reproducible. -/
structure VerifiedExternalReference where
  reference : ExternalReference
  contentSha256 : String
deriving DecidableEq, Repr

def openStaxMassToChargeReference : VerifiedExternalReference where
  reference := {
    title := "Organic Chemistry, 12.1: Mass Spectrometry of Small Molecules"
    stableURL :=
      "https://raw.githubusercontent.com/openstax/osbooks-organic-chemistry/8917713cdfb7f74018a8fd43cdcfe3173419bb82/modules/m00135/index.cnxml"
    doi := none
    locator := "module m00135, paragraph para-00004"
    scopedClaim :=
      "Ions are sorted by m/z; because their number of charges z is usually one, m/z is then their mass, while the unfragmented cation radical is the molecular ion."
    applicabilityConditions :=
      ["ordinary small-molecule mass spectrum",
       "the observed isotope pair is interpreted as the molecular-ion cluster"] }
  contentSha256 :=
    "f9e2b332b4e0098bd70ee8b3a7dd017eef5f3d622e4c20213b03e68c54dd563f"

def openStaxChlorineIsotopeReference : VerifiedExternalReference where
  reference := {
    title := "Organic Chemistry, 12.3: Mass Spectrometry of Common Functional Groups"
    stableURL :=
      "https://raw.githubusercontent.com/openstax/osbooks-organic-chemistry/8917713cdfb7f74018a8fd43cdcfe3173419bb82/modules/m00137/index.cnxml"
    doi := none
    locator := "module m00137, Halides, paragraph para-00007"
    scopedClaim :=
      "A molecule containing one chlorine atom has molecular-ion peaks two mass units apart for chlorine-35 and chlorine-37, with an approximately 3:1 M to M+2 ratio."
    applicabilityConditions :=
      ["one chlorine atom in the molecular ion", "natural chlorine isotopes"] }
  contentSha256 :=
    "c4f3ee34408b9d35261ee978f8a7cd9e6903bb579211d951255238cbbf2c41a6"

def openStaxAromaticSubstitutionReference : VerifiedExternalReference where
  reference := {
    title := "Organic Chemistry, Chapter 16: Why This Chapter?"
    stableURL :=
      "https://raw.githubusercontent.com/openstax/osbooks-organic-chemistry/8917713cdfb7f74018a8fd43cdcfe3173419bb82/modules/m00188/index.cnxml"
    doi := none
    locator := "module m00188, paragraphs para-00003 and para-00004"
    scopedClaim :=
      "Electrophilic aromatic substitution is characteristic of all aromatic rings: an electrophile substitutes for a ring hydrogen, and a halogen such as chlorine can be introduced this way."
    applicabilityConditions :=
      ["substrate has an aromatic ring", "reaction is aromatic chlorination"] }
  contentSha256 :=
    "d7f875d15cac1c124f4e66dc6feb66e0e8a815be3cf27be9628e0fdd57db0072"

def openStaxAromaticChlorinationReference : VerifiedExternalReference where
  reference := {
    title := "Organic Chemistry, 16.2: Other Aromatic Substitutions"
    stableURL :=
      "https://raw.githubusercontent.com/openstax/osbooks-organic-chemistry/8917713cdfb7f74018a8fd43cdcfe3173419bb82/modules/m00190/index.cnxml"
    doi := none
    locator :=
      "module m00190, Aromatic Halogenation, paragraphs para-00002 and para-00004 plus figure fig-00003 alt text"
    scopedClaim :=
      "Chlorine is introduced into an aromatic ring by electrophilic substitution; the displayed chlorine/FeCl3 example replaces ring H by Cl and forms HCl."
    applicabilityConditions :=
      ["aromatic substrate", "a chlorination outcome is stated",
       "used only for the net one-site atom ledger, not catalyst, yield, or protocol"] }
  contentSha256 :=
    "0ea036095bcd4a81c39a7d6774d6ee6dc1ea1e8a91813fefc206bcb7361570cb"

/-- The problem prints the simplified `3:1` isotope convention.  This
binomial coefficient carrier records all isotopologues uniformly rather than
putting the desired chlorine count in the candidate definition. -/
def chlorineIsotopologueCoefficient (chlorineAtoms heavyCount : ℕ) : ℕ :=
  Nat.choose chlorineAtoms heavyCount * 3 ^ (chlorineAtoms - heavyCount)

def IsThreeToOneTwoPeakPattern (chlorineAtoms : ℕ) : Prop :=
  chlorineAtoms + 1 = 2 ∧
  chlorineIsotopologueCoefficient chlorineAtoms 0 =
    3 * chlorineIsotopologueCoefficient chlorineAtoms 1

/-- Nominal integer mass, appropriate to the integer `m/z` values printed in
the problem.  The pinned isotope records above certify the mass numbers. -/
def nominalMassNumber
    (formula : MolecularFormula) (chlorineMassNumber : ℕ) : ℕ :=
  carbon12Reference.massNumber * formula.carbon +
  hydrogen1Reference.massNumber * formula.hydrogen +
  oxygen16Reference.massNumber * formula.oxygen +
  chlorineMassNumber * formula.chlorine

inductive NominalMassUnit where
  | dalton
deriving DecidableEq, Repr

inductive ChargeMagnitudeUnit where
  | elementaryCharge
deriving DecidableEq, Repr

/-- The printed number is dimensionless only after dividing a nominal mass in
daltons by a charge magnitude in elementary-charge units. -/
structure MzReadout where
  value : ℕ
  numeratorUnit : NominalMassUnit
  denominatorUnit : ChargeMagnitudeUnit
deriving DecidableEq, Repr

structure SpectrumDoubletObservation where
  lowPeak : MzReadout
  highPeak : MzReadout
  lowIntensityWeight : ℕ
  highIntensityWeight : ℕ
  locator : SourceLocator
deriving DecidableEq, Repr

def observedChlorinationDoublet : SpectrumDoubletObservation where
  lowPeak := ⟨218, .dalton, .elementaryCharge⟩
  highPeak := ⟨220, .dalton, .elementaryCharge⟩
  lowIntensityWeight := 3
  highIntensityWeight := 1
  locator := .page3OpeningParagraph

def molecularRadicalCationCharge : ℤ := 1

/-- An explicit `z = 1` certificate connects nominal molecular mass to each
printed `m/z`; no hidden division by an unspecified ion charge remains. -/
structure NominalMzCertificate
    (formula : MolecularFormula) (chlorineMassNumber : ℕ)
    (readout : MzReadout) where
  molecularIonCharge : ℤ
  molecularIonCharge_eq : molecularIonCharge = 1
  chargeMagnitude : ℕ
  chargeMagnitude_eq : chargeMagnitude = 1
  chargeMagnitude_eq_natAbs : chargeMagnitude = molecularIonCharge.natAbs
  molecularIonCharge_eq_ledger :
    molecularIonCharge = molecularRadicalCationCharge
  numeratorUnit_eq : readout.numeratorUnit = .dalton
  denominatorUnit_eq : readout.denominatorUnit = .elementaryCharge
  massToChargeEquation :
    nominalMassNumber formula chlorineMassNumber =
      readout.value * chargeMagnitude
  interpretationAuthority : VerifiedExternalReference
  interpretationAuthority_eq :
    interpretationAuthority = openStaxMassToChargeReference

inductive VisibleColour where
  | blue
deriving DecidableEq, Repr

/-- Source observations are data, not an inverse colour-classification axiom.
The candidate below must independently satisfy the graph, transformation, and
mass-ledger constraints. -/
structure ZSourceObservationData where
  domain : Finset TableCompound
  tableLocator : SourceLocator
  colour : VisibleColour
  colourLocator : SourceLocator
  spectrum : SpectrumDoubletObservation

def zSourceObservationData : ZSourceObservationData where
  domain := tableCandidateDomain
  tableLocator := .page2PlantCompoundTable
  colour := .blue
  colourLocator := .page3OpeningParagraph
  spectrum := observedChlorinationDoublet

theorem twoPeakPattern_has_one_chlorine
    {chlorineAtoms : ℕ}
    (h : IsThreeToOneTwoPeakPattern chlorineAtoms) :
    chlorineAtoms = 1 := by
  rcases h with ⟨hPeaks, _hRatio⟩
  omega

/-! ## Complete structures read from the figure or named references -/

/-- Source-image transcription of compound 7.  Carbon vertices `0` and `1`
are the fused atoms.  Vertices `0`--`9` form the fused 5/7 azulene skeleton;
`10`, `11` are methyl carbons and `12`--`13` are the ethyl carbons. -/
def compoundSevenFromImage : MolecularStructure where
  atomCount := 30
  atoms := hydrocarbonAtoms 14 16
  bonds := [
    mkBond 0 1 .single,
    mkBond 0 2 .double,
    mkBond 0 5 .single,
    mkBond 1 3 .double,
    mkBond 1 6 .single,
    mkBond 2 7 .single,
    mkBond 3 8 .single,
    mkBond 4 5 .double,
    mkBond 4 9 .single,
    mkBond 6 7 .double,
    mkBond 8 9 .double,
    mkBond 2 10 .single,
    mkBond 3 11 .single,
    mkBond 4 12 .single,
    mkBond 12 13 .single,
    mkBond 5 14 .single,
    mkBond 6 15 .single,
    mkBond 7 16 .single,
    mkBond 8 17 .single,
    mkBond 9 18 .single,
    mkBond 10 19 .single,
    mkBond 10 20 .single,
    mkBond 10 21 .single,
    mkBond 11 22 .single,
    mkBond 11 23 .single,
    mkBond 11 24 .single,
    mkBond 12 25 .single,
    mkBond 12 26 .single,
    mkBond 13 27 .single,
    mkBond 13 28 .single,
    mkBond 13 29 .single]

structure DepictedMoleculeRecord where
  provenance : EvidenceProvenance
  locator : SourceLocator
  imagePath : String
  imageSha256 : String
  tableCompound : TableCompound
  molecule : MolecularStructure

def compoundSevenDepiction : DepictedMoleculeRecord where
  provenance := .problemImage
  locator := .page2CompoundSevenPanel
  imagePath := "icho_2026_source/image/T1_page-2.png"
  imageSha256 :=
    "06f9276f8440fd17bd18f6778d1cc5950d47ffebaa60395b7078b96fcbf4f0cb"
  tableCompound := .compound7
  molecule := compoundSevenFromImage

/-- PubChem CID 10719, retained in PubChem atom order rather than the figure's
atom order.  This independence makes the figure-to-name bridge auditable. -/
def chamazuleneReferenceStructure : MolecularStructure where
  atomCount := 30
  atoms := hydrocarbonAtoms 14 16
  bonds := [
    mkBond 0 1 .single,
    mkBond 0 2 .double,
    mkBond 0 5 .single,
    mkBond 1 3 .double,
    mkBond 1 6 .single,
    mkBond 2 7 .single,
    mkBond 2 11 .single,
    mkBond 3 9 .single,
    mkBond 3 12 .single,
    mkBond 4 5 .double,
    mkBond 4 8 .single,
    mkBond 4 10 .single,
    mkBond 6 7 .double,
    mkBond 8 13 .single,
    mkBond 9 10 .double,
    mkBond 5 14 .single,
    mkBond 6 15 .single,
    mkBond 7 16 .single,
    mkBond 8 17 .single,
    mkBond 8 18 .single,
    mkBond 9 19 .single,
    mkBond 10 20 .single,
    mkBond 11 21 .single,
    mkBond 11 22 .single,
    mkBond 11 23 .single,
    mkBond 12 24 .single,
    mkBond 12 25 .single,
    mkBond 12 26 .single,
    mkBond 13 27 .single,
    mkBond 13 28 .single,
    mkBond 13 29 .single]

/-- Azulene: fused five- and seven-membered carbon rings, with every hydrogen
explicit.  The fused carbon atoms are `0` and `1`. -/
def azuleneStructure : MolecularStructure where
  atomCount := 18
  atoms := hydrocarbonAtoms 10 8
  bonds := [
    mkBond 0 1 .single,
    mkBond 0 2 .double,
    mkBond 0 5 .single,
    mkBond 1 3 .double,
    mkBond 1 6 .single,
    mkBond 2 7 .single,
    mkBond 3 8 .single,
    mkBond 4 5 .double,
    mkBond 4 9 .single,
    mkBond 6 7 .double,
    mkBond 8 9 .double,
    mkBond 2 10 .single,
    mkBond 3 11 .single,
    mkBond 4 12 .single,
    mkBond 5 13 .single,
    mkBond 6 14 .single,
    mkBond 7 15 .single,
    mkBond 8 16 .single,
    mkBond 9 17 .single]

/-- Naphthalene: two fused six-membered rings, with every hydrogen explicit. -/
def naphthaleneStructure : MolecularStructure where
  atomCount := 18
  atoms := hydrocarbonAtoms 10 8
  bonds := [
    mkBond 0 1 .single,
    mkBond 0 2 .double,
    mkBond 2 3 .single,
    mkBond 3 4 .double,
    mkBond 4 5 .single,
    mkBond 5 1 .double,
    mkBond 0 6 .single,
    mkBond 6 7 .double,
    mkBond 7 8 .single,
    mkBond 8 9 .double,
    mkBond 9 1 .single,
    mkBond 2 10 .single,
    mkBond 3 11 .single,
    mkBond 4 12 .single,
    mkBond 5 13 .single,
    mkBond 6 14 .single,
    mkBond 7 15 .single,
    mkBond 8 16 .single,
    mkBond 9 17 .single]

structure NamedStructureRecord where
  commonName : String
  iupacName : String
  connectivitySmiles : String
  cid : ℕ
  formula : MolecularFormula
  molecule : MolecularStructure
  source : ExternalReference

def chamazuleneRecord : NamedStructureRecord where
  commonName := "Chamazulene"
  iupacName := "7-ethyl-1,4-dimethylazulene"
  connectivitySmiles := "CCC1=CC2=C(C=CC2=C(C=C1)C)C"
  cid := 10719
  formula := ⟨14, 16, 0, 0⟩
  molecule := chamazuleneReferenceStructure
  source := {
    title := "PubChem Compound Summary: Chamazulene"
    stableURL :=
      "https://pubchem.ncbi.nlm.nih.gov/rest/pug/compound/name/chamazulene/property/MolecularFormula,CanonicalSMILES,IUPACName,Title/JSON"
    doi := none
    locator := "PropertyTable.Properties[0], CID 10719"
    scopedClaim :=
      "Name, formula C14H16, IUPAC name, and connectivity SMILES for chamazulene."
    applicabilityConditions := ["identity and connectivity record only"] }

def azuleneRecord : NamedStructureRecord where
  commonName := "Azulene"
  iupacName := "azulene"
  connectivitySmiles := "C1=CC=C2C=CC=C2C=C1"
  cid := 9231
  formula := ⟨10, 8, 0, 0⟩
  molecule := azuleneStructure
  source := {
    title := "PubChem Compound Summary: Azulene"
    stableURL :=
      "https://pubchem.ncbi.nlm.nih.gov/rest/pug/compound/name/azulene/property/MolecularFormula,CanonicalSMILES,IUPACName,Title/JSON"
    doi := none
    locator := "PropertyTable.Properties[0], CID 9231"
    scopedClaim := "Name, formula C10H8, and connectivity SMILES for azulene."
    applicabilityConditions := ["identity and connectivity record only"] }

def naphthaleneRecord : NamedStructureRecord where
  commonName := "Naphthalene"
  iupacName := "naphthalene"
  connectivitySmiles := "C1=CC=C2C=CC=CC2=C1"
  cid := 931
  formula := ⟨10, 8, 0, 0⟩
  molecule := naphthaleneStructure
  source := {
    title := "PubChem Compound Summary: Naphthalene"
    stableURL :=
      "https://pubchem.ncbi.nlm.nih.gov/rest/pug/compound/name/naphthalene/property/MolecularFormula,CanonicalSMILES,IUPACName,Title/JSON"
    doi := none
    locator := "PropertyTable.Properties[0], CID 931"
    scopedClaim :=
      "Name, formula C10H8, and connectivity SMILES for naphthalene."
    applicabilityConditions := ["identity and connectivity record only"] }

/-! ## Explicit derivative, symmetry, aromaticity, and transformation carriers -/

structure AlkylSubstitutionCertificate
    (core derivative : MolecularStructure) where
  coreEmbedding : CarbonSkeletonEmbedding core derivative
  methylAttachment : Fin 2 → CarbonSite core
  methylCarbon : Fin 2 → CarbonSite derivative
  ethylAttachment : CarbonSite core
  ethylAlpha : CarbonSite derivative
  ethylBeta : CarbonSite derivative
  attachmentSitesDistinct :
    methylAttachment 0 ≠ methylAttachment 1 ∧
    methylAttachment 0 ≠ ethylAttachment ∧
    methylAttachment 1 ≠ ethylAttachment
  methylBonds : ∀ k : Fin 2,
    derivative.bondOrderAt
      (coreEmbedding.toFun (methylAttachment k)).1 (methylCarbon k).1 = 1
  ethylAttachmentBond :
    derivative.bondOrderAt
      (coreEmbedding.toFun ethylAttachment).1 ethylAlpha.1 = 1
  ethylInternalBond : derivative.bondOrderAt ethylAlpha.1 ethylBeta.1 = 1
  methylHydrogens : ∀ k : Fin 2,
    derivative.hydrogenNeighbourCount (methylCarbon k).1 = 3
  ethylAlphaHydrogens : derivative.hydrogenNeighbourCount ethylAlpha.1 = 2
  ethylBetaHydrogens : derivative.hydrogenNeighbourCount ethylBeta.1 = 3
  substitutedCoreHydrogens :
    (∀ k : Fin 2,
      core.hydrogenNeighbourCount (methylAttachment k).1 = 1 ∧
      derivative.hydrogenNeighbourCount
        (coreEmbedding.toFun (methylAttachment k)).1 = 0) ∧
    core.hydrogenNeighbourCount ethylAttachment.1 = 1 ∧
    derivative.hydrogenNeighbourCount
      (coreEmbedding.toFun ethylAttachment).1 = 0
  allDerivativeCarbonsAccounted : ∀ j : CarbonSite derivative,
    (∃ i : CarbonSite core, coreEmbedding.toFun i = j) ∨
    j = methylCarbon 0 ∨ j = methylCarbon 1 ∨
    j = ethylAlpha ∨ j = ethylBeta
  carbonLedger :
    derivative.formula.carbon = core.formula.carbon + 2 + 2
  hydrogenLedger :
    derivative.formula.hydrogen = core.formula.hydrogen - 3 + 6 + 5

def HasTwoMethylAndOneEthylSubstitution
    (core derivative : MolecularStructure) : Prop :=
  Nonempty (AlkylSubstitutionCertificate core derivative)

abbrev Vec3 := Fin 3 → ℝ

def dot3 (u v : Vec3) : ℝ := ∑ k : Fin 3, u k * v k

structure PlaneThroughOrigin where
  normal : Vec3
  normalNonzero : ∃ k : Fin 3, normal k ≠ 0

noncomputable def PlaneThroughOrigin.reflect
    (plane : PlaneThroughOrigin) (x : Vec3) : Vec3 :=
  fun k => x k -
    (2 * dot3 x plane.normal / dot3 plane.normal plane.normal) * plane.normal k

def PerpendicularPlanes (first second : PlaneThroughOrigin) : Prop :=
  dot3 first.normal second.normal = 0

structure SpatialRealization (m : MolecularStructure) where
  position : Fin m.atomCount → Vec3
  injective : Function.Injective position
  noncollinear : ∃ i j k : Fin m.atomCount,
    i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    ¬ ∃ scale : ℝ, ∀ d : Fin 3,
      position k d - position i d =
        scale * (position j d - position i d)

structure ReflectionSymmetryCertificate
    (m : MolecularStructure) (realization : SpatialRealization m)
    (plane : PlaneThroughOrigin) where
  atomPermutation : Equiv.Perm (Fin m.atomCount)
  preservesAtoms : ∀ i : Fin m.atomCount,
    m.atoms i = m.atoms (atomPermutation i)
  /-- A molecular mirror operation preserves nuclear connectivity.  It need
  not preserve one arbitrary localized Kekulé colouring of an aromatic
  resonance hybrid. -/
  preservesAdjacency : ∀ i j : Fin m.atomCount,
    m.bonded i j ↔ m.bonded (atomPermutation i) (atomPermutation j)
  realizesReflection : ∀ i : Fin m.atomCount,
    plane.reflect (realization.position i) =
      realization.position (atomPermutation i)

def HasTwoPerpendicularMirrorPlanes (m : MolecularStructure) : Prop :=
  ∃ realization : SpatialRealization m,
    ∃ first second : PlaneThroughOrigin,
      PerpendicularPlanes first second ∧
      Nonempty (ReflectionSymmetryCertificate m realization first) ∧
      Nonempty (ReflectionSymmetryCertificate m realization second)

def HasThreeMutuallyPerpendicularMirrorPlanes
    (m : MolecularStructure) : Prop :=
  ∃ realization : SpatialRealization m,
    ∃ first second third : PlaneThroughOrigin,
      PerpendicularPlanes first second ∧
      PerpendicularPlanes first third ∧
      PerpendicularPlanes second third ∧
      Nonempty (ReflectionSymmetryCertificate m realization first) ∧
      Nonempty (ReflectionSymmetryCertificate m realization second) ∧
      Nonempty (ReflectionSymmetryCertificate m realization third)

structure HuckelAromaticityCertificate (m : MolecularStructure) where
  piAtoms : Finset (Fin m.atomCount)
  piAtomsExactlyCarbons : ∀ i : Fin m.atomCount,
    i ∈ piAtoms ↔ (m.atoms i).element = .carbon
  allPiAtomsCarbon : ∀ i ∈ piAtoms, (m.atoms i).element = .carbon
  eachPiAtomConjugated : ∀ i ∈ piAtoms,
    ∃ j ∈ piAtoms, m.bondOrderAt i j = 2
  piSystemConnected : ∀ i ∈ piAtoms, ∀ j ∈ piAtoms,
    Relation.ReflTransGen
      (fun a b : Fin m.atomCount =>
        a ∈ piAtoms ∧ b ∈ piAtoms ∧ m.bondOrderAt a b > 0) i j
  piElectronCount : ℕ
  piElectronCount_eq : piElectronCount = piAtoms.card
  huckelIndex : ℕ
  huckelRule : piElectronCount = 4 * huckelIndex + 2

def IsAromatic (m : MolecularStructure) : Prop :=
  Nonempty (HuckelAromaticityCertificate m)

/-! ## Outcome-decisive chlorination and ionization ledgers -/

def chlorineMoleculeFormula : MolecularFormula := ⟨0, 0, 0, 2⟩

def hydrogenChlorideFormula : MolecularFormula := ⟨0, 1, 0, 1⟩

inductive ReactionSide where
  | reactant
  | product
deriving DecidableEq, Repr

/-- This is the complete species domain used for the one-site aromatic
chlorination ledger.  There is deliberately no `other` or residual species. -/
inductive MonochlorinationSpecies where
  | aromaticSubstrate
  | molecularChlorine
  | monochlorinatedProduct
  | hydrogenChloride
deriving DecidableEq, Fintype, Repr

def monochlorinationSpeciesDomain : Finset MonochlorinationSpecies :=
  Finset.univ

def monochlorinationFormula
    (substrate : MolecularStructure) (productFormula : MolecularFormula) :
    MonochlorinationSpecies → MolecularFormula
  | .aromaticSubstrate => substrate.formula
  | .molecularChlorine => chlorineMoleculeFormula
  | .monochlorinatedProduct => productFormula
  | .hydrogenChloride => hydrogenChlorideFormula

def monochlorinationCoefficient (substitutionCount : ℕ) :
    ReactionSide → MonochlorinationSpecies → ℕ
  | .reactant, .aromaticSubstrate => 1
  | .reactant, .molecularChlorine => substitutionCount
  | .product, .monochlorinatedProduct => 1
  | .product, .hydrogenChloride => substitutionCount
  | _, _ => 0

def monochlorinationAtomTotal
    (side : ReactionSide) (substrate : MolecularStructure)
    (productFormula : MolecularFormula) (substitutionCount : ℕ)
    (element : Element) : ℕ :=
  ∑ species : MonochlorinationSpecies,
    monochlorinationCoefficient substitutionCount side species *
      (monochlorinationFormula substrate productFormula species).atomCount element

/-- All four molecular species in the chlorination equation are neutral. -/
def monochlorinationCharge (_ : MonochlorinationSpecies) : ℤ := 0

def monochlorinationChargeTotal
    (side : ReactionSide) (substitutionCount : ℕ) : ℤ :=
  ∑ species : MonochlorinationSpecies,
    (monochlorinationCoefficient substitutionCount side species : ℤ) *
      monochlorinationCharge species

structure MonochlorinationLedger
    (substrate : MolecularStructure) (productFormula : MolecularFormula)
    (substitutionCount : ℕ) where
  speciesDomain : Finset MonochlorinationSpecies
  speciesDomain_eq : speciesDomain = monochlorinationSpeciesDomain
  allSpeciesAccounted : ∀ species, species ∈ speciesDomain
  atomBalanced : ∀ element : Element,
    monochlorinationAtomTotal .reactant substrate productFormula
        substitutionCount element =
      monochlorinationAtomTotal .product substrate productFormula
        substitutionCount element
  chargeBalanced :
    monochlorinationChargeTotal .reactant substitutionCount =
      monochlorinationChargeTotal .product substitutionCount

/-- The source's chlorination is used quantitatively only through the atom and
charge ledger needed to interpret the molecular-ion masses.  The record claims
no catalyst, phase, yield, completeness, or absence of other experimental
products.  `productFormula` is not preset to the eventual candidate formula. -/
structure QuantitativeAromaticMonochlorinationStage
    (core substrate : MolecularStructure) (productFormula : MolecularFormula) where
  classification : StagedTransformationUse
  classification_eq : classification = .quantitativeMaterialStage
  problemLocator : SourceLocator
  problemLocator_eq : problemLocator = .page3OpeningParagraph
  aromaticCore : IsAromatic core
  substrateIsDerivative : HasTwoMethylAndOneEthylSubstitution core substrate
  substrateHasReplaceableHydrogen : 0 < substrate.formula.hydrogen
  substitutionCount : ℕ
  substitutionCountPositive : 0 < substitutionCount
  generalSubstitutionAuthority : VerifiedExternalReference
  generalSubstitutionAuthority_eq :
    generalSubstitutionAuthority = openStaxAromaticSubstitutionReference
  chlorineLedgerAuthority : VerifiedExternalReference
  chlorineLedgerAuthority_eq :
    chlorineLedgerAuthority = openStaxAromaticChlorinationReference
  ledger : MonochlorinationLedger substrate productFormula substitutionCount

/-- Electron ionization is a second, separately balanced material stage:
neutral molecule → molecular radical cation + electron. -/
inductive IonizationSpecies where
  | neutralMolecule
  | molecularRadicalCation
  | electron
deriving DecidableEq, Fintype, Repr

def ionizationSpeciesDomain : Finset IonizationSpecies := Finset.univ

def ionizationFormula
    (neutralFormula : MolecularFormula) : IonizationSpecies → MolecularFormula
  | .neutralMolecule => neutralFormula
  | .molecularRadicalCation => neutralFormula
  | .electron => zeroFormula

def ionizationCharge : IonizationSpecies → ℤ
  | .neutralMolecule => 0
  | .molecularRadicalCation => molecularRadicalCationCharge
  | .electron => -1

def ionizationCoefficient : ReactionSide → IonizationSpecies → ℕ
  | .reactant, .neutralMolecule => 1
  | .product, .molecularRadicalCation => 1
  | .product, .electron => 1
  | _, _ => 0

def ionizationAtomTotal
    (side : ReactionSide) (neutralFormula : MolecularFormula)
    (element : Element) : ℕ :=
  ∑ species : IonizationSpecies,
    ionizationCoefficient side species *
      (ionizationFormula neutralFormula species).atomCount element

def ionizationChargeTotal (side : ReactionSide) : ℤ :=
  ∑ species : IonizationSpecies,
    (ionizationCoefficient side species : ℤ) * ionizationCharge species

structure ElectronIonizationLedger (neutralFormula : MolecularFormula) where
  classification : StagedTransformationUse
  classification_eq : classification = .quantitativeMaterialStage
  speciesDomain : Finset IonizationSpecies
  speciesDomain_eq : speciesDomain = ionizationSpeciesDomain
  allSpeciesAccounted : ∀ species, species ∈ speciesDomain
  atomBalanced : ∀ element : Element,
    ionizationAtomTotal .reactant neutralFormula element =
      ionizationAtomTotal .product neutralFormula element
  chargeBalanced :
    ionizationChargeTotal .reactant = ionizationChargeTotal .product
  molecularIonRadicalElectrons : ℕ
  molecularIonRadicalElectrons_eq : molecularIonRadicalElectrons = 1
  interpretationAuthority : VerifiedExternalReference
  interpretationAuthority_eq :
    interpretationAuthority = openStaxMassToChargeReference

/-- Complete compatibility certificate for the two printed peaks. -/
structure ObservedChlorineDoubletCertificate
    (productFormula : MolecularFormula) where
  observation : SpectrumDoubletObservation
  observation_eq : observation = observedChlorinationDoublet
  isotopePattern : IsThreeToOneTwoPeakPattern productFormula.chlorine
  peakSpacing : observation.highPeak.value = observation.lowPeak.value + 2
  printedIntensityRatio :
    observation.lowIntensityWeight = 3 * observation.highIntensityWeight
  lowIsotopologueWeight :
    chlorineIsotopologueCoefficient productFormula.chlorine 0 =
      observation.lowIntensityWeight
  highIsotopologueWeight :
    chlorineIsotopologueCoefficient productFormula.chlorine 1 =
      observation.highIntensityWeight
  isotopeAuthority : VerifiedExternalReference
  isotopeAuthority_eq : isotopeAuthority = openStaxChlorineIsotopeReference
  ionizationLedger : ElectronIonizationLedger productFormula
  lowPeak : NominalMzCertificate
    productFormula chlorine35Reference.massNumber observation.lowPeak
  highPeak : NominalMzCertificate
    productFormula chlorine37Reference.massNumber observation.highPeak

/-- The spectrum first forces one chlorine and hence one substitution event;
the atom ledger then forces the product formula.  No count is preset in a
product-formula definition. -/
theorem compoundSeven_chlorination_ledger_forces_formula
    {productFormula : MolecularFormula}
    (stage : QuantitativeAromaticMonochlorinationStage
      azuleneStructure compoundSevenFromImage productFormula)
    (_spectrum : ObservedChlorineDoubletCertificate productFormula) :
    stage.substitutionCount = 1 ∧ productFormula = ⟨14, 15, 0, 1⟩ := by
  have hProductChlorine : productFormula.chlorine = 1 :=
    twoPeakPattern_has_one_chlorine _spectrum.isotopePattern
  have hC := stage.ledger.atomBalanced Element.carbon
  have hH := stage.ledger.atomBalanced Element.hydrogen
  have hO := stage.ledger.atomBalanced Element.oxygen
  have hCl := stage.ledger.atomBalanced Element.chlorine
  have hSubstrateFormula :
      compoundSevenFromImage.formula = ⟨14, 16, 0, 0⟩ := by
    decide
  have hSpecies : (Finset.univ : Finset MonochlorinationSpecies) =
      {.aromaticSubstrate, .molecularChlorine,
        .monochlorinatedProduct, .hydrogenChloride} := by
    decide
  simp [monochlorinationAtomTotal, hSpecies,
    monochlorinationCoefficient, monochlorinationFormula,
    hSubstrateFormula, chlorineMoleculeFormula, hydrogenChlorideFormula,
    MolecularFormula.atomCount] at hC hH hO hCl
  have hSubstitution : stage.substitutionCount = 1 := by omega
  constructor
  · exact hSubstitution
  · cases productFormula
    simp_all

def CompoundSevenChlorinationSpec : Prop :=
  ∃ productFormula : MolecularFormula,
    ∃ stage : QuantitativeAromaticMonochlorinationStage
      azuleneStructure compoundSevenFromImage productFormula,
    ∃ _spectrum : ObservedChlorineDoubletCertificate productFormula,
      stage.substitutionCount = 1 ∧
      productFormula = ⟨14, 15, 0, 1⟩

/-- This record intentionally makes no statement about yield, completeness,
phase, coefficient, byproducts, or an omitted stream. -/
structure QualitativeNamedTransformRecord where
  classification : StagedTransformationUse
  problemLocator : SourceLocator
  reactant : NamedStructureRecord
  product : NamedStructureRecord
  conditionPrintedByProblem : String
  literatureContext : ExternalReference
  yield : Option ℚ
  stoichiometricCoefficient : Option ℚ
  phase : Option String
  byproducts : Option (List MolecularFormula)

def azuleneToNaphthaleneTransform : QualitativeNamedTransformRecord where
  classification := .qualitativeNamedTransformOnly
  problemLocator := .page3OpeningParagraph
  reactant := azuleneRecord
  product := naphthaleneRecord
  conditionPrintedByProblem := "heated; temperature and protocol unspecified"
  literatureContext := {
    title := "Thermal isomerization of azulene to naphthalene in shock waves"
    stableURL := "https://doi.org/10.1002/kin.550200504"
    doi := some "10.1002/kin.550200504"
    locator := "Abstract, first and second sentences"
    scopedClaim :=
      "Azulene was thermally isomerized in shock waves at 1300-1900 K, with azulene and naphthalene monitored by UV absorption."
    applicabilityConditions :=
      ["azulene substrate", "shock-wave heating", "1300-1900 K"] }
  yield := none
  stoichiometricCoefficient := none
  phase := none
  byproducts := none

def QualitativeTransformCompatibility
    (record : QualitativeNamedTransformRecord) : Prop :=
  record.classification = .qualitativeNamedTransformOnly ∧
  record.problemLocator = .page3OpeningParagraph ∧
  record.reactant.molecule.formula = record.product.molecule.formula ∧
  ¬ Nonempty
    (MolecularIsomorphism record.reactant.molecule record.product.molecule) ∧
  record.yield = none ∧
  record.stoichiometricCoefficient = none ∧
  record.phase = none ∧
  record.byproducts = none

/-! ## Source-to-candidate bridge obligations -/

structure RequestedOutputBundle where
  identityZ : TableCompound
  structureZ : MolecularStructure
  structureA : MolecularStructure
  structureB : MolecularStructure

/-- The candidates are named here; none of their specifications below assumes
that it is the requested answer.  Each field must pass all source-derived
graph, symmetry, transformation, and spectrum checks in `RawResult`. -/
def derivedOutputs : RequestedOutputBundle where
  identityZ := compoundSevenDepiction.tableCompound
  structureZ := compoundSevenDepiction.molecule
  structureA := azuleneRecord.molecule
  structureB := naphthaleneRecord.molecule

/-- Named Lean carrier for requested output `identity_z`. -/
def identityZOutput : TableCompound := derivedOutputs.identityZ

/-- Named full Lewis-graph carrier for requested output `structure_a`. -/
def structureAOutput : MolecularStructure := derivedOutputs.structureA

/-- Named full Lewis-graph carrier for requested output `structure_b`. -/
def structureBOutput : MolecularStructure := derivedOutputs.structureB

def ImageIdentityBridgeSpec : Prop :=
  derivedOutputs.structureZ.formula = tableFormula derivedOutputs.identityZ ∧
  derivedOutputs.structureZ.wellFormedLewis ∧
  derivedOutputs.structureZ.noSpecifiedStereochemistry ∧
  chamazuleneReferenceStructure.formula = chamazuleneRecord.formula ∧
  chamazuleneReferenceStructure.wellFormedLewis ∧
  chamazuleneReferenceStructure.noSpecifiedStereochemistry ∧
  Nonempty
    (MolecularIsomorphism
      derivedOutputs.structureZ chamazuleneReferenceStructure)

def IdentityZRawSpec : Prop :=
  identityZOutput = .compound7 ∧
  identityZOutput ∈ zSourceObservationData.domain ∧
  zSourceObservationData.tableLocator = .page2PlantCompoundTable ∧
  zSourceObservationData.colour = .blue ∧
  zSourceObservationData.colourLocator = .page3OpeningParagraph ∧
  ImageIdentityBridgeSpec ∧
  CompoundSevenChlorinationSpec

def StructureOfASpec : Prop :=
  structureAOutput.formula = ⟨10, 8, 0, 0⟩ ∧
  structureAOutput.wellFormedLewis ∧
  structureAOutput.noSpecifiedStereochemistry ∧
  IsAromatic structureAOutput ∧
  HasTwoMethylAndOneEthylSubstitution
    structureAOutput derivedOutputs.structureZ ∧
  HasTwoPerpendicularMirrorPlanes structureAOutput

def StructureOfBSpec : Prop :=
  structureBOutput.formula = ⟨10, 8, 0, 0⟩ ∧
  structureBOutput.wellFormedLewis ∧
  structureBOutput.noSpecifiedStereochemistry ∧
  IsAromatic structureBOutput ∧
  HasThreeMutuallyPerpendicularMirrorPlanes structureBOutput ∧
  azuleneToNaphthaleneTransform.reactant.molecule = structureAOutput ∧
  azuleneToNaphthaleneTransform.product.molecule = structureBOutput ∧
  QualitativeTransformCompatibility azuleneToNaphthaleneTransform

/-- One conjunction covers all three requested outputs in source order:
identity of `Z`, structure of `A`, and structure of `B`. -/
def RawResult : Prop :=
  IdentityZRawSpec ∧ StructureOfASpec ∧ StructureOfBSpec

/-- Exact-symbolic reporting adds the three externally auditable names and
SMILES encodings while retaining the full graph-level raw result. -/
def ReportedResult : Prop :=
  RawResult ∧
  chamazuleneRecord.commonName = "Chamazulene" ∧
  chamazuleneRecord.iupacName = "7-ethyl-1,4-dimethylazulene" ∧
  chamazuleneRecord.connectivitySmiles =
    "CCC1=CC2=C(C=CC2=C(C=C1)C)C" ∧
  azuleneRecord.commonName = "Azulene" ∧
  azuleneRecord.connectivitySmiles = "C1=CC=C2C=CC=C2C=C1" ∧
  naphthaleneRecord.commonName = "Naphthalene" ∧
  naphthaleneRecord.connectivitySmiles = "C1=CC=C2C=CC=CC2=C1"

/-! ## Finite graph witnesses used by the result proof -/

private theorem reflTransGen_reverse
    {α : Type} {r : α → α → Prop}
    (hsymm : ∀ {i j}, r i j → r j i) {i j : α}
    (h : Relation.ReflTransGen r i j) : Relation.ReflTransGen r j i := by
  induction h with
  | refl => exact .refl
  | tail hab hbc ih =>
      exact (Relation.ReflTransGen.single (hsymm hbc)).trans ih

private theorem connected_of_root
    {α : Type} {r : α → α → Prop} (root : α)
    (hsymm : ∀ {i j}, r i j → r j i)
    (hroot : ∀ i, Relation.ReflTransGen r root i) :
    ∀ i j, Relation.ReflTransGen r i j := by
  intro i j
  exact (reflTransGen_reverse hsymm (hroot i)).trans (hroot j)

private theorem bond_connects_comm {n : ℕ} (b : Bond n) (i j : Fin n) :
    b.connects i j = b.connects j i := by
  simp [Bond.connects, Bool.or_comm]

private theorem bondOrderAt_comm (m : MolecularStructure)
    (i j : Fin m.atomCount) : m.bondOrderAt i j = m.bondOrderAt j i := by
  unfold MolecularStructure.bondOrderAt
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _hb
  rw [bond_connects_comm]

private theorem bonded_comm (m : MolecularStructure)
    (i j : Fin m.atomCount) : m.bonded i j ↔ m.bonded j i := by
  unfold MolecularStructure.bonded
  rw [bondOrderAt_comm]

private instance molecularStructureBondedDecidable
    (m : MolecularStructure) (i j : Fin m.atomCount) :
    Decidable (m.bonded i j) := by
  unfold MolecularStructure.bonded
  infer_instance

private theorem bonded_of_mem_bond
    {m : MolecularStructure} {i j : Fin m.atomCount}
    (b : Bond m.atomCount) (hb : b ∈ m.bonds)
    (hconnects : b.connects i j = true) : m.bonded i j := by
  unfold MolecularStructure.bonded MolecularStructure.bondOrderAt
  have hmem : b.order.valence ∈
      m.bonds.map (fun c => if c.connects i j then c.order.valence else 0) := by
    apply List.mem_map.mpr
    exact ⟨b, hb, by simp [hconnects]⟩
  have hle := List.le_sum_of_mem hmem
  have hpos : 0 < b.order.valence := by cases b.order <;> decide
  exact hpos.trans_le hle

private instance compoundSevenAtomCountNeZero :
    NeZero compoundSevenFromImage.atomCount := ⟨by decide⟩

private instance chamazuleneReferenceAtomCountNeZero :
    NeZero chamazuleneReferenceStructure.atomCount := ⟨by decide⟩

private instance azuleneAtomCountNeZero :
    NeZero azuleneStructure.atomCount := ⟨by decide⟩

private instance naphthaleneAtomCountNeZero :
    NeZero naphthaleneStructure.atomCount := ⟨by decide⟩

private def compoundSevenParent :
    Fin compoundSevenFromImage.atomCount → Fin compoundSevenFromImage.atomCount := ![
  0, 0, 0, 1, 5, 0, 1, 2, 3, 4, 2, 3, 4, 12, 5,
  6, 7, 8, 9, 10, 10, 10, 11, 11, 11, 12, 12, 13, 13, 13]

private def compoundSevenSpanningBond :
    Fin compoundSevenFromImage.atomCount → Bond compoundSevenFromImage.atomCount := ![
  mkBond 0 1 .single, mkBond 0 1 .single, mkBond 0 2 .double,
  mkBond 1 3 .double, mkBond 4 5 .double, mkBond 0 5 .single,
  mkBond 1 6 .single, mkBond 2 7 .single, mkBond 3 8 .single,
  mkBond 4 9 .single, mkBond 2 10 .single, mkBond 3 11 .single,
  mkBond 4 12 .single, mkBond 12 13 .single, mkBond 5 14 .single,
  mkBond 6 15 .single, mkBond 7 16 .single, mkBond 8 17 .single,
  mkBond 9 18 .single, mkBond 10 19 .single, mkBond 10 20 .single,
  mkBond 10 21 .single, mkBond 11 22 .single, mkBond 11 23 .single,
  mkBond 11 24 .single, mkBond 12 25 .single, mkBond 12 26 .single,
  mkBond 13 27 .single, mkBond 13 28 .single, mkBond 13 29 .single]

private theorem compoundSeven_spanningBond_data :
    ∀ i : Fin compoundSevenFromImage.atomCount, i ≠ 0 →
      compoundSevenSpanningBond i ∈ compoundSevenFromImage.bonds ∧
      (compoundSevenSpanningBond i).connects (compoundSevenParent i) i = true := by
  decide

private theorem compoundSeven_parent_bonded :
    ∀ i : Fin compoundSevenFromImage.atomCount, i ≠ 0 →
      compoundSevenFromImage.bonded (compoundSevenParent i) i := by
  intro i hi
  exact bonded_of_mem_bond (compoundSevenSpanningBond i)
    (compoundSeven_spanningBond_data i hi).1
    (compoundSeven_spanningBond_data i hi).2

private def chamazuleneReferenceParent :
    Fin chamazuleneReferenceStructure.atomCount →
      Fin chamazuleneReferenceStructure.atomCount := ![
  0, 0, 0, 1, 5, 0, 1, 2, 4, 3, 4, 2, 3, 8, 5,
  6, 7, 8, 8, 9, 10, 11, 11, 11, 12, 12, 12, 13, 13, 13]

private def chamazuleneReferenceSpanningBond :
    Fin chamazuleneReferenceStructure.atomCount →
      Bond chamazuleneReferenceStructure.atomCount := ![
  mkBond 0 1 .single, mkBond 0 1 .single, mkBond 0 2 .double,
  mkBond 1 3 .double, mkBond 4 5 .double, mkBond 0 5 .single,
  mkBond 1 6 .single, mkBond 2 7 .single, mkBond 4 8 .single,
  mkBond 3 9 .single, mkBond 4 10 .single, mkBond 2 11 .single,
  mkBond 3 12 .single, mkBond 8 13 .single, mkBond 5 14 .single,
  mkBond 6 15 .single, mkBond 7 16 .single, mkBond 8 17 .single,
  mkBond 8 18 .single, mkBond 9 19 .single, mkBond 10 20 .single,
  mkBond 11 21 .single, mkBond 11 22 .single, mkBond 11 23 .single,
  mkBond 12 24 .single, mkBond 12 25 .single, mkBond 12 26 .single,
  mkBond 13 27 .single, mkBond 13 28 .single, mkBond 13 29 .single]

private theorem chamazuleneReference_spanningBond_data :
    ∀ i : Fin chamazuleneReferenceStructure.atomCount, i ≠ 0 →
      chamazuleneReferenceSpanningBond i ∈ chamazuleneReferenceStructure.bonds ∧
      (chamazuleneReferenceSpanningBond i).connects
        (chamazuleneReferenceParent i) i = true := by
  decide

private theorem chamazuleneReference_parent_bonded :
    ∀ i : Fin chamazuleneReferenceStructure.atomCount, i ≠ 0 →
      chamazuleneReferenceStructure.bonded
        (chamazuleneReferenceParent i) i := by
  intro i hi
  exact bonded_of_mem_bond (chamazuleneReferenceSpanningBond i)
    (chamazuleneReference_spanningBond_data i hi).1
    (chamazuleneReference_spanningBond_data i hi).2

private def azuleneParent :
    Fin azuleneStructure.atomCount → Fin azuleneStructure.atomCount := ![
  0, 0, 0, 1, 5, 0, 1, 2, 3, 4, 2, 3, 4, 5, 6, 7, 8, 9]

private def azuleneSpanningBond :
    Fin azuleneStructure.atomCount → Bond azuleneStructure.atomCount := ![
  mkBond 0 1 .single, mkBond 0 1 .single, mkBond 0 2 .double,
  mkBond 1 3 .double, mkBond 4 5 .double, mkBond 0 5 .single,
  mkBond 1 6 .single, mkBond 2 7 .single, mkBond 3 8 .single,
  mkBond 4 9 .single, mkBond 2 10 .single, mkBond 3 11 .single,
  mkBond 4 12 .single, mkBond 5 13 .single, mkBond 6 14 .single,
  mkBond 7 15 .single, mkBond 8 16 .single, mkBond 9 17 .single]

private theorem azulene_spanningBond_data :
    ∀ i : Fin azuleneStructure.atomCount, i ≠ 0 →
      azuleneSpanningBond i ∈ azuleneStructure.bonds ∧
      (azuleneSpanningBond i).connects (azuleneParent i) i = true := by
  decide

private theorem azulene_parent_bonded :
    ∀ i : Fin azuleneStructure.atomCount, i ≠ 0 →
      azuleneStructure.bonded (azuleneParent i) i := by
  intro i hi
  exact bonded_of_mem_bond (azuleneSpanningBond i)
    (azulene_spanningBond_data i hi).1
    (azulene_spanningBond_data i hi).2

private def naphthaleneParent :
    Fin naphthaleneStructure.atomCount → Fin naphthaleneStructure.atomCount := ![
  0, 0, 0, 2, 3, 1, 0, 6, 7, 1, 2, 3, 4, 5, 6, 7, 8, 9]

private def naphthaleneSpanningBond :
    Fin naphthaleneStructure.atomCount → Bond naphthaleneStructure.atomCount := ![
  mkBond 0 1 .single, mkBond 0 1 .single, mkBond 0 2 .double,
  mkBond 2 3 .single, mkBond 3 4 .double, mkBond 5 1 .double,
  mkBond 0 6 .single, mkBond 6 7 .double, mkBond 7 8 .single,
  mkBond 9 1 .single, mkBond 2 10 .single, mkBond 3 11 .single,
  mkBond 4 12 .single, mkBond 5 13 .single, mkBond 6 14 .single,
  mkBond 7 15 .single, mkBond 8 16 .single, mkBond 9 17 .single]

private theorem naphthalene_spanningBond_data :
    ∀ i : Fin naphthaleneStructure.atomCount, i ≠ 0 →
      naphthaleneSpanningBond i ∈ naphthaleneStructure.bonds ∧
      (naphthaleneSpanningBond i).connects (naphthaleneParent i) i = true := by
  decide

private theorem naphthalene_parent_bonded :
    ∀ i : Fin naphthaleneStructure.atomCount, i ≠ 0 →
      naphthaleneStructure.bonded (naphthaleneParent i) i := by
  intro i hi
  exact bonded_of_mem_bond (naphthaleneSpanningBond i)
    (naphthalene_spanningBond_data i hi).1
    (naphthalene_spanningBond_data i hi).2

private theorem compoundSeven_rooted
    (i : Fin compoundSevenFromImage.atomCount) :
    Relation.ReflTransGen compoundSevenFromImage.bonded 0 i := by
  have p0 : Relation.ReflTransGen compoundSevenFromImage.bonded 0 0 := .refl
  have p1 := p0.tail (compoundSeven_parent_bonded 1 (by decide))
  have p2 := p0.tail (compoundSeven_parent_bonded 2 (by decide))
  have p5 := p0.tail (compoundSeven_parent_bonded 5 (by decide))
  have p3 := p1.tail (compoundSeven_parent_bonded 3 (by decide))
  have p6 := p1.tail (compoundSeven_parent_bonded 6 (by decide))
  have p7 := p2.tail (compoundSeven_parent_bonded 7 (by decide))
  have p8 := p3.tail (compoundSeven_parent_bonded 8 (by decide))
  have p4 := p5.tail (compoundSeven_parent_bonded 4 (by decide))
  have p9 := p4.tail (compoundSeven_parent_bonded 9 (by decide))
  have p10 := p2.tail (compoundSeven_parent_bonded 10 (by decide))
  have p11 := p3.tail (compoundSeven_parent_bonded 11 (by decide))
  have p12 := p4.tail (compoundSeven_parent_bonded 12 (by decide))
  have p13 := p12.tail (compoundSeven_parent_bonded 13 (by decide))
  have p14 := p5.tail (compoundSeven_parent_bonded 14 (by decide))
  have p15 := p6.tail (compoundSeven_parent_bonded 15 (by decide))
  have p16 := p7.tail (compoundSeven_parent_bonded 16 (by decide))
  have p17 := p8.tail (compoundSeven_parent_bonded 17 (by decide))
  have p18 := p9.tail (compoundSeven_parent_bonded 18 (by decide))
  have p19 := p10.tail (compoundSeven_parent_bonded 19 (by decide))
  have p20 := p10.tail (compoundSeven_parent_bonded 20 (by decide))
  have p21 := p10.tail (compoundSeven_parent_bonded 21 (by decide))
  have p22 := p11.tail (compoundSeven_parent_bonded 22 (by decide))
  have p23 := p11.tail (compoundSeven_parent_bonded 23 (by decide))
  have p24 := p11.tail (compoundSeven_parent_bonded 24 (by decide))
  have p25 := p12.tail (compoundSeven_parent_bonded 25 (by decide))
  have p26 := p12.tail (compoundSeven_parent_bonded 26 (by decide))
  have p27 := p13.tail (compoundSeven_parent_bonded 27 (by decide))
  have p28 := p13.tail (compoundSeven_parent_bonded 28 (by decide))
  have p29 := p13.tail (compoundSeven_parent_bonded 29 (by decide))
  fin_cases i <;> assumption

private theorem chamazuleneReference_rooted
    (i : Fin chamazuleneReferenceStructure.atomCount) :
    Relation.ReflTransGen chamazuleneReferenceStructure.bonded 0 i := by
  have p0 : Relation.ReflTransGen chamazuleneReferenceStructure.bonded 0 0 := .refl
  have p1 := p0.tail (chamazuleneReference_parent_bonded 1 (by decide))
  have p2 := p0.tail (chamazuleneReference_parent_bonded 2 (by decide))
  have p5 := p0.tail (chamazuleneReference_parent_bonded 5 (by decide))
  have p3 := p1.tail (chamazuleneReference_parent_bonded 3 (by decide))
  have p6 := p1.tail (chamazuleneReference_parent_bonded 6 (by decide))
  have p7 := p2.tail (chamazuleneReference_parent_bonded 7 (by decide))
  have p11 := p2.tail (chamazuleneReference_parent_bonded 11 (by decide))
  have p9 := p3.tail (chamazuleneReference_parent_bonded 9 (by decide))
  have p12 := p3.tail (chamazuleneReference_parent_bonded 12 (by decide))
  have p4 := p5.tail (chamazuleneReference_parent_bonded 4 (by decide))
  have p8 := p4.tail (chamazuleneReference_parent_bonded 8 (by decide))
  have p10 := p4.tail (chamazuleneReference_parent_bonded 10 (by decide))
  have p13 := p8.tail (chamazuleneReference_parent_bonded 13 (by decide))
  have p14 := p5.tail (chamazuleneReference_parent_bonded 14 (by decide))
  have p15 := p6.tail (chamazuleneReference_parent_bonded 15 (by decide))
  have p16 := p7.tail (chamazuleneReference_parent_bonded 16 (by decide))
  have p17 := p8.tail (chamazuleneReference_parent_bonded 17 (by decide))
  have p18 := p8.tail (chamazuleneReference_parent_bonded 18 (by decide))
  have p19 := p9.tail (chamazuleneReference_parent_bonded 19 (by decide))
  have p20 := p10.tail (chamazuleneReference_parent_bonded 20 (by decide))
  have p21 := p11.tail (chamazuleneReference_parent_bonded 21 (by decide))
  have p22 := p11.tail (chamazuleneReference_parent_bonded 22 (by decide))
  have p23 := p11.tail (chamazuleneReference_parent_bonded 23 (by decide))
  have p24 := p12.tail (chamazuleneReference_parent_bonded 24 (by decide))
  have p25 := p12.tail (chamazuleneReference_parent_bonded 25 (by decide))
  have p26 := p12.tail (chamazuleneReference_parent_bonded 26 (by decide))
  have p27 := p13.tail (chamazuleneReference_parent_bonded 27 (by decide))
  have p28 := p13.tail (chamazuleneReference_parent_bonded 28 (by decide))
  have p29 := p13.tail (chamazuleneReference_parent_bonded 29 (by decide))
  fin_cases i <;> assumption

private theorem azulene_rooted (i : Fin azuleneStructure.atomCount) :
    Relation.ReflTransGen azuleneStructure.bonded 0 i := by
  have p0 : Relation.ReflTransGen azuleneStructure.bonded 0 0 := .refl
  have p1 := p0.tail (azulene_parent_bonded 1 (by decide))
  have p2 := p0.tail (azulene_parent_bonded 2 (by decide))
  have p5 := p0.tail (azulene_parent_bonded 5 (by decide))
  have p3 := p1.tail (azulene_parent_bonded 3 (by decide))
  have p6 := p1.tail (azulene_parent_bonded 6 (by decide))
  have p7 := p2.tail (azulene_parent_bonded 7 (by decide))
  have p8 := p3.tail (azulene_parent_bonded 8 (by decide))
  have p4 := p5.tail (azulene_parent_bonded 4 (by decide))
  have p9 := p4.tail (azulene_parent_bonded 9 (by decide))
  have p10 := p2.tail (azulene_parent_bonded 10 (by decide))
  have p11 := p3.tail (azulene_parent_bonded 11 (by decide))
  have p12 := p4.tail (azulene_parent_bonded 12 (by decide))
  have p13 := p5.tail (azulene_parent_bonded 13 (by decide))
  have p14 := p6.tail (azulene_parent_bonded 14 (by decide))
  have p15 := p7.tail (azulene_parent_bonded 15 (by decide))
  have p16 := p8.tail (azulene_parent_bonded 16 (by decide))
  have p17 := p9.tail (azulene_parent_bonded 17 (by decide))
  fin_cases i <;> assumption

private theorem naphthalene_rooted (i : Fin naphthaleneStructure.atomCount) :
    Relation.ReflTransGen naphthaleneStructure.bonded 0 i := by
  have p0 : Relation.ReflTransGen naphthaleneStructure.bonded 0 0 := .refl
  have p1 := p0.tail (naphthalene_parent_bonded 1 (by decide))
  have p2 := p0.tail (naphthalene_parent_bonded 2 (by decide))
  have p6 := p0.tail (naphthalene_parent_bonded 6 (by decide))
  have p5 := p1.tail (naphthalene_parent_bonded 5 (by decide))
  have p9 := p1.tail (naphthalene_parent_bonded 9 (by decide))
  have p3 := p2.tail (naphthalene_parent_bonded 3 (by decide))
  have p7 := p6.tail (naphthalene_parent_bonded 7 (by decide))
  have p4 := p3.tail (naphthalene_parent_bonded 4 (by decide))
  have p8 := p7.tail (naphthalene_parent_bonded 8 (by decide))
  have p10 := p2.tail (naphthalene_parent_bonded 10 (by decide))
  have p11 := p3.tail (naphthalene_parent_bonded 11 (by decide))
  have p12 := p4.tail (naphthalene_parent_bonded 12 (by decide))
  have p13 := p5.tail (naphthalene_parent_bonded 13 (by decide))
  have p14 := p6.tail (naphthalene_parent_bonded 14 (by decide))
  have p15 := p7.tail (naphthalene_parent_bonded 15 (by decide))
  have p16 := p8.tail (naphthalene_parent_bonded 16 (by decide))
  have p17 := p9.tail (naphthalene_parent_bonded 17 (by decide))
  fin_cases i <;> assumption

private theorem compoundSeven_connected : compoundSevenFromImage.connected := by
  apply connected_of_root (r := compoundSevenFromImage.bonded) 0
  · intro i j h
    exact (bonded_comm compoundSevenFromImage i j).mp h
  · exact compoundSeven_rooted

private theorem chamazuleneReference_connected :
    chamazuleneReferenceStructure.connected := by
  apply connected_of_root (r := chamazuleneReferenceStructure.bonded) 0
  · intro i j h
    exact (bonded_comm chamazuleneReferenceStructure i j).mp h
  · exact chamazuleneReference_rooted

private theorem azulene_connected : azuleneStructure.connected := by
  apply connected_of_root (r := azuleneStructure.bonded) 0
  · intro i j h
    exact (bonded_comm azuleneStructure i j).mp h
  · exact azulene_rooted

private theorem naphthalene_connected : naphthaleneStructure.connected := by
  apply connected_of_root (r := naphthaleneStructure.bonded) 0
  · intro i j h
    exact (bonded_comm naphthaleneStructure i j).mp h
  · exact naphthalene_rooted

private theorem compoundSeven_wellFormed :
    compoundSevenFromImage.wellFormedLewis := by
  refine ⟨by decide, by decide, by decide,
    by decide, by decide, ?_⟩
  exact compoundSeven_connected

private theorem chamazuleneReference_wellFormed :
    chamazuleneReferenceStructure.wellFormedLewis := by
  refine ⟨by decide, by decide, by decide,
    by decide, by decide, ?_⟩
  exact chamazuleneReference_connected

private theorem azulene_wellFormed : azuleneStructure.wellFormedLewis := by
  refine ⟨by decide, by decide, by decide,
    by decide, by decide, ?_⟩
  exact azulene_connected

private theorem naphthalene_wellFormed : naphthaleneStructure.wellFormedLewis := by
  refine ⟨by decide, by decide, by decide,
    by decide, by decide, ?_⟩
  exact naphthalene_connected

private theorem compoundSeven_noSpecifiedStereochemistry :
    compoundSevenFromImage.noSpecifiedStereochemistry := by
  unfold MolecularStructure.noSpecifiedStereochemistry
  decide

private theorem chamazuleneReference_noSpecifiedStereochemistry :
    chamazuleneReferenceStructure.noSpecifiedStereochemistry := by
  unfold MolecularStructure.noSpecifiedStereochemistry
  decide

private theorem azulene_noSpecifiedStereochemistry :
    azuleneStructure.noSpecifiedStereochemistry := by
  unfold MolecularStructure.noSpecifiedStereochemistry
  decide

private theorem naphthalene_noSpecifiedStereochemistry :
    naphthaleneStructure.noSpecifiedStereochemistry := by
  unfold MolecularStructure.noSpecifiedStereochemistry
  decide

private def imageToReferenceMap : Fin 30 → Fin 30 := ![
  0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 8, 13, 14,
  15, 16, 19, 20, 21, 22, 23, 24, 25, 26, 17, 18, 27, 28, 29]

private noncomputable def imageToReferenceEquiv : Fin 30 ≃ Fin 30 :=
  Equiv.ofBijective imageToReferenceMap (by decide)

private noncomputable def compoundSevenImageIsomorphism :
    MolecularIsomorphism compoundSevenFromImage chamazuleneReferenceStructure where
  atomEquiv := imageToReferenceEquiv
  preservesAtom := by decide
  preservesAdjacency := by decide

private def azuleneCarbonEmbedding
    (i : CarbonSite azuleneStructure) : CarbonSite compoundSevenFromImage :=
  ⟨⟨i.1.val, by
      have hi := i.1.isLt
      change i.1.val < 18 at hi
      change i.1.val < 30
      omega⟩,
    by
      have hi : i.1.val < 10 := by
        by_contra h
        have hge : ¬ i.1.val < 10 := by omega
        simpa [azuleneStructure, hydrocarbonAtoms, neutralAtom, hge] using i.2
      have hi14 : i.1.val < 14 := by omega
      simp [compoundSevenFromImage, hydrocarbonAtoms, neutralAtom, hi14]⟩

private def azuleneSkeletonEmbedding :
    CarbonSkeletonEmbedding azuleneStructure compoundSevenFromImage where
  toFun := azuleneCarbonEmbedding
  injective := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun x => x.1.val) hij
  preservesAdjacency := by decide

private def compoundSevenAlkylSubstitutionCertificate :
    AlkylSubstitutionCertificate azuleneStructure compoundSevenFromImage where
  coreEmbedding := azuleneSkeletonEmbedding
  methylAttachment := ![⟨2, by decide⟩, ⟨3, by decide⟩]
  methylCarbon := ![⟨10, by decide⟩, ⟨11, by decide⟩]
  ethylAttachment := ⟨4, by decide⟩
  ethylAlpha := ⟨12, by decide⟩
  ethylBeta := ⟨13, by decide⟩
  attachmentSitesDistinct := by decide
  methylBonds := by decide
  ethylAttachmentBond := by decide
  ethylInternalBond := by decide
  methylHydrogens := by decide
  ethylAlphaHydrogens := by decide
  ethylBetaHydrogens := by decide
  substitutedCoreHydrogens := by decide
  allDerivativeCarbonsAccounted := by decide
  carbonLedger := by decide
  hydrogenLedger := by decide

private def azulenePiAtoms : Finset (Fin azuleneStructure.atomCount) :=
  Finset.univ.filter fun i => (azuleneStructure.atoms i).element = .carbon

private def naphthalenePiAtoms : Finset (Fin naphthaleneStructure.atomCount) :=
  Finset.univ.filter fun i => (naphthaleneStructure.atoms i).element = .carbon

private theorem azulene_pi_rooted
    (i : Fin azuleneStructure.atomCount) (hi : i ∈ azulenePiAtoms) :
    Relation.ReflTransGen
      (fun a b : Fin azuleneStructure.atomCount =>
        a ∈ azulenePiAtoms ∧ b ∈ azulenePiAtoms ∧
          azuleneStructure.bondOrderAt a b > 0) 0 i := by
  let r := fun a b : Fin azuleneStructure.atomCount =>
    a ∈ azulenePiAtoms ∧ b ∈ azulenePiAtoms ∧
      azuleneStructure.bondOrderAt a b > 0
  change Relation.ReflTransGen r 0 i
  have p0 : Relation.ReflTransGen r 0 0 := .refl
  have p1 := p0.tail (by decide : r 0 1)
  have p2 := p0.tail (by decide : r 0 2)
  have p5 := p0.tail (by decide : r 0 5)
  have p3 := p1.tail (by decide : r 1 3)
  have p6 := p1.tail (by decide : r 1 6)
  have p7 := p2.tail (by decide : r 2 7)
  have p8 := p3.tail (by decide : r 3 8)
  have p4 := p5.tail (by decide : r 5 4)
  have p9 := p4.tail (by decide : r 4 9)
  have hc : (azuleneStructure.atoms i).element = .carbon := by
    simpa [azulenePiAtoms] using hi
  have hilow : i.val < 10 := by
    by_contra h
    have hge : ¬ i.val < 10 := by omega
    simpa [azuleneStructure, hydrocarbonAtoms, neutralAtom, hge] using hc
  let k : Fin 10 := ⟨i.val, hilow⟩
  have hik :
      Fin.castLE (by decide : 10 ≤ azuleneStructure.atomCount) k = i := by
    apply Fin.ext
    rfl
  have hpaths : ∀ q : Fin 10,
      Relation.ReflTransGen r 0
        (Fin.castLE (by decide : 10 ≤ azuleneStructure.atomCount) q) := by
    intro q
    fin_cases q <;> assumption
  rw [← hik]
  exact hpaths k

private theorem naphthalene_pi_rooted
    (i : Fin naphthaleneStructure.atomCount) (hi : i ∈ naphthalenePiAtoms) :
    Relation.ReflTransGen
      (fun a b : Fin naphthaleneStructure.atomCount =>
        a ∈ naphthalenePiAtoms ∧ b ∈ naphthalenePiAtoms ∧
          naphthaleneStructure.bondOrderAt a b > 0) 0 i := by
  let r := fun a b : Fin naphthaleneStructure.atomCount =>
    a ∈ naphthalenePiAtoms ∧ b ∈ naphthalenePiAtoms ∧
      naphthaleneStructure.bondOrderAt a b > 0
  change Relation.ReflTransGen r 0 i
  have p0 : Relation.ReflTransGen r 0 0 := .refl
  have p1 := p0.tail (by decide : r 0 1)
  have p2 := p0.tail (by decide : r 0 2)
  have p6 := p0.tail (by decide : r 0 6)
  have p5 := p1.tail (by decide : r 1 5)
  have p9 := p1.tail (by decide : r 1 9)
  have p3 := p2.tail (by decide : r 2 3)
  have p7 := p6.tail (by decide : r 6 7)
  have p4 := p3.tail (by decide : r 3 4)
  have p8 := p7.tail (by decide : r 7 8)
  have hc : (naphthaleneStructure.atoms i).element = .carbon := by
    simpa [naphthalenePiAtoms] using hi
  have hilow : i.val < 10 := by
    by_contra h
    have hge : ¬ i.val < 10 := by omega
    simpa [naphthaleneStructure, hydrocarbonAtoms, neutralAtom, hge] using hc
  let k : Fin 10 := ⟨i.val, hilow⟩
  have hik :
      Fin.castLE (by decide : 10 ≤ naphthaleneStructure.atomCount) k = i := by
    apply Fin.ext
    rfl
  have hpaths : ∀ q : Fin 10,
      Relation.ReflTransGen r 0
        (Fin.castLE (by decide : 10 ≤ naphthaleneStructure.atomCount) q) := by
    intro q
    fin_cases q <;> assumption
  rw [← hik]
  exact hpaths k

private def azuleneAromaticityCertificate :
    HuckelAromaticityCertificate azuleneStructure where
  piAtoms := azulenePiAtoms
  piAtomsExactlyCarbons := by decide
  allPiAtomsCarbon := by decide
  eachPiAtomConjugated := by decide
  piSystemConnected := by
    intro i hi j hj
    have hsymm : ∀ {a b : Fin azuleneStructure.atomCount},
        (a ∈ azulenePiAtoms ∧ b ∈ azulenePiAtoms ∧
          azuleneStructure.bondOrderAt a b > 0) →
        (b ∈ azulenePiAtoms ∧ a ∈ azulenePiAtoms ∧
          azuleneStructure.bondOrderAt b a > 0) := by
      decide
    exact (reflTransGen_reverse hsymm (azulene_pi_rooted i hi)).trans
      (azulene_pi_rooted j hj)
  piElectronCount := 10
  piElectronCount_eq := by decide
  huckelIndex := 2
  huckelRule := by norm_num

private def naphthaleneAromaticityCertificate :
    HuckelAromaticityCertificate naphthaleneStructure where
  piAtoms := naphthalenePiAtoms
  piAtomsExactlyCarbons := by decide
  allPiAtomsCarbon := by decide
  eachPiAtomConjugated := by decide
  piSystemConnected := by
    intro i hi j hj
    have hsymm : ∀ {a b : Fin naphthaleneStructure.atomCount},
        (a ∈ naphthalenePiAtoms ∧ b ∈ naphthalenePiAtoms ∧
          naphthaleneStructure.bondOrderAt a b > 0) →
        (b ∈ naphthalenePiAtoms ∧ a ∈ naphthalenePiAtoms ∧
          naphthaleneStructure.bondOrderAt b a > 0) := by
      decide
    exact (reflTransGen_reverse hsymm (naphthalene_pi_rooted i hi)).trans
      (naphthalene_pi_rooted j hj)
  piElectronCount := 10
  piElectronCount_eq := by decide
  huckelIndex := 2
  huckelRule := by norm_num

/-! ## Explicit geometric reflection witnesses -/

private noncomputable def xMirrorPlane : PlaneThroughOrigin where
  normal := ![1, 0, 0]
  normalNonzero := ⟨0, by change (1 : ℝ) ≠ 0; norm_num⟩

private noncomputable def yMirrorPlane : PlaneThroughOrigin where
  normal := ![0, 1, 0]
  normalNonzero := ⟨1, by change (1 : ℝ) ≠ 0; norm_num⟩

private noncomputable def zMirrorPlane : PlaneThroughOrigin where
  normal := ![0, 0, 1]
  normalNonzero := ⟨2, by change (1 : ℝ) ≠ 0; norm_num⟩

private theorem xMirrorPlane_reflect (v : Vec3) :
    xMirrorPlane.reflect v = ![-v 0, v 1, v 2] := by
  funext d
  fin_cases d <;>
    simp [PlaneThroughOrigin.reflect, xMirrorPlane, dot3,
      Fin.sum_univ_succ] <;> ring

private theorem yMirrorPlane_reflect (v : Vec3) :
    yMirrorPlane.reflect v = ![v 0, -v 1, v 2] := by
  funext d
  fin_cases d <;>
    simp [PlaneThroughOrigin.reflect, yMirrorPlane, dot3,
      Fin.sum_univ_succ] <;> ring

private theorem zMirrorPlane_reflect (v : Vec3) :
    zMirrorPlane.reflect v = ![v 0, v 1, -v 2] := by
  funext d
  fin_cases d <;>
    simp [PlaneThroughOrigin.reflect, zMirrorPlane, dot3,
      Fin.sum_univ_succ] <;> ring

private def azuleneGridPosition : Fin 18 → ℤ × ℤ := ![
  (1, 0), (-1, 0), (2, 1), (3, 2), (4, 3), (-3, 2),
  (-2, 1), (0, 7), (-4, 3), (0, 8), (5, 4), (6, 5),
  (7, 6), (-6, 5), (-5, 4), (0, 9), (-7, 6), (0, 10)]

private def naphthaleneGridPosition : Fin 18 → ℤ × ℤ := ![
  (0, 1), (0, -1), (1, 2), (2, 3), (2, -3), (1, -2),
  (-1, 2), (-2, 3), (-2, -3), (-1, -2), (3, 4), (4, 5),
  (4, -5), (3, -4), (-3, 4), (-4, 5), (-4, -5), (-3, -4)]

private theorem azuleneGridPosition_injective :
    Function.Injective azuleneGridPosition := by decide

private theorem naphthaleneGridPosition_injective :
    Function.Injective naphthaleneGridPosition := by decide

private noncomputable def azulenePosition (i : Fin 18) : Vec3 :=
  ![(azuleneGridPosition i).1, (azuleneGridPosition i).2, 0]

private noncomputable def naphthalenePosition (i : Fin 18) : Vec3 :=
  ![(naphthaleneGridPosition i).1, (naphthaleneGridPosition i).2, 0]

private noncomputable def azuleneSpatialRealization :
    SpatialRealization azuleneStructure where
  position := azulenePosition
  injective := by
    intro i j hij
    apply azuleneGridPosition_injective
    apply Prod.ext
    · have hx := congrFun hij (0 : Fin 3)
      change ((azuleneGridPosition i).1 : ℝ) =
        ((azuleneGridPosition j).1 : ℝ) at hx
      exact_mod_cast hx
    · have hy := congrFun hij (1 : Fin 3)
      change ((azuleneGridPosition i).2 : ℝ) =
        ((azuleneGridPosition j).2 : ℝ) at hy
      exact_mod_cast hy
  noncollinear := by
    refine ⟨0, 1, 2, by decide, by decide, by decide, ?_⟩
    rintro ⟨scale, hscale⟩
    have h0 : azuleneGridPosition 0 = (1, 0) := by decide
    have h1 : azuleneGridPosition 1 = (-1, 0) := by decide
    have h2 : azuleneGridPosition 2 = (2, 1) := by decide
    have hy := hscale (1 : Fin 3)
    change ((azuleneGridPosition 2).2 : ℝ) -
        ((azuleneGridPosition 0).2 : ℝ) =
      scale * (((azuleneGridPosition 1).2 : ℝ) -
        ((azuleneGridPosition 0).2 : ℝ)) at hy
    rw [h0, h1, h2] at hy
    norm_num at hy

private noncomputable def naphthaleneSpatialRealization :
    SpatialRealization naphthaleneStructure where
  position := naphthalenePosition
  injective := by
    intro i j hij
    apply naphthaleneGridPosition_injective
    apply Prod.ext
    · have hx := congrFun hij (0 : Fin 3)
      change ((naphthaleneGridPosition i).1 : ℝ) =
        ((naphthaleneGridPosition j).1 : ℝ) at hx
      exact_mod_cast hx
    · have hy := congrFun hij (1 : Fin 3)
      change ((naphthaleneGridPosition i).2 : ℝ) =
        ((naphthaleneGridPosition j).2 : ℝ) at hy
      exact_mod_cast hy
  noncollinear := by
    refine ⟨0, 1, 2, by decide, by decide, by decide, ?_⟩
    rintro ⟨scale, hscale⟩
    have h0 : naphthaleneGridPosition 0 = (0, 1) := by decide
    have h1 : naphthaleneGridPosition 1 = (0, -1) := by decide
    have h2 : naphthaleneGridPosition 2 = (1, 2) := by decide
    have hx := hscale (0 : Fin 3)
    change ((naphthaleneGridPosition 2).1 : ℝ) -
        ((naphthaleneGridPosition 0).1 : ℝ) =
      scale * (((naphthaleneGridPosition 1).1 : ℝ) -
        ((naphthaleneGridPosition 0).1 : ℝ)) at hx
    rw [h0, h1, h2] at hx
    norm_num at hx

private def azuleneInPlaneReflectionMap : Fin 18 → Fin 18 := ![
  1, 0, 6, 5, 8, 3, 2, 7, 4, 9, 14, 13, 16, 11, 10, 15, 12, 17]

private noncomputable def azuleneInPlaneReflection : Fin 18 ≃ Fin 18 :=
  Equiv.ofBijective azuleneInPlaneReflectionMap (by decide)

private def naphthaleneXReflectionMap : Fin 18 → Fin 18 := ![
  0, 1, 6, 7, 8, 9, 2, 3, 4, 5, 14, 15, 16, 17, 10, 11, 12, 13]

private noncomputable def naphthaleneXReflection : Fin 18 ≃ Fin 18 :=
  Equiv.ofBijective naphthaleneXReflectionMap (by decide)

private def naphthaleneYReflectionMap : Fin 18 → Fin 18 := ![
  1, 0, 5, 4, 3, 2, 9, 8, 7, 6, 13, 12, 11, 10, 17, 16, 15, 14]

private noncomputable def naphthaleneYReflection : Fin 18 ≃ Fin 18 :=
  Equiv.ofBijective naphthaleneYReflectionMap (by decide)

private theorem azuleneGrid_reflect :
    ∀ i : Fin 18, azuleneGridPosition (azuleneInPlaneReflectionMap i) =
      (-(azuleneGridPosition i).1, (azuleneGridPosition i).2) := by
  native_decide

private theorem naphthaleneGrid_reflectX :
    ∀ i : Fin 18, naphthaleneGridPosition (naphthaleneXReflectionMap i) =
      (-(naphthaleneGridPosition i).1, (naphthaleneGridPosition i).2) := by
  native_decide

private theorem naphthaleneGrid_reflectY :
    ∀ i : Fin 18, naphthaleneGridPosition (naphthaleneYReflectionMap i) =
      ((naphthaleneGridPosition i).1, -(naphthaleneGridPosition i).2) := by
  native_decide

private theorem azuleneReflection_preservesAdjacency :
    ∀ i j : Fin 18,
      azuleneStructure.bonded i j ↔
        azuleneStructure.bonded (azuleneInPlaneReflectionMap i)
          (azuleneInPlaneReflectionMap j) := by
  native_decide

private theorem naphthaleneXReflection_preservesAdjacency :
    ∀ i j : Fin 18,
      naphthaleneStructure.bonded i j ↔
        naphthaleneStructure.bonded (naphthaleneXReflectionMap i)
          (naphthaleneXReflectionMap j) := by
  native_decide

private theorem naphthaleneYReflection_preservesAdjacency :
    ∀ i j : Fin 18,
      naphthaleneStructure.bonded i j ↔
        naphthaleneStructure.bonded (naphthaleneYReflectionMap i)
          (naphthaleneYReflectionMap j) := by
  native_decide

private noncomputable def azuleneMolecularPlaneCertificate :
    ReflectionSymmetryCertificate azuleneStructure azuleneSpatialRealization
      zMirrorPlane where
  atomPermutation := Equiv.refl _
  preservesAtoms := by simp
  preservesAdjacency := by simp
  realizesReflection := by
    intro i
    rw [zMirrorPlane_reflect]
    funext d
    fin_cases d <;> simp [azuleneSpatialRealization, azulenePosition]

private noncomputable def azuleneInPlaneCertificate :
    ReflectionSymmetryCertificate azuleneStructure azuleneSpatialRealization
      xMirrorPlane where
  atomPermutation := azuleneInPlaneReflection
  preservesAtoms := by decide
  preservesAdjacency := by
    intro i j
    change azuleneStructure.bonded i j ↔
      azuleneStructure.bonded (azuleneInPlaneReflectionMap i)
        (azuleneInPlaneReflectionMap j)
    exact azuleneReflection_preservesAdjacency i j
  realizesReflection := by
    intro i
    rw [xMirrorPlane_reflect]
    funext d
    fin_cases d
    · change -((azuleneGridPosition i).1 : ℝ) =
        ((azuleneGridPosition (azuleneInPlaneReflectionMap i)).1 : ℝ)
      exact_mod_cast (congrArg Prod.fst (azuleneGrid_reflect i)).symm
    · change ((azuleneGridPosition i).2 : ℝ) =
        ((azuleneGridPosition (azuleneInPlaneReflectionMap i)).2 : ℝ)
      exact_mod_cast (congrArg Prod.snd (azuleneGrid_reflect i)).symm
    · simp [azuleneSpatialRealization, azulenePosition]

private theorem azulene_hasTwoPerpendicularMirrorPlanes :
    HasTwoPerpendicularMirrorPlanes azuleneStructure := by
  refine ⟨azuleneSpatialRealization, zMirrorPlane, xMirrorPlane, ?_,
    ⟨azuleneMolecularPlaneCertificate⟩, ⟨azuleneInPlaneCertificate⟩⟩
  norm_num [PerpendicularPlanes, dot3, zMirrorPlane, xMirrorPlane,
    Fin.sum_univ_succ]

private noncomputable def naphthaleneXPlaneCertificate :
    ReflectionSymmetryCertificate naphthaleneStructure
      naphthaleneSpatialRealization xMirrorPlane where
  atomPermutation := naphthaleneXReflection
  preservesAtoms := by decide
  preservesAdjacency := by
    intro i j
    change naphthaleneStructure.bonded i j ↔
      naphthaleneStructure.bonded (naphthaleneXReflectionMap i)
        (naphthaleneXReflectionMap j)
    exact naphthaleneXReflection_preservesAdjacency i j
  realizesReflection := by
    intro i
    rw [xMirrorPlane_reflect]
    funext d
    fin_cases d
    · change -((naphthaleneGridPosition i).1 : ℝ) =
        ((naphthaleneGridPosition (naphthaleneXReflectionMap i)).1 : ℝ)
      exact_mod_cast (congrArg Prod.fst (naphthaleneGrid_reflectX i)).symm
    · change ((naphthaleneGridPosition i).2 : ℝ) =
        ((naphthaleneGridPosition (naphthaleneXReflectionMap i)).2 : ℝ)
      exact_mod_cast (congrArg Prod.snd (naphthaleneGrid_reflectX i)).symm
    · simp [naphthaleneSpatialRealization, naphthalenePosition]

private noncomputable def naphthaleneYPlaneCertificate :
    ReflectionSymmetryCertificate naphthaleneStructure
      naphthaleneSpatialRealization yMirrorPlane where
  atomPermutation := naphthaleneYReflection
  preservesAtoms := by decide
  preservesAdjacency := by
    intro i j
    change naphthaleneStructure.bonded i j ↔
      naphthaleneStructure.bonded (naphthaleneYReflectionMap i)
        (naphthaleneYReflectionMap j)
    exact naphthaleneYReflection_preservesAdjacency i j
  realizesReflection := by
    intro i
    rw [yMirrorPlane_reflect]
    funext d
    fin_cases d
    · change ((naphthaleneGridPosition i).1 : ℝ) =
        ((naphthaleneGridPosition (naphthaleneYReflectionMap i)).1 : ℝ)
      exact_mod_cast (congrArg Prod.fst (naphthaleneGrid_reflectY i)).symm
    · change -((naphthaleneGridPosition i).2 : ℝ) =
        ((naphthaleneGridPosition (naphthaleneYReflectionMap i)).2 : ℝ)
      exact_mod_cast (congrArg Prod.snd (naphthaleneGrid_reflectY i)).symm
    · simp [naphthaleneSpatialRealization, naphthalenePosition]

private noncomputable def naphthaleneMolecularPlaneCertificate :
    ReflectionSymmetryCertificate naphthaleneStructure
      naphthaleneSpatialRealization zMirrorPlane where
  atomPermutation := Equiv.refl _
  preservesAtoms := by simp
  preservesAdjacency := by simp
  realizesReflection := by
    intro i
    rw [zMirrorPlane_reflect]
    funext d
    fin_cases d <;> simp [naphthaleneSpatialRealization, naphthalenePosition]

private theorem naphthalene_hasThreeMutuallyPerpendicularMirrorPlanes :
    HasThreeMutuallyPerpendicularMirrorPlanes naphthaleneStructure := by
  refine ⟨naphthaleneSpatialRealization, xMirrorPlane, yMirrorPlane,
    zMirrorPlane, ?_, ?_, ?_, ⟨naphthaleneXPlaneCertificate⟩,
    ⟨naphthaleneYPlaneCertificate⟩, ⟨naphthaleneMolecularPlaneCertificate⟩⟩
  · norm_num [PerpendicularPlanes, dot3, xMirrorPlane, yMirrorPlane,
      Fin.sum_univ_succ]
  · norm_num [PerpendicularPlanes, dot3, xMirrorPlane, zMirrorPlane,
      Fin.sum_univ_succ]
  · norm_num [PerpendicularPlanes, dot3, yMirrorPlane, zMirrorPlane,
      Fin.sum_univ_succ]

/-! ## A graph invariant separating the two C10H8 connectivities -/

private def IsHydrogenFreeCarbon (m : MolecularStructure)
    (i : Fin m.atomCount) : Prop :=
  (m.atoms i).element = .carbon ∧
  ∀ h : Fin m.atomCount,
    (m.atoms h).element = .hydrogen → ¬ m.bonded i h

private def IsHydrogenBearingCarbon (m : MolecularStructure)
    (i : Fin m.atomCount) : Prop :=
  (m.atoms i).element = .carbon ∧
  ∃ h : Fin m.atomCount,
    (m.atoms h).element = .hydrogen ∧ m.bonded i h

/-- The hydrogen-free fused edge has, on one side, two hydrogen-bearing
neighbours with a common hydrogen-bearing neighbour.  This is the five-ring
side of azulene; neither six-ring side of naphthalene has this pattern. -/
private def HasShortFusedSide (m : MolecularStructure) : Prop :=
  ∃ u : Fin m.atomCount, IsHydrogenFreeCarbon m u ∧
  ∃ v : Fin m.atomCount, IsHydrogenFreeCarbon m v ∧ m.bonded u v ∧
  ∃ a : Fin m.atomCount, IsHydrogenBearingCarbon m a ∧ m.bonded u a ∧
  ∃ b : Fin m.atomCount, IsHydrogenBearingCarbon m b ∧ m.bonded v b ∧
  ∃ c : Fin m.atomCount, IsHydrogenBearingCarbon m c ∧
    m.bonded a c ∧ m.bonded b c

private theorem hydrogenFreeCarbon_map
    {first second : MolecularStructure}
    (iso : MolecularIsomorphism first second)
    {i : Fin first.atomCount} (hi : IsHydrogenFreeCarbon first i) :
    IsHydrogenFreeCarbon second (iso.atomEquiv i) := by
  constructor
  · have hatom := congrArg (fun atom => atom.element) (iso.preservesAtom i)
    exact hatom.symm.trans hi.1
  · intro h hh hbond
    obtain ⟨h, rfl⟩ := iso.atomEquiv.surjective h
    apply hi.2 h
    · have hatom := congrArg (fun atom => atom.element) (iso.preservesAtom h)
      exact hatom.trans hh
    · exact (iso.preservesAdjacency i h).mpr hbond

private theorem hydrogenBearingCarbon_map
    {first second : MolecularStructure}
    (iso : MolecularIsomorphism first second)
    {i : Fin first.atomCount} (hi : IsHydrogenBearingCarbon first i) :
    IsHydrogenBearingCarbon second (iso.atomEquiv i) := by
  constructor
  · have hatom := congrArg (fun atom => atom.element) (iso.preservesAtom i)
    exact hatom.symm.trans hi.1
  · obtain ⟨h, hh, hbond⟩ := hi.2
    refine ⟨iso.atomEquiv h, ?_, (iso.preservesAdjacency i h).mp hbond⟩
    have hatom := congrArg (fun atom => atom.element) (iso.preservesAtom h)
    exact hatom.symm.trans hh

private theorem shortFusedSide_map
    {first second : MolecularStructure}
    (iso : MolecularIsomorphism first second)
    (h : HasShortFusedSide first) : HasShortFusedSide second := by
  rcases h with ⟨u, hu, v, hv, huv, a, ha, hua, b, hb, hvb,
    c, hc, hac, hbc⟩
  refine ⟨iso.atomEquiv u, hydrogenFreeCarbon_map iso hu,
    iso.atomEquiv v, hydrogenFreeCarbon_map iso hv,
    (iso.preservesAdjacency u v).mp huv,
    iso.atomEquiv a, hydrogenBearingCarbon_map iso ha,
    (iso.preservesAdjacency u a).mp hua,
    iso.atomEquiv b, hydrogenBearingCarbon_map iso hb,
    (iso.preservesAdjacency v b).mp hvb,
    iso.atomEquiv c, hydrogenBearingCarbon_map iso hc,
    (iso.preservesAdjacency a c).mp hac,
    (iso.preservesAdjacency b c).mp hbc⟩

private theorem azulene_hasShortFusedSide : HasShortFusedSide azuleneStructure := by
  unfold HasShortFusedSide IsHydrogenFreeCarbon IsHydrogenBearingCarbon
  native_decide

private theorem naphthalene_not_hasShortFusedSide :
    ¬ HasShortFusedSide naphthaleneStructure := by
  unfold HasShortFusedSide IsHydrogenFreeCarbon IsHydrogenBearingCarbon
  native_decide

private theorem azulene_not_isomorphic_to_naphthalene :
    ¬ Nonempty (MolecularIsomorphism azuleneStructure naphthaleneStructure) := by
  rintro ⟨iso⟩
  exact naphthalene_not_hasShortFusedSide
    (shortFusedSide_map iso azulene_hasShortFusedSide)

/-! ## Quantitative chlorination and molecular-ion witnesses -/

private def compoundSevenMonochlorinatedFormula : MolecularFormula :=
  ⟨14, 15, 0, 1⟩

private def compoundSevenMonochlorinationLedger :
    MonochlorinationLedger compoundSevenFromImage
      compoundSevenMonochlorinatedFormula 1 where
  speciesDomain := monochlorinationSpeciesDomain
  speciesDomain_eq := rfl
  allSpeciesAccounted := by intro species; exact Finset.mem_univ species
  atomBalanced := by native_decide
  chargeBalanced := by native_decide

private def compoundSevenQuantitativeChlorinationStage :
    QuantitativeAromaticMonochlorinationStage azuleneStructure
      compoundSevenFromImage compoundSevenMonochlorinatedFormula where
  classification := .quantitativeMaterialStage
  classification_eq := rfl
  problemLocator := .page3OpeningParagraph
  problemLocator_eq := rfl
  aromaticCore := ⟨azuleneAromaticityCertificate⟩
  substrateIsDerivative := ⟨compoundSevenAlkylSubstitutionCertificate⟩
  substrateHasReplaceableHydrogen := by decide
  substitutionCount := 1
  substitutionCountPositive := by decide
  generalSubstitutionAuthority := openStaxAromaticSubstitutionReference
  generalSubstitutionAuthority_eq := rfl
  chlorineLedgerAuthority := openStaxAromaticChlorinationReference
  chlorineLedgerAuthority_eq := rfl
  ledger := compoundSevenMonochlorinationLedger

private def compoundSevenIonizationLedger :
    ElectronIonizationLedger compoundSevenMonochlorinatedFormula where
  classification := .quantitativeMaterialStage
  classification_eq := rfl
  speciesDomain := ionizationSpeciesDomain
  speciesDomain_eq := rfl
  allSpeciesAccounted := by intro species; exact Finset.mem_univ species
  atomBalanced := by native_decide
  chargeBalanced := by native_decide
  molecularIonRadicalElectrons := 1
  molecularIonRadicalElectrons_eq := rfl
  interpretationAuthority := openStaxMassToChargeReference
  interpretationAuthority_eq := rfl

private def compoundSevenLowPeakCertificate :
    NominalMzCertificate compoundSevenMonochlorinatedFormula
      chlorine35Reference.massNumber observedChlorinationDoublet.lowPeak where
  molecularIonCharge := 1
  molecularIonCharge_eq := rfl
  chargeMagnitude := 1
  chargeMagnitude_eq := rfl
  chargeMagnitude_eq_natAbs := by decide
  molecularIonCharge_eq_ledger := rfl
  numeratorUnit_eq := rfl
  denominatorUnit_eq := rfl
  massToChargeEquation := by native_decide
  interpretationAuthority := openStaxMassToChargeReference
  interpretationAuthority_eq := rfl

private def compoundSevenHighPeakCertificate :
    NominalMzCertificate compoundSevenMonochlorinatedFormula
      chlorine37Reference.massNumber observedChlorinationDoublet.highPeak where
  molecularIonCharge := 1
  molecularIonCharge_eq := rfl
  chargeMagnitude := 1
  chargeMagnitude_eq := rfl
  chargeMagnitude_eq_natAbs := by decide
  molecularIonCharge_eq_ledger := rfl
  numeratorUnit_eq := rfl
  denominatorUnit_eq := rfl
  massToChargeEquation := by native_decide
  interpretationAuthority := openStaxMassToChargeReference
  interpretationAuthority_eq := rfl

private def compoundSevenObservedDoubletCertificate :
    ObservedChlorineDoubletCertificate compoundSevenMonochlorinatedFormula where
  observation := observedChlorinationDoublet
  observation_eq := rfl
  isotopePattern := by
    unfold IsThreeToOneTwoPeakPattern
    decide
  peakSpacing := by decide
  printedIntensityRatio := by decide
  lowIsotopologueWeight := by decide
  highIsotopologueWeight := by decide
  isotopeAuthority := openStaxChlorineIsotopeReference
  isotopeAuthority_eq := rfl
  ionizationLedger := compoundSevenIonizationLedger
  lowPeak := compoundSevenLowPeakCertificate
  highPeak := compoundSevenHighPeakCertificate

private theorem compoundSeven_chlorinationSpec :
    CompoundSevenChlorinationSpec := by
  refine ⟨compoundSevenMonochlorinatedFormula,
    compoundSevenQuantitativeChlorinationStage,
    compoundSevenObservedDoubletCertificate, ?_, rfl⟩
  rfl

private theorem azuleneToNaphthalene_compatibility :
    QualitativeTransformCompatibility azuleneToNaphthaleneTransform := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · decide
  · simpa [azuleneToNaphthaleneTransform, azuleneRecord, naphthaleneRecord]
      using azulene_not_isomorphic_to_naphthalene

private theorem imageIdentityBridge : ImageIdentityBridgeSpec := by
  refine ⟨by decide, ?_, ?_, by decide, ?_, ?_,
    ⟨compoundSevenImageIsomorphism⟩⟩
  · simpa [derivedOutputs, compoundSevenDepiction] using compoundSeven_wellFormed
  · simpa [derivedOutputs, compoundSevenDepiction] using
      compoundSeven_noSpecifiedStereochemistry
  · exact chamazuleneReference_wellFormed
  · exact chamazuleneReference_noSpecifiedStereochemistry

private theorem identityZ_spec : IdentityZRawSpec := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, imageIdentityBridge,
    compoundSeven_chlorinationSpec⟩

private theorem structureA_spec : StructureOfASpec := by
  refine ⟨by decide, ?_, ?_, ⟨azuleneAromaticityCertificate⟩,
    ⟨compoundSevenAlkylSubstitutionCertificate⟩, ?_⟩
  · simpa [structureAOutput, derivedOutputs, azuleneRecord] using azulene_wellFormed
  · simpa [structureAOutput, derivedOutputs, azuleneRecord] using
      azulene_noSpecifiedStereochemistry
  · simpa [structureAOutput, derivedOutputs, azuleneRecord] using
      azulene_hasTwoPerpendicularMirrorPlanes

private theorem structureB_spec : StructureOfBSpec := by
  refine ⟨by decide, ?_, ?_, ⟨naphthaleneAromaticityCertificate⟩,
    ?_, rfl, rfl, azuleneToNaphthalene_compatibility⟩
  · simpa [structureBOutput, derivedOutputs, naphthaleneRecord] using
      naphthalene_wellFormed
  · simpa [structureBOutput, derivedOutputs, naphthaleneRecord] using
      naphthalene_noSpecifiedStereochemistry
  · simpa [structureBOutput, derivedOutputs, naphthaleneRecord] using
      naphthalene_hasThreeMutuallyPerpendicularMirrorPlanes

theorem raw_result : RawResult := by
  exact ⟨identityZ_spec, structureA_spec, structureB_spec⟩

theorem reported_result : ReportedResult := by
  exact ⟨raw_result, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/- The payload hashes are patched after the answer-blind candidate record is
serialized canonically. -/
theorem raw_result_contract :
    ("31b79ee7cd5a2bb4089c518b757c2ffe47752819a653ad874537e61834c52595" : String) =
      "31b79ee7cd5a2bb4089c518b757c2ffe47752819a653ad874537e61834c52595" ∧
    RawResult := by
  exact ⟨rfl, raw_result⟩

theorem reported_result_contract :
    ("f475b88940adeccf0ccba09f68c92075d2c48e016afd93bd38b57c0470ff11c8" : String) =
      "f475b88940adeccf0ccba09f68c92075d2c48e016afd93bd38b57c0470ff11c8" ∧
    ReportedResult := by
  exact ⟨rfl, reported_result⟩

end IChO2026Problems.T1A2
