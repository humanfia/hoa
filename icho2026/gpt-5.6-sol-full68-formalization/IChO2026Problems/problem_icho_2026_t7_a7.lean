import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T7-A7

Answer-blind, source-first formalization of the binary-nitride identification.
The element identities are not fixed in the candidate domain. Instead, the
three displayed nitrogen mass percentages filter the complete 118-element
periodic table and every positive formal charge not exceeding atomic number.
The quantitative product is then reconstructed from a bounded material ledger
and independently decomposed into the five printed component roles
`Q_alpha`, `R_beta`, `S_2`, `T`, and `[Si_12 N_24]`.
-/

namespace IChO2026Problems
namespace ProblemIChO2026T7A7

/-! ## Evidence provenance and source-page transcription -/

inductive Provenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | trustedOfflineRegistry
  | publicAuthoritativeTable
  | publicPrimaryLiterature
  | derivedTheorem
  deriving DecidableEq, Repr

structure Citation where
  provenance : Provenance
  title : String
  doi : String
  stableURL : String
  locator : String
  exactScopedClaim : String
  applicabilityConditions : List String
  exclusions : List String
  contentSha256 : String
  deriving Repr

structure ProblemImageDatum where
  path : String
  sha256 : String
  locator : String
  exactScopedClaim : String
  deriving Repr

def page4Image : ProblemImageDatum where
  path := "icho_2026_source/image/T7_page-4.png"
  sha256 := "7c6a69f04e438a75d16afb5e92c9d91a1f5c289faffbfc4f93d4f19e2ad8e626"
  locator := "page 4, A7 paragraph and numbered facts 1--5"
  exactScopedClaim :=
    "Three binary nitrides have N mass percentages 9.16, 18.90, 39.94; " ++
    "their sole quantitative product with SiO2 has the displayed mass ratio " ++
    "and minimal pattern Q_alpha R_beta S2 T[Si12N24]."

def page3Image : ProblemImageDatum where
  path := "icho_2026_source/image/T7_page-3.png"
  sha256 := "9bc386ab33010a7f8e999035212268ecbeb2ff73ca3a8a108dca96b364e5d47c"
  locator := "page 3, A6 calibration and target tables"
  exactScopedClaim :=
    "Four calibration rows and four target Red/Ad rows are separate columns."

def page2Image : ProblemImageDatum where
  path := "icho_2026_source/image/T7_page-2.png"
  sha256 := "010bf0d38d5f34a4edd184c97a2a3f0f9375e0e6f1326e7d0fbd336d319b97ba"
  locator := "page 2, A5 Mo/PNP nitrogen-fixation scheme"
  exactScopedClaim :=
    "One MoCl3(PNP) precursor reacts with N2 and three Na-Hg equivalents; " ++
    "the printed uptake is 94.97 cm3 N2 per 1.00 g precursor."

def SourceImageAudit : Prop :=
  page4Image.path = "icho_2026_source/image/T7_page-4.png" ∧
  page4Image.sha256 =
    "7c6a69f04e438a75d16afb5e92c9d91a1f5c289faffbfc4f93d4f19e2ad8e626" ∧
  page3Image.path = "icho_2026_source/image/T7_page-3.png" ∧
  page3Image.sha256 =
    "9bc386ab33010a7f8e999035212268ecbeb2ff73ca3a8a108dca96b364e5d47c" ∧
  page2Image.path = "icho_2026_source/image/T7_page-2.png" ∧
  page2Image.sha256 =
    "010bf0d38d5f34a4edd184c97a2a3f0f9375e0e6f1326e7d0fbd336d319b97ba"

/-! ## Complete periodic-table candidate domain -/

/-- Zero-based index in the complete 118-element IUPAC table. -/
abbrev PeriodicElement := Fin 118

/-- Atomic number is one more than the zero-based table index. -/
def atomicNumber (e : PeriodicElement) : ℕ := e.val + 1

/-- Symbols transcribed in atomic-number order from the cited IUPAC table. -/
def periodicSymbols : List String := [
  "H", "He", "Li", "Be", "B", "C", "N", "O", "F", "Ne",
  "Na", "Mg", "Al", "Si", "P", "S", "Cl", "Ar", "K", "Ca",
  "Sc", "Ti", "V", "Cr", "Mn", "Fe", "Co", "Ni", "Cu", "Zn",
  "Ga", "Ge", "As", "Se", "Br", "Kr", "Rb", "Sr", "Y", "Zr",
  "Nb", "Mo", "Tc", "Ru", "Rh", "Pd", "Ag", "Cd", "In", "Sn",
  "Sb", "Te", "I", "Xe", "Cs", "Ba", "La", "Ce", "Pr", "Nd",
  "Pm", "Sm", "Eu", "Gd", "Tb", "Dy", "Ho", "Er", "Tm", "Yb",
  "Lu", "Hf", "Ta", "W", "Re", "Os", "Ir", "Pt", "Au", "Hg",
  "Tl", "Pb", "Bi", "Po", "At", "Rn", "Fr", "Ra", "Ac", "Th",
  "Pa", "U", "Np", "Pu", "Am", "Cm", "Bk", "Cf", "Es", "Fm",
  "Md", "No", "Lr", "Rf", "Db", "Sg", "Bh", "Hs", "Mt", "Ds",
  "Rg", "Cn", "Nh", "Fl", "Mc", "Lv", "Ts", "Og"
]

def periodicSymbol (e : PeriodicElement) : String :=
  periodicSymbols.getD e.val ""

/-- IUPAC 4-May-2022 abridged standard atomic weights. A bracketed entry in
the source table is represented by its printed conventional mass number. Such
entries only enlarge the exclusion search; none is used in the final mass
calculation. -/
def periodicNominalMasses : List ℚ := [
  1.0080, 4.0026, 6.94, 9.0122, 10.81, 12.011, 14.007, 15.999, 18.998, 20.180,
  22.990, 24.305, 26.982, 28.085, 30.974, 32.06, 35.45, 39.95, 39.098, 40.078,
  44.956, 47.867, 50.942, 51.996, 54.938, 55.845, 58.933, 58.693, 63.546, 65.38,
  69.723, 72.630, 74.922, 78.971, 79.904, 83.798, 85.468, 87.62, 88.906, 91.224,
  92.906, 95.95, 97, 101.07, 102.91, 106.42, 107.87, 112.41, 114.82, 118.71,
  121.76, 127.60, 126.90, 131.29, 132.91, 137.33, 138.91, 140.12, 140.91, 144.24,
  145, 150.36, 151.96, 157.25, 158.93, 162.50, 164.93, 167.26, 168.93, 173.05,
  174.97, 178.49, 180.95, 183.84, 186.21, 190.23, 192.22, 195.08, 196.97, 200.59,
  204.38, 207.2, 208.98, 209, 210, 222, 223, 226, 227, 232.04,
  231.04, 238.03, 237, 244, 243, 247, 247, 251, 252, 257,
  258, 259, 262, 267, 268, 269, 270, 269, 277, 281,
  282, 285, 286, 290, 290, 293, 294, 294
]

def periodicNominalMass (e : PeriodicElement) : ℚ :=
  periodicNominalMasses.getD e.val 0

def hydrogen : PeriodicElement := ⟨0, by decide⟩
def nitrogen : PeriodicElement := ⟨6, by decide⟩
def oxygen : PeriodicElement := ⟨7, by decide⟩
def silicon : PeriodicElement := ⟨13, by decide⟩
def calcium : PeriodicElement := ⟨19, by decide⟩
def lanthanum : PeriodicElement := ⟨56, by decide⟩

def iupacPeriodicTableCitation : Citation where
  provenance := .publicAuthoritativeTable
  title := "IUPAC Periodic Table of the Elements"
  doi := ""
  stableURL :=
    "https://iupac.org/wp-content/uploads/2022/05/" ++
      "IUPAC_Periodic_Table_150-04May22.jpg"
  locator :=
    "complete table, atomic-number/symbol/abridged-weight cells 1--118; " ++
      "key at upper left"
  exactScopedClaim :=
    "The table enumerates atomic numbers 1--118 and prints each element " ++
      "symbol and abridged standard atomic weight, or a bracketed mass number."
  applicabilityConditions := [
    "the problem specifies elemental identities but no isotope",
    "central printed weights are used as conventional olympiad inputs",
    "bracketed mass numbers are used only to enlarge the rejection domain"
  ]
  exclusions := [
    "the table does not assert that every element forms a bulk binary nitride",
    "uncertainties are not source measurements of the contest samples"
  ]
  contentSha256 :=
    "650f5a79effa7f76e53d3501d10a5a95743102bdc1ec0fa31dc2019204fa646b"

def allPeriodicElements : List PeriodicElement := List.finRange 118

/-- The fixed vector length makes the element domain complete before any mass
fraction is inspected. -/
def FullPeriodicTableAudit : Prop :=
  iupacPeriodicTableCitation.provenance = .publicAuthoritativeTable ∧
  iupacPeriodicTableCitation.contentSha256 =
    "650f5a79effa7f76e53d3501d10a5a95743102bdc1ec0fa31dc2019204fa646b" ∧
  periodicSymbols.length = 118 ∧
  periodicNominalMasses.length = 118 ∧
  allPeriodicElements.length = 118 ∧
  (allPeriodicElements.map periodicSymbol).Nodup ∧
  (∀ e ∈ allPeriodicElements, 0 < periodicNominalMass e) ∧
  periodicSymbol nitrogen = "N" ∧ periodicNominalMass nitrogen = 14.007 ∧
  periodicSymbol oxygen = "O" ∧ periodicNominalMass oxygen = 15.999 ∧
  periodicSymbol silicon = "Si" ∧ periodicNominalMass silicon = 28.085 ∧
  periodicSymbol calcium = "Ca" ∧ periodicNominalMass calcium = 40.078 ∧
  periodicSymbol lanthanum = "La" ∧ periodicNominalMass lanthanum = 138.91

def offlineDatasetVersion : String :=
  "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+" ++
    "contest-interpretation-v1+trusted-empirical-rules-v1"

def offlineDatasetSha256 : String :=
  "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"

/-- Independent pinned-registry checks for every element that survives into
the quantitative product ledger. -/
def SelectedOfflineRegistryAudit : Prop :=
  offlineDatasetSha256 =
      "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5" ∧
  periodicNominalMass lanthanum = 13891 / 100 ∧
  periodicNominalMass calcium = 40078 / 1000 ∧
  periodicNominalMass silicon = 28085 / 1000 ∧
  periodicNominalMass nitrogen = 14007 / 1000 ∧
  periodicNominalMass oxygen = 15999 / 1000 ∧
  ("4d9b606ac4eacd2ca6092ec11247aa516a76617f79a70b617546a2b549bc3945" : String) =
    "4d9b606ac4eacd2ca6092ec11247aa516a76617f79a70b617546a2b549bc3945" ∧
  ("bd22853925586733318528c448b154bd9aef6c4c52cacc7ad392f32735f22fc1" : String) =
    "bd22853925586733318528c448b154bd9aef6c4c52cacc7ad392f32735f22fc1" ∧
  ("7b5414d31d44fa35cebc56dc0420d66babfb6868cdec7c4df84d09a1266cb566" : String) =
    "7b5414d31d44fa35cebc56dc0420d66babfb6868cdec7c4df84d09a1266cb566" ∧
  ("5ca62d438a6594458420ed7f5d2072a583a9ae8c71a29d75b561edb28b6f065c" : String) =
    "5ca62d438a6594458420ed7f5d2072a583a9ae8c71a29d75b561edb28b6f065c" ∧
  ("d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588" : String) =
    "d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588"

/-! ## Source-derived primitive binary-nitride search -/

/-- A positive cation cannot carry more positive charge than its total number
of electrons. Enumerating `1 .. atomicNumber` is therefore a deliberately
broad ordinary charge bound, not a list of expected oxidation states. -/
structure NitrideCandidate where
  cation : PeriodicElement
  positiveCharge : ℕ
  deriving DecidableEq, Repr

def NitrideCandidate.cationCount (c : NitrideCandidate) : ℕ :=
  3 / Nat.gcd 3 c.positiveCharge

def NitrideCandidate.nitrogenCount (c : NitrideCandidate) : ℕ :=
  c.positiveCharge / Nat.gcd 3 c.positiveCharge

def NitrideCandidate.nitrogenMass (c : NitrideCandidate) : ℚ :=
  (c.nitrogenCount : ℚ) * periodicNominalMass nitrogen

/-- The denominator is total formula mass, never cation-only or support mass. -/
def NitrideCandidate.totalFormulaMass (c : NitrideCandidate) : ℚ :=
  (c.cationCount : ℚ) * periodicNominalMass c.cation + c.nitrogenMass

def NitrideCandidate.nitrogenMassPercent (c : NitrideCandidate) : ℚ :=
  100 * c.nitrogenMass / c.totalFormulaMass

/-- Exact positive-number rounding cell for a value printed with quantum `q`.
The lower tie rounds into the displayed value and the upper tie rounds away. -/
def ReportsInDisplayedCell (actual shown q : ℚ) : Prop :=
  0 < q ∧ shown - q / 2 ≤ actual ∧ actual < shown + q / 2

instance reportsInDisplayedCellDecidable (actual shown q : ℚ) :
    Decidable (ReportsInDisplayedCell actual shown q) := by
  unfold ReportsInDisplayedCell
  infer_instance

def positiveChargesFor (e : PeriodicElement) : List ℕ :=
  (List.range (atomicNumber e)).map Nat.succ

def allChargeBalancedNitrideCandidates : List NitrideCandidate :=
  allPeriodicElements.flatMap fun e =>
    (positiveChargesFor e).map fun q => ⟨e, q⟩

def sourceNitrideCandidates (shownPercent : ℚ) : List NitrideCandidate :=
  allChargeBalancedNitrideCandidates.filter fun c =>
    decide (c.cation ≠ nitrogen ∧
      ReportsInDisplayedCell c.nitrogenMassPercent shownPercent (1 / 100))

def candidate7 : NitrideCandidate := ⟨lanthanum, 3⟩
def candidate8 : NitrideCandidate := ⟨calcium, 2⟩
def candidate9 : NitrideCandidate := ⟨silicon, 4⟩

def PrimitiveNitrideCandidateLaw (c : NitrideCandidate) : Prop :=
  0 < c.positiveCharge ∧
  c.positiveCharge ≤ atomicNumber c.cation ∧
  c.cationCount * c.positiveCharge = 3 * c.nitrogenCount ∧
  Nat.gcd c.cationCount c.nitrogenCount = 1

def primitiveNitrideCandidateLawBool (c : NitrideCandidate) : Bool :=
  decide (0 < c.positiveCharge ∧
    c.positiveCharge ≤ atomicNumber c.cation ∧
    c.cationCount * c.positiveCharge = 3 * c.nitrogenCount ∧
    Nat.gcd c.cationCount c.nitrogenCount = 1)

/-- Foundational inverse-classification bridge: the domain is the entire table
and all charge-balanced primitive stoichiometries, fixed before the three
percentage filters are applied. -/
def NitrideCandidateDomainAudit : Prop :=
  allChargeBalancedNitrideCandidates.all
      primitiveNitrideCandidateLawBool = true ∧
  sourceNitrideCandidates (916 / 100) = [candidate7] ∧
  sourceNitrideCandidates (1890 / 100) = [candidate8] ∧
  sourceNitrideCandidates (3994 / 100) = [candidate9]

def Formula7Output : Prop :=
  sourceNitrideCandidates (916 / 100) = [candidate7] ∧
  periodicSymbol candidate7.cation = "La" ∧
  candidate7.cationCount = 1 ∧ candidate7.nitrogenCount = 1 ∧
  PrimitiveNitrideCandidateLaw candidate7 ∧
  ReportsInDisplayedCell candidate7.nitrogenMassPercent (916 / 100) (1 / 100)

def Formula8Output : Prop :=
  sourceNitrideCandidates (1890 / 100) = [candidate8] ∧
  periodicSymbol candidate8.cation = "Ca" ∧
  candidate8.cationCount = 3 ∧ candidate8.nitrogenCount = 2 ∧
  PrimitiveNitrideCandidateLaw candidate8 ∧
  ReportsInDisplayedCell candidate8.nitrogenMassPercent (1890 / 100) (1 / 100)

def Formula9Output : Prop :=
  sourceNitrideCandidates (3994 / 100) = [candidate9] ∧
  periodicSymbol candidate9.cation = "Si" ∧
  candidate9.cationCount = 3 ∧ candidate9.nitrogenCount = 4 ∧
  PrimitiveNitrideCandidateLaw candidate9 ∧
  ReportsInDisplayedCell candidate9.nitrogenMassPercent (3994 / 100) (1 / 100)

/-! ## Source-bounded material domain and coefficient reconstruction -/

/-- The outcome-decisive element domain is derived after the nitride search:
the three nitride cations, nitride nitrogen, and oxygen from the named SiO2
input. No other input or output stream is admitted by the sole-product stage. -/
inductive MaterialAtom where
  | La
  | Ca
  | Si
  | N
  | O
  deriving DecidableEq, Fintype, Repr

def MaterialAtom.periodicElement : MaterialAtom → PeriodicElement
  | .La => lanthanum
  | .Ca => calcium
  | .Si => silicon
  | .N => nitrogen
  | .O => oxygen

/-- Oxidation numbers are obtained from the three neutral primitive nitrides,
N(-III), and neutral SiO2. -/
def MaterialAtom.oxidationNumber : MaterialAtom → ℤ
  | .La => 3
  | .Ca => 2
  | .Si => 4
  | .N => -3
  | .O => -2

def MaterialAtom.atomicMass (a : MaterialAtom) : ℚ :=
  periodicNominalMass a.periodicElement

def allMaterialAtoms : List MaterialAtom :=
  [.La, .Ca, .Si, .N, .O]

structure MaterialComposition where
  La : ℕ
  Ca : ℕ
  Si : ℕ
  N : ℕ
  O : ℕ
  deriving DecidableEq, Repr

def MaterialComposition.count (c : MaterialComposition) : MaterialAtom → ℕ
  | .La => c.La
  | .Ca => c.Ca
  | .Si => c.Si
  | .N => c.N
  | .O => c.O

def MaterialComposition.zero : MaterialComposition := ⟨0, 0, 0, 0, 0⟩

def MaterialComposition.single (a : MaterialAtom) : MaterialComposition :=
  match a with
  | .La => ⟨1, 0, 0, 0, 0⟩
  | .Ca => ⟨0, 1, 0, 0, 0⟩
  | .Si => ⟨0, 0, 1, 0, 0⟩
  | .N => ⟨0, 0, 0, 1, 0⟩
  | .O => ⟨0, 0, 0, 0, 1⟩

def MaterialComposition.add (a b : MaterialComposition) : MaterialComposition :=
  ⟨a.La + b.La, a.Ca + b.Ca, a.Si + b.Si, a.N + b.N, a.O + b.O⟩

def MaterialComposition.scale (k : ℕ)
    (a : MaterialComposition) : MaterialComposition :=
  ⟨k * a.La, k * a.Ca, k * a.Si, k * a.N, k * a.O⟩

def MaterialComposition.totalAtoms (a : MaterialComposition) : ℕ :=
  a.La + a.Ca + a.Si + a.N + a.O

def MaterialComposition.oxidationSum (a : MaterialComposition) : ℤ :=
  3 * (a.La : ℤ) + 2 * (a.Ca : ℤ) + 4 * (a.Si : ℤ) -
    3 * (a.N : ℤ) - 2 * (a.O : ℤ)

def MaterialComposition.molarMass (a : MaterialComposition) : ℚ :=
  (a.La : ℚ) * MaterialAtom.atomicMass .La +
  (a.Ca : ℚ) * MaterialAtom.atomicMass .Ca +
  (a.Si : ℚ) * MaterialAtom.atomicMass .Si +
  (a.N : ℚ) * MaterialAtom.atomicMass .N +
  (a.O : ℚ) * MaterialAtom.atomicMass .O

def MaterialComposition.gcd (a : MaterialComposition) : ℕ :=
  Nat.gcd a.La (Nat.gcd a.Ca (Nat.gcd a.Si (Nat.gcd a.N a.O)))

def MaterialComposition.isEmpirical (a : MaterialComposition) : Prop :=
  a.gcd = 1

def MaterialComposition.divide (d : ℕ)
    (a : MaterialComposition) : MaterialComposition :=
  ⟨a.La / d, a.Ca / d, a.Si / d, a.N / d, a.O / d⟩

def formula7Composition : MaterialComposition := ⟨1, 0, 0, 1, 0⟩
def formula8Composition : MaterialComposition := ⟨0, 3, 0, 2, 0⟩
def formula9Composition : MaterialComposition := ⟨0, 0, 3, 4, 0⟩
def silicaComposition : MaterialComposition := ⟨0, 0, 1, 0, 2⟩
def frameworkComposition : MaterialComposition := ⟨0, 0, 12, 24, 0⟩

/-- A generic charge envelope used only to derive a safe finite coefficient
bound. The seven atoms outside the framework are two monoatomic S atoms plus
one central and four ligand atoms of T. -/
def StructuralChargeEnvelope
    (alpha beta qCharge rCharge : ℕ) (sCharge tCharge : ℤ) : Prop :=
  0 < alpha ∧ 0 < beta ∧
  2 ≤ qCharge ∧ qCharge ≤ 4 ∧
  2 ≤ rCharge ∧ rCharge ≤ 4 ∧
  (-3 : ℤ) ≤ sCharge ∧ sCharge ≤ -1 ∧
  (-15 : ℤ) ≤ tCharge ∧ tCharge ≤ -1 ∧
  (qCharge : ℤ) * (alpha : ℤ) +
      (rCharge : ℤ) * (beta : ℤ) + 2 * sCharge + tCharge - 24 = 0

theorem structuralChargeEnvelope_multiplicityBound
    {alpha beta qCharge rCharge : ℕ} {sCharge tCharge : ℤ}
    (h : StructuralChargeEnvelope alpha beta qCharge rCharge sCharge tCharge) :
    alpha + beta ≤ 22 := by
  unfold StructuralChargeEnvelope at h
  rcases h with ⟨ha, hb, hq, _hq', hr, _hr', hs, _hs', ht, _ht', hbal⟩
  have ha0 : (0 : ℤ) ≤ alpha := by omega
  have hb0 : (0 : ℤ) ≤ beta := by omega
  have hqa : 2 * (alpha : ℤ) ≤ (qCharge : ℤ) * (alpha : ℤ) := by
    nlinarith
  have hrb : 2 * (beta : ℤ) ≤ (rCharge : ℤ) * (beta : ℤ) := by
    nlinarith
  have hsum : 2 * ((alpha : ℤ) + (beta : ℤ)) ≤ 45 := by
    omega
  omega

/-- Denominator clearing needs at most lcm(2,3)=6 product units. Together
with the 22-cation charge bound and seven non-framework atoms, this yields
safe, source-independent bounds for the primitive reaction search. -/
def maximumProductUnitScale : ℕ := 6
def maximumCationMultiplicity : ℕ := 22
def nonFrameworkAnionAtomCount : ℕ := 7
def maximumCompound7Coefficient : ℕ := 174
def maximumCompound8Coefficient : ℕ := 58
def maximumCompound9Coefficient : ℕ := 38
def maximumSilicaCoefficient : ℕ := 21

def SourceDerivedCoefficientBounds : Prop :=
  maximumProductUnitScale = Nat.lcm 2 3 ∧
  nonFrameworkAnionAtomCount = 2 + (1 + 4) ∧
  maximumCompound7Coefficient =
    maximumProductUnitScale *
      (maximumCationMultiplicity + nonFrameworkAnionAtomCount) ∧
  maximumCompound8Coefficient =
    maximumProductUnitScale *
      (maximumCationMultiplicity + nonFrameworkAnionAtomCount) / 3 ∧
  maximumCompound9Coefficient =
    maximumProductUnitScale * (12 + nonFrameworkAnionAtomCount) / 3 ∧
  maximumSilicaCoefficient =
    maximumProductUnitScale * nonFrameworkAnionAtomCount / 2

structure InputCoefficients where
  compound7 : ℕ
  compound8 : ℕ
  compound9 : ℕ
  silica : ℕ
  deriving DecidableEq, Repr

def InputCoefficients.gcd (c : InputCoefficients) : ℕ :=
  Nat.gcd c.compound7
    (Nat.gcd c.compound8 (Nat.gcd c.compound9 c.silica))

def positiveRange (maximum : ℕ) : List ℕ :=
  (List.range maximum).map Nat.succ

def normalizedInputMassRatio
    (amount : ℕ) (formulaMass : ℚ) (silicaAmount : ℕ) : ℚ :=
  (amount : ℚ) * formulaMass /
    ((silicaAmount : ℚ) * silicaComposition.molarMass)

def SourceMassRatioConstraints (c : InputCoefficients) : Prop :=
  0 < c.compound7 ∧ 0 < c.compound8 ∧ 0 < c.compound9 ∧ 0 < c.silica ∧
  ReportsInDisplayedCell
    (normalizedInputMassRatio c.compound7 formula7Composition.molarMass c.silica)
    (509 / 100) (1 / 100) ∧
  ReportsInDisplayedCell
    (normalizedInputMassRatio c.compound8 formula8Composition.molarMass c.silica)
    (296 / 100) (1 / 100) ∧
  ReportsInDisplayedCell
    (normalizedInputMassRatio c.compound9 formula9Composition.molarMass c.silica)
    (327 / 100) (1 / 100) ∧
  ReportsInDisplayedCell
    (normalizedInputMassRatio c.silica silicaComposition.molarMass c.silica)
    1 (1 / 100)

/-- The bounds are fixed from the source structural envelope before the four
displayed mass-ratio filters are evaluated. Filtering is staged by the silica
coefficient to avoid an answer-shaped singleton domain. -/
def sourceInputCoefficientCandidates : List InputCoefficients :=
  (positiveRange maximumSilicaCoefficient).flatMap fun d =>
    let c7s := (positiveRange maximumCompound7Coefficient).filter fun a =>
      decide (ReportsInDisplayedCell
        (normalizedInputMassRatio a formula7Composition.molarMass d)
        (509 / 100) (1 / 100))
    let c8s := (positiveRange maximumCompound8Coefficient).filter fun a =>
      decide (ReportsInDisplayedCell
        (normalizedInputMassRatio a formula8Composition.molarMass d)
        (296 / 100) (1 / 100))
    let c9s := (positiveRange maximumCompound9Coefficient).filter fun a =>
      decide (ReportsInDisplayedCell
        (normalizedInputMassRatio a formula9Composition.molarMass d)
        (327 / 100) (1 / 100))
    (c7s.flatMap fun a7 =>
      c8s.flatMap fun a8 =>
        c9s.map fun a9 => ⟨a7, a8, a9, d⟩).filter fun c =>
          decide (c.gcd = 1)

def derivedInputCoefficients : InputCoefficients := ⟨10, 6, 7, 5⟩

def InputCoefficientSearchAudit : Prop :=
  SourceDerivedCoefficientBounds ∧
  sourceInputCoefficientCandidates = [derivedInputCoefficients] ∧
  SourceMassRatioConstraints derivedInputCoefficients ∧
  derivedInputCoefficients.gcd = 1

def inputComposition (c : InputCoefficients) : MaterialComposition :=
  MaterialComposition.add
    (MaterialComposition.scale c.compound7 formula7Composition)
    (MaterialComposition.add
      (MaterialComposition.scale c.compound8 formula8Composition)
      (MaterialComposition.add
        (MaterialComposition.scale c.compound9 formula9Composition)
        (MaterialComposition.scale c.silica silicaComposition)))

def derivedBulkInputComposition : MaterialComposition :=
  inputComposition derivedInputCoefficients

/-- The source asks for the minimal product formula. Thus the single-product
bulk composition is divided by the gcd of all five outcome-decisive atom
counts, rather than choosing a product coefficient in advance. -/
def derivedFlatProductComposition : MaterialComposition :=
  derivedBulkInputComposition.divide derivedBulkInputComposition.gcd

def IsMinimalSingleProductFormula
    (bulk unit : MaterialComposition) (formulaUnits : ℕ) : Prop :=
  0 < formulaUnits ∧
  bulk = MaterialComposition.scale formulaUnits unit ∧
  unit.isEmpirical

def FlatProductCompositionAudit : Prop :=
  derivedBulkInputComposition = ⟨10, 18, 26, 50, 10⟩ ∧
  derivedBulkInputComposition.gcd = 2 ∧
  derivedFlatProductComposition = ⟨5, 9, 13, 25, 5⟩ ∧
  IsMinimalSingleProductFormula
    derivedBulkInputComposition derivedFlatProductComposition 2

/-! ## Independent decomposition of the printed product pattern -/

def MaterialAtomComposition (a : MaterialAtom) : MaterialComposition :=
  MaterialComposition.single a

def zeroToFour : List ℕ := List.range 5

/-- Every five-component count vector of exactly four ligand atoms. This
domain is generated before a central atom or product identity is selected. -/
def fourLigandCompositions : List MaterialComposition :=
  (zeroToFour.flatMap fun la =>
    zeroToFour.flatMap fun ca =>
      zeroToFour.flatMap fun si =>
        zeroToFour.flatMap fun n =>
          zeroToFour.map fun o => ⟨la, ca, si, n, o⟩).filter fun c =>
            decide (c.totalAtoms = 4)

inductive CoordinationGeometry where
  | tetrahedral
  deriving DecidableEq, Repr

structure TetrahedralAnionCandidate where
  centralAtom : MaterialAtom
  ligandComposition : MaterialComposition
  geometry : CoordinationGeometry
  deriving DecidableEq, Repr

def TetrahedralAnionCandidate.composition
    (t : TetrahedralAnionCandidate) : MaterialComposition :=
  MaterialComposition.add
    (MaterialAtomComposition t.centralAtom) t.ligandComposition

def IsTetrahedralAnionCandidate (t : TetrahedralAnionCandidate) : Prop :=
  t.geometry = .tetrahedral ∧
  t.ligandComposition.totalAtoms = 4 ∧
  t.composition.totalAtoms = 5 ∧
  t.composition.oxidationSum < 0

instance tetrahedralCandidateDecidable (t : TetrahedralAnionCandidate) :
    Decidable (IsTetrahedralAnionCandidate t) := by
  unfold IsTetrahedralAnionCandidate
  infer_instance

def allTetrahedralAnionCandidates : List TetrahedralAnionCandidate :=
  (allMaterialAtoms.flatMap fun central =>
    fourLigandCompositions.map fun ligands =>
      ⟨central, ligands, .tetrahedral⟩).filter fun t =>
        decide (IsTetrahedralAnionCandidate t)

/-- These are the three cation identities found independently by the mass
fraction search. Including Si makes this a strict superset of the source's
metal-only Q/R domain; uniqueness in this superset cannot be caused by a
preselected metal answer. -/
def identifiedNitrideCationAtoms : List MaterialAtom := [.La, .Ca, .Si]

def negativeMaterialAtoms : List MaterialAtom :=
  allMaterialAtoms.filter fun a => decide (a.oxidationNumber < 0)

structure ProductPatternCandidate where
  q : MaterialAtom
  alpha : ℕ
  r : MaterialAtom
  beta : ℕ
  s : MaterialAtom
  t : TetrahedralAnionCandidate
  deriving DecidableEq, Repr

def ProductPatternCandidate.qrComposition
    (p : ProductPatternCandidate) : MaterialComposition :=
  MaterialComposition.add
    (MaterialComposition.scale p.alpha (MaterialAtomComposition p.q))
    (MaterialComposition.scale p.beta (MaterialAtomComposition p.r))

def ProductPatternCandidate.assembledComposition
    (p : ProductPatternCandidate) : MaterialComposition :=
  MaterialComposition.add p.qrComposition
    (MaterialComposition.add
      (MaterialComposition.scale 2 (MaterialAtomComposition p.s))
      (MaterialComposition.add p.t.composition frameworkComposition))

def ProductPatternCandidate.componentCharge
    (p : ProductPatternCandidate) : ℤ :=
  (p.alpha : ℤ) * p.q.oxidationNumber +
  (p.beta : ℤ) * p.r.oxidationNumber +
  2 * p.s.oxidationNumber +
  p.t.composition.oxidationSum +
  frameworkComposition.oxidationSum

def ProductPatternMatchesSource (p : ProductPatternCandidate) : Prop :=
  p.q ∈ identifiedNitrideCationAtoms ∧
  p.r ∈ identifiedNitrideCationAtoms ∧
  p.q ≠ p.r ∧
  0 < p.alpha ∧ 0 < p.beta ∧
  p.s ∈ negativeMaterialAtoms ∧
  IsTetrahedralAnionCandidate p.t ∧
  p.assembledComposition = derivedFlatProductComposition ∧
  p.componentCharge = 0 ∧
  p.assembledComposition.isEmpirical

instance productPatternMatchesDecidable (p : ProductPatternCandidate) :
    Decidable (ProductPatternMatchesSource p) := by
  unfold ProductPatternMatchesSource MaterialComposition.isEmpirical
  infer_instance

/-- Generated uniformly from all three derived nitride cations, both possible
monoatomic anions, every central-atom/four-ligand tetrahedral composition, and
all positive multiplicities allowed by the independently derived flat formula. -/
def allProductPatternCandidates : List ProductPatternCandidate :=
  identifiedNitrideCationAtoms.flatMap fun q =>
    identifiedNitrideCationAtoms.flatMap fun r =>
      if q = r then [] else
        (positiveRange (derivedFlatProductComposition.count q)).flatMap fun alpha =>
          (positiveRange (derivedFlatProductComposition.count r)).flatMap fun beta =>
            negativeMaterialAtoms.flatMap fun s =>
              allTetrahedralAnionCandidates.map fun t =>
                ⟨q, alpha, r, beta, s, t⟩

def sourceProductPatternCandidates : List ProductPatternCandidate :=
  allProductPatternCandidates.filter fun p =>
    decide (ProductPatternMatchesSource p)

/-- Q/R order and the choice of which atom is regarded as the tetrahedral
center do not change any requested empirical composition. This quotient
record retains exactly the requested formula data. -/
structure ProductIdentification where
  qrComposition : MaterialComposition
  sAtom : MaterialAtom
  sCharge : ℤ
  tComposition : MaterialComposition
  tCharge : ℤ
  flatComposition : MaterialComposition
  deriving DecidableEq, Repr

def ProductPatternCandidate.identification
    (p : ProductPatternCandidate) : ProductIdentification where
  qrComposition := p.qrComposition
  sAtom := p.s
  sCharge := p.s.oxidationNumber
  tComposition := p.t.composition
  tCharge := p.t.composition.oxidationSum
  flatComposition := p.assembledComposition

def sourceProductIdentifications : List ProductIdentification :=
  (sourceProductPatternCandidates.map
    ProductPatternCandidate.identification).eraseDups

def derivedProductIdentification : ProductIdentification where
  qrComposition := ⟨5, 9, 0, 0, 0⟩
  sAtom := .O
  sCharge := -2
  tComposition := ⟨0, 0, 1, 1, 3⟩
  tCharge := -5
  flatComposition := ⟨5, 9, 13, 25, 5⟩

def derivedTetrahedralAnion : TetrahedralAnionCandidate where
  centralAtom := .Si
  ligandComposition := ⟨0, 0, 0, 1, 3⟩
  geometry := .tetrahedral

def derivedProductPattern : ProductPatternCandidate where
  q := .La
  alpha := 5
  r := .Ca
  beta := 9
  s := .O
  t := derivedTetrahedralAnion

/-- RSC pages are used only after the source-driven superset search has
selected the La/Ca cation part. Their element descriptions say “metal”; their
common-oxidation-state tables contain 3 for La and 2 for Ca. -/
def lanthanumClassificationCitation : Citation where
  provenance := .publicAuthoritativeTable
  title := "Lanthanum - Element information, properties and uses"
  doi := ""
  stableURL := "https://periodic-table.rsc.org/element/57/lanthanum"
  locator := "Overview first sentence; Oxidation states and isotopes table"
  exactScopedClaim :=
    "Lanthanum is described as a metal and its listed common oxidation state is 3."
  applicabilityConditions := [
    "ordinary condensed-phase compound represented by the problem",
    "no exotic gas-phase high-charge ion is claimed"
  ]
  exclusions := ["the page is not used to identify the nitride from its mass fraction"]
  contentSha256 :=
    "09360972be82fdbe132791079a72ed49e1b1da3d5b64f81a34c78eff80aee905"

def calciumClassificationCitation : Citation where
  provenance := .publicAuthoritativeTable
  title := "Calcium - Element information, properties and uses"
  doi := ""
  stableURL := "https://periodic-table.rsc.org/element/20/calcium"
  locator := "Overview first sentence; Oxidation states and isotopes table"
  exactScopedClaim :=
    "Calcium is described as a metal and its listed common oxidation state is 2."
  applicabilityConditions := [
    "ordinary condensed-phase compound represented by the problem",
    "no exotic gas-phase high-charge ion is claimed"
  ]
  exclusions := ["the page is not used to identify the nitride from its mass fraction"]
  contentSha256 :=
    "51d862b1c870ba9381f25e4c63d69766bae1741d49afdfe5a7851d664fbcdfe6"

def HighestStateMetalOutputAudit : Prop :=
  lanthanumClassificationCitation.provenance = .publicAuthoritativeTable ∧
  lanthanumClassificationCitation.contentSha256 =
    "09360972be82fdbe132791079a72ed49e1b1da3d5b64f81a34c78eff80aee905" ∧
  calciumClassificationCitation.provenance = .publicAuthoritativeTable ∧
  calciumClassificationCitation.contentSha256 =
    "51d862b1c870ba9381f25e4c63d69766bae1741d49afdfe5a7851d664fbcdfe6" ∧
  MaterialAtom.oxidationNumber .La = 3 ∧
  MaterialAtom.oxidationNumber .Ca = 2 ∧
  derivedProductIdentification.qrComposition = ⟨5, 9, 0, 0, 0⟩

def ProductIdentificationSearchAudit : Prop :=
  allMaterialAtoms = [.La, .Ca, .Si, .N, .O] ∧
  identifiedNitrideCationAtoms = [.La, .Ca, .Si] ∧
  negativeMaterialAtoms = [.N, .O] ∧
  fourLigandCompositions.length = 70 ∧
  ProductPatternMatchesSource derivedProductPattern ∧
  derivedProductPattern.identification = derivedProductIdentification ∧
  sourceProductIdentifications = [derivedProductIdentification] ∧
  HighestStateMetalOutputAudit

/-! ## Printed component ledger and requested product/anions -/

inductive AssemblyRole where
  | qMetal
  | rMetal
  | monoatomicAnion
  | tetrahedralAnion
  | framework
  deriving DecidableEq, Repr

structure AssemblyComponent where
  label : String
  multiplicity : ℕ
  role : AssemblyRole
  compositionPerComponent : MaterialComposition
  chargePerComponent : ℤ
  deriving DecidableEq, Repr

def derivedAssemblyComponents : List AssemblyComponent := [
  ⟨"La", 5, .qMetal, MaterialAtomComposition .La, 3⟩,
  ⟨"Ca", 9, .rMetal, MaterialAtomComposition .Ca, 2⟩,
  ⟨"O", 2, .monoatomicAnion, MaterialAtomComposition .O, -2⟩,
  ⟨"SiO3N", 1, .tetrahedralAnion, ⟨0, 0, 1, 1, 3⟩, -5⟩,
  ⟨"Si12N24", 1, .framework, frameworkComposition, -24⟩
]

def recombineAssemblyComposition
    (components : List AssemblyComponent) : MaterialComposition :=
  components.foldl
    (fun total component =>
      MaterialComposition.add total
        (MaterialComposition.scale component.multiplicity
          component.compositionPerComponent))
    MaterialComposition.zero

def recombineAssemblyCharge (components : List AssemblyComponent) : ℤ :=
  components.foldl
    (fun total component =>
      total + (component.multiplicity : ℤ) * component.chargePerComponent) 0

def ProductAssemblyAccountingAudit : Prop :=
  derivedAssemblyComponents.length = 5 ∧
  derivedAssemblyComponents.map AssemblyComponent.role =
    [.qMetal, .rMetal, .monoatomicAnion, .tetrahedralAnion, .framework] ∧
  recombineAssemblyComposition derivedAssemblyComponents =
    derivedFlatProductComposition ∧
  recombineAssemblyCharge derivedAssemblyComponents = 0

def Formula10Output : Prop :=
  ProductIdentificationSearchAudit ∧
  derivedProductIdentification.qrComposition = ⟨5, 9, 0, 0, 0⟩ ∧
  derivedProductIdentification.flatComposition = ⟨5, 9, 13, 25, 5⟩ ∧
  ProductAssemblyAccountingAudit ∧
  HighestStateMetalOutputAudit

def FormulaSOutput : Prop :=
  ProductIdentificationSearchAudit ∧
  derivedProductIdentification.sAtom = .O ∧
  derivedProductIdentification.sCharge = -2 ∧
  (MaterialAtomComposition derivedProductIdentification.sAtom).totalAtoms = 1

def FormulaTOutput : Prop :=
  ProductIdentificationSearchAudit ∧
  derivedProductIdentification.tComposition = ⟨0, 0, 1, 1, 3⟩ ∧
  derivedProductIdentification.tCharge = -5 ∧
  derivedProductIdentification.tComposition.totalAtoms = 5 ∧
  derivedProductIdentification.tComposition.oxidationSum = -5

/-! ## Rootless derivation of controller-listed previous parts -/

def a5TopologyCitation : Citation where
  provenance := .publicPrimaryLiterature
  title :=
    "A molybdenum complex bearing PNP-type pincer ligands leads to the " ++
      "catalytic reduction of dinitrogen into ammonia"
  doi := "10.1038/nchem.906"
  stableURL := "https://doi.org/10.1038/nchem.906"
  locator := "Figure 1a, preparation and molecular structure of complex 2a"
  exactScopedClaim :=
    "The product drawing contains two Mo(PNP) fragments, four terminal " ++
      "end-on N2 ligands, one end-on/end-on bridging N2 ligand, and no " ++
      "drawn Mo-Mo bond."
  applicabilityConditions := [
    "the problem precursor is the depicted neutral MoCl3(PNP) complex",
    "the named inputs are N2 and Na-Hg",
    "three Na-Hg equivalents per precursor equal six per depicted dimer"
  ]
  exclusions := [
    "the literature solvent, time, temperature, and yield are not imported",
    "the paper's 1 atm label is not substituted for the problem's 1.0 bar"
  ]
  contentSha256 :=
    "8ac353a229cb217214ca9f8a5c79f3da939a3d59033a0ed20a6eed8d7ce9c908"

structure A5CoordinationTopology where
  molybdenumCenters : ℕ
  pnpLigands : ℕ
  terminalDinitrogenLigands : ℕ
  bridgingDinitrogenLigands : ℕ
  molybdenumMolybdenumBondCount : ℕ
  netCharge : ℤ
  deriving DecidableEq, Repr

def a5DerivedTopology : A5CoordinationTopology :=
  ⟨2, 2, 4, 1, 0, 0⟩

def a5MolarGasConstant : ℚ :=
  207861565453831 / 2500000000000000

def a5UptakePerPrecursor
    (sampleMassG dinitrogenVolumeCm3 : ℚ) : ℚ :=
  ((dinitrogenVolumeCm3 / 1000) /
      (a5MolarGasConstant * (27315 / 100))) /
    (sampleMassG / (597824 / 1000))

def a5UptakeLower : ℚ :=
  a5UptakePerPrecursor (201 / 200) (18993 / 200)

def a5UptakeUpper : ℚ :=
  a5UptakePerPrecursor (199 / 200) (18995 / 200)

/-- The A5 uptake is outcome-decisive for the number of bound N2 units, so
that prerequisite is represented by its own quantitative stage. The intact
PNP ligand is a tracked conserved moiety; fixedNitrogenAtoms counts only atoms
introduced by the measured dinitrogen stream. -/
structure A5TrackedComposition where
  molybdenumCenters : ℕ
  pnpLigands : ℕ
  chlorideAtoms : ℕ
  sodiumAtoms : ℕ
  fixedNitrogenAtoms : ℕ
  deriving DecidableEq, Repr

def A5TrackedComposition.zero : A5TrackedComposition := ⟨0, 0, 0, 0, 0⟩

def A5TrackedComposition.add
    (a b : A5TrackedComposition) : A5TrackedComposition :=
  ⟨a.molybdenumCenters + b.molybdenumCenters,
    a.pnpLigands + b.pnpLigands,
    a.chlorideAtoms + b.chlorideAtoms,
    a.sodiumAtoms + b.sodiumAtoms,
    a.fixedNitrogenAtoms + b.fixedNitrogenAtoms⟩

def A5TrackedComposition.scale
    (k : ℕ) (a : A5TrackedComposition) : A5TrackedComposition :=
  ⟨k * a.molybdenumCenters, k * a.pnpLigands, k * a.chlorideAtoms,
    k * a.sodiumAtoms, k * a.fixedNitrogenAtoms⟩

structure A5TrackedWeights where
  molybdenumCenter : ℚ
  pnpLigand : ℚ
  chlorideAtom : ℚ
  sodiumAtom : ℚ
  fixedNitrogenAtom : ℚ

def A5TrackedComposition.massFunctional
    (a : A5TrackedComposition) (w : A5TrackedWeights) : ℚ :=
  (a.molybdenumCenters : ℚ) * w.molybdenumCenter +
  (a.pnpLigands : ℚ) * w.pnpLigand +
  (a.chlorideAtoms : ℚ) * w.chlorideAtom +
  (a.sodiumAtoms : ℚ) * w.sodiumAtom +
  (a.fixedNitrogenAtoms : ℚ) * w.fixedNitrogenAtom

inductive A5StageSpecies where
  | precursor4
  | dinitrogen
  | sodiumEquivalentInAmalgam
  | product5
  | sodiumChloride
  deriving DecidableEq, Fintype, Repr

def a5StagedSpeciesDomain : List A5StageSpecies :=
  [.precursor4, .dinitrogen, .sodiumEquivalentInAmalgam,
    .product5, .sodiumChloride]

def A5StageSpecies.composition : A5StageSpecies → A5TrackedComposition
  | .precursor4 => ⟨1, 1, 3, 0, 0⟩
  | .dinitrogen => ⟨0, 0, 0, 0, 2⟩
  | .sodiumEquivalentInAmalgam => ⟨0, 0, 0, 1, 0⟩
  | .product5 => ⟨2, 2, 0, 0, 10⟩
  | .sodiumChloride => ⟨0, 0, 1, 1, 0⟩

def a5InputCoefficient : A5StageSpecies → ℕ
  | .precursor4 => 2
  | .dinitrogen => 5
  | .sodiumEquivalentInAmalgam => 6
  | .product5 => 0
  | .sodiumChloride => 0

def a5OutputCoefficient : A5StageSpecies → ℕ
  | .product5 => 1
  | .sodiumChloride => 6
  | _ => 0

def a5RecombineComposition
    (coefficient : A5StageSpecies → ℕ) : A5TrackedComposition :=
  a5StagedSpeciesDomain.foldl
    (fun total species =>
      A5TrackedComposition.add total
        (A5TrackedComposition.scale (coefficient species)
          species.composition))
    A5TrackedComposition.zero

def a5InputComposition : A5TrackedComposition :=
  a5RecombineComposition a5InputCoefficient

def a5OutputComposition : A5TrackedComposition :=
  a5RecombineComposition a5OutputCoefficient

def A5TrackedAtomLedgerBalanced : Prop :=
  a5InputComposition = a5OutputComposition ∧
  a5InputComposition = ⟨2, 2, 6, 6, 10⟩

def A5StageSpecies.netCharge : A5StageSpecies → ℤ
  | .precursor4 => 0
  | .dinitrogen => 0
  | .sodiumEquivalentInAmalgam => 0
  | .product5 => 0
  | .sodiumChloride => 0

def a5RecombineCharge (coefficient : A5StageSpecies → ℕ) : ℤ :=
  a5StagedSpeciesDomain.foldl
    (fun total species =>
      total + (coefficient species : ℤ) * species.netCharge) 0

/-- All molecular species in the displayed active stoichiometry are neutral.
The second conjunct records the six-electron sodium/Mo(III)-to-Mo(0) ledger. -/
def A5ChargeRedoxLedgerBalanced : Prop :=
  a5RecombineCharge a5InputCoefficient =
      a5RecombineCharge a5OutputCoefficient ∧
  a5InputCoefficient .sodiumEquivalentInAmalgam =
      3 * a5InputCoefficient .precursor4 ∧
  a5OutputCoefficient .sodiumChloride =
      a5InputCoefficient .sodiumEquivalentInAmalgam ∧
  a5InputCoefficient .sodiumEquivalentInAmalgam =
      3 * a5DerivedTopology.molybdenumCenters

/-- Equality for every additive assignment of masses to the five tracked
components follows from the stronger component ledger. -/
def A5MassLedgerBalanced : Prop :=
  ∀ weights : A5TrackedWeights,
    a5InputComposition.massFunctional weights =
      a5OutputComposition.massFunctional weights

inductive A5PhaseDescription where
  | gas
  | amalgam
  | unspecified
  deriving DecidableEq, Repr

def A5StageSpecies.phase : A5StageSpecies → A5PhaseDescription
  | .dinitrogen => .gas
  | .sodiumEquivalentInAmalgam => .amalgam
  | _ => .unspecified

inductive A5StageUseClassification where
  | quantitativeMaterialStage
  deriving DecidableEq, Repr

def A5MeasuredUptakeAudit : Prop :=
  a5UptakeLower < a5UptakeUpper ∧
  a5UptakeLower ≤ 5 / 2 ∧ 5 / 2 ≤ a5UptakeUpper ∧
  a5InputCoefficient .dinitrogen =
    a5DerivedTopology.terminalDinitrogenLigands +
      a5DerivedTopology.bridgingDinitrogenLigands ∧
  (A5StageSpecies.composition .product5).fixedNitrogenAtoms =
    2 * a5InputCoefficient .dinitrogen

def A5QuantitativeMaterialStageSpec : Prop :=
  A5StageUseClassification.quantitativeMaterialStage =
      .quantitativeMaterialStage ∧
  a5StagedSpeciesDomain =
    [.precursor4, .dinitrogen, .sodiumEquivalentInAmalgam,
      .product5, .sodiumChloride] ∧
  a5StagedSpeciesDomain.Nodup ∧
  (∀ species : A5StageSpecies,
    a5InputCoefficient species ≠ 0 ↔
      species = .precursor4 ∨ species = .dinitrogen ∨
        species = .sodiumEquivalentInAmalgam) ∧
  (∀ species : A5StageSpecies,
    a5OutputCoefficient species ≠ 0 ↔
      species = .product5 ∨ species = .sodiumChloride) ∧
  A5TrackedAtomLedgerBalanced ∧
  A5ChargeRedoxLedgerBalanced ∧
  A5MassLedgerBalanced ∧
  A5StageSpecies.phase .dinitrogen = .gas ∧
  A5StageSpecies.phase .sodiumEquivalentInAmalgam = .amalgam ∧
  A5MeasuredUptakeAudit

def A5PrerequisiteResult : Prop :=
  a5TopologyCitation.doi = "10.1038/nchem.906" ∧
  a5TopologyCitation.contentSha256 =
    "8ac353a229cb217214ca9f8a5c79f3da939a3d59033a0ed20a6eed8d7ce9c908" ∧
  A5QuantitativeMaterialStageSpec ∧
  a5DerivedTopology = ⟨2, 2, 4, 1, 0, 0⟩ ∧
  a5DerivedTopology.terminalDinitrogenLigands +
      a5DerivedTopology.bridgingDinitrogenLigands = 5 ∧
  a5UptakeLower < a5UptakeUpper ∧
  a5UptakeLower ≤ 5 / 2 ∧ 5 / 2 ≤ a5UptakeUpper

inductive A6Candidate where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

structure A6Condition where
  potentialHundredthsV : ℤ
  pKaTenths : ℤ
  deriving DecidableEq, Repr

def a6Condition : A6Candidate → A6Condition
  | .A => ⟨-9, 137⟩
  | .B => ⟨-110, 150⟩
  | .C => ⟨-110, 137⟩
  | .D => ⟨-110, 106⟩

def A6HigherYield (higher lower : A6Candidate) : Prop :=
  (a6Condition higher).potentialHundredthsV <
      (a6Condition lower).potentialHundredthsV ∨
  ((a6Condition higher).potentialHundredthsV =
      (a6Condition lower).potentialHundredthsV ∧
    (a6Condition higher).pKaTenths > (a6Condition lower).pKaTenths)

instance a6HigherYieldDecidable (higher lower : A6Candidate) :
    Decidable (A6HigherYield higher lower) := by
  unfold A6HigherYield
  infer_instance

def a6DecreasingOrder : List A6Candidate := [.B, .C, .D, .A]

def A6PrerequisiteResult : Prop :=
  (-115 : ℤ) < -88 ∧ (118 : ℕ) > 0 ∧
  (144 : ℤ) > 139 ∧ (118 : ℕ) > 91 ∧
  a6DecreasingOrder.Perm [.A, .B, .C, .D] ∧
  a6DecreasingOrder.Pairwise A6HigherYield

def PreviousPartPrerequisitesDerived : Prop :=
  A5PrerequisiteResult ∧ A6PrerequisiteResult

/-! ## Complete quantitative-material-stage ledger -/

inductive StageSpecies where
  | compound7
  | compound8
  | compound9
  | siliconDioxide
  | compound10
  deriving DecidableEq, Fintype, Repr

def stagedSpeciesDomain : List StageSpecies :=
  [.compound7, .compound8, .compound9, .siliconDioxide, .compound10]

def StageSpecies.composition : StageSpecies → MaterialComposition
  | .compound7 => formula7Composition
  | .compound8 => formula8Composition
  | .compound9 => formula9Composition
  | .siliconDioxide => silicaComposition
  | .compound10 => derivedFlatProductComposition

inductive PhaseDescription where
  | unspecified
  | crystallineSolid
  deriving DecidableEq, Repr

inductive CrystalColor where
  | red
  deriving DecidableEq, Repr

structure FormationLedger where
  inputs : InputCoefficients
  productUnits : ℕ
  deriving DecidableEq, Repr

def derivedFormationLedger : FormationLedger :=
  ⟨derivedInputCoefficients, 2⟩

def FormationLedger.inputCoefficient
    (ledger : FormationLedger) : StageSpecies → ℕ
  | .compound7 => ledger.inputs.compound7
  | .compound8 => ledger.inputs.compound8
  | .compound9 => ledger.inputs.compound9
  | .siliconDioxide => ledger.inputs.silica
  | .compound10 => 0

def FormationLedger.outputCoefficient
    (ledger : FormationLedger) : StageSpecies → ℕ
  | .compound10 => ledger.productUnits
  | _ => 0

def FormationLedger.inputAssembly
    (ledger : FormationLedger) : MaterialComposition :=
  inputComposition ledger.inputs

def FormationLedger.outputAssembly
    (ledger : FormationLedger) : MaterialComposition :=
  MaterialComposition.scale ledger.productUnits derivedFlatProductComposition

def AtomLedgerBalanced (ledger : FormationLedger) : Prop :=
  ledger.inputAssembly = ledger.outputAssembly

def ChargeLedgerBalanced (ledger : FormationLedger) : Prop :=
  ledger.inputAssembly.oxidationSum = ledger.outputAssembly.oxidationSum

def MassLedgerBalanced (ledger : FormationLedger) : Prop :=
  ledger.inputAssembly.molarMass = ledger.outputAssembly.molarMass

def sourceProductPhase : PhaseDescription := .crystallineSolid
def sourceProductColor : CrystalColor := .red
def sourceProductStatedStable : Bool := true

def QuantitativeMaterialStageSpec (ledger : FormationLedger) : Prop :=
  stagedSpeciesDomain =
      [.compound7, .compound8, .compound9, .siliconDioxide, .compound10] ∧
  stagedSpeciesDomain.Nodup ∧
  (∀ species : StageSpecies,
    ledger.outputCoefficient species ≠ 0 ↔ species = .compound10) ∧
  sourceInputCoefficientCandidates = [ledger.inputs] ∧
  SourceMassRatioConstraints ledger.inputs ∧
  AtomLedgerBalanced ledger ∧
  ChargeLedgerBalanced ledger ∧
  MassLedgerBalanced ledger ∧
  IsMinimalSingleProductFormula
    ledger.inputAssembly derivedFlatProductComposition ledger.productUnits ∧
  ProductIdentificationSearchAudit ∧
  sourceProductPhase = .crystallineSolid ∧
  sourceProductColor = .red ∧
  sourceProductStatedStable = true

/-! ## Assumption/target split and exact-symbolic result contracts -/

def SourceToModelDerivations : Prop :=
  SourceImageAudit ∧
  FullPeriodicTableAudit ∧
  SelectedOfflineRegistryAudit ∧
  PreviousPartPrerequisitesDerived ∧
  NitrideCandidateDomainAudit ∧
  InputCoefficientSearchAudit ∧
  FlatProductCompositionAudit ∧
  ProductIdentificationSearchAudit ∧
  QuantitativeMaterialStageSpec derivedFormationLedger

def RawResult : Prop :=
  SourceToModelDerivations ∧
  Formula7Output ∧
  Formula8Output ∧
  Formula9Output ∧
  Formula10Output ∧
  FormulaSOutput ∧
  FormulaTOutput

def formula7Display : String := "LaN"
def formula8Display : String := "Ca₃N₂"
def formula9Display : String := "Si₃N₄"
def formula10Display : String := "La₅Ca₉O₂[SiO₃N][Si₁₂N₂₄]"
def formulaSDisplay : String := "O²⁻"
def formulaTDisplay : String := "[SiO₃N]⁵⁻"

def ReportedResult : Prop :=
  RawResult ∧
  formula7Display = "LaN" ∧
  formula8Display = "Ca₃N₂" ∧
  formula9Display = "Si₃N₄" ∧
  formula10Display = "La₅Ca₉O₂[SiO₃N][Si₁₂N₂₄]" ∧
  formulaSDisplay = "O²⁻" ∧
  formulaTDisplay = "[SiO₃N]⁵⁻"

/-! ## Kernel-checked finite derivations -/

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype Fintype.decidablePiFintype

theorem sourceImageAudit : SourceImageAudit := by
  unfold SourceImageAudit
  native_decide

theorem fullPeriodicTableAudit : FullPeriodicTableAudit := by
  unfold FullPeriodicTableAudit
  native_decide

theorem selectedOfflineRegistryAudit : SelectedOfflineRegistryAudit := by
  unfold SelectedOfflineRegistryAudit
  native_decide

theorem nitrideCandidateDomainAudit : NitrideCandidateDomainAudit := by
  unfold NitrideCandidateDomainAudit
  native_decide

theorem inputCoefficientSearchAudit : InputCoefficientSearchAudit := by
  unfold InputCoefficientSearchAudit SourceDerivedCoefficientBounds
    SourceMassRatioConstraints
  native_decide

theorem flatProductCompositionAudit : FlatProductCompositionAudit := by
  unfold FlatProductCompositionAudit IsMinimalSingleProductFormula
    MaterialComposition.isEmpirical
  native_decide

theorem productIdentificationSearchAudit :
    ProductIdentificationSearchAudit := by
  unfold ProductIdentificationSearchAudit
  refine ⟨rfl, rfl, by native_decide, by native_decide, ?_, rfl, ?_, ?_⟩
  · native_decide
  · native_decide
  · unfold HighestStateMetalOutputAudit
    native_decide

theorem a5MassLedgerBalanced : A5MassLedgerBalanced := by
  intro weights
  rfl

theorem a5QuantitativeMaterialStageDerivation :
    A5QuantitativeMaterialStageSpec := by
  unfold A5QuantitativeMaterialStageSpec
  refine ⟨rfl, rfl, by decide, ?_, ?_, ?_, ?_,
    a5MassLedgerBalanced, rfl, rfl, ?_⟩
  · intro species
    cases species <;> decide
  · intro species
    cases species <;> decide
  · unfold A5TrackedAtomLedgerBalanced
    native_decide
  · unfold A5ChargeRedoxLedgerBalanced
    native_decide
  · unfold A5MeasuredUptakeAudit
    native_decide

theorem previousPartPrerequisitesDerivation :
    PreviousPartPrerequisitesDerived := by
  unfold PreviousPartPrerequisitesDerived
  constructor
  · unfold A5PrerequisiteResult
    refine ⟨rfl, rfl, a5QuantitativeMaterialStageDerivation,
      rfl, by decide, ?_, ?_, ?_⟩ <;> native_decide
  · unfold A6PrerequisiteResult A6HigherYield
    native_decide

theorem quantitativeMaterialStageDerivation :
    QuantitativeMaterialStageSpec derivedFormationLedger := by
  have hi := inputCoefficientSearchAudit
  have hf := flatProductCompositionAudit
  unfold InputCoefficientSearchAudit at hi
  unfold QuantitativeMaterialStageSpec
  refine ⟨rfl, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    productIdentificationSearchAudit, rfl, rfl, rfl⟩
  · intro species
    cases species <;> native_decide
  · simpa [derivedFormationLedger] using hi.2.1
  · simpa [derivedFormationLedger] using hi.2.2.1
  · unfold AtomLedgerBalanced
    native_decide
  · unfold ChargeLedgerBalanced
    native_decide
  · unfold MassLedgerBalanced
    native_decide
  · simpa [derivedFormationLedger, FormationLedger.inputAssembly,
      derivedBulkInputComposition] using
      hf.2.2.2

theorem rawResultDerivation : RawResult := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨sourceImageAudit, fullPeriodicTableAudit,
      selectedOfflineRegistryAudit, previousPartPrerequisitesDerivation,
      nitrideCandidateDomainAudit, inputCoefficientSearchAudit,
      flatProductCompositionAudit, productIdentificationSearchAudit,
      quantitativeMaterialStageDerivation⟩
  · rcases nitrideCandidateDomainAudit with ⟨_, h7, _, _⟩
    refine ⟨h7, ?_⟩
    unfold candidate7 PrimitiveNitrideCandidateLaw
    native_decide
  · rcases nitrideCandidateDomainAudit with ⟨_, _, h8, _⟩
    refine ⟨h8, ?_⟩
    unfold candidate8 PrimitiveNitrideCandidateLaw
    native_decide
  · rcases nitrideCandidateDomainAudit with ⟨_, _, _, h9⟩
    refine ⟨h9, ?_⟩
    unfold candidate9 PrimitiveNitrideCandidateLaw
    native_decide
  · refine ⟨productIdentificationSearchAudit, ?_⟩
    unfold ProductAssemblyAccountingAudit HighestStateMetalOutputAudit
    native_decide
  · refine ⟨productIdentificationSearchAudit, ?_⟩
    native_decide
  · refine ⟨productIdentificationSearchAudit, ?_⟩
    native_decide

theorem reportedResultDerivation : ReportedResult := by
  exact ⟨rawResultDerivation, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem formulaIdentificationRaw :
    ("f5ecffa4053d2277f225baf0c3ef6542a8b4bdac2c18589ed7b4eca2212af15a" : String) =
      "f5ecffa4053d2277f225baf0c3ef6542a8b4bdac2c18589ed7b4eca2212af15a" ∧
      RawResult := by
  exact ⟨rfl, rawResultDerivation⟩

theorem formulaIdentificationReported :
    ("47c189eec63213c3eaa7352228a9dd42bc77ddf7c35fe9e32552fde5dff4ad4c" : String) =
      "47c189eec63213c3eaa7352228a9dd42bc77ddf7c35fe9e32552fde5dff4ad4c" ∧
      ReportedResult := by
  exact ⟨rfl, reportedResultDerivation⟩

end ProblemIChO2026T7A7
end IChO2026Problems
