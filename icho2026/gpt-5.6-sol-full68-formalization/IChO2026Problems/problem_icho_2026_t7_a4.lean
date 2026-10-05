import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T7-A4: removal of carbon dioxide by compound 3

The source depicts compound 3 as `(HOCH₂CH₂)₂NCH₃` and says that its aqueous
solution is used in the `Z` scrubber to remove `CO₂`.  The nitrogen bears two
hydroxyethyl groups and one methyl group, and no hydrogen, so the depicted
compound is a tertiary alkanolamine (N-methyldiethanolamine, MDEA).

The product-classification bridge is scoped to the following public chemistry
source, located without using any problem-specific search terms:

* P. M. M. Blauwhoff, G. F. Versteeg, and W. P. M. van Swaaij,
  "A study on the reaction between CO2 and alkanolamines in aqueous
  solutions", *Chemical Engineering Science* **39** (1984), 207--225,
  DOI `10.1016/0009-2509(84)80021-4`;
* stable URL: `https://doi.org/10.1016/0009-2509(84)80021-4`;
* open repository copy:
  `https://pure.rug.nl/ws/files/3410233/1984ChemEngSciBlauwhoff.pdf`;
* exact locator: journal p. 221, equation (26) and its immediately preceding
  paragraph;
* scoped claim: in water, a tertiary alkanolamine catalyses carbon-dioxide
  hydration, giving the protonated amine and bicarbonate.  The cited page
  explicitly reports this mechanism for TEA and MDEA.

No claim about equilibrium position, conversion, rate, or sole-product yield
is made here.  The requested equation does require stoichiometric
coefficients, so it is classified as a `quantitativeMaterialStage` for the
limited purpose of atom and charge accounting.  The primitive coefficients
are derived from the source/literature role pattern, atom conservation, charge
conservation, and a candidate-independent gcd normalization.
-/

namespace IChO2026Problems.ProblemIChO2026T7A4

open scoped BigOperators

/-! ## Source inventory and provenance -/

/-- Elements occurring in compound 3, the scrubbed gas, solvent, products, or
the two spectator gases printed around scrubber `Z`. -/
inductive Element where
  | carbon
  | hydrogen
  | nitrogen
  | oxygen
  deriving DecidableEq, Fintype, Repr

/-- Finite species domain used by the source-to-equation audit.  Nitrogen and
hydrogen retain the two unchanged gas-stream constituents from Fig. 1; proton
is the explicitly cancelled hydration/proton-transfer intermediate. -/
inductive Species where
  | compound3
  | carbonDioxide
  | water
  | proton
  | protonatedCompound3
  | bicarbonate
  | nitrogen
  | hydrogen
  deriving DecidableEq, Fintype, Repr

/-- Explicit enumeration of the closed species domain, used to evaluate the
finite atom and charge ledgers. -/
private theorem species_univ :
    (Finset.univ : Finset Species) =
      { .compound3, .carbonDioxide, .water, .proton,
        .protonatedCompound3, .bicarbonate, .nitrogen, .hydrogen } := by
  decide

/-- Permitted origins in the answer-blind candidate-domain policy. -/
inductive FactProvenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- Exact source locations used in this formalization. -/
inductive SourceLocator where
  | page1ScrubberInletLabel
  | page1ScrubberOutletLabel
  | page1ScrubberZLabel
  | page2RemovalSentence
  | page2Compound3Drawing
  | blauwhoffPage221Equation26
  deriving DecidableEq, Repr

/-- Every species has a source-bounded origin; there is no anonymous or
catch-all material stream. -/
structure SpeciesOrigin where
  provenance : FactProvenance
  locator : SourceLocator
  deriving DecidableEq, Repr

/-- Candidate-domain provenance fixed before solving the balance equations. -/
def speciesOrigin : Species → SpeciesOrigin
  | .compound3 => ⟨.problemImage, .page2Compound3Drawing⟩
  | .carbonDioxide => ⟨.problemText, .page2RemovalSentence⟩
  | .water => ⟨.problemText, .page2RemovalSentence⟩
  | .proton => ⟨.trustedGeneralLaw, .blauwhoffPage221Equation26⟩
  | .protonatedCompound3 =>
      ⟨.trustedGeneralLaw, .blauwhoffPage221Equation26⟩
  | .bicarbonate => ⟨.trustedGeneralLaw, .blauwhoffPage221Equation26⟩
  | .nitrogen => ⟨.problemImage, .page1ScrubberInletLabel⟩
  | .hydrogen => ⟨.problemImage, .page1ScrubberInletLabel⟩

/-- The equation uses coefficients and therefore activates the finite
species/atom/charge ledger, without asserting quantitative conversion. -/
inductive TransformationUse where
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

def targetTransformationUse : TransformationUse :=
  .quantitativeMaterialStage

/-! ## Visual recount of compound 3 -/

/-- Molecular formula over the four elements relevant here. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

namespace MolecularFormula

def add (a b : MolecularFormula) : MolecularFormula where
  carbon := a.carbon + b.carbon
  hydrogen := a.hydrogen + b.hydrogen
  nitrogen := a.nitrogen + b.nitrogen
  oxygen := a.oxygen + b.oxygen

def scale (n : ℕ) (a : MolecularFormula) : MolecularFormula where
  carbon := n * a.carbon
  hydrogen := n * a.hydrogen
  nitrogen := n * a.nitrogen
  oxygen := n * a.oxygen

end MolecularFormula

/-- One `HOCH₂CH₂-` substituent attached to nitrogen: `C₂H₅O`. -/
def hydroxyethylSubstituentFormula : MolecularFormula :=
  ⟨2, 5, 0, 1⟩

/-- One methyl substituent attached to nitrogen: `CH₃`. -/
def methylSubstituentFormula : MolecularFormula :=
  ⟨1, 3, 0, 0⟩

def nitrogenCenterFormula : MolecularFormula :=
  ⟨0, 0, 1, 0⟩

def hydrogenAtomFormula : MolecularFormula :=
  ⟨0, 1, 0, 0⟩

/-- Component ledger read directly from the drawing of compound 3.  The
`nitrogenHydrogens` field is zero because all three bonds from N terminate in
carbon substituents. -/
structure AmineDepictionLedger where
  hydroxyethylGroups : ℕ
  methylGroups : ℕ
  nitrogenCenters : ℕ
  nitrogenHydrogens : ℕ
  deriving DecidableEq, Repr

def compound3Depiction : AmineDepictionLedger where
  hydroxyethylGroups := 2
  methylGroups := 1
  nitrogenCenters := 1
  nitrogenHydrogens := 0

/-- Recombine every visually distinct component of the displayed molecule. -/
def formulaFromAmineDepiction
    (ledger : AmineDepictionLedger) : MolecularFormula :=
  MolecularFormula.add
    (MolecularFormula.scale ledger.hydroxyethylGroups
      hydroxyethylSubstituentFormula)
    (MolecularFormula.add
      (MolecularFormula.scale ledger.methylGroups methylSubstituentFormula)
      (MolecularFormula.add
        (MolecularFormula.scale ledger.nitrogenCenters nitrogenCenterFormula)
        (MolecularFormula.scale ledger.nitrogenHydrogens hydrogenAtomFormula)))

/-- Candidate-independent structural definition of a tertiary amine. -/
def IsTertiaryAmine (ledger : AmineDepictionLedger) : Prop :=
  ledger.nitrogenCenters = 1 ∧
    ledger.hydroxyethylGroups + ledger.methylGroups = 3 ∧
    ledger.nitrogenHydrogens = 0

/-- Named carrier for the image recount `2 C₂H₅O + CH₃ + N = C₅H₁₃NO₂`. -/
theorem compound3_formula_from_image :
    formulaFromAmineDepiction compound3Depiction = ⟨5, 13, 1, 2⟩ := by
  rfl

/-- The source drawing itself, rather than a candidate premise, establishes
that compound 3 belongs to the tertiary-amine class needed by the scoped
literature bridge. -/
theorem compound3_is_tertiary_amine :
    IsTertiaryAmine compound3Depiction := by
  norm_num [IsTertiaryAmine, compound3Depiction]

/-! ## Formula, atom, and charge ledgers -/

/-- Formula of every species in the closed material domain.  The formula of
the protonated absorbent is obtained by adding one H to the visually recounted
neutral molecule. -/
def molecularFormula : Species → MolecularFormula
  | .compound3 => formulaFromAmineDepiction compound3Depiction
  | .carbonDioxide => ⟨1, 0, 0, 2⟩
  | .water => ⟨0, 2, 0, 1⟩
  | .proton => ⟨0, 1, 0, 0⟩
  | .protonatedCompound3 =>
      MolecularFormula.add
        (formulaFromAmineDepiction compound3Depiction) hydrogenAtomFormula
  | .bicarbonate => ⟨1, 1, 0, 3⟩
  | .nitrogen => ⟨0, 0, 2, 0⟩
  | .hydrogen => ⟨0, 2, 0, 0⟩

/-- Atom count in one formula unit of a species. -/
def atomCount (species : Species) : Element → ℕ
  | .carbon => (molecularFormula species).carbon
  | .hydrogen => (molecularFormula species).hydrogen
  | .nitrogen => (molecularFormula species).nitrogen
  | .oxygen => (molecularFormula species).oxygen

/-- Formal charge in elementary-charge units. -/
def formalCharge : Species → ℤ
  | .proton => 1
  | .protonatedCompound3 => 1
  | .bicarbonate => -1
  | .compound3 | .carbonDioxide | .water | .nitrogen | .hydrogen => 0

/-- Total atom count on one side of a reaction. -/
def atomsInComplex (complex : CRNT.Complex Species) (element : Element) : ℕ :=
  ∑ species : Species, complex species * atomCount species element

/-- Total formal charge on one side of a reaction. -/
def chargeInComplex (complex : CRNT.Complex Species) : ℤ :=
  ∑ species : Species, (complex species : ℤ) * formalCharge species

def AtomBalanced (reaction : CRNT.Reaction Species) : Prop :=
  ∀ element : Element,
    atomsInComplex reaction.source element =
      atomsInComplex reaction.target element

def ChargeBalanced (reaction : CRNT.Reaction Species) : Prop :=
  chargeInComplex reaction.source = chargeInComplex reaction.target

/-! ## Source phase and scrubber context -/

inductive ReactionMedium where
  | aqueous
  deriving DecidableEq, Repr

/-- Figure 1 gives complete gas labels on the two sides of scrubber `Z`, while
the sentence above A4 supplies the aqueous absorbent and its solvent. -/
structure ScrubberContext where
  inletGasSpecies : Finset Species
  outletGasSpecies : Finset Species
  absorbentSolute : Species
  solvent : Species
  medium : ReactionMedium
  deriving DecidableEq

def problemContext : ScrubberContext where
  inletGasSpecies := { .nitrogen, .carbonDioxide, .hydrogen }
  outletGasSpecies := { .nitrogen, .hydrogen }
  absorbentSolute := .compound3
  solvent := .water
  medium := .aqueous

/-- Exact source-context carrier, independent of the candidate equation. -/
def MatchesSourceContext (context : ScrubberContext) : Prop :=
  context.inletGasSpecies = { .nitrogen, .carbonDioxide, .hydrogen } ∧
    context.outletGasSpecies = { .nitrogen, .hydrogen } ∧
    context.absorbentSolute = .compound3 ∧
    context.solvent = .water ∧
    context.medium = .aqueous

/-- A gas species is removed between the labeled inlet and outlet of `Z`. -/
def RemovedFromGasPhase (context : ScrubberContext) (species : Species) : Prop :=
  species ∈ context.inletGasSpecies ∧
    species ∉ context.outletGasSpecies

theorem source_scrubber_context :
    MatchesSourceContext problemContext ∧
      RemovedFromGasPhase problemContext .carbonDioxide := by
  simp [MatchesSourceContext, RemovedFromGasPhase, problemContext]

/-! ## Scoped public-literature bridge -/

/-- Machine-readable bibliographic carrier for the sole external chemistry
bridge used by this target. -/
structure LiteratureReference where
  title : String
  doi : String
  stableUrl : String
  repositoryUrl : String
  locator : String
  retrievedContentSha256 : String
  deriving DecidableEq, Repr

def blauwhoffReference : LiteratureReference where
  title := "A study on the reaction between CO2 and alkanolamines in aqueous solutions"
  doi := "10.1016/0009-2509(84)80021-4"
  stableUrl := "https://doi.org/10.1016/0009-2509(84)80021-4"
  repositoryUrl :=
    "https://pure.rug.nl/ws/files/3410233/1984ChemEngSciBlauwhoff.pdf"
  locator := "journal page 221, equation (26) and immediately preceding paragraph"
  retrievedContentSha256 :=
    "e58c1ebe505a47bcc5171436276a923edcb2ba84afa8c79339dacfc1705d0c61"

inductive AmineClass where
  | primary
  | secondary
  | tertiary
  deriving DecidableEq, Repr

/-- Abstract roles in the cited tertiary-amine hydration equation. -/
inductive HydrationRole where
  | neutralTertiaryAmine
  | carbonDioxide
  | water
  | protonatedTertiaryAmine
  | bicarbonate
  deriving DecidableEq, Fintype, Repr

inductive EquationSide where
  | reactant
  | product
  deriving DecidableEq, Repr

/-- A source-scoped claim records only the class, medium, and reaction-side
roles supported by the cited equation.  It does not assert a yield, rate,
equilibrium constant, or open-world inverse classification. -/
structure ScopedHydrationClaim where
  reference : LiteratureReference
  requiredAmineClass : AmineClass
  requiredMedium : ReactionMedium
  side : HydrationRole → EquationSide

def hydrationRoleSide : HydrationRole → EquationSide
  | .neutralTertiaryAmine | .carbonDioxide | .water => .reactant
  | .protonatedTertiaryAmine | .bicarbonate => .product

def blauwhoffHydrationClaim : ScopedHydrationClaim where
  reference := blauwhoffReference
  requiredAmineClass := .tertiary
  requiredMedium := .aqueous
  side := hydrationRoleSide

/-- Instantiation of each generic literature role by a species established
from the bound problem image/text. -/
def speciesForHydrationRole : HydrationRole → Species
  | .neutralTertiaryAmine => .compound3
  | .carbonDioxide => .carbonDioxide
  | .water => .water
  | .protonatedTertiaryAmine => .protonatedCompound3
  | .bicarbonate => .bicarbonate

/-- Every applicability condition of the scoped claim is bound to the current
source: the depicted amine is tertiary and the problem explicitly says its
solution is aqueous. -/
def ScopedHydrationClaimApplicable : Prop :=
  MatchesSourceContext problemContext ∧
    IsTertiaryAmine compound3Depiction ∧
    formalCharge .compound3 = 0 ∧
    blauwhoffHydrationClaim.reference = blauwhoffReference ∧
    blauwhoffHydrationClaim.requiredAmineClass = .tertiary ∧
    blauwhoffHydrationClaim.requiredMedium = problemContext.medium ∧
    blauwhoffHydrationClaim.side = hydrationRoleSide

theorem scoped_hydration_claim_applies :
    ScopedHydrationClaimApplicable := by
  exact ⟨source_scrubber_context.1, compound3_is_tertiary_amine,
    rfl, rfl, rfl, rfl, rfl⟩

/-- A concrete reaction respects the cited direction and all five generic
roles.  Positivity is required, but no coefficient is selected here. -/
def RespectsHydrationRoleClaim
    (claim : ScopedHydrationClaim) (reaction : CRNT.Reaction Species) : Prop :=
  ∀ role : HydrationRole,
    match claim.side role with
    | .reactant =>
        0 < reaction.source (speciesForHydrationRole role) ∧
          reaction.target (speciesForHydrationRole role) = 0
    | .product =>
        reaction.source (speciesForHydrationRole role) = 0 ∧
          0 < reaction.target (speciesForHydrationRole role)

/-! ## Candidate-independent balancing problem -/

/-- Unknown coefficients for the five literature-supported roles. -/
structure EquationCoefficients where
  compound3 : ℕ
  carbonDioxide : ℕ
  water : ℕ
  protonatedCompound3 : ℕ
  bicarbonate : ℕ
  deriving DecidableEq, Repr

/-- Construct a reaction from any coefficient tuple while leaving the proton
intermediate and the two gas spectators absent from the net equation. -/
def reactionFromCoefficients
    (coefficients : EquationCoefficients) : CRNT.Reaction Species where
  source
    | .compound3 => coefficients.compound3
    | .carbonDioxide => coefficients.carbonDioxide
    | .water => coefficients.water
    | .proton | .protonatedCompound3 | .bicarbonate | .nitrogen | .hydrogen => 0
  target
    | .protonatedCompound3 => coefficients.protonatedCompound3
    | .bicarbonate => coefficients.bicarbonate
    | .compound3 | .carbonDioxide | .water | .proton | .nitrogen | .hydrogen => 0

/-- Carbon, hydrogen, nitrogen, and oxygen ledgers obtained from the displayed
formula of compound 3 and the four ordinary molecular/ionic formulae. -/
def CoefficientAtomLedger (c : EquationCoefficients) : Prop :=
  5 * c.compound3 + c.carbonDioxide =
      5 * c.protonatedCompound3 + c.bicarbonate ∧
    13 * c.compound3 + 2 * c.water =
      14 * c.protonatedCompound3 + c.bicarbonate ∧
    c.compound3 = c.protonatedCompound3 ∧
    2 * c.compound3 + 2 * c.carbonDioxide + c.water =
      2 * c.protonatedCompound3 + 3 * c.bicarbonate

/-- The reactants are neutral and the product charges are `+1` and `-1`. -/
def CoefficientChargeLedger (c : EquationCoefficients) : Prop :=
  (0 : ℤ) = (c.protonatedCompound3 : ℤ) - (c.bicarbonate : ℤ)

/-- Positive, primitive whole-number normalization, imposed symmetrically by
the gcd rather than by preselecting any requested coefficient. -/
def PrimitivePositive (c : EquationCoefficients) : Prop :=
  0 < c.compound3 ∧
    0 < c.carbonDioxide ∧
    0 < c.water ∧
    0 < c.protonatedCompound3 ∧
    0 < c.bicarbonate ∧
    Nat.gcd c.compound3
      (Nat.gcd c.carbonDioxide
        (Nat.gcd c.water
          (Nat.gcd c.protonatedCompound3 c.bicarbonate))) = 1

def HydrationCoefficientSpec (c : EquationCoefficients) : Prop :=
  CoefficientAtomLedger c ∧
    CoefficientChargeLedger c ∧
    PrimitivePositive c

/-- The complete source-derived candidate specification.  The chemistry
authority fixes only the five roles and their sides; conservation and primitive
normalization decide their coefficients. -/
def SourceDerivedCoefficientSpec (c : EquationCoefficients) : Prop :=
  ScopedHydrationClaimApplicable ∧
    RespectsHydrationRoleClaim blauwhoffHydrationClaim
      (reactionFromCoefficients c) ∧
    HydrationCoefficientSpec c

/-- Candidate obtained by solving the coefficient ledgers. -/
def derivedCoefficients : EquationCoefficients where
  compound3 := 1
  carbonDioxide := 1
  water := 1
  protonatedCompound3 := 1
  bicarbonate := 1

/-- Concrete net reaction selected only after the candidate-independent
source, structure, role, balance, charge, and normalization constraints. -/
def carbonDioxideRemovalReaction : CRNT.Reaction Species :=
  reactionFromCoefficients derivedCoefficients

theorem coefficient_ledgers_match_reaction_balance
    (c : EquationCoefficients) :
    CoefficientAtomLedger c ↔ AtomBalanced (reactionFromCoefficients c) := by
  constructor
  · rintro ⟨hcarbon, hhydrogen, hnitrogen, hoxygen⟩ element
    cases element <;>
      simp [atomsInComplex, atomCount, molecularFormula,
        species_univ, reactionFromCoefficients, formulaFromAmineDepiction,
        compound3Depiction, MolecularFormula.add, MolecularFormula.scale,
        hydroxyethylSubstituentFormula, methylSubstituentFormula,
        nitrogenCenterFormula, hydrogenAtomFormula] <;>
      omega
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [atomsInComplex, atomCount, molecularFormula,
        species_univ, reactionFromCoefficients, formulaFromAmineDepiction,
        compound3Depiction, MolecularFormula.add, MolecularFormula.scale,
        hydroxyethylSubstituentFormula, methylSubstituentFormula,
        nitrogenCenterFormula, hydrogenAtomFormula, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using h .carbon
    · simpa [atomsInComplex, atomCount, molecularFormula,
        species_univ, reactionFromCoefficients, formulaFromAmineDepiction,
        compound3Depiction, MolecularFormula.add, MolecularFormula.scale,
        hydroxyethylSubstituentFormula, methylSubstituentFormula,
        nitrogenCenterFormula, hydrogenAtomFormula, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using h .hydrogen
    · simpa [atomsInComplex, atomCount, molecularFormula,
        species_univ, reactionFromCoefficients, formulaFromAmineDepiction,
        compound3Depiction, MolecularFormula.add, MolecularFormula.scale,
        hydroxyethylSubstituentFormula, methylSubstituentFormula,
        nitrogenCenterFormula, hydrogenAtomFormula, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using h .nitrogen
    · simpa [atomsInComplex, atomCount, molecularFormula,
        species_univ, reactionFromCoefficients, formulaFromAmineDepiction,
        compound3Depiction, MolecularFormula.add, MolecularFormula.scale,
        hydroxyethylSubstituentFormula, methylSubstituentFormula,
        nitrogenCenterFormula, hydrogenAtomFormula, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using h .oxygen

theorem coefficient_charge_matches_reaction_balance
    (c : EquationCoefficients) :
    CoefficientChargeLedger c ↔ ChargeBalanced (reactionFromCoefficients c) := by
  simp [CoefficientChargeLedger, ChargeBalanced, chargeInComplex,
    species_univ, reactionFromCoefficients, formalCharge, sub_eq_add_neg]

theorem derived_coefficients_spec :
    SourceDerivedCoefficientSpec derivedCoefficients := by
  refine ⟨scoped_hydration_claim_applies, ?_, ?_⟩
  · intro role
    cases role <;>
      norm_num [blauwhoffHydrationClaim, hydrationRoleSide,
        reactionFromCoefficients, derivedCoefficients,
        speciesForHydrationRole]
  · refine ⟨?_, ?_, ?_⟩
    · norm_num [CoefficientAtomLedger, derivedCoefficients]
    · norm_num [CoefficientChargeLedger, derivedCoefficients]
    · norm_num [PrimitivePositive, derivedCoefficients]

/-- Uniqueness is only within the finite, source/literature-supported role
domain; it is not an open-world claim about every possible aqueous process. -/
theorem hydration_coefficients_unique
    (c : EquationCoefficients)
    (h : SourceDerivedCoefficientSpec c) :
    c = derivedCoefficients := by
  rcases c with ⟨a, b, w, d, e⟩
  rcases h with ⟨_, _, ⟨hatoms, hcharge, hpositive⟩⟩
  rcases hatoms with ⟨hcarbon, hhydrogen, hnitrogen, _⟩
  rcases hpositive with ⟨_, _, _, _, _, hgcd⟩
  change 5 * a + b = 5 * d + e at hcarbon
  change 13 * a + 2 * w = 14 * d + e at hhydrogen
  change a = d at hnitrogen
  change (0 : ℤ) = (d : ℤ) - (e : ℤ) at hcharge
  have hde : d = e := by omega
  have hba : b = a := by omega
  have hwa : w = a := by omega
  have hda : d = a := hnitrogen.symm
  have hea : e = a := by omega
  have ha : a = 1 := by
    simpa [hba, hwa, hda, hea] using hgcd
  subst a
  subst b
  subst w
  subst d
  subst e
  rfl

/-! ## Proton-transfer derivation and cancellation -/

/-- `CO₂ + H₂O ⟶ HCO₃⁻ + H⁺`, the hydration bookkeeping step. -/
def carbonDioxideHydrationStep : CRNT.Reaction Species where
  source
    | .carbonDioxide | .water => 1
    | _ => 0
  target
    | .bicarbonate | .proton => 1
    | _ => 0

/-- `(HOCH₂CH₂)₂NCH₃ + H⁺ ⟶ [(HOCH₂CH₂)₂NHCH₃]⁺`. -/
def compound3ProtonationStep : CRNT.Reaction Species where
  source
    | .compound3 | .proton => 1
    | _ => 0
  target
    | .protonatedCompound3 => 1
    | _ => 0

/-- The one proton appearing on both sides after the two steps are added. -/
def protonCancellationComplex : CRNT.Complex Species
  | .proton => 1
  | _ => 0

def combinedStepSource : CRNT.Complex Species :=
  CRNT.Complex.add carbonDioxideHydrationStep.source
    compound3ProtonationStep.source

def combinedStepTarget : CRNT.Complex Species :=
  CRNT.Complex.add carbonDioxideHydrationStep.target
    compound3ProtonationStep.target

/-- Adding the two literature-supported bookkeeping steps gives the requested
net equation plus the same proton complex on both sides. -/
def ProtonCancellationSpec : Prop :=
  combinedStepSource =
      CRNT.Complex.add carbonDioxideRemovalReaction.source
        protonCancellationComplex ∧
    combinedStepTarget =
      CRNT.Complex.add carbonDioxideRemovalReaction.target
        protonCancellationComplex

def MechanismLedgerSpec : Prop :=
  AtomBalanced carbonDioxideHydrationStep ∧
    ChargeBalanced carbonDioxideHydrationStep ∧
    AtomBalanced compound3ProtonationStep ∧
    ChargeBalanced compound3ProtonationStep ∧
    ProtonCancellationSpec

theorem mechanism_ledgers_and_cancellation :
    MechanismLedgerSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro element
    cases element <;>
      simp [atomsInComplex, species_univ, atomCount, molecularFormula,
        carbonDioxideHydrationStep, formulaFromAmineDepiction,
        compound3Depiction, MolecularFormula.add, MolecularFormula.scale,
        hydroxyethylSubstituentFormula, methylSubstituentFormula,
        nitrogenCenterFormula, hydrogenAtomFormula]
  · simp [ChargeBalanced, chargeInComplex, species_univ,
      carbonDioxideHydrationStep, formalCharge]
  · intro element
    cases element <;>
      simp [atomsInComplex, species_univ, atomCount, molecularFormula,
        compound3ProtonationStep, formulaFromAmineDepiction,
        compound3Depiction, MolecularFormula.add, MolecularFormula.scale,
        hydroxyethylSubstituentFormula, methylSubstituentFormula,
        nitrogenCenterFormula, hydrogenAtomFormula]
  · simp [ChargeBalanced, chargeInComplex, species_univ,
      compound3ProtonationStep, formalCharge]
  · constructor <;> funext species <;> cases species <;> rfl

/-! ## Raw and exact-symbolic reported outputs -/

/-- Coefficient-by-coefficient meaning of the displayed equation, including
absence of the cancelled proton and the two unchanged gas spectators. -/
def HasDisplayedReactionEquation (reaction : CRNT.Reaction Species) : Prop :=
  reaction.source .compound3 = 1 ∧
    reaction.source .carbonDioxide = 1 ∧
    reaction.source .water = 1 ∧
    reaction.source .proton = 0 ∧
    reaction.source .protonatedCompound3 = 0 ∧
    reaction.source .bicarbonate = 0 ∧
    reaction.source .nitrogen = 0 ∧
    reaction.source .hydrogen = 0 ∧
    reaction.target .compound3 = 0 ∧
    reaction.target .carbonDioxide = 0 ∧
    reaction.target .water = 0 ∧
    reaction.target .proton = 0 ∧
    reaction.target .protonatedCompound3 = 1 ∧
    reaction.target .bicarbonate = 1 ∧
    reaction.target .nitrogen = 0 ∧
    reaction.target .hydrogen = 0

/-- Human-readable rendering of the structured reaction carrier. -/
def reactionEquationDisplay : String :=
  "(HOCH₂CH₂)₂NCH₃ + CO₂ + H₂O → [(HOCH₂CH₂)₂NHCH₃]⁺ + HCO₃⁻"

/-- Raw exact-symbolic result: all source facts and applicability conditions,
the solved primitive coefficient specification, its scoped uniqueness, and the
independent atom/charge/cancellation ledgers. -/
def ReactionEquationRawResult : Prop :=
  targetTransformationUse = .quantitativeMaterialStage ∧
    MatchesSourceContext problemContext ∧
    RemovedFromGasPhase problemContext .carbonDioxide ∧
    formulaFromAmineDepiction compound3Depiction = ⟨5, 13, 1, 2⟩ ∧
    IsTertiaryAmine compound3Depiction ∧
    ScopedHydrationClaimApplicable ∧
    SourceDerivedCoefficientSpec derivedCoefficients ∧
    (∀ c : EquationCoefficients,
      SourceDerivedCoefficientSpec c → c = derivedCoefficients) ∧
    MechanismLedgerSpec ∧
    AtomBalanced carbonDioxideRemovalReaction ∧
    ChargeBalanced carbonDioxideRemovalReaction

/-- Exact reporting adds the full displayed coefficient ledger.  There is no
rounding layer for a symbolic chemical equation. -/
def ReactionEquationReportedResult : Prop :=
  ReactionEquationRawResult ∧
    HasDisplayedReactionEquation carbonDioxideRemovalReaction

/-- Raw answer-blind Lean carrier for requested output `reaction_equation`. -/
theorem reaction_equation_raw_result :
    ReactionEquationRawResult := by
  refine ⟨rfl, source_scrubber_context.1, source_scrubber_context.2,
    compound3_formula_from_image, compound3_is_tertiary_amine,
    scoped_hydration_claim_applies, derived_coefficients_spec, ?_,
    mechanism_ledgers_and_cancellation, ?_, ?_⟩
  · intro c hc
    exact hydration_coefficients_unique c hc
  · rw [carbonDioxideRemovalReaction]
    exact (coefficient_ledgers_match_reaction_balance derivedCoefficients).mp
      derived_coefficients_spec.2.2.1
  · rw [carbonDioxideRemovalReaction]
    exact (coefficient_charge_matches_reaction_balance derivedCoefficients).mp
      derived_coefficients_spec.2.2.2.1

/-- Reported exact-symbolic Lean carrier for requested output
`reaction_equation`. -/
theorem reaction_equation_reported_result :
    ReactionEquationReportedResult := by
  refine ⟨reaction_equation_raw_result, ?_⟩
  norm_num [HasDisplayedReactionEquation, carbonDioxideRemovalReaction,
    reactionFromCoefficients, derivedCoefficients]

end IChO2026Problems.ProblemIChO2026T7A4
