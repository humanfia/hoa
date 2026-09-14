import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T1-A1: identification of X and Y

This file formalizes the student-visible table and the two qualitative
observations used in subquestion 1.1.  The submitted objects are labelled
`gpt_corrected_kimi_draft`: the compound numbers and names in the supplied
Kimi draft are retained, while the auxiliary SMILES for Y is corrected to the
connectivity drawn for compound 3.

The molecular graphs below contain heavy atoms explicitly and recover the
hydrogen count by ordinary valence completion.  The acid transformation is
used only as a qualitative named-transform compatibility constraint; no yield,
completion, sole-product, phase, or material-balance claim is made.
-/

namespace IChO2026Problems
namespace Icho2026T1A1

/-! ## Student-visible table -/

/-- The four plant rows printed in the table on page Q1-2. -/
inductive Plant where
  | zingiber
  | hypericum
  | chamomilla
  | artemisia
  deriving DecidableEq, Fintype, Repr

/-- The ten numbered compounds printed in the table. -/
inductive TableCompound where
  | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10
  deriving DecidableEq, Fintype, Repr

/-- Molecular formula fields needed by this table.  Every printed formula in
T1-A1 contains only carbon, hydrogen, and oxygen. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

/-- The common formula of compounds 2, 3, 6, and 10. -/
def c10h18o : MolecularFormula := ⟨10, 18, 1⟩

/-- The formula printed beneath each numbered structure. -/
def tableFormula : TableCompound → MolecularFormula
  | .c1 => ⟨11, 14, 3⟩
  | .c2 => c10h18o
  | .c3 => c10h18o
  | .c4 => ⟨6, 12, 1⟩
  | .c5 => ⟨10, 12, 2⟩
  | .c6 => c10h18o
  | .c7 => ⟨14, 16, 0⟩
  | .c8 => ⟨15, 24, 0⟩
  | .c9 => ⟨10, 16, 1⟩
  | .c10 => c10h18o

/-- Human-facing number printed below a table compound. -/
def tableNumber : TableCompound → ℕ
  | .c1 => 1
  | .c2 => 2
  | .c3 => 3
  | .c4 => 4
  | .c5 => 5
  | .c6 => 6
  | .c7 => 7
  | .c8 => 8
  | .c9 => 9
  | .c10 => 10

/-- The extraction rows, including the three occurrences of compound 3. -/
def extractableCompounds : Plant → Finset TableCompound
  | .zingiber => {.c1, .c2, .c3}
  | .hypericum => {.c4, .c5, .c6}
  | .chamomilla => {.c7, .c8, .c3}
  | .artemisia => {.c9, .c10, .c3}

/-- A numbered compound occurs in at least one row of the printed table. -/
def AppearsInTable (c : TableCompound) : Prop :=
  ∃ p : Plant, c ∈ extractableCompounds p

/-- Formula conservation for two distinct isomers restricts both table entries
to the only repeated printed formula.  This is the finite domain used below;
it is not a candidate-named singleton. -/
def repeatedFormulaDomain : Finset TableCompound :=
  {.c2, .c3, .c6, .c10}

theorem distinct_same_formula_domain
    {x y : TableCompound}
    (hxy : x ≠ y)
    (hformula : tableFormula x = tableFormula y) :
    x ∈ repeatedFormulaDomain ∧ y ∈ repeatedFormulaDomain := by
  cases x <;> cases y <;>
    simp_all [tableFormula, c10h18o, repeatedFormulaDomain]

/-- Roles of the four chromatographically distinct elixir constituents. -/
inductive ElixirRole where
  | x | y | z | w
  deriving DecidableEq, Fintype, Repr

/-- The source says the four roles denote four different substances. -/
structure ElixirAssignment where
  compound : ElixirRole → TableCompound
  distinct : Function.Injective compound

/-! ## Heavy-atom connectivity and formula audit -/

inductive HeavyElement where
  | carbon
  | oxygen
  deriving DecidableEq, BEq, Repr

def HeavyElement.standardValence : HeavyElement → ℕ
  | .carbon => 4
  | .oxygen => 2

inductive BondOrder where
  | single
  | double
  deriving DecidableEq, Repr

def BondOrder.valence : BondOrder → ℕ
  | .single => 1
  | .double => 2

/-- Bonds are stored once, with their smaller endpoint first. -/
structure Bond where
  left : ℕ
  right : ℕ
  order : BondOrder
  deriving DecidableEq, Repr

def singleBond (i j : ℕ) : Bond :=
  ⟨min i j, max i j, .single⟩

def doubleBond (i j : ℕ) : Bond :=
  ⟨min i j, max i j, .double⟩

/-- A finite heavy-atom molecular graph.  Hydrogens are implicit and are
recovered from the standard valences above. -/
structure HeavyAtomGraph where
  atoms : List HeavyElement
  bonds : List Bond
  deriving DecidableEq, Repr

def HeavyAtomGraph.HasBond
    (g : HeavyAtomGraph) (i j : ℕ) (order : BondOrder) : Prop :=
  (⟨min i j, max i j, order⟩ : Bond) ∈ g.bonds

def HeavyAtomGraph.bondValenceAt (g : HeavyAtomGraph) (i : ℕ) : ℕ :=
  (g.bonds.map fun b =>
    if b.left = i ∨ b.right = i then b.order.valence else 0).sum

def HeavyAtomGraph.atomValenceAt (g : HeavyAtomGraph) (i : ℕ) : ℕ :=
  match g.atoms[i]? with
  | some e => e.standardValence
  | none => 0

/-- Hydrogens required to complete all heavy-atom valences. -/
def HeavyAtomGraph.implicitHydrogenCount (g : HeavyAtomGraph) : ℕ :=
  ((List.range g.atoms.length).map fun i =>
    g.atomValenceAt i - g.bondValenceAt i).sum

/-- Basic well-formedness of a source-read heavy-atom graph. -/
def HeavyAtomGraph.Valid (g : HeavyAtomGraph) : Prop :=
  g.bonds.Nodup ∧
  (∀ b ∈ g.bonds,
    b.left < b.right ∧ b.right < g.atoms.length) ∧
  (∀ i, i < g.atoms.length →
    g.bondValenceAt i ≤ g.atomValenceAt i)

/-- A heavy-atom graph realizes a formula when its explicit C/O inventory and
its valence-completed H inventory agree with the formula. -/
def HeavyAtomGraph.RealizesFormula
    (g : HeavyAtomGraph) (f : MolecularFormula) : Prop :=
  g.atoms.count .carbon = f.carbon ∧
  g.atoms.count .oxygen = f.oxygen ∧
  g.implicitHydrogenCount = f.hydrogen

def c10oHeavyAtoms : List HeavyElement :=
  List.replicate 10 .carbon ++ [.oxygen]

/-!
The linalool indices follow the chain
`C1=C2-C3(OH)(Me)-C4-C5-C6=C7(Me)2`; oxygen is atom 10.
-/
structure CyclizationRoles where
  c1 : ℕ
  c2 : ℕ
  alcoholCenter : ℕ
  c4 : ℕ
  c5 : ℕ
  c6 : ℕ
  gemCarbon : ℕ
  gemMethylOne : ℕ
  alcoholMethyl : ℕ
  gemMethylTwo : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

def CyclizationRoles.asList (r : CyclizationRoles) : List ℕ :=
  [r.c1, r.c2, r.alcoholCenter, r.c4, r.c5, r.c6,
    r.gemCarbon, r.gemMethylOne, r.alcoholMethyl,
    r.gemMethylTwo, r.oxygen]

def linaloolRoles : CyclizationRoles :=
  ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10⟩

/-- Connectivity pattern read from the acyclic structure numbered 6. -/
def linaloolPatternBonds (r : CyclizationRoles) : List Bond :=
  [ doubleBond r.c1 r.c2,
    singleBond r.c2 r.alcoholCenter,
    singleBond r.alcoholCenter r.c4,
    singleBond r.c4 r.c5,
    singleBond r.c5 r.c6,
    doubleBond r.c6 r.gemCarbon,
    singleBond r.gemCarbon r.gemMethylOne,
    singleBond r.alcoholCenter r.alcoholMethyl,
    singleBond r.gemCarbon r.gemMethylTwo,
    singleBond r.alcoholCenter r.oxygen ]

/-- Connectivity pattern after the two ring closures: C1--C6 and O--C7.
This is the depicted 1,8-cineole graph, with oxygen adjacent to the
methyl-bearing bridgehead and to the gem-dimethyl carbon. -/
def cineolePatternBonds (r : CyclizationRoles) : List Bond :=
  [ singleBond r.c1 r.c2,
    singleBond r.c2 r.alcoholCenter,
    singleBond r.alcoholCenter r.c4,
    singleBond r.c4 r.c5,
    singleBond r.c5 r.c6,
    singleBond r.c6 r.gemCarbon,
    singleBond r.gemCarbon r.gemMethylOne,
    singleBond r.alcoholCenter r.alcoholMethyl,
    singleBond r.gemCarbon r.gemMethylTwo,
    singleBond r.alcoholCenter r.oxygen,
    singleBond r.c1 r.c6,
    singleBond r.gemCarbon r.oxygen ]

/-- Compound 6 as read directly from the source drawing. -/
def linaloolGraph : HeavyAtomGraph :=
  ⟨c10oHeavyAtoms, linaloolPatternBonds linaloolRoles⟩

/-- Compound 3 as read directly from the source drawing. -/
def correctedCineoleGraph : HeavyAtomGraph :=
  ⟨c10oHeavyAtoms, cineolePatternBonds linaloolRoles⟩

theorem linalool_graph_valid : linaloolGraph.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · simp [linaloolGraph, linaloolPatternBonds, linaloolRoles,
      singleBond, doubleBond, c10oHeavyAtoms]
  · intro i hi
    simp [linaloolGraph, c10oHeavyAtoms] at hi
    interval_cases i <;>
      decide

theorem corrected_cineole_graph_valid : correctedCineoleGraph.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · simp [correctedCineoleGraph, cineolePatternBonds, linaloolRoles,
      singleBond, c10oHeavyAtoms]
  · intro i hi
    simp [correctedCineoleGraph, c10oHeavyAtoms] at hi
    interval_cases i <;>
      decide

theorem linalool_formula_audit :
    linaloolGraph.RealizesFormula c10h18o := by
  unfold HeavyAtomGraph.RealizesFormula
  decide

theorem corrected_cineole_formula_audit :
    correctedCineoleGraph.RealizesFormula c10h18o := by
  unfold HeavyAtomGraph.RealizesFormula
  decide

/-- Named carrier for the complete compound-6 panel used by the X output. -/
def Compound6ImageCarrier : Prop :=
  tableNumber .c6 = 6 ∧
  tableFormula .c6 = c10h18o ∧
  linaloolGraph.atoms = c10oHeavyAtoms ∧
  linaloolGraph.bonds = linaloolPatternBonds linaloolRoles ∧
  linaloolGraph.Valid ∧
  linaloolGraph.RealizesFormula c10h18o

/-- Named carrier for the complete compound-3 panel used by the Y output. -/
def Compound3ImageCarrier : Prop :=
  tableNumber .c3 = 3 ∧
  tableFormula .c3 = c10h18o ∧
  correctedCineoleGraph.atoms = c10oHeavyAtoms ∧
  correctedCineoleGraph.bonds = cineolePatternBonds linaloolRoles ∧
  correctedCineoleGraph.Valid ∧
  correctedCineoleGraph.RealizesFormula c10h18o

theorem compound6_image_carrier : Compound6ImageCarrier := by
  exact ⟨rfl, rfl, rfl, rfl, linalool_graph_valid,
    linalool_formula_audit⟩

theorem compound3_image_carrier : Compound3ImageCarrier := by
  exact ⟨rfl, rfl, rfl, rfl, corrected_cineole_graph_valid,
    corrected_cineole_formula_audit⟩

/-! ## Authorized correction of the auxiliary Y SMILES -/

/-- The exact auxiliary string in the sealed Kimi draft.  It is retained for
the correction audit and is not used as a source premise. -/
def frozenDraftYSmiles : String :=
  "CC12CCC(CC1)OC2(C)C"

/-- Corrected auxiliary string whose connectivity is compound 3 as drawn. -/
def correctedYSmiles : String :=
  "CC12CCC(CC1)C(C)(C)O2"

/-- Bonds common to the frozen-string graph and the corrected graph.  In these
indices, atom 2 is the methyl-bearing bridgehead, atom 5 the other bridgehead,
atom 6 the gem-dimethyl carbon, and atom 10 oxygen. -/
def yCommonBonds : List Bond :=
  [ singleBond 0 1,
    singleBond 1 2,
    singleBond 2 3,
    singleBond 3 4,
    singleBond 4 5,
    singleBond 0 5,
    singleBond 2 8,
    singleBond 6 7,
    singleBond 6 9,
    singleBond 6 10 ]

/-- Connectivity actually encoded by the frozen draft string. -/
def frozenDraftYSmilesGraph : HeavyAtomGraph :=
  ⟨c10oHeavyAtoms,
    yCommonBonds ++ [singleBond 2 6, singleBond 5 10]⟩

/-- The complete exact graph discrepancy authorized for correction: the
frozen string attaches bridgehead 2 to gem carbon 6 and bridgehead 5 to O;
the drawing instead attaches bridgehead 2 to O and bridgehead 5 to carbon 6.
All bonds in `yCommonBonds` are unchanged. -/
def YConnectivityCorrection : Prop :=
  frozenDraftYSmilesGraph.bonds =
      yCommonBonds ++ [singleBond 2 6, singleBond 5 10] ∧
  correctedCineoleGraph.bonds.Perm
      (yCommonBonds ++ [singleBond 2 10, singleBond 5 6]) ∧
  frozenDraftYSmilesGraph.HasBond 2 6 .single ∧
  frozenDraftYSmilesGraph.HasBond 5 10 .single ∧
  ¬ frozenDraftYSmilesGraph.HasBond 2 10 .single ∧
  ¬ frozenDraftYSmilesGraph.HasBond 5 6 .single ∧
  correctedCineoleGraph.HasBond 2 10 .single ∧
  correctedCineoleGraph.HasBond 5 6 .single ∧
  ¬ correctedCineoleGraph.HasBond 2 6 .single ∧
  ¬ correctedCineoleGraph.HasBond 5 10 .single

theorem y_connectivity_correction_exact : YConnectivityCorrection := by
  unfold YConnectivityCorrection HeavyAtomGraph.HasBond
  decide

theorem corrected_smiles_is_not_frozen_smiles :
    correctedYSmiles ≠ frozenDraftYSmiles := by
  decide

/-! ## Plane of symmetry -/

/-- A graph-level carrier for the source's molecular mirror-plane statement.
It is an involution preserving atom labels and bond orders, and it must
actually exchange at least one pair of atoms. -/
def IsCombinatorialMirrorPlane
    (g : HeavyAtomGraph) (reflect : ℕ → ℕ) : Prop :=
  (∀ i, i < g.atoms.length → reflect i < g.atoms.length) ∧
  (∀ i, i < g.atoms.length → reflect (reflect i) = i) ∧
  (∀ i, i < g.atoms.length → g.atoms[i]? = g.atoms[reflect i]?) ∧
  (∀ i j, i < g.atoms.length → j < g.atoms.length →
    ∀ order : BondOrder,
      g.HasBond i j order ↔ g.HasBond (reflect i) (reflect j) order) ∧
  (∃ i, i < g.atoms.length ∧ reflect i ≠ i)

/-- Reflection of the two ethylene bridges and the two gem methyl groups in
compound 3.  Atoms 2, 5, 6, 8, and 10 lie in the combinatorial fixed set. -/
def cineoleReflection : ℕ → ℕ
  | 0 => 4
  | 4 => 0
  | 1 => 3
  | 3 => 1
  | 7 => 9
  | 9 => 7
  | i => i

def HeavyAtomGraph.HasMirrorPlane (g : HeavyAtomGraph) : Prop :=
  ∃ reflect : ℕ → ℕ, IsCombinatorialMirrorPlane g reflect

theorem corrected_cineole_mirror_plane :
    IsCombinatorialMirrorPlane correctedCineoleGraph cineoleReflection := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i < 11 := by
      simpa [correctedCineoleGraph, c10oHeavyAtoms] using hi
    have hreflect : cineoleReflection i < 11 := by
      interval_cases i <;> decide
    simpa [correctedCineoleGraph, c10oHeavyAtoms] using hreflect
  · intro i hi
    simp [correctedCineoleGraph, c10oHeavyAtoms] at hi
    interval_cases i <;> decide
  · intro i hi
    simp [correctedCineoleGraph, c10oHeavyAtoms] at hi
    interval_cases i <;> decide
  · intro i j hi hj order
    unfold HeavyAtomGraph.HasBond
    simp [correctedCineoleGraph, c10oHeavyAtoms] at hi hj
    interval_cases i <;> interval_cases j <;> cases order <;>
      decide
  · exact ⟨0, by decide, by decide⟩

/-! ## Qualitative acid-cycloisomerization compatibility -/

/-- The source transformation is not used quantitatively. -/
inductive StagedTransformationClass where
  | qualitative_named_transform_only
  deriving DecidableEq, Repr

/-- Named structural stages used only to audit the direction and connectivity
of the candidate transformation. -/
inductive AcidCyclizationStage where
  | allylicAlcoholActivation
  | sixMemberedCarbonRingClosure
  | waterCapture
  | alkeneActivation
  | intramolecularEtherClosure
  | catalystRegeneration
  deriving DecidableEq, Repr

def qualitativeAcidStages : List AcidCyclizationStage :=
  [.allylicAlcoholActivation,
   .sixMemberedCarbonRingClosure,
   .waterCapture,
   .alkeneActivation,
   .intramolecularEtherClosure,
   .catalystRegeneration]

/-- A non-exclusive structural compatibility certificate for the explicit
source statement that X can isomerize to Y in acidic medium.  It records atom
retention, the complete source and target heavy-atom patterns, formula
conservation, and direction.  It intentionally has no fields for yield,
completion, phases, byproducts, or absence of other products. -/
structure QualitativeAcidCycloisomerizationCertificate
    (source target : HeavyAtomGraph) where
  classification : StagedTransformationClass
  classification_eq :
    classification = .qualitative_named_transform_only
  roles : CyclizationRoles
  rolesCoverSource : roles.asList.Perm (List.range source.atoms.length)
  sameHeavyAtoms : source.atoms = target.atoms
  sourceValid : source.Valid
  targetValid : target.Valid
  sourceFormula : source.RealizesFormula c10h18o
  targetFormula : target.RealizesFormula c10h18o
  sourceConnectivity : source.bonds.Perm (linaloolPatternBonds roles)
  targetConnectivity : target.bonds.Perm (cineolePatternBonds roles)
  stages : List AcidCyclizationStage
  stages_eq : stages = qualitativeAcidStages

theorem linalool_to_corrected_cineole_qualitative_compatibility :
    Nonempty
      (QualitativeAcidCycloisomerizationCertificate
        linaloolGraph correctedCineoleGraph) := by
  refine ⟨{
    classification := .qualitative_named_transform_only
    classification_eq := rfl
    roles := linaloolRoles
    rolesCoverSource := by decide
    sameHeavyAtoms := rfl
    sourceValid := linalool_graph_valid
    targetValid := corrected_cineole_graph_valid
    sourceFormula := linalool_formula_audit
    targetFormula := corrected_cineole_formula_audit
    sourceConnectivity := List.Perm.refl _
    targetConnectivity := List.Perm.refl _
    stages := qualitativeAcidStages
    stages_eq := rfl
  }⟩

/-! ## Submitted exact symbolic identifications -/

/-- Required label for this isolated authorized-correction rerun. -/
inductive EvaluationBasis where
  | gpt_corrected_kimi_draft
  deriving DecidableEq, Repr

/-- A concrete identification plus its auditable molecular carrier. -/
structure IdentificationOutput where
  basis : EvaluationBasis
  role : ElixirRole
  compound : TableCompound
  number : ℕ
  commonName : String
  systematicName : String
  formula : MolecularFormula
  auxiliarySmiles : String
  graph : HeavyAtomGraph
  deriving DecidableEq, Repr

def IdentificationOutput.WellFormed (out : IdentificationOutput) : Prop :=
  out.basis = .gpt_corrected_kimi_draft ∧
  out.number = tableNumber out.compound ∧
  out.formula = tableFormula out.compound ∧
  AppearsInTable out.compound ∧
  out.graph.Valid ∧
  out.graph.RealizesFormula out.formula

/-- Unchanged X output from the supplied draft. -/
def identityXOutput : IdentificationOutput where
  basis := .gpt_corrected_kimi_draft
  role := .x
  compound := .c6
  number := 6
  commonName := "linalool"
  systematicName := "3,7-dimethylocta-1,6-dien-3-ol"
  formula := c10h18o
  auxiliarySmiles := "C=CC(C)(O)CCC=C(C)C"
  graph := linaloolGraph

/-- Y output with the authorized corrected auxiliary connectivity. -/
def identityYOutput : IdentificationOutput where
  basis := .gpt_corrected_kimi_draft
  role := .y
  compound := .c3
  number := 3
  commonName := "1,8-cineole (eucalyptol)"
  systematicName := "1,3,3-trimethyl-2-oxabicyclo[2.2.2]octane"
  formula := c10h18o
  auxiliarySmiles := correctedYSmiles
  graph := correctedCineoleGraph

/-- Joint source-side specification checked by the candidate pair. -/
def CandidatePairMeetsSourceConstraints
    (x y : IdentificationOutput) : Prop :=
  x.role = .x ∧
  y.role = .y ∧
  x.WellFormed ∧
  y.WellFormed ∧
  x.compound ≠ y.compound ∧
  x.compound ∈ repeatedFormulaDomain ∧
  y.compound ∈ repeatedFormulaDomain ∧
  x.formula = y.formula ∧
  Nonempty (QualitativeAcidCycloisomerizationCertificate x.graph y.graph) ∧
  y.graph.HasMirrorPlane

theorem submitted_pair_meets_source_constraints :
    CandidatePairMeetsSourceConstraints identityXOutput identityYOutput := by
  have hxAppears : AppearsInTable .c6 :=
    ⟨.hypericum, by simp [extractableCompounds]⟩
  have hyAppears : AppearsInTable .c3 :=
    ⟨.zingiber, by simp [extractableCompounds]⟩
  have hxWellFormed : identityXOutput.WellFormed := by
    exact ⟨rfl, rfl, rfl, hxAppears, linalool_graph_valid,
      linalool_formula_audit⟩
  have hyWellFormed : identityYOutput.WellFormed := by
    exact ⟨rfl, rfl, rfl, hyAppears, corrected_cineole_graph_valid,
      corrected_cineole_formula_audit⟩
  exact ⟨rfl, rfl, hxWellFormed, hyWellFormed, by decide,
    by decide, by decide, rfl,
    linalool_to_corrected_cineole_qualitative_compatibility,
    ⟨cineoleReflection, corrected_cineole_mirror_plane⟩⟩

/-- Raw semantic carrier for requested output `identity_x`. -/
def IdentityXRawResult : Prop :=
  identityXOutput.basis = .gpt_corrected_kimi_draft ∧
  identityXOutput.role = .x ∧
  identityXOutput.compound = .c6 ∧
  identityXOutput.number = 6 ∧
  identityXOutput.commonName = "linalool" ∧
  Compound6ImageCarrier ∧
  CandidatePairMeetsSourceConstraints identityXOutput identityYOutput

/-- Raw semantic carrier for requested output `identity_y`. -/
def IdentityYRawResult : Prop :=
  identityYOutput.basis = .gpt_corrected_kimi_draft ∧
  identityYOutput.role = .y ∧
  identityYOutput.compound = .c3 ∧
  identityYOutput.number = 3 ∧
  identityYOutput.commonName = "1,8-cineole (eucalyptol)" ∧
  identityYOutput.auxiliarySmiles = correctedYSmiles ∧
  Compound3ImageCarrier ∧
  CandidatePairMeetsSourceConstraints identityXOutput identityYOutput ∧
  YConnectivityCorrection

def identityXDisplay : String :=
  "gpt_corrected_kimi_draft: compound 6, linalool"

def identityYDisplay : String :=
  "gpt_corrected_kimi_draft: compound 3, 1,8-cineole (eucalyptol); \
   corrected SMILES CC12CCC(CC1)C(C)(C)O2"

/-- Exact-symbolic reporting does not round the classification. -/
def IdentityXReportedResult : Prop :=
  IdentityXRawResult ∧
  identityXDisplay =
    "gpt_corrected_kimi_draft: compound 6, linalool"

/-- Exact-symbolic reporting does not round the classification. -/
def IdentityYReportedResult : Prop :=
  IdentityYRawResult ∧
  identityYDisplay =
    "gpt_corrected_kimi_draft: compound 3, 1,8-cineole (eucalyptol); \
     corrected SMILES CC12CCC(CC1)C(C)(C)O2"

/-- Combined raw contract for both requested outputs, in source order. -/
def RawResult : Prop :=
  IdentityXRawResult ∧ IdentityYRawResult

/-- Combined reported contract for both requested outputs, in source order. -/
def ReportedResult : Prop :=
  IdentityXReportedResult ∧ IdentityYReportedResult

theorem gpt_corrected_kimi_draft_raw_result : RawResult := by
  exact
    ⟨⟨rfl, rfl, rfl, rfl, rfl, compound6_image_carrier,
        submitted_pair_meets_source_constraints⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, compound3_image_carrier,
        submitted_pair_meets_source_constraints,
        y_connectivity_correction_exact⟩⟩

theorem gpt_corrected_kimi_draft_reported_result : ReportedResult := by
  exact
    ⟨⟨gpt_corrected_kimi_draft_raw_result.1, rfl⟩,
      ⟨gpt_corrected_kimi_draft_raw_result.2, rfl⟩⟩

/-! ## Frozen-draft fidelity and correction scope -/

def frozenDraftXOutput : IdentificationOutput := identityXOutput

def frozenDraftYOutput : IdentificationOutput :=
  { identityYOutput with
    auxiliarySmiles := frozenDraftYSmiles
    graph := frozenDraftYSmilesGraph }

/-- All X fields and all non-connectivity Y fields are preserved.  The sole
change is the authorized Y auxiliary string/graph rewiring recorded by
`YConnectivityCorrection`. -/
def AuthorizedCorrectionOnly : Prop :=
  frozenDraftXOutput = identityXOutput ∧
  frozenDraftYOutput.basis = identityYOutput.basis ∧
  frozenDraftYOutput.role = identityYOutput.role ∧
  frozenDraftYOutput.compound = identityYOutput.compound ∧
  frozenDraftYOutput.number = identityYOutput.number ∧
  frozenDraftYOutput.commonName = identityYOutput.commonName ∧
  frozenDraftYOutput.systematicName = identityYOutput.systematicName ∧
  frozenDraftYOutput.formula = identityYOutput.formula ∧
  frozenDraftYOutput.auxiliarySmiles = frozenDraftYSmiles ∧
  identityYOutput.auxiliarySmiles = correctedYSmiles ∧
  frozenDraftYOutput.graph = frozenDraftYSmilesGraph ∧
  identityYOutput.graph = correctedCineoleGraph ∧
  frozenDraftYOutput.graph ≠ identityYOutput.graph ∧
  YConnectivityCorrection

theorem authorized_correction_only : AuthorizedCorrectionOnly := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, by decide, y_connectivity_correction_exact⟩

/-- Formalization target for T1-A1. -/
theorem icho_2026_t1_a1_target :
    RawResult ∧ ReportedResult ∧ AuthorizedCorrectionOnly := by
  exact ⟨gpt_corrected_kimi_draft_raw_result,
    gpt_corrected_kimi_draft_reported_result,
    authorized_correction_only⟩

end Icho2026T1A1
end IChO2026Problems
