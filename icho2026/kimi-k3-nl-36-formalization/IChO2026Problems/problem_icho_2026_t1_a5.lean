import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem 1.5

This file formalizes the three displayed structural answers as explicit finite
molecular graphs.  Hydrogens are vertices rather than implicit annotations;
atom charge, radical count, atom stereochemistry, bond order, and bond
stereochemistry are therefore all part of the output.

The two arrows in the problem are used only as qualitative named-transform
constraints.  The graph-edit and formula ledgers below check compatibility of
the submitted structures; they make no assertion about yield, completeness,
phase, omitted products, or reaction conditions not printed in the problem.
-/

namespace IChO2026Problems.ProblemIcho2026T1A5

inductive Element where
  | hydrogen
  | carbon
  | oxygen
  deriving DecidableEq, Fintype, Repr

inductive AtomStereo where
  | notStereogenic
  | r
  | s
  deriving DecidableEq, Repr

inductive BondOrder where
  | single
  | double
  | triple
  | aromatic
  deriving DecidableEq, Repr

inductive BondStereo where
  | notStereogenic
  | e
  | z
  deriving DecidableEq, Repr

structure AtomData where
  element : Element
  formalCharge : ℤ
  radicalElectrons : ℕ
  stereo : AtomStereo
  deriving DecidableEq, Repr

structure BondData where
  order : BondOrder
  stereo : BondStereo
  deriving DecidableEq, Repr

/-- A molecular graph whose atom identifiers are supplied by the caller. -/
structure MolecularStructure (ι : Type) where
  atom : ι → AtomData
  bond : ι → ι → Option BondData

def neutralAtom (element : Element) : AtomData where
  element := element
  formalCharge := 0
  radicalElectrons := 0
  stereo := .notStereogenic

def singleBond : BondData := ⟨.single, .notStereogenic⟩
def doubleBond : BondData := ⟨.double, .notStereogenic⟩
def aromaticBond : BondData := ⟨.aromatic, .notStereogenic⟩

def BondOrder.valence : BondOrder → ℚ
  | .single => 1
  | .double => 2
  | .triple => 3
  | .aromatic => 3 / 2

def Element.neutralValence : Element → ℚ
  | .hydrogen => 1
  | .carbon => 4
  | .oxygen => 2

noncomputable def MolecularStructure.localValence
    {ι : Type} [Fintype ι] (m : MolecularStructure ι) (i : ι) : ℚ := by
  classical
  exact ∑ j, ((m.bond i j).map (fun (b : BondData) => b.order.valence)).getD 0

/-- Closed-shell neutral graph validity for the three neutral output molecules. -/
def MolecularStructure.ClosedShellNeutralWellFormed
    {ι : Type} [Fintype ι] (m : MolecularStructure ι) : Prop :=
  (∀ i, m.bond i i = none) ∧
  (∀ i j, m.bond i j = m.bond j i) ∧
  (∀ i, (m.atom i).formalCharge = 0 ∧
    (m.atom i).radicalElectrons = 0 ∧
    m.localValence i = (m.atom i).element.neutralValence)

/-- Structural equivalence preserves every atom field and every bond field. -/
def StructurallyEquivalent
    {ι κ : Type} (m : MolecularStructure ι) (n : MolecularStructure κ) : Prop :=
  ∃ e : ι ≃ κ,
    (∀ i, m.atom i = n.atom (e i)) ∧
    (∀ i j, m.bond i j = n.bond (e i) (e j))

def PreservesStructure
    {ι : Type} (m : MolecularStructure ι) (σ : ι ≃ ι) : Prop :=
  (∀ i, m.atom (σ i) = m.atom i) ∧
  (∀ i j, m.bond (σ i) (σ j) = m.bond i j)

/-- The permutation has order exactly `n`; this is the combinatorial carrier
for the source's rotational-axis statements. -/
def PermutationOrderExactly {ι : Type} (σ : ι ≃ ι) (n : ℕ) : Prop :=
  (∀ i, (σ ^ n) i = i) ∧
  (∀ k, 0 < k → k < n → ∃ i, (σ ^ k) i ≠ i)

abbrev MolecularFormula := CRNT.Complex Element

noncomputable def MolecularStructure.formula
    {ι : Type} [Fintype ι] (m : MolecularStructure ι) : MolecularFormula := by
  classical
  exact fun e => (Finset.univ.filter fun i => (m.atom i).element = e).card

def formulaC12H18 : MolecularFormula
  | .carbon => 12
  | .hydrogen => 18
  | .oxygen => 0

def formulaC12H6O12 : MolecularFormula
  | .carbon => 12
  | .hydrogen => 6
  | .oxygen => 12

def formulaC12O9 : MolecularFormula
  | .carbon => 12
  | .hydrogen => 0
  | .oxygen => 9

def waterFormula : MolecularFormula
  | .carbon => 0
  | .hydrogen => 2
  | .oxygen => 1

/- The nominal weights are the version-pinned CIAAW 2024 abridged values.
Dataset SHA-256:
11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5. -/
noncomputable def atomicWeight : Element → ℝ
  | .hydrogen => 1008 / 1000
  | .carbon => 12011 / 1000
  | .oxygen => 15999 / 1000

noncomputable def formulaMass (f : MolecularFormula) : ℝ :=
  ∑ e, (f e : ℝ) * atomicWeight e

noncomputable def elementMassFraction
    (e : Element) (f : MolecularFormula) : ℝ :=
  (f e : ℝ) * atomicWeight e / formulaMass f

/-- `11.18%` is a displayed mass fraction with quantum `0.01` percentage
points, i.e. `1/10000` as a dimensionless fraction. -/
def hydrogenFractionObservation (f : MolecularFormula) : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement
    (elementMassFraction .hydrogen f) (1118 / 10000) (1 / 10000)

/-- `49.98%` is treated with the same displayed-fraction quantum. -/
def oxygenFractionObservation (f : MolecularFormula) : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement
    (elementMassFraction .oxygen f) (4998 / 10000) (1 / 10000)

def successor6 (i : Fin 6) : Fin 6 :=
  ⟨(i.val + 1) % 6, Nat.mod_lt _ (by decide)⟩

def predecessor6 (i : Fin 6) : Fin 6 :=
  ⟨(i.val + 5) % 6, Nat.mod_lt _ (by decide)⟩

def adjacent6 (i j : Fin 6) : Prop :=
  successor6 i = j ∨ successor6 j = i

instance adjacent6Decidable (i j : Fin 6) : Decidable (adjacent6 i j) := by
  unfold adjacent6
  infer_instance

def rotateFin6 : Fin 6 ≃ Fin 6 where
  toFun := successor6
  invFun := predecessor6
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

def successor3 (i : Fin 3) : Fin 3 :=
  ⟨(i.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

def predecessor3 (i : Fin 3) : Fin 3 :=
  ⟨(i.val + 2) % 3, Nat.mod_lt _ (by decide)⟩

def rotateFin3 : Fin 3 ≃ Fin 3 where
  toFun := successor3
  invFun := predecessor3
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-! ## E: hexamethylbenzene, with every hydrogen explicit -/

inductive EAtom where
  | ring (site : Fin 6)
  | methyl (site : Fin 6)
  | methylHydrogen (site : Fin 6) (which : Fin 3)
  deriving DecidableEq, Fintype, Repr

def eAtomData : EAtom → AtomData
  | .ring _ => neutralAtom .carbon
  | .methyl _ => neutralAtom .carbon
  | .methylHydrogen _ _ => neutralAtom .hydrogen

def eBondData : EAtom → EAtom → Option BondData
  | .ring i, .ring j => if adjacent6 i j then some aromaticBond else none
  | .ring i, .methyl j => if i = j then some singleBond else none
  | .methyl i, .ring j => if i = j then some singleBond else none
  | .methyl i, .methylHydrogen j _ => if i = j then some singleBond else none
  | .methylHydrogen i _, .methyl j => if i = j then some singleBond else none
  | _, _ => none

/-- Complete graph for `C₆(CH₃)₆`; this is the `structure_e` carrier. -/
def structureE : MolecularStructure EAtom := ⟨eAtomData, eBondData⟩

def rotateEAtom : EAtom ≃ EAtom where
  toFun
    | .ring i => .ring (rotateFin6 i)
    | .methyl i => .methyl (rotateFin6 i)
    | .methylHydrogen i h => .methylHydrogen (rotateFin6 i) h
  invFun
    | .ring i => .ring (rotateFin6.symm i)
    | .methyl i => .methyl (rotateFin6.symm i)
    | .methylHydrogen i h => .methylHydrogen (rotateFin6.symm i) h
  left_inv := by
    intro i
    cases i <;> simp
  right_inv := by
    intro i
    cases i <;> simp

def IsMethylAt
    {ι : Type} (m : MolecularStructure ι)
    (ring methyl : ι) (hydrogen : Fin 3 → ι) : Prop :=
  (m.atom ring).element = .carbon ∧
  (m.atom methyl).element = .carbon ∧
  (∀ h, (m.atom (hydrogen h)).element = .hydrogen) ∧
  m.bond ring methyl = some singleBond ∧
  (∀ h, m.bond methyl (hydrogen h) = some singleBond)

/-! ## F: mellitic acid, with six explicit carboxylic-acid groups -/

inductive FAtom where
  | ring (site : Fin 6)
  | carboxylCarbon (site : Fin 6)
  | carbonylOxygen (site : Fin 6)
  | hydroxylOxygen (site : Fin 6)
  | acidicHydrogen (site : Fin 6)
  deriving DecidableEq, Fintype, Repr

def fAtomData : FAtom → AtomData
  | .ring _ => neutralAtom .carbon
  | .carboxylCarbon _ => neutralAtom .carbon
  | .carbonylOxygen _ => neutralAtom .oxygen
  | .hydroxylOxygen _ => neutralAtom .oxygen
  | .acidicHydrogen _ => neutralAtom .hydrogen

def fBondData : FAtom → FAtom → Option BondData
  | .ring i, .ring j => if adjacent6 i j then some aromaticBond else none
  | .ring i, .carboxylCarbon j => if i = j then some singleBond else none
  | .carboxylCarbon i, .ring j => if i = j then some singleBond else none
  | .carboxylCarbon i, .carbonylOxygen j => if i = j then some doubleBond else none
  | .carbonylOxygen i, .carboxylCarbon j => if i = j then some doubleBond else none
  | .carboxylCarbon i, .hydroxylOxygen j => if i = j then some singleBond else none
  | .hydroxylOxygen i, .carboxylCarbon j => if i = j then some singleBond else none
  | .hydroxylOxygen i, .acidicHydrogen j => if i = j then some singleBond else none
  | .acidicHydrogen i, .hydroxylOxygen j => if i = j then some singleBond else none
  | _, _ => none

/-- Complete graph for `C₆(COOH)₆`; this is the `structure_f` carrier. -/
def structureF : MolecularStructure FAtom := ⟨fAtomData, fBondData⟩

def rotateFAtom : FAtom ≃ FAtom where
  toFun
    | .ring i => .ring (rotateFin6 i)
    | .carboxylCarbon i => .carboxylCarbon (rotateFin6 i)
    | .carbonylOxygen i => .carbonylOxygen (rotateFin6 i)
    | .hydroxylOxygen i => .hydroxylOxygen (rotateFin6 i)
    | .acidicHydrogen i => .acidicHydrogen (rotateFin6 i)
  invFun
    | .ring i => .ring (rotateFin6.symm i)
    | .carboxylCarbon i => .carboxylCarbon (rotateFin6.symm i)
    | .carbonylOxygen i => .carbonylOxygen (rotateFin6.symm i)
    | .hydroxylOxygen i => .hydroxylOxygen (rotateFin6.symm i)
    | .acidicHydrogen i => .acidicHydrogen (rotateFin6.symm i)
  left_inv := by
    intro i
    cases i <;> simp
  right_inv := by
    intro i
    cases i <;> simp

def IsCarboxylicAcidAt
    {ι : Type} (m : MolecularStructure ι)
    (ring carbonylCarbon carbonylOxygen hydroxylOxygen hydrogen : ι) : Prop :=
  (m.atom ring).element = .carbon ∧
  (m.atom carbonylCarbon).element = .carbon ∧
  (m.atom carbonylOxygen).element = .oxygen ∧
  (m.atom hydroxylOxygen).element = .oxygen ∧
  (m.atom hydrogen).element = .hydrogen ∧
  m.bond ring carbonylCarbon = some singleBond ∧
  m.bond carbonylCarbon carbonylOxygen = some doubleBond ∧
  m.bond carbonylCarbon hydroxylOxygen = some singleBond ∧
  m.bond hydroxylOxygen hydrogen = some singleBond

/-! ## G: mellitic trianhydride, including all three bridging oxygens -/

inductive GAtom where
  | ring (site : Fin 6)
  | carboxylCarbon (site : Fin 6)
  | carbonylOxygen (site : Fin 6)
  | bridgeOxygen (bridge : Fin 3)
  deriving DecidableEq, Fintype, Repr

def gAtomData : GAtom → AtomData
  | .ring _ => neutralAtom .carbon
  | .carboxylCarbon _ => neutralAtom .carbon
  | .carbonylOxygen _ => neutralAtom .oxygen
  | .bridgeOxygen _ => neutralAtom .oxygen

/-- Bridge `j` joins the adjacent carboxyl carbons at ring sites `2j` and
`2j+1`, yielding the three alternating anhydride closures. -/
def belongsToBridge (site : Fin 6) (bridge : Fin 3) : Prop :=
  site.val = 2 * bridge.val ∨ site.val = 2 * bridge.val + 1

instance belongsToBridgeDecidable (site : Fin 6) (bridge : Fin 3) :
    Decidable (belongsToBridge site bridge) := by
  unfold belongsToBridge
  infer_instance

def gBondData : GAtom → GAtom → Option BondData
  | .ring i, .ring j => if adjacent6 i j then some aromaticBond else none
  | .ring i, .carboxylCarbon j => if i = j then some singleBond else none
  | .carboxylCarbon i, .ring j => if i = j then some singleBond else none
  | .carboxylCarbon i, .carbonylOxygen j => if i = j then some doubleBond else none
  | .carbonylOxygen i, .carboxylCarbon j => if i = j then some doubleBond else none
  | .carboxylCarbon i, .bridgeOxygen j =>
      if belongsToBridge i j then some singleBond else none
  | .bridgeOxygen i, .carboxylCarbon j =>
      if belongsToBridge j i then some singleBond else none
  | _, _ => none

/-- Complete graph for `C₁₂O₉`; this is the `structure_g` carrier. -/
def structureG : MolecularStructure GAtom := ⟨gAtomData, gBondData⟩

def rotateGAtom : GAtom ≃ GAtom where
  toFun
    | .ring i => .ring (rotateFin6 (rotateFin6 i))
    | .carboxylCarbon i => .carboxylCarbon (rotateFin6 (rotateFin6 i))
    | .carbonylOxygen i => .carbonylOxygen (rotateFin6 (rotateFin6 i))
    | .bridgeOxygen i => .bridgeOxygen (rotateFin3 i)
  invFun
    | .ring i => .ring (rotateFin6.symm (rotateFin6.symm i))
    | .carboxylCarbon i => .carboxylCarbon (rotateFin6.symm (rotateFin6.symm i))
    | .carbonylOxygen i => .carbonylOxygen (rotateFin6.symm (rotateFin6.symm i))
    | .bridgeOxygen i => .bridgeOxygen (rotateFin3.symm i)
  left_inv := by
    intro i
    cases i <;> simp
  right_inv := by
    intro i
    cases i <;> simp

def IsAnhydrideBridgeAt
    {ι : Type} (m : MolecularStructure ι)
    (firstCarbonyl secondCarbonyl firstOxygen secondOxygen bridgeOxygen : ι) : Prop :=
  (m.atom firstCarbonyl).element = .carbon ∧
  (m.atom secondCarbonyl).element = .carbon ∧
  (m.atom firstOxygen).element = .oxygen ∧
  (m.atom secondOxygen).element = .oxygen ∧
  (m.atom bridgeOxygen).element = .oxygen ∧
  m.bond firstCarbonyl firstOxygen = some doubleBond ∧
  m.bond secondCarbonyl secondOxygen = some doubleBond ∧
  m.bond firstCarbonyl bridgeOxygen = some singleBond ∧
  m.bond secondCarbonyl bridgeOxygen = some singleBond

def ContainsOnlyCarbonAndOxygen
    {ι : Type} [Fintype ι] (m : MolecularStructure ι) : Prop :=
  (∀ i, (m.atom i).element = .carbon ∨ (m.atom i).element = .oxygen) ∧
  (∃ i, (m.atom i).element = .carbon) ∧
  (∃ i, (m.atom i).element = .oxygen)

/-! ## Source arrows and non-quantitative compatibility ledgers -/

inductive SubstanceRole where
  | e
  | f
  | g
  deriving DecidableEq, Repr

inductive Reagent where
  | potassiumPermanganate
  | nitricAcid
  | phosphorusPentoxide
  deriving DecidableEq, Repr

inductive Medium where
  | acidic
  | notPrinted
  deriving DecidableEq, Repr

structure QualitativeNamedTransform where
  reactant : SubstanceRole
  product : SubstanceRole
  reagents : List Reagent
  medium : Medium
  deriving DecidableEq, Repr

/-- Figure Q1-3: `E --(KMnO₄/HNO₃)→ F`. -/
def sourceOxidationArrow : QualitativeNamedTransform where
  reactant := .e
  product := .f
  reagents := [.potassiumPermanganate, .nitricAcid]
  medium := .acidic

/-- Figure Q1-3: `F --(P₂O₅)→ G`; no temperature or phase is printed. -/
def sourceDehydrationArrow : QualitativeNamedTransform where
  reactant := .f
  product := .g
  reagents := [.phosphorusPentoxide]
  medium := .notPrinted

def sourceArrowContract : Prop :=
  sourceOxidationArrow.reactant = .e ∧
  sourceOxidationArrow.product = .f ∧
  sourceOxidationArrow.reagents = [.potassiumPermanganate, .nitricAcid] ∧
  sourceOxidationArrow.medium = .acidic ∧
  sourceDehydrationArrow.reactant = .f ∧
  sourceDehydrationArrow.product = .g ∧
  sourceDehydrationArrow.reagents = [.phosphorusPentoxide] ∧
  sourceDehydrationArrow.medium = .notPrinted

/-- Candidate-local graph audit: each methyl substituent in E corresponds to
one carboxylic-acid substituent at the same ring site in F, and the aromatic
six-carbon skeleton is retained.  This is compatibility, not an empirical
claim that the printed conditions force this product. -/
def oxidationStructureCompatibility : Prop :=
  (∀ i j,
    structureE.bond (.ring i) (.ring j) =
      structureF.bond (.ring i) (.ring j)) ∧
  (∀ i,
    IsMethylAt structureE (.ring i) (.methyl i) (.methylHydrogen i) ∧
    IsCarboxylicAcidAt structureF (.ring i) (.carboxylCarbon i)
      (.carbonylOxygen i) (.hydroxylOxygen i) (.acidicHydrogen i))

/-- Candidate-local dehydration ledger.  It records the primitive formula
difference and all three anhydride bridges but does not assert a material-stage
yield or that no other product is formed. -/
def dehydrationStructureCompatibility : Prop :=
  structureF.formula =
      CRNT.Complex.add structureG.formula (CRNT.Complex.smul 3 waterFormula) ∧
  (∀ j : Fin 3,
    IsAnhydrideBridgeAt structureG
      (.carboxylCarbon ⟨2 * j.val, by omega⟩)
      (.carboxylCarbon ⟨2 * j.val + 1, by omega⟩)
      (.carbonylOxygen ⟨2 * j.val, by omega⟩)
      (.carbonylOxygen ⟨2 * j.val + 1, by omega⟩)
      (.bridgeOxygen j))

/-- Exact structural answer for E, including formula, all six methyl groups,
closed-shell valence, absent stereocentres, six-fold graph symmetry, and the
printed hydrogen fraction. -/
def StructureEAnswer : Prop :=
  structureE.ClosedShellNeutralWellFormed ∧
  structureE.formula = formulaC12H18 ∧
  (∀ i, IsMethylAt structureE (.ring i) (.methyl i) (.methylHydrogen i)) ∧
  PreservesStructure structureE rotateEAtom ∧
  PermutationOrderExactly rotateEAtom 6 ∧
  hydrogenFractionObservation structureE.formula

/-- Exact structural answer for F: the six ring positions each bear `COOH`. -/
def StructureFAnswer : Prop :=
  structureF.ClosedShellNeutralWellFormed ∧
  structureF.formula = formulaC12H6O12 ∧
  (∀ i, IsCarboxylicAcidAt structureF (.ring i) (.carboxylCarbon i)
    (.carbonylOxygen i) (.hydroxylOxygen i) (.acidicHydrogen i)) ∧
  PreservesStructure structureF rotateFAtom ∧
  PermutationOrderExactly rotateFAtom 6 ∧
  oxidationStructureCompatibility

/-- Exact structural answer for G: six carbonyls are paired by three explicit
anhydride oxygens, producing `C₁₂O₉` and an order-three rotation. -/
def StructureGAnswer : Prop :=
  structureG.ClosedShellNeutralWellFormed ∧
  structureG.formula = formulaC12O9 ∧
  ContainsOnlyCarbonAndOxygen structureG ∧
  PreservesStructure structureG rotateGAtom ∧
  PermutationOrderExactly rotateGAtom 3 ∧
  oxygenFractionObservation structureG.formula ∧
  dehydrationStructureCompatibility

/-- Raw exact-symbolic result for all three requested outputs. -/
def RawResult : Prop :=
  sourceArrowContract ∧ StructureEAnswer ∧ StructureFAnswer ∧ StructureGAnswer

/-- Exact symbolic reporting performs no rounding or representational change. -/
def ReportedResult : Prop := RawResult

private theorem sourceArrowContract_holds : sourceArrowContract := by
  simp [sourceArrowContract, sourceOxidationArrow, sourceDehydrationArrow]

private theorem structureE_wellFormed :
    structureE.ClosedShellNeutralWellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> decide
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · intro i
    cases i with
    | ring i =>
        fin_cases i <;>
          norm_num [MolecularStructure.localValence, structureE, eAtomData, eBondData,
            neutralAtom, singleBond, aromaticBond, BondOrder.valence,
            Element.neutralValence, adjacent6, successor6] <;> native_decide
    | methyl i =>
        fin_cases i <;>
          norm_num [MolecularStructure.localValence, structureE, eAtomData, eBondData,
            neutralAtom, singleBond, aromaticBond, BondOrder.valence,
            Element.neutralValence, adjacent6, successor6] <;> native_decide
    | methylHydrogen i h =>
        fin_cases i <;> fin_cases h <;>
          norm_num [MolecularStructure.localValence, structureE, eAtomData, eBondData,
            neutralAtom, singleBond, aromaticBond, BondOrder.valence,
            Element.neutralValence, adjacent6, successor6] <;> native_decide

private theorem structureF_wellFormed :
    structureF.ClosedShellNeutralWellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> decide
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · intro i
    cases i with
    | ring i =>
        fin_cases i <;>
          norm_num [MolecularStructure.localValence, structureF, fAtomData, fBondData,
            neutralAtom, singleBond, doubleBond, aromaticBond, BondOrder.valence,
            Element.neutralValence, adjacent6, successor6] <;> native_decide
    | carboxylCarbon i =>
        fin_cases i <;>
          norm_num [MolecularStructure.localValence, structureF, fAtomData, fBondData,
            neutralAtom, singleBond, doubleBond, aromaticBond, BondOrder.valence,
            Element.neutralValence, adjacent6, successor6] <;> native_decide
    | carbonylOxygen i =>
        fin_cases i <;>
          norm_num [MolecularStructure.localValence, structureF, fAtomData, fBondData,
            neutralAtom, singleBond, doubleBond, aromaticBond, BondOrder.valence,
            Element.neutralValence, adjacent6, successor6] <;> native_decide
    | hydroxylOxygen i =>
        fin_cases i <;>
          norm_num [MolecularStructure.localValence, structureF, fAtomData, fBondData,
            neutralAtom, singleBond, doubleBond, aromaticBond, BondOrder.valence,
            Element.neutralValence, adjacent6, successor6] <;> native_decide
    | acidicHydrogen i =>
        fin_cases i <;>
          norm_num [MolecularStructure.localValence, structureF, fAtomData, fBondData,
            neutralAtom, singleBond, doubleBond, aromaticBond, BondOrder.valence,
            Element.neutralValence, adjacent6, successor6] <;> native_decide

private theorem structureG_wellFormed :
    structureG.ClosedShellNeutralWellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> decide
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · intro i
    cases i with
    | ring i =>
        fin_cases i <;>
          norm_num [MolecularStructure.localValence, structureG, gAtomData, gBondData,
            neutralAtom, singleBond, doubleBond, aromaticBond, BondOrder.valence,
            Element.neutralValence, adjacent6, successor6, belongsToBridge] <;>
          native_decide
    | carboxylCarbon i =>
        fin_cases i <;>
          norm_num [MolecularStructure.localValence, structureG, gAtomData, gBondData,
            neutralAtom, singleBond, doubleBond, aromaticBond, BondOrder.valence,
            Element.neutralValence, adjacent6, successor6, belongsToBridge] <;>
          native_decide
    | carbonylOxygen i =>
        fin_cases i <;>
          norm_num [MolecularStructure.localValence, structureG, gAtomData, gBondData,
            neutralAtom, singleBond, doubleBond, aromaticBond, BondOrder.valence,
            Element.neutralValence, adjacent6, successor6, belongsToBridge] <;>
          native_decide
    | bridgeOxygen i =>
        fin_cases i <;>
          norm_num [MolecularStructure.localValence, structureG, gAtomData, gBondData,
            neutralAtom, singleBond, doubleBond, aromaticBond, BondOrder.valence,
            Element.neutralValence, adjacent6, successor6, belongsToBridge] <;>
          native_decide

private theorem structureE_formula_holds :
    structureE.formula = formulaC12H18 := by
  decide

private theorem structureF_formula_holds :
    structureF.formula = formulaC12H6O12 := by
  decide

private theorem structureG_formula_holds :
    structureG.formula = formulaC12O9 := by
  decide

private theorem structureE_methyl_groups :
    ∀ i, IsMethylAt structureE (.ring i) (.methyl i) (.methylHydrogen i) := by
  intro i
  simp [IsMethylAt, structureE, eAtomData, eBondData, neutralAtom, singleBond]

private theorem structureF_carboxylic_acid_groups :
    ∀ i, IsCarboxylicAcidAt structureF (.ring i) (.carboxylCarbon i)
      (.carbonylOxygen i) (.hydroxylOxygen i) (.acidicHydrogen i) := by
  intro i
  simp [IsCarboxylicAcidAt, structureF, fAtomData, fBondData, neutralAtom,
    singleBond, doubleBond]

private theorem structureG_contains_only_carbon_and_oxygen :
    ContainsOnlyCarbonAndOxygen structureG := by
  unfold ContainsOnlyCarbonAndOxygen
  native_decide

private theorem structureE_rotation_preserves :
    PreservesStructure structureE rotateEAtom := by
  unfold PreservesStructure
  native_decide

private theorem structureF_rotation_preserves :
    PreservesStructure structureF rotateFAtom := by
  unfold PreservesStructure
  native_decide

private theorem structureG_rotation_preserves :
    PreservesStructure structureG rotateGAtom := by
  unfold PreservesStructure
  native_decide

private theorem rotateEAtom_order_six :
    PermutationOrderExactly rotateEAtom 6 := by
  unfold PermutationOrderExactly
  constructor
  · intro i
    fin_cases i <;> native_decide
  · intro k hkPos hkLt
    interval_cases k <;>
      refine ⟨.ring 0, ?_⟩ <;>
      native_decide

private theorem rotateFAtom_order_six :
    PermutationOrderExactly rotateFAtom 6 := by
  unfold PermutationOrderExactly
  constructor
  · intro i
    fin_cases i <;> native_decide
  · intro k hkPos hkLt
    interval_cases k <;>
      refine ⟨.ring 0, ?_⟩ <;>
      native_decide

private theorem rotateGAtom_order_three :
    PermutationOrderExactly rotateGAtom 3 := by
  unfold PermutationOrderExactly
  constructor
  · intro i
    fin_cases i <;> native_decide
  · intro k hkPos hkLt
    interval_cases k <;>
      refine ⟨.ring 0, ?_⟩ <;>
      native_decide

private theorem oxidation_compatibility_holds :
    oxidationStructureCompatibility := by
  unfold oxidationStructureCompatibility
  constructor
  · intro i j
    rfl
  · intro i
    exact ⟨structureE_methyl_groups i, structureF_carboxylic_acid_groups i⟩

private theorem structureG_anhydride_bridges :
    ∀ j : Fin 3,
      IsAnhydrideBridgeAt structureG
        (.carboxylCarbon ⟨2 * j.val, by omega⟩)
        (.carboxylCarbon ⟨2 * j.val + 1, by omega⟩)
        (.carbonylOxygen ⟨2 * j.val, by omega⟩)
        (.carbonylOxygen ⟨2 * j.val + 1, by omega⟩)
        (.bridgeOxygen j) := by
  intro j
  simp [IsAnhydrideBridgeAt, structureG, gAtomData, gBondData, neutralAtom,
    singleBond, doubleBond, belongsToBridge]

private theorem dehydration_compatibility_holds :
    dehydrationStructureCompatibility := by
  refine ⟨?_, structureG_anhydride_bridges⟩
  rw [structureF_formula_holds, structureG_formula_holds]
  funext e
  cases e <;> rfl

private theorem element_univ :
    (Finset.univ : Finset Element) = {.hydrogen, .carbon, .oxygen} := by
  native_decide

private theorem formulaMass_C12H18 :
    formulaMass formulaC12H18 =
      (12 : ℝ) * (12011 / 1000) + (18 : ℝ) * (1008 / 1000) := by
  unfold formulaMass
  rw [element_univ]
  rw [Finset.sum_insert (by decide :
    Element.hydrogen ∉ ({.carbon, .oxygen} : Finset Element))]
  rw [Finset.sum_insert (by decide :
    Element.carbon ∉ ({.oxygen} : Finset Element))]
  norm_num [formulaC12H18, atomicWeight]

private theorem formulaMass_C12O9 :
    formulaMass formulaC12O9 =
      (12 : ℝ) * (12011 / 1000) + (9 : ℝ) * (15999 / 1000) := by
  unfold formulaMass
  rw [element_univ]
  rw [Finset.sum_insert (by decide :
    Element.hydrogen ∉ ({.carbon, .oxygen} : Finset Element))]
  rw [Finset.sum_insert (by decide :
    Element.carbon ∉ ({.oxygen} : Finset Element))]
  norm_num [formulaC12O9, atomicWeight]

private theorem structureE_hydrogen_fraction :
    hydrogenFractionObservation structureE.formula := by
  rw [structureE_formula_holds]
  unfold hydrogenFractionObservation
  unfold IChO2026Chem.Reporting.ConsistentMeasurement elementMassFraction
  rw [formulaMass_C12H18]
  norm_num [formulaC12H18, atomicWeight, abs_le]

private theorem structureG_oxygen_fraction :
    oxygenFractionObservation structureG.formula := by
  rw [structureG_formula_holds]
  unfold oxygenFractionObservation
  unfold IChO2026Chem.Reporting.ConsistentMeasurement elementMassFraction
  rw [formulaMass_C12O9]
  norm_num [formulaC12O9, atomicWeight, abs_le]

private theorem structureE_answer_holds : StructureEAnswer := by
  exact ⟨structureE_wellFormed, structureE_formula_holds,
    structureE_methyl_groups, structureE_rotation_preserves,
    rotateEAtom_order_six, structureE_hydrogen_fraction⟩

private theorem structureF_answer_holds : StructureFAnswer := by
  exact ⟨structureF_wellFormed, structureF_formula_holds,
    structureF_carboxylic_acid_groups, structureF_rotation_preserves,
    rotateFAtom_order_six, oxidation_compatibility_holds⟩

private theorem structureG_answer_holds : StructureGAnswer := by
  exact ⟨structureG_wellFormed, structureG_formula_holds,
    structureG_contains_only_carbon_and_oxygen, structureG_rotation_preserves,
    rotateGAtom_order_three, structureG_oxygen_fraction,
    dehydration_compatibility_holds⟩

theorem problem_icho_2026_t1_a5_raw_result : RawResult := by
  exact ⟨sourceArrowContract_holds, structureE_answer_holds,
    structureF_answer_holds, structureG_answer_holds⟩

theorem problem_icho_2026_t1_a5_reported_result : ReportedResult := by
  exact problem_icho_2026_t1_a5_raw_result

end IChO2026Problems.ProblemIcho2026T1A5
