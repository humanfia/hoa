import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem T8.2

This file formalizes the five structures requested in the oxidation sequence of
triethanolamine. Hydrogen atoms are represented explicitly by the
`attachedHydrogens` field of their unique heavy-atom site. Thus the heavy-atom
graph and every hydrogen--heavy-atom bond are both recoverable from a
`MolecularStructure`.

The transformation is used only as a `qualitative_named_transform_only` source
arrow. The declarations below check candidate connectivity, Lewis bookkeeping,
primitive atom/charge balance, and compatibility with the printed arrows; they
make no claim about yield, completeness, or absence of other pathways.
-/

namespace IChO2026Problems
namespace T8A2

open scoped BigOperators

/-! ## A small explicit Lewis-structure model -/

/-- Elements occurring in structures 2--7 and in the proton/water ledgers. -/
inductive Element where
  | hydrogen
  | carbon
  | nitrogen
  | oxygen
  deriving DecidableEq, Fintype, Repr

/-- Heavy-atom bond order; hydrogen bonds are counted at their attachment site. -/
inductive BondOrder where
  | none
  | single
  | double
  | triple
  deriving DecidableEq, Repr

def BondOrder.value : BondOrder → ℕ
  | .none => 0
  | .single => 1
  | .double => 2
  | .triple => 3

inductive TetrahedralConfiguration where
  | r
  | s
  deriving DecidableEq, Repr

inductive AlkeneConfiguration where
  | e
  | z
  deriving DecidableEq, Repr

/-- A Lewis atom together with all hydrogens singly bonded to it. -/
structure AtomSite where
  element : Element
  attachedHydrogens : ℕ
  lonePairs : ℕ
  radicalElectrons : ℕ
  formalCharge : ℤ
  deriving DecidableEq, Repr

/-- A finite labelled molecular graph. The vertex type is declared separately
for each molecular skeleton, so every heavy atom has a stable semantic name. -/
structure MolecularStructure (V : Type) where
  site : V → AtomSite
  bond : V → V → BondOrder
  tetrahedralStereo : V → Option TetrahedralConfiguration
  alkeneStereo : V → V → Option AlkeneConfiguration

/-- Molecular formula in the element order used in this problem. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

def MolecularFormula.zero : MolecularFormula :=
  { carbon := 0, hydrogen := 0, nitrogen := 0, oxygen := 0 }

def MolecularFormula.add (a b : MolecularFormula) : MolecularFormula :=
  { carbon := a.carbon + b.carbon
    hydrogen := a.hydrogen + b.hydrogen
    nitrogen := a.nitrogen + b.nitrogen
    oxygen := a.oxygen + b.oxygen }

def MolecularFormula.smul (k : ℕ) (a : MolecularFormula) : MolecularFormula :=
  { carbon := k * a.carbon
    hydrogen := k * a.hydrogen
    nitrogen := k * a.nitrogen
    oxygen := k * a.oxygen }

def MolecularFormula.count (f : MolecularFormula) : Element → ℕ
  | .hydrogen => f.hydrogen
  | .carbon => f.carbon
  | .nitrogen => f.nitrogen
  | .oxygen => f.oxygen

def molecularFormula {V : Type} [Fintype V] [DecidableEq V]
    (m : MolecularStructure V) : MolecularFormula :=
  { carbon := ∑ v : V, if (m.site v).element = .carbon then 1 else 0
    hydrogen := ∑ v : V, ((m.site v).attachedHydrogens +
      (if (m.site v).element = .hydrogen then 1 else 0))
    nitrogen := ∑ v : V, if (m.site v).element = .nitrogen then 1 else 0
    oxygen := ∑ v : V, if (m.site v).element = .oxygen then 1 else 0 }

def totalFormalCharge {V : Type} [Fintype V]
    (m : MolecularStructure V) : ℤ :=
  ∑ v : V, (m.site v).formalCharge

def totalRadicalElectrons {V : Type} [Fintype V]
    (m : MolecularStructure V) : ℕ :=
  ∑ v : V, (m.site v).radicalElectrons

def incidentBondOrder {V : Type} [Fintype V]
    (m : MolecularStructure V) (v : V) : ℕ :=
  ∑ w : V, (m.bond v w).value

def valenceElectrons : Element → ℕ
  | .hydrogen => 1
  | .carbon => 4
  | .nitrogen => 5
  | .oxygen => 6

/-- The Lewis formal-charge equation at a named heavy-atom site. -/
def LewisChargeAt {V : Type} [Fintype V]
    (m : MolecularStructure V) (v : V) : Prop :=
  let a := m.site v
  ((valenceElectrons a.element : ℕ) : ℤ) -
      (2 * (a.lonePairs : ℤ) + (a.radicalElectrons : ℤ)) -
      ((incidentBondOrder m v : ℕ) : ℤ) - (a.attachedHydrogens : ℤ) =
    a.formalCharge

/-- Structural well-formedness needed in this target. -/
def WellFormed {V : Type} [Fintype V]
    (m : MolecularStructure V) : Prop :=
  (∀ v, (m.site v).element ≠ .hydrogen) ∧
  (∀ v, m.bond v v = .none) ∧
  (∀ v w, m.bond v w = m.bond w v) ∧
  (∀ v, LewisChargeAt m v)

def NoSpecifiedStereochemistry {V : Type}
    (m : MolecularStructure V) : Prop :=
  (∀ v, m.tetrahedralStereo v = none) ∧
  (∀ v w, m.alkeneStereo v w = none)

def SameNuclearFramework {V : Type}
    (a b : MolecularStructure V) : Prop :=
  (∀ v, (a.site v).element = (b.site v).element ∧
    (a.site v).attachedHydrogens = (b.site v).attachedHydrogens) ∧
  (∀ v w, a.bond v w = b.bond v w)

def SameHeavySkeleton {V : Type}
    (a b : MolecularStructure V) : Prop :=
  (∀ v, (a.site v).element = (b.site v).element) ∧
  (∀ v w, a.bond v w = b.bond v w)

def SameConnectivityExcept {V : Type} [DecidableEq V]
    (a b : MolecularStructure V) (x y : V) : Prop :=
  ∀ u v, ¬ ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) →
    a.bond u v = b.bond u v

def HasLocalizedRadical {V : Type} [Fintype V]
    (m : MolecularStructure V) (v : V) : Prop :=
  (m.site v).radicalElectrons = 1 ∧ totalRadicalElectrons m = 1

def HasIminiumAt {V : Type}
    (m : MolecularStructure V) (n c : V) : Prop :=
  (m.site n).element = .nitrogen ∧
  (m.site c).element = .carbon ∧
  (m.site n).formalCharge = 1 ∧
  (m.site n).radicalElectrons = 0 ∧
  (m.site c).attachedHydrogens = 1 ∧
  m.bond n c = .double

def HasSecondaryAmineAt {V : Type}
    (m : MolecularStructure V) (n c1 c2 : V) : Prop :=
  (m.site n).element = .nitrogen ∧
  (m.site n).attachedHydrogens = 1 ∧
  (m.site n).formalCharge = 0 ∧
  (m.site n).lonePairs = 1 ∧
  (m.site c1).element = .carbon ∧
  (m.site c2).element = .carbon ∧
  m.bond n c1 = .single ∧ m.bond n c2 = .single

def HasAldehydeAt {V : Type}
    (m : MolecularStructure V) (carbonylC carbonylO substituentC : V) : Prop :=
  (m.site carbonylC).element = .carbon ∧
  (m.site carbonylC).attachedHydrogens = 1 ∧
  (m.site carbonylO).element = .oxygen ∧
  (m.site carbonylO).attachedHydrogens = 0 ∧
  (m.site substituentC).element = .carbon ∧
  m.bond carbonylC carbonylO = .double ∧
  m.bond carbonylC substituentC = .single

/-- A deliberately one-way compatibility predicate: an aldehyde candidate is
compatible with the printed positive Tollens test. No inverse classification
of all Tollens-positive compounds is asserted. -/
def TollensCompatible {V : Type} (m : MolecularStructure V) : Prop :=
  ∃ carbonylC carbonylO substituentC,
    HasAldehydeAt m carbonylC carbonylO substituentC

/-! ## Source structure 2 and candidate structures 3--7 -/

def mkSite (element : Element) (attachedHydrogens lonePairs radicalElectrons : ℕ)
    (formalCharge : ℤ) : AtomSite :=
  { element, attachedHydrogens, lonePairs, radicalElectrons, formalCharge }

/-- Named heavy atoms of N(CH2CH2OH)3, read directly from the figure. -/
inductive TEOASite where
  | nitrogen
  | alpha1 | beta1 | oxygen1
  | alpha2 | beta2 | oxygen2
  | alpha3 | beta3 | oxygen3
  deriving DecidableEq, Fintype, Repr

def teoaBond : TEOASite → TEOASite → BondOrder
  | .nitrogen, .alpha1 | .alpha1, .nitrogen
  | .nitrogen, .alpha2 | .alpha2, .nitrogen
  | .nitrogen, .alpha3 | .alpha3, .nitrogen
  | .alpha1, .beta1 | .beta1, .alpha1
  | .beta1, .oxygen1 | .oxygen1, .beta1
  | .alpha2, .beta2 | .beta2, .alpha2
  | .beta2, .oxygen2 | .oxygen2, .beta2
  | .alpha3, .beta3 | .beta3, .alpha3
  | .beta3, .oxygen3 | .oxygen3, .beta3 => .single
  | _, _ => .none

def teoaNeutralAtom : TEOASite → AtomSite
  | .nitrogen => mkSite .nitrogen 0 1 0 0
  | .alpha1 | .beta1 | .alpha2 | .beta2 | .alpha3 | .beta3 =>
      mkSite .carbon 2 0 0 0
  | .oxygen1 | .oxygen2 | .oxygen3 => mkSite .oxygen 1 2 0 0

/-- Species 2 as drawn: neutral triethanolamine. -/
def structure2 : MolecularStructure TEOASite where
  site := teoaNeutralAtom
  bond := teoaBond
  tetrahedralStereo := fun _ => none
  alkeneStereo := fun _ _ => none

def structure3Atom : TEOASite → AtomSite
  | .nitrogen => mkSite .nitrogen 0 0 1 1
  | v => teoaNeutralAtom v

/-- Candidate 3: the nitrogen-centred triethanolamine radical cation. -/
def structure3 : MolecularStructure TEOASite where
  site := structure3Atom
  bond := teoaBond
  tetrahedralStereo := fun _ => none
  alkeneStereo := fun _ _ => none

def structure4Atom : TEOASite → AtomSite
  | .alpha1 => mkSite .carbon 1 0 1 0
  | v => teoaNeutralAtom v

/-- Candidate 4: a neutral alpha-aminoalkyl radical. `alpha1` is one of
three symmetry-equivalent alpha carbons in species 2. -/
def structure4 : MolecularStructure TEOASite where
  site := structure4Atom
  bond := teoaBond
  tetrahedralStereo := fun _ => none
  alkeneStereo := fun _ _ => none

def iminiumBond : TEOASite → TEOASite → BondOrder
  | .nitrogen, .alpha1 | .alpha1, .nitrogen => .double
  | u, v => teoaBond u v

def structure5Atom : TEOASite → AtomSite
  | .nitrogen => mkSite .nitrogen 0 0 0 1
  | .alpha1 => mkSite .carbon 1 0 0 0
  | v => teoaNeutralAtom v

/-- Candidate 5: the N=CH-CH2OH iminium ion. -/
def structure5 : MolecularStructure TEOASite where
  site := structure5Atom
  bond := iminiumBond
  tetrahedralStereo := fun _ => none
  alkeneStereo := fun _ _ => none

/-- Named heavy atoms of HN(CH2CH2OH)2. -/
inductive DEASite where
  | nitrogen
  | alpha1 | beta1 | oxygen1
  | alpha2 | beta2 | oxygen2
  deriving DecidableEq, Fintype, Repr

def deaBond : DEASite → DEASite → BondOrder
  | .nitrogen, .alpha1 | .alpha1, .nitrogen
  | .nitrogen, .alpha2 | .alpha2, .nitrogen
  | .alpha1, .beta1 | .beta1, .alpha1
  | .beta1, .oxygen1 | .oxygen1, .beta1
  | .alpha2, .beta2 | .beta2, .alpha2
  | .beta2, .oxygen2 | .oxygen2, .beta2 => .single
  | _, _ => .none

def deaAtom : DEASite → AtomSite
  | .nitrogen => mkSite .nitrogen 1 1 0 0
  | .alpha1 | .beta1 | .alpha2 | .beta2 => mkSite .carbon 2 0 0 0
  | .oxygen1 | .oxygen2 => mkSite .oxygen 1 2 0 0

/-- Candidate 6: neutral diethanolamine. -/
def structure6 : MolecularStructure DEASite where
  site := deaAtom
  bond := deaBond
  tetrahedralStereo := fun _ => none
  alkeneStereo := fun _ _ => none

/-- Named heavy atoms of HOCH2CHO. -/
inductive GlycolaldehydeSite where
  | aldehydeCarbon
  | carbonylOxygen
  | hydroxymethylCarbon
  | hydroxyOxygen
  deriving DecidableEq, Fintype, Repr

def glycolaldehydeBond : GlycolaldehydeSite → GlycolaldehydeSite → BondOrder
  | .aldehydeCarbon, .carbonylOxygen | .carbonylOxygen, .aldehydeCarbon => .double
  | .aldehydeCarbon, .hydroxymethylCarbon | .hydroxymethylCarbon, .aldehydeCarbon
  | .hydroxymethylCarbon, .hydroxyOxygen | .hydroxyOxygen, .hydroxymethylCarbon =>
      .single
  | _, _ => .none

def glycolaldehydeAtom : GlycolaldehydeSite → AtomSite
  | .aldehydeCarbon => mkSite .carbon 1 0 0 0
  | .carbonylOxygen => mkSite .oxygen 0 2 0 0
  | .hydroxymethylCarbon => mkSite .carbon 2 0 0 0
  | .hydroxyOxygen => mkSite .oxygen 1 2 0 0

/-- Candidate 7: glycolaldehyde. -/
def structure7 : MolecularStructure GlycolaldehydeSite where
  site := glycolaldehydeAtom
  bond := glycolaldehydeBond
  tetrahedralStereo := fun _ => none
  alkeneStereo := fun _ _ => none

/-! ## Generic edit and fragment-mapping checks -/

def OneElectronOxidationAt {V : Type} [Fintype V] [DecidableEq V]
    (before after : MolecularStructure V) (centre : V) : Prop :=
  SameNuclearFramework before after ∧
  molecularFormula after = molecularFormula before ∧
  totalFormalCharge after = totalFormalCharge before + 1 ∧
  totalRadicalElectrons after = totalRadicalElectrons before + 1 ∧
  (after.site centre).element = .nitrogen ∧
  (after.site centre).radicalElectrons = (before.site centre).radicalElectrons + 1 ∧
  (∀ v, v ≠ centre → after.site v = before.site v)

def AlphaDeprotonation {V : Type} [Fintype V] [DecidableEq V]
    (before after : MolecularStructure V) (n alpha : V) : Prop :=
  SameHeavySkeleton before after ∧
  (before.site n).element = .nitrogen ∧
  (before.site alpha).element = .carbon ∧
  before.bond n alpha = .single ∧
  (after.site alpha).attachedHydrogens + 1 = (before.site alpha).attachedHydrogens ∧
  (molecularFormula after).hydrogen + 1 = (molecularFormula before).hydrogen ∧
  totalFormalCharge before = totalFormalCharge after + 1 ∧
  totalRadicalElectrons after = totalRadicalElectrons before ∧
  (before.site n).radicalElectrons = 1 ∧
  (after.site n).radicalElectrons = 0 ∧
  (after.site alpha).radicalElectrons = 1 ∧
  (∀ v, v ≠ n → v ≠ alpha → after.site v = before.site v)

def RadicalOxidationToIminium {V : Type} [Fintype V] [DecidableEq V]
    (before after : MolecularStructure V) (n alpha : V) : Prop :=
  (∀ v, (before.site v).element = (after.site v).element ∧
    (before.site v).attachedHydrogens = (after.site v).attachedHydrogens) ∧
  SameConnectivityExcept before after n alpha ∧
  before.bond n alpha = .single ∧ after.bond n alpha = .double ∧
  totalFormalCharge after = totalFormalCharge before + 1 ∧
  totalRadicalElectrons after + 1 = totalRadicalElectrons before ∧
  (before.site alpha).radicalElectrons = 1 ∧
  (after.site alpha).radicalElectrons = 0 ∧
  HasIminiumAt after n alpha ∧
  (∀ v, v ≠ n → v ≠ alpha → after.site v = before.site v)

def PreservesMappedElements {S P : Type}
    (source : MolecularStructure S) (product : MolecularStructure P)
    (atomMap : P → Option S) : Prop :=
  ∀ p s, atomMap p = some s → (product.site p).element = (source.site s).element

def PreservesMappedBonds {S P : Type}
    (source : MolecularStructure S) (product : MolecularStructure P)
    (atomMap : P → Option S) : Prop :=
  ∀ p q sp sq, atomMap p = some sp → atomMap q = some sq →
    product.bond p q ≠ .none → product.bond p q = source.bond sp sq

/-- Generic structural and primitive-balance contract for hydrolysis of an
iminium fragment into a secondary amine plus an aldehyde. -/
def IminiumHydrolysisCompatible
    {S A D : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (source : MolecularStructure S) (amine : MolecularStructure A)
    (aldehyde : MolecularStructure D)
    (sourceN sourceC : S) (amineN amineC1 amineC2 : A)
    (aldehydeC carbonylO substituentC : D)
    (amineMap : A → Option S) (aldehydeMap : D → Option S) : Prop :=
  HasIminiumAt source sourceN sourceC ∧
  HasSecondaryAmineAt amine amineN amineC1 amineC2 ∧
  HasAldehydeAt aldehyde aldehydeC carbonylO substituentC ∧
  PreservesMappedElements source amine amineMap ∧
  PreservesMappedElements source aldehyde aldehydeMap ∧
  PreservesMappedBonds source amine amineMap ∧
  PreservesMappedBonds source aldehyde aldehydeMap ∧
  aldehydeMap carbonylO = none ∧
  (aldehyde.site carbonylO).element = .oxygen ∧
  MolecularFormula.add (molecularFormula source)
      { carbon := 0, hydrogen := 2, nitrogen := 0, oxygen := 1 } =
    MolecularFormula.add
      (MolecularFormula.add (molecularFormula amine) (molecularFormula aldehyde))
      { carbon := 0, hydrogen := 1, nitrogen := 0, oxygen := 0 } ∧
  totalFormalCharge source =
    totalFormalCharge amine + totalFormalCharge aldehyde + 1

/-- The two unchanged hydroxyethyl arms of 5 become the two arms of 6. -/
def amineFragmentMap : DEASite → Option TEOASite
  | .nitrogen => some .nitrogen
  | .alpha1 => some .alpha2
  | .beta1 => some .beta2
  | .oxygen1 => some .oxygen2
  | .alpha2 => some .alpha3
  | .beta2 => some .beta3
  | .oxygen2 => some .oxygen3

/-- The oxidized arm becomes 7; its new carbonyl oxygen is supplied by water. -/
def aldehydeFragmentMap : GlycolaldehydeSite → Option TEOASite
  | .aldehydeCarbon => some .alpha1
  | .carbonylOxygen => none
  | .hydroxymethylCarbon => some .beta1
  | .hydroxyOxygen => some .oxygen1

/-! ## Explicit source-arrow and conservation ledgers -/

structure ChemicalSummary where
  formula : MolecularFormula
  charge : ℤ
  deriving DecidableEq, Repr

def molecularSummary {V : Type} [Fintype V] [DecidableEq V]
    (m : MolecularStructure V) : ChemicalSummary :=
  { formula := molecularFormula m, charge := totalFormalCharge m }

def protonSummary : ChemicalSummary :=
  { formula := { carbon := 0, hydrogen := 1, nitrogen := 0, oxygen := 0 }
    charge := 1 }

def electronSummary : ChemicalSummary :=
  { formula := MolecularFormula.zero, charge := -1 }

def waterSummary : ChemicalSummary :=
  { formula := { carbon := 0, hydrogen := 2, nitrogen := 0, oxygen := 1 }
    charge := 0 }

def carbonDioxideSummary : ChemicalSummary :=
  { formula := { carbon := 1, hydrogen := 0, nitrogen := 0, oxygen := 2 }
    charge := 0 }

def carbonMonoxideSummary : ChemicalSummary :=
  { formula := { carbon := 1, hydrogen := 0, nitrogen := 0, oxygen := 1 }
    charge := 0 }

def atomsInComplex {S : Type} [Fintype S]
    (summary : S → ChemicalSummary) (c : CRNT.Complex S) (e : Element) : ℕ :=
  ∑ s : S, c s * (summary s).formula.count e

def chargeInComplex {S : Type} [Fintype S]
    (summary : S → ChemicalSummary) (c : CRNT.Complex S) : ℤ :=
  ∑ s : S, (c s : ℤ) * (summary s).charge

def BalancedReaction {S : Type} [Fintype S]
    (summary : S → ChemicalSummary) (r : CRNT.Reaction S) : Prop :=
  (∀ e : Element, atomsInComplex summary r.source e = atomsInComplex summary r.target e) ∧
  chargeInComplex summary r.source = chargeInComplex summary r.target

inductive MechanismSpecies where
  | reductant2
  | intermediate3
  | intermediate4
  | intermediate5
  | product6
  | product7
  | water
  | proton
  | electron
  deriving DecidableEq, Fintype, Repr

def mechanismSummary : MechanismSpecies → ChemicalSummary
  | .reductant2 => molecularSummary structure2
  | .intermediate3 => molecularSummary structure3
  | .intermediate4 => molecularSummary structure4
  | .intermediate5 => molecularSummary structure5
  | .product6 => molecularSummary structure6
  | .product7 => molecularSummary structure7
  | .water => waterSummary
  | .proton => protonSummary
  | .electron => electronSummary

/-- Printed `2 -> 3 + e-`. -/
def step23 : CRNT.Reaction MechanismSpecies where
  source := fun
    | .reductant2 => 1
    | _ => 0
  target := fun
    | .intermediate3 | .electron => 1
    | _ => 0

/-- Printed `3 -> 4 + H+`. -/
def step34 : CRNT.Reaction MechanismSpecies where
  source := fun
    | .intermediate3 => 1
    | _ => 0
  target := fun
    | .intermediate4 | .proton => 1
    | _ => 0

/-- Printed `4 -> 5 + e-`. -/
def step45 : CRNT.Reaction MechanismSpecies where
  source := fun
    | .intermediate4 => 1
    | _ => 0
  target := fun
    | .intermediate5 | .electron => 1
    | _ => 0

/-- Printed `5 + H2O -> 6 + 7 + H+`. -/
def stepHydrolysis : CRNT.Reaction MechanismSpecies where
  source := fun
    | .intermediate5 | .water => 1
    | _ => 0
  target := fun
    | .product6 | .product7 | .proton => 1
    | _ => 0

/-- Sum of the four printed oxidation arrows. -/
def overallOxidation : CRNT.Reaction MechanismSpecies where
  source := fun
    | .reductant2 | .water => 1
    | _ => 0
  target := fun
    | .product6 | .product7 => 1
    | .proton | .electron => 2
    | _ => 0

inductive ReductionSpecies where
  | carbonDioxide
  | proton
  | electron
  | carbonMonoxide
  | water
  deriving DecidableEq, Fintype, Repr

def reductionSummary : ReductionSpecies → ChemicalSummary
  | .carbonDioxide => carbonDioxideSummary
  | .proton => protonSummary
  | .electron => electronSummary
  | .carbonMonoxide => carbonMonoxideSummary
  | .water => waterSummary

/-- The previous-part equation, derived inline from the problem-only species:
`CO2 + 2 H+ + 2 e- -> CO + H2O`. -/
def acidicCarbonDioxideReduction : CRNT.Reaction ReductionSpecies where
  source := fun
    | .carbonDioxide => 1
    | .proton | .electron => 2
    | _ => 0
  target := fun
    | .carbonMonoxide | .water => 1
    | _ => 0

def AcidicReductionSpecification : Prop :=
  BalancedReaction reductionSummary acidicCarbonDioxideReduction ∧
  acidicCarbonDioxideReduction.source .carbonDioxide = 1 ∧
  acidicCarbonDioxideReduction.source .proton = 2 ∧
  acidicCarbonDioxideReduction.source .electron = 2 ∧
  acidicCarbonDioxideReduction.target .carbonMonoxide = 1 ∧
  acidicCarbonDioxideReduction.target .water = 1

/-- Named carrier for all four source arrows and their primitive balances. -/
def SourceMechanismSpecification : Prop :=
  BalancedReaction mechanismSummary step23 ∧
  BalancedReaction mechanismSummary step34 ∧
  BalancedReaction mechanismSummary step45 ∧
  BalancedReaction mechanismSummary stepHydrolysis ∧
  BalancedReaction mechanismSummary overallOxidation ∧
  step23.source .reductant2 = 1 ∧ step23.target .intermediate3 = 1 ∧
  step23.target .electron = 1 ∧
  step34.source .intermediate3 = 1 ∧ step34.target .intermediate4 = 1 ∧
  step34.target .proton = 1 ∧
  step45.source .intermediate4 = 1 ∧ step45.target .intermediate5 = 1 ∧
  step45.target .electron = 1 ∧
  stepHydrolysis.source .intermediate5 = 1 ∧ stepHydrolysis.source .water = 1 ∧
  stepHydrolysis.target .product6 = 1 ∧ stepHydrolysis.target .product7 = 1 ∧
  stepHydrolysis.target .proton = 1

/-! ## One semantic carrier for every requested output -/

def Structure3Specification : Prop :=
  WellFormed structure3 ∧
  NoSpecifiedStereochemistry structure3 ∧
  OneElectronOxidationAt structure2 structure3 .nitrogen ∧
  HasLocalizedRadical structure3 .nitrogen ∧
  molecularFormula structure3 =
    { carbon := 6, hydrogen := 15, nitrogen := 1, oxygen := 3 } ∧
  totalFormalCharge structure3 = 1

def Structure4Specification : Prop :=
  WellFormed structure4 ∧
  NoSpecifiedStereochemistry structure4 ∧
  AlphaDeprotonation structure3 structure4 .nitrogen .alpha1 ∧
  HasLocalizedRadical structure4 .alpha1 ∧
  molecularFormula structure4 =
    { carbon := 6, hydrogen := 14, nitrogen := 1, oxygen := 3 } ∧
  totalFormalCharge structure4 = 0

def Structure5Specification : Prop :=
  WellFormed structure5 ∧
  NoSpecifiedStereochemistry structure5 ∧
  RadicalOxidationToIminium structure4 structure5 .nitrogen .alpha1 ∧
  HasIminiumAt structure5 .nitrogen .alpha1 ∧
  molecularFormula structure5 =
    { carbon := 6, hydrogen := 14, nitrogen := 1, oxygen := 3 } ∧
  totalFormalCharge structure5 = 1

def Structure6Specification : Prop :=
  WellFormed structure6 ∧
  NoSpecifiedStereochemistry structure6 ∧
  HasSecondaryAmineAt structure6 .nitrogen .alpha1 .alpha2 ∧
  molecularFormula structure6 =
    { carbon := 4, hydrogen := 11, nitrogen := 1, oxygen := 2 } ∧
  totalFormalCharge structure6 = 0 ∧
  IminiumHydrolysisCompatible structure5 structure6 structure7
    .nitrogen .alpha1 .nitrogen .alpha1 .alpha2
    .aldehydeCarbon .carbonylOxygen .hydroxymethylCarbon
    amineFragmentMap aldehydeFragmentMap

def Structure7Specification : Prop :=
  WellFormed structure7 ∧
  NoSpecifiedStereochemistry structure7 ∧
  HasAldehydeAt structure7 .aldehydeCarbon .carbonylOxygen .hydroxymethylCarbon ∧
  TollensCompatible structure7 ∧
  molecularFormula structure7 =
    { carbon := 2, hydrogen := 4, nitrogen := 0, oxygen := 2 } ∧
  totalFormalCharge structure7 = 0 ∧
  IminiumHydrolysisCompatible structure5 structure6 structure7
    .nitrogen .alpha1 .nitrogen .alpha1 .alpha2
    .aldehydeCarbon .carbonylOxygen .hydroxymethylCarbon
    amineFragmentMap aldehydeFragmentMap

/-- Raw derivation contract: inline previous-part balance, all source arrows,
and all five graph-level candidates. -/
def RawResult : Prop :=
  AcidicReductionSpecification ∧
  SourceMechanismSpecification ∧
  Structure3Specification ∧
  Structure4Specification ∧
  Structure5Specification ∧
  Structure6Specification ∧
  Structure7Specification

/-- Exact symbolic reporting contract, in requested output order 3, 4, 5, 6, 7. -/
def ReportedResult : Prop :=
  Structure3Specification ∧
  Structure4Specification ∧
  Structure5Specification ∧
  Structure6Specification ∧
  Structure7Specification

/-! The current pass creates faithful proof obligations; proof search is deferred. -/

theorem acidicReduction_from_problem : AcidicReductionSpecification := by
  unfold AcidicReductionSpecification BalancedReaction
  decide

theorem sourceMechanism_balanced : SourceMechanismSpecification := by
  unfold SourceMechanismSpecification BalancedReaction
  decide

theorem structure3_answer : Structure3Specification := by
  unfold Structure3Specification WellFormed LewisChargeAt
    NoSpecifiedStereochemistry OneElectronOxidationAt SameNuclearFramework
    HasLocalizedRadical
  decide

theorem structure4_answer : Structure4Specification := by
  unfold Structure4Specification WellFormed LewisChargeAt
    NoSpecifiedStereochemistry AlphaDeprotonation SameHeavySkeleton
    HasLocalizedRadical
  decide

theorem structure5_answer : Structure5Specification := by
  unfold Structure5Specification WellFormed LewisChargeAt
    NoSpecifiedStereochemistry RadicalOxidationToIminium SameConnectivityExcept
    HasIminiumAt
  decide

private theorem iminiumHydrolysis_compatible :
    IminiumHydrolysisCompatible structure5 structure6 structure7
      .nitrogen .alpha1 .nitrogen .alpha1 .alpha2
      .aldehydeCarbon .carbonylOxygen .hydroxymethylCarbon
      amineFragmentMap aldehydeFragmentMap := by
  unfold IminiumHydrolysisCompatible
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold HasIminiumAt
    decide
  · unfold HasSecondaryAmineAt
    decide
  · unfold HasAldehydeAt
    decide
  · unfold PreservesMappedElements
    decide
  · unfold PreservesMappedElements
    decide
  · unfold PreservesMappedBonds
    decide
  · unfold PreservesMappedBonds
    decide
  · decide
  · decide
  · decide
  · decide

theorem structure6_answer : Structure6Specification := by
  unfold Structure6Specification
  refine ⟨?_, ?_, ?_, ?_, ?_, iminiumHydrolysis_compatible⟩
  · unfold WellFormed LewisChargeAt
    decide
  · unfold NoSpecifiedStereochemistry
    decide
  · unfold HasSecondaryAmineAt
    decide
  · decide
  · decide

theorem structure7_answer : Structure7Specification := by
  unfold Structure7Specification
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, iminiumHydrolysis_compatible⟩
  · unfold WellFormed LewisChargeAt
    decide
  · unfold NoSpecifiedStereochemistry
    decide
  · unfold HasAldehydeAt
    decide
  · refine ⟨.aldehydeCarbon, .carbonylOxygen, .hydroxymethylCarbon, ?_⟩
    unfold HasAldehydeAt
    decide
  · decide
  · decide

theorem raw_result : RawResult := by
  exact ⟨acidicReduction_from_problem, sourceMechanism_balanced,
    structure3_answer, structure4_answer, structure5_answer,
    structure6_answer, structure7_answer⟩

theorem reported_result : ReportedResult := by
  exact ⟨structure3_answer, structure4_answer, structure5_answer,
    structure6_answer, structure7_answer⟩

end T8A2
end IChO2026Problems
