import Mathlib

/-!
# IChO 2026, theory problem 5.2: cardiolipin PL1 and monoanion Y

The problem permits `R` as an abbreviation for each (identical) hydrocarbon
part of a fatty-acid residue.  Accordingly, `Element.residueR` is a labelled
pseudoatom.  Every atom outside those four permitted `R` abbreviations is
represented explicitly, including carbon-bound hydrogens.  The two hydrogen
bonds in `Y` are deliberately kept separate from its covalent bonds.

The source data and the derived candidates are separated below.  In
particular, `printedInventory n` retains the source's unknown `n`, while
`derivedInventory`, `pl1R`, `pl1S`, `yLeft`, and `yRight` are constructed
values supported by later proofs.
-/

namespace IChO2026Problems.T5A2

inductive Side where
  | left | right
  deriving DecidableEq, Repr, Fintype

inductive Glycerol where
  | leftOuter | central | rightOuter
  deriving DecidableEq, Repr, Fintype

inductive Position where
  | one | two | three
  deriving DecidableEq, Repr, Fintype

inductive HSlot where
  | first | second
  deriving DecidableEq, Repr, Fintype

inductive AcylSite where
  | leftOne | leftTwo | rightTwo | rightThree
  deriving DecidableEq, Repr, Fintype

/-- Atom names for the whole cardiolipin outside the internal atoms hidden by
the problem-authorized `R` abbreviation. -/
inductive AtomId where
  | glycerolCarbon (g : Glycerol) (p : Position)
  | glycerolOxygen (g : Glycerol) (p : Position)
  | carbonHydrogen (g : Glycerol) (p : Position) (h : HSlot)
  | phosphorus (s : Side)
  | phosphateOxo (s : Side)
  | phosphateAcidO (s : Side)
  | phosphateHydrogen (s : Side)
  | carbonylCarbon (a : AcylSite)
  | carbonylOxygen (a : AcylSite)
  | residue (a : AcylSite)
  | centralHydroxylHydrogen
  deriving DecidableEq, Repr, Fintype

inductive Element where
  | H | C | O | P
  | residueR
  deriving DecidableEq, Repr

inductive BondOrder where
  | single | double
  deriving DecidableEq, Repr

def BondOrder.weight : BondOrder → ℕ
  | .single => 1
  | .double => 2

structure AtomState where
  element : Element
  formalCharge : ℤ
  radicalElectrons : ℕ
  deriving DecidableEq, Repr

structure Bond where
  atom₁ : AtomId
  atom₂ : AtomId
  order : BondOrder
  deriving DecidableEq, Repr

structure HydrogenBond where
  donorO : AtomId
  donorH : AtomId
  acceptorO : AtomId
  deriving DecidableEq, Repr

inductive Configuration where
  | R | S
  deriving DecidableEq, Repr

def Configuration.flip : Configuration → Configuration
  | .R => .S
  | .S => .R

/-- `neutral` is PL1.  The other two cases are the two symmetry-related
proton-localized canonical forms used to depict monoanion Y. -/
inductive Protonation where
  | neutral | leftDeprotonated | rightDeprotonated
  deriving DecidableEq, Repr

@[ext] structure ChemicalStructure where
  protonation : Protonation
  peripheralStereo : Side → Configuration

/-- A complete fragment inventory.  A type-a fragment is the hydrogen cap
shown in the source figure; the OH on each phosphate is already part of a
type-b fragment. -/
structure FragmentInventory where
  hydrogenCaps : ℕ
  phosphates : ℕ
  glycerols : ℕ
  acylResidues : ℕ
  deriving DecidableEq, Repr

/-- The problem prints the hydrogen count symbolically as `n`; it is therefore
an argument here, not assumed source data. -/
def printedInventory (n : ℕ) : FragmentInventory where
  hydrogenCaps := n
  phosphates := 2
  glycerols := 3
  acylResidues := 4

/-- Each type-c glycerol supplies three oxygen ports.  Each type-d acyl
fragment uses one, each type-b phosphate has two connector bonds and therefore
uses two, and every remaining oxygen port must be capped by one type-a H.
This equation is obtained directly from the fragment drawings. -/
def closesAllGlycerolOxygenPorts (n : ℕ) : Prop :=
  3 * (printedInventory n).glycerols =
    (printedInventory n).acylResidues +
    2 * (printedInventory n).phosphates +
    (printedInventory n).hydrogenCaps

/-- The inventory obtained after solving, rather than assuming, the port
balance. -/
def derivedInventory : FragmentInventory := printedInventory 1

def sideSwap : Side → Side
  | .left => .right
  | .right => .left

def positionSwap : Position → Position
  | .one => .three
  | .two => .two
  | .three => .one

def glycerolSwap : Glycerol → Glycerol
  | .leftOuter => .rightOuter
  | .central => .central
  | .rightOuter => .leftOuter

def acylSwap : AcylSite → AcylSite
  | .leftOne => .rightThree
  | .leftTwo => .rightTwo
  | .rightTwo => .leftTwo
  | .rightThree => .leftOne

/-- Reflection in the plane that exchanges the two halves of the connectivity
diagram.  Spatial reflection also flips every tetrahedral configuration; that
second operation is implemented by `mirror`. -/
def reflectAtom : AtomId → AtomId
  | .glycerolCarbon g p => .glycerolCarbon (glycerolSwap g) (positionSwap p)
  | .glycerolOxygen g p => .glycerolOxygen (glycerolSwap g) (positionSwap p)
  | .carbonHydrogen g p h =>
      .carbonHydrogen (glycerolSwap g) (positionSwap p) h
  | .phosphorus s => .phosphorus (sideSwap s)
  | .phosphateOxo s => .phosphateOxo (sideSwap s)
  | .phosphateAcidO s => .phosphateAcidO (sideSwap s)
  | .phosphateHydrogen s => .phosphateHydrogen (sideSwap s)
  | .carbonylCarbon a => .carbonylCarbon (acylSwap a)
  | .carbonylOxygen a => .carbonylOxygen (acylSwap a)
  | .residue a => .residue (acylSwap a)
  | .centralHydroxylHydrogen => .centralHydroxylHydrogen

def reflectProtonation : Protonation → Protonation
  | .neutral => .neutral
  | .leftDeprotonated => .rightDeprotonated
  | .rightDeprotonated => .leftDeprotonated

def mirror (m : ChemicalStructure) : ChemicalStructure where
  protonation := reflectProtonation m.protonation
  peripheralStereo := fun s => (m.peripheralStereo (sideSwap s)).flip

/-- The requested enantiomer.  Choosing `(S,S)` instead would give the other
valid answer. -/
def pl1R : ChemicalStructure where
  protonation := .neutral
  peripheralStereo := fun _ => .R

def pl1S : ChemicalStructure := mirror pl1R

def mesoRS : ChemicalStructure where
  protonation := .neutral
  peripheralStereo
    | .left => .R
    | .right => .S

def mesoSR : ChemicalStructure where
  protonation := .neutral
  peripheralStereo
    | .left => .S
    | .right => .R

def yLeft : ChemicalStructure where
  protonation := .leftDeprotonated
  peripheralStereo := pl1R.peripheralStereo

def yRight : ChemicalStructure where
  protonation := .rightDeprotonated
  peripheralStereo := pl1R.peripheralStereo

def AtomId.present (p : Protonation) : AtomId → Bool
  | .carbonHydrogen _ .two .second => false
  | .phosphateHydrogen .left => p != .leftDeprotonated
  | .phosphateHydrogen .right => p != .rightDeprotonated
  | _ => true

def AtomId.element : AtomId → Element
  | .glycerolCarbon _ _ | .carbonylCarbon _ => .C
  | .glycerolOxygen _ _ | .phosphateOxo _ | .phosphateAcidO _
      | .carbonylOxygen _ => .O
  | .carbonHydrogen _ _ _ | .phosphateHydrogen _
      | .centralHydroxylHydrogen => .H
  | .phosphorus _ => .P
  | .residue _ => .residueR

def AtomId.formalCharge (p : Protonation) : AtomId → ℤ
  | .phosphateAcidO .left => if p = .leftDeprotonated then -1 else 0
  | .phosphateAcidO .right => if p = .rightDeprotonated then -1 else 0
  | _ => 0

def atomState? (m : ChemicalStructure) (a : AtomId) : Option AtomState :=
  if a.present m.protonation then
    some { element := a.element,
           formalCharge := a.formalCharge m.protonation,
           radicalElectrons := 0 }
  else none

def mkBond (a b : AtomId) (order : BondOrder := .single) : Bond :=
  { atom₁ := a, atom₂ := b, order := order }

def glycerolBondsFor (g : Glycerol) : List Bond :=
  [ mkBond (.glycerolCarbon g .one) (.glycerolCarbon g .two),
    mkBond (.glycerolCarbon g .two) (.glycerolCarbon g .three),
    mkBond (.glycerolCarbon g .one) (.glycerolOxygen g .one),
    mkBond (.glycerolCarbon g .two) (.glycerolOxygen g .two),
    mkBond (.glycerolCarbon g .three) (.glycerolOxygen g .three),
    mkBond (.glycerolCarbon g .one) (.carbonHydrogen g .one .first),
    mkBond (.glycerolCarbon g .one) (.carbonHydrogen g .one .second),
    mkBond (.glycerolCarbon g .two) (.carbonHydrogen g .two .first),
    mkBond (.glycerolCarbon g .three) (.carbonHydrogen g .three .first),
    mkBond (.glycerolCarbon g .three) (.carbonHydrogen g .three .second) ]

def glycerolBonds : List Bond :=
  glycerolBondsFor .leftOuter ++
  glycerolBondsFor .central ++
  glycerolBondsFor .rightOuter

def phosphateBonds : List Bond :=
  [ mkBond (.phosphorus .left) (.phosphateOxo .left) .double,
    mkBond (.phosphorus .left) (.phosphateAcidO .left),
    mkBond (.phosphorus .left) (.glycerolOxygen .leftOuter .three),
    mkBond (.phosphorus .left) (.glycerolOxygen .central .one),
    mkBond (.phosphorus .right) (.phosphateOxo .right) .double,
    mkBond (.phosphorus .right) (.phosphateAcidO .right),
    mkBond (.phosphorus .right) (.glycerolOxygen .central .three),
    mkBond (.phosphorus .right) (.glycerolOxygen .rightOuter .one) ]

def acidHydrogenBonds : Protonation → List Bond
  | .neutral =>
      [ mkBond (.phosphateAcidO .left) (.phosphateHydrogen .left),
        mkBond (.phosphateAcidO .right) (.phosphateHydrogen .right) ]
  | .leftDeprotonated =>
      [ mkBond (.phosphateAcidO .right) (.phosphateHydrogen .right) ]
  | .rightDeprotonated =>
      [ mkBond (.phosphateAcidO .left) (.phosphateHydrogen .left) ]

def acylBondsFor : AcylSite → List Bond
  | .leftOne =>
      [ mkBond (.carbonylCarbon .leftOne) (.carbonylOxygen .leftOne) .double,
        mkBond (.carbonylCarbon .leftOne) (.residue .leftOne),
        mkBond (.carbonylCarbon .leftOne) (.glycerolOxygen .leftOuter .one) ]
  | .leftTwo =>
      [ mkBond (.carbonylCarbon .leftTwo) (.carbonylOxygen .leftTwo) .double,
        mkBond (.carbonylCarbon .leftTwo) (.residue .leftTwo),
        mkBond (.carbonylCarbon .leftTwo) (.glycerolOxygen .leftOuter .two) ]
  | .rightTwo =>
      [ mkBond (.carbonylCarbon .rightTwo) (.carbonylOxygen .rightTwo) .double,
        mkBond (.carbonylCarbon .rightTwo) (.residue .rightTwo),
        mkBond (.carbonylCarbon .rightTwo) (.glycerolOxygen .rightOuter .two) ]
  | .rightThree =>
      [ mkBond (.carbonylCarbon .rightThree) (.carbonylOxygen .rightThree) .double,
        mkBond (.carbonylCarbon .rightThree) (.residue .rightThree),
        mkBond (.carbonylCarbon .rightThree) (.glycerolOxygen .rightOuter .three) ]

def acylBonds : List Bond :=
  acylBondsFor .leftOne ++ acylBondsFor .leftTwo ++
  acylBondsFor .rightTwo ++ acylBondsFor .rightThree

def covalentBonds (m : ChemicalStructure) : List Bond :=
  glycerolBonds ++ phosphateBonds ++ acidHydrogenBonds m.protonation ++
  acylBonds ++
  [mkBond (.glycerolOxygen .central .two) .centralHydroxylHydrogen]

def Bond.connects (b : Bond) (a₁ a₂ : AtomId) : Bool :=
  (b.atom₁ = a₁ && b.atom₂ = a₂) || (b.atom₁ = a₂ && b.atom₂ = a₁)

def bonded (m : ChemicalStructure) (a₁ a₂ : AtomId) (o : BondOrder) : Bool :=
  (covalentBonds m).any fun b => b.connects a₁ a₂ && b.order = o

/-- The defining cardiolipin assembly at its fragment-connection ports: two
diacylated peripheral glycerols are connected through two phosphate diesters
to the terminal oxygens of a central glycerol, whose middle oxygen is OH.
This is the standard constitutional meaning of the source's classification of
PL1 as a cardiolipin, stated independently of either candidate value. -/
def HasCardiolipinConnectivity (m : ChemicalStructure) : Prop :=
  bonded m (.phosphorus .left) (.glycerolOxygen .leftOuter .three) .single = true ∧
  bonded m (.phosphorus .left) (.glycerolOxygen .central .one) .single = true ∧
  bonded m (.phosphorus .right) (.glycerolOxygen .central .three) .single = true ∧
  bonded m (.phosphorus .right) (.glycerolOxygen .rightOuter .one) .single = true ∧
  bonded m (.carbonylCarbon .leftOne) (.glycerolOxygen .leftOuter .one) .single = true ∧
  bonded m (.carbonylCarbon .leftTwo) (.glycerolOxygen .leftOuter .two) .single = true ∧
  bonded m (.carbonylCarbon .rightTwo) (.glycerolOxygen .rightOuter .two) .single = true ∧
  bonded m (.carbonylCarbon .rightThree) (.glycerolOxygen .rightOuter .three) .single = true ∧
  bonded m (.glycerolOxygen .central .two) .centralHydroxylHydrogen .single = true

/-- A finite, executable certificate that reflection carries every bond of
`m₁` to a bond of the same order in `m₂`, and conversely. -/
def ReflectsConnectivity (m₁ m₂ : ChemicalStructure) : Prop :=
  ((covalentBonds m₁).all fun b =>
      (covalentBonds m₂).any fun b' =>
        b'.connects (reflectAtom b.atom₁) (reflectAtom b.atom₂) &&
          b'.order = b.order) = true ∧
  ((covalentBonds m₂).all fun b =>
      (covalentBonds m₁).any fun b' =>
        b'.connects (reflectAtom b.atom₁) (reflectAtom b.atom₂) &&
          b'.order = b.order) = true

def bondValence (m : ChemicalStructure) (a : AtomId) : ℕ :=
  (covalentBonds m).foldl
    (fun total b => if b.atom₁ = a || b.atom₂ = a
      then total + b.order.weight else total) 0

def expectedValence (m : ChemicalStructure) (a : AtomId) : ℕ :=
  match a.element with
  | .H => 1
  | .C => 4
  | .O => if a.formalCharge m.protonation = -1 then 1 else 2
  | .P => 5
  | .residueR => 1

def countElement (m : ChemicalStructure) (e : Element) : ℕ :=
  (Finset.univ.filter fun a : AtomId =>
      a.present m.protonation && a.element = e).card

def netCharge (m : ChemicalStructure) : ℤ :=
  ∑ a : AtomId, if a.present m.protonation
    then a.formalCharge m.protonation else 0

def noPeroxideBond (m : ChemicalStructure) : Prop :=
  ∀ b ∈ covalentBonds m,
    ¬(b.atom₁.element = .O ∧ b.atom₂.element = .O)

def closedShell (m : ChemicalStructure) : Prop :=
  ∀ a state, atomState? m a = some state → state.radicalElectrons = 0

def validValences (m : ChemicalStructure) : Prop :=
  ∀ a, a.present m.protonation → bondValence m a = expectedValence m a

def hasCardiolipinInventory (m : ChemicalStructure) : Prop :=
  countElement m .C = 13 ∧
  countElement m .O = 17 ∧
  countElement m .P = 2 ∧
  countElement m .residueR = 4

def samePeripheralConfiguration (m : ChemicalStructure) : Prop :=
  m.peripheralStereo .left = m.peripheralStereo .right

def IsChiral (m : ChemicalStructure) : Prop := mirror m ≠ m

def IsEnantiomerPair (m₁ m₂ : ChemicalStructure) : Prop :=
  mirror m₁ = m₂ ∧ m₁ ≠ m₂

/-- The two noncovalent contacts in the left-deprotonated drawing of Y:

`P_left-O⁻ ··· H-O_central ··· H-O-P_right`.
-/
def hydrogenBonds : Protonation → List HydrogenBond
  | .neutral => []
  | .leftDeprotonated =>
      [ { donorO := .glycerolOxygen .central .two,
          donorH := .centralHydroxylHydrogen,
          acceptorO := .phosphateAcidO .left },
        { donorO := .phosphateAcidO .right,
          donorH := .phosphateHydrogen .right,
          acceptorO := .glycerolOxygen .central .two } ]
  | .rightDeprotonated =>
      [ { donorO := .glycerolOxygen .central .two,
          donorH := .centralHydroxylHydrogen,
          acceptorO := .phosphateAcidO .right },
        { donorO := .phosphateAcidO .left,
          donorH := .phosphateHydrogen .left,
          acceptorO := .glycerolOxygen .central .two } ]

def validHydrogenBond (m : ChemicalStructure) (h : HydrogenBond) : Prop :=
  h.donorO.element = .O ∧ h.donorH.element = .H ∧
  h.acceptorO.element = .O ∧
  bonded m h.donorO h.donorH .single = true ∧
  h.donorO ≠ h.acceptorO

def IsStabilizedMonoanion (m : ChemicalStructure) : Prop :=
  netCharge m = -1 ∧
  countElement m .H = 17 ∧
  (hydrogenBonds m.protonation).length = 2 ∧
  (∀ h ∈ hydrogenBonds m.protonation, validHydrogenBond m h)

/-- The printed fragment counts and closure of every glycerol oxygen port force
exactly one type-a hydrogen cap. -/
theorem source_constraints_force_n_eq_one {n : ℕ}
    (h : closesAllGlycerolOxygenPorts n) : n = 1 := by
  change 3 * 3 = 4 + 2 * 2 + n at h
  omega

/-- Hence the preceding parity answer follows for every assembly satisfying
the source-derived port equation; it is not supplied as a premise. -/
theorem preceding_part_n_is_odd {n : ℕ}
    (h : closesAllGlycerolOxygenPorts n) : Odd n := by
  rw [source_constraints_force_n_eq_one h]
  exact ⟨0, rfl⟩

theorem pl1R_closes_all_fragment_ports :
    closesAllGlycerolOxygenPorts derivedInventory.hydrogenCaps := by
  change 3 * 3 = 4 + 2 * 2 + 1
  decide

theorem pl1R_inventory : hasCardiolipinInventory pl1R := by
  change
    countElement pl1R .C = 13 ∧ countElement pl1R .O = 17 ∧
    countElement pl1R .P = 2 ∧ countElement pl1R .residueR = 4
  decide

theorem pl1R_hydrogen_count : countElement pl1R .H = 18 := by
  decide

theorem pl1R_neutral : netCharge pl1R = 0 := by
  decide

theorem pl1R_all_formal_charges_zero (a : AtomId) :
    a.formalCharge pl1R.protonation = 0 := by
  revert a
  decide

theorem pl1R_validValences : validValences pl1R := by
  change ∀ a : AtomId,
    a.present pl1R.protonation → bondValence pl1R a = expectedValence pl1R a
  decide

theorem pl1R_cardiolipin_connectivity : HasCardiolipinConnectivity pl1R := by
  unfold HasCardiolipinConnectivity
  decide

theorem pl1R_no_peroxide : noPeroxideBond pl1R := by
  change ∀ b ∈ covalentBonds pl1R,
    ¬(b.atom₁.element = .O ∧ b.atom₂.element = .O)
  decide

theorem pl1R_closed_shell : closedShell pl1R := by
  intro a state h
  simp only [atomState?] at h
  split at h
  · cases h
    rfl
  · simp at h

theorem pl1R_same_configuration : samePeripheralConfiguration pl1R := by
  rfl

theorem mirror_pl1R_eq_pl1S : mirror pl1R = pl1S := by
  rfl

theorem pl1R_ne_pl1S : pl1R ≠ pl1S := by
  intro h
  have hs := congrArg (fun m => m.peripheralStereo .left) h
  simp [pl1R, pl1S, mirror, sideSwap, Configuration.flip] at hs

theorem pl1R_is_chiral : IsChiral pl1R := by
  intro h
  exact pl1R_ne_pl1S h.symm

theorem pl1R_pl1S_enantiomers : IsEnantiomerPair pl1R pl1S := by
  exact ⟨mirror_pl1R_eq_pl1S, pl1R_ne_pl1S⟩

/-- In contrast with `(R,R)`, either mixed peripheral assignment is unchanged
by spatial reflection plus exchange of the identical halves: it is meso. -/
theorem mixed_diastereomers_are_achiral :
    mirror mesoRS = mesoRS ∧ mirror mesoSR = mesoSR := by
  constructor
  · apply ChemicalStructure.ext
    · rfl
    · funext s
      cases s <;> rfl
  · apply ChemicalStructure.ext
    · rfl
    · funext s
      cases s <;> rfl

/-- Reflection preserves every neutral covalent bond and its order.  Thus the
difference between `pl1R` and `pl1S` is genuinely stereochemical, not a change
of constitution. -/
theorem reflection_preserves_pl1_connectivity
    : ReflectsConnectivity pl1R pl1S := by
  unfold ReflectsConnectivity
  decide

/-- Complete formal certificate for the requested PL1 drawing. -/
theorem structure_pl1 :
    closesAllGlycerolOxygenPorts derivedInventory.hydrogenCaps ∧
    hasCardiolipinInventory pl1R ∧
    countElement pl1R .H = 18 ∧
    netCharge pl1R = 0 ∧
    HasCardiolipinConnectivity pl1R ∧
    validValences pl1R ∧
    noPeroxideBond pl1R ∧
    closedShell pl1R ∧
    samePeripheralConfiguration pl1R ∧
    IsEnantiomerPair pl1R pl1S ∧
    ReflectsConnectivity pl1R pl1S := by
  exact ⟨pl1R_closes_all_fragment_ports, pl1R_inventory,
    pl1R_hydrogen_count, pl1R_neutral,
    pl1R_cardiolipin_connectivity, pl1R_validValences,
    pl1R_no_peroxide, pl1R_closed_shell,
    pl1R_same_configuration, pl1R_pl1S_enantiomers,
    reflection_preserves_pl1_connectivity⟩

theorem yLeft_inventory : hasCardiolipinInventory yLeft := by
  change
    countElement yLeft .C = 13 ∧ countElement yLeft .O = 17 ∧
    countElement yLeft .P = 2 ∧ countElement yLeft .residueR = 4
  decide

theorem yLeft_charge_localization (a : AtomId) :
    a.formalCharge yLeft.protonation =
      if a = .phosphateAcidO .left then -1 else 0 := by
  revert a
  decide

theorem yLeft_validValences : validValences yLeft := by
  change ∀ a : AtomId,
    a.present yLeft.protonation → bondValence yLeft a = expectedValence yLeft a
  decide

theorem yLeft_cardiolipin_connectivity : HasCardiolipinConnectivity yLeft := by
  unfold HasCardiolipinConnectivity
  decide

theorem yLeft_no_peroxide : noPeroxideBond yLeft := by
  change ∀ b ∈ covalentBonds yLeft,
    ¬(b.atom₁.element = .O ∧ b.atom₂.element = .O)
  decide

theorem yLeft_closed_shell : closedShell yLeft := by
  intro a state h
  simp only [atomState?] at h
  split at h
  · cases h
    rfl
  · simp at h

theorem yLeft_stabilized_monoanion : IsStabilizedMonoanion yLeft := by
  refine ⟨by decide, by decide, rfl, ?_⟩
  intro h hh
  simp only [yLeft, hydrogenBonds, List.mem_cons, List.not_mem_nil,
    or_false] at hh
  rcases hh with rfl | rfl <;> (unfold validHydrogenBond; decide)

theorem yRight_stabilized_monoanion : IsStabilizedMonoanion yRight := by
  refine ⟨by decide, by decide, rfl, ?_⟩
  intro h hh
  simp only [yRight, hydrogenBonds, List.mem_cons, List.not_mem_nil,
    or_false] at hh
  rcases hh with rfl | rfl <;> (unfold validHydrogenBond; decide)

/-- The two displayed proton-localization forms are symmetry-equivalent. -/
theorem y_canonical_forms_reflected_atom_states (a : AtomId) :
    atomState? yLeft a = atomState? yRight (reflectAtom a) := by
  revert a
  decide

theorem y_canonical_forms_reflected_connectivity
    : ReflectsConnectivity yLeft yRight := by
  unfold ReflectsConnectivity
  decide

/-- Thermodynamic data used only for the qualitative explanation of the pKa
ordering.  `extraYStability > 0` is precisely the problem-stated stabilization
of monoanion Y.  The two equations are the standard relation
`ΔG° = R*T*ln(10)*pKa`; the last equation states that losing the stabilizing
network adds this positive free-energy cost to the second deprotonation. -/
structure DeprotonationThermodynamics where
  R : ℝ
  T : ℝ
  pKa1 : ℝ
  pKa2 : ℝ
  deltaG1 : ℝ
  deltaG2 : ℝ
  extraYStability : ℝ
  positiveRT : 0 < R * T
  positiveStabilization : 0 < extraYStability
  firstLaw : deltaG1 = R * T * Real.log 10 * pKa1
  secondLaw : deltaG2 = R * T * Real.log 10 * pKa2
  lossOfYNetwork : deltaG2 = deltaG1 + extraYStability

theorem positive_stabilization_raises_second_pKa
    (d : DeprotonationThermodynamics) : d.pKa1 < d.pKa2 := by
  have hlog : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have hk : 0 < d.R * d.T * Real.log 10 := mul_pos d.positiveRT hlog
  have henergy : d.deltaG1 < d.deltaG2 := by
    rw [d.lossOfYNetwork]
    linarith [d.positiveStabilization]
  rw [d.firstLaw, d.secondLaw] at henergy
  nlinarith

/-- Complete formal certificate for Y and for how its two hydrogen bonds make
the second deprotonation less favorable (hence `pKa2 > pKa1`). -/
theorem structure_y (d : DeprotonationThermodynamics) :
    hasCardiolipinInventory yLeft ∧
    IsStabilizedMonoanion yLeft ∧
    IsStabilizedMonoanion yRight ∧
    HasCardiolipinConnectivity yLeft ∧
    validValences yLeft ∧
    noPeroxideBond yLeft ∧
    closedShell yLeft ∧
    ReflectsConnectivity yLeft yRight ∧
    d.pKa1 < d.pKa2 := by
  exact ⟨yLeft_inventory, yLeft_stabilized_monoanion,
    yRight_stabilized_monoanion,
    yLeft_cardiolipin_connectivity, yLeft_validValences,
    yLeft_no_peroxide, yLeft_closed_shell,
    y_canonical_forms_reflected_connectivity,
    positive_stabilization_raises_second_pKa d⟩

#print axioms structure_pl1
#print axioms structure_y

end IChO2026Problems.T5A2
