import IChO2026Chem

/-!
# IChO 2026 T3-A4: repeat units of COFs 3--6

The source drawing uses the same topological cell convention as its COF-1
example: a complete tritopic node and the inward half of each of three ditopic
linkers.  Thus each of the three dashed cell edges cuts two arene C--C bonds.

This file does not encode a chemical drawing as a name or a string.  Each
answer is a finite, atom-labelled molecular graph.  Hydrogens are recorded on
their attached heavy atom, and every heavy atom records element, formal charge,
radical-electron count, and stereochemical annotation.  `BoundaryCut` records
the six bonds crossed by the three dashed lines.
-/

namespace IChO2026Problems.T3A4

inductive Element where
  | C | N | O
  deriving DecidableEq, Repr

inductive Stereo where
  | none | clockwise | anticlockwise
  deriving DecidableEq, Repr

inductive BondOrder where
  | single | double | aromatic
  deriving DecidableEq, Repr

/-- An atom in the cell.  Hydrogen atoms are represented by the exact number
attached to this heavy atom. -/
structure Atom where
  id : Nat
  element : Element
  formalCharge : Int
  radicalElectrons : Nat
  attachedHydrogens : Nat
  stereo : Stereo
  deriving DecidableEq, Repr

structure Bond where
  left : Nat
  right : Nat
  order : BondOrder
  deriving DecidableEq, Repr

structure MolecularGraph where
  atoms : List Atom
  bonds : List Bond
  deriving DecidableEq, Repr

/-- Sites used by one of the three condensation linkages. -/
structure ArmSites where
  arm : Nat
  nodeAnchor : Nat
  hydroxylCarbon : Nat
  linkageCarbon : Nat
  nitrogen : Nat
  linkerJunction : Nat
  linkerNearA : Nat
  linkerNearB : Nat
  oxygen : Nat
  deriving DecidableEq, Repr

/-- One dashed cell edge cuts the arene bond from `insideAtom` to the indicated
carbon position in the outward half of the same ditopic linker. -/
structure BoundaryCut where
  arm : Nat
  insideAtom : Nat
  outsideRingPosition : Nat
  outsideElement : Element
  order : BondOrder
  deriving DecidableEq, Repr

structure RepeatUnit where
  graph : MolecularGraph
  arms : List ArmSites
  boundaryCuts : List BoundaryCut
  deriving DecidableEq, Repr

def atom (id : Nat) (element : Element) (h : Nat) : Atom :=
  { id := id
    element := element
    formalCharge := 0
    radicalElectrons := 0
    attachedHydrogens := h
    stereo := .none }

def bond (left right : Nat) (order : BondOrder) : Bond :=
  { left := left, right := right, order := order }

def Bond.connects (b : Bond) (x y : Nat) : Bool :=
  (b.left == x && b.right == y) || (b.left == y && b.right == x)

def MolecularGraph.hasAtom (g : MolecularGraph) (id : Nat) : Bool :=
  g.atoms.any fun a => a.id == id

def MolecularGraph.atomAt? (g : MolecularGraph) (id : Nat) : Option Atom :=
  g.atoms.find? fun a => a.id == id

def MolecularGraph.hasBond
    (g : MolecularGraph) (x y : Nat) (order : BondOrder) : Bool :=
  g.bonds.any fun b => b.connects x y && b.order == order

def MolecularGraph.atomHas
    (g : MolecularGraph) (id : Nat) (element : Element) (h : Nat) : Bool :=
  match g.atomAt? id with
  | some a => a.element == element && a.attachedHydrogens == h
  | none => false

inductive HydroxyPlacement where
  | onLinker
  | onNode
  deriving DecidableEq, Repr

def coreAtoms (p : HydroxyPlacement) : List Atom :=
  let oddH := if p == .onLinker then 1 else 0
  [atom 0 .C 0, atom 1 .C oddH, atom 2 .C 0,
   atom 3 .C oddH, atom 4 .C 0, atom 5 .C oddH]

def armSites (p : HydroxyPlacement) (k : Nat) : ArmSites :=
  let base := 6 + 6 * k
  { arm := k
    nodeAnchor := 2 * k
    hydroxylCarbon := if p == .onLinker then base + 3 else 2 * k + 1
    linkageCarbon := base
    nitrogen := base + 1
    linkerJunction := base + 2
    linkerNearA := base + 3
    linkerNearB := base + 4
    oxygen := base + 5 }

def armAtoms (p : HydroxyPlacement) (k : Nat) : List Atom :=
  let s := armSites p k
  let nearAH := if p == .onLinker then 0 else 1
  [ atom s.linkageCarbon .C 1,
    atom s.nitrogen .N 0,
    atom s.linkerJunction .C 0,
    atom s.linkerNearA .C nearAH,
    atom s.linkerNearB .C 1,
    atom s.oxygen .O 1 ]

def coreBonds : List Bond :=
  [bond 0 1 .aromatic, bond 1 2 .aromatic, bond 2 3 .aromatic,
   bond 3 4 .aromatic, bond 4 5 .aromatic, bond 5 0 .aromatic]

def armBonds (s : ArmSites) : List Bond :=
  [ bond s.nodeAnchor s.linkageCarbon .single,
    bond s.linkageCarbon s.nitrogen .double,
    bond s.nitrogen s.linkerJunction .single,
    bond s.linkerJunction s.linkerNearA .aromatic,
    bond s.linkerJunction s.linkerNearB .aromatic,
    bond s.hydroxylCarbon s.oxygen .single ]

def cutsForArm (s : ArmSites) : List BoundaryCut :=
  [ { arm := s.arm
      insideAtom := s.linkerNearA
      outsideRingPosition := 2
      outsideElement := .C
      order := .aromatic },
    { arm := s.arm
      insideAtom := s.linkerNearB
      outsideRingPosition := 4
      outsideElement := .C
      order := .aromatic } ]

def imineUnit (p : HydroxyPlacement) : RepeatUnit :=
  let arms := [armSites p 0, armSites p 1, armSites p 2]
  { graph :=
      { atoms := coreAtoms p ++ armAtoms p 0 ++ armAtoms p 1 ++ armAtoms p 2
        bonds := coreBonds ++ arms.flatMap armBonds }
    arms := arms
    boundaryCuts := arms.flatMap cutsForArm }

/-! ## Problem inputs transcribed from the two source monomer drawings -/

inductive RingSubstituent where
  | aldehyde | amine | hydroxy | hydrogen
  deriving DecidableEq, Repr

/-- Positions 0--5 run consecutively around the drawn benzene ring. -/
structure RingPattern where
  p0 : RingSubstituent
  p1 : RingSubstituent
  p2 : RingSubstituent
  p3 : RingSubstituent
  p4 : RingSubstituent
  p5 : RingSubstituent
  deriving DecidableEq, Repr

namespace ProblemInput

/-- 1,3,5-benzenetricarbaldehyde, the black precursor of COF-3. -/
def cof3Node : RingPattern :=
  ⟨.aldehyde, .hydrogen, .aldehyde, .hydrogen, .aldehyde, .hydrogen⟩

/-- The red 1,4-diamino-2,5-dihydroxybenzene precursor of COF-3. -/
def cof3Linker : RingPattern :=
  ⟨.amine, .hydroxy, .hydrogen, .amine, .hydroxy, .hydrogen⟩

/-- 2,4,6-trihydroxybenzene-1,3,5-tricarbaldehyde, the black precursor of COF-5. -/
def cof5Node : RingPattern :=
  ⟨.aldehyde, .hydroxy, .aldehyde, .hydroxy, .aldehyde, .hydroxy⟩

/-- p-Phenylenediamine, the red precursor of COF-5. -/
def cof5Linker : RingPattern :=
  ⟨.amine, .hydrogen, .hydrogen, .amine, .hydrogen, .hydrogen⟩

def cof3ImineStretchObserved : Bool := true
def cof4ImineStretchObserved : Bool := false
def cof4AdditionalHydrogenLoss : Nat := 6
def cof5ToCof6IsIrreversible : Bool := true
def cof6ImineStretchObserved : Bool := false

end ProblemInput

/-- Condensation of the three aldehydes at a tritopic node with halves of three
diamines.  The two branches are distinguished solely by where the source
figure places the ortho hydroxyl groups. -/
def condenseSourceMonomers
    (node linker : RingPattern) : Option RepeatUnit :=
  if node == ProblemInput.cof3Node && linker == ProblemInput.cof3Linker then
    some (imineUnit .onLinker)
  else if node == ProblemInput.cof5Node && linker == ProblemInput.cof5Linker then
    some (imineUnit .onNode)
  else
    none

def cof3RepeatUnit : RepeatUnit := imineUnit .onLinker
def cof5RepeatUnit : RepeatUnit := imineUnit .onNode

/-! ## General local reaction operations used for the two products -/

def siteHasId (sites : List ArmSites) (select : ArmSites → Nat) (id : Nat) : Bool :=
  sites.any fun s => select s == id

/-- Oxidative cyclization of each o-hydroxy imine: remove H from the phenolic
oxygen and imine carbon and close an O--C bond.  The pre-existing C=N bond is
therefore the C=N bond of a benzoxazole, not an imine C(H)=N bond. -/
def oxidativeCyclization (u : RepeatUnit) : RepeatUnit :=
  let changedAtoms := u.graph.atoms.map fun a =>
    if siteHasId u.arms (fun s => s.oxygen) a.id ||
       siteHasId u.arms (fun s => s.linkageCarbon) a.id then
      { a with attachedHydrogens := a.attachedHydrogens - 1 }
    else a
  let ringClosureBonds := u.arms.map fun s => bond s.oxygen s.linkageCarbon .single
  { u with graph := { atoms := changedAtoms, bonds := u.graph.bonds ++ ringClosureBonds } }

def cof4RepeatUnit : RepeatUnit := oxidativeCyclization cof3RepeatUnit

def isCoreBond (b : Bond) : Bool := b.left < 6 && b.right < 6

def belongsToArmBond
    (sites : List ArmSites) (left right : ArmSites → Nat) (b : Bond) : Bool :=
  sites.any fun s => b.connects (left s) (right s)

/-- Concerted bookkeeping for the enol-imine to beta-ketoenamine tautomer:
O--H becomes C=O and N--H; node--C becomes C=C; C=N becomes C--N; and the
formerly aromatic node is represented by six single ring bonds. -/
def ketoEnamineTautomerization (u : RepeatUnit) : RepeatUnit :=
  let changedAtoms := u.graph.atoms.map fun a =>
    if siteHasId u.arms (fun s => s.oxygen) a.id then
      { a with attachedHydrogens := a.attachedHydrogens - 1 }
    else if siteHasId u.arms (fun s => s.nitrogen) a.id then
      { a with attachedHydrogens := a.attachedHydrogens + 1 }
    else a
  let changedBonds := u.graph.bonds.map fun b =>
    if isCoreBond b then
      { b with order := .single }
    else if belongsToArmBond u.arms (fun s => s.nodeAnchor)
        (fun s => s.linkageCarbon) b then
      { b with order := .double }
    else if belongsToArmBond u.arms (fun s => s.linkageCarbon)
        (fun s => s.nitrogen) b then
      { b with order := .single }
    else if belongsToArmBond u.arms (fun s => s.hydroxylCarbon)
        (fun s => s.oxygen) b then
      { b with order := .double }
    else b
  { u with graph := { atoms := changedAtoms, bonds := changedBonds } }

def cof6RepeatUnit : RepeatUnit := ketoEnamineTautomerization cof5RepeatUnit

/-! ## Executable structural checks -/

structure Formula where
  carbon : Nat
  hydrogen : Nat
  nitrogen : Nat
  oxygen : Nat
  deriving DecidableEq, Repr

def elementCount (g : MolecularGraph) (e : Element) : Nat :=
  (g.atoms.filter fun a => a.element == e).length

def hydrogenCount (u : RepeatUnit) : Nat :=
  (u.graph.atoms.map Atom.attachedHydrogens).sum

def formula (u : RepeatUnit) : Formula :=
  { carbon := elementCount u.graph .C
    hydrogen := hydrogenCount u
    nitrogen := elementCount u.graph .N
    oxygen := elementCount u.graph .O }

def graphWellFormed (u : RepeatUnit) : Bool :=
  let ids := u.graph.atoms.map Atom.id
  decide ids.Nodup &&
  u.graph.bonds.all (fun b =>
    u.graph.hasAtom b.left && u.graph.hasAtom b.right && !(b.left == b.right)) &&
  u.boundaryCuts.all (fun c =>
    c.arm < u.arms.length && u.graph.hasAtom c.insideAtom &&
      c.outsideElement == .C && c.order == .aromatic)

def allAtomsNeutralClosedShellAchiral (u : RepeatUnit) : Bool :=
  u.graph.atoms.all fun a =>
    a.formalCharge == 0 && a.radicalElectrons == 0 && a.stereo == .none

def orderWeight : BondOrder → Nat
  | .single => 2
  | .double => 4
  | .aromatic => 3

def internalBondValence (u : RepeatUnit) (id : Nat) : Nat :=
  (u.graph.bonds.map fun b => if b.left == id || b.right == id then
    orderWeight b.order else 0).sum

def boundaryBondValence (u : RepeatUnit) (id : Nat) : Nat :=
  (u.boundaryCuts.map fun c => if c.insideAtom == id then
    orderWeight c.order else 0).sum

def expectedDoubledValence : Element → Nat
  | .C => 8
  | .N => 6
  | .O => 4

def atomHasValidValence (u : RepeatUnit) (a : Atom) : Bool :=
  2 * a.attachedHydrogens + internalBondValence u a.id +
      boundaryBondValence u a.id == expectedDoubledValence a.element

def allAtomsHaveValidValence (u : RepeatUnit) : Bool :=
  u.graph.atoms.all (atomHasValidValence u)

def armIsImine (u : RepeatUnit) (s : ArmSites) : Bool :=
  u.graph.atomHas s.linkageCarbon .C 1 &&
  u.graph.atomHas s.nitrogen .N 0 &&
  u.graph.hasBond s.linkageCarbon s.nitrogen .double

def armIsBenzoxazole (u : RepeatUnit) (s : ArmSites) : Bool :=
  u.graph.atomHas s.linkageCarbon .C 0 &&
  u.graph.atomHas s.oxygen .O 0 &&
  u.graph.hasBond s.linkageCarbon s.nitrogen .double &&
  u.graph.hasBond s.linkageCarbon s.oxygen .single &&
  u.graph.hasBond s.oxygen s.hydroxylCarbon .single &&
  u.graph.hasBond s.nitrogen s.linkerJunction .single &&
  u.graph.hasBond s.linkerJunction s.hydroxylCarbon .aromatic

def armIsKetoEnamine (u : RepeatUnit) (s : ArmSites) : Bool :=
  u.graph.atomHas s.linkageCarbon .C 1 &&
  u.graph.atomHas s.nitrogen .N 1 &&
  u.graph.atomHas s.oxygen .O 0 &&
  u.graph.hasBond s.nodeAnchor s.linkageCarbon .double &&
  u.graph.hasBond s.linkageCarbon s.nitrogen .single &&
  u.graph.hasBond s.hydroxylCarbon s.oxygen .double

def imineCount (u : RepeatUnit) : Nat :=
  (u.arms.filter (armIsImine u)).length

def benzoxazoleCount (u : RepeatUnit) : Nat :=
  (u.arms.filter (armIsBenzoxazole u)).length

def ketoEnamineCount (u : RepeatUnit) : Nat :=
  (u.arms.filter (armIsKetoEnamine u)).length

def carbonNitrogenDoubleBondCount (u : RepeatUnit) : Nat :=
  (u.graph.bonds.filter fun b =>
    b.order == .double &&
      ((u.graph.atomAt? b.left).map Atom.element == some .C &&
       (u.graph.atomAt? b.right).map Atom.element == some .N ||
       (u.graph.atomAt? b.left).map Atom.element == some .N &&
       (u.graph.atomAt? b.right).map Atom.element == some .C)).length

def standardBoundaryCuts : List BoundaryCut :=
  [ { arm := 0, insideAtom := 9, outsideRingPosition := 2,
      outsideElement := .C, order := .aromatic },
    { arm := 0, insideAtom := 10, outsideRingPosition := 4,
      outsideElement := .C, order := .aromatic },
    { arm := 1, insideAtom := 15, outsideRingPosition := 2,
      outsideElement := .C, order := .aromatic },
    { arm := 1, insideAtom := 16, outsideRingPosition := 4,
      outsideElement := .C, order := .aromatic },
    { arm := 2, insideAtom := 21, outsideRingPosition := 2,
      outsideElement := .C, order := .aromatic },
    { arm := 2, insideAtom := 22, outsideRingPosition := 4,
      outsideElement := .C, order := .aromatic } ]

/-! ## Final requested outputs -/

theorem cof3_repeat_unit :
    condenseSourceMonomers ProblemInput.cof3Node ProblemInput.cof3Linker =
      some cof3RepeatUnit ∧
    graphWellFormed cof3RepeatUnit = true ∧
    allAtomsHaveValidValence cof3RepeatUnit = true ∧
    allAtomsNeutralClosedShellAchiral cof3RepeatUnit = true ∧
    formula cof3RepeatUnit = ⟨18, 12, 3, 3⟩ ∧
    imineCount cof3RepeatUnit = 3 ∧
    cof3RepeatUnit.boundaryCuts = standardBoundaryCuts := by
  decide

theorem cof4_repeat_unit :
    cof4RepeatUnit = oxidativeCyclization cof3RepeatUnit ∧
    graphWellFormed cof4RepeatUnit = true ∧
    allAtomsHaveValidValence cof4RepeatUnit = true ∧
    allAtomsNeutralClosedShellAchiral cof4RepeatUnit = true ∧
    formula cof4RepeatUnit = ⟨18, 6, 3, 3⟩ ∧
    hydrogenCount cof3RepeatUnit - hydrogenCount cof4RepeatUnit =
      ProblemInput.cof4AdditionalHydrogenLoss ∧
    imineCount cof4RepeatUnit = 0 ∧
    benzoxazoleCount cof4RepeatUnit = 3 ∧
    carbonNitrogenDoubleBondCount cof4RepeatUnit = 3 ∧
    cof4RepeatUnit.boundaryCuts = standardBoundaryCuts := by
  decide

theorem cof5_repeat_unit :
    condenseSourceMonomers ProblemInput.cof5Node ProblemInput.cof5Linker =
      some cof5RepeatUnit ∧
    graphWellFormed cof5RepeatUnit = true ∧
    allAtomsHaveValidValence cof5RepeatUnit = true ∧
    allAtomsNeutralClosedShellAchiral cof5RepeatUnit = true ∧
    formula cof5RepeatUnit = ⟨18, 12, 3, 3⟩ ∧
    imineCount cof5RepeatUnit = 3 ∧
    cof5RepeatUnit.boundaryCuts = standardBoundaryCuts := by
  decide

theorem cof6_repeat_unit :
    cof6RepeatUnit = ketoEnamineTautomerization cof5RepeatUnit ∧
    ProblemInput.cof5ToCof6IsIrreversible = true ∧
    graphWellFormed cof6RepeatUnit = true ∧
    allAtomsHaveValidValence cof6RepeatUnit = true ∧
    allAtomsNeutralClosedShellAchiral cof6RepeatUnit = true ∧
    formula cof6RepeatUnit = formula cof5RepeatUnit ∧
    imineCount cof6RepeatUnit = 0 ∧
    ketoEnamineCount cof6RepeatUnit = 3 ∧
    carbonNitrogenDoubleBondCount cof6RepeatUnit = 0 ∧
    cof6RepeatUnit.boundaryCuts = standardBoundaryCuts := by
  decide

/-- The source spectroscopic and elemental-analysis observations discriminate
the derived products exactly as stated in the question. -/
theorem products_match_problem_observations :
    (imineCount cof3RepeatUnit > 0) = ProblemInput.cof3ImineStretchObserved ∧
    (imineCount cof4RepeatUnit > 0) = ProblemInput.cof4ImineStretchObserved ∧
    hydrogenCount cof3RepeatUnit - hydrogenCount cof4RepeatUnit =
      ProblemInput.cof4AdditionalHydrogenLoss ∧
    (imineCount cof6RepeatUnit > 0) = ProblemInput.cof6ImineStretchObserved := by
  decide

#print axioms cof3_repeat_unit
#print axioms cof4_repeat_unit
#print axioms cof5_repeat_unit
#print axioms cof6_repeat_unit
#print axioms products_match_problem_observations

end IChO2026Problems.T3A4
