import Mathlib

/-!
# IChO 2026, theory problem 6.5: structures F--L

This file formalizes the constitutional structures in the printed synthesis.
The answer is not stored as a name or a SMILES string: `MolecularGraph` records
every heavy atom, the number of hydrogens on that atom, every bond and bond
order, formal charge, radical count, and any specified stereochemistry.

The source scheme itself is represented by `problemStartingMaterial`, the two
aryllithium fragments, and the sequence of `Step`s.  The reaction rules are
separate, reusable rewrites of a chain of ring units.  Each final theorem says
that evaluating the appropriate prefix of the source scheme gives the claimed
atom-level graph, and also checks its formula and graph/valence invariants.
-/

namespace IChO2026Problems.T6A5

/-! ## Atom-level molecular graphs -/

inductive Element
  | C | O | Si | Br
  deriving DecidableEq, Repr, BEq

inductive BondOrder
  | single | double
  deriving DecidableEq, Repr, BEq

def BondOrder.valence : BondOrder → Nat
  | .single => 1
  | .double => 2

/-- The problem gives no wedges, dashes, E/Z labels, or R/S labels for F--L. -/
inductive AtomStereo
  | unspecified | R | S
  deriving DecidableEq, Repr, BEq

inductive BondStereo
  | unspecified | wedge | dash | E | Z
  deriving DecidableEq, Repr, BEq

/-- A stable identifier: `component` names a ring or substituent and `position`
names an atom within it. -/
structure AtomId where
  component : String
  position : Nat
  deriving DecidableEq, Repr, BEq

structure Atom where
  id : AtomId
  element : Element
  /-- Hydrogens suppressed by ordinary skeletal notation, stored explicitly. -/
  hydrogens : Nat
  formalCharge : Int
  radicalElectrons : Nat
  stereo : AtomStereo
  deriving DecidableEq, Repr, BEq

structure Bond where
  a : AtomId
  b : AtomId
  order : BondOrder
  stereo : BondStereo
  deriving DecidableEq, Repr, BEq

structure MolecularGraph where
  atoms : List Atom
  bonds : List Bond
  deriving DecidableEq, Repr, BEq

def MolecularGraph.empty : MolecularGraph := ⟨[], []⟩

def MolecularGraph.append (g h : MolecularGraph) : MolecularGraph :=
  ⟨g.atoms ++ h.atoms, g.bonds ++ h.bonds⟩

def MolecularGraph.ofBond (b : Bond) : MolecularGraph := ⟨[], [b]⟩

def atomId (component : String) (position : Nat) : AtomId :=
  ⟨component, position⟩

def neutralAtom (component : String) (position : Nat)
    (element : Element) (hydrogens : Nat) : Atom :=
  { id := atomId component position
    element := element
    hydrogens := hydrogens
    formalCharge := 0
    radicalElectrons := 0
    stereo := .unspecified }

def plainBond (a b : AtomId) (order : BondOrder := .single) : Bond :=
  { a := a, b := b, order := order, stereo := .unspecified }

def joinGraphs (graphs : List MolecularGraph) : MolecularGraph :=
  graphs.foldl MolecularGraph.append MolecularGraph.empty

/-! ## Exact fragments used by the scheme -/

/-- A para-disubstituted phenylene ring. Positions 0 and 3 are its two
attachment sites. The alternating bonds are one Kekule representation. -/
def phenylene (tag : String) : MolecularGraph :=
  { atoms :=
      [ neutralAtom tag 0 .C 0, neutralAtom tag 1 .C 1,
        neutralAtom tag 2 .C 1, neutralAtom tag 3 .C 0,
        neutralAtom tag 4 .C 1, neutralAtom tag 5 .C 1 ]
    bonds :=
      [ plainBond (atomId tag 0) (atomId tag 1) .double,
        plainBond (atomId tag 1) (atomId tag 2) .single,
        plainBond (atomId tag 2) (atomId tag 3) .double,
        plainBond (atomId tag 3) (atomId tag 4) .single,
        plainBond (atomId tag 4) (atomId tag 5) .double,
        plainBond (atomId tag 5) (atomId tag 0) .single ] }

/-- The 1,4-cyclohexadiene carbon skeleton of a masked phenylene unit.
Positions 0 and 3 are saturated carbons; each receives an O substituent and
one connection to the neighboring ring unit. -/
def dieneRing (tag : String) : MolecularGraph :=
  { atoms :=
      [ neutralAtom tag 0 .C 0, neutralAtom tag 1 .C 1,
        neutralAtom tag 2 .C 1, neutralAtom tag 3 .C 0,
        neutralAtom tag 4 .C 1, neutralAtom tag 5 .C 1 ]
    bonds :=
      [ plainBond (atomId tag 0) (atomId tag 1) .single,
        plainBond (atomId tag 1) (atomId tag 2) .double,
        plainBond (atomId tag 2) (atomId tag 3) .single,
        plainBond (atomId tag 3) (atomId tag 4) .single,
        plainBond (atomId tag 4) (atomId tag 5) .double,
        plainBond (atomId tag 5) (atomId tag 0) .single ] }

def hydroxyOn (parent : AtomId) (tag : String) : MolecularGraph :=
  { atoms := [neutralAtom tag 0 .O 1]
    bonds := [plainBond parent (atomId tag 0)] }

def carbonylOn (parent : AtomId) (tag : String) : MolecularGraph :=
  { atoms := [neutralAtom tag 0 .O 0]
    bonds := [plainBond parent (atomId tag 0) .double] }

/-- OSiEt3, including all six carbons and their atom-local hydrogens. -/
def tesEtherOn (parent : AtomId) (tag : String) : MolecularGraph :=
  { atoms :=
      [ neutralAtom tag 0 .O 0, neutralAtom tag 1 .Si 0,
        neutralAtom tag 2 .C 2, neutralAtom tag 3 .C 3,
        neutralAtom tag 4 .C 2, neutralAtom tag 5 .C 3,
        neutralAtom tag 6 .C 2, neutralAtom tag 7 .C 3 ]
    bonds :=
      [ plainBond parent (atomId tag 0),
        plainBond (atomId tag 0) (atomId tag 1),
        plainBond (atomId tag 1) (atomId tag 2),
        plainBond (atomId tag 2) (atomId tag 3),
        plainBond (atomId tag 1) (atomId tag 4),
        plainBond (atomId tag 4) (atomId tag 5),
        plainBond (atomId tag 1) (atomId tag 6),
        plainBond (atomId tag 6) (atomId tag 7) ] }

/-- OSiMe2-t-Bu, including all six carbons and their atom-local hydrogens. -/
def tbsEtherOn (parent : AtomId) (tag : String) : MolecularGraph :=
  { atoms :=
      [ neutralAtom tag 0 .O 0, neutralAtom tag 1 .Si 0,
        neutralAtom tag 2 .C 3, neutralAtom tag 3 .C 3,
        neutralAtom tag 4 .C 0, neutralAtom tag 5 .C 3,
        neutralAtom tag 6 .C 3, neutralAtom tag 7 .C 3 ]
    bonds :=
      [ plainBond parent (atomId tag 0),
        plainBond (atomId tag 0) (atomId tag 1),
        plainBond (atomId tag 1) (atomId tag 2),
        plainBond (atomId tag 1) (atomId tag 3),
        plainBond (atomId tag 1) (atomId tag 4),
        plainBond (atomId tag 4) (atomId tag 5),
        plainBond (atomId tag 4) (atomId tag 6),
        plainBond (atomId tag 4) (atomId tag 7) ] }

inductive OxygenState
  | hydroxy | TES
  deriving DecidableEq, Repr, BEq

def oxygenStateOn (parent : AtomId) (tag : String) : OxygenState → MolecularGraph
  | .hydroxy => hydroxyOn parent tag
  | .TES => tesEtherOn parent tag

/-- Units are connected through positions 0 (left) and 3 (right).
`quinone` means the para-hydroxycyclohexa-2,5-dienone unit: OH at position 0
and C=O at position 3. -/
inductive RingUnit
  | phenylene
  | maskedDiene (at0 at3 : OxygenState)
  | quinone
  deriving DecidableEq, Repr, BEq

def ringUnitGraph (tag : String) : RingUnit → MolecularGraph
  | .phenylene => phenylene tag
  | .maskedDiene at0 at3 =>
      joinGraphs
        [ dieneRing tag,
          oxygenStateOn (atomId tag 0) (tag ++ ".o0") at0,
          oxygenStateOn (atomId tag 3) (tag ++ ".o3") at3 ]
  | .quinone =>
      joinGraphs
        [ dieneRing tag,
          hydroxyOn (atomId tag 0) (tag ++ ".o0"),
          carbonylOn (atomId tag 3) (tag ++ ".o3") ]

inductive EndGroup
  | none | bromine | hydroxy | TBS
  deriving DecidableEq, Repr, BEq

def endGroupGraph (parent : AtomId) (tag : String) : EndGroup → MolecularGraph
  | .none => MolecularGraph.empty
  | .bromine =>
      { atoms := [neutralAtom tag 0 .Br 0]
        bonds := [plainBond parent (atomId tag 0)] }
  | .hydroxy => hydroxyOn parent tag
  | .TBS => tbsEtherOn parent tag

/-- An ordered chain of para-connected six-membered units. If `cyclic` is
true, position 3 of the last unit is bonded to position 0 of the first. -/
structure Constitution where
  cyclic : Bool
  units : List RingUnit
  leftEnd : EndGroup
  rightEnd : EndGroup
  deriving DecidableEq, Repr, BEq

def unitTag (i : Nat) : String := "u" ++ toString i

def unitGraphsFrom : Nat → List RingUnit → MolecularGraph
  | _, [] => MolecularGraph.empty
  | i, u :: us =>
      MolecularGraph.append (ringUnitGraph (unitTag i) u)
        (unitGraphsFrom (i + 1) us)

def internalConnectionBonds (numberOfUnits : Nat) : List Bond :=
  (List.range (numberOfUnits - 1)).map fun i =>
    plainBond (atomId (unitTag i) 3) (atomId (unitTag (i + 1)) 0)

/-- Expand the compact constitution into the complete atom/bond graph. -/
def expand (s : Constitution) : MolecularGraph :=
  if _h : s.units = [] then
    MolecularGraph.empty
  else
    let last := s.units.length - 1
    let core := unitGraphsFrom 0 s.units
    let links : MolecularGraph := ⟨[], internalConnectionBonds s.units.length⟩
    let left := endGroupGraph (atomId (unitTag 0) 0) "left.end" s.leftEnd
    let right := endGroupGraph (atomId (unitTag last) 3) "right.end" s.rightEnd
    let closure :=
      if s.cyclic then
        MolecularGraph.ofBond
          (plainBond (atomId (unitTag last) 3) (atomId (unitTag 0) 0))
      else MolecularGraph.empty
    joinGraphs [core, links, left, right, closure]

/-! ## General reaction rewrites and problem inputs -/

structure AryllithiumFragment where
  arylUnits : List RingUnit
  distalEnd : EndGroup
  deriving DecidableEq, Repr, BEq

def replaceLast (f : RingUnit → Option (List RingUnit)) :
    List RingUnit → Option (List RingUnit)
  | [] => none
  | [u] => f u
  | u :: us => (replaceLast f us).map (u :: ·)

/-- Nucleophilic addition of an aryllithium to the terminal quinone carbonyl:
the quinone becomes a 1,4-diol masked ring and the aryl fragment is installed
at that carbon. -/
def aryllithiumAddition (s : Constitution)
    (r : AryllithiumFragment) : Option Constitution :=
  if s.cyclic then none
  else match s.rightEnd with
    | .none =>
        match replaceLast
            (fun u => match u with
              | .quinone =>
                  some (.maskedDiene .hydroxy .hydroxy :: r.arylUnits)
              | _ => none) s.units with
        | some units => some { s with units := units, rightEnd := r.distalEnd }
        | none => none
    | _ => none

def silylateOxygen : OxygenState → OxygenState
  | .hydroxy => .TES
  | .TES => .TES

def silylateUnit : RingUnit → RingUnit
  | .maskedDiene at0 at3 =>
      .maskedDiene (silylateOxygen at0) (silylateOxygen at3)
  | u => u

/-- Two equivalents of TESCl protect the two free alcohols of the newly
formed masked ring. Already protected masked rings are unchanged. -/
def silylateFreeDiol (s : Constitution) : Constitution :=
  { s with units := s.units.map silylateUnit }

/-- Selective cleavage of the terminal phenolic TBS ether. -/
def deprotectTerminalTBS (s : Constitution) : Option Constitution :=
  if s.cyclic then none
  else match s.rightEnd with
    | .TBS => some { s with rightEnd := .hydroxy }
    | _ => none

/-- Aqueous two-electron oxidative dearomatization of a terminal para-phenol:
the phenylene plus terminal OH becomes a para-hydroxycyclohexadienone. -/
def oxidativeDearomatization (s : Constitution) : Option Constitution :=
  if s.cyclic then none
  else match s.rightEnd with
    | .hydroxy =>
        match replaceLast
            (fun u => match u with
              | .phenylene => some [.quinone]
              | _ => none) s.units with
        | some units => some { s with units := units, rightEnd := .none }
        | none => none
    | _ => none

/-- Intramolecular reductive coupling replaces both terminal aryl C--Br bonds
by the new aryl--aryl C--C bond that closes the nanohoop precursor. -/
def yamamotoCyclization (s : Constitution) : Option Constitution :=
  if s.cyclic then none
  else match s.leftEnd, s.rightEnd with
    | .bromine, .bromine =>
        some { s with cyclic := true, leftEnd := .none, rightEnd := .none }
    | _, _ => none

inductive Step
  | addAryllithium (fragment : AryllithiumFragment)
  | silylateDiol
  | removeTerminalTBS
  | dearomatizePhenol
  | closeArylBromides
  deriving DecidableEq, Repr, BEq

def applyStep (s : Constitution) : Step → Option Constitution
  | .addAryllithium r => aryllithiumAddition s r
  | .silylateDiol => some (silylateFreeDiol s)
  | .removeTerminalTBS => deprotectTerminalTBS s
  | .dearomatizePhenol => oxidativeDearomatization s
  | .closeArylBromides => yamamotoCyclization s

def runScheme : Constitution → List Step → Option Constitution
  | s, [] => some s
  | s, step :: steps =>
      (applyStep s step).bind fun next => runScheme next steps

/-! The following three declarations transcribe only objects printed on Q6-3:
the starting para-bromophenyl quinol, the OTBS-biaryllithium, and the
para-bromophenyllithium. -/

def problemStartingMaterial : Constitution :=
  { cyclic := false
    units := [.phenylene, .quinone]
    leftEnd := .bromine
    rightEnd := .none }

def problemFirstAryllithium : AryllithiumFragment :=
  { arylUnits := [.phenylene, .phenylene]
    distalEnd := .TBS }

def problemSecondAryllithium : AryllithiumFragment :=
  { arylUnits := [.phenylene]
    distalEnd := .bromine }

def throughF : List Step :=
  [.addAryllithium problemFirstAryllithium]

def throughG : List Step := throughF ++ [.silylateDiol]
def throughH : List Step := throughG ++ [.removeTerminalTBS]
def throughI : List Step := throughH ++ [.dearomatizePhenol]
def throughJ : List Step := throughI ++ [.addAryllithium problemSecondAryllithium]
def throughK : List Step := throughJ ++ [.silylateDiol]
def throughL : List Step := throughK ++ [.closeArylBromides]

/-! ## Claimed structures, expressed constitutionally and expanded atomwise -/

def fConstitution : Constitution :=
  { cyclic := false
    units :=
      [.phenylene, .maskedDiene .hydroxy .hydroxy,
       .phenylene, .phenylene]
    leftEnd := .bromine
    rightEnd := .TBS }

def gConstitution : Constitution :=
  { fConstitution with
    units :=
      [.phenylene, .maskedDiene .TES .TES, .phenylene, .phenylene] }

def hConstitution : Constitution :=
  { gConstitution with rightEnd := .hydroxy }

def iConstitution : Constitution :=
  { cyclic := false
    units := [.phenylene, .maskedDiene .TES .TES, .phenylene, .quinone]
    leftEnd := .bromine
    rightEnd := .none }

def jConstitution : Constitution :=
  { cyclic := false
    units :=
      [.phenylene, .maskedDiene .TES .TES, .phenylene,
       .maskedDiene .hydroxy .hydroxy, .phenylene]
    leftEnd := .bromine
    rightEnd := .bromine }

def kConstitution : Constitution :=
  { jConstitution with
    units :=
      [.phenylene, .maskedDiene .TES .TES, .phenylene,
       .maskedDiene .TES .TES, .phenylene] }

def lConstitution : Constitution :=
  { cyclic := true
    units :=
      [.phenylene, .maskedDiene .TES .TES, .phenylene,
       .maskedDiene .TES .TES, .phenylene]
    leftEnd := .none
    rightEnd := .none }

def structureF : MolecularGraph := expand fConstitution
def structureG : MolecularGraph := expand gConstitution
def structureH : MolecularGraph := expand hConstitution
def structureI : MolecularGraph := expand iConstitution
def structureJ : MolecularGraph := expand jConstitution
def structureK : MolecularGraph := expand kConstitution
def structureL : MolecularGraph := expand lConstitution

/-! ## Independently checkable graph invariants and molecular formulae -/

structure Formula where
  carbon : Nat
  hydrogen : Nat
  oxygen : Nat
  silicon : Nat
  bromine : Nat
  deriving DecidableEq, Repr, BEq

def Formula.zero : Formula := ⟨0, 0, 0, 0, 0⟩

def Formula.addAtom (f : Formula) (a : Atom) : Formula :=
  let withH := { f with hydrogen := f.hydrogen + a.hydrogens }
  match a.element with
  | .C => { withH with carbon := withH.carbon + 1 }
  | .O => { withH with oxygen := withH.oxygen + 1 }
  | .Si => { withH with silicon := withH.silicon + 1 }
  | .Br => { withH with bromine := withH.bromine + 1 }

def molecularFormula (g : MolecularGraph) : Formula :=
  g.atoms.foldl Formula.addAtom Formula.zero

def containsAtom (g : MolecularGraph) (id : AtomId) : Bool :=
  g.atoms.any fun a => a.id == id

def distinctAtomIds : List Atom → Bool
  | [] => true
  | a :: as => (!(as.any fun b => b.id == a.id)) && distinctAtomIds as

def sameUndirectedBond (x y : Bond) : Bool :=
  ((x.a == y.a) && (x.b == y.b)) || ((x.a == y.b) && (x.b == y.a))

def distinctBonds : List Bond → Bool
  | [] => true
  | b :: bs => (!(bs.any fun c => sameUndirectedBond b c)) && distinctBonds bs

def bondValenceAt (g : MolecularGraph) (id : AtomId) : Nat :=
  g.bonds.foldl
    (fun total b =>
      if (b.a == id) || (b.b == id) then total + b.order.valence else total)
    0

def normalValence : Element → Nat
  | .C => 4
  | .O => 2
  | .Si => 4
  | .Br => 1

/-- Besides referential integrity and ordinary valences, this verifies that no
unrequested charge, radical, or stereochemical assertion was smuggled in. -/
def wellFormedClosedShellGraph (g : MolecularGraph) : Bool :=
  distinctAtomIds g.atoms &&
  distinctBonds g.bonds &&
  g.bonds.all (fun b =>
    containsAtom g b.a && containsAtom g b.b && !(b.a == b.b) &&
      (b.stereo == .unspecified)) &&
  g.atoms.all (fun a =>
    bondValenceAt g a.id + a.hydrogens == normalValence a.element &&
      a.formalCharge == 0 && a.radicalElectrons == 0 &&
      (a.stereo == .unspecified))

def formulaF : Formula := ⟨30, 33, 3, 1, 1⟩
def formulaG : Formula := ⟨42, 61, 3, 3, 1⟩
def formulaH : Formula := ⟨36, 47, 3, 2, 1⟩
def formulaI : Formula := ⟨36, 47, 4, 2, 1⟩
def formulaJ : Formula := ⟨42, 52, 4, 2, 2⟩
def formulaK : Formula := ⟨54, 80, 4, 4, 2⟩
def formulaL : Formula := ⟨54, 80, 4, 4, 0⟩

/-! The product printed immediately after L supplies an independent downstream
check on L. Four equivalents of fluoride expose four OH groups, and reductive
aromatization turns the two masked diene units into phenylenes. -/

def removeTES : OxygenState → OxygenState
  | .hydroxy => .hydroxy
  | .TES => .hydroxy

def removeTESFromUnit : RingUnit → RingUnit
  | .maskedDiene at0 at3 => .maskedDiene (removeTES at0) (removeTES at3)
  | u => u

def fluorideDeprotection (s : Constitution) : Constitution :=
  { s with units := s.units.map removeTESFromUnit }

def aromatizeDiolUnit : RingUnit → RingUnit
  | .maskedDiene .hydroxy .hydroxy => .phenylene
  | u => u

def tinDichlorideAromatization (s : Constitution) : Constitution :=
  { s with units := s.units.map aromatizeDiolUnit }

def fiveCPPConstitution : Constitution :=
  { cyclic := true
    units := [.phenylene, .phenylene, .phenylene, .phenylene, .phenylene]
    leftEnd := .none
    rightEnd := .none }

def fiveCPP : MolecularGraph := expand fiveCPPConstitution
def formulaFiveCPP : Formula := ⟨30, 20, 0, 0, 0⟩

/-! ## Final requested outputs

Each theorem simultaneously proves (1) derivation from the printed reaction
prefix, (2) the complete graph's molecular formula, and (3) atom/bond,
valence, charge, radical, and stereochemical consistency.
-/

theorem structure_f :
    (runScheme problemStartingMaterial throughF).map expand = some structureF ∧
    molecularFormula structureF = formulaF ∧
    wellFormedClosedShellGraph structureF = true := by
  decide

theorem structure_g :
    (runScheme problemStartingMaterial throughG).map expand = some structureG ∧
    molecularFormula structureG = formulaG ∧
    wellFormedClosedShellGraph structureG = true := by
  decide

theorem structure_h :
    (runScheme problemStartingMaterial throughH).map expand = some structureH ∧
    molecularFormula structureH = formulaH ∧
    wellFormedClosedShellGraph structureH = true := by
  decide

theorem structure_i :
    (runScheme problemStartingMaterial throughI).map expand = some structureI ∧
    molecularFormula structureI = formulaI ∧
    wellFormedClosedShellGraph structureI = true := by
  decide

theorem structure_j :
    (runScheme problemStartingMaterial throughJ).map expand = some structureJ ∧
    molecularFormula structureJ = formulaJ ∧
    wellFormedClosedShellGraph structureJ = true := by
  decide

theorem structure_k :
    (runScheme problemStartingMaterial throughK).map expand = some structureK ∧
    molecularFormula structureK = formulaK ∧
    wellFormedClosedShellGraph structureK = true := by
  decide

theorem structure_l :
    (runScheme problemStartingMaterial throughL).map expand = some structureL ∧
    molecularFormula structureL = formulaL ∧
    wellFormedClosedShellGraph structureL = true := by
  decide

/-- Downstream validation against the [5]CPP product drawn in the source. -/
theorem structure_l_gives_five_cpp :
    (runScheme problemStartingMaterial throughL).map
        (fun s => expand (tinDichlorideAromatization (fluorideDeprotection s))) =
      some fiveCPP ∧
    molecularFormula fiveCPP = formulaFiveCPP ∧
    wellFormedClosedShellGraph fiveCPP = true := by
  decide

#print axioms structure_f
#print axioms structure_g
#print axioms structure_h
#print axioms structure_i
#print axioms structure_j
#print axioms structure_k
#print axioms structure_l
#print axioms structure_l_gives_five_cpp

end IChO2026Problems.T6A5
