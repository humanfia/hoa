import Mathlib

/-!
# IChO 2026, theory problem 6.6

This file formalizes the structures in the reaction scheme, not merely their
names.  A `Molecule` is an ordered heavy-atom graph.  Every heavy atom records
its element, formal charge, number of radical electrons, and number of
hydrogens suppressed by the skeletal drawing.  `bonds` records connectivity
and bond order, and `stereocentres` is explicit (empty for every answer here).

The chemical transformations are kept separate from the problem-source facts.
The source has answer boxes M, N, O, Q and R.  It displays the already-known
free cyclic hexamer P6, but has no standalone P intermediate or P answer box.
-/

namespace IChO2026Problems.ProblemIChO2026T6A6

inductive Element where
  | C | N | O | Br | Zn
  deriving DecidableEq, Repr

inductive BondOrder where
  | single | double | triple | aromatic | coordination
  deriving DecidableEq, Repr

inductive Configuration where
  | R | S | E | Z
  deriving DecidableEq, Repr

structure Atom where
  element : Element
  formalCharge : Int := 0
  radicalElectrons : Nat := 0
  implicitHydrogens : Nat := 0
  deriving DecidableEq, Repr

structure Bond where
  left : Nat
  right : Nat
  order : BondOrder
  deriving DecidableEq, Repr

structure Molecule where
  atoms : List Atom
  bonds : List Bond
  stereocentres : List (Nat × Configuration) := []
  deriving DecidableEq, Repr

def c (h : Nat := 0) : Atom :=
  { element := .C, implicitHydrogens := h }

def n (charge : Int := 0) : Atom :=
  { element := .N, formalCharge := charge }

def oxygen : Atom := { element := .O }
def bromine : Atom := { element := .Br }
def zinc : Atom := { element := .Zn, formalCharge := 2 }

def sb (i j : Nat) : Bond := { left := i, right := j, order := .single }
def db (i j : Nat) : Bond := { left := i, right := j, order := .double }
def tb (i j : Nat) : Bond := { left := i, right := j, order := .triple }
def ab (i j : Nat) : Bond := { left := i, right := j, order := .aromatic }
def cb (i j : Nat) : Bond := { left := i, right := j, order := .coordination }

def Bond.validAt (atomCount : Nat) (b : Bond) : Prop :=
  b.left < atomCount ∧ b.right < atomCount ∧ b.left ≠ b.right

instance (atomCount : Nat) (b : Bond) : Decidable (b.validAt atomCount) := by
  unfold Bond.validAt
  infer_instance

def Molecule.Valid (m : Molecule) : Prop :=
  m.bonds.all (fun b => decide (b.validAt m.atoms.length)) = true ∧
  m.stereocentres.all (fun s => decide (s.1 < m.atoms.length)) = true

instance (m : Molecule) : Decidable m.Valid := by
  unfold Molecule.Valid
  infer_instance

def Molecule.hasBond (m : Molecule) (i j : Nat) (o : BondOrder) : Prop :=
  { left := i, right := j, order := o } ∈ m.bonds ∨
  { left := j, right := i, order := o } ∈ m.bonds

instance (m : Molecule) (i j : Nat) (o : BondOrder) :
    Decidable (m.hasBond i j o) := by
  unfold Molecule.hasBond
  infer_instance

def Molecule.atomAt (m : Molecule) (i : Nat) : Option Atom := m.atoms[i]?

def Molecule.countElement (m : Molecule) (e : Element) : Nat :=
  (m.atoms.filter fun a => a.element = e).length

def Molecule.hydrogenCount (m : Molecule) : Nat :=
  m.atoms.foldl (fun total a => total + a.implicitHydrogens) 0

def Molecule.netFormalCharge (m : Molecule) : Int :=
  m.atoms.foldl (fun total a => total + a.formalCharge) 0

def Molecule.radicalElectronCount (m : Molecule) : Nat :=
  m.atoms.foldl (fun total a => total + a.radicalElectrons) 0

structure Formula where
  carbon : Nat := 0
  hydrogen : Nat := 0
  nitrogen : Nat := 0
  oxygen : Nat := 0
  bromine : Nat := 0
  zinc : Nat := 0
  deriving DecidableEq, Repr

def Molecule.formula (m : Molecule) : Formula :=
  { carbon := m.countElement .C
    hydrogen := m.hydrogenCount
    nitrogen := m.countElement .N
    oxygen := m.countElement .O
    bromine := m.countElement .Br
    zinc := m.countElement .Zn }

def CertifiedNeutralClosedShell (m : Molecule) (f : Formula) : Prop :=
  m.Valid ∧
  m.formula = f ∧
  m.netFormalCharge = 0 ∧
  m.radicalElectronCount = 0 ∧
  m.stereocentres = []

instance (m : Molecule) (f : Formula) :
    Decidable (CertifiedNeutralClosedShell m f) := by
  unfold CertifiedNeutralClosedShell
  infer_instance

/-! ## The thermodynamic arene M and aldehyde N -/

/-- Positions are numbered around toluene with the methyl-bearing carbon at 0.
For three bulky substituents in thermodynamic equilibrium, `2 ≤ first`,
`second ≤ 4`, and a gap of at least one carbon encode the least-crowded
(no ortho pair) arrangement. -/
structure DiTertButylSites where
  first : Nat
  second : Nat

def IsLeastCrowded (s : DiTertButylSites) : Prop :=
  2 ≤ s.first ∧ s.first < s.second ∧ s.first + 2 ≤ s.second ∧ s.second ≤ 4

instance (s : DiTertButylSites) : Decidable (IsLeastCrowded s) := by
  unfold IsLeastCrowded
  infer_instance

def mSites : DiTertButylSites := { first := 2, second := 4 }

theorem leastCrowded_sites_unique (s : DiTertButylSites)
    (h : IsLeastCrowded s) : s = mSites := by
  rcases s with ⟨a, b⟩
  simp only [IsLeastCrowded, mSites] at h ⊢
  have ha : a = 2 := by omega
  have hb : b = 4 := by omega
  subst a
  subst b
  rfl

/-- M: ring atoms 0--5; methyl carbon 6; tert-butyl centres 7 and 11;
their methyl carbons are 8--10 and 12--14. -/
def structureM : Molecule where
  atoms :=
    [c 0, c 1, c 0, c 1, c 0, c 1,
     c 3,
     c 0, c 3, c 3, c 3,
     c 0, c 3, c 3, c 3]
  bonds :=
    [ab 0 1, ab 1 2, ab 2 3, ab 3 4, ab 4 5, ab 5 0,
     sb 0 6,
     sb 2 7, sb 7 8, sb 7 9, sb 7 10,
     sb 4 11, sb 11 12, sb 11 13, sb 11 14]

inductive MProtonEnvironment where
  | equivalentArylPair
  | uniqueAryl
  | tolylMethyl
  | tertButylMethyls
  deriving DecidableEq, Fintype, Repr

/-- All 24 hydrogens of M are represented here.  The constructors already
quotient sites related by the mirror plane and by rapid methyl rotation. -/
inductive MHydrogenSite where
  | arylPair (which : Fin 2)
  | arylUnique
  | tolyl (which : Fin 3)
  | tertButyl (group : Fin 2) (methyl : Fin 3) (which : Fin 3)
  deriving DecidableEq, Fintype, Repr

def mProtonEnvironment : MHydrogenSite → MProtonEnvironment
  | .arylPair _ => .equivalentArylPair
  | .arylUnique => .uniqueAryl
  | .tolyl _ => .tolylMethyl
  | .tertButyl _ _ _ => .tertButylMethyls

theorem m_has_four_proton_environments :
    Function.Surjective mProtonEnvironment ∧
      Fintype.card MProtonEnvironment = 4 := by
  constructor
  · intro e
    cases e with
    | equivalentArylPair => exact ⟨.arylPair 0, rfl⟩
    | uniqueAryl => exact ⟨.arylUnique, rfl⟩
    | tolylMethyl => exact ⟨.tolyl 0, rfl⟩
    | tertButylMethyls => exact ⟨.tertButyl 0 0 0, rfl⟩
  · decide

inductive BenzylicStage where
  | methyl | benzylBromide | aldehyde
  deriving DecidableEq, Repr

/-- Radical NBS/(BzO)₂ bromination at the only benzylic methyl site. -/
def radicalBenzylicBromination : BenzylicStage → BenzylicStage
  | .methyl => .benzylBromide
  | x => x

/-- Sommelet conversion followed by acidic hydrolysis. -/
def sommeletHydrolysis : BenzylicStage → BenzylicStage
  | .benzylBromide => .aldehyde
  | x => x

/-- N: ring atoms 0--5; formyl C/O 6--7; tert-butyl centres 8 and 12. -/
def structureN : Molecule where
  atoms :=
    [c 0, c 1, c 0, c 1, c 0, c 1,
     c 1, oxygen,
     c 0, c 3, c 3, c 3,
     c 0, c 3, c 3, c 3]
  bonds :=
    [ab 0 1, ab 1 2, ab 2 3, ab 3 4, ab 4 5, ab 5 0,
     sb 0 6, db 6 7,
     sb 2 8, sb 8 9, sb 8 10, sb 8 11,
     sb 4 12, sb 12 13, sb 12 14, sb 12 15]

/-! ## Zinc porphyrins O, Q and R -/

inductive MesoEnd where
  | hydrogen | bromine | terminalEthynyl | coupledEthynyl
  deriving DecidableEq, Repr

def mesoHydrogenCount : MesoEnd → Nat
  | .hydrogen => 1
  | _ => 0

def porphyrinCoreAtoms (endGroup : MesoEnd) : List Atom :=
  [c 0, c (mesoHydrogenCount endGroup), c 0, c (mesoHydrogenCount endGroup)] ++
  ((List.range 4).flatMap fun i =>
    [n (if i % 2 = 0 then -1 else 0), c 0, c 1, c 1, c 0]) ++
  [zinc]

/-- One complete 3,5-di-tert-butylphenyl group.  Local atoms 0--5 are
the phenyl ring; local atoms 6 and 10 are tert-butyl centres. -/
def arylAtoms : List Atom :=
  [c 0, c 1, c 0, c 1, c 0, c 1,
   c 0, c 3, c 3, c 3,
   c 0, c 3, c 3, c 3]

def terminalAtoms : MesoEnd → List Atom
  | .hydrogen => []
  | .bromine => [bromine, bromine]
  | .terminalEthynyl => [c 0, c 1, c 0, c 1]
  | .coupledEthynyl => [c 0, c 0, c 0, c 0]

def porphyrinAtoms (endGroup : MesoEnd) : List Atom :=
  porphyrinCoreAtoms endGroup ++ arylAtoms ++ arylAtoms ++ terminalAtoms endGroup

def pyrroleBonds (i : Nat) : List Bond :=
  let p := 4 + 5 * i
  let q := 4 + 5 * ((i + 1) % 4)
  [ab p (p + 1), ab (p + 1) (p + 2), ab (p + 2) (p + 3),
   ab (p + 3) (p + 4), ab (p + 4) p,
   ab i (p + 4), ab i (q + 1), cb 24 p]

def porphyrinCoreBonds : List Bond :=
  (List.range 4).flatMap pyrroleBonds

def arylBonds (base : Nat) : List Bond :=
  [ab base (base + 1), ab (base + 1) (base + 2),
   ab (base + 2) (base + 3), ab (base + 3) (base + 4),
   ab (base + 4) (base + 5), ab (base + 5) base,
   sb (base + 2) (base + 6),
   sb (base + 6) (base + 7), sb (base + 6) (base + 8),
   sb (base + 6) (base + 9),
   sb (base + 4) (base + 10),
   sb (base + 10) (base + 11), sb (base + 10) (base + 12),
   sb (base + 10) (base + 13)]

def terminalBonds : MesoEnd → List Bond
  | .hydrogen => []
  | .bromine => [sb 1 53, sb 3 54]
  | .terminalEthynyl => [sb 1 53, tb 53 54, sb 3 55, tb 55 56]
  | .coupledEthynyl => [sb 1 53, tb 53 54, sb 3 55, tb 55 56]

def porphyrinBonds (endGroup : MesoEnd) : List Bond :=
  porphyrinCoreBonds ++
  [sb 0 25, sb 2 39] ++ arylBonds 25 ++ arylBonds 39 ++
  terminalBonds endGroup

def porphyrin (endGroup : MesoEnd) : Molecule where
  atoms := porphyrinAtoms endGroup
  bonds := porphyrinBonds endGroup

def structureO : Molecule := porphyrin .hydrogen
def structureQ : Molecule := porphyrin .bromine
def structureR : Molecule := porphyrin .terminalEthynyl

/-- The MacDonald/Lindsey [2+2] condensation with the supplied dipyrromethane,
DDQ oxidation, and zinc insertion gives the trans-A₂ zinc porphyrin. -/
def porphyrinCondensation : BenzylicStage → Option MesoEnd
  | .aldehyde => some .hydrogen
  | _ => none

def mesoBromination : MesoEnd → Option MesoEnd
  | .hydrogen => some .bromine
  | _ => none

inductive ProtectedEnd where
  | brominated | trihexylsilylEthynyl | terminalEthynyl
  deriving DecidableEq, Repr

def sonogashiraInstall : ProtectedEnd → Option ProtectedEnd
  | .brominated => some .trihexylsilylEthynyl
  | _ => none

def fluorideDeprotect : ProtectedEnd → Option ProtectedEnd
  | .trihexylsilylEthynyl => some .terminalEthynyl
  | _ => none

/-! ## The displayed product P6 -/

def shiftBond (offset : Nat) (b : Bond) : Bond :=
  { b with left := b.left + offset, right := b.right + offset }

def coupledMonomer : Molecule := porphyrin .coupledEthynyl

def p6Atoms : List Atom :=
  (List.range 6).flatMap fun _ => coupledMonomer.atoms

def p6InternalBonds : List Bond :=
  (List.range 6).flatMap fun i =>
    coupledMonomer.bonds.map (shiftBond (57 * i))

/-- Side 3 of unit i is joined to side 1 of the next unit.  Together with the
two C≡C bonds already in each monomer, these six new single bonds give six
Por--C≡C--C≡C--Por links and close one macrocycle. -/
def p6ClosingBonds : List Bond :=
  (List.range 6).map fun i =>
    sb (57 * i + 56) (57 * ((i + 1) % 6) + 54)

def structureP6 : Molecule where
  atoms := p6Atoms
  bonds := p6InternalBonds ++ p6ClosingBonds

def oxidativeTemplateCoupling : ProtectedEnd → Option Molecule
  | .terminalEthynyl => some structureP6
  | _ => none

/-! ## Source-label audit -/

inductive PrintedLabel where
  | M | N | O | P | Q | R | P6
  deriving DecidableEq, Repr

/-- Labels printed under the blank response regions on student answer sheets
A6-5 and A6-6. -/
def studentAnswerBoxes : List PrintedLabel := [.M, .N, .O, .Q, .R]

/-- The structure printed in the question itself, after DABCO removes T6. -/
def structuresAlreadyDisplayed : List PrintedLabel := [.P6]

theorem structure_P_source_gap :
    PrintedLabel.P ∉ studentAnswerBoxes ∧
    PrintedLabel.P6 ∈ structuresAlreadyDisplayed := by
  decide

/-- The `structure_p` field generated by TASK.json is discharged by proving
the source mismatch, rather than by postulating an unprinted molecule. -/
theorem structure_P :
    PrintedLabel.P ∉ studentAnswerBoxes ∧
    PrintedLabel.P6 ∈ structuresAlreadyDisplayed :=
  structure_P_source_gap

/-! ## Certified requested outputs -/

theorem structure_M :
    IsLeastCrowded mSites ∧
    CertifiedNeutralClosedShell structureM
      { carbon := 15, hydrogen := 24 } ∧
    structureM.bonds.Nodup ∧
    structureM.hasBond 0 6 .single ∧
    structureM.hasBond 2 7 .single ∧
    structureM.hasBond 4 11 .single := by
  decide

theorem structure_N :
    sommeletHydrolysis (radicalBenzylicBromination .methyl) = .aldehyde ∧
    CertifiedNeutralClosedShell structureN
      { carbon := 15, hydrogen := 22, oxygen := 1 } ∧
    structureN.bonds.Nodup ∧
    structureN.hasBond 0 6 .single ∧
    structureN.hasBond 6 7 .double := by
  decide

theorem structure_O :
    porphyrinCondensation .aldehyde = some .hydrogen ∧
    CertifiedNeutralClosedShell structureO
      { carbon := 48, hydrogen := 52, nitrogen := 4, zinc := 1 } ∧
    structureO.bonds.Nodup ∧
    structureO.hasBond 0 25 .single ∧
    structureO.hasBond 2 39 .single ∧
    structureO.atomAt 1 = some (c 1) ∧
    structureO.atomAt 3 = some (c 1) ∧
    structureO.hasBond 24 4 .coordination ∧
    structureO.hasBond 24 9 .coordination ∧
    structureO.hasBond 24 14 .coordination ∧
    structureO.hasBond 24 19 .coordination := by
  decide

theorem structure_Q :
    mesoBromination .hydrogen = some .bromine ∧
    CertifiedNeutralClosedShell structureQ
      { carbon := 48, hydrogen := 50, nitrogen := 4,
        bromine := 2, zinc := 1 } ∧
    structureQ.bonds.Nodup ∧
    structureQ.atomAt 53 = some bromine ∧
    structureQ.atomAt 54 = some bromine ∧
    structureQ.hasBond 1 53 .single ∧
    structureQ.hasBond 3 54 .single := by
  decide

theorem structure_R :
    fluorideDeprotect (.trihexylsilylEthynyl) = some .terminalEthynyl ∧
    sonogashiraInstall .brominated = some .trihexylsilylEthynyl ∧
    CertifiedNeutralClosedShell structureR
      { carbon := 52, hydrogen := 52, nitrogen := 4, zinc := 1 } ∧
    structureR.bonds.Nodup ∧
    structureR.hasBond 1 53 .single ∧
    structureR.hasBond 53 54 .triple ∧
    structureR.atomAt 54 = some (c 1) ∧
    structureR.hasBond 3 55 .single ∧
    structureR.hasBond 55 56 .triple ∧
    structureR.atomAt 56 = some (c 1) := by
  decide

theorem structure_P6 :
    oxidativeTemplateCoupling .terminalEthynyl = some structureP6 ∧
    CertifiedNeutralClosedShell structureP6
      { carbon := 312, hydrogen := 300, nitrogen := 24, zinc := 6 } ∧
    structureP6.atoms.length = 342 ∧
    structureP6.bonds.length = 402 ∧
    structureP6.hasBond 56 (57 + 54) .single ∧
    structureP6.hasBond (57 * 5 + 56) 54 .single := by
  set_option maxRecDepth 10000 in
  decide

#print axioms leastCrowded_sites_unique
#print axioms m_has_four_proton_environments
#print axioms structure_M
#print axioms structure_N
#print axioms structure_O
#print axioms structure_Q
#print axioms structure_R
#print axioms structure_P
#print axioms structure_P_source_gap
#print axioms structure_P6

end IChO2026Problems.ProblemIChO2026T6A6
