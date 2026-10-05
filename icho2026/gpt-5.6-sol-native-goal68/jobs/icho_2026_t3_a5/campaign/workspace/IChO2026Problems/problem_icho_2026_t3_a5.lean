import Mathlib

/-!
# IChO 2026, theory problem 3, part 5

This file formalizes the structure obtained by oxidizing the imine links of
the pictured C2 + D4 Kagome COF and then cleaving the central C2 olefins by
reductive ozonolysis.

The source data and the chemical transformations are separated below.  The
answer is not represented by a name or a string: `MacroAtom` has 300 explicit
atoms (hydrogens included), `macroBond` fixes every bond, and `macroAtomSpec`
fixes element, charge, radical count, and stereochemistry at every site.
-/

namespace IChO2026Problems.T3A5

/-! ## Small chemistry vocabulary -/

inductive Element where
  | H | C | N | O | F
  deriving DecidableEq, Repr, Fintype

inductive BondOrder where
  | none | single | double | aromatic
  deriving DecidableEq, Repr, Fintype

inductive TetrahedralStereo where
  | clockwise | anticlockwise
  deriving DecidableEq, Repr, Fintype

structure AtomSpec where
  element : Element
  formalCharge : Int
  radicalElectrons : Nat
  stereo : Option TetrahedralStereo
  deriving DecidableEq, Repr

structure Formula where
  carbon : Nat
  hydrogen : Nat
  fluorine : Nat
  nitrogen : Nat
  oxygen : Nat
  deriving DecidableEq, Repr

def Formula.add (a b : Formula) : Formula :=
  { carbon := a.carbon + b.carbon
    hydrogen := a.hydrogen + b.hydrogen
    fluorine := a.fluorine + b.fluorine
    nitrogen := a.nitrogen + b.nitrogen
    oxygen := a.oxygen + b.oxygen }

def Formula.sub (a b : Formula) : Formula :=
  { carbon := a.carbon - b.carbon
    hydrogen := a.hydrogen - b.hydrogen
    fluorine := a.fluorine - b.fluorine
    nitrogen := a.nitrogen - b.nitrogen
    oxygen := a.oxygen - b.oxygen }

def Formula.scale (n : Nat) (a : Formula) : Formula :=
  { carbon := n * a.carbon
    hydrogen := n * a.hydrogen
    fluorine := n * a.fluorine
    nitrogen := n * a.nitrogen
    oxygen := n * a.oxygen }

/-! ## Problem inputs read from the figures -/

/-- The page-3/page-5 C2 drawing is the olefinic tetratopic building block
`(E)-3,3',5,5'-tetrakis(4-aminophenyl)stilbene`.  Only the features used by
the derivation are recorded here. -/
structure C2Source where
  carbon : Nat
  hydrogen : Nat
  nitrogen : Nat
  amines : Nat
  cleavableOlefins : Nat
  deriving DecidableEq, Repr

def c2Source : C2Source :=
  { carbon := 38, hydrogen := 32, nitrogen := 4,
    amines := 4, cleavableOlefins := 1 }

/-- D4 in the figure is 2,3,5,6-tetrafluoroterephthaldehyde. -/
structure D4Source where
  carbon : Nat
  hydrogen : Nat
  fluorine : Nat
  oxygen : Nat
  aldehydes : Nat
  deriving DecidableEq, Repr

def d4Source : D4Source :=
  { carbon := 8, hydrogen := 2, fluorine := 4, oxygen := 2, aldehydes := 2 }

inductive LinkageState where
  | imine | amide
  deriving DecidableEq, Repr

inductive CleavageState where
  | stilbene | aldehydes
  deriving DecidableEq, Repr

inductive AssemblyState where
  | kagomeNetwork | isolatedHexagon
  deriving DecidableEq, Repr

/-- Source state: AcOH condensation of tetratopic C2 and ditopic D4 is shown
as a Kagome imine COF.  A Kagome hexagonal boundary contains six D4 linkers
and six halves of C2, hence three complete C2 building blocks. -/
structure ProcessState where
  linkage : LinkageState
  cleavage : CleavageState
  assembly : AssemblyState
  c2MoleculesPerHexagon : Nat
  d4MoleculesPerHexagon : Nat
  condensationLinksPerHexagon : Nat
  deriving DecidableEq, Repr

def cof7ProblemInput : ProcessState :=
  { linkage := .imine
    cleavage := .stilbene
    assembly := .kagomeNetwork
    c2MoleculesPerHexagon := 3
    d4MoleculesPerHexagon := 6
    condensationLinksPerHexagon := 12 }

/-! ## Trusted general transformations and the topology derivation -/

/-- Buffered sodium chlorite oxidation changes an imine `Ar-N=CH-Ar` into
the corresponding amide `Ar-NH-C(=O)-Ar`; it preserves the scaffold. -/
def bufferedChloriteOxidation (s : ProcessState) : ProcessState :=
  { s with linkage := match s.linkage with | .imine => .amide | .amide => .amide }

/-- Reductive ozonolysis (`O3`, then `Me2S`) cleaves each stilbene `Ar-CH=CH-Ar`
to two `Ar-CHO` ends.  In the pictured Kagome connectivity the olefins bisect
the tetratopic vertices between adjacent hexagons; cutting them therefore
excises the intact hexagonal boundary. -/
def reductiveOzonolysis (s : ProcessState) : ProcessState :=
  match s.cleavage, s.assembly with
  | .stilbene, .kagomeNetwork =>
      { s with cleavage := .aldehydes, assembly := .isolatedHexagon }
  | .stilbene, .isolatedHexagon => { s with cleavage := .aldehydes }
  | .aldehydes, _ => s

def synthesisPipeline : ProcessState :=
  reductiveOzonolysis (bufferedChloriteOxidation cof7ProblemInput)

theorem pipeline_state :
    synthesisPipeline =
      { linkage := .amide
        cleavage := .aldehydes
        assembly := .isolatedHexagon
        c2MoleculesPerHexagon := 3
        d4MoleculesPerHexagon := 6
        condensationLinksPerHexagon := 12 } := by
  rfl

/-! The alternating block-level boundary is checked independently of the
atom-level construction. -/

inductive BoundaryNode where
  | c2Half (i : Fin 6)
  | d4 (i : Fin 6)
  deriving DecidableEq, Repr, Fintype

def next6 (i : Fin 6) : Fin 6 :=
  ⟨(i.val + 1) % 6, Nat.mod_lt _ (by decide)⟩

def boundaryAdjacent : BoundaryNode → BoundaryNode → Bool
  | .c2Half i, .d4 j => (j == i) || (next6 j == i)
  | .d4 i, .c2Half j => (i == j) || (next6 i == j)
  | _, _ => false

def boundaryCycle : List BoundaryNode :=
  [ .c2Half 0, .d4 0, .c2Half 1, .d4 1,
    .c2Half 2, .d4 2, .c2Half 3, .d4 3,
    .c2Half 4, .d4 4, .c2Half 5, .d4 5 ]

def closesThroughAdjacentPairs : List BoundaryNode → Bool
  | [] => false
  | h :: t => ((h :: t).zip (t ++ [h])).all fun p => boundaryAdjacent p.1 p.2

def IsCompleteSimpleBoundaryCycle (xs : List BoundaryNode) : Prop :=
  xs.Nodup ∧ xs.toFinset = Finset.univ ∧ closesThroughAdjacentPairs xs = true

theorem kagome_hexagon_boundary_is_cycle :
    IsCompleteSimpleBoundaryCycle boundaryCycle := by
  unfold IsCompleteSimpleBoundaryCycle
  refine ⟨by decide, by decide, ?_⟩
  decide

def boundaryNeighbors (v : BoundaryNode) : Finset BoundaryNode :=
  Finset.univ.filter fun w => boundaryAdjacent v w

theorem kagome_hexagon_boundary_degree_two :
    ∀ v : BoundaryNode, (boundaryNeighbors v).card = 2 := by
  decide

/-! ## Explicit atom graph of one sixth and of the complete macrocycle -/

inductive HydrogenPosition where
  | core1 | core3 | core5
  | left1 | left2 | left4 | left5
  | right1 | right2 | right4 | right5
  | aldehyde | amideLeft | amideRight
  deriving DecidableEq, Repr, Fintype

/-- One symmetry repeat contains one ozonolytically generated C2 half and one
D4-derived tetrafluoroterephthaloyl linker. -/
inductive RepeatAtom where
  | core (i : Fin 6)
  | leftPhenyl (i : Fin 6)
  | rightPhenyl (i : Fin 6)
  | d4Ring (i : Fin 6)
  | aldehydeC | aldehydeO
  | amideLeftN | amideRightN
  | carbonylLeftC | carbonylLeftO
  | carbonylRightC | carbonylRightO
  | fluorine (i : Fin 4)
  | hydrogen (p : HydrogenPosition)
  deriving DecidableEq, Repr, Fintype

def repeatElement : RepeatAtom → Element
  | .hydrogen _ => .H
  | .amideLeftN | .amideRightN => .N
  | .aldehydeO | .carbonylLeftO | .carbonylRightO => .O
  | .fluorine _ => .F
  | _ => .C

def repeatAtomSpec (a : RepeatAtom) : AtomSpec :=
  { element := repeatElement a
    formalCharge := 0
    radicalElectrons := 0
    stereo := none }

def hydrogenParent : HydrogenPosition → RepeatAtom
  | .core1 => .core 1
  | .core3 => .core 3
  | .core5 => .core 5
  | .left1 => .leftPhenyl 1
  | .left2 => .leftPhenyl 2
  | .left4 => .leftPhenyl 4
  | .left5 => .leftPhenyl 5
  | .right1 => .rightPhenyl 1
  | .right2 => .rightPhenyl 2
  | .right4 => .rightPhenyl 4
  | .right5 => .rightPhenyl 5
  | .aldehyde => .aldehydeC
  | .amideLeft => .amideLeftN
  | .amideRight => .amideRightN

def ringAdjacent (i j : Fin 6) : Bool :=
  (((i.val + 1) % 6) == j.val) || (((j.val + 1) % 6) == i.val)

def aromaticPair : RepeatAtom → RepeatAtom → Bool
  | .core i, .core j => ringAdjacent i j
  | .leftPhenyl i, .leftPhenyl j => ringAdjacent i j
  | .rightPhenyl i, .rightPhenyl j => ringAdjacent i j
  | .d4Ring i, .d4Ring j => ringAdjacent i j
  | _, _ => false

def undirectedPair (x y a b : RepeatAtom) : Bool :=
  ((x == a) && (y == b)) || ((x == b) && (y == a))

def isLocalDouble (x y : RepeatAtom) : Bool :=
  undirectedPair x y .aldehydeC .aldehydeO ||
  undirectedPair x y .carbonylLeftC .carbonylLeftO ||
  undirectedPair x y .carbonylRightC .carbonylRightO

def isHydrogenBond : RepeatAtom → RepeatAtom → Bool
  | .hydrogen h, a => a == hydrogenParent h
  | a, .hydrogen h => a == hydrogenParent h
  | _, _ => false

def isLocalSingle (x y : RepeatAtom) : Bool :=
  isHydrogenBond x y ||
  undirectedPair x y (.core 0) .aldehydeC ||
  undirectedPair x y (.core 2) (.leftPhenyl 0) ||
  undirectedPair x y (.core 4) (.rightPhenyl 0) ||
  undirectedPair x y (.leftPhenyl 3) .amideLeftN ||
  undirectedPair x y (.rightPhenyl 3) .amideRightN ||
  undirectedPair x y (.d4Ring 0) .carbonylLeftC ||
  undirectedPair x y (.d4Ring 3) .carbonylRightC ||
  undirectedPair x y (.d4Ring 1) (.fluorine 0) ||
  undirectedPair x y (.d4Ring 2) (.fluorine 1) ||
  undirectedPair x y (.d4Ring 4) (.fluorine 2) ||
  undirectedPair x y (.d4Ring 5) (.fluorine 3) ||
  undirectedPair x y .amideRightN .carbonylLeftC

def repeatLocalBond (x y : RepeatAtom) : BondOrder :=
  if isLocalDouble x y then .double
  else if aromaticPair x y then .aromatic
  else if isLocalSingle x y then .single
  else .none

/-- Six copies are placed cyclically.  The right carbonyl of cell `i` bonds
to the left amide nitrogen of cell `i+1`; this is the only inter-cell bond. -/
abbrev MacroAtom := Fin 6 × RepeatAtom

def macroAtomSpec (a : MacroAtom) : AtomSpec := repeatAtomSpec a.2

theorem repeatUnit_explicit_atom_count : Fintype.card RepeatAtom = 50 := by
  decide

theorem macrocycleX_explicit_atom_count : Fintype.card MacroAtom = 300 := by
  change Fintype.card (Fin 6 × RepeatAtom) = 300
  rw [Fintype.card_prod, repeatUnit_explicit_atom_count]
  rfl

def isForwardAmideBond (x y : MacroAtom) : Bool :=
  (x.2 == RepeatAtom.carbonylRightC) &&
  (y.2 == RepeatAtom.amideLeftN) &&
  (y.1 == next6 x.1)

def macroBond (x y : MacroAtom) : BondOrder :=
  if x.1 == y.1 then repeatLocalBond x.2 y.2
  else if isForwardAmideBond x y || isForwardAmideBond y x then .single
  else .none

def countRepeatElement (e : Element) : Nat :=
  (Finset.univ.filter fun a : RepeatAtom => repeatElement a = e).card

def countMacroElement (e : Element) : Nat :=
  (Finset.univ.filter fun a : MacroAtom => (macroAtomSpec a).element = e).card

def repeatUnitFormula : Formula :=
  { carbon := countRepeatElement .C
    hydrogen := countRepeatElement .H
    fluorine := countRepeatElement .F
    nitrogen := countRepeatElement .N
    oxygen := countRepeatElement .O }

def macrocycleXFormula : Formula :=
  Formula.scale 6 repeatUnitFormula

theorem macrocycleX_repeat_formula :
    repeatUnitFormula =
      { carbon := 27, hydrogen := 14, fluorine := 4, nitrogen := 2, oxygen := 3 } := by
  decide

theorem macrocycleX_formula :
    macrocycleXFormula =
      { carbon := 162, hydrogen := 84, fluorine := 24,
        nitrogen := 12, oxygen := 18 } := by
  rw [macrocycleXFormula, macrocycleX_repeat_formula]
  rfl

theorem macrocycleX_formula_is_six_repeats :
    macrocycleXFormula = Formula.scale 6 repeatUnitFormula := by
  rfl

/-! Formula accounting directly from the pictured reagents:
3 C2 + 6 D4, loss of 12 waters on imine condensation, addition of one O at
each of 12 imines on chlorite oxidation, and addition of one O at each of six
olefinic carbons retained in this macrocycle on reductive ozonolysis. -/

def c2Formula : Formula :=
  { carbon := c2Source.carbon, hydrogen := c2Source.hydrogen,
    fluorine := 0, nitrogen := c2Source.nitrogen, oxygen := 0 }

def d4Formula : Formula :=
  { carbon := d4Source.carbon, hydrogen := d4Source.hydrogen,
    fluorine := d4Source.fluorine, nitrogen := 0, oxygen := d4Source.oxygen }

def waterFormula : Formula :=
  { carbon := 0, hydrogen := 2, fluorine := 0, nitrogen := 0, oxygen := 1 }

def oxygenAtomFormula : Formula :=
  { carbon := 0, hydrogen := 0, fluorine := 0, nitrogen := 0, oxygen := 1 }

def reactionAccountedFormula : Formula :=
  let monomers := (Formula.scale 3 c2Formula).add (Formula.scale 6 d4Formula)
  let imineCOF := monomers.sub (Formula.scale 12 waterFormula)
  let amideCOF := imineCOF.add (Formula.scale 12 oxygenAtomFormula)
  amideCOF.add (Formula.scale 6 oxygenAtomFormula)

theorem macrocycleX_formula_derived_from_reagents :
    reactionAccountedFormula = macrocycleXFormula := by
  rw [macrocycleX_formula]
  norm_num [reactionAccountedFormula, c2Formula, d4Formula, c2Source, d4Source,
    waterFormula, oxygenAtomFormula, Formula.scale, Formula.add, Formula.sub]

/-! Structural sanity checks over the explicit atom graph. -/

set_option maxRecDepth 100000 in
theorem repeatLocalBond_is_undirected :
    ∀ x y : RepeatAtom, repeatLocalBond x y = repeatLocalBond y x := by
  decide

set_option maxRecDepth 100000 in
theorem repeatLocalBond_has_no_self_bonds :
    ∀ x : RepeatAtom, repeatLocalBond x x = .none := by
  decide

theorem macrocycleX_bonds_are_undirected :
    ∀ x y : MacroAtom, macroBond x y = macroBond y x := by
  intro x y
  unfold macroBond
  by_cases h : x.1 = y.1
  · have hxy : (x.1 == y.1) = true := beq_iff_eq.mpr h
    have hyx : (y.1 == x.1) = true := beq_iff_eq.mpr h.symm
    rw [hxy, hyx]
    exact repeatLocalBond_is_undirected x.2 y.2
  · have hxy : (x.1 == y.1) = false := beq_eq_false_iff_ne.mpr h
    have hyx : (y.1 == x.1) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
    rw [hxy, hyx]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Bool.or_comm]

theorem macrocycleX_has_no_self_bonds :
    ∀ x : MacroAtom, macroBond x x = .none := by
  intro x
  unfold macroBond
  simp only [beq_self_eq_true, ↓reduceIte]
  exact repeatLocalBond_has_no_self_bonds x.2

theorem macrocycleX_carbonyl_bond_orders (i : Fin 6) :
    macroBond (i, .aldehydeC) (i, .aldehydeO) = .double ∧
    macroBond (i, .carbonylLeftC) (i, .carbonylLeftO) = .double ∧
    macroBond (i, .carbonylRightC) (i, .carbonylRightO) = .double := by
  fin_cases i <;> decide

theorem macrocycleX_local_amide_bond (i : Fin 6) :
    macroBond (i, .amideRightN) (i, .carbonylLeftC) = .single := by
  fin_cases i <;> decide

theorem macrocycleX_intercell_amide_bond (i : Fin 6) :
    macroBond (i, .carbonylRightC) (next6 i, .amideLeftN) = .single := by
  fin_cases i <;> decide

theorem macrocycleX_fluorine_substitution (i : Fin 6) :
    macroBond (i, .d4Ring 1) (i, .fluorine 0) = .single ∧
    macroBond (i, .d4Ring 2) (i, .fluorine 1) = .single ∧
    macroBond (i, .d4Ring 4) (i, .fluorine 2) = .single ∧
    macroBond (i, .d4Ring 5) (i, .fluorine 3) = .single := by
  fin_cases i <;> decide

theorem macrocycleX_is_neutral_closed_shell_achiral :
    ∀ a : MacroAtom,
      (macroAtomSpec a).formalCharge = 0 ∧
      (macroAtomSpec a).radicalElectrons = 0 ∧
      (macroAtomSpec a).stereo = none := by
  intro a
  exact ⟨rfl, rfl, rfl⟩

/-! Minimality: the graph is explicitly six cyclic copies of `RepeatAtom`.
Moreover, no decomposition into more than six identical integral formula
units is possible: any such repeat count divides both N = 12 and O = 18, so
it divides 6. -/

def IsIntegralFormulaRepeatCount (k : Nat) : Prop :=
  ∃ unit : Formula, Formula.scale k unit = macrocycleXFormula

theorem six_is_an_integral_formula_repeat_count :
    IsIntegralFormulaRepeatCount 6 := by
  exact ⟨repeatUnitFormula, macrocycleX_formula_is_six_repeats.symm⟩

theorem no_identical_integral_repeat_count_exceeds_six
    {k : Nat} (_hk : 0 < k) (h : IsIntegralFormulaRepeatCount k) : k ≤ 6 := by
  rcases h with ⟨unit, hunit⟩
  have hformula := macrocycleX_formula
  have hnEq : k * unit.nitrogen = 12 := by
    have h1 := congrArg Formula.nitrogen hunit
    have h2 := congrArg Formula.nitrogen hformula
    exact h1.trans h2
  have hoEq : k * unit.oxygen = 18 := by
    have h1 := congrArg Formula.oxygen hunit
    have h2 := congrArg Formula.oxygen hformula
    exact h1.trans h2
  have hn : k ∣ 12 := ⟨unit.nitrogen, hnEq.symm⟩
  have ho : k ∣ 18 := ⟨unit.oxygen, hoEq.symm⟩
  have h6 : k ∣ Nat.gcd 12 18 := Nat.dvd_gcd hn ho
  norm_num at h6
  exact Nat.le_of_dvd (by decide) h6

/-- Final requested output: the reagent pipeline gives the neutral, closed-shell,
six-repeat hexagonal polyamide graph, and the displayed one-sixth unit is
minimal among identical integral molecular repeat units. -/
theorem macrocycleX_smallest_repeat_unit :
    synthesisPipeline.assembly = .isolatedHexagon ∧
    synthesisPipeline.linkage = .amide ∧
    synthesisPipeline.cleavage = .aldehydes ∧
    IsCompleteSimpleBoundaryCycle boundaryCycle ∧
    macrocycleXFormula = Formula.scale 6 repeatUnitFormula ∧
    (∀ k : Nat, 0 < k → IsIntegralFormulaRepeatCount k → k ≤ 6) := by
  refine ⟨rfl, rfl, rfl, kagome_hexagon_boundary_is_cycle, ?_, ?_⟩
  · exact macrocycleX_formula_is_six_repeats
  · intro k hk h
    exact no_identical_integral_repeat_count_exceeds_six hk h

#print axioms pipeline_state
#print axioms kagome_hexagon_boundary_is_cycle
#print axioms kagome_hexagon_boundary_degree_two
#print axioms repeatUnit_explicit_atom_count
#print axioms macrocycleX_repeat_formula
#print axioms macrocycleX_formula
#print axioms macrocycleX_explicit_atom_count
#print axioms macrocycleX_formula_derived_from_reagents
#print axioms macrocycleX_bonds_are_undirected
#print axioms macrocycleX_has_no_self_bonds
#print axioms macrocycleX_carbonyl_bond_orders
#print axioms macrocycleX_local_amide_bond
#print axioms macrocycleX_intercell_amide_bond
#print axioms macrocycleX_fluorine_substitution
#print axioms macrocycleX_is_neutral_closed_shell_achiral
#print axioms no_identical_integral_repeat_count_exceeds_six
#print axioms macrocycleX_smallest_repeat_unit

end IChO2026Problems.T3A5
