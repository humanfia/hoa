import Mathlib

/-!
# IChO 2026, theory problem 3, part 3

This file formalizes the finite classification requested by the topology table.
The monomer roles below are a transcription of the functional-group counts and
geometries drawn on question page Q3-3.  The three constructors of
`Combination` are exactly the reaction-class pairings admitted by the question:

* `A + B` gives a boronate ester;
* `C + D` gives an imine;
* `E + D` gives a C=C linkage.

Thus an inhabitant of `Combination` is already an admissible condensation pair;
arbitrary chemically incompatible pairs are not silently included as candidates.
-/

namespace IChO2026Problems.T3A3

inductive AMonomer
  | A1 | A2 | A3 | A4
  deriving DecidableEq, Repr, Fintype

inductive BMonomer
  | B1 | B2 | B3
  deriving DecidableEq, Repr, Fintype

inductive CMonomer
  | C1 | C2 | C3
  deriving DecidableEq, Repr, Fintype

inductive DMonomer
  | D1 | D2 | D3 | D4
  deriving DecidableEq, Repr, Fintype

inductive EMonomer
  | E1
  deriving DecidableEq, Repr, Fintype

/-- The connectivity/geometry role visible in a monomer drawing.
`rhombicFour` is the C2-symmetric, four-ended tetraphenylethene/pyrene-style
role of A3 and C2.  With a linear partner it gives the dual-pore Kagome
schematic, unlike the square-planar role of B1 and C3. -/
inductive NodeRole
  | linearTwo
  | trigonalThree
  | tetragonalFour
  | rhombicFour
  | hexagonalSix
  | tetrahedralFour
  deriving DecidableEq, Repr, Fintype

/-! ## Problem-input transcription -/

def roleA : AMonomer → NodeRole
  | .A1 => .trigonalThree
  | .A2 => .linearTwo
  | .A3 => .rhombicFour
  | .A4 => .tetrahedralFour

def roleB : BMonomer → NodeRole
  | .B1 => .tetragonalFour
  | .B2 => .linearTwo
  | .B3 => .trigonalThree

def roleC : CMonomer → NodeRole
  | .C1 => .linearTwo
  | .C2 => .rhombicFour
  | .C3 => .tetragonalFour

def roleD : DMonomer → NodeRole
  | .D1 => .hexagonalSix
  | .D2 => .trigonalThree
  | .D3 => .tetrahedralFour
  | .D4 => .linearTwo

def roleE : EMonomer → NodeRole
  | .E1 => .trigonalThree

/-- Every chemically admissible pair from the displayed monomers. -/
inductive Combination
  | AB (a : AMonomer) (b : BMonomer)
  | CD (c : CMonomer) (d : DMonomer)
  | ED (e : EMonomer) (d : DMonomer)
  deriving DecidableEq, Repr, Fintype

def roles : Combination → NodeRole × NodeRole
  | .AB a b => (roleA a, roleB b)
  | .CD c d => (roleC c, roleD d)
  | .ED e d => (roleE e, roleD d)

inductive Topology
  | tetragonal1
  | tetragonal2
  | hexagonal1
  | hexagonal2
  | trigonal
  | kagome
  | tetrahedral
  deriving DecidableEq, Repr, Fintype

/-- Equality of an unordered pair of monomer roles. -/
def SameRolePair (p q : NodeRole × NodeRole) : Prop :=
  (p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1)

instance sameRolePairDecidable (p q : NodeRole × NodeRole) :
    Decidable (SameRolePair p q) := by
  unfold SameRolePair
  infer_instance

/-- The two building-block roles depicted by each topology schematic. -/
def requiredRoles : Topology → NodeRole × NodeRole
  | .tetragonal1 => (.tetragonalFour, .linearTwo)
  | .tetragonal2 => (.tetragonalFour, .rhombicFour)
  | .hexagonal1 => (.trigonalThree, .linearTwo)
  | .hexagonal2 => (.trigonalThree, .trigonalThree)
  | .trigonal => (.hexagonalSix, .linearTwo)
  | .kagome => (.rhombicFour, .linearTwo)
  | .tetrahedral => (.tetrahedralFour, .linearTwo)

def Fits (t : Topology) (c : Combination) : Prop :=
  SameRolePair (roles c) (requiredRoles t)

instance fitsDecidable (t : Topology) (c : Combination) : Decidable (Fits t c) := by
  unfold Fits
  infer_instance

/-! ## Derived exhaustive classification -/

/-- The complete solution set obtained by enumerating the 28 admissible
condensation pairs and comparing their displayed roles with the schematics. -/
def allSolutions : Topology → List Combination
  | .tetragonal1 =>
      [.AB .A2 .B1, .CD .C3 .D4]
  | .tetragonal2 =>
      [.AB .A3 .B1]
  | .hexagonal1 =>
      [.AB .A1 .B2, .AB .A2 .B3, .CD .C1 .D2, .ED .E1 .D4]
  | .hexagonal2 =>
      [.AB .A1 .B3, .ED .E1 .D2]
  | .trigonal =>
      [.CD .C1 .D1]
  | .kagome =>
      [.AB .A3 .B2, .CD .C2 .D4]
  | .tetrahedral =>
      [.AB .A4 .B2, .CD .C1 .D3]

/-- Exhaustiveness is proved over the full finite candidate type, rather than
postulated for the cells marked `XXX`. -/
theorem fits_iff_mem_allSolutions :
    ∀ (t : Topology) (c : Combination), Fits t c ↔ c ∈ allSolutions t := by
  intro t c
  fin_cases t <;> fin_cases c <;> decide

/-! ## The submitted two-row table -/

inductive Cell
  | combination (c : Combination)
  | xxx
  deriving DecidableEq, Repr

/-- Examples printed in the first (non-answer) row of the question. -/
def supplied : Topology → List Combination
  | .hexagonal1 => [.AB .A2 .B3]
  | .hexagonal2 => [.ED .E1 .D2]
  | .kagome => [.CD .C2 .D4]
  | _ => []

/-- Two entries for every column of answer sheet A3-2.  Where a topology has
more valid new examples than available rows, any two valid new examples are
permitted; this submission chooses the two shown here. -/
def submission : Topology → List Cell
  | .tetragonal1 =>
      [.combination (.AB .A2 .B1), .combination (.CD .C3 .D4)]
  | .tetragonal2 =>
      [.combination (.AB .A3 .B1), .xxx]
  | .hexagonal1 =>
      [.combination (.AB .A1 .B2), .combination (.CD .C1 .D2)]
  | .hexagonal2 =>
      [.combination (.AB .A1 .B3), .xxx]
  | .trigonal =>
      [.combination (.CD .C1 .D1), .xxx]
  | .kagome =>
      [.combination (.AB .A3 .B2), .xxx]
  | .tetrahedral =>
      [.combination (.AB .A4 .B2), .combination (.CD .C1 .D3)]

def submittedCombinations (cells : List Cell) : List Combination :=
  cells.filterMap fun
    | .combination c => some c
    | .xxx => none

/-- Validity says: there are exactly two answer cells; every written example
fits and is new; no example is repeated; and the presence of `XXX` is licensed
only if every fitting combination is already supplied or written elsewhere in
that column. -/
def ValidSubmission (t : Topology) (cells : List Cell) : Prop :=
  cells.length = 2 ∧
  (∀ c ∈ submittedCombinations cells, Fits t c ∧ c ∉ supplied t) ∧
  (supplied t ++ submittedCombinations cells).Nodup ∧
  (.xxx ∈ cells →
    ∀ c, Fits t c → c ∈ supplied t ++ submittedCombinations cells)

/-- This is the formal correctness theorem for all fourteen requested cells.
In particular its final conjunct proves each `XXX` by exhaustive exclusion. -/
theorem topology_table_valid :
    ∀ t : Topology, ValidSubmission t (submission t) := by
  intro t
  fin_cases t <;>
    simp [ValidSubmission, submission, submittedCombinations, supplied,
      fits_iff_mem_allSolutions, allSolutions]

/-- A single inspectable value containing the table in printed column order. -/
def topologyTable : List (Topology × List Cell) :=
  [(.tetragonal1, submission .tetragonal1),
   (.tetragonal2, submission .tetragonal2),
   (.hexagonal1, submission .hexagonal1),
   (.hexagonal2, submission .hexagonal2),
   (.trigonal, submission .trigonal),
   (.kagome, submission .kagome),
   (.tetrahedral, submission .tetrahedral)]

theorem topology_table_entries :
    topologyTable =
      [(.tetragonal1,
          [.combination (.AB .A2 .B1), .combination (.CD .C3 .D4)]),
       (.tetragonal2,
          [.combination (.AB .A3 .B1), .xxx]),
       (.hexagonal1,
          [.combination (.AB .A1 .B2), .combination (.CD .C1 .D2)]),
       (.hexagonal2,
          [.combination (.AB .A1 .B3), .xxx]),
       (.trigonal,
          [.combination (.CD .C1 .D1), .xxx]),
       (.kagome,
          [.combination (.AB .A3 .B2), .xxx]),
       (.tetrahedral,
          [.combination (.AB .A4 .B2), .combination (.CD .C1 .D3)])] := by
  rfl

#print axioms fits_iff_mem_allSolutions
#print axioms topology_table_valid
#print axioms topology_table_entries

end IChO2026Problems.T3A3
