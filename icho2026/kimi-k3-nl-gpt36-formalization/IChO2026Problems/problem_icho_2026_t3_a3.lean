import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem 3.3

The problem page gives a finite inventory of labelled monomers, their reactive
groups, and seven two-building-block topology diagrams.  This file models that
inventory directly.  In particular, an `XXX` cell is not an unconstrained flag:
it means that every reaction-compatible pair with the required depicted
geometries has already occurred in the printed givens or an earlier answer row.
-/

namespace IChO2026Problems.IChO2026T3A3

/-- The fifteen serial monomer labels printed on page Q3-3. -/
inductive Monomer where
  | A1 | A2 | A3 | A4
  | B1 | B2 | B3
  | C1 | C2 | C3
  | D1 | D2 | D3 | D4
  | E1
  deriving DecidableEq, Fintype, Repr

/-- Functional-group classes visible in the printed molecular structures. -/
inductive ReactiveClass where
  | boronicAcid
  | polyol
  | amine
  | aldehyde
  | activeMethylene
  deriving DecidableEq, Fintype, Repr

/-- Geometry and connectivity of a monomer's complete set of reactive sites.
The names distinguish the three different four- and six-connected figures. -/
inductive SiteGeometry where
  | linear2
  | trigonalPlanar3
  | squarePlanar4
  | rhombicPlanar4
  | tetrahedral4
  | trigonalPlanar6
  deriving DecidableEq, Fintype, Repr

/-- The seven topology columns, in the order printed in the answer table. -/
inductive Topology where
  | tetragonal1
  | tetragonal2
  | hexagonal1
  | hexagonal2
  | trigonal
  | kagome
  | tetrahedral
  deriving DecidableEq, Fintype, Repr

/-- The only three condensation-link types admitted by the question. -/
inductive CondensationKind where
  | boronateEster
  | imine
  | carbonCarbon
  deriving DecidableEq, Fintype, Repr

/-- Source-image classification of each labelled monomer by functional group. -/
def reactiveClass : Monomer → ReactiveClass
  | .A1 | .A2 | .A3 | .A4 => .boronicAcid
  | .B1 | .B2 | .B3 => .polyol
  | .C1 | .C2 | .C3 => .amine
  | .D1 | .D2 | .D3 | .D4 => .aldehyde
  | .E1 => .activeMethylene

/-- Source-image classification of each labelled monomer by the geometry and
number of its reactive sites. -/
def siteGeometry : Monomer → SiteGeometry
  | .A2 | .B2 | .C1 | .D4 => .linear2
  | .A1 | .B3 | .D2 | .E1 => .trigonalPlanar3
  | .B1 | .C3 => .squarePlanar4
  | .A3 | .C2 => .rhombicPlanar4
  | .A4 | .D3 => .tetrahedral4
  | .D1 => .trigonalPlanar6

/-- The site count is retained separately from the geometric label so that a
later proof can audit every depicted degree. -/
def siteCount : SiteGeometry → ℕ
  | .linear2 => 2
  | .trigonalPlanar3 => 3
  | .squarePlanar4 | .rhombicPlanar4 | .tetrahedral4 => 4
  | .trigonalPlanar6 => 6

/-- Reaction compatibility read from the stipulated condensation families.
The orientation is canonical: A--B, C--D, and E--D. -/
def condensationKind (first second : Monomer) : Option CondensationKind :=
  match reactiveClass first, reactiveClass second with
  | .boronicAcid, .polyol => some .boronateEster
  | .amine, .aldehyde => some .imine
  | .activeMethylene, .aldehyde => some .carbonCarbon
  | _, _ => none

/-- A candidate combination is a canonically oriented pair of printed labels. -/
abbrev MonomerCombination := Monomer × Monomer

/-- The complete candidate domain is generated before choosing an answer by
filtering all pairs of printed monomers with the source-stipulated chemistry. -/
def reactionCompatibleCombinations : Finset MonomerCombination :=
  Finset.univ.filter fun pair => (condensationKind pair.1 pair.2).isSome

/-- Symmetric chemical compatibility of two printed monomers.  This predicate
is independent of the canonical ordering used in the finite representation. -/
def ChemicallyCompatible (first second : Monomer) : Prop :=
  (condensationKind first second).isSome ∨
    (condensationKind second first).isSome

/-- Completeness condition for the finite domain: every compatible unordered
pair has one of its two orientations in the generated canonical domain, and
every represented pair comes from such a compatible unordered pair. -/
def CandidateDomainComplete : Prop :=
  ∀ first second,
    ChemicallyCompatible first second ↔
      ∃ pair ∈ reactionCompatibleCombinations,
        pair = (first, second) ∨ pair = (second, first)

/-- An unordered match against the pair of building-block geometries required
by a topology diagram. -/
def hasGeometryPair
    (pair : MonomerCombination) (first second : SiteGeometry) : Prop :=
  (siteGeometry pair.1 = first ∧ siteGeometry pair.2 = second) ∨
  (siteGeometry pair.1 = second ∧ siteGeometry pair.2 = first)

/-- Geometry pairs obtained by counting the black and red vertices and their
incident half-edges in each topology icon on page Q3-3. -/
def matchesTopology (topology : Topology) (pair : MonomerCombination) : Prop :=
  match topology with
  | .tetragonal1 => hasGeometryPair pair .squarePlanar4 .linear2
  | .tetragonal2 => hasGeometryPair pair .squarePlanar4 .tetrahedral4
  | .hexagonal1 => hasGeometryPair pair .trigonalPlanar3 .linear2
  | .hexagonal2 => hasGeometryPair pair .trigonalPlanar3 .trigonalPlanar3
  | .trigonal => hasGeometryPair pair .trigonalPlanar6 .linear2
  | .kagome => hasGeometryPair pair .rhombicPlanar4 .linear2
  | .tetrahedral => hasGeometryPair pair .tetrahedral4 .linear2

/-- A pair is admissible for a topology exactly when it lies in the complete
reaction-compatible domain and has the two geometries depicted for the column. -/
def Admissible (topology : Topology) (pair : MonomerCombination) : Prop :=
  pair ∈ reactionCompatibleCombinations ∧ matchesTopology topology pair

/-- The three examples already printed in the first table row on page Q3-4. -/
def suppliedExamples : Topology → Finset MonomerCombination
  | .hexagonal1 => {(.A2, .B3)}
  | .hexagonal2 => {(.E1, .D2)}
  | .kagome => {(.C2, .D4)}
  | _ => ∅

/-- A blank answer cell is filled by either a new combination or `XXX`. -/
inductive TableCell where
  | combination (pair : MonomerCombination)
  | xxx
  deriving DecidableEq, Repr

/-- The singleton set contributed by a combination cell; `XXX` contributes no
new pair. -/
def TableCell.pairs : TableCell → Finset MonomerCombination
  | .combination pair => {pair}
  | .xxx => ∅

/-- Meaning of one filled cell relative to all examples used earlier in its
column.  The universal clause is the formal justification required for `XXX`. -/
def CellCorrect
    (topology : Topology) (used : Finset MonomerCombination) : TableCell → Prop
  | .combination pair => Admissible topology pair ∧ pair ∉ used
  | .xxx => ∀ pair, Admissible topology pair → pair ∈ used

/-- Two complete answer rows, one cell for every topology column. -/
structure TopologyTable where
  row1 : Topology → TableCell
  row2 : Topology → TableCell

/-- The source-derived specification of a completed table.  Besides validating
all fourteen blank cells sequentially, it checks that every supplied example
itself has the topology under which the problem prints it. -/
def TopologyTableCorrect (table : TopologyTable) : Prop :=
  CandidateDomainComplete ∧
    (∀ topology pair, pair ∈ suppliedExamples topology → Admissible topology pair) ∧
    (∀ topology,
      CellCorrect topology (suppliedExamples topology) (table.row1 topology)) ∧
    (∀ topology,
      CellCorrect topology
        (suppliedExamples topology ∪ (table.row1 topology).pairs)
        (table.row2 topology))

/-- Kimi-K3's first filled row, preserved verbatim from the authorized draft. -/
def proposedRow1 : Topology → TableCell
  | .tetragonal1 => .combination (.A2, .B1)
  | .tetragonal2 => .combination (.A4, .B1)
  | .hexagonal1 => .combination (.A1, .B2)
  | .hexagonal2 => .combination (.A1, .B3)
  | .trigonal => .combination (.C1, .D1)
  | .kagome => .combination (.A3, .B2)
  | .tetrahedral => .combination (.A4, .B2)

/-- Kimi-K3's second filled row, including the three exhaustiveness claims. -/
def proposedRow2 : Topology → TableCell
  | .tetragonal1 => .combination (.C3, .D4)
  | .tetragonal2 => .combination (.C3, .D3)
  | .hexagonal1 => .combination (.C1, .D2)
  | .hexagonal2 => .xxx
  | .trigonal => .xxx
  | .kagome => .xxx
  | .tetrahedral => .combination (.C1, .D3)

/-- The concrete two-row classification submitted for the table. -/
def proposedTopologyTable : TopologyTable where
  row1 := proposedRow1
  row2 := proposedRow2

/-- Raw exact-symbolic result proposition. -/
def topologyTableRawResult : Prop :=
  TopologyTableCorrect proposedTopologyTable

/-- The problem requests exact symbolic reporting, so reporting preserves the
same table and the same semantic specification without numerical rounding. -/
def topologyTableReportedResult : Prop :=
  TopologyTableCorrect proposedTopologyTable

/-- The candidate domain is sound and complete for unordered pairs from the
printed inventory under the three allowed condensation families. -/
theorem reactionCompatibleCombinations_source_complete :
    CandidateDomainComplete := by
  unfold CandidateDomainComplete ChemicallyCompatible
  intro first second
  constructor
  · rintro (h | h)
    · refine ⟨(first, second), ?_, Or.inl rfl⟩
      simpa [reactionCompatibleCombinations] using h
    · refine ⟨(second, first), ?_, Or.inr rfl⟩
      simpa [reactionCompatibleCombinations] using h
  · rintro ⟨pair, hpair, hEq⟩
    have hcompatible := (Finset.mem_filter.mp hpair).2
    rcases hEq with hEq | hEq
    · subst pair
      exact Or.inl hcompatible
    · subst pair
      exact Or.inr hcompatible

/-- The three combinations supplied by the problem satisfy their printed
topology constraints. -/
theorem suppliedExamples_are_admissible :
    ∀ topology pair, pair ∈ suppliedExamples topology → Admissible topology pair := by
  unfold Admissible matchesTopology hasGeometryPair
  intro topology
  fin_cases topology <;>
    simp [suppliedExamples, reactionCompatibleCombinations, siteGeometry,
      condensationKind, reactiveClass]

/-- Main raw answer contract: all fourteen cells are correct, and each `XXX`
follows from exhaustive elimination over the independently generated domain. -/
theorem topologyTable_raw_result : topologyTableRawResult := by
  unfold topologyTableRawResult TopologyTableCorrect
  refine ⟨reactionCompatibleCombinations_source_complete,
    suppliedExamples_are_admissible, ?_, ?_⟩
  · intro topology
    fin_cases topology <;>
      simp only [proposedTopologyTable, proposedRow1, CellCorrect] <;>
      unfold Admissible matchesTopology hasGeometryPair <;>
      decide
  · intro topology
    fin_cases topology <;>
      simp only [proposedTopologyTable, proposedRow1, proposedRow2,
        TableCell.pairs, CellCorrect] <;>
      unfold Admissible matchesTopology hasGeometryPair <;>
      set_option maxRecDepth 10000 in decide

/-- Exact-symbolic reported answer contract. -/
theorem topologyTable_reported_result : topologyTableReportedResult := by
  exact topologyTable_raw_result

end IChO2026Problems.IChO2026T3A3
