import Mathlib

/-!
# IChO 2026 (58th IChO, Uzbekistan) — Theory question T3, subquestion 3.3

Formalization of the reticular-design table of T3.3 ("Into Reticular
Chemistry"), solved from the problem-only source pages
`icho_2026_source/image/T3_page-3.png` (monomer library A–E plus the seven
topology figures) and `icho_2026_source/image/T3_page-4.png` (the table to
fill, with the printed examples **A2+B3** (Hexagonal 1), **E1+D2**
(Hexagonal 2) and **C2+D4** (Kagome)).

## Grounding in the printed sources

**Allowed linkages (Q3-3 banner).** Only condensation to **boronate esters**
(B(OH)₂ + catechol), **imines** (CHO + NH₂) and **C=C bonds** (aldehyde +
benzylic nitrile, Knoevenagel-type) may be used, so a usable pair of monomers
must carry complementary functional-group classes: A (boronic acids) only
with B (catechols); C (amines) only with D (aldehydes); E (nitrile) only
with D.

**Connectivities** (number of condensation linkages the printed monomer can
form, counted from the drawn structures on Q3-3):

* A1 = 3 (1,3,5-tris(4-boronophenyl)benzene core), A2 = 2
  (benzene-1,4-diboronic acid), A3 = 4 (tetra(4-boronophenyl)ethylene),
  A4 = 4 (tetrakis(4-boronophenyl)silane — tetrahedral Si centre);
* B1 = 4 (porphyrin bearing four 3,4-dihydroxyphenyl groups), B2 = 2
  (naphthalene-2,3,6,7-tetrol), B3 = 3 (2,3,6,7,10,11-
  hexahydroxytriphenylene, three catechol faces);
* C1 = 2 (benzidine), C2 = 4 (tetra(4-aminophenyl)stilbene), C3 = 4
  (tetra(4-aminophenyl)porphyrin);
* D1 = 6 (hexa(4-formylphenyl)benzene), D2 = 3 (2,4,6-tris(4-formylphenyl)-
  1,3,5-triazine), D3 = 4 (tetrakis(4-formylphenyl)methane — tetrahedral C
  centre), D4 = 2 (2,3,5,6-tetrafluoroterephthalaldehyde);
* E1 = 3 (benzene-1,3,5-triyltriacetonitrile).

**Geometry.** A4 (Si) and D3 (sp³ C) are tetrahedral (3D) centres; all
other monomers are planar π-systems.  The six 2D topology figures admit
only planar building blocks; the Tetrahedral figure (a 3D net) requires a
tetrahedral degree-4 vertex.

**Net signatures** (degrees of the two roles) read off the topology figures
on Q3-3 together with the printed examples:

* Hexagonal 1 = A2+B3: honeycomb; B3 (3) sits on the hexagon vertices, A2
  (2) bridges adjacent vertices → role degrees **(3, 2)**.
* Hexagonal 2 = E1+D2: staggered honeycomb in which *both* alternating
  vertex sublattices are occupied by monomers (E1 red, D2 black), directly
  linked → role degrees **(3, 3)**; since both E1 and D2 are 3-connecting,
  this is the only consistent reading of the printed example (and it
  matches the figure, where the monomer junctions sit *at* the net
  vertices rather than along the edges).
* Tetragonal 1 / Tetragonal 2: square nets, role degrees **(4, 2)**; the
  two figures draw the two building blocks in opposite colours.
* Trigonal: triangular net, role degrees **(6, 2)**.
* Kagome = C2+D4: C2 (4) on the degree-4 corner-sharing vertices, D4 (2)
  linking them → role degrees **(4, 2)**.
* Tetrahedral: 3D net, tetrahedral **4**-vertex + **2**-linker.

The exhaustive certificate theorems below depend only on these
problem-grounded data plus the finiteness of the printed library (15
monomers); no official solutions, marking schemes or answer repositories
were consulted.
-/

namespace IChO2026T3A3

/-- Functional-group classes of the monomer library (Q3-3: "A–D represent
compound classes with different functional groups"; E1 is printed in its own
box as the benzylic-nitrile C=C partner). -/
inductive HClass | boronicAcid | catechol | amine | aldehyde | nitrile
  deriving DecidableEq, Repr

/-- The fifteen monomers printed on Q3-3 (A1–A4, B1–B3, C1–C3, D1–D4, E1). -/
inductive Monomer
  | A1 | A2 | A3 | A4 | B1 | B2 | B3 | C1 | C2 | C3 | D1 | D2 | D3 | D4 | E1
  deriving DecidableEq, Repr, Fintype

/-- Number of condensation linkages each printed monomer can form, counted
from the drawn structures. -/
def connectivity : Monomer → ℕ
  | .A1 => 3 | .A2 => 2 | .A3 => 4 | .A4 => 4
  | .B1 => 4 | .B2 => 2 | .B3 => 3
  | .C1 => 2 | .C2 => 4 | .C3 => 4
  | .D1 => 6 | .D2 => 3 | .D3 => 4 | .D4 => 2
  | .E1 => 3

/-- Functional-group class of each printed monomer. -/
def hclass : Monomer → HClass
  | .A1 | .A2 | .A3 | .A4 => .boronicAcid
  | .B1 | .B2 | .B3 => .catechol
  | .C1 | .C2 | .C3 => .amine
  | .D1 | .D2 | .D3 | .D4 => .aldehyde
  | .E1 => .nitrile

/-- Geometry of the monomer's connectivity centre. -/
inductive Geometry | planar | tetrahedral
  deriving DecidableEq, Repr

/-- A4 (Si centre) and D3 (sp³ C centre) are tetrahedral; every other
monomer is a planar π-system. -/
def geometry : Monomer → Geometry
  | .A4 | .D3 => .tetrahedral
  | _ => .planar

/-- Functional-group compatibility under the problem's restriction to
boronate-ester, imine and C=C condensations: boronic acids pair only with
catechols, amines only with aldehydes, nitriles only with aldehydes. -/
def reactCompatible (m n : Monomer) : Prop :=
  match hclass m, hclass n with
  | .boronicAcid, .catechol | .catechol, .boronicAcid
  | .amine, .aldehyde | .aldehyde, .amine
  | .nitrile, .aldehyde | .aldehyde, .nitrile => True
  | _, _ => False

instance {m n : Monomer} : Decidable (reactCompatible m n) := by
  unfold reactCompatible
  cases hclass m <;> cases hclass n <;>
    first | exact .isTrue trivial | exact .isFalse id

/-- Signature of a topology: the connectivities required of the two roles
(unordered), whether the net is 2-dimensional (planar building blocks only),
and whether one role must be a tetrahedral centre. -/
structure Net where
  roleA : ℕ
  roleB : ℕ
  planarOnly : Bool
  needsTetrahedral : Bool
  deriving DecidableEq, Repr

/-- The seven role assignments read off the topology figures on Q3-3,
cross-checked against the printed table examples. -/
def tetragonal1Net : Net := ⟨4, 2, true, false⟩
def tetragonal2Net : Net := ⟨4, 2, true, false⟩
def hexagonal1Net  : Net := ⟨3, 2, true, false⟩

/-- **Reading of the two Hexagonal figures.**  Hexagonal 1 is the plain
honeycomb: one sublattice role is a 3-connecting vertex centre, the other a
2-connecting linker along the edges, role degrees **(3, 2)** (its printed
example A2+B3 has B3, three catechols, at the vertices).  Hexagonal 2 is the
**staggered** honeycomb in which *both* vertex sublattices are occupied by
3-connecting monomer junctions linked directly: its printed example E1+D2
pairs E1 (three benzylic nitriles) with D2 (three aldehydes), so each
vertex — whatever its colour — is a junction of three neighbouring monomers,
giving role degrees **(3, 3)**.  This is the only signature consistent with
the printed Hexagonal 2 example, since no 2-connecting monomer occurs in it. -/
def hexagonal2Net  : Net := ⟨3, 3, true, false⟩
def trigonalNet    : Net := ⟨6, 2, true, false⟩
def kagomeNet      : Net := ⟨4, 2, true, false⟩
def tetrahedralNet : Net := ⟨4, 2, false, true⟩

/-- Pair `(x, y)` realises net `t`: two distinct compatible monomers whose
connectivities match the two role degrees; 2D nets require planar building
blocks, and a net that needs a tetrahedral centre requires the role with
degree ≥ 3 to be tetrahedral. -/
def Realises (t : Net) (x y : Monomer) : Prop :=
  x ≠ y ∧
  reactCompatible x y ∧
  ((connectivity x = t.roleA ∧ connectivity y = t.roleB) ∨
   (connectivity y = t.roleA ∧ connectivity x = t.roleB)) ∧
  (t.planarOnly → geometry x = .planar ∧ geometry y = .planar) ∧
  (t.needsTetrahedral →
    (connectivity x = t.roleA → geometry x = .tetrahedral) ∧
    (connectivity y = t.roleA → geometry y = .tetrahedral))

/-- `Realises` is decidable once `reactCompatible` is. -/
instance {t : Net} {x y : Monomer} : Decidable (Realises t x y) := by
  unfold Realises
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Unordered pair equality, used to state exhaustiveness certificates.
Marked `@[reducible]` so kernel-level decision can see through it. -/
@[reducible] def samePair (x y a b : Monomer) : Prop :=
  (x = a ∧ y = b) ∨ (x = b ∧ y = a)

/-! ## The three printed example entries are reproduced -/

theorem supplied_hexagonal1 :
    Realises hexagonal1Net Monomer.A2 Monomer.B3 := by decide
theorem supplied_hexagonal2 :
    Realises hexagonal2Net Monomer.E1 Monomer.D2 := by decide
theorem supplied_kagome :
    Realises kagomeNet Monomer.C2 Monomer.D4 := by decide

/-! ## Complete enumeration of all realisers of each net

The library is finite (15 monomers), so the set of *all* admissible pairs
for each topology is computed by kernel-checked enumeration over the 15×15
ordered pairs.  These certificates justify the "XXX" cells: a cell is
marked XXX exactly when every realiser of that column's net is the printed
example or is already given in another filled cell. -/

/-- Square-net (role degrees 4 + 2, 2D) realisers: exactly the four
unordered pairs A3+B2, B1+A2, C2+D4, C3+D4.  Proved by exhaustive
enumeration (`fin_cases`) over the 15×15 ordered pairs of the printed
library, each case closed by kernel-checked decision. -/
theorem square_net_exhaustive (x y : Monomer)
    (h : Realises tetragonal1Net x y) :
    samePair x y .A3 .B2 ∨ samePair x y .B1 .A2 ∨
    samePair x y .C2 .D4 ∨ samePair x y .C3 .D4 := by
  revert h
  fin_cases x <;> fin_cases y <;> decide

/-- Honeycomb (3 + 2, 2D, Hexagonal 1) realisers: exactly A2+B3, A1+B2,
C1+D2, E1+D4. -/
theorem hexagonal1_net_exhaustive (x y : Monomer)
    (h : Realises hexagonal1Net x y) :
    samePair x y .A2 .B3 ∨ samePair x y .A1 .B2 ∨
    samePair x y .C1 .D2 ∨ samePair x y .E1 .D4 := by
  revert h
  fin_cases x <;> fin_cases y <;> decide


/-- Hexagonal 2 = the staggered honeycomb (role degrees 3 + 3): realisers are
exactly E1+D2 (the printed example) and A1+B3. -/
theorem hexagonal2_net_exhaustive (x y : Monomer)
    (h : Realises hexagonal2Net x y) :
    samePair x y .E1 .D2 ∨ samePair x y .A1 .B3 := by
  revert h
  fin_cases x <;> fin_cases y <;> decide

/-- Trigonal (6 + 2) realisers: only C1+D1.  D1 is the unique 6-connecting
monomer; its compatible partners are the amines, and C1 is the only
2-connecting amine. -/
theorem trigonal_net_exhaustive (x y : Monomer)
    (h : Realises trigonalNet x y) :
    samePair x y .C1 .D1 := by
  revert h
  fin_cases x <;> fin_cases y <;> decide

/-- Tetrahedral (tetrahedral 4-vertex + 2-linker, 3D) realisers: exactly
A4+B2 and C1+D3. -/
theorem tetrahedral_net_exhaustive (x y : Monomer)
    (h : Realises tetrahedralNet x y) :
    samePair x y .A4 .B2 ∨ samePair x y .C1 .D3 := by
  revert h
  fin_cases x <;> fin_cases y <;> decide

/-- Kagome has the same (4, 2) signature as the square nets, so its
realisers are the same four pairs; the printed example C2+D4 occupies the
Kagome column. -/
theorem kagome_net_exhaustive (x y : Monomer)
    (h : Realises kagomeNet x y) :
    samePair x y .A3 .B2 ∨ samePair x y .B1 .A2 ∨
    samePair x y .C2 .D4 ∨ samePair x y .C3 .D4 := by
  revert h
  fin_cases x <;> fin_cases y <;> decide

/-! ## The completed graded table

One entry per graded cell; every filled cell carries a combination that is
*new* (no combination appears twice in the whole table, including the
printed examples), and every XXX cell is backed by the exhaustive
certificates: all remaining realisers of that column are already used. -/

/-- The attempted additional cells of the table (two blank rows per column). -/
def tableFill : List (Net × Option (Monomer × Monomer)) :=
  [ (tetragonal1Net, some (.A3, .B2))   -- Tetragonal 1, row 1
  , (tetragonal1Net, none)              -- Tetragonal 1, row 2: XXX
  , (tetragonal2Net, some (.C3, .D4))   -- Tetragonal 2, row 1
  , (tetragonal2Net, none)              -- Tetragonal 2, row 2: XXX
  , (hexagonal1Net,  some (.A1, .B2))   -- Hexagonal 1, row 1
  , (hexagonal1Net,  some (.C1, .D2))   -- Hexagonal 1, row 2
  , (hexagonal2Net,  some (.A1, .B3))   -- Hexagonal 2, row 1
  , (hexagonal2Net,  none)              -- Hexagonal 2, row 2: XXX
  , (trigonalNet,    some (.C1, .D1))   -- Trigonal, row 1
  , (trigonalNet,    none)              -- Trigonal, row 2: XXX
  , (kagomeNet,      some (.B1, .A2))   -- Kagome, row 1
  , (kagomeNet,      none)              -- Kagome, row 2: XXX
  , (tetrahedralNet, some (.A4, .B2))   -- Tetrahedral, row 1
  , (tetrahedralNet, some (.C1, .D3))   -- Tetrahedral, row 2
  ]

/-- All combinations already committed in the table: the three printed
examples followed by every filled additional cell. -/
def usedPairs : List (Monomer × Monomer) :=
  [ (.A2, .B3), (.E1, .D2), (.C2, .D4) ] ++ (tableFill.filterMap Prod.snd)

/-- Unordered pair membership in a list. -/
def pairMem (x y : Monomer) (l : List (Monomer × Monomer)) : Prop :=
  (x, y) ∈ l ∨ (y, x) ∈ l

instance (x y : Monomer) (l : List (Monomer × Monomer)) :
    Decidable (pairMem x y l) := by
  unfold pairMem
  infer_instance

/-- Every filled entry realises its column's net. -/
theorem filled_entries_realise :
    Realises tetragonal1Net .A3 .B2 ∧ Realises tetragonal2Net .C3 .D4 ∧
    Realises hexagonal1Net .A1 .B2 ∧  Realises hexagonal1Net .C1 .D2 ∧
    Realises hexagonal2Net .A1 .B3 ∧  Realises trigonalNet .C1 .D1 ∧
    Realises kagomeNet .B1 .A2 ∧      Realises tetrahedralNet .A4 .B2 ∧
    Realises tetrahedralNet .C1 .D3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Master correctness theorem.** Every filled cell's combination is new
(it appears neither among the printed examples nor in any earlier filled
cell), and for every column *every* realiser of its net is already
accounted for: each exhibited triple of vertices/identical matches certifies
the absence of further valid combinations. -/
theorem table_fill_correct :
    -- filled entries are new (not printed, not repeated later)
    (¬ pairMem Monomer.A3 Monomer.B2 [(.A2, .B3), (.E1, .D2), (.C2, .D4)]) ∧
    (¬ pairMem Monomer.C3 Monomer.D4
        [(.A2, .B3), (.E1, .D2), (.C2, .D4), (.A3, .B2)]) ∧
    (¬ pairMem Monomer.A1 Monomer.B2
        [(.A2, .B3), (.E1, .D2), (.C2, .D4), (.A3, .B2), (.C3, .D4)]) ∧
    (¬ pairMem Monomer.C1 Monomer.D2
        [(.A2, .B3), (.E1, .D2), (.C2, .D4), (.A3, .B2), (.C3, .D4), (.A1, .B2)]) ∧
    (¬ pairMem Monomer.E1 Monomer.D4
        [(.A2, .B3), (.E1, .D2), (.C2, .D4), (.A3, .B2), (.C3, .D4), (.A1, .B2),
         (.C1, .D2)]) ∧
    (¬ pairMem Monomer.C1 Monomer.D1
        [(.A2, .B3), (.E1, .D2), (.C2, .D4), (.A3, .B2), (.C3, .D4), (.A1, .B2),
         (.C1, .D2), (.E1, .D4)]) ∧
    (¬ pairMem Monomer.B1 Monomer.A2
        [(.A2, .B3), (.E1, .D2), (.C2, .D4), (.A3, .B2), (.C3, .D4), (.A1, .B2),
         (.C1, .D2), (.E1, .D4), (.C1, .D1)]) ∧
    (¬ pairMem Monomer.A4 Monomer.B2
        [(.A2, .B3), (.E1, .D2), (.C2, .D4), (.A3, .B2), (.C3, .D4), (.A1, .B2),
         (.C1, .D2), (.E1, .D4), (.C1, .D1), (.B1, .A2)]) ∧
    (¬ pairMem Monomer.C1 Monomer.D3
        [(.A2, .B3), (.E1, .D2), (.C2, .D4), (.A3, .B2), (.C3, .D4), (.A1, .B2),
         (.C1, .D2), (.E1, .D4), (.C1, .D1), (.B1, .A2), (.A4, .B2)]) ∧
    -- XXX certificates: every realiser of every column is already committed
    (∀ x y : Monomer, Realises tetragonal1Net x y → pairMem x y usedPairs) ∧
    (∀ x y : Monomer, Realises tetragonal2Net x y → pairMem x y usedPairs) ∧
    (∀ x y : Monomer, Realises kagomeNet x y → pairMem x y usedPairs) ∧
    -- Hexagonal 1 has a *further* valid combination E1+D4 that fits in no
    -- remaining cell, so no XXX may be written in the Hexagonal 1 column
    (Realises hexagonal1Net .E1 .D4 ∧ ¬ pairMem Monomer.E1 Monomer.D4 usedPairs) ∧
    (∀ x y : Monomer, Realises hexagonal2Net x y → pairMem x y usedPairs) ∧
    (∀ x y : Monomer, Realises trigonalNet x y → pairMem x y usedPairs) ∧
    (∀ x y : Monomer, Realises tetrahedralNet x y → pairMem x y usedPairs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide -- A3+B2 is new
  · decide -- C3+D4 is new
  · decide -- A1+B2 is new
  · decide -- C1+D2 is new
  · decide -- A1+B3 is new
  · decide -- C1+D1 is new
  · decide -- B1+A2 is new
  · decide -- A4+B2 is new
  · decide -- C1+D3 is new
  · -- Tetragonal 1 coverage
    intro x y h
    rcases square_net_exhaustive x y h with h₁ | h₁ | h₁ | h₁ <;>
      rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · -- Tetragonal 2 coverage (same signature)
    intro x y h
    rcases square_net_exhaustive x y h with h₁ | h₁ | h₁ | h₁ <;>
      rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · -- Kagome coverage (same signature)
    intro x y h
    rcases kagome_net_exhaustive x y h with h₁ | h₁ | h₁ | h₁ <;>
      rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · exact ⟨by decide, by decide⟩ -- E1+D4 realises hex 1 but is uncommitted
  · -- Hexagonal 2 coverage
    intro x y h
    rcases hexagonal2_net_exhaustive x y h with h₁ | h₁ <;>
      rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · -- Trigonal coverage
    intro x y h
    rcases trigonal_net_exhaustive x y h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · -- Tetrahedral coverage
    intro x y h
    rcases tetrahedral_net_exhaustive x y h with h₁ | h₁ <;>
      rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

#print axioms table_fill_correct
#print axioms filled_entries_realise
#print axioms square_net_exhaustive
#print axioms hexagonal2_net_exhaustive
#print axioms trigonal_net_exhaustive
#print axioms tetrahedral_net_exhaustive
#print axioms supplied_hexagonal1
#print axioms supplied_hexagonal2
#print axioms supplied_kagome

end IChO2026T3A3
