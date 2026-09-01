/-
Copyright (c) 2026 Archon answer-blind IChO formalization project. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon chemistry-formalize agent
-/
import IChO2026Chem

/-!
# IChO 2026, Problem T9, subquestion 9.3 (target `icho_2026_t9_a3`)

**Problem.** (Sealed problem bundle: T9 page 2, question 9.3, with the scheme
on T9 page 2 and the shared context on T9 page 1.)  Cyclodextrins (CD) are
cyclic oligosaccharides of glucose subunits joined by α-1,4-glycosidic bonds;
α-, β- and γ-CD contain 6, 7 and 8 α-D-glucopyranoside units.  On T9 page 2 the
β-CD template (three free OH groups per unit: the secondary 2-OH and 3-OH and
the primary 6-CH₂OH; subscript 7) is flanked by two arrows: to the right,
`1) TsCl (7 equiv.), Py; 2) NaOH, H₂O, 60 °C` gives Stoddart's compound K
(9.2, a different subquestion); to the left, `1) NaIO₄; 2) NaBH₄, H₂O;
3) Ac₂O, Py` gives macrocycle **X**.

**Current subquestion (9.3).**  Determine the ring size `rs` of macrocycle X
and give the number of stereocentres `sc` in X.

**Requested outputs.**  (i) `rs`, the ring size of X (exact integer);
(ii) `sc`, the number of stereocentres in X (exact integer).

## Derivation (from problem-side evidence only)

* **Unit count.**  X is drawn from the β-CD template (subscript 7 on
  T9 page 2; shared context: β-CD contains 7 α-D-glucopyranoside units;
  T9 page 1 structure labelled "n = 7, β-CD"), so X has 7 residues.
* **Periodate selectivity.**  In each unit the free OH groups are at C2, C3
  and C6 (template, T9 page 2); C1 and C4 carry the glycosidic ether oxygens
  and C5 bears the ring oxygen.  The only *vicinal* free diol is the
  C2–C3 diol (C6–OH has no OH-bearing neighbour).  NaIO₄ cleaves exactly the
  C–C bond of a vicinal diol (Malaprade oxidation, trusted general law), so
  the C2–C3 bond of each unit is cleaved and the pyranose ring opens to a
  dialdehyde (formyl groups at the former C2 and C3).
* **Reduction and acetylation.**  NaBH₄ reduces each –CHO to –CH₂OH (two
  identical H atoms: no new stereocentre); Ac₂O/Py then acetylates every free
  OH (trusted general laws).  Neither step changes the backbone connectivity.
* **Ring size.**  After C2–C3 cleavage, C2 and C3 are exocyclic –CH₂OAc arms
  on C1 and C4, and C6 is the exocyclic –CH₂OAc on C5.  The closed
  macrocyclic loop of X therefore runs through exactly five atoms per unit —
  C1, the glycosidic oxygen, C4, C5 and the ring oxygen O5 — giving
  `rs = 5 * 7 = 35`.
* **Stereocentres.**  Per unit, C1 (substituents O5, glycosidic O, C2 arm, H),
  C4 (glycosidic O, C5, C3 arm, H) and C5 (C4, C6 arm, O5, H) remain sp³
  stereocentres; C2, C3 and C6 are achiral CH₂ carbons and the ether oxygens
  are not configurationally stable stereocentres.  Hence
  `sc = 3 * 7 = 21`.

The previous part T9-A2 (compound K) is contextual only: the scheme makes X
directly from β-CD, and K (one free OH per unit) cannot undergo the
periodate cleavage; nothing from T9-A2 enters the derivation above.

## Reporting

Both outputs carry the source reporting policy `exact_integer`
(problem-output type): the exact counts are reported unchanged, i.e. the
reporting quantum is 1 on the integer lattice and the tie rule never applies.
-/

namespace IChO2026Problems.Icho2026T9A3

/-! ## Unit inventory and β-CD structure (problem text and images) -/

/-- Number of α-D-glucopyranoside units in β-cyclodextrin (shared context:
"β-cyclodextrin contain[s] … 7 α-D-glucopyranoside units"; T9 page 1 structure
labelled "n = 7, β-CD"; the X-synthesis template on T9 page 2 carries the
subscript 7). -/
def betaCDUnitCount : ℕ := 7

/-- The per-unit atom inventory of one α-1,4-linked α-D-glucopyranoside
residue relevant to the synthesis of X: the five ring carbons C1–C5, the
hydroxymethyl carbon C6, the pyranose ring oxygen O5 (`ringO`), and the
α-1,4-glycosidic oxygen (`glycosidicO`) joining C1 of this unit to C4 of the
next (provenance: `problem_image` — the CD templates on T9 pages 1–2). -/
inductive UnitAtom where
  | C1 | C2 | C3 | C4 | C5 | C6 | ringO | glycosidicO
  deriving DecidableEq

/-- All eight per-unit atom positions, each listed once. -/
def allUnitAtoms : List UnitAtom :=
  [.C1, .C2, .C3, .C4, .C5, .C6, .ringO, .glycosidicO]

/-- Free hydroxy-bearing atoms of a β-CD glucopyranoside unit: the secondary
2-OH and 3-OH and the primary 6-CH₂OH, as drawn in the X/K template on
T9 page 2 (three free OH groups per unit).  C1 and C4 carry the glycosidic
ether oxygens and C5 bears the ring oxygen, so they have no free OH. -/
def hasFreeHydroxyInBetaCD : UnitAtom → Bool
  | .C2 | .C3 | .C6 => true
  | _ => false

/-- Covalent adjacency among the per-unit atoms of an α-1,4-linked
glucopyranoside unit: the pyranose ring path C1–C2–C3–C4–C5–O5–C1, the
C5–C6 exocyclic bond, and the glycosidic oxygen bridging C1 of this unit and
C4 (of the next unit; within this per-unit adjacency both endpoints are
recorded).  Provenance: `problem_image` (chair template and the "n = 7, β-CD"
structure) and `problem_text` (α-1,4-glycosidic bonds). -/
def bondedInUnit : UnitAtom → UnitAtom → Bool
  | .C1, .C2 | .C2, .C1 => true
  | .C2, .C3 | .C3, .C2 => true
  | .C3, .C4 | .C4, .C3 => true
  | .C4, .C5 | .C5, .C4 => true
  | .C5, .ringO | .ringO, .C5 => true
  | .ringO, .C1 | .C1, .ringO => true
  | .C5, .C6 | .C6, .C5 => true
  | .C1, .glycosidicO | .glycosidicO, .C1 => true
  | .glycosidicO, .C4 | .C4, .glycosidicO => true
  | _, _ => false

/-- A free vicinal diol pair: two bonded atoms that both bear a free OH.
NaIO₄ cleaves exactly the C–C bond of a free vicinal diol, oxidising each
carbon to a formyl group (Malaprade oxidation; trusted general law). -/
def isFreeVicinalDiolPair (a b : UnitAtom) : Bool :=
  hasFreeHydroxyInBetaCD a && hasFreeHydroxyInBetaCD b && bondedInUnit a b

/-- Periodate selectivity, derived (not assumed): the only free vicinal diol
in a β-CD glucopyranoside unit is the 2,3-diol — the primary 6-OH has no
OH-bearing neighbour.  Hence NaIO₄ cleaves exactly the C2–C3 bond of each
unit, opening the pyranose ring to the C2/C3 dialdehyde. -/
theorem free_vicinal_diol_unique :
    (allUnitAtoms.product allUnitAtoms).filter
        (fun p => isFreeVicinalDiolPair p.1 p.2) =
      [(.C2, .C3), (.C3, .C2)] := by
  decide

/-! ## Atom fates in macrocycle X -/

/-- Per-unit atoms lying in the macrocyclic backbone of X.  After the C2–C3
cleavage, C2 and C3 are exocyclic –CH₂OAc arms on C1 and C4 (NaBH₄ reduces
the formyls to –CH₂OH; Ac₂O/Py acetylates; trusted general laws), and C6 is
the exocyclic –CH₂OAc group on C5.  The closed macrocycle loop of X therefore
runs through C1, the glycosidic oxygen, C4, C5 and the ring oxygen O5 of each
unit — five atoms per unit — and closes after the seven units. -/
def inMacrocycleBackboneOfX : UnitAtom → Bool
  | .C1 | .glycosidicO | .C4 | .C5 | .ringO => true
  | .C2 | .C3 | .C6 => false

/-- Macrocyclic backbone atoms contributed by each unit of X. -/
def ringBackboneAtomsPerUnit : ℕ :=
  (allUnitAtoms.filter inMacrocycleBackboneOfX).length

/-- Each unit of X contributes exactly 5 atoms to the macrocycle ring. -/
theorem ringBackboneAtomsPerUnit_eq : ringBackboneAtomsPerUnit = 5 := by
  decide

/-- Stereogenic atoms of X.  C1 (bonded to O5, the glycosidic O, the C2
–CH₂OAc arm and H), C4 (bonded to the glycosidic O of the previous unit, C5,
the C3 –CH₂OAc arm and H) and C5 (bonded to C4, the C6 –CH₂OAc group, O5 and
H) remain sp³ carbons with four different substituents.  C2 and C3 pass
through planar formyl carbons to –CH₂OAc groups and C6 is –CH₂OAc: all three
bear two identical H atoms and are not stereogenic; the ether oxygens are not
configurationally stable stereocentres.  No step creates a stereocentre. -/
def isStereocentreInX : UnitAtom → Bool
  | .C1 | .C4 | .C5 => true
  | .C2 | .C3 | .C6 | .ringO | .glycosidicO => false

/-- Stereocentres contributed by each unit of X. -/
def stereocentresPerUnitInX : ℕ :=
  (allUnitAtoms.filter isStereocentreInX).length

/-- Each unit of X contributes exactly 3 stereocentres (C1, C4, C5). -/
theorem stereocentresPerUnitInX_eq : stereocentresPerUnitInX = 3 := by
  decide

/-! ## Raw (unrounded) quantities -/

/-- Raw ring size of macrocycle X: backbone atoms per unit × the seven β-CD
units. -/
def macrocycleXRingSizeRaw : ℕ := ringBackboneAtomsPerUnit * betaCDUnitCount

/-- Raw stereocentre count of X: stereocentres per unit × the seven β-CD
units. -/
def macrocycleXStereocentreCountRaw : ℕ := stereocentresPerUnitInX * betaCDUnitCount

/-- Exact value of the raw ring size: `5 * 7 = 35`. -/
theorem macrocycleXRingSizeRaw_eq : macrocycleXRingSizeRaw = 35 := by
  decide

/-- Exact value of the raw stereocentre count: `3 * 7 = 21`. -/
theorem macrocycleXStereocentreCountRaw_eq : macrocycleXStereocentreCountRaw = 21 := by
  decide

/-! ## Raw and reported result specifications -/

/-- Raw derivation specification covering both requested outputs before any
reporting step: the β-CD unit count is 7, the per-unit structural counts are
5 backbone atoms and 3 stereocentres (fixed by the periodate / reduction /
acetylation analysis above), and the raw outputs are the per-unit counts
multiplied by the unit count — the unrounded governing relations
`rs = 5 * 7` and `sc = 3 * 7`. -/
def RawResultSpec : Prop :=
  betaCDUnitCount = 7
  ∧ ringBackboneAtomsPerUnit = 5
  ∧ stereocentresPerUnitInX = 3
  ∧ macrocycleXRingSizeRaw = ringBackboneAtomsPerUnit * betaCDUnitCount
  ∧ macrocycleXStereocentreCountRaw = stereocentresPerUnitInX * betaCDUnitCount

/-- Reported (final) specification: under the problem-output-type reporting
policy both outputs are exact integers — ring size `rs = 35` and stereocentre
count `sc = 21` — each reported unchanged at quantum 1 on the integer lattice
(the tie rule never applies to an exact integer). -/
def ReportedResultSpec : Prop :=
  macrocycleXRingSizeRaw = 35
  ∧ macrocycleXStereocentreCountRaw = 21
  ∧ IChO2026Chem.Reporting.ReportsAtQuantum (macrocycleXRingSizeRaw : ℝ) 35 1
  ∧ IChO2026Chem.Reporting.ReportsAtQuantum (macrocycleXStereocentreCountRaw : ℝ) 21 1

/-- Raw result certificate: binds the answer-blind raw-role payload digest to
`RawResultSpec`. -/
theorem rawResultCertificate :
    ("777940e4bf2d54fd14fe22d8a352576d8733601eaf2a0f4dd6ea981de6367775" : String)
      = "777940e4bf2d54fd14fe22d8a352576d8733601eaf2a0f4dd6ea981de6367775"
      ∧ RawResultSpec := by
  exact ⟨rfl, rfl, by decide, by decide, rfl, rfl⟩

/-- Reported result certificate: binds the answer-blind reported-role payload
digest to `ReportedResultSpec`. -/
theorem reportedResultCertificate :
    ("89f2b63ebc9a8da3f13bbd4c77a5a5cd5a8729ab5c5387d9ff76e8452d61f38e" : String)
      = "89f2b63ebc9a8da3f13bbd4c77a5a5cd5a8729ab5c5387d9ff76e8452d61f38e"
      ∧ ReportedResultSpec := by
  have h35 : macrocycleXRingSizeRaw = 35 := by decide
  have h21 : macrocycleXStereocentreCountRaw = 21 := by decide
  refine ⟨rfl, h35, h21, ?_, ?_⟩
  · refine ⟨one_pos, ⟨35, by norm_num⟩, ?_⟩
    rw [h35]
    rw [if_pos (by norm_num : (0 : ℝ) ≤ ((35 : ℕ) : ℝ))]
    exact ⟨by norm_num, by norm_num⟩
  · refine ⟨one_pos, ⟨21, by norm_num⟩, ?_⟩
    rw [h21]
    rw [if_pos (by norm_num : (0 : ℝ) ≤ ((21 : ℕ) : ℝ))]
    exact ⟨by norm_num, by norm_num⟩

end IChO2026Problems.Icho2026T9A3
