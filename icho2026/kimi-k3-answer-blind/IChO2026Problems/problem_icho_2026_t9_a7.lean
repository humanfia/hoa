import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T9, Part A7 (problem_icho_2026_t9_a7)

Answer-blind formalization of:

> Calculate the m/z value for the two [M+Na]+ peaks that were observed for the
> degradation products from L. Use integer values of atomic mass.

## Source evidence and provenance

* `icho_2026_source/image/T9_page-3.png` (printed page Q9-3): synthesis of L.
  beta-CD (7 glucopyranoside units; boxes show seven primary CH2OH groups and
  (OH)14 secondary hydroxy groups) is perbenzylated (1) NaH (30 equiv.),
  BnCl (30 equiv.)) and then partially debenzylated (2) DIBAL-H (2 equiv.))
  to give L.
* Shared problem text (Sinay directing rule): a single protic group (NH or
  OH) at unit 1 directs the *next* reductive debenzylation of a primary OH
  group to unit 4 of the macrocyclic ring (or to unit 3 if the unit 4
  position is not available).  In the synthesis of L every position is still
  benzylated when the first protic OH appears, so unit 4 is available and L
  carries its two free primary 6-OH groups at units 1 and 4.
* `icho_2026_source/image/T9_page-4.png` (printed page Q9-4): the
  hexo-5-enose degradation scheme.  A ring segment whose middle unit bears
  the free primary OH is treated with 1) I2, P(C6H5)3; 2) Zn, C3H7OH;
  3) NaBH4; 4) Ac2O, Py.  The modified unit becomes an open-chain
  hex-5-enose bearing one OAc (printed label C22H25O4) that remains
  glycosidically attached to the preceding 2,3,6-tri-O-benzyl glucopyranosyl
  unit (printed label C27H28O5), while the glycosidic bond at the anomeric
  carbon of the degraded unit is cleaved and the neighbouring unit is
  released with a new 4-OAc group.

## Component ledger (image_component_accounting)

* hex-5-enose piece, role `product_fragment`, multiplicity 1 per fragment:
  AcOCH2-CH(OBn)-CH(OBn)-CH(O-)-CH=CH2, counted as C22H25O4 (printed label,
  without the glycosidic bridge oxygen).
* 2,3,6-tri-O-benzyl glucopyranosyl unit, role `repeat_unit`, multiplicity k
  (= 2 or 3): counted as C27H28O5 (printed label: ring O, three benzyl ether
  oxygens, and one glycosidic oxygen at its anomeric carbon).
* 4-O-acetyl end cap, role `terminal_group`, multiplicity 1 per fragment:
  the C4-OH released at the cleavage is acetylated, contributing
  -O-CO-CH3 = C2H3O2 (AcO group drawn on the released unit).
* glycosidic bridge oxygens are carried inside the printed glucopyranosyl
  label (one per unit); no anonymous or catch-all material stream is used.

Fragment assembly: `degradationFragment k = C22H25O4 + k * C27H28O5 + C2H3O2`,
giving C78H84O16 for k = 2 and C105H112O21 for k = 3.

The closed material ledger `degradation_conservation` cross-checks the whole
transformation against L = C175H184O35 (perbenzyl-beta-CD C189H196O35 minus
two benzyl groups): L + 4 acetyl nets + 2 NaBH4 dihydrogen nets
= fragment1 + fragment2 + 2 removed C6 oxygens.

## Requested outputs

* `first_fragment_mz` : m/z of the [M+Na]+ adduct of the smaller fragment
  (two pyranose units; units 2,3 of the ring): 1299.
* `second_fragment_mz` : m/z of the [M+Na]+ adduct of the larger fragment
  (three pyranose units; units 5,6,7): 1731.
(Outputs are listed in ascending m/z, the standard MS reading order.)
-/

namespace IChO2026Problems.problem_icho_2026_t9_a7

/-- Elements occurring in the degradation products and in the sodium adduct. -/
inductive Element
  | C | H | O | Na
  deriving DecidableEq, Repr

/-- Problem-stipulated integer atomic masses: the subquestion requires integer
values of atomic mass.  The pinned CIAAW abridged standard weights
(C 12.011, H 1.0080, O 15.999, Na 22.990) round to exactly these integers.
Pinned dataset version ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+
contest-interpretation-v1+trusted-empirical-rules-v1, data sha256
11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5. -/
def integerAtomicMass : Element → ℕ
  | .C => 12
  | .H => 1
  | .O => 16
  | .Na => 23

/-- Molecular formula over C, H, O: the only elements appearing in the
degradation products (sodium enters only as the [M+Na]+ adduct). -/
structure MolFormula where
  c : ℕ
  h : ℕ
  o : ℕ
  deriving DecidableEq, Repr

/-- Componentwise addition of two formula blocks. -/
def MolFormula.add (f g : MolFormula) : MolFormula :=
  ⟨f.c + g.c, f.h + g.h, f.o + g.o⟩

/-- `n`-fold repetition of a formula block. -/
def MolFormula.scale (n : ℕ) (f : MolFormula) : MolFormula :=
  ⟨n * f.c, n * f.h, n * f.o⟩

/-- Integer molecular mass under the stipulated integer atomic masses. -/
def formulaMass (f : MolFormula) : ℕ :=
  f.c * integerAtomicMass .C + f.h * integerAtomicMass .H + f.o * integerAtomicMass .O

/-- m/z of the [M+Na]+ adduct (singly charged): neutral integer mass plus the
integer mass of sodium. -/
def sodiumAdductMz (f : MolFormula) : ℕ :=
  formulaMass f + integerAtomicMass .Na

/-- The hex-5-enose piece of the degradation, printed label C22H25O4 on
T9_page-4: AcOCH2-CH(OBn)-CH(OBn)-CH(O-)-CH=CH2, counted without the
glycosidic bridge oxygen that ties its C4 to the preceding pyranose unit. -/
def hexEnosePiece : MolFormula := ⟨22, 25, 4⟩

/-- A 2,3,6-tri-O-benzyl glucopyranosyl unit inside a fragment chain, printed
label C27H28O5 on T9_page-4: ring oxygen, three benzyl ether oxygens, and one
glycosidic oxygen at its anomeric carbon. -/
def glucopyranosylUnit : MolFormula := ⟨27, 28, 5⟩

/-- Terminal 4-O-acetyl cap: the C4-OH released when the anomeric bond of the
degraded unit breaks is acetylated in the Ac2O/Py step, contributing
-O-CO-CH3 = C2H3O2 (the AcO group drawn on the released unit, T9_page-4). -/
def acetylEndCap : MolFormula := ⟨2, 3, 2⟩

/-- A degradation chain that keeps `k` intact glucopyranosyl units: one
hex-5-enose piece, `k` glucopyranosyl units, and one 4-O-acetyl end cap. -/
def degradationFragment (k : ℕ) : MolFormula :=
  (hexEnosePiece.add (glucopyranosylUnit.scale k)).add acetylEndCap

/-- beta-CD ring size: 7 alpha-D-glucopyranoside units (shared context). -/
def ringSize : ℕ := 7

/-- Number of free primary 6-OH groups in L: DIBAL-H (2 equiv.) removes
exactly two primary benzyl ethers from perbenzyl-beta-CD (T9_page-3). -/
def modifiedUnitCount : ℕ := 2

/-- Ring position of the second debenzylated unit of L.  The problem quotes
the Sinay rule: the protic group at unit 1 directs the next debenzylation to
unit 4 whenever that position is available; in the synthesis of L it is
available, so the second free OH is at unit 4. -/
def secondModifiedPosition : ℕ := 4

/-- Pyranose units on the short arc between the modified units 1 and 4:
units 2 and 3, hence 4 - 1 - 1 = 2 units. -/
def shortArcUnits : ℕ := secondModifiedPosition - 1 - 1

/-- Pyranose units on the long arc: units 5, 6 and 7, hence 7 - 4 = 3. -/
def longArcUnits : ℕ := ringSize - secondModifiedPosition

/-- First degradation product of L: hex-5-enose plus the two pyranose units
of the short arc plus the 4-O-acetyl cap. -/
def firstFragment : MolFormula := degradationFragment shortArcUnits

/-- Second degradation product of L: hex-5-enose plus the three pyranose
units of the long arc plus the 4-O-acetyl cap. -/
def secondFragment : MolFormula := degradationFragment longArcUnits

/-- The two modified units and the two arcs partition the 7-membered ring. -/
theorem unit_partition : shortArcUnits + longArcUnits + modifiedUnitCount = ringSize := rfl

/-- The first fragment has formula C78H84O16. -/
theorem first_fragment_formula : firstFragment = ⟨78, 84, 16⟩ := rfl

/-- The second fragment has formula C105H112O21. -/
theorem second_fragment_formula : secondFragment = ⟨105, 112, 21⟩ := rfl

/-- Neutral integer mass of the first fragment: 78*12 + 84 + 16*16 = 1276. -/
theorem first_fragment_mass : formulaMass firstFragment = 1276 := rfl

/-- Neutral integer mass of the second fragment: 105*12 + 112 + 21*16 = 1708. -/
theorem second_fragment_mass : formulaMass secondFragment = 1708 := rfl

/-- Requested output `first_fragment_mz`: the [M+Na]+ peak of the smaller
degradation product appears at m/z 1299. -/
theorem first_fragment_mz : sodiumAdductMz firstFragment = 1299 := rfl

/-- Requested output `second_fragment_mz`: the [M+Na]+ peak of the larger
degradation product appears at m/z 1731. -/
theorem second_fragment_mz : sodiumAdductMz secondFragment = 1731 := rfl

/-- beta-Cyclodextrin, C42H70O35 = 7 x C6H10O5 glucopyranosyl residues. -/
def betaCD : MolFormula := ⟨42, 70, 35⟩

/-- Net formula change for benzylation -OH -> -OCH2Ph: +C7H6. -/
def benzylNet : MolFormula := ⟨7, 6, 0⟩

/-- Perbenzyl-beta-CD: all 21 hydroxy groups benzylated, C189H196O35. -/
def perbenzylBetaCD : MolFormula := betaCD.add (benzylNet.scale 21)

/-- L: perbenzyl-beta-CD after reductive removal of two benzyl groups
(two -OBn -> -OH), C175H184O35. -/
def lFormula : MolFormula := ⟨175, 184, 35⟩

/-- L is exactly perbenzyl-beta-CD minus two benzyl net blocks. -/
theorem lFormula_check : lFormula.add (benzylNet.scale 2) = perbenzylBetaCD := rfl

/-- Net formula change for acetylation -OH -> -OCOCH3: +C2H2O. -/
def acetylNet : MolFormula := ⟨2, 2, 1⟩

/-- Net H2 taken up per aldehyde reduced by NaBH4. -/
def dihydrogenNet : MolFormula := ⟨0, 2, 0⟩

/-- The C6 oxygen of each degraded unit leaves at the iodination step
(6-OH -> 6-I); this tracked stream keeps the ledger closed. -/
def removedC6Oxygen : MolFormula := ⟨0, 0, 1⟩

/-- Closed material ledger for the hexo-5-enose degradation of L:
L + four acetyl nets (one hex-5-enose C1-OAc and one terminal C4-OAc per
modified unit) + two NaBH4 dihydrogen nets
= first fragment + second fragment + two removed C6 oxygens.
Both sides are C183H196O39. -/
theorem degradation_conservation :
    (lFormula.add (acetylNet.scale 4)).add (dihydrogenNet.scale 2)
      = (firstFragment.add secondFragment).add (removedC6Oxygen.scale 2) := rfl

/-- Raw, unrounded result specification covering both requested outputs:
the exact integer m/z values of the two [M+Na]+ peaks. -/
def RawResultSpec : Prop :=
  sodiumAdductMz firstFragment = 1299 ∧ sodiumAdductMz secondFragment = 1731

/-- Reported result specification: the problem output type is an exact
integer, so each raw value is reported at the unit quantum with the
half-away-from-zero tie rule (which never triggers for an exact integer). -/
def ReportedResultSpec : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum (sodiumAdductMz firstFragment : ℝ) 1299 1 ∧
  IChO2026Chem.Reporting.ReportsAtQuantum (sodiumAdductMz secondFragment : ℝ) 1731 1

/-- The first [M+Na]+ value 1299 is already a multiple of the unit quantum. -/
theorem reported_first :
    IChO2026Chem.Reporting.ReportsAtQuantum (sodiumAdductMz firstFragment : ℝ) 1299 1 := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  rw [first_fragment_mz]
  refine ⟨by norm_num, ⟨1299, by norm_num⟩, ?_⟩
  rw [if_pos (by positivity)]
  norm_num

/-- The second [M+Na]+ value 1731 is already a multiple of the unit quantum. -/
theorem reported_second :
    IChO2026Chem.Reporting.ReportsAtQuantum (sodiumAdductMz secondFragment : ℝ) 1731 1 := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  rw [second_fragment_mz]
  refine ⟨by norm_num, ⟨1731, by norm_num⟩, ?_⟩
  rw [if_pos (by positivity)]
  norm_num

/-- Answer-blind raw-result contract: payload digest plus the raw
specification, both proved from the source-derived fragment formulas. -/
theorem raw_result_contract :
    ("2f09f82f5e601f1271b0b46486d27a5c6678ea54fb00dcbd7608cf0531721143" : String)
      = "2f09f82f5e601f1271b0b46486d27a5c6678ea54fb00dcbd7608cf0531721143"
      ∧ RawResultSpec :=
  ⟨rfl, first_fragment_mz, second_fragment_mz⟩

/-- Answer-blind reported-result contract: payload digest plus the reporting
specification at the exact-integer quantum. -/
theorem reported_result_contract :
    ("bad4d7a8e4fd310376ad8a47fb9b966e805fd1327d236fe5fa2d1953af5e33ea" : String)
      = "bad4d7a8e4fd310376ad8a47fb9b966e805fd1327d236fe5fa2d1953af5e33ea"
      ∧ ReportedResultSpec :=
  ⟨rfl, reported_first, reported_second⟩

end IChO2026Problems.problem_icho_2026_t9_a7
