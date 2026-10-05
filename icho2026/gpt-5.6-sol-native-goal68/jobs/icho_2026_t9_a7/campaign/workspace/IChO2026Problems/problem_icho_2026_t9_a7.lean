import Mathlib

/-!
# IChO 2026 T9-A7: sodium-adduct masses after hexo-5-enose degradation

The declarations in `SourceData` transcribe only information printed in the
problem (including the structural drawing on Q9-4) or the conventional
expansion `AcO = CH₃COO`.  The fragment formulas and both requested `m/z`
values are then derived below.
-/

namespace IChO2026Problems.T9A7

/-- Atom counts in a neutral formula.  Nitrogen and other elements are absent
from every component drawn for the two T9-A7 degradation fragments. -/
structure CHOFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

namespace CHOFormula

/-- Component-wise molecular-formula addition. -/
def add (a b : CHOFormula) : CHOFormula where
  carbon := a.carbon + b.carbon
  hydrogen := a.hydrogen + b.hydrogen
  oxygen := a.oxygen + b.oxygen

/-- `n` copies of one molecular-formula component. -/
def scale (n : ℕ) (a : CHOFormula) : CHOFormula where
  carbon := n * a.carbon
  hydrogen := n * a.hydrogen
  oxygen := n * a.oxygen

/-- Nominal neutral mass obtained from the integer atomic masses requested in
the problem: C = 12, H = 1, O = 16. -/
def nominalMass (a : CHOFormula) : ℕ :=
  12 * a.carbon + a.hydrogen + 16 * a.oxygen

end CHOFormula

namespace SourceData

/-- β-CD has seven glucopyranoside units (Q9-1). -/
def betaCDUnitCount : ℕ := 7

/-- Number of the initially deprotected unit in the numbered Q9-3 template. -/
def firstDeprotectedUnit : ℕ := 1

/-- Q9-3 states that the protic group on unit 1 directs the next primary
debenzylation to unit 4 when that position is available. -/
def secondDeprotectedUnit : ℕ := 4

/-- Formula printed under the bracketed intact perbenzylated residue on Q9-4. -/
def intactResidue : CHOFormula :=
  { carbon := 27, hydrogen := 28, oxygen := 5 }

/-- Formula printed under the bracketed enose-end component on Q9-4. -/
def degradedEnd : CHOFormula :=
  { carbon := 22, hydrogen := 25, oxygen := 4 }

/-- The other end in the Q9-4 product drawing is labelled `AcO`.  Expanding
the conventional acetoxy abbreviation as `CH₃COO` gives C₂H₃O₂. -/
def acetoxyEnd : CHOFormula :=
  { carbon := 2, hydrogen := 3, oxygen := 2 }

/-- Integer sodium atomic mass used for a sodium adduct. -/
def sodiumMass : ℕ := 23

end SourceData

open CHOFormula SourceData

/-- The number of intact residues strictly between units 1 and 4 in the
increasing direction around the numbered β-CD template. -/
def shortArcResidues : ℕ :=
  secondDeprotectedUnit - firstDeprotectedUnit - 1

/-- The other arc contains all remaining intact residues: from seven total
units remove the two degraded units and the intact units of the short arc. -/
def longArcResidues : ℕ :=
  betaCDUnitCount - 2 - shortArcResidues

theorem degradation_arc_counts :
    shortArcResidues = 2 ∧ longArcResidues = 3 := by
  norm_num [shortArcResidues, longArcResidues, betaCDUnitCount,
    firstDeprotectedUnit, secondDeprotectedUnit]

/-- A degradation fragment consists of one printed enose-end component, the
acetoxy group at its other cut end, and `n` intact bracketed residues. -/
def fragmentFormula (n : ℕ) : CHOFormula :=
  add (add degradedEnd acetoxyEnd) (scale n intactResidue)

theorem first_fragment_formula :
    fragmentFormula shortArcResidues =
      { carbon := 78, hydrogen := 84, oxygen := 16 } := by
  norm_num [fragmentFormula, shortArcResidues, SourceData.secondDeprotectedUnit,
    SourceData.firstDeprotectedUnit, CHOFormula.add, CHOFormula.scale,
    SourceData.degradedEnd, SourceData.acetoxyEnd, SourceData.intactResidue]

theorem second_fragment_formula :
    fragmentFormula longArcResidues =
      { carbon := 105, hydrogen := 112, oxygen := 21 } := by
  norm_num [fragmentFormula, longArcResidues, shortArcResidues,
    SourceData.betaCDUnitCount, SourceData.secondDeprotectedUnit,
    SourceData.firstDeprotectedUnit, CHOFormula.add, CHOFormula.scale,
    SourceData.degradedEnd, SourceData.acetoxyEnd, SourceData.intactResidue]

/-- Since `[M+Na]⁺` has charge magnitude one, its nominal `m/z` is the neutral
nominal mass plus the integer mass 23 of one sodium atom. -/
def sodiumAdductMz (neutral : CHOFormula) : ℕ :=
  nominalMass neutral + sodiumMass

/-- Requested first output: the sodium adduct of the three-residue (short-arc)
degradation product has `m/z = 1299`. -/
theorem first_fragment_mz :
    sodiumAdductMz (fragmentFormula shortArcResidues) = 1299 := by
  norm_num [sodiumAdductMz, CHOFormula.nominalMass, fragmentFormula,
    shortArcResidues, SourceData.secondDeprotectedUnit,
    SourceData.firstDeprotectedUnit, CHOFormula.add, CHOFormula.scale,
    SourceData.degradedEnd, SourceData.acetoxyEnd, SourceData.intactResidue,
    SourceData.sodiumMass]

/-- Requested second output: the sodium adduct of the four-residue (long-arc)
degradation product has `m/z = 1731`. -/
theorem second_fragment_mz :
    sodiumAdductMz (fragmentFormula longArcResidues) = 1731 := by
  norm_num [sodiumAdductMz, CHOFormula.nominalMass, fragmentFormula,
    longArcResidues, shortArcResidues, SourceData.betaCDUnitCount,
    SourceData.secondDeprotectedUnit, SourceData.firstDeprotectedUnit,
    CHOFormula.add, CHOFormula.scale, SourceData.degradedEnd,
    SourceData.acetoxyEnd, SourceData.intactResidue, SourceData.sodiumMass]

/-- Both exact integer outputs requested by T9-A7. -/
theorem t9_a7_answer :
    sodiumAdductMz (fragmentFormula shortArcResidues) = 1299 ∧
    sodiumAdductMz (fragmentFormula longArcResidues) = 1731 := by
  exact ⟨first_fragment_mz, second_fragment_mz⟩

#print axioms degradation_arc_counts
#print axioms first_fragment_formula
#print axioms second_fragment_formula
#print axioms first_fragment_mz
#print axioms second_fragment_mz
#print axioms t9_a7_answer

end IChO2026Problems.T9A7
