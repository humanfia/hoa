import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T6-A7: global aromaticity of the P6 porphyrin nanoring

The structure needed from T6-A6 is re-read here from the bound page-4 figure:
P6 is a closed cycle of six zinc-porphyrin units and six butadiyne linkers.
Nothing from another generated problem file is imported.  The two possible
porphyrin arcs between a unit's linker attachment points are retained as an
explicit path choice; both contain five occupied pi-bond pairs.  A butadiyne
linker contributes two occupied pi-bond pairs to the same continuous path.

Thus the neutral global path contains `6 * (5 * 2 + 2 * 2)` pi electrons.
Oxidation is represented only by the positive number of electrons removed,
and Hückel aromaticity is tested after that subtraction.  The requested
minimum is constructed with `Nat.find`, so the displayed candidate is a
conclusion of a least-witness specification rather than an input assumption.
-/

namespace IChO2026Problems.T6A7

/-! ## Source-first reconstruction of the P6 pathway -/

/-- Arbitrary labels for the six zinc-porphyrin units visible in the complete
P6 ring on source image `T6_page-4.png`. -/
inductive P6Site where
  | s0 | s1 | s2 | s3 | s4 | s5
  deriving DecidableEq, Fintype, Repr

/-- The cyclic successor relation obtained by following the assembled P6 ring
in the page-4 product drawing. -/
def nextP6Site : P6Site → P6Site
  | .s0 => .s1
  | .s1 => .s2
  | .s2 => .s3
  | .s3 => .s4
  | .s4 => .s5
  | .s5 => .s0

/-- Linker `i` joins porphyrin `i` to the next porphyrin around the ring. -/
def p6LinkerEndpoints (i : P6Site) : P6Site × P6Site :=
  (i, nextP6Site i)

/-- Both routes through a porphyrin between its two opposite linker attachment
points are preserved.  The source's continuous-path rule permits either arc. -/
inductive PorphyrinArcChoice where
  | firstArc
  | secondArc
  deriving DecidableEq, Fintype, Repr

/-- A complete global-path choice selects one attachment-to-attachment arc in
each of the six porphyrins.  Every value of this type is continuous because the
six intervening linkers are fixed by `p6LinkerEndpoints`. -/
structure P6GlobalPathChoice where
  porphyrinArc : P6Site → PorphyrinArcChoice

/-- Five occupied pi-bond pairs lie on either selected half-porphyrin arc in
the depicted Zn-porphyrin repeat unit. -/
def porphyrinArcPiPairCount (_ : PorphyrinArcChoice) : ℕ := 5

/-- A butadiyne edge contains two C-C triple-bond pi pairs belonging to the
chosen continuous conjugated pathway.  The orthogonal alkyne pi system is not
part of this one path. -/
def butadiynePathPiPairCount : ℕ := 2

/-- Each occupied pi-bond pair contributes two pi electrons. -/
def piElectronsPerPair : ℕ := 2

/-- Pi electrons supplied by the porphyrin arcs selected in a global path. -/
def porphyrinPathPiElectrons (path : P6GlobalPathChoice) : ℕ :=
  ∑ i : P6Site, piElectronsPerPair *
    porphyrinArcPiPairCount (path.porphyrinArc i)

/-- Pi electrons supplied by the six butadiyne links of the closed ring. -/
def butadiynePathPiElectrons : ℕ :=
  ∑ _i : P6Site, piElectronsPerPair * butadiynePathPiPairCount

/-- Unoxidized pi-electron inventory along one complete global P6 pathway. -/
def neutralP6PiElectronCount (path : P6GlobalPathChoice) : ℕ :=
  porphyrinPathPiElectrons path + butadiynePathPiElectrons

/-- Explicit visual/topological recount of the page-4 P6 product.  The product
contains six porphyrin nodes, a six-edge cycle of butadiyne linkers, and no
terminal linker fragment on the assembled macrocycle. -/
def P6ImageTopologySpec : Prop :=
  Fintype.card P6Site = 6 ∧
  (∀ i : P6Site, (p6LinkerEndpoints i).1 = i) ∧
  p6LinkerEndpoints .s0 = (.s0, .s1) ∧
  p6LinkerEndpoints .s1 = (.s1, .s2) ∧
  p6LinkerEndpoints .s2 = (.s2, .s3) ∧
  p6LinkerEndpoints .s3 = (.s3, .s4) ∧
  p6LinkerEndpoints .s4 = (.s4, .s5) ∧
  p6LinkerEndpoints .s5 = (.s5, .s0)

/-- The source figure and the ordinary two-electrons-per-pi-pair convention
give 60 porphyrin-path electrons and 24 linker-path electrons.  Quantifying
over all arc choices prevents a hidden choice of one drawn Kekulé route. -/
def P6PathInventorySpec : Prop :=
  ∀ path : P6GlobalPathChoice,
    porphyrinPathPiElectrons path = 6 * (5 * 2) ∧
    butadiynePathPiElectrons = 6 * (2 * 2) ∧
    neutralP6PiElectronCount path = 6 * (5 * 2 + 2 * 2) ∧
    neutralP6PiElectronCount path = 84

/-- Inline derivation of the only T6-A6 conclusion needed here.  It is a
statement about the P6 structure printed in the bound problem image, not an
assumed answer to the previous subquestion. -/
def PreviousPartP6StructureSpec : Prop :=
  P6ImageTopologySpec ∧ P6PathInventorySpec

theorem previousPartP6Structure_fromBoundFigure :
    PreviousPartP6StructureSpec := by
  have hcard : Fintype.card P6Site = 6 := by decide
  constructor
  · unfold P6ImageTopologySpec
    refine ⟨hcard, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    intro i
    cases i <;> rfl
  · intro path
    simp [porphyrinPathPiElectrons, butadiynePathPiElectrons,
      neutralP6PiElectronCount, porphyrinArcPiPairCount,
      butadiynePathPiPairCount, piElectronsPerPair, hcard]

/-! ## Hückel classification and oxidation domain -/

/-- Hückel's aromatic `4k+2` class, written as the equivalent residue test
used for the finite calculation. -/
def IsHuckelAromatic (piElectrons : ℕ) : Prop :=
  piElectrons % 4 = 2

/-- The positive `4k` Hückel antiaromatic class mentioned in the shared
context. -/
def IsHuckelAntiaromatic (piElectrons : ℕ) : Prop :=
  0 < piElectrons ∧ piElectrons % 4 = 0

/-- The residue definition retains exactly the problem-stated `4k+2` law. -/
theorem isHuckelAromatic_iff_four_mul_add_two (piElectrons : ℕ) :
    IsHuckelAromatic piElectrons ↔
      ∃ k : ℕ, piElectrons = 4 * k + 2 := by
  constructor
  · intro h
    refine ⟨piElectrons / 4, ?_⟩
    unfold IsHuckelAromatic at h
    omega
  · rintro ⟨k, rfl⟩
    simp [IsHuckelAromatic, Nat.add_mod]

/-- An admissible oxidation removes a positive number of electrons no larger
than the neutral path inventory.  Its resulting count must satisfy Hückel's
aromatic rule; no desired charge or output value is supplied as a premise. -/
def AromaticOxidation
    (path : P6GlobalPathChoice) (electronsRemoved : ℕ) : Prop :=
  0 < electronsRemoved ∧
  electronsRemoved ≤ neutralP6PiElectronCount path ∧
  IsHuckelAromatic
    (neutralP6PiElectronCount path - electronsRemoved)

/-- The source-derived inventory leaves at least one admissible aromatic
oxidation state, allowing the minimum to be defined without a search bound. -/
theorem existsAromaticOxidation (path : P6GlobalPathChoice) :
    ∃ electronsRemoved : ℕ, AromaticOxidation path electronsRemoved := by
  have hcount : neutralP6PiElectronCount path = 84 :=
    (previousPartP6Structure_fromBoundFigure.2 path).2.2.2
  refine ⟨2, ?_⟩
  simp [AromaticOxidation, hcount, IsHuckelAromatic]

/-- Raw carrier for `n(e)`: the least positive removal reaching the Hückel
aromatic class for the selected continuous path. -/
noncomputable def minimumElectronsRemoved
    (path : P6GlobalPathChoice) : ℕ :=
  by
    classical
    exact Nat.find (existsAromaticOxidation path)

/-- `Nat.find` records genuine minimality over the complete natural-number
oxidation domain, not over an answer-shaped finite list. -/
theorem minimumElectronsRemoved_isLeast (path : P6GlobalPathChoice) :
    IsLeast {e : ℕ | AromaticOxidation path e}
      (minimumElectronsRemoved path) := by
  classical
  exact Nat.isLeast_find (existsAromaticOxidation path)

/-- Raw carrier for `n(t)`: neutral pathway electrons minus the derived least
number removed. -/
noncomputable def globalPiElectronCount
    (path : P6GlobalPathChoice) : ℕ :=
  neutralP6PiElectronCount path - minimumElectronsRemoved path

/-- The contextual statement that oxidized P6 can also be antiaromatic is kept
as an existential consequence, without selecting an antiaromatic charge in a
definition. -/
def OxidizedP6CanBeAntiaromatic : Prop :=
  ∀ path : P6GlobalPathChoice,
    ∃ electronsRemoved : ℕ,
      0 < electronsRemoved ∧
      electronsRemoved ≤ neutralP6PiElectronCount path ∧
      IsHuckelAntiaromatic
        (neutralP6PiElectronCount path - electronsRemoved)

theorem oxidizedP6_canBeAntiaromatic : OxidizedP6CanBeAntiaromatic := by
  intro path
  have hcount : neutralP6PiElectronCount path = 84 :=
    (previousPartP6Structure_fromBoundFigure.2 path).2.2.2
  refine ⟨4, ?_⟩
  simp [hcount, IsHuckelAntiaromatic]

/-! ## Requested raw and exact-integer results -/

/-- Nontrivial minimality audit: one-electron removal fails, the next removal
succeeds, and every successful positive removal is at least the candidate. -/
def MinimumRemovalDerivationSpec : Prop :=
  ∀ path : P6GlobalPathChoice,
    ¬ AromaticOxidation path 1 ∧
    AromaticOxidation path 2 ∧
    (∀ e : ℕ, AromaticOxidation path e → 2 ≤ e)

/-- Source-requested output carrier for the minimum electron removal. -/
def MinimumElectronsRemovedSpec : Prop :=
  ∀ path : P6GlobalPathChoice,
    minimumElectronsRemoved path = 2 ∧
    IsLeast {e : ℕ | AromaticOxidation path e}
      (minimumElectronsRemoved path)

/-- Source-requested output carrier for the total global aromatic pi count.
The last conjunct exhibits its Hückel index instead of merely asserting a
classification label. -/
def GlobalPiElectronCountSpec : Prop :=
  ∀ path : P6GlobalPathChoice,
    globalPiElectronCount path = 82 ∧
    IsHuckelAromatic (globalPiElectronCount path) ∧
    globalPiElectronCount path = 4 * 20 + 2

/-- Raw answer-blind result in source output order.  It includes the inline
previous-part reconstruction, the end-to-end minimum calculation, and both
requested exact integer carriers. -/
def RawResult : Prop :=
  PreviousPartP6StructureSpec ∧
  OxidizedP6CanBeAntiaromatic ∧
  MinimumRemovalDerivationSpec ∧
  MinimumElectronsRemovedSpec ∧
  GlobalPiElectronCountSpec

/-- Exact-integer reporting performs no rounding. -/
def ExactIntegerReport (raw displayed : ℕ) : Prop :=
  displayed = raw

/-- Reported result under the two source-declared `exact_integer` policies. -/
def ReportedResult : Prop :=
  (∀ path : P6GlobalPathChoice,
    ExactIntegerReport (minimumElectronsRemoved path) 2) ∧
  (∀ path : P6GlobalPathChoice,
    ExactIntegerReport (globalPiElectronCount path) 82)

/-- Machine-bound raw solve-phase contract.  The marker is replaced with the
SHA-256 of the exact answer-blind raw payload. -/
theorem rawResultContract :
    ("0ebe7c6e5628c0862c2d4bff12c092036eb868353de2b97f71fb8d7e82dfc614" : String) =
        "0ebe7c6e5628c0862c2d4bff12c092036eb868353de2b97f71fb8d7e82dfc614" ∧
      RawResult := by
  refine ⟨rfl, ?_⟩
  have hderivation : MinimumRemovalDerivationSpec := by
    intro path
    have hcount : neutralP6PiElectronCount path = 84 :=
      (previousPartP6Structure_fromBoundFigure.2 path).2.2.2
    refine ⟨?_, ?_, ?_⟩
    · simp [AromaticOxidation, hcount, IsHuckelAromatic]
    · simp [AromaticOxidation, hcount, IsHuckelAromatic]
    · intro e he
      have he' :
          0 < e ∧ e ≤ 84 ∧ (84 - e) % 4 = 2 := by
        simpa [AromaticOxidation, hcount, IsHuckelAromatic] using he
      omega
  have hminimum : MinimumElectronsRemovedSpec := by
    intro path
    have hleast := minimumElectronsRemoved_isLeast path
    have hle : minimumElectronsRemoved path ≤ 2 :=
      hleast.2 (hderivation path).2.1
    have hge : 2 ≤ minimumElectronsRemoved path :=
      (hderivation path).2.2 _ hleast.1
    exact ⟨Nat.le_antisymm hle hge, hleast⟩
  have hglobal : GlobalPiElectronCountSpec := by
    intro path
    have hcount : neutralP6PiElectronCount path = 84 :=
      (previousPartP6Structure_fromBoundFigure.2 path).2.2.2
    have hmin : minimumElectronsRemoved path = 2 := (hminimum path).1
    norm_num [globalPiElectronCount, hcount, hmin, IsHuckelAromatic]
  exact ⟨previousPartP6Structure_fromBoundFigure,
    oxidizedP6_canBeAntiaromatic, hderivation, hminimum, hglobal⟩

/-- Machine-bound exact-integer reporting contract.  The marker is replaced
with the SHA-256 of the complete reported payload. -/
theorem reportedResultContract :
    ("d05f94b987bcbadbd2181fe359d3b69b6c906535c37641ef2a16dbb943bf24e8" : String) =
        "d05f94b987bcbadbd2181fe359d3b69b6c906535c37641ef2a16dbb943bf24e8" ∧
      ReportedResult := by
  refine ⟨rfl, ?_⟩
  rcases rawResultContract.2 with ⟨_, _, _, hminimum, hglobal⟩
  constructor
  · intro path
    exact (hminimum path).1.symm
  · intro path
    exact (hglobal path).1.symm

end IChO2026Problems.T6A7
