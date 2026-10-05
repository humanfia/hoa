import Mathlib

/-!
# IChO 2026, problem T6.2: intermediates in the surface synthesis of C₁₄

The source figure starts from decachloroanthracene and labels four neutral
surface-dehalogenation arrows by the numbers of chlorine radicals lost.  This
file uses the clockwise numbering described below and represents every
perimeter C--C bond, both possible anthracene fusion bonds, every attached
chlorine, formal charge, unpaired electron, and stereochemical descriptor.

The AFM panels determine the chlorine-site and fusion-bond readouts.  The
displayed Lewis structures are then concrete valence-valid completions of
those readouts.  Their chosen radical and multiple-bond locations are one
resonance representative; the specification does not assert that this
representative is the only resonance drawing.
-/

namespace IChO2026Problems.T6A2

/-! ## Atom labels and local structural vocabulary -/

/-- The fourteen carbon atoms on the clockwise anthracene perimeter.  Index
`0` is C1 in the chemical description and index `13` is C14. -/
abbrev CarbonSite := Fin 14

def c1 : CarbonSite := 0
def c2 : CarbonSite := 1
def c3 : CarbonSite := 2
def c4 : CarbonSite := 3
def c5 : CarbonSite := 4
def c6 : CarbonSite := 5
def c7 : CarbonSite := 6
def c8 : CarbonSite := 7
def c9 : CarbonSite := 8
def c10 : CarbonSite := 9
def c11 : CarbonSite := 10
def c12 : CarbonSite := 11
def c13 : CarbonSite := 12
def c14 : CarbonSite := 13

/-- The two internal fusion bonds of the anthracene precursor. -/
inductive FusionBond where
  | left   -- C3--C12
  | right  -- C5--C10
  deriving DecidableEq, Fintype, Repr

/-- All species in the displayed transformation are adsorbed on a surface. -/
inductive ChemicalPhase where
  | surfaceAdsorbed
  deriving DecidableEq, Fintype, Repr

/-- No stereocentre occurs in these planar carbon/chlorine structures.  The
other constructors make the absence of stereochemistry an explicit datum. -/
inductive StereoDescriptor where
  | none
  | clockwise
  | anticlockwise
  deriving DecidableEq, Fintype, Repr

/-- Atom references include every carbon and the possible chlorine attached
to each numbered perimeter carbon.  A chlorine reference is present exactly
when its C--Cl bond order is one. -/
inductive AtomRef where
  | carbon (site : CarbonSite)
  | chlorine (attachedTo : CarbonSite)
  deriving DecidableEq, Fintype, Repr

/-- The finite material domain actually used by each arrow in the figure.
There is no anonymous material stream. -/
inductive StageSpecies where
  | carbonFramework
  | boundChlorine
  | chlorineRadical
  deriving DecidableEq, Fintype, Repr

def stageSpeciesDomain : Finset StageSpecies :=
  {.carbonFramework, .boundChlorine, .chlorineRadical}

/-- Carbon atoms in one unit of each ledger species. -/
def StageSpecies.carbonAtoms : StageSpecies → ℕ
  | .carbonFramework => 14
  | .boundChlorine => 0
  | .chlorineRadical => 0

/-- Chlorine atoms in one unit of each ledger species. -/
def StageSpecies.chlorineAtoms : StageSpecies → ℕ
  | .carbonFramework => 0
  | .boundChlorine => 1
  | .chlorineRadical => 1

/-- All three ledger species are formally neutral; the dot on `Cl•` records
an unpaired electron rather than ionic charge. -/
def StageSpecies.formalCharge : StageSpecies → ℤ
  | .carbonFramework => 0
  | .boundChlorine => 0
  | .chlorineRadical => 0

/-! ## Source states and quantitative arrow ledger -/

/-- Connectivity and inventory data visible before choosing a Lewis
resonance representative.  `chlorineBondOrder i = 1` means that the unique
chlorine at site `i` is attached by a single bond; zero means it is absent. -/
structure FrameworkState where
  chlorineBondOrder : CarbonSite → ℕ
  leftFusionPresent : Bool
  rightFusionPresent : Bool
  netFormalCharge : ℤ
  phase : ChemicalPhase

/-- The carbon inventory is fixed by the type `Fin 14`. -/
def frameworkCarbonCount : ℕ := Fintype.card CarbonSite

/-- Number of attached chlorine atoms in a framework state. -/
def attachedChlorineCount (state : FrameworkState) : ℕ :=
  (Finset.univ.filter (fun i => state.chlorineBondOrder i = 1)).card

/-- Every possible C--Cl bond is either absent or a single bond. -/
def FrameworkState.WellFormed (state : FrameworkState) : Prop :=
  ∀ i, state.chlorineBondOrder i = 0 ∨ state.chlorineBondOrder i = 1

/-- Read either named fusion bond from a framework state. -/
def FrameworkState.fusionPresent
    (state : FrameworkState) : FusionBond → Bool
  | .left => state.leftFusionPresent
  | .right => state.rightFusionPresent

/-- The para pair whose removal permits the corresponding retro-Bergman
opening in the anthracene skeleton shown in reaction (1). -/
def IsRetroBergmanTriggerSite : FusionBond → CarbonSite → Prop
  | .left, i => i = c2 ∨ i = c13
  | .right, i => i = c6 ∨ i = c9

/-- Both trigger chlorines for a fused six-membered ring are absent. -/
def TriggerPairCleared (state : FrameworkState) (fusion : FusionBond) : Prop :=
  ∀ i, IsRetroBergmanTriggerSite fusion i → state.chlorineBondOrder i = 0

/-- No attached chlorine is introduced by a `-n Cl•` arrow. -/
def NoChlorineAdded (before after : FrameworkState) : Prop :=
  ∀ i, after.chlorineBondOrder i = 1 → before.chlorineBondOrder i = 1

/-- The sites at which a chlorine atom is removed by an arrow. -/
def removedChlorineSites
    (before after : FrameworkState) : Finset CarbonSite :=
  Finset.univ.filter (fun i =>
    before.chlorineBondOrder i = 1 ∧ after.chlorineBondOrder i = 0)

/-- Number of neutral chlorine radicals in the only outgoing material stream. -/
def removedChlorineCount (before after : FrameworkState) : ℕ :=
  (removedChlorineSites before after).card

/-- Outcome-decisive atom, charge, and phase ledger for a displayed
dehalogenation arrow.  Carbon atoms stay in the typed C14 framework; each lost
bound chlorine becomes one neutral chlorine radical. -/
def DehalogenationLedger
    (before after : FrameworkState) (lost : ℕ) : Prop :=
  frameworkCarbonCount = StageSpecies.carbonFramework.carbonAtoms ∧
  attachedChlorineCount before * StageSpecies.boundChlorine.chlorineAtoms =
    attachedChlorineCount after * StageSpecies.boundChlorine.chlorineAtoms +
      lost * StageSpecies.chlorineRadical.chlorineAtoms ∧
  before.netFormalCharge = after.netFormalCharge +
    (lost : ℤ) * StageSpecies.chlorineRadical.formalCharge ∧
  before.phase = .surfaceAdsorbed ∧ after.phase = .surfaceAdsorbed

/-- Topological content of the retro-Bergman drawing: an existing fusion bond
survives precisely while its para trigger pair has not both been cleared. -/
def RetroBergmanTopology
    (before after : FrameworkState) : Prop :=
  ∀ fusion,
    after.fusionPresent fusion = true ↔
      before.fusionPresent fusion = true ∧
        ¬ TriggerPairCleared after fusion

/-- Complete source-arrow contract used in this target.  It combines the
printed chlorine-radical coefficient, a closed finite material ledger, and the
fusion-bond consequence of reaction (1). -/
def SurfaceDehalogenationStep
    (before after : FrameworkState) (lost : ℕ) : Prop :=
  before.WellFormed ∧
  after.WellFormed ∧
  NoChlorineAdded before after ∧
  removedChlorineCount before after = lost ∧
  DehalogenationLedger before after lost ∧
  RetroBergmanTopology before after

/-! ## Source-first image readouts

The ten entries equal to one in `precursorState` are exactly the ten chlorine
substituents drawn on decachloroanthracene.  The other state vectors record the
bright substituent sites and the retained/opened fusion topology in panels
A--D, with all entries ordered C1 through C14.
-/

def precursorState : FrameworkState where
  chlorineBondOrder := ![1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1]
  leftFusionPresent := true
  rightFusionPresent := true
  netFormalCharge := 0
  phase := .surfaceAdsorbed

/-- Structure A is supplied by the problem as the worked example. -/
def givenAState : FrameworkState where
  chlorineBondOrder := ![1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1]
  leftFusionPresent := false
  rightFusionPresent := true
  netFormalCharge := 0
  phase := .surfaceAdsorbed

def panelBObservation : FrameworkState where
  chlorineBondOrder := ![0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0]
  leftFusionPresent := false
  rightFusionPresent := true
  netFormalCharge := 0
  phase := .surfaceAdsorbed

def panelCObservation : FrameworkState where
  chlorineBondOrder := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
  leftFusionPresent := false
  rightFusionPresent := false
  netFormalCharge := 0
  phase := .surfaceAdsorbed

def panelDObservation : FrameworkState where
  chlorineBondOrder := ![1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1]
  leftFusionPresent := false
  rightFusionPresent := false
  netFormalCharge := 0
  phase := .surfaceAdsorbed

/-- The unhalogenated monocyclic endpoint shown below panel C. -/
def cyclo14Endpoint : FrameworkState where
  chlorineBondOrder := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  leftFusionPresent := false
  rightFusionPresent := false
  netFormalCharge := 0
  phase := .surfaceAdsorbed

/-! ## Explicit Lewis structures -/

/-- A complete Lewis representative.  Entry `i` of `perimeterBondOrder` is the
order of C(i+1)--C(i+2), with entry 13 denoting C14--C1. -/
structure LewisStructure where
  framework : FrameworkState
  perimeterBondOrder : CarbonSite → ℕ
  leftFusionBondOrder : ℕ
  rightFusionBondOrder : ℕ
  formalCharge : AtomRef → ℤ
  unpairedElectrons : AtomRef → ℕ
  stereochemistry : AtomRef → StereoDescriptor

/-- Cyclic predecessor of a perimeter site. -/
def previousSite (i : CarbonSite) : CarbonSite :=
  ⟨(i.val + 13) % 14, Nat.mod_lt _ (by decide)⟩

/-- Bond-order contribution of the two possible internal fusion bonds. -/
def fusionBondContribution (molecule : LewisStructure) (i : CarbonSite) : ℕ :=
  (if i = c3 ∨ i = c12 then molecule.leftFusionBondOrder else 0) +
  (if i = c5 ∨ i = c10 then molecule.rightFusionBondOrder else 0)

/-- Carbon valence ledger.  A localized unpaired electron fills the fourth
valence slot of a neutral trivalent radical carbon. -/
def carbonValence (molecule : LewisStructure) (i : CarbonSite) : ℕ :=
  molecule.perimeterBondOrder (previousSite i) +
  molecule.perimeterBondOrder i +
  fusionBondContribution molecule i +
  molecule.framework.chlorineBondOrder i +
  molecule.unpairedElectrons (.carbon i)

/-- The possible chlorine atom at `i` belongs to the molecule exactly when its
single C--Cl bond is present. -/
def LewisStructure.AtomPresent
    (molecule : LewisStructure) : AtomRef → Prop
  | .carbon _ => True
  | .chlorine i => molecule.framework.chlorineBondOrder i = 1

/-- Sum of formal charges over all present carbon and chlorine atoms. -/
def totalFormalCharge (molecule : LewisStructure) : ℤ :=
  (∑ i : CarbonSite, molecule.formalCharge (.carbon i)) +
  (Finset.univ.filter
      (fun i => molecule.framework.chlorineBondOrder i = 1)).sum
    (fun i => molecule.formalCharge (.chlorine i))

/-- Sum of localized unpaired electrons over all present atoms. -/
def totalUnpairedElectrons (molecule : LewisStructure) : ℕ :=
  (∑ i : CarbonSite, molecule.unpairedElectrons (.carbon i)) +
  (Finset.univ.filter
      (fun i => molecule.framework.chlorineBondOrder i = 1)).sum
    (fun i => molecule.unpairedElectrons (.chlorine i))

/-- Formula carrier for this target's carbon/chlorine structures. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  chlorine : ℕ
  deriving DecidableEq, Repr

def LewisStructure.formula (molecule : LewisStructure) : MolecularFormula where
  carbon := frameworkCarbonCount
  hydrogen := 0
  chlorine := attachedChlorineCount molecule.framework

/-- Complete local validity conditions for the neutral Lewis structures in
the source scheme. -/
def LewisStructure.Valid (molecule : LewisStructure) : Prop :=
  molecule.framework.WellFormed ∧
  (∀ i, 1 ≤ molecule.perimeterBondOrder i ∧
    molecule.perimeterBondOrder i ≤ 3) ∧
  molecule.leftFusionBondOrder =
    (if molecule.framework.leftFusionPresent then 1 else 0) ∧
  molecule.rightFusionBondOrder =
    (if molecule.framework.rightFusionPresent then 1 else 0) ∧
  totalFormalCharge molecule = molecule.framework.netFormalCharge ∧
  (∀ atom, molecule.AtomPresent atom → molecule.formalCharge atom = 0) ∧
  (∀ i, molecule.unpairedElectrons (.carbon i) ≤ 1) ∧
  (∀ i, molecule.unpairedElectrons (.chlorine i) = 0) ∧
  (∀ atom, molecule.stereochemistry atom = .none) ∧
  ∀ i, carbonValence molecule i = 4

/-- Compatibility with an AFM panel is kept separate from the target Lewis
candidate: it compares the independently recorded substituent and topology
readout, charge class, and phase. -/
def MatchesAFMPanel
    (observation : FrameworkState) (molecule : LewisStructure) : Prop :=
  (∀ i, molecule.framework.chlorineBondOrder i =
    observation.chlorineBondOrder i) ∧
  molecule.framework.leftFusionPresent = observation.leftFusionPresent ∧
  molecule.framework.rightFusionPresent = observation.rightFusionPresent ∧
  molecule.framework.netFormalCharge = observation.netFormalCharge ∧
  molecule.framework.phase = observation.phase

/-- Exactly one carbon bears the chosen localized radical in this resonance
representative; every other present atom has no unpaired electron. -/
def RadicalExactlyAt (molecule : LewisStructure) (site : CarbonSite) : Prop :=
  molecule.unpairedElectrons (.carbon site) = 1 ∧
  ∀ atom, molecule.AtomPresent atom → atom ≠ .carbon site →
    molecule.unpairedElectrons atom = 0

/-- Constructive decision procedure for the two source-defined trigger pairs. -/
local instance instDecidableIsRetroBergmanTriggerSite
    (fusion : FusionBond) (i : CarbonSite) :
    Decidable (IsRetroBergmanTriggerSite fusion i) := by
  cases fusion with
  | left =>
      change Decidable (i = c2 ∨ i = c13)
      infer_instance
  | right =>
      change Decidable (i = c6 ∨ i = c9)
      infer_instance

/-- Constructive decision procedure for membership in a concrete Lewis
structure's finite atom inventory. -/
local instance instDecidableAtomPresent
    (molecule : LewisStructure) (atom : AtomRef) :
    Decidable (molecule.AtomPresent atom) := by
  cases atom with
  | carbon site =>
      change Decidable True
      infer_instance
  | chlorine i =>
      change Decidable (molecule.framework.chlorineBondOrder i = 1)
      infer_instance

def bondPatternB : CarbonSite → ℕ :=
  ![3, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 1]

def bondPatternC : CarbonSite → ℕ :=
  ![3, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 1]

def bondPatternD : CarbonSite → ℕ :=
  ![2, 2, 2, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 1]

def zeroFormalCharge : AtomRef → ℤ := fun _ => 0

def noStereochemistry : AtomRef → StereoDescriptor := fun _ => .none

def radicalAt (site : CarbonSite) : AtomRef → ℕ
  | .carbon i => if i = site then 1 else 0
  | .chlorine _ => 0

/-! ### Candidate drawings B--D -/

/-- B: C14Cl3 radical, with the C5--C10 fusion bond retained. -/
def structureB : LewisStructure where
  framework := {
    chlorineBondOrder := ![0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0]
    leftFusionPresent := false
    rightFusionPresent := true
    netFormalCharge := 0
    phase := .surfaceAdsorbed
  }
  perimeterBondOrder := bondPatternB
  leftFusionBondOrder := 0
  rightFusionBondOrder := 1
  formalCharge := zeroFormalCharge
  unpairedElectrons := radicalAt c8
  stereochemistry := noStereochemistry

/-- C: monocyclic C14Cl radical. -/
def structureC : LewisStructure where
  framework := {
    chlorineBondOrder := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    leftFusionPresent := false
    rightFusionPresent := false
    netFormalCharge := 0
    phase := .surfaceAdsorbed
  }
  perimeterBondOrder := bondPatternC
  leftFusionBondOrder := 0
  rightFusionBondOrder := 0
  formalCharge := zeroFormalCharge
  unpairedElectrons := radicalAt c8
  stereochemistry := noStereochemistry

/-- D: alternative-branch monocyclic C14Cl5 radical. -/
def structureD : LewisStructure where
  framework := {
    chlorineBondOrder := ![1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1]
    leftFusionPresent := false
    rightFusionPresent := false
    netFormalCharge := 0
    phase := .surfaceAdsorbed
  }
  perimeterBondOrder := bondPatternD
  leftFusionBondOrder := 0
  rightFusionBondOrder := 0
  formalCharge := zeroFormalCharge
  unpairedElectrons := radicalAt c11
  stereochemistry := noStereochemistry

def formulaC14Cl3 : MolecularFormula := ⟨14, 0, 3⟩
def formulaC14Cl1 : MolecularFormula := ⟨14, 0, 1⟩
def formulaC14Cl5 : MolecularFormula := ⟨14, 0, 5⟩

/-! ## Assumption/target split and requested-output specifications

There are no answer-shaped hypotheses.  `precursorState`, `givenAState`, the
three panel observations, the endpoint, and the printed arrow coefficients are
source-side data.  Each target below asks an explicit candidate to satisfy the
generic arrow ledger, AFM compatibility, formula, full atom/bond representation,
neutrality, radical placement, absence of stereochemistry, and carbon valence.
-/

/-- The worked example A obeys the initial `-2 Cl•` source arrow. -/
def GivenAPrefixSpec : Prop :=
  SurfaceDehalogenationStep precursorState givenAState 2

/-- Exact structural specification for requested output `structure_b`. -/
def StructureBSpec (molecule : LewisStructure) : Prop :=
  GivenAPrefixSpec ∧
  SurfaceDehalogenationStep givenAState molecule.framework 5 ∧
  MatchesAFMPanel panelBObservation molecule ∧
  molecule.Valid ∧
  molecule.formula = formulaC14Cl3 ∧
  (∀ i, molecule.perimeterBondOrder i = bondPatternB i) ∧
  RadicalExactlyAt molecule c8 ∧
  totalUnpairedElectrons molecule = 1

/-- Exact structural specification for requested output `structure_c`. -/
def StructureCSpec (molecule : LewisStructure) : Prop :=
  StructureBSpec structureB ∧
  SurfaceDehalogenationStep structureB.framework molecule.framework 2 ∧
  SurfaceDehalogenationStep molecule.framework cyclo14Endpoint 1 ∧
  MatchesAFMPanel panelCObservation molecule ∧
  molecule.Valid ∧
  molecule.formula = formulaC14Cl1 ∧
  (∀ i, molecule.perimeterBondOrder i = bondPatternC i) ∧
  RadicalExactlyAt molecule c8 ∧
  totalUnpairedElectrons molecule = 1

/-- Exact structural specification for requested output `structure_d`. -/
def StructureDSpec (molecule : LewisStructure) : Prop :=
  GivenAPrefixSpec ∧
  SurfaceDehalogenationStep givenAState molecule.framework 3 ∧
  MatchesAFMPanel panelDObservation molecule ∧
  molecule.Valid ∧
  molecule.formula = formulaC14Cl5 ∧
  (∀ i, molecule.perimeterBondOrder i = bondPatternD i) ∧
  RadicalExactlyAt molecule c11 ∧
  totalUnpairedElectrons molecule = 1

/-- Requested output carrier for box B. -/
theorem structure_b : StructureBSpec structureB := by
  unfold StructureBSpec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold GivenAPrefixSpec SurfaceDehalogenationStep
      FrameworkState.WellFormed NoChlorineAdded DehalogenationLedger
      RetroBergmanTopology TriggerPairCleared
    decide
  · unfold SurfaceDehalogenationStep FrameworkState.WellFormed
      NoChlorineAdded DehalogenationLedger RetroBergmanTopology
      TriggerPairCleared
    decide
  · unfold MatchesAFMPanel
    decide
  · unfold LewisStructure.Valid FrameworkState.WellFormed
    decide
  · decide
  · decide
  · unfold RadicalExactlyAt
    decide
  · decide

/-- Requested output carrier for box C. -/
theorem structure_c : StructureCSpec structureC := by
  unfold StructureCSpec
  refine ⟨structure_b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold SurfaceDehalogenationStep FrameworkState.WellFormed
      NoChlorineAdded DehalogenationLedger RetroBergmanTopology
      TriggerPairCleared
    decide
  · unfold SurfaceDehalogenationStep FrameworkState.WellFormed
      NoChlorineAdded DehalogenationLedger RetroBergmanTopology
      TriggerPairCleared
    decide
  · unfold MatchesAFMPanel
    decide
  · unfold LewisStructure.Valid FrameworkState.WellFormed
    decide
  · decide
  · decide
  · unfold RadicalExactlyAt
    decide
  · decide

/-- Requested output carrier for box D. -/
theorem structure_d : StructureDSpec structureD := by
  unfold StructureDSpec
  refine ⟨structure_b.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold SurfaceDehalogenationStep FrameworkState.WellFormed
      NoChlorineAdded DehalogenationLedger RetroBergmanTopology
      TriggerPairCleared
    decide
  · unfold MatchesAFMPanel
    decide
  · unfold LewisStructure.Valid FrameworkState.WellFormed
    decide
  · decide
  · decide
  · unfold RadicalExactlyAt
    decide
  · decide

/-- Combined source-derived symbolic result in requested order B, C, D. -/
def RawResult : Prop :=
  StructureBSpec structureB ∧
  StructureCSpec structureC ∧
  StructureDSpec structureD

/-- All three outputs use exact-symbolic reporting, so reporting preserves the
full structural specifications. -/
def ReportedResult : Prop :=
  StructureBSpec structureB ∧
  StructureCSpec structureC ∧
  StructureDSpec structureD

/-- Raw solve-phase result contract. -/
theorem raw_result : RawResult := by
  exact ⟨structure_b, structure_c, structure_d⟩

/-- Exact-symbolic reported result contract. -/
theorem reported_result : ReportedResult := by
  exact ⟨structure_b, structure_c, structure_d⟩

end IChO2026Problems.T6A2
