import Mathlib

/-!
# IChO 2026, theory problem 6, part 7

This file formalizes the problem-side electron count for the P6 porphyrin
nanoring and the subsequent Hückel minimization.  In particular, the reported
integers are not hypotheses: `minimumElectronsRemoved` is defined by a least
witness construction.

The source image `T6_page-4.png` depicts six zinc-porphyrin nodes joined in a
cycle by six butadiyne links.  A continuous path through one porphyrin contains
five drawn double bonds, while one aligned pi component from each of the two
triple bonds in a butadiyne link belongs to the global path.  The aryl
substituents, zinc centres, and template are not on that path.
-/

namespace IChO2026Problems
namespace T6A7

/-- Permitted origins for the finite counts used in this target. -/
inductive CountProvenance
  | problemText
  | problemImage
  | problemStatedFallback
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- The source-first topology and pi-path inventory of P6.

`ringClosureLinkCount` counts the one link crossing the boundary when the
six-node cycle is displayed as a linear list of repeat units.  It is already
included in `butadiyneLinkCount`, so it must not be counted a second time. -/
structure P6PathInventory where
  porphyrinNodeCount : ℕ
  butadiyneLinkCount : ℕ
  precursorTerminalEthynylEndCount : ℕ
  ringClosureLinkCount : ℕ
  porphyrinPathDoubleBondCountPerNode : ℕ
  tripleBondCountPerLink : ℕ
  continuousPiBondCountPerTripleBond : ℕ
  electronCountPerPiBond : ℕ
  topologyProvenance : CountProvenance
  pathProvenance : CountProvenance
  electronPairProvenance : CountProvenance

/-- Literal recount of the P6 repeat drawing and complete cyclic assembly in
`T6_page-4.png`.  Six bis-terminal-ethynyl porphyrins provide twelve ends;
pairing those ends gives the six butadiyne links of the closed cycle. -/
def p6PathInventory : P6PathInventory where
  porphyrinNodeCount := 6
  butadiyneLinkCount := 6
  precursorTerminalEthynylEndCount := 12
  ringClosureLinkCount := 1
  porphyrinPathDoubleBondCountPerNode := 5
  tripleBondCountPerLink := 2
  continuousPiBondCountPerTripleBond := 1
  electronCountPerPiBond := 2
  topologyProvenance := .problemImage
  pathProvenance := .problemImage
  electronPairProvenance := .trustedGeneralLaw

/-- Nontrivial topology audit: the six nodes form one degree-two cycle, so the
number of links equals the number of nodes, and the twelve precursor termini
are paired exactly once. -/
def P6TopologyAudit (inventory : P6PathInventory) : Prop :=
  0 < inventory.porphyrinNodeCount ∧
    inventory.porphyrinNodeCount = 6 ∧
    inventory.butadiyneLinkCount = inventory.porphyrinNodeCount ∧
    inventory.precursorTerminalEthynylEndCount =
      2 * inventory.porphyrinNodeCount ∧
    inventory.precursorTerminalEthynylEndCount =
      2 * inventory.butadiyneLinkCount ∧
    inventory.ringClosureLinkCount = 1 ∧
    inventory.topologyProvenance = .problemImage

/-- Audit of only the bonds belonging to the continuous global pi pathway. -/
def P6ContinuousPathAudit (inventory : P6PathInventory) : Prop :=
  inventory.porphyrinPathDoubleBondCountPerNode = 5 ∧
    inventory.tripleBondCountPerLink = 2 ∧
    inventory.continuousPiBondCountPerTripleBond = 1 ∧
    inventory.electronCountPerPiBond = 2 ∧
    inventory.pathProvenance = .problemImage ∧
    inventory.electronPairProvenance = .trustedGeneralLaw

/-- Species roles in the source arrow used from previous part T6-A6. -/
inductive P6AssemblySpecies
  | rBisTerminalEthynylZincPorphyrin
  | p6CyclicHexamer
  deriving DecidableEq, Repr

/-- The part-A6 synthesis arrow is used only as a qualitative structural
compatibility constraint.  This carrier makes no assertion about yield,
completion, sole-product status, phases, or unshown material streams. -/
structure QualitativeP6AssemblyArrow where
  reactant : P6AssemblySpecies
  product : P6AssemblySpecies
  reactantMultiplicity : ℕ
  terminalEthynylEndsPerReactant : ℕ
  butadiyneLinksInProduct : ℕ
  provenance : CountProvenance

/-- Relevant part-A6 conclusion rederived from the reaction scheme on page 4:
R is a bis-terminal-ethynyl zinc porphyrin and six copies are coupled into P6. -/
def previousPartA6AssemblyArrow : QualitativeP6AssemblyArrow where
  reactant := .rBisTerminalEthynylZincPorphyrin
  product := .p6CyclicHexamer
  reactantMultiplicity := 6
  terminalEthynylEndsPerReactant := 2
  butadiyneLinksInProduct := 6
  provenance := .problemImage

/-- The qualitative arrow has the endpoint-pair balance needed for the P6
connectivity recount. -/
def QualitativeAssemblyCompatible (arrow : QualitativeP6AssemblyArrow) : Prop :=
  arrow.reactant = .rBisTerminalEthynylZincPorphyrin ∧
    arrow.product = .p6CyclicHexamer ∧
    arrow.reactantMultiplicity = 6 ∧
    arrow.reactantMultiplicity * arrow.terminalEthynylEndsPerReactant =
      2 * arrow.butadiyneLinksInProduct ∧
    arrow.provenance = .problemImage

/-- Pi electrons contributed by the selected five-double-bond route through
one porphyrin node. -/
def porphyrinPathPiElectrons (inventory : P6PathInventory) : ℕ :=
  inventory.electronCountPerPiBond *
    inventory.porphyrinPathDoubleBondCountPerNode

/-- Pi electrons contributed by the continuous component of one butadiyne
link.  A triple bond has two orthogonal pi components, but only one component
per triple bond lies on the continuous global pathway specified in the text. -/
def butadiynePathPiElectrons (inventory : P6PathInventory) : ℕ :=
  inventory.electronCountPerPiBond *
    (inventory.tripleBondCountPerLink *
      inventory.continuousPiBondCountPerTripleBond)

/-- Exact, unoxidized global-path count obtained before applying Hückel's rule. -/
def neutralP6PiElectronCount : ℕ :=
  p6PathInventory.porphyrinNodeCount *
      porphyrinPathPiElectrons p6PathInventory +
    p6PathInventory.butadiyneLinkCount *
      butadiynePathPiElectrons p6PathInventory

/-- Hückel's `4k + 2` condition for a globally aromatic pi circuit. -/
def HuckelAromaticCount (piElectrons : ℕ) : Prop :=
  ∃ k : ℕ, piElectrons = 4 * k + 2

/-- The corresponding `4k` count, retained because the source states that
oxidized P6 can also exhibit global anti-aromaticity. -/
def HuckelAntiaromaticCount (piElectrons : ℕ) : Prop :=
  ∃ k : ℕ, piElectrons = 4 * k

/-- An oxidation removes a positive number of electrons no larger than the
initial path population. -/
def AdmissibleOxidation (initial removed : ℕ) : Prop :=
  0 < removed ∧ removed ≤ initial

/-- Removing `removed` electrons from `initial` leaves a Hückel-aromatic
global circuit. -/
def AromaticAfterRemoval (initial removed : ℕ) : Prop :=
  AdmissibleOxidation initial removed ∧
    HuckelAromaticCount (initial - removed)

/-- Specification of the word "minimum" in the question. -/
def IsMinimumAromaticRemoval (initial removed : ℕ) : Prop :=
  AromaticAfterRemoval initial removed ∧
    ∀ other : ℕ, AromaticAfterRemoval initial other → removed ≤ other

/-- The source-derived neutral count admits at least one positive aromatic
oxidation state.  This existence result supplies the search domain; it does not
select the reported number. -/
theorem p6_has_aromatic_oxidation :
    ∃ removed : ℕ, AromaticAfterRemoval neutralP6PiElectronCount removed := by
  refine ⟨2, ?_⟩
  constructor
  · constructor
    · norm_num
    · norm_num [neutralP6PiElectronCount, porphyrinPathPiElectrons,
        butadiynePathPiElectrons, p6PathInventory]
  · refine ⟨20, ?_⟩
    norm_num [neutralP6PiElectronCount, porphyrinPathPiElectrons,
      butadiynePathPiElectrons, p6PathInventory]

/-- Candidate output constructed as the least source-admissible Hückel witness,
not as a preselected numeral. -/
noncomputable def minimumElectronsRemoved : ℕ := by
  classical
  exact Nat.find p6_has_aromatic_oxidation

/-- The second requested output is the exact population remaining after the
least aromatic oxidation. -/
noncomputable def globalPiElectronCount : ℕ :=
  neutralP6PiElectronCount - minimumElectronsRemoved

theorem p6_source_recount :
    P6TopologyAudit p6PathInventory ∧
      P6ContinuousPathAudit p6PathInventory ∧
      QualitativeAssemblyCompatible previousPartA6AssemblyArrow ∧
      neutralP6PiElectronCount =
        6 * ((2 * 5) + (2 * (2 * 1))) := by
  norm_num [P6TopologyAudit, P6ContinuousPathAudit,
    QualitativeAssemblyCompatible, neutralP6PiElectronCount,
    porphyrinPathPiElectrons, butadiynePathPiElectrons, p6PathInventory,
    previousPartA6AssemblyArrow]

theorem minimumElectronsRemoved_spec :
    IsMinimumAromaticRemoval neutralP6PiElectronCount
      minimumElectronsRemoved := by
  classical
  constructor
  · exact Nat.find_spec p6_has_aromatic_oxidation
  · intro other hother
    exact Nat.find_min' p6_has_aromatic_oxidation hother

theorem p6_oxidation_supports_both_huckel_classes :
    (∃ removed : ℕ,
        AromaticAfterRemoval neutralP6PiElectronCount removed) ∧
      (∃ removed : ℕ,
        AdmissibleOxidation neutralP6PiElectronCount removed ∧
          HuckelAntiaromaticCount
            (neutralP6PiElectronCount - removed)) := by
  refine ⟨p6_has_aromatic_oxidation, 4, ?_⟩
  constructor
  · constructor
    · norm_num
    · norm_num [neutralP6PiElectronCount, porphyrinPathPiElectrons,
        butadiynePathPiElectrons, p6PathInventory]
  · refine ⟨20, ?_⟩
    norm_num [neutralP6PiElectronCount, porphyrinPathPiElectrons,
      butadiynePathPiElectrons, p6PathInventory]

/-- Raw answer-blind result: source recount, least-witness semantics, and the
unrounded subtraction relating the two requested outputs. -/
def T6A7RawResult : Prop :=
  P6TopologyAudit p6PathInventory ∧
    P6ContinuousPathAudit p6PathInventory ∧
    QualitativeAssemblyCompatible previousPartA6AssemblyArrow ∧
    neutralP6PiElectronCount =
      p6PathInventory.porphyrinNodeCount *
          porphyrinPathPiElectrons p6PathInventory +
        p6PathInventory.butadiyneLinkCount *
          butadiynePathPiElectrons p6PathInventory ∧
    IsMinimumAromaticRemoval neutralP6PiElectronCount
      minimumElectronsRemoved ∧
    globalPiElectronCount =
      neutralP6PiElectronCount - minimumElectronsRemoved

/-- Exact-integer reporting contract for both requested outputs. -/
def T6A7ReportedResult : Prop :=
  minimumElectronsRemoved = 2 ∧ globalPiElectronCount = 82

theorem t6_a7_raw_result : T6A7RawResult := by
  rcases p6_source_recount with ⟨htopology, hpath, hassembly, _⟩
  exact ⟨htopology, hpath, hassembly, rfl,
    minimumElectronsRemoved_spec, rfl⟩

/-- Requested output `minimum_electrons_removed`. -/
theorem minimum_electrons_removed : minimumElectronsRemoved = 2 := by
  have htwo : AromaticAfterRemoval neutralP6PiElectronCount 2 := by
    constructor
    · constructor
      · norm_num
      · norm_num [neutralP6PiElectronCount, porphyrinPathPiElectrons,
          butadiynePathPiElectrons, p6PathInventory]
    · refine ⟨20, ?_⟩
      norm_num [neutralP6PiElectronCount, porphyrinPathPiElectrons,
        butadiynePathPiElectrons, p6PathInventory]
  have hminimum := minimumElectronsRemoved_spec
  have hle : minimumElectronsRemoved ≤ 2 := hminimum.2 2 htwo
  rcases hminimum.1 with ⟨⟨hpositive, hinitial⟩, k, hk⟩
  norm_num [neutralP6PiElectronCount, porphyrinPathPiElectrons,
    butadiynePathPiElectrons, p6PathInventory] at hinitial hk
  omega

/-- Requested output `global_pi_electron_count`. -/
theorem global_pi_electron_count : globalPiElectronCount = 82 := by
  simp [globalPiElectronCount, minimum_electrons_removed,
    neutralP6PiElectronCount, porphyrinPathPiElectrons,
    butadiynePathPiElectrons, p6PathInventory]

theorem t6_a7_reported_result : T6A7ReportedResult := by
  exact ⟨minimum_electrons_removed, global_pi_electron_count⟩

end T6A7
end IChO2026Problems
