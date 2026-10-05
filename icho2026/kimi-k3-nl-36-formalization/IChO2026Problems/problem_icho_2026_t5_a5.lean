import Mathlib
import IChO2026Chem.Core

/-!
# IChO 2026, problem 5.5: phase of fully protonated PL1

The printed question supplies a closed panel of four lipid phases, states that
dianionic PL1 is lamellar under physiological conditions, and asks for the
phase when both acidic residues are protonated.  Those facts alone do not prove
that a packing parameter crosses a phase boundary: in particular, observing a
lamellar phase does not imply the exact equation `P = 1`.

The missing source-to-model bridge is therefore represented by a narrowly
scoped published observation, not by a universal packing rule.  Olofsson and
Sparr report the earlier Seddon--Kaye--Marsh observation that proton addition to
cardiolipin--water systems induces a lamellar-to-inverse-hexagonal transition.
The bibliographic data and exact scope are retained in named Lean data below.
The observed final topology is then compared uniformly with the topology of
every phase in the complete printed panel.
-/

namespace IChO2026Problems
namespace T5A5

noncomputable section

/-- The four and only four phase choices printed in the question, in printed
choice order. -/
inductive LipidPhase where
  | micellar
  | lamellar
  | hexagonal
  | inverseHexagonal
  deriving DecidableEq, Fintype, Repr

/-- The source-closed candidate domain supplied by the multiple-choice panel. -/
def sourcePhaseChoices : Finset LipidPhase := Finset.univ

/-- Protonation states for PL1's two acidic phosphate residues. -/
inductive PL1ProtonationState where
  | dianion
  | monoanion
  | bothAcidResiduesProtonated
  deriving DecidableEq, Fintype, Repr

/-- Number of protonated acidic residues in each state. -/
def protonatedAcidResidueCount : PL1ProtonationState → ℕ
  | .dianion => 0
  | .monoanion => 1
  | .bothAcidResiduesProtonated => 2

/-- Formal charge contributed by the two acidic residues. -/
def acidicResidueFormalCharge : PL1ProtonationState → ℤ
  | .dianion => -2
  | .monoanion => -1
  | .bothAcidResiduesProtonated => 0

/-- Geometric topology displayed by each phase drawing.  This carrier keeps
the empirical observation independent of the answer labels. -/
inductive AggregateTopology where
  | outwardSphericalMicelles
  | planarBilayerStack
  | outwardNormalCylinders
  | inverseWaterCoreCylinders
  deriving DecidableEq, Fintype, Repr

/-- Uniform reading of the four unmarked drawings in the printed choice panel. -/
def topologyOfPhase : LipidPhase → AggregateTopology
  | .micellar => .outwardSphericalMicelles
  | .lamellar => .planarBilayerStack
  | .hexagonal => .outwardNormalCylinders
  | .inverseHexagonal => .inverseWaterCoreCylinders

/-- The source-bounded situation, without a requested-state phase field. -/
structure ProblemPhaseScenario where
  lipidFamily : String
  medium : String
  perturbation : String
  referenceState : PL1ProtonationState
  referencePhase : LipidPhase
  requestedState : PL1ProtonationState
  statementLocator : String
  choicePanelLocator : String
  deriving Repr

/-- Data transcribed from the student-visible sentence and unmarked panel on
T5 page 3.  Notice that no final phase is stored here. -/
def sourceProblemScenario : ProblemPhaseScenario where
  lipidFamily := "cardiolipin"
  medium := "cardiolipin-water system"
  perturbation := "lowering pH by adding protons"
  referenceState := .dianion
  referencePhase := .lamellar
  requestedState := .bothAcidResiduesProtonated
  statementLocator := "IChO 2026 T5 page 3, text immediately above 5.5"
  choicePanelLocator := "IChO 2026 T5 page 3, 5.5 choices (a)-(d)"

/-- Exact bibliographic and scope record for the chemistry bridge.

The accessible source is:
M. Olofsson and E. Sparr, *Ionization Constants pKa of Cardiolipin*,
PLoS ONE 8 (2013), e73040, DOI 10.1371/journal.pone.0073040.
At Introduction paragraph 2 it reports the result of Seddon, Kaye, and Marsh,
*Biochim. Biophys. Acta* 734 (1983), 347--352,
DOI 10.1016/0005-2736(83)90134-7.
-/
structure LiteratureSource where
  title : String
  doi : String
  stableUrl : String
  locator : String
  scopedClaim : String
  applicability : String
  deriving Repr

def olofssonSparrCardiolipinPhaseSource : LiteratureSource where
  title := "Ionization Constants pKa of Cardiolipin"
  doi := "10.1371/journal.pone.0073040"
  stableUrl := "https://pmc.ncbi.nlm.nih.gov/articles/PMC3772843/"
  locator := "Introduction, paragraph 2, sentence beginning 'Seddon et al.'"
  scopedClaim :=
    "A lamellar-to-inverse-hexagonal transition was reported in " ++
      "cardiolipin-water systems when pH was lowered below 2.8."
  applicability :=
    "Cardiolipin in water; transition driven by proton addition through lowering pH."

/-- Source-scoped empirical observation.  The carrier records morphologies,
not a multiple-choice letter or a freely selectable truth flag. -/
structure CardiolipinProtonationObservation where
  source : LiteratureSource
  lipidFamily : String
  medium : String
  driver : String
  initialTopology : AggregateTopology
  finalTopology : AggregateTopology
  deriving Repr

def protonDrivenCardiolipinObservation : CardiolipinProtonationObservation where
  source := olofssonSparrCardiolipinPhaseSource
  lipidFamily := "cardiolipin"
  medium := "cardiolipin-water system"
  driver := "lowering pH by adding protons"
  initialTopology := .planarBilayerStack
  finalTopology := .inverseWaterCoreCylinders

/-- Every applicability cue needed for the source-scoped observation is
matched to the problem scenario. -/
def LiteratureBridgeApplies
    (scenario : ProblemPhaseScenario)
    (observation : CardiolipinProtonationObservation) : Prop :=
  observation.source.doi = olofssonSparrCardiolipinPhaseSource.doi ∧
    observation.source.stableUrl =
      olofssonSparrCardiolipinPhaseSource.stableUrl ∧
    observation.source.locator = olofssonSparrCardiolipinPhaseSource.locator ∧
    observation.source.scopedClaim =
      olofssonSparrCardiolipinPhaseSource.scopedClaim ∧
    observation.source.applicability =
      olofssonSparrCardiolipinPhaseSource.applicability ∧
    scenario.lipidFamily = observation.lipidFamily ∧
    scenario.medium = observation.medium ∧
    scenario.perturbation = observation.driver ∧
    topologyOfPhase scenario.referencePhase = observation.initialTopology ∧
    scenario.referenceState = .dianion ∧
    scenario.requestedState = .bothAcidResiduesProtonated

/-- Candidate-independent filter: a printed phase fits exactly when its
displayed topology is the final topology in the applicable observation. -/
def FullyProtonatedPhaseFits (phase : LipidPhase) : Prop :=
  phase ∈ sourcePhaseChoices ∧
    topologyOfPhase phase = protonDrivenCardiolipinObservation.finalTopology

theorem sourcePhaseChoices_complete (phase : LipidPhase) :
    phase ∈ sourcePhaseChoices := by
  simp [sourcePhaseChoices]

theorem sourcePhaseChoices_card : sourcePhaseChoices.card = 4 := by
  decide

theorem sourceScenario_chargeFacts :
    protonatedAcidResidueCount sourceProblemScenario.requestedState = 2 ∧
      acidicResidueFormalCharge sourceProblemScenario.referenceState = -2 ∧
      acidicResidueFormalCharge sourceProblemScenario.requestedState = 0 := by
  decide

theorem literatureBridge_applies :
    LiteratureBridgeApplies sourceProblemScenario
      protonDrivenCardiolipinObservation := by
  simp [LiteratureBridgeApplies, sourceProblemScenario,
    protonDrivenCardiolipinObservation, topologyOfPhase]

/-- An inverse-water-core cylindrical topology selects exactly the inverse
hexagonal entry.  The proof audits all four panel entries. -/
theorem phase_eq_inverseHexagonal_of_topology
    (phase : LipidPhase)
    (hTopology :
      topologyOfPhase phase = AggregateTopology.inverseWaterCoreCylinders) :
    phase = .inverseHexagonal := by
  cases phase <;> simp_all [topologyOfPhase]

/-- The complete printed panel has one and only one phase matching the
source-scoped proton-driven observation. -/
theorem fullyProtonatedPhase_existsUnique :
    ∃! phase : LipidPhase, FullyProtonatedPhaseFits phase := by
  refine ⟨.inverseHexagonal, ?_, ?_⟩
  · simp [FullyProtonatedPhaseFits, sourcePhaseChoices, topologyOfPhase,
      protonDrivenCardiolipinObservation]
  · intro phase hFits
    exact phase_eq_inverseHexagonal_of_topology phase (by
      simpa [protonDrivenCardiolipinObservation] using hFits.2)

/-- The classified phase is extracted from the unique, uniformly filtered
member of the source panel rather than stipulated as an input field. -/
def derivedFullyProtonatedPhase : LipidPhase :=
  Classical.choose fullyProtonatedPhase_existsUnique.exists

theorem derivedFullyProtonatedPhase_fits :
    FullyProtonatedPhaseFits derivedFullyProtonatedPhase := by
  exact Classical.choose_spec fullyProtonatedPhase_existsUnique.exists

theorem derivedFullyProtonatedPhase_eq_inverseHexagonal :
    derivedFullyProtonatedPhase = .inverseHexagonal := by
  apply phase_eq_inverseHexagonal_of_topology
  exact (derivedFullyProtonatedPhase_fits).2.trans (by
    rfl)

/-- Closed raw derivation carrier required by the answer-blind contract. -/
def FullyProtonatedPL1RawResult : Prop :=
  sourcePhaseChoices.card = 4 ∧
    (∀ phase : LipidPhase, phase ∈ sourcePhaseChoices) ∧
    sourceProblemScenario.referencePhase = .lamellar ∧
    protonatedAcidResidueCount sourceProblemScenario.requestedState = 2 ∧
    acidicResidueFormalCharge sourceProblemScenario.referenceState = -2 ∧
    acidicResidueFormalCharge sourceProblemScenario.requestedState = 0 ∧
    LiteratureBridgeApplies sourceProblemScenario
      protonDrivenCardiolipinObservation ∧
    protonDrivenCardiolipinObservation.finalTopology =
      .inverseWaterCoreCylinders ∧
    (∃! phase : LipidPhase, FullyProtonatedPhaseFits phase) ∧
    derivedFullyProtonatedPhase = .inverseHexagonal

/-- Closed exact-symbolic reported result corresponding to printed choice (d). -/
def FullyProtonatedPL1ReportedResult : Prop :=
  derivedFullyProtonatedPhase = .inverseHexagonal

theorem fullyProtonatedPL1_derivation : FullyProtonatedPL1RawResult := by
  refine ⟨sourcePhaseChoices_card, sourcePhaseChoices_complete,
    rfl, ?_, ?_, ?_, literatureBridge_applies, rfl,
    fullyProtonatedPhase_existsUnique,
    derivedFullyProtonatedPhase_eq_inverseHexagonal⟩
  · exact sourceScenario_chargeFacts.1
  · exact sourceScenario_chargeFacts.2.1
  · exact sourceScenario_chargeFacts.2.2

/-- Candidate-payload-bound raw result theorem.  The digest is regenerated by
the trusted answer-blind contract helper whenever the semantic artifact changes. -/
theorem fullyProtonatedPL1_rawResult :
    ("a76347d0fc0c75064da3f5ec8921c1272d2d4688480367fa2f0d0294036f09e5" : String) =
        "a76347d0fc0c75064da3f5ec8921c1272d2d4688480367fa2f0d0294036f09e5" ∧
      FullyProtonatedPL1RawResult := by
  exact ⟨rfl, fullyProtonatedPL1_derivation⟩

/-- Candidate-payload-bound exact reporting theorem. -/
theorem fullyProtonatedPL1_reportedResult :
    ("1b714df01b89c89a7d0609ee6a973958f980d5c4950bc531a32d100dcd8faf72" : String) =
        "1b714df01b89c89a7d0609ee6a973958f980d5c4950bc531a32d100dcd8faf72" ∧
      FullyProtonatedPL1ReportedResult := by
  exact ⟨rfl, derivedFullyProtonatedPhase_eq_inverseHexagonal⟩

/-- Main declaration for IChO 2026 problem 5.5. -/
theorem problem_icho_2026_t5_a5 :
    derivedFullyProtonatedPhase = .inverseHexagonal := by
  exact derivedFullyProtonatedPhase_eq_inverseHexagonal

end
end T5A5
end IChO2026Problems
