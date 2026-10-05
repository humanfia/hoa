import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem T2, part A2

This file formalizes the steady-state calculation for bromous acid in the two
alternating kinetic regimes of the Belousov--Zhabotinsky mechanism printed in
the problem.  Numerical concentration coordinates are in `mol dm^-3` (M), and
reaction rates are in `M s^-1`.

The mechanism is recorded before the calculation.  The seventh printed step
has "other products", so its product side is deliberately represented as only
partially disclosed rather than inventing a catch-all chemical species or a
stoichiometric coefficient for it.
-/

namespace IChO2026Problems.IChO2026T2A2

open IChO2026Chem

noncomputable section

/-- Chemical species explicitly named in the printed BZ mechanism. -/
inductive Species
  | hbro2
  | bromate
  | proton
  | bro2Radical
  | water
  | ceriumIII
  | ceriumIV
  | hbro
  | bromide
  | malonicAcid
  | bromomalonicAcid
  deriving DecidableEq, Fintype, Repr

/-- The three process labels used by the source mechanism. -/
inductive Process
  | A
  | B
  | C
  deriving DecidableEq, Fintype, Repr

/-- The two regimes that alternate, while Process C continues. -/
inductive DominantRegime
  | processA
  | processB
  deriving DecidableEq, Fintype, Repr

/-- Source-stated visible colors of the two alternating regimes. -/
inductive SolutionColour
  | yellow
  | colourless
  deriving DecidableEq, Fintype, Repr

/-- Process A is yellow and Process B is colourless. -/
def regimeColour : DominantRegime → SolutionColour
  | .processA => .yellow
  | .processB => .colourless

/-- The process that is practically suppressed in each dominant regime. -/
def practicallySuppressedProcess : DominantRegime → Process
  | .processA => .B
  | .processB => .A

/-- Process C is the source-stated continuously occurring process. -/
def continuouslyOccurringProcess : Process := .C

/-- Labels of the seven elementary steps in the displayed mechanism. -/
inductive ReactionStep
  | r1
  | r2
  | r3
  | r4
  | r5
  | r6
  | r7
  deriving DecidableEq, Fintype, Repr

/-- Whether the printed product complex is complete.  Step 7 is partial because
the source itself appends "other products" without identities or coefficients. -/
inductive ProductDisclosure
  | complete
  | additionalUnspecifiedProducts
  deriving DecidableEq, Repr

/-- A source-faithful reaction scheme, allowing the product side to be only
partially disclosed.  Complexes use CRNT's verified stoichiometric-vector API. -/
structure SchematicReaction where
  process : Process
  reactants : CRNT.Complex Species
  knownProducts : CRNT.Complex Species
  disclosure : ProductDisclosure

/-- The complete printed stoichiometry of steps 1--6 and the disclosed portion
of step 7. -/
def reactionScheme : ReactionStep → SchematicReaction
  | .r1 =>
      { process := .A
        reactants := fun s => match s with
          | .hbro2 => 1
          | .bromate => 1
          | .proton => 1
          | _ => 0
        knownProducts := fun s => match s with
          | .bro2Radical => 2
          | .water => 1
          | _ => 0
        disclosure := .complete }
  | .r2 =>
      { process := .A
        reactants := fun s => match s with
          | .bro2Radical => 1
          | .ceriumIII => 1
          | .proton => 1
          | _ => 0
        knownProducts := fun s => match s with
          | .hbro2 => 1
          | .ceriumIV => 1
          | _ => 0
        disclosure := .complete }
  | .r3 =>
      { process := .A
        reactants := fun s => match s with
          | .hbro2 => 2
          | _ => 0
        knownProducts := fun s => match s with
          | .bromate => 1
          | .hbro => 1
          | .proton => 1
          | _ => 0
        disclosure := .complete }
  | .r4 =>
      { process := .B
        reactants := fun s => match s with
          | .hbro2 => 1
          | .bromide => 1
          | .proton => 1
          | _ => 0
        knownProducts := fun s => match s with
          | .hbro => 2
          | _ => 0
        disclosure := .complete }
  | .r5 =>
      { process := .B
        reactants := fun s => match s with
          | .bromate => 1
          | .bromide => 1
          | .proton => 2
          | _ => 0
        knownProducts := fun s => match s with
          | .hbro => 1
          | .hbro2 => 1
          | _ => 0
        disclosure := .complete }
  | .r6 =>
      { process := .B
        reactants := fun s => match s with
          | .hbro => 1
          | .malonicAcid => 1
          | _ => 0
        knownProducts := fun s => match s with
          | .bromomalonicAcid => 1
          | .water => 1
          | _ => 0
        disclosure := .complete }
  | .r7 =>
      { process := .C
        reactants := fun s => match s with
          | .ceriumIV => 1
          | .bromomalonicAcid => 1
          | _ => 0
        knownProducts := fun s => match s with
          | .ceriumIII => 1
          | .bromide => 1
          | _ => 0
        disclosure := .additionalUnspecifiedProducts }

/-- Units used for the printed numerical rate constants. -/
inductive RateConstantUnit
  | molarPowNegOnePerSecond
  | molarPowNegTwoPerSecond
  | molarPowNegThreePerSecond
  deriving DecidableEq, Repr

/-- A numerical rate constant together with its source-printed unit. -/
structure RateConstantData where
  value : ℝ
  unit : RateConstantUnit

/-- `k₁ = 1.0 * 10^4 M^-2 s^-1`. -/
def k1 : ℝ := 1.0 * 10 ^ 4

/-- `k₂ = 6.2 * 10^4 M^-2 s^-1`. -/
def k2 : ℝ := 6.2 * 10 ^ 4

/-- `k₃ = 4.0 * 10^7 M^-1 s^-1`. -/
def k3 : ℝ := 4.0 * 10 ^ 7

/-- `k₄ = 2.0 * 10^9 M^-2 s^-1`. -/
def k4 : ℝ := 2.0 * 10 ^ 9

/-- `k₅ = 2.1 M^-3 s^-1`. -/
def k5 : ℝ := 2.1

/-- `k₆ = 8.2 M^-1 s^-1`. -/
def k6 : ℝ := 8.2

/-- `k₇ = 1.0 * 10^2 M^-1 s^-1`. -/
def k7 : ℝ := 1.0 * 10 ^ 2

/-- All seven source-stated rate constants and their units. -/
def rateConstant : ReactionStep → RateConstantData
  | .r1 => ⟨k1, .molarPowNegTwoPerSecond⟩
  | .r2 => ⟨k2, .molarPowNegTwoPerSecond⟩
  | .r3 => ⟨k3, .molarPowNegOnePerSecond⟩
  | .r4 => ⟨k4, .molarPowNegTwoPerSecond⟩
  | .r5 => ⟨k5, .molarPowNegThreePerSecond⟩
  | .r6 => ⟨k6, .molarPowNegOnePerSecond⟩
  | .r7 => ⟨k7, .molarPowNegOnePerSecond⟩

/-- Source-stated initial bromate concentration, in `mol dm^-3`. -/
def bromateInitial : ℝ := 0.06

/-- Source-stated initial malonic-acid concentration, in `mol dm^-3`. -/
def malonicAcidInitial : ℝ := 0.1

/-- Source-stated initial proton concentration, in `mol dm^-3`. -/
def protonInitial : ℝ := 0.8

/-- Source-stated initial Ce(IV) concentration, in `mol dm^-3`. -/
def ceriumIVInitial : ℝ := 0.001

/-- The four explicitly supplied initial concentrations. -/
def suppliedInitialConcentration : Species → Option ℝ
  | .bromate => some bromateInitial
  | .malonicAcid => some malonicAcidInitial
  | .proton => some protonInitial
  | .ceriumIV => some ceriumIVInitial
  | _ => none

/-- A concentration vector; every coordinate is numerically expressed in
`mol dm^-3`.  This is the same representation (`Species → ℝ`) used by CRNT's
kinetics layer, whose optional module is not needed for the present local rate
balances. -/
abbrev Concentration := Species → ℝ

/-- Every chemical concentration coordinate is nonnegative. -/
def NonnegativeConcentration (x : Concentration) : Prop :=
  ∀ s : Species, 0 ≤ x s

/-- The source's constant-reactant/pH idealization.  Ce(IV) is deliberately not
fixed, while bromate, malonic acid, and proton concentration are fixed. -/
def FixedInputs (x : Concentration) : Prop :=
  x .bromate = bromateInitial ∧
  x .malonicAcid = malonicAcidInitial ∧
  x .proton = protonInitial

/-- Elementary mass-action rate for each printed step, in `M s^-1`. -/
def elementaryRate : ReactionStep → Concentration → ℝ
  | .r1, x => k1 * x .hbro2 * x .bromate * x .proton
  | .r2, x => k2 * x .bro2Radical * x .ceriumIII * x .proton
  | .r3, x => k3 * x .hbro2 ^ 2
  | .r4, x => k4 * x .hbro2 * x .bromide * x .proton
  | .r5, x => k5 * x .bromate * x .bromide * x .proton ^ 2
  | .r6, x => k6 * x .hbro * x .malonicAcid
  | .r7, x => k7 * x .ceriumIV * x .bromomalonicAcid

/-- Process-A steady-state balances.  The first equation is the BrO2-radical
balance `2 v₁ - v₂ = 0`; the second is the HBrO2 balance
`-v₁ + v₂ - 2 v₃ = 0`. -/
structure ProcessAStationaryState where
  concentration : Concentration
  nonnegative : NonnegativeConcentration concentration
  fixedInputs : FixedInputs concentration
  bro2RadicalBalance :
    2 * elementaryRate .r1 concentration - elementaryRate .r2 concentration = 0
  hbro2Balance :
    -elementaryRate .r1 concentration + elementaryRate .r2 concentration -
      2 * elementaryRate .r3 concentration = 0

/-- The source-active Process-A branch: reaction 1 has positive flux. -/
def ProcessAActive (s : ProcessAStationaryState) : Prop :=
  0 < elementaryRate .r1 s.concentration

/-- Process-B HBrO2 steady-state balance `-v₄ + v₅ = 0`. -/
structure ProcessBStationaryState where
  concentration : Concentration
  nonnegative : NonnegativeConcentration concentration
  fixedInputs : FixedInputs concentration
  hbro2Balance :
    -elementaryRate .r4 concentration + elementaryRate .r5 concentration = 0

/-- The source-active Process-B branch: reaction 5 has positive flux.  This
implies, rather than assumes as a submitted value, that bromide is nonzero. -/
def ProcessBActive (s : ProcessBStationaryState) : Prop :=
  0 < elementaryRate .r5 s.concentration

/-- Exact unrounded source-derived stationary concentration for Process A. -/
def hbro2ProcessARaw : ℝ :=
  k1 * bromateInitial * protonInitial / (2 * k3)

/-- Exact unrounded source-derived stationary concentration for Process B. -/
def hbro2ProcessBRaw : ℝ :=
  k5 * bromateInitial * protonInitial / k4

/-- A candidate is the stationary Process-A concentration exactly when active
steady states exist and every active steady state has that HBrO2 coordinate. -/
def IsActiveProcessAStationaryValue (candidate : ℝ) : Prop :=
  (∃ s : ProcessAStationaryState, ProcessAActive s) ∧
  ∀ s : ProcessAStationaryState,
    ProcessAActive s → s.concentration .hbro2 = candidate

/-- Analogous non-vacuous specification for active Process-B steady states. -/
def IsActiveProcessBStationaryValue (candidate : ℝ) : Prop :=
  (∃ s : ProcessBStationaryState, ProcessBActive s) ∧
  ∀ s : ProcessBStationaryState,
    ProcessBActive s → s.concentration .hbro2 = candidate

/-- Before activity is imposed, Process A also has the zero-HBrO2 branch. -/
def ProcessAStationaryBranchSpec : Prop :=
  ∀ s : ProcessAStationaryState,
    s.concentration .hbro2 = 0 ∨
      s.concentration .hbro2 = hbro2ProcessARaw

/-- Before activity is imposed, zero reaction-5 flux is the degenerate Process-B
branch; otherwise the stationary HBrO2 value is forced. -/
def ProcessBStationaryBranchSpec : Prop :=
  ∀ s : ProcessBStationaryState,
    elementaryRate .r5 s.concentration = 0 ∨
      s.concentration .hbro2 = hbro2ProcessBRaw

/-- Both exact requested outputs, including their evaluated rational forms. -/
def RawResultSpec : Prop :=
  ProcessAStationaryBranchSpec ∧
  ProcessBStationaryBranchSpec ∧
  IsActiveProcessAStationaryValue hbro2ProcessARaw ∧
  IsActiveProcessBStationaryValue hbro2ProcessBRaw ∧
  hbro2ProcessARaw = (3 : ℝ) / 500000 ∧
  hbro2ProcessBRaw = (63 : ℝ) / 1250000000000

/-- Three-significant-figure display value for Process A (`6.00e-6 M`). -/
def hbro2ProcessAReported : ℝ := (3 : ℝ) / 500000

/-- The Process-A three-significant-figure quantum (`1e-8 M`). -/
def processAReportingQuantum : ℝ := (1 : ℝ) / 100000000

/-- Three-significant-figure display value for Process B (`5.04e-11 M`). -/
def hbro2ProcessBReported : ℝ := (63 : ℝ) / 1250000000000

/-- The Process-B three-significant-figure quantum (`1e-13 M`). -/
def processBReportingQuantum : ℝ := (1 : ℝ) / 10000000000000

/-- The magnitude bands that mechanically select the two output-specific
three-significant-figure quanta. -/
def ReportingQuantumSpec : Prop :=
  ((1 : ℝ) / 1000000 ≤ hbro2ProcessARaw ∧
    hbro2ProcessARaw < (1 : ℝ) / 100000 ∧
    processAReportingQuantum = (1 : ℝ) / 100000000) ∧
  ((1 : ℝ) / 100000000000 ≤ hbro2ProcessBRaw ∧
    hbro2ProcessBRaw < (1 : ℝ) / 10000000000 ∧
    processBReportingQuantum = (1 : ℝ) / 10000000000000)

/-- Combined reporting proposition for both requested outputs. -/
def ReportedResultSpec : Prop :=
  RawResultSpec ∧
  ReportingQuantumSpec ∧
  Reporting.ReportsAtQuantum
    hbro2ProcessARaw hbro2ProcessAReported processAReportingQuantum ∧
  Reporting.ReportsAtQuantum
    hbro2ProcessBRaw hbro2ProcessBReported processBReportingQuantum

/-- A concrete nonnegative Process-A steady state.  Its radical coordinate is
chosen by solving the printed radical balance after the HBrO2 coordinate has
been derived from the two Process-A steady-state equations. -/
private def processAWitnessConcentration : Concentration := fun species =>
  match species with
  | .hbro2 => hbro2ProcessARaw
  | .bromate => bromateInitial
  | .proton => protonInitial
  | .bro2Radical => (18 : ℝ) / 77500
  | .ceriumIII => ceriumIVInitial / 2
  | .ceriumIV => ceriumIVInitial / 2
  | .malonicAcid => malonicAcidInitial
  | _ => 0

private def processAWitness : ProcessAStationaryState where
  concentration := processAWitnessConcentration
  nonnegative := by
    intro species
    cases species <;>
      norm_num [processAWitnessConcentration, hbro2ProcessARaw, k1, k3,
        bromateInitial, protonInitial, malonicAcidInitial, ceriumIVInitial]
  fixedInputs := by
    norm_num [FixedInputs, processAWitnessConcentration, bromateInitial,
      malonicAcidInitial, protonInitial]
  bro2RadicalBalance := by
    norm_num [elementaryRate, processAWitnessConcentration, hbro2ProcessARaw,
      k1, k2, k3, bromateInitial, protonInitial, ceriumIVInitial]
  hbro2Balance := by
    norm_num [elementaryRate, processAWitnessConcentration, hbro2ProcessARaw,
      k1, k2, k3, bromateInitial, protonInitial, ceriumIVInitial]

/-- A concrete nonnegative Process-B steady state with positive reaction-5
flux.  The bromide coordinate is only a cancellable positive witness. -/
private def processBWitnessConcentration : Concentration := fun species =>
  match species with
  | .hbro2 => hbro2ProcessBRaw
  | .bromate => bromateInitial
  | .bromide => 1
  | .proton => protonInitial
  | .malonicAcid => malonicAcidInitial
  | .ceriumIII => ceriumIVInitial
  | _ => 0

private def processBWitness : ProcessBStationaryState where
  concentration := processBWitnessConcentration
  nonnegative := by
    intro species
    cases species <;>
      norm_num [processBWitnessConcentration, hbro2ProcessBRaw, k4, k5,
        bromateInitial, protonInitial, malonicAcidInitial, ceriumIVInitial]
  fixedInputs := by
    norm_num [FixedInputs, processBWitnessConcentration, bromateInitial,
      malonicAcidInitial, protonInitial]
  hbro2Balance := by
    norm_num [elementaryRate, processBWitnessConcentration, hbro2ProcessBRaw,
      k4, k5, bromateInitial, protonInitial]

/-- Eliminating the BrO2-radical rate from the two Process-A balances leaves
exactly the inactive zero branch and the positive stationary branch. -/
private theorem processA_stationary_branches : ProcessAStationaryBranchSpec := by
  intro s
  rcases s.fixedInputs with ⟨hbromate, _hmalonic, hproton⟩
  have hradical := s.bro2RadicalBalance
  have hhbro2 := s.hbro2Balance
  simp only [elementaryRate] at hradical hhbro2
  rw [hbromate, hproton] at hradical hhbro2
  norm_num [k1, k2, k3, bromateInitial, protonInitial] at hradical hhbro2
  by_cases hzero : s.concentration .hbro2 = 0
  · exact Or.inl hzero
  · right
    have hnonnegative := s.nonnegative .hbro2
    have hpositive : 0 < s.concentration .hbro2 :=
      lt_of_le_of_ne hnonnegative (Ne.symm hzero)
    norm_num [hbro2ProcessARaw, k1, k3, bromateInitial, protonInitial]
    nlinarith [hradical, hhbro2]

/-- Factoring the Process-B balance retains the zero-production branch; on
the complementary branch the common bromide factor can be cancelled. -/
private theorem processB_stationary_branches : ProcessBStationaryBranchSpec := by
  intro s
  by_cases hzero : elementaryRate .r5 s.concentration = 0
  · exact Or.inl hzero
  · right
    rcases s.fixedInputs with ⟨hbromate, _hmalonic, hproton⟩
    have hbalance := s.hbro2Balance
    have hbromide : s.concentration .bromide ≠ 0 := by
      intro hbromideZero
      apply hzero
      simp [elementaryRate, hbromideZero]
    simp only [elementaryRate] at hbalance
    rw [hbromate, hproton] at hbalance
    have hfactored :
        s.concentration .bromide *
          (-k4 * s.concentration .hbro2 * protonInitial +
            k5 * bromateInitial * protonInitial ^ 2) = 0 := by
      calc
        _ = -(k4 * s.concentration .hbro2 *
              s.concentration .bromide * protonInitial) +
              k5 * bromateInitial * s.concentration .bromide *
                protonInitial ^ 2 := by ring
        _ = 0 := hbalance
    have hrateRelation :
        -k4 * s.concentration .hbro2 * protonInitial +
          k5 * bromateInitial * protonInitial ^ 2 = 0 :=
      (mul_eq_zero.mp hfactored).resolve_left hbromide
    norm_num [k4, k5, bromateInitial, protonInitial, hbro2ProcessBRaw] at hrateRelation ⊢
    linarith

private theorem processA_active_value :
    IsActiveProcessAStationaryValue hbro2ProcessARaw := by
  constructor
  · refine ⟨processAWitness, ?_⟩
    norm_num [ProcessAActive, processAWitness, elementaryRate,
      processAWitnessConcentration, hbro2ProcessARaw, k1, k3,
      bromateInitial, protonInitial]
  · intro s hactive
    unfold ProcessAActive at hactive
    rcases processA_stationary_branches s with hzero | hvalue
    · have hrateZero : elementaryRate .r1 s.concentration = 0 := by
        simp [elementaryRate, hzero]
      exact (ne_of_gt hactive hrateZero).elim
    · exact hvalue

private theorem processB_active_value :
    IsActiveProcessBStationaryValue hbro2ProcessBRaw := by
  constructor
  · refine ⟨processBWitness, ?_⟩
    norm_num [ProcessBActive, processBWitness, elementaryRate,
      processBWitnessConcentration, k5, bromateInitial, protonInitial]
  · intro s hactive
    unfold ProcessBActive at hactive
    rcases processB_stationary_branches s with hzero | hvalue
    · exact (ne_of_gt hactive hzero).elim
    · exact hvalue

/-- The Process-A raw requested-output carrier. -/
theorem hbro2_process_a_raw :
    IsActiveProcessAStationaryValue hbro2ProcessARaw ∧
      hbro2ProcessARaw = (3 : ℝ) / 500000 := by
  refine ⟨processA_active_value, ?_⟩
  norm_num [hbro2ProcessARaw, k1, k3, bromateInitial, protonInitial]

/-- The Process-B raw requested-output carrier. -/
theorem hbro2_process_b_raw :
    IsActiveProcessBStationaryValue hbro2ProcessBRaw ∧
      hbro2ProcessBRaw = (63 : ℝ) / 1250000000000 := by
  refine ⟨processB_active_value, ?_⟩
  norm_num [hbro2ProcessBRaw, k4, k5, bromateInitial, protonInitial]

/-- The complete raw result, including both inactive branches. -/
theorem raw_result : RawResultSpec := by
  refine ⟨processA_stationary_branches, processB_stationary_branches,
    processA_active_value, processB_active_value, ?_, ?_⟩
  · norm_num [hbro2ProcessARaw, k1, k3, bromateInitial, protonInitial]
  · norm_num [hbro2ProcessBRaw, k4, k5, bromateInitial, protonInitial]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"hbro2_process_a","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"6.00e-6","reporting_quantum":"1/100000000","raw_declaration":"IChO2026Problems.IChO2026T2A2.hbro2ProcessARaw","reporting_declaration":"IChO2026Problems.IChO2026T2A2.hbro2_process_a_reported"}

/-- The Process-A reporting certificate at its three-significant-figure quantum. -/
theorem hbro2_process_a_reported :
    Reporting.ReportsAtQuantum
      hbro2ProcessARaw hbro2ProcessAReported processAReportingQuantum := by
  unfold Reporting.ReportsAtQuantum
  refine ⟨?_, ⟨600, ?_⟩, ?_⟩
  · norm_num [processAReportingQuantum]
  · norm_num [hbro2ProcessAReported, processAReportingQuantum]
  · norm_num [hbro2ProcessARaw, hbro2ProcessAReported,
      processAReportingQuantum, k1, k3, bromateInitial, protonInitial]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"hbro2_process_b","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"5.04e-11","reporting_quantum":"1/10000000000000","raw_declaration":"IChO2026Problems.IChO2026T2A2.hbro2ProcessBRaw","reporting_declaration":"IChO2026Problems.IChO2026T2A2.hbro2_process_b_reported"}

/-- The Process-B reporting certificate at its three-significant-figure quantum. -/
theorem hbro2_process_b_reported :
    Reporting.ReportsAtQuantum
      hbro2ProcessBRaw hbro2ProcessBReported processBReportingQuantum := by
  unfold Reporting.ReportsAtQuantum
  refine ⟨?_, ⟨504, ?_⟩, ?_⟩
  · norm_num [processBReportingQuantum]
  · norm_num [hbro2ProcessBReported, processBReportingQuantum]
  · norm_num [hbro2ProcessBRaw, hbro2ProcessBReported,
      processBReportingQuantum, k4, k5, bromateInitial, protonInitial]

/-- Combined reported result for both requested outputs. -/
theorem reported_result : ReportedResultSpec := by
  refine ⟨raw_result, ?_, hbro2_process_a_reported, hbro2_process_b_reported⟩
  norm_num [ReportingQuantumSpec, hbro2ProcessARaw, hbro2ProcessBRaw,
    processAReportingQuantum, processBReportingQuantum, k1, k3, k4, k5,
    bromateInitial, protonInitial]

/-- Candidate-payload-bound raw result contract.  The literal is replaced by
the solve artifact's mechanically computed SHA-256 before handoff. -/
theorem rawResultContract :
    ("0cb161c99cbdb6f4ea426501924bab535e340228a247246d629ceb1fca8e9905" : String) =
      "0cb161c99cbdb6f4ea426501924bab535e340228a247246d629ceb1fca8e9905" ∧
      RawResultSpec := by
  exact ⟨rfl, raw_result⟩

/-- Candidate-payload-bound reported result contract. -/
theorem reportedResultContract :
    ("c2f0e19f04afbbd356e27ca1f73ea426db339825074d7e35e8034a3edcb90b10" : String) =
      "c2f0e19f04afbbd356e27ca1f73ea426db339825074d7e35e8034a3edcb90b10" ∧
      ReportedResultSpec := by
  exact ⟨rfl, reported_result⟩

end

end IChO2026Problems.IChO2026T2A2
