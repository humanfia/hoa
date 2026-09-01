import Mathlib
import IChO2026Chem

/-!
# IChO 2026, theory problem 2, part 3

The numerical convention in this file is that concentrations are measured in
`mol dm⁻³` (M), times in seconds, and mass-action rates in `M s⁻¹`.  Thus the
printed numerical rate constants are represented by real numbers in the
corresponding powers of M and seconds.

The critical bromide concentration is derived from the boundary at which the
mass-action rates of elementary steps (1) and (4) are equal.  The stationary
HBrO₂ concentrations requested in the preceding part are derived locally from
the printed mechanism; they are not imported from another generated target.
-/

namespace IChO2026Problems
namespace ProblemIcho2026T2A3

noncomputable section

/-- Chemical entities explicitly named in the problem context and mechanism. -/
inductive Species where
  | potassiumBromate
  | malonicAcid
  | ceriumIVSulfate
  | sulfuricAcid
  | bromousAcid
  | bromate
  | proton
  | bromineDioxideRadical
  | water
  | ceriumIII
  | ceriumIV
  | hypobromousAcid
  | bromide
  | bromomalonicAcid
  | carbonDioxide
  | unspecifiedProcessCProduct
  deriving DecidableEq, Repr

/-- Every elementary step displayed in this target takes place in solution. -/
inductive Phase where
  | aqueous
  deriving DecidableEq, Repr

/-- A species and its positive-in-the-source stoichiometric coefficient. -/
abbrev StoichiometricTerm := Species × ℕ

/-- The source-visible skeleton of an elementary reaction.

`rateOrder` records the total order indicated by its printed mass-action rate
constant.  It is kept separate from the numerical rate constant so that the
different printed units are not conflated.
-/
structure ElementaryStep where
  reactants : List StoichiometricTerm
  products : List StoichiometricTerm
  phase : Phase := .aqueous
  rateOrder : ℕ
  deriving Repr

def step1 : ElementaryStep :=
  { reactants := [(.bromousAcid, 1), (.bromate, 1), (.proton, 1)]
    products := [(.bromineDioxideRadical, 2), (.water, 1)]
    rateOrder := 3 }

def step2 : ElementaryStep :=
  { reactants := [(.bromineDioxideRadical, 1), (.ceriumIII, 1), (.proton, 1)]
    products := [(.bromousAcid, 1), (.ceriumIV, 1)]
    rateOrder := 3 }

def step3 : ElementaryStep :=
  { reactants := [(.bromousAcid, 2)]
    products := [(.bromate, 1), (.hypobromousAcid, 1), (.proton, 1)]
    rateOrder := 2 }

def step4 : ElementaryStep :=
  { reactants := [(.bromousAcid, 1), (.bromide, 1), (.proton, 1)]
    products := [(.hypobromousAcid, 2)]
    rateOrder := 3 }

def step5 : ElementaryStep :=
  { reactants := [(.bromate, 1), (.bromide, 1), (.proton, 2)]
    products := [(.hypobromousAcid, 1), (.bromousAcid, 1)]
    rateOrder := 4 }

def step6 : ElementaryStep :=
  { reactants := [(.hypobromousAcid, 1), (.malonicAcid, 1)]
    products := [(.bromomalonicAcid, 1), (.water, 1)]
    rateOrder := 2 }

def step7 : ElementaryStep :=
  { reactants := [(.ceriumIV, 1), (.bromomalonicAcid, 1)]
    products := [(.ceriumIII, 1), (.bromide, 1), (.unspecifiedProcessCProduct, 1)]
    rateOrder := 2 }

def processA : List ElementaryStep := [step1, step2, step3]
def processB : List ElementaryStep := [step4, step5, step6]
def processC : List ElementaryStep := [step7]

/-- Numerical data printed on page Q2-2.

The fields `k1`, `k2`, and `k4` have units M⁻² s⁻¹; `k3`, `k6`, and `k7`
have units M⁻¹ s⁻¹; and `k5` has units M⁻³ s⁻¹.  The remaining fields are
molar concentrations.
-/
structure BZKineticData where
  k1 : ℝ
  k2 : ℝ
  k3 : ℝ
  k4 : ℝ
  k5 : ℝ
  k6 : ℝ
  k7 : ℝ
  bromate : ℝ
  malonicAcid : ℝ
  proton : ℝ
  ceriumIV0 : ℝ

/-- Exact-as-printed source data; no measurement uncertainty is asserted. -/
def printedData : BZKineticData :=
  { k1 := (10 : ℝ) ^ 4
    k2 := ((62 : ℝ) / 10) * (10 : ℝ) ^ 4
    k3 := 4 * (10 : ℝ) ^ 7
    k4 := 2 * (10 : ℝ) ^ 9
    k5 := (21 : ℝ) / 10
    k6 := (82 : ℝ) / 10
    k7 := (10 : ℝ) ^ 2
    bromate := (6 : ℝ) / 100
    malonicAcid := (1 : ℝ) / 10
    proton := (8 : ℝ) / 10
    ceriumIV0 := (1 : ℝ) / 1000 }

/-- The conjunction binds every numerical field to its exact problem locator. -/
def PrintedDataSpecification (d : BZKineticData) : Prop :=
  d.k1 = (10 : ℝ) ^ 4 ∧
  d.k2 = ((62 : ℝ) / 10) * (10 : ℝ) ^ 4 ∧
  d.k3 = 4 * (10 : ℝ) ^ 7 ∧
  d.k4 = 2 * (10 : ℝ) ^ 9 ∧
  d.k5 = (21 : ℝ) / 10 ∧
  d.k6 = (82 : ℝ) / 10 ∧
  d.k7 = (10 : ℝ) ^ 2 ∧
  d.bromate = (6 : ℝ) / 100 ∧
  d.malonicAcid = (1 : ℝ) / 10 ∧
  d.proton = (8 : ℝ) / 10 ∧
  d.ceriumIV0 = (1 : ℝ) / 1000 ∧
  0 < d.k1 ∧ 0 < d.k2 ∧ 0 < d.k3 ∧ 0 < d.k4 ∧
  0 < d.k5 ∧ 0 < d.k6 ∧ 0 < d.k7 ∧
  0 < d.bromate ∧ 0 < d.malonicAcid ∧ 0 < d.proton ∧ 0 < d.ceriumIV0

theorem printedData_specification : PrintedDataSpecification printedData := by
  norm_num [PrintedDataSpecification, printedData]

/-- Mass-action rate of elementary step (1), in M s⁻¹. -/
def rate1 (d : BZKineticData) (hbrO2 : ℝ) : ℝ :=
  d.k1 * hbrO2 * d.bromate * d.proton

/-- Mass-action event rate of elementary step (3), in M s⁻¹. -/
def rate3 (d : BZKineticData) (hbrO2 : ℝ) : ℝ :=
  d.k3 * hbrO2 ^ 2

/-- Mass-action rate of elementary step (4), in M s⁻¹. -/
def rate4 (d : BZKineticData) (hbrO2 bromide : ℝ) : ℝ :=
  d.k4 * hbrO2 * bromide * d.proton

/-- Mass-action rate of elementary step (5), in M s⁻¹. -/
def rate5 (d : BZKineticData) (bromide : ℝ) : ℝ :=
  d.k5 * d.bromate * bromide * d.proton ^ 2

/-- Reduced Process-A HBrO₂ steady-state balance after eliminating the
BrO₂ radical balance: step (1) produces the net HBrO₂ influx, while two
HBrO₂ are consumed per event of step (3). -/
def ProcessAReducedSteadyState
    (d : BZKineticData) (hbrO2 : ℝ) : Prop :=
  0 < hbrO2 ∧ rate1 d hbrO2 = 2 * rate3 d hbrO2

/-- Process-B HBrO₂ steady-state balance at a positive bromide concentration. -/
def ProcessBSteadyStateAt
    (d : BZKineticData) (bromide hbrO2 : ℝ) : Prop :=
  0 < bromide ∧ 0 < hbrO2 ∧ rate4 d hbrO2 bromide = rate5 d bromide

/-- Inline candidate for `[HBrO₂]A`, derived from the reduced Process-A
steady-state equation rather than imported from T2-A2. -/
def stationaryHBrO2A : ℝ :=
  printedData.k1 * printedData.bromate * printedData.proton /
    (2 * printedData.k3)

/-- Inline candidate for `[HBrO₂]B`, obtained by cancelling the common positive
`[Br⁻][H⁺]` factor from the rates of steps (4) and (5). -/
def stationaryHBrO2B : ℝ :=
  printedData.k5 * printedData.bromate * printedData.proton / printedData.k4

/-- Discharge of the preceding-part prerequisite from problem-only kinetic
data.  The exact results are `6.00e-6 M` and `5.04e-11 M`; the looser fallback
values printed by the problem are not used. -/
theorem previousPart_stationaryConcentrations :
    ProcessAReducedSteadyState printedData stationaryHBrO2A ∧
    stationaryHBrO2A = ((6 : ℝ) / 1000000) ∧
    (∀ bromide : ℝ, 0 < bromide →
      ProcessBSteadyStateAt printedData bromide stationaryHBrO2B) ∧
    stationaryHBrO2B = ((63 : ℝ) / 1250000000000) := by
  norm_num [ProcessAReducedSteadyState, ProcessBSteadyStateAt,
    stationaryHBrO2A, stationaryHBrO2B, rate1, rate3, rate4, rate5,
    printedData]
  intro bromide hbromide
  exact ⟨hbromide, by ring⟩

/-- Source-derived, unrounded candidate for the critical bromide concentration.

At the switch, rates (1) and (4) are equal.  Their common positive factors
`[HBrO₂]` and `[H⁺]` cancel, leaving `k1 [BrO₃⁻] / k4`.
-/
def bromideCriticalRaw : ℝ :=
  printedData.k1 * printedData.bromate / printedData.k4

/-- Full chemical characterization of the raw candidate: equality at the
boundary, the two strict rate-order directions on either side, and exact
evaluation from the printed inputs. -/
def BromideCriticalRawDerivation : Prop :=
  PrintedDataSpecification printedData ∧
  0 < bromideCriticalRaw ∧
  bromideCriticalRaw =
    printedData.k1 * printedData.bromate / printedData.k4 ∧
  (∀ hbrO2 : ℝ, 0 < hbrO2 →
    rate1 printedData hbrO2 =
      rate4 printedData hbrO2 bromideCriticalRaw) ∧
  (∀ hbrO2 bromide : ℝ, 0 < hbrO2 → 0 ≤ bromide →
    (rate4 printedData hbrO2 bromide > rate1 printedData hbrO2 ↔
      bromide > bromideCriticalRaw) ∧
    (rate1 printedData hbrO2 > rate4 printedData hbrO2 bromide ↔
      bromide < bromideCriticalRaw)) ∧
  bromideCriticalRaw = ((3 : ℝ) / 10000000)

/-- Raw answer-blind result contract.  The nondegenerate enclosure is exactly
the `3.00e-7 ± 0.5e-9` final reporting cell, not a widened empirical tolerance. -/
theorem bromideCriticalRawResult :
    (IChO2026Problems.ProblemIcho2026T2A3.BromideCriticalRawDerivation) ∧
    (((599 : ℝ) / 2000000000) ≤
        (IChO2026Problems.ProblemIcho2026T2A3.bromideCriticalRaw) ∧
      (IChO2026Problems.ProblemIcho2026T2A3.bromideCriticalRaw) ≤
        ((601 : ℝ) / 2000000000)) := by
  constructor
  · unfold BromideCriticalRawDerivation
    refine ⟨printedData_specification, ?_, rfl, ?_, ?_, ?_⟩
    · norm_num [bromideCriticalRaw, printedData]
    · intro hbrO2 _
      norm_num [rate1, rate4, bromideCriticalRaw, printedData]
      ring
    · intro hbrO2 bromide hhbrO2 _
      constructor
      · constructor <;> intro hrate
        · norm_num [rate1, rate4, bromideCriticalRaw, printedData] at hrate ⊢
          nlinarith
        · norm_num [rate1, rate4, bromideCriticalRaw, printedData] at hrate ⊢
          nlinarith
      · constructor <;> intro hrate
        · norm_num [rate1, rate4, bromideCriticalRaw, printedData] at hrate ⊢
          nlinarith
        · norm_num [rate1, rate4, bromideCriticalRaw, printedData] at hrate ⊢
          nlinarith
    · norm_num [bromideCriticalRaw, printedData]
  · norm_num [bromideCriticalRaw, printedData]

/-- Final three-significant-figure report using the project-wide
half-away-from-zero rule. -/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"bromide_critical","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"3/10000000","reporting_quantum":"1/1000000000","raw_declaration":"IChO2026Problems.ProblemIcho2026T2A3.bromideCriticalRaw","reporting_declaration":"IChO2026Problems.ProblemIcho2026T2A3.bromideCriticalReportedResult"}
theorem bromideCriticalReportedResult :
    IChO2026Chem.Reporting.ReportsAtQuantum
      (IChO2026Problems.ProblemIcho2026T2A3.bromideCriticalRaw)
      ((3 : ℝ) / 10000000)
      ((1 : ℝ) / 1000000000) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ?_, ?_⟩
  · exact ⟨300, by norm_num⟩
  · rw [if_pos]
    · constructor <;> norm_num [bromideCriticalRaw, printedData]
    · norm_num [bromideCriticalRaw, printedData]

end
end ProblemIcho2026T2A3
end IChO2026Problems
