import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T2-A2: stationary bromous-acid concentrations

All scalar concentration values below are numerical values in `mol dm⁻³` (the
problem's `M`), and all rate-constant values are numerical values in the printed
`M`/second units.  The unit exponents attached to each rate constant preserve
the source units while the exact real-valued formulas expose the algebra used
by the steady-state approximation.
-/

namespace IChO2026Problems
namespace T2A2

noncomputable section

/-- Numerical value of a molar concentration in `mol dm⁻³`. -/
abbrev MolarConcentration := ℝ

/-- Numerical value of a reaction rate in `mol dm⁻³ s⁻¹`. -/
abbrev ReactionRate := ℝ

/-- Reagents explicitly named as the initial BZ mixture. -/
inductive FeedReagent
  | potassiumBromate
  | malonicAcid
  | ceriumIVSulfate
  | sulfuricAcid
deriving DecidableEq, Fintype, Repr

/-- The four reagents listed in the statement, before spectator-ion expansion. -/
def initialFeed : List FeedReagent :=
  [.potassiumBromate, .malonicAcid, .ceriumIVSulfate, .sulfuricAcid]

/-- Species and named product classes occurring in the printed context and mechanism. -/
inductive Species
  | hBrO2
  | brO3Minus
  | proton
  | brO2Radical
  | water
  | ceIII
  | ceIV
  | hBrO
  | bromide
  | malonicAcid
  | bromomalonicAcid
  | carbonDioxide
  | otherProducts
deriving DecidableEq, Fintype, Repr

/-- The three printed kinetic processes. -/
inductive BZProcess
  | A
  | B
  | C
deriving DecidableEq, Fintype, Repr

/-- The two solution colours explicitly assigned to the oscillating cerium states. -/
inductive SolutionColour
  | yellow
  | colourless
deriving DecidableEq, Fintype, Repr

/-- During Process A the source assigns the yellow state; during Process B it assigns
the colourless state.  Process C is continuous and has no separate colour assignment. -/
def processColour : BZProcess → Option SolutionColour
  | .A => some .yellow
  | .B => some .colourless
  | .C => none

/-- Reaction (1): HBrO₂ + BrO₃⁻ + H⁺ ⟶ 2 BrO₂· + H₂O. -/
def reaction1 : CRNT.Reaction Species where
  source := fun s =>
    match s with
    | .hBrO2 | .brO3Minus | .proton => 1
    | _ => 0
  target := fun s =>
    match s with
    | .brO2Radical => 2
    | .water => 1
    | _ => 0

/-- Reaction (2): BrO₂· + Ce³⁺ + H⁺ ⟶ HBrO₂ + Ce⁴⁺. -/
def reaction2 : CRNT.Reaction Species where
  source := fun s =>
    match s with
    | .brO2Radical | .ceIII | .proton => 1
    | _ => 0
  target := fun s =>
    match s with
    | .hBrO2 | .ceIV => 1
    | _ => 0

/-- Reaction (3): 2 HBrO₂ ⟶ BrO₃⁻ + HBrO + H⁺. -/
def reaction3 : CRNT.Reaction Species where
  source := fun s =>
    match s with
    | .hBrO2 => 2
    | _ => 0
  target := fun s =>
    match s with
    | .brO3Minus | .hBrO | .proton => 1
    | _ => 0

/-- Reaction (4): HBrO₂ + Br⁻ + H⁺ ⟶ 2 HBrO. -/
def reaction4 : CRNT.Reaction Species where
  source := fun s =>
    match s with
    | .hBrO2 | .bromide | .proton => 1
    | _ => 0
  target := fun s =>
    match s with
    | .hBrO => 2
    | _ => 0

/-- Reaction (5): BrO₃⁻ + Br⁻ + 2 H⁺ ⟶ HBrO + HBrO₂. -/
def reaction5 : CRNT.Reaction Species where
  source := fun s =>
    match s with
    | .brO3Minus | .bromide => 1
    | .proton => 2
    | _ => 0
  target := fun s =>
    match s with
    | .hBrO | .hBrO2 => 1
    | _ => 0

/-- Reaction (6): HBrO + MA ⟶ BMA + H₂O. -/
def reaction6 : CRNT.Reaction Species where
  source := fun s =>
    match s with
    | .hBrO | .malonicAcid => 1
    | _ => 0
  target := fun s =>
    match s with
    | .bromomalonicAcid | .water => 1
    | _ => 0

/-- Reaction (7): Ce⁴⁺ + BMA ⟶ Ce³⁺ + Br⁻ + other products.
`otherProducts` preserves the source's deliberately unspecified product class. -/
def reaction7 : CRNT.Reaction Species where
  source := fun s =>
    match s with
    | .ceIV | .bromomalonicAcid => 1
    | _ => 0
  target := fun s =>
    match s with
    | .ceIII | .bromide | .otherProducts => 1
    | _ => 0

/-- The printed partition of reactions into Process A. -/
def processAReactions : List (CRNT.Reaction Species) :=
  [reaction1, reaction2, reaction3]

/-- The printed partition of reactions into Process B. -/
def processBReactions : List (CRNT.Reaction Species) :=
  [reaction4, reaction5, reaction6]

/-- The printed partition of reactions into continuous Process C. -/
def processCReactions : List (CRNT.Reaction Species) :=
  [reaction7]

/-- A printed rate constant together with its exponents in `M` and seconds.
For example, exponents `(-2,-1)` denote `M⁻² s⁻¹`. -/
structure PrintedRateConstant where
  value : ℝ
  molarityExponent : ℤ
  secondExponent : ℤ

def k1 : PrintedRateConstant :=
  ⟨(1 : ℝ) * 10 ^ 4, -2, -1⟩

def k2 : PrintedRateConstant :=
  ⟨((62 : ℝ) / 10) * 10 ^ 4, -2, -1⟩

def k3 : PrintedRateConstant :=
  ⟨(4 : ℝ) * 10 ^ 7, -1, -1⟩

def k4 : PrintedRateConstant :=
  ⟨(2 : ℝ) * 10 ^ 9, -2, -1⟩

def k5 : PrintedRateConstant :=
  ⟨(21 : ℝ) / 10, -3, -1⟩

def k6 : PrintedRateConstant :=
  ⟨(82 : ℝ) / 10, -1, -1⟩

def k7 : PrintedRateConstant :=
  ⟨(1 : ℝ) * 10 ^ 2, -1, -1⟩

/-- Exact source-stipulated initial concentrations, all in `mol dm⁻³`. -/
structure SourceConcentrations where
  bromate0 : MolarConcentration
  malonicAcid0 : MolarConcentration
  proton0 : MolarConcentration
  ceriumIV0 : MolarConcentration

def sourceConcentrations : SourceConcentrations where
  bromate0 := (6 : ℝ) / 100
  malonicAcid0 := (1 : ℝ) / 10
  proton0 := (8 : ℝ) / 10
  ceriumIV0 := (1 : ℝ) / 1000

/-- The statement maintains bromate concentration throughout the oscillation. -/
def bromateConcentration : MolarConcentration :=
  sourceConcentrations.bromate0

/-- The statement maintains malonic-acid concentration throughout the oscillation. -/
def malonicAcidConcentration : MolarConcentration :=
  sourceConcentrations.malonicAcid0

/-- Constant proton concentration corresponding to the maintained pH. -/
def protonConcentration : MolarConcentration :=
  sourceConcentrations.proton0

/-- Initial Ce⁴⁺ concentration; unlike the other printed reactants, it is not
assumed constant. -/
def initialCeriumIVConcentration : MolarConcentration :=
  sourceConcentrations.ceriumIV0

/-- Source positivity facts needed when eliminating concentration factors. -/
theorem sourceData_positive :
    0 < bromateConcentration ∧
      0 < malonicAcidConcentration ∧
      0 < protonConcentration ∧
      0 < initialCeriumIVConcentration ∧
      0 < k1.value ∧ 0 < k2.value ∧ 0 < k3.value ∧ 0 < k4.value ∧
      0 < k5.value ∧ 0 < k6.value ∧ 0 < k7.value := by
  norm_num [bromateConcentration, malonicAcidConcentration,
    protonConcentration, initialCeriumIVConcentration,
    sourceConcentrations, k1, k2, k3, k4, k5, k6, k7]

/-- Mass-action rate of reaction (1) during Process A. -/
def rate1 (hbro2 : MolarConcentration) : ReactionRate :=
  k1.value * hbro2 * bromateConcentration * protonConcentration

/-- Mass-action rate of reaction (2) during Process A. -/
def rate2 (brO2Radical ceIII : MolarConcentration) : ReactionRate :=
  k2.value * brO2Radical * ceIII * protonConcentration

/-- Mass-action rate of reaction (3) during Process A. -/
def rate3 (hbro2 : MolarConcentration) : ReactionRate :=
  k3.value * hbro2 ^ 2

/-- Mass-action rate of reaction (4) during Process B. -/
def rate4 (hbro2 bromide : MolarConcentration) : ReactionRate :=
  k4.value * hbro2 * bromide * protonConcentration

/-- Mass-action rate of reaction (5) during Process B. -/
def rate5 (bromide : MolarConcentration) : ReactionRate :=
  k5.value * bromateConcentration * bromide * protonConcentration ^ 2

/-- Mass-action rate of reaction (6), included to preserve the full Process B table. -/
def rate6 (hbrO : MolarConcentration) : ReactionRate :=
  k6.value * hbrO * malonicAcidConcentration

/-- Mass-action rate of continuous reaction (7). -/
def rate7 (ceriumIV bma : MolarConcentration) : ReactionRate :=
  k7.value * ceriumIV * bma

/-- Full Process A steady-state equations for the BrO₂ radical and HBrO₂.
Reaction (1) creates two radicals, reaction (2) consumes one radical and creates
one HBrO₂, and reaction (3) consumes two HBrO₂. -/
def ProcessASteadyState
    (hbro2 brO2Radical ceIII : MolarConcentration) : Prop :=
  0 < hbro2 ∧ 0 ≤ brO2Radical ∧ 0 < ceIII ∧
    2 * rate1 hbro2 = rate2 brO2Radical ceIII ∧
    -rate1 hbro2 + rate2 brO2Radical ceIII - 2 * rate3 hbro2 = 0

/-- Eliminating the radical rate from the two Process A stationary equations. -/
def ProcessAReducedSteadyState (hbro2 : MolarConcentration) : Prop :=
  0 < hbro2 ∧ rate1 hbro2 = 2 * rate3 hbro2

/-- Process B stationarity equates production by reaction (5) with consumption
by reaction (4); active Process B supplies a positive bromide concentration. -/
def ProcessBSteadyState
    (hbro2 bromide : MolarConcentration) : Prop :=
  0 < hbro2 ∧ 0 < bromide ∧ rate5 bromide = rate4 hbro2 bromide

/-- The bromide-independent Process B equation after cancellation of positive
`[Br⁻]` and one positive `[H⁺]` factor. -/
def ProcessBReducedSteadyState (hbro2 : MolarConcentration) : Prop :=
  0 < hbro2 ∧
    k5.value * bromateConcentration * protonConcentration = k4.value * hbro2

theorem processA_reduced_of_full
    {hbro2 brO2Radical ceIII : MolarConcentration}
    (h : ProcessASteadyState hbro2 brO2Radical ceIII) :
    ProcessAReducedSteadyState hbro2 := by
  unfold ProcessASteadyState at h
  unfold ProcessAReducedSteadyState
  rcases h with ⟨hhbro2, _, _, hradical, hbalance⟩
  refine ⟨hhbro2, ?_⟩
  linarith

theorem processB_reduced_of_full
    {hbro2 bromide : MolarConcentration}
    (h : ProcessBSteadyState hbro2 bromide) :
    ProcessBReducedSteadyState hbro2 := by
  unfold ProcessBSteadyState at h
  unfold ProcessBReducedSteadyState
  rcases h with ⟨hhbro2, hbromide, hrate⟩
  refine ⟨hhbro2, ?_⟩
  have hproton : protonConcentration ≠ 0 := by
    norm_num [protonConcentration, sourceConcentrations]
  have hfactor : bromide * protonConcentration ≠ 0 :=
    mul_ne_zero (ne_of_gt hbromide) hproton
  apply mul_left_cancel₀ hfactor
  calc
    (bromide * protonConcentration) *
          (k5.value * bromateConcentration * protonConcentration) =
        rate5 bromide := by
          rw [rate5]
          ring
    _ = rate4 hbro2 bromide := hrate
    _ = (bromide * protonConcentration) * (k4.value * hbro2) := by
          rw [rate4]
          ring

/-- Raw source-derived stationary concentration for Process A, before any
decimal reporting.  No fallback value is used. -/
def hbro2ProcessARaw : MolarConcentration :=
  k1.value * bromateConcentration * protonConcentration / (2 * k3.value)

/-- Raw source-derived stationary concentration for Process B, before any
decimal reporting.  Bromide has canceled from the active-process balance. -/
def hbro2ProcessBRaw : MolarConcentration :=
  k5.value * bromateConcentration * protonConcentration / k4.value

theorem hbro2ProcessARaw_stationary :
    ProcessAReducedSteadyState hbro2ProcessARaw := by
  norm_num [ProcessAReducedSteadyState, rate1, rate3,
    hbro2ProcessARaw, k1, k3, bromateConcentration,
    protonConcentration, sourceConcentrations]

theorem hbro2ProcessARaw_realizable
    (ceIII : MolarConcentration) (hCeIII : 0 < ceIII) :
    ∃ brO2Radical : MolarConcentration,
      ProcessASteadyState hbro2ProcessARaw brO2Radical ceIII := by
  rcases sourceData_positive with
    ⟨hbromate, _, hproton, _, hk1, hk2, _, _, _, _, _⟩
  rcases hbro2ProcessARaw_stationary with ⟨hhbro2, hreduced⟩
  let brO2Radical : MolarConcentration :=
    (2 * rate1 hbro2ProcessARaw) /
      (k2.value * ceIII * protonConcentration)
  have hrate1 : 0 < rate1 hbro2ProcessARaw := by
    unfold rate1
    positivity
  have hdenominator : 0 < k2.value * ceIII * protonConcentration := by
    positivity
  have hradical : 0 ≤ brO2Radical := by
    dsimp [brO2Radical]
    exact le_of_lt (div_pos (mul_pos (by norm_num) hrate1) hdenominator)
  have hrate2 :
      2 * rate1 hbro2ProcessARaw = rate2 brO2Radical ceIII := by
    unfold rate2
    dsimp [brO2Radical]
    field_simp [ne_of_gt hdenominator]
  refine ⟨brO2Radical, hhbro2, hradical, hCeIII, hrate2, ?_⟩
  linarith

theorem hbro2ProcessA_unique
    {hbro2 : MolarConcentration}
    (h : ProcessAReducedSteadyState hbro2) :
    hbro2 = hbro2ProcessARaw := by
  unfold ProcessAReducedSteadyState at h
  rcases h with ⟨hhbro2, hrate⟩
  norm_num [rate1, rate3, k1, k3, bromateConcentration,
    protonConcentration, sourceConcentrations] at hrate
  norm_num [hbro2ProcessARaw, k1, k3, bromateConcentration,
    protonConcentration, sourceConcentrations]
  nlinarith

theorem hbro2ProcessBRaw_stationary :
    ProcessBReducedSteadyState hbro2ProcessBRaw := by
  norm_num [ProcessBReducedSteadyState, hbro2ProcessBRaw,
    k4, k5, bromateConcentration, protonConcentration,
    sourceConcentrations]

theorem hbro2ProcessBRaw_full
    (bromide : MolarConcentration) (hBromide : 0 < bromide) :
    ProcessBSteadyState hbro2ProcessBRaw bromide := by
  unfold ProcessBSteadyState
  refine ⟨hbro2ProcessBRaw_stationary.1, hBromide, ?_⟩
  norm_num [rate4, rate5, hbro2ProcessBRaw, k4, k5,
    bromateConcentration, protonConcentration, sourceConcentrations]
  ring

theorem hbro2ProcessB_unique
    {hbro2 : MolarConcentration}
    (h : ProcessBReducedSteadyState hbro2) :
    hbro2 = hbro2ProcessBRaw := by
  unfold ProcessBReducedSteadyState at h
  rcases h with ⟨_, hrate⟩
  norm_num [k4, k5, bromateConcentration, protonConcentration,
    sourceConcentrations] at hrate
  norm_num [hbro2ProcessBRaw, k4, k5, bromateConcentration,
    protonConcentration, sourceConcentrations]
  linarith

/-- Exact unrounded arithmetic value of the Process A carrier. -/
theorem hbro2ProcessARaw_exact :
    hbro2ProcessARaw = (3 : ℝ) / 500000 := by
  norm_num [hbro2ProcessARaw, k1, k3, bromateConcentration,
    protonConcentration, sourceConcentrations]

/-- Exact unrounded arithmetic value of the Process B carrier. -/
theorem hbro2ProcessBRaw_exact :
    hbro2ProcessBRaw = (63 : ℝ) / 1250000000000 := by
  norm_num [hbro2ProcessBRaw, k4, k5, bromateConcentration,
    protonConcentration, sourceConcentrations]

/-- The combined raw result specification covers both requested outputs, their
governing stationary equations, existence in the full balances, uniqueness,
and exact unrounded values. -/
def RawResultSpec : Prop :=
  ProcessAReducedSteadyState hbro2ProcessARaw ∧
    (∀ ceIII : MolarConcentration, 0 < ceIII →
      ∃ brO2Radical : MolarConcentration,
        ProcessASteadyState hbro2ProcessARaw brO2Radical ceIII) ∧
    (∀ hbro2 : MolarConcentration,
      ProcessAReducedSteadyState hbro2 → hbro2 = hbro2ProcessARaw) ∧
    hbro2ProcessARaw = (3 : ℝ) / 500000 ∧
    ProcessBReducedSteadyState hbro2ProcessBRaw ∧
    (∀ bromide : MolarConcentration, 0 < bromide →
      ProcessBSteadyState hbro2ProcessBRaw bromide) ∧
    (∀ hbro2 : MolarConcentration,
      ProcessBReducedSteadyState hbro2 → hbro2 = hbro2ProcessBRaw) ∧
    hbro2ProcessBRaw = (63 : ℝ) / 1250000000000

theorem rawResultSpec_holds : RawResultSpec := by
  exact
    ⟨hbro2ProcessARaw_stationary,
      hbro2ProcessARaw_realizable,
      fun _ h => hbro2ProcessA_unique h,
      hbro2ProcessARaw_exact,
      hbro2ProcessBRaw_stationary,
      hbro2ProcessBRaw_full,
      fun _ h => hbro2ProcessB_unique h,
      hbro2ProcessBRaw_exact⟩

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"hbro2_process_a","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"6.00e-6","reporting_quantum":"1e-8","raw_declaration":"IChO2026Problems.T2A2.hbro2ProcessARaw","reporting_declaration":"IChO2026Problems.T2A2.hbro2ProcessAReported"}
theorem hbro2ProcessAReported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      hbro2ProcessARaw ((3 : ℝ) / 500000) ((1 : ℝ) / 100000000) := by
  rw [hbro2ProcessARaw_exact]
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨(600 : ℤ), by norm_num⟩, ?_⟩
  norm_num

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"hbro2_process_b","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"5.04e-11","reporting_quantum":"1e-13","raw_declaration":"IChO2026Problems.T2A2.hbro2ProcessBRaw","reporting_declaration":"IChO2026Problems.T2A2.hbro2ProcessBReported"}
theorem hbro2ProcessBReported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      hbro2ProcessBRaw ((63 : ℝ) / 1250000000000)
        ((1 : ℝ) / 10000000000000) := by
  rw [hbro2ProcessBRaw_exact]
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨(504 : ℤ), by norm_num⟩, ?_⟩
  norm_num

/-- The combined reported result uses the predeclared three-significant-figure
policy independently for each requested output. -/
def ReportedResultSpec : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum
      hbro2ProcessARaw ((3 : ℝ) / 500000) ((1 : ℝ) / 100000000) ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      hbro2ProcessBRaw ((63 : ℝ) / 1250000000000)
        ((1 : ℝ) / 10000000000000)

theorem reportedResultSpec_holds : ReportedResultSpec := by
  exact ⟨hbro2ProcessAReported, hbro2ProcessBReported⟩

/-- Payload-bound answer-blind raw result contract. -/
theorem rawResultContract :
    ("4ef50a274c5cf7d543b9b3216975d529b2e28321860c7f1bf54c598ef38073c8" : String) =
        "4ef50a274c5cf7d543b9b3216975d529b2e28321860c7f1bf54c598ef38073c8" ∧
      IChO2026Problems.T2A2.RawResultSpec := by
  exact ⟨rfl, rawResultSpec_holds⟩

/-- Payload-bound answer-blind reported result contract. -/
theorem reportedResultContract :
    ("9e4724a5863a72c3bd1d6855ce3478b0ac8befb778251a5d2c0ee90ebce6091f" : String) =
        "9e4724a5863a72c3bd1d6855ce3478b0ac8befb778251a5d2c0ee90ebce6091f" ∧
      IChO2026Problems.T2A2.ReportedResultSpec := by
  exact ⟨rfl, reportedResultSpec_holds⟩

end
end T2A2
end IChO2026Problems
