import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, theory problem 2, part 5

This file formalizes the source-side kinetic calculation of the period of the
Belousov--Zhabotinsky oscillation.  Concentrations are represented by their
numerical values in molar, rates by their numerical values in molar per second,
and times by their numerical values in seconds.  The dimensional exponents of
all seven printed rate constants are retained explicitly in `RateConstantData`.

The results of parts 2.2 and 2.3 are rederived here from the printed mechanism;
no result from another generated problem file is imported.  The almost
instantaneous return leg in the phase portrait is assigned zero duration only
in the explicitly named contest calculation idealization.  Thus the raw output
below is the slow-leg model period, and no unsupported error bound for the
physical return time is asserted.
-/

namespace IChO2026Problems.IChO2026T2A5

noncomputable section

/-- Chemical species and source-named reagent forms occurring in the bound
problem statement. -/
inductive Species
  | potassiumBromate
  | malonicAcid
  | ceriumIVSulfate
  | sulfuricAcid
  | hbrO2
  | bromate
  | proton
  | bromineDioxideRadical
  | water
  | ceriumIII
  | ceriumIV
  | hbrO
  | bromide
  | bromomalonicAcid
  | carbonDioxide
  deriving DecidableEq, Repr

/-- The mechanism is displayed for a solution.  The phase of carbon dioxide
in the preliminary overall-reaction prompt is not specified there. -/
inductive Phase
  | aqueous
  | unspecified
  deriving DecidableEq, Repr

def speciesPhase : Species → Phase
  | .carbonDioxide => .unspecified
  | _ => .aqueous

/-- The four materials explicitly said to be mixed to initiate the BZ
reaction. -/
def initialReagents : List Species :=
  [.potassiumBromate, .malonicAcid, .ceriumIVSulfate, .sulfuricAcid]

/-- Source-stated redox roles from the preliminary overall-reaction prompt. -/
structure OverallBZRoles where
  oxidizedSubstrate : Species
  oxidationProduct : Species
  reducedSubstrate : Species
  reductionProduct : Species
  catalyst : Species

def overallBZRoles : OverallBZRoles where
  oxidizedSubstrate := .malonicAcid
  oxidationProduct := .carbonDioxide
  reducedSubstrate := .bromate
  reductionProduct := .bromide
  catalyst := .ceriumIV

inductive Process
  | A
  | B
  | C
  deriving DecidableEq, Repr

inductive SolutionColor
  | yellow
  | colorless
  deriving DecidableEq, Repr

/-- Processes A and B alternate, while C remains active in either regime. -/
inductive Regime
  | processA
  | processB
  deriving DecidableEq, Repr

def activeProcesses : Regime → List Process
  | .processA => [.A, .C]
  | .processB => [.B, .C]

def regimeColor : Regime → SolutionColor
  | .processA => .yellow
  | .processB => .colorless

/-- Whether the displayed product list is complete.  Step (7) explicitly has
an unspecified `other products` tail, whose composition and coefficient are
therefore deliberately not invented. -/
inductive ProductDisclosure
  | complete
  | plusUnspecifiedProducts
  deriving DecidableEq, Repr

/-- A printed rate constant.  `molarityExponent = e` and
`secondsExponent = f` mean that the numerical value is quoted in
`M^e s^f`. -/
structure RateConstantData where
  value : ℝ
  molarityExponent : ℤ
  secondsExponent : ℤ

/-- One elementary step of the printed mechanism. -/
structure ElementaryStep where
  number : ℕ
  process : Process
  reactants : List (Species × ℕ)
  products : List (Species × ℕ)
  productDisclosure : ProductDisclosure
  rateConstant : RateConstantData

/- Exact numerical values printed on page T2-2. -/

def k1 : ℝ := 10000
def k2 : ℝ := 62000
def k3 : ℝ := 40000000
def k4 : ℝ := 2000000000
def k5 : ℝ := 21 / 10
def k6 : ℝ := 82 / 10
def k7 : ℝ := 100

def step1 : ElementaryStep where
  number := 1
  process := .A
  reactants := [(.hbrO2, 1), (.bromate, 1), (.proton, 1)]
  products := [(.bromineDioxideRadical, 2), (.water, 1)]
  productDisclosure := .complete
  rateConstant := ⟨k1, -2, -1⟩

def step2 : ElementaryStep where
  number := 2
  process := .A
  reactants := [(.bromineDioxideRadical, 1), (.ceriumIII, 1), (.proton, 1)]
  products := [(.hbrO2, 1), (.ceriumIV, 1)]
  productDisclosure := .complete
  rateConstant := ⟨k2, -2, -1⟩

def step3 : ElementaryStep where
  number := 3
  process := .A
  reactants := [(.hbrO2, 2)]
  products := [(.bromate, 1), (.hbrO, 1), (.proton, 1)]
  productDisclosure := .complete
  rateConstant := ⟨k3, -1, -1⟩

def step4 : ElementaryStep where
  number := 4
  process := .B
  reactants := [(.hbrO2, 1), (.bromide, 1), (.proton, 1)]
  products := [(.hbrO, 2)]
  productDisclosure := .complete
  rateConstant := ⟨k4, -2, -1⟩

def step5 : ElementaryStep where
  number := 5
  process := .B
  reactants := [(.bromate, 1), (.bromide, 1), (.proton, 2)]
  products := [(.hbrO, 1), (.hbrO2, 1)]
  productDisclosure := .complete
  rateConstant := ⟨k5, -3, -1⟩

def step6 : ElementaryStep where
  number := 6
  process := .B
  reactants := [(.hbrO, 1), (.malonicAcid, 1)]
  products := [(.bromomalonicAcid, 1), (.water, 1)]
  productDisclosure := .complete
  rateConstant := ⟨k6, -1, -1⟩

def step7 : ElementaryStep where
  number := 7
  process := .C
  reactants := [(.ceriumIV, 1), (.bromomalonicAcid, 1)]
  products := [(.ceriumIII, 1), (.bromide, 1)]
  productDisclosure := .plusUnspecifiedProducts
  rateConstant := ⟨k7, -1, -1⟩

def mechanism : List ElementaryStep :=
  [step1, step2, step3, step4, step5, step6, step7]

/-- Total mass-action order obtained from the displayed reactant
stoichiometry. -/
def massActionOrder (s : ElementaryStep) : ℕ :=
  (s.reactants.map Prod.snd).sum

/-- The printed units have exponent `1 - order` in molarity and exponent `-1`
in seconds for every elementary rate constant. -/
def RateConstantUnitsMatch (s : ElementaryStep) : Prop :=
  s.rateConstant.molarityExponent = 1 - (massActionOrder s : ℤ) ∧
    s.rateConstant.secondsExponent = -1

theorem printed_rate_constant_units_match :
    ∀ s ∈ mechanism, RateConstantUnitsMatch s := by
  intro s hs
  simp only [mechanism, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [RateConstantUnitsMatch, massActionOrder, step1, step2, step3,
      step4, step5, step6, step7]

/-- A concentration profile gives numerical molar concentrations while
retaining the species index. -/
abbrev ConcentrationProfile := Species → ℝ

/-- Generic mass-action rate (numerical value in M s⁻¹) for a displayed
elementary step. -/
def massActionRate (s : ElementaryStep) (c : ConcentrationProfile) : ℝ :=
  s.rateConstant.value *
    (s.reactants.map (fun term => c term.1 ^ term.2)).prod

/- Exact concentrations printed on pages T2-2 and T2-3, in M. -/

def bromateConcentration : ℝ := 3 / 50
def malonicAcidConcentration : ℝ := 1 / 10
def protonConcentration : ℝ := 4 / 5
def initialCeriumIVConcentration : ℝ := 1 / 1000
def maximumBromideConcentration : ℝ := 7 / 10000

/-- Time-dependent profiles satisfying the source statement that bromate,
malonic-acid, and proton concentrations are maintained throughout the
reaction.  Cerium(IV) and the oscillating intermediates are intentionally not
fixed by this predicate. -/
def MaintainedReactantConcentrations
    (concentration : ℝ → ConcentrationProfile) : Prop :=
  ∀ t : ℝ,
    concentration t .bromate = bromateConcentration ∧
      concentration t .malonicAcid = malonicAcidConcentration ∧
      concentration t .proton = protonConcentration

theorem printed_concentrations_positive :
    0 < bromateConcentration ∧
      0 < malonicAcidConcentration ∧
      0 < protonConcentration ∧
      0 < initialCeriumIVConcentration ∧
      0 < maximumBromideConcentration := by
  norm_num [bromateConcentration, malonicAcidConcentration,
    protonConcentration, initialCeriumIVConcentration,
    maximumBromideConcentration]

/- Named elementary rates used in the steady-state and period calculation.
Each argument is the molar concentration of the species named in its binder. -/

def rate1 (hbrO2 : ℝ) : ℝ :=
  k1 * hbrO2 * bromateConcentration * protonConcentration

def rate2 (brO2Radical ceriumIII : ℝ) : ℝ :=
  k2 * brO2Radical * ceriumIII * protonConcentration

def rate3 (hbrO2 : ℝ) : ℝ :=
  k3 * hbrO2 ^ 2

def rate4 (hbrO2 bromide : ℝ) : ℝ :=
  k4 * hbrO2 * bromide * protonConcentration

def rate5 (bromide : ℝ) : ℝ :=
  k5 * bromateConcentration * bromide * protonConcentration ^ 2

def rate6 (hbrO malonicAcid : ℝ) : ℝ :=
  k6 * hbrO * malonicAcid

def rate6AtSourceConditions (hbrO : ℝ) : ℝ :=
  rate6 hbrO malonicAcidConcentration

def rate7 (ceriumIV bromomalonicAcid : ℝ) : ℝ :=
  k7 * ceriumIV * bromomalonicAcid

/-- Full steady-state equations for the two intermediates used in Process A.
Step (1) produces two BrO₂ radicals; step (2) consumes one. -/
def ProcessASteadyState
    (hbrO2 brO2Radical ceriumIII : ℝ) : Prop :=
  0 < hbrO2 ∧ 0 ≤ brO2Radical ∧ 0 ≤ ceriumIII ∧
    2 * rate1 hbrO2 = rate2 brO2Radical ceriumIII ∧
    -rate1 hbrO2 + rate2 brO2Radical ceriumIII - 2 * rate3 hbrO2 = 0

/-- Reduced HBrO₂ steady-state equation after eliminating the BrO₂ radical
rate from Process A. -/
def ProcessAReducedSteadyState (hbrO2 : ℝ) : Prop :=
  0 < hbrO2 ∧ rate1 hbrO2 = 2 * rate3 hbrO2

theorem processA_full_ssa_implies_reduced
    {hbrO2 brO2Radical ceriumIII : ℝ}
    (h : ProcessASteadyState hbrO2 brO2Radical ceriumIII) :
    ProcessAReducedSteadyState hbrO2 := by
  rcases h with ⟨hhbrO2, _, _, hradical, hhbrO2ss⟩
  constructor
  · exact hhbrO2
  · linarith

/-- Source-derived candidate for `[HBrO₂]A`, in M. -/
def stationaryHBrO2A : ℝ :=
  k1 * bromateConcentration * protonConcentration / (2 * k3)

/-- In Process B, production of one HBrO₂ molecule in step (5) balances its
consumption in step (4). -/
def ProcessBSteadyState (hbrO2 bromide : ℝ) : Prop :=
  0 < hbrO2 ∧ 0 < bromide ∧ rate4 hbrO2 bromide = rate5 bromide

/-- Source-derived candidate for `[HBrO₂]B`, in M. -/
def stationaryHBrO2B : ℝ :=
  k5 * bromateConcentration * protonConcentration / k4

/-- The complete locally derived result required from part 2.2.  It validates
both candidates against the appropriate steady-state balance and states their
uniqueness under the displayed positive-concentration conditions. -/
def PreviousA2Result : Prop :=
  ProcessAReducedSteadyState stationaryHBrO2A ∧
    (∀ x : ℝ, ProcessAReducedSteadyState x → x = stationaryHBrO2A) ∧
    (∀ bromide : ℝ, 0 < bromide →
      ProcessBSteadyState stationaryHBrO2B bromide) ∧
    (∀ x bromide : ℝ, ProcessBSteadyState x bromide →
      x = stationaryHBrO2B)

theorem previous_a2_derived : PreviousA2Result := by
  constructor
  · constructor
    · norm_num [stationaryHBrO2A, k1, bromateConcentration,
        protonConcentration, k3]
    · norm_num [stationaryHBrO2A, rate1, rate3, k1,
        bromateConcentration, protonConcentration, k3]
  constructor
  · intro x hx
    rcases hx with ⟨hxpos, hxrate⟩
    dsimp [rate1, rate3, k1, bromateConcentration,
      protonConcentration, k3] at hxrate
    dsimp [stationaryHBrO2A, k1, bromateConcentration,
      protonConcentration, k3]
    nlinarith
  constructor
  · intro bromide hbromide
    constructor
    · norm_num [stationaryHBrO2B, k5, bromateConcentration,
        protonConcentration, k4]
    constructor
    · exact hbromide
    · norm_num [rate4, rate5, stationaryHBrO2B, k4, k5,
        bromateConcentration, protonConcentration]
      ring
  · intro x bromide hx
    rcases hx with ⟨hxpos, hbromide, hxrate⟩
    dsimp [rate4, rate5, k4, k5, bromateConcentration,
      protonConcentration] at hxrate
    dsimp [stationaryHBrO2B, k5, bromateConcentration,
      protonConcentration, k4]
    nlinarith

theorem stationary_hbrO2_values :
    stationaryHBrO2A = (3 : ℝ) / 500000 ∧
      stationaryHBrO2B = (63 : ℝ) / 1250000000000 := by
  norm_num [stationaryHBrO2A, stationaryHBrO2B, k1, k3, k4, k5,
    bromateConcentration, protonConcentration]

/-- At the switch boundary, rates (1) and (4) are equal for any positive
HBrO₂ concentration. -/
def CriticalBromideSpec (bromide : ℝ) : Prop :=
  0 < bromide ∧
    ∀ hbrO2 : ℝ, 0 < hbrO2 → rate4 hbrO2 bromide = rate1 hbrO2

/-- Source-derived candidate for the critical bromide concentration, in M. -/
def criticalBromideConcentration : ℝ :=
  k1 * bromateConcentration / k4

/-- The complete locally derived result required from part 2.3. -/
def PreviousA3Result : Prop :=
  CriticalBromideSpec criticalBromideConcentration ∧
    ∀ bromide : ℝ, CriticalBromideSpec bromide →
      bromide = criticalBromideConcentration

theorem previous_a3_derived : PreviousA3Result := by
  constructor
  · constructor
    · norm_num [criticalBromideConcentration, k1,
        bromateConcentration, k4]
    · intro hbrO2 _
      norm_num [criticalBromideConcentration, rate4, rate1, k1, k4,
        bromateConcentration, protonConcentration]
      ring
  · intro bromide hbromide
    rcases hbromide with ⟨_, hrates⟩
    have hone := hrates 1 (by norm_num)
    dsimp [rate4, rate1, k1, k4, bromateConcentration,
      protonConcentration] at hone
    dsimp [criticalBromideConcentration, k1, bromateConcentration, k4]
    linarith

theorem critical_bromide_value :
    criticalBromideConcentration = (3 : ℝ) / 10000000 := by
  norm_num [criticalBromideConcentration, k1, bromateConcentration, k4]

/-- In the slow Process-B leg, steps (4) and (5) each consume one bromide ion. -/
def combinedBromideConsumptionRate (bromide : ℝ) : ℝ :=
  rate4 stationaryHBrO2B bromide + rate5 bromide

/-- First-order coefficient, in s⁻¹, of bromide disappearance.  The leading
factor two records the two independently consumed bromide ions. -/
def bromideDecayCoefficient : ℝ :=
  2 * k5 * bromateConcentration * protonConcentration ^ 2

theorem bromide_decay_coefficient_value :
    bromideDecayCoefficient = (504 : ℝ) / 3125 := by
  norm_num [bromideDecayCoefficient, k5, bromateConcentration,
    protonConcentration]

/-- Mechanistic balance reducing the sum of the step-(4) and step-(5) rates to
the first-order bromide disappearance law. -/
def ProcessBBromideBalance : Prop :=
  ∀ bromide : ℝ, 0 ≤ bromide →
    combinedBromideConsumptionRate bromide =
      bromideDecayCoefficient * bromide

theorem processB_bromide_balance : ProcessBBromideBalance := by
  intro bromide _
  norm_num [combinedBromideConsumptionRate, rate4, rate5,
    stationaryHBrO2B, bromideDecayCoefficient, k4, k5,
    bromateConcentration, protonConcentration]
  ring

/-- Bromide concentration along the slow leg, starting at the printed maximum
concentration. -/
noncomputable def bromideSlowLeg (t : ℝ) : ℝ :=
  maximumBromideConcentration * Real.exp (-bromideDecayCoefficient * t)

/-- ODE, initial value, positivity, and direction of the source-described slow
leg. -/
def BromideSlowLegSpec (bromide : ℝ → ℝ) : Prop :=
  bromide 0 = maximumBromideConcentration ∧
    (∀ t : ℝ, HasDerivAt bromide
      (-combinedBromideConsumptionRate (bromide t)) t) ∧
    (∀ t : ℝ, 0 ≤ t → 0 < bromide t) ∧
    StrictAntiOn bromide (Set.Ici (0 : ℝ))

theorem bromide_slow_leg_kinetics :
    BromideSlowLegSpec bromideSlowLeg := by
  constructor
  · simp [bromideSlowLeg, maximumBromideConcentration]
  constructor
  · intro t
    have hbromide : 0 < bromideSlowLeg t := by
      exact mul_pos (by norm_num [bromideSlowLeg,
        maximumBromideConcentration]) (Real.exp_pos _)
    rw [processB_bromide_balance (bromideSlowLeg t) hbromide.le]
    change HasDerivAt
      (fun u : ℝ => maximumBromideConcentration *
        Real.exp (-bromideDecayCoefficient * u))
      (-(bromideDecayCoefficient *
        (maximumBromideConcentration *
          Real.exp (-bromideDecayCoefficient * t)))) t
    have hlinear : HasDerivAt
        (fun u : ℝ => -bromideDecayCoefficient * u)
        (-bromideDecayCoefficient) t := by
      simpa using (hasDerivAt_id t).const_mul (-bromideDecayCoefficient)
    have hexponential : HasDerivAt
        (fun u : ℝ => Real.exp (-bromideDecayCoefficient * u))
        (Real.exp (-bromideDecayCoefficient * t) *
          (-bromideDecayCoefficient)) t :=
      (Real.hasDerivAt_exp _).comp t hlinear
    exact (hexponential.const_mul maximumBromideConcentration).congr_deriv
      (by ring)
  constructor
  · intro t _
    exact mul_pos (by norm_num [bromideSlowLeg,
      maximumBromideConcentration]) (Real.exp_pos _)
  · intro x _ y _ hxy
    unfold bromideSlowLeg
    apply mul_lt_mul_of_pos_left _ (by
      norm_num [maximumBromideConcentration])
    rw [Real.exp_lt_exp]
    have hcoeff : 0 < bromideDecayCoefficient := by
      rw [bromide_decay_coefficient_value]
      norm_num
    nlinarith

/-- A duration reaches the critical concentration for the first time along the
slow leg. -/
def SlowLegDurationSpec (duration : ℝ) : Prop :=
  0 ≤ duration ∧
    bromideSlowLeg duration = criticalBromideConcentration ∧
    ∀ t : ℝ, 0 ≤ t → t < duration →
      criticalBromideConcentration < bromideSlowLeg t

/-- Exact, unrounded source-derived duration in seconds. -/
noncomputable def oscillationPeriodRaw : ℝ :=
  Real.log
      (maximumBromideConcentration / criticalBromideConcentration) /
    bromideDecayCoefficient

/-- Positivity and ordering conditions required by the logarithm, division,
and first-crossing calculation. -/
def OscillationPeriodDomainConditions : Prop :=
  0 < criticalBromideConcentration ∧
    criticalBromideConcentration < maximumBromideConcentration ∧
    0 < bromideDecayCoefficient

theorem oscillation_period_domain_conditions :
    OscillationPeriodDomainConditions := by
  rw [OscillationPeriodDomainConditions, critical_bromide_value,
    bromide_decay_coefficient_value]
  norm_num [maximumBromideConcentration]

theorem oscillation_period_exact_formula :
    oscillationPeriodRaw =
      (3125 : ℝ) / 504 * Real.log ((7000 : ℝ) / 3) := by
  rw [oscillationPeriodRaw, critical_bromide_value,
    bromide_decay_coefficient_value]
  norm_num [maximumBromideConcentration]
  ring

/-- The exact logarithmic candidate is the first time at which the positive
slow-leg trajectory reaches the independently derived switching threshold. -/
theorem oscillation_period_slow_leg_duration :
    SlowLegDurationSpec oscillationPeriodRaw := by
  rcases oscillation_period_domain_conditions with ⟨hcritical, horder, hdecay⟩
  have hmaximum : 0 < maximumBromideConcentration := hcritical.trans horder
  have hratio : 1 <
      maximumBromideConcentration / criticalBromideConcentration := by
    exact (lt_div_iff₀ hcritical).2 (by simpa using horder)
  have hduration : 0 ≤ oscillationPeriodRaw := by
    exact (div_pos (Real.log_pos hratio) hdecay).le
  have hreach :
      bromideSlowLeg oscillationPeriodRaw = criticalBromideConcentration := by
    rw [bromideSlowLeg, oscillationPeriodRaw]
    have hdecay_ne : bromideDecayCoefficient ≠ 0 := ne_of_gt hdecay
    have hexponent :
        -bromideDecayCoefficient *
            (Real.log
              (maximumBromideConcentration / criticalBromideConcentration) /
              bromideDecayCoefficient) =
          -Real.log
            (maximumBromideConcentration / criticalBromideConcentration) := by
      field_simp
    rw [hexponent, Real.exp_neg,
      Real.exp_log (div_pos hmaximum hcritical)]
    field_simp
  refine ⟨hduration, hreach, ?_⟩
  intro t ht hlt
  have hanti := bromide_slow_leg_kinetics.2.2.2
  calc
    criticalBromideConcentration = bromideSlowLeg oscillationPeriodRaw :=
      hreach.symm
    _ < bromideSlowLeg t := hanti ht hduration hlt

/-- The phase-portrait instruction says that the return to the maximum is
almost immediate.  The requested contest calculation therefore idealizes its
duration as zero, without asserting any numerical physical-error bound. -/
def NegligibleReturnCycleSpec (period slowLegDuration : ℝ) : Prop :=
  0 ≤ slowLegDuration ∧ period = slowLegDuration + 0

/-- Problem-specific derivation specification for the requested raw result.
It includes the independently rederived A2 and A3 prerequisites, the
mechanistic bromide balance, the ODE solution, its first critical crossing, and
the explicitly named negligible-return timing idealization. -/
def OscillationPeriodDerivation : Prop :=
  PreviousA2Result ∧
    PreviousA3Result ∧
    OscillationPeriodDomainConditions ∧
    ProcessBBromideBalance ∧
    BromideSlowLegSpec bromideSlowLeg ∧
    SlowLegDurationSpec oscillationPeriodRaw ∧
    NegligibleReturnCycleSpec oscillationPeriodRaw oscillationPeriodRaw

/-- A rational Taylor enclosure for the exponential proves the lower decimal
bound needed below.  Splitting the exponent into eight equal pieces keeps the
Taylor argument in `[0,1]`; no floating-point evaluation is used. -/
lemma log_ratio_lower_bound :
    (48084 : ℝ) / 1000 * ((504 : ℝ) / 3125) <
      Real.log ((7000 : ℝ) / 3) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 7000 / 3)]
  let x : ℝ :=
    ((48084 : ℝ) / 1000 * ((504 : ℝ) / 3125)) / 8
  have hxnonneg : 0 ≤ x := by norm_num [x]
  have hxone : x ≤ 1 := by norm_num [x]
  have hsplit :
      (48084 : ℝ) / 1000 * ((504 : ℝ) / 3125) = (8 : ℕ) * x := by
    norm_num [x]
  rw [hsplit, Real.exp_nat_mul]
  let upper : ℝ :=
    (∑ m ∈ Finset.range 8, x ^ m / m.factorial) +
      x ^ 8 * (8 + 1) / ((Nat.factorial 8 : ℝ) * 8)
  have hexp : Real.exp x ≤ upper := by
    exact Real.exp_bound' hxnonneg hxone (by norm_num : 0 < (8 : ℕ))
  calc
    Real.exp x ^ 8 ≤ upper ^ 8 :=
      pow_le_pow_left₀ (Real.exp_pos x).le hexp 8
    _ < (7000 : ℝ) / 3 := by
      norm_num [upper, x, Finset.sum_range_succ, Nat.factorial]

/-- The matching lower Taylor polynomial proves the upper decimal bound for
the logarithm, again entirely over exact rationals. -/
lemma log_ratio_upper_bound :
    Real.log ((7000 : ℝ) / 3) <
      (48085 : ℝ) / 1000 * ((504 : ℝ) / 3125) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 7000 / 3)]
  let x : ℝ :=
    ((48085 : ℝ) / 1000 * ((504 : ℝ) / 3125)) / 8
  have hxnonneg : 0 ≤ x := by norm_num [x]
  have hsplit :
      (48085 : ℝ) / 1000 * ((504 : ℝ) / 3125) = (8 : ℕ) * x := by
    norm_num [x]
  rw [hsplit, Real.exp_nat_mul]
  let lower : ℝ := ∑ m ∈ Finset.range 8, x ^ m / m.factorial
  have hexp : lower ≤ Real.exp x := by
    exact Real.sum_le_exp_of_nonneg hxnonneg 8
  calc
    (7000 : ℝ) / 3 < lower ^ 8 := by
      norm_num [lower, x, Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp x ^ 8 := by
      apply pow_le_pow_left₀
      · norm_num [lower, x, Finset.sum_range_succ, Nat.factorial]
      · exact hexp

/-- Raw answer-blind result and its certified nondegenerate interval.  The
candidate artifact separately certifies that the rational endpoints are
distinct; this theorem has exactly the pipeline-generated numeric raw-result
contract type. -/
theorem oscillationPeriod_raw_result :
    OscillationPeriodDerivation ∧
      (12021 : ℝ) / 250 ≤ oscillationPeriodRaw ∧
      oscillationPeriodRaw ≤ (9617 : ℝ) / 200 := by
  constructor
  · exact ⟨previous_a2_derived, previous_a3_derived,
      oscillation_period_domain_conditions, processB_bromide_balance,
      bromide_slow_leg_kinetics, oscillation_period_slow_leg_duration,
      oscillation_period_slow_leg_duration.1, by simp⟩
  constructor
  · rw [oscillation_period_exact_formula]
    nlinarith [log_ratio_lower_bound]
  · rw [oscillation_period_exact_formula]
    nlinarith [log_ratio_upper_bound]

/-- Three-significant-figure display selected by the source report.  Since the
result lies in the tens decade, its reporting quantum is `0.1 s`. -/
def oscillationPeriodReported : ℝ := 481 / 10

def oscillationPeriodReportingQuantum : ℝ := 1 / 10

/-- Machine-checkable half-away-from-zero reporting certificate. -/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"oscillation_period","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"48.1","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.IChO2026T2A5.oscillationPeriodRaw","reporting_declaration":"IChO2026Problems.IChO2026T2A5.oscillationPeriod_reported_result"}
theorem oscillationPeriod_reported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      oscillationPeriodRaw
      ((481 : ℝ) / 10)
      ((1 : ℝ) / 10) := by
  have hbounds := oscillationPeriod_raw_result.2
  have hrawnonneg : 0 ≤ oscillationPeriodRaw := by
    linarith [hbounds.1]
  refine ⟨?_, ?_, ?_⟩
  · norm_num [oscillationPeriodReportingQuantum]
  · refine ⟨(481 : ℤ), ?_⟩
    norm_num [oscillationPeriodReported, oscillationPeriodReportingQuantum]
  · rw [if_pos hrawnonneg]
    constructor
    · norm_num [oscillationPeriodReported,
        oscillationPeriodReportingQuantum]
      linarith [hbounds.1]
    · norm_num [oscillationPeriodReported,
        oscillationPeriodReportingQuantum]
      linarith [hbounds.2]

end

end IChO2026Problems.IChO2026T2A5
