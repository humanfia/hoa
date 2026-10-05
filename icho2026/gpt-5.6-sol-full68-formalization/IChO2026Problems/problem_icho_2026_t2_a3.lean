import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem T2-A3

This file formalizes the critical bromide concentration in the
Belousov--Zhabotinsky mechanism printed in the problem.  All numerical values
are represented in the source's molar (`mol dm⁻³`) and second unit scale.

Assumptions/source data: the seven printed elementary reactions, their printed
mass-action constants, the maintained bromate and proton concentrations, and
the statement that the A/B switch occurs when the rates of steps 1 and 4 cross.

Target: characterize the unique nonnegative bromide concentration at which
those two rates agree, retain the direction of both strict rate comparisons,
and certify the project-mandated three-significant-figure report.
-/

namespace IChO2026Problems
namespace T2A3

noncomputable section

/-- Numerical concentrations are expressed in `mol dm⁻³` (the `M` used in the
problem), and numerical rates are expressed in `mol dm⁻³ s⁻¹`. -/
abbrev MolarConcentration := ℝ
abbrev MolarRate := ℝ

/-- Every chemically identified species explicitly occurring in the seven-step
source mechanism. -/
inductive BZSpecies where
  | hBrO2
  | bromate
  | proton
  | bromineDioxideRadical
  | water
  | ceriumIII
  | ceriumIV
  | hBrO
  | bromide
  | malonicAcid
  | bromomalonicAcid
  deriving DecidableEq, Fintype, Repr

/-- The seven elementary steps, in the source order. -/
inductive BZStep where
  | step1 | step2 | step3 | step4 | step5 | step6 | step7
  deriving DecidableEq, Fintype, Repr

/-- Whether the source exhaustively names the products of an elementary step.
This avoids assigning a fictitious formula or stoichiometric coefficient to
the literal “other products” in step 7. -/
inductive ProductSpecification where
  | complete
  | includesOtherUnspecifiedProducts
  deriving DecidableEq, Repr

def sourceProductSpecification : BZStep → ProductSpecification
  | .step7 => .includesOtherUnspecifiedProducts
  | _ => .complete

/-- The three named processes grouping the elementary steps. -/
inductive BZProcess where
  | A | B | C
  deriving DecidableEq, Fintype, Repr

/-- The two source-observed colours used to identify Processes A and B. -/
inductive SolutionColour where
  | yellow | colourless
  deriving DecidableEq, Fintype, Repr

/-- Source grouping: steps 1--3 form A, 4--6 form B, and step 7 forms C. -/
def processOfStep : BZStep → BZProcess
  | .step1 | .step2 | .step3 => .A
  | .step4 | .step5 | .step6 => .B
  | .step7 => .C

/-- Process C is source-stated to occur continuously. -/
def continuouslyActiveProcess : BZProcess := .C

/-- Processes A and B are the source-stated alternating pair. -/
def alternatingProcesses : BZProcess × BZProcess := (.A, .B)

/-- Source colour convention.  Process C is continuous rather than a separate
colour phase, so the statement assigns it no phase colour. -/
def processColour : BZProcess → Option SolutionColour
  | .A => some .yellow
  | .B => some .colourless
  | .C => none

/-- Formal charges printed or fixed by the explicit species notation. -/
def sourceCharge : BZSpecies → ℤ
  | .hBrO2 => 0
  | .bromate => -1
  | .proton => 1
  | .bromineDioxideRadical => 0
  | .water => 0
  | .ceriumIII => 3
  | .ceriumIV => 4
  | .hBrO => 0
  | .bromide => -1
  | .malonicAcid => 0
  | .bromomalonicAcid => 0

/-- The molecular formulas explicitly described by `MA = CH₂(COOH)₂` and
`BMA = CHBr(COOH)₂`. -/
structure CHBrOFormula where
  carbon : ℕ
  hydrogen : ℕ
  bromine : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

def malonicAcidFormula : CHBrOFormula := ⟨3, 4, 0, 4⟩
def bromomalonicAcidFormula : CHBrOFormula := ⟨3, 3, 1, 4⟩

/-- A compact constructor for source stoichiometric complexes. -/
def complexOf (terms : List (BZSpecies × ℕ)) : CRNT.Complex BZSpecies :=
  fun species =>
    terms.foldr
      (fun term total => (if term.1 = species then term.2 else 0) + total)
      0

/-- The known stoichiometric portion of every source reaction.  For step 7 it
must be read together with `sourceProductSpecification`, which records the
additional unnamed products without turning them into a material species. -/
def sourceReaction : BZStep → CRNT.Reaction BZSpecies
  | .step1 =>
      { source := complexOf [(.hBrO2, 1), (.bromate, 1), (.proton, 1)]
        target := complexOf [(.bromineDioxideRadical, 2), (.water, 1)] }
  | .step2 =>
      { source :=
          complexOf [(.bromineDioxideRadical, 1), (.ceriumIII, 1), (.proton, 1)]
        target := complexOf [(.hBrO2, 1), (.ceriumIV, 1)] }
  | .step3 =>
      { source := complexOf [(.hBrO2, 2)]
        target := complexOf [(.bromate, 1), (.hBrO, 1), (.proton, 1)] }
  | .step4 =>
      { source := complexOf [(.hBrO2, 1), (.bromide, 1), (.proton, 1)]
        target := complexOf [(.hBrO, 2)] }
  | .step5 =>
      { source := complexOf [(.bromate, 1), (.bromide, 1), (.proton, 2)]
        target := complexOf [(.hBrO, 1), (.hBrO2, 1)] }
  | .step6 =>
      { source := complexOf [(.hBrO, 1), (.malonicAcid, 1)]
        target := complexOf [(.bromomalonicAcid, 1), (.water, 1)] }
  | .step7 =>
      { source := complexOf [(.ceriumIV, 1), (.bromomalonicAcid, 1)]
        target := complexOf [(.ceriumIII, 1), (.bromide, 1)] }

/-- Numerical values of `k₁,...,k₇`, exactly as printed. -/
def sourceRateConstant : BZStep → ℝ
  | .step1 => 10000
  | .step2 => 62000
  | .step3 => 40000000
  | .step4 => 2000000000
  | .step5 => 21 / 10
  | .step6 => 82 / 10
  | .step7 => 100

/-- Unit exponents for a printed rate constant: `M^molarityExponent ·
s^secondsExponent`. -/
structure RateConstantUnit where
  molarityExponent : ℤ
  secondsExponent : ℤ
  deriving DecidableEq, Repr

/-- The source prints `M⁻² s⁻¹` for steps 1, 2, and 4; `M⁻³ s⁻¹` for step 5;
and `M⁻¹ s⁻¹` for steps 3, 6, and 7. -/
def sourceRateConstantUnit : BZStep → RateConstantUnit
  | .step1 | .step2 | .step4 => ⟨-2, -1⟩
  | .step5 => ⟨-3, -1⟩
  | .step3 | .step6 | .step7 => ⟨-1, -1⟩

theorem sourceRateConstant_pos (step : BZStep) :
    0 < sourceRateConstant step := by
  cases step <;> norm_num [sourceRateConstant]

/- Source-stipulated concentrations, exact as printed. -/
def bromateConcentration : MolarConcentration := 6 / 100
def malonicAcidConcentration : MolarConcentration := 1 / 10
def protonConcentration : MolarConcentration := 8 / 10
def initialCeriumIVConcentration : MolarConcentration := 1 / 1000

/- Printed fallbacks are recorded for provenance only.  They are not used in
the raw derivation below. -/
def printedFallbackHBrO2A : MolarConcentration := 1 / 100000
def printedFallbackHBrO2B : MolarConcentration := 1 / 10000000000
def printedFallbackCriticalForLaterParts : MolarConcentration := 1 / 10000000

/- Explicit mass-action formulas for all seven source steps. -/
def step1Rate (hBrO2 bromate proton : MolarConcentration) : MolarRate :=
  sourceRateConstant .step1 * hBrO2 * bromate * proton

def step2Rate (radical ceriumIII proton : MolarConcentration) : MolarRate :=
  sourceRateConstant .step2 * radical * ceriumIII * proton

def step3Rate (hBrO2 : MolarConcentration) : MolarRate :=
  sourceRateConstant .step3 * hBrO2 ^ 2

def step4Rate (hBrO2 bromide proton : MolarConcentration) : MolarRate :=
  sourceRateConstant .step4 * hBrO2 * bromide * proton

def step5Rate (bromate bromide proton : MolarConcentration) : MolarRate :=
  sourceRateConstant .step5 * bromate * bromide * proton ^ 2

def step6Rate (hBrO malonicAcid : MolarConcentration) : MolarRate :=
  sourceRateConstant .step6 * hBrO * malonicAcid

def step7Rate (ceriumIV bromomalonicAcid : MolarConcentration) : MolarRate :=
  sourceRateConstant .step7 * ceriumIV * bromomalonicAcid

/-- The source-written formulas, assembled uniformly from a concentration
vector. -/
def sourceRateFormula (step : BZStep)
    (x : BZSpecies → MolarConcentration) : MolarRate :=
  match step with
  | .step1 => step1Rate (x .hBrO2) (x .bromate) (x .proton)
  | .step2 => step2Rate (x .bromineDioxideRadical) (x .ceriumIII) (x .proton)
  | .step3 => step3Rate (x .hBrO2)
  | .step4 => step4Rate (x .hBrO2) (x .bromide) (x .proton)
  | .step5 => step5Rate (x .bromate) (x .bromide) (x .proton)
  | .step6 => step6Rate (x .hBrO) (x .malonicAcid)
  | .step7 => step7Rate (x .ceriumIV) (x .bromomalonicAcid)

/-- The local source-rate interface retains the standard mass-action
nonnegativity property for all seven source reactions. -/
theorem sourceRateFormula_nonnegative (step : BZStep)
    (x : BZSpecies → MolarConcentration)
    (hx : ∀ species : BZSpecies, 0 ≤ x species) :
    0 ≤ sourceRateFormula step x := by
  have hhBrO2 : 0 ≤ x .hBrO2 := hx .hBrO2
  have hbromate : 0 ≤ x .bromate := hx .bromate
  have hproton : 0 ≤ x .proton := hx .proton
  have hradical : 0 ≤ x .bromineDioxideRadical := hx .bromineDioxideRadical
  have hceriumIII : 0 ≤ x .ceriumIII := hx .ceriumIII
  have hhBrO : 0 ≤ x .hBrO := hx .hBrO
  have hbromide : 0 ≤ x .bromide := hx .bromide
  have hmalonicAcid : 0 ≤ x .malonicAcid := hx .malonicAcid
  have hceriumIV : 0 ≤ x .ceriumIV := hx .ceriumIV
  have hbromomalonicAcid : 0 ≤ x .bromomalonicAcid := hx .bromomalonicAcid
  cases step <;>
    simp only [sourceRateFormula, step1Rate, step2Rate, step3Rate, step4Rate,
      step5Rate, step6Rate, step7Rate, sourceRateConstant] <;>
    positivity

/-! ## Inline derivation of the previous part (T2-A2) -/

/-- Full Process-A steady-state equations for the BrO₂ radical and HBrO₂.
The coefficient two in each balance comes from the printed stoichiometry of
steps 1 and 3. -/
def ProcessAFullSteadyState
    (hBrO2 radical ceriumIII : MolarConcentration) : Prop :=
  0 < hBrO2 ∧ 0 < radical ∧ 0 < ceriumIII ∧
  step2Rate radical ceriumIII protonConcentration =
    2 * step1Rate hBrO2 bromateConcentration protonConcentration ∧
  -step1Rate hBrO2 bromateConcentration protonConcentration +
      step2Rate radical ceriumIII protonConcentration -
      2 * step3Rate hBrO2 = 0

/-- Eliminating the steady-state radical balance gives the HBrO₂ balance used
to calculate the Process-A stationary concentration. -/
def ProcessAReducedSteadyState (hBrO2 : MolarConcentration) : Prop :=
  0 < hBrO2 ∧
  step1Rate hBrO2 bromateConcentration protonConcentration =
    2 * step3Rate hBrO2

theorem processA_full_implies_reduced
    {hBrO2 radical ceriumIII : MolarConcentration}
    (h : ProcessAFullSteadyState hBrO2 radical ceriumIII) :
    ProcessAReducedSteadyState hBrO2 := by
  rcases h with ⟨hhBrO2, _, _, hradical, hHBrO2⟩
  refine ⟨hhBrO2, ?_⟩
  linarith

/-- The Process-B HBrO₂ steady-state balance: step 5 forms one HBrO₂ and
step 4 consumes one.  Bromide is required to be positive before cancellation. -/
def ProcessBSteadyState
    (hBrO2 bromide : MolarConcentration) : Prop :=
  0 < hBrO2 ∧ 0 < bromide ∧
  step5Rate bromateConcentration bromide protonConcentration =
    step4Rate hBrO2 bromide protonConcentration

/-- Source-derived, unrounded Process-A stationary concentration. -/
def stationaryHBrO2A : MolarConcentration :=
  sourceRateConstant .step1 * bromateConcentration * protonConcentration /
    (2 * sourceRateConstant .step3)

/-- Source-derived, unrounded Process-B stationary concentration. -/
def stationaryHBrO2B : MolarConcentration :=
  sourceRateConstant .step5 * bromateConcentration * protonConcentration /
    sourceRateConstant .step4

/-- The whole previous-part obligation is rederived from source constants;
neither printed fallback is assumed. -/
def PreviousPartInlineDerivation : Prop :=
  ProcessAReducedSteadyState stationaryHBrO2A ∧
  (∀ hBrO2 : MolarConcentration,
    ProcessAReducedSteadyState hBrO2 → hBrO2 = stationaryHBrO2A) ∧
  (∀ bromide : MolarConcentration, 0 < bromide →
    ProcessBSteadyState stationaryHBrO2B bromide) ∧
  (∀ hBrO2 bromide : MolarConcentration,
    ProcessBSteadyState hBrO2 bromide → hBrO2 = stationaryHBrO2B)

theorem previousPart_inline_derivation : PreviousPartInlineDerivation := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [ProcessAReducedSteadyState, stationaryHBrO2A, step1Rate,
      step3Rate, sourceRateConstant, bromateConcentration, protonConcentration]
  · intro hBrO2 hsteady
    rcases hsteady with ⟨hpos, hbalance⟩
    norm_num [step1Rate, step3Rate, sourceRateConstant, bromateConcentration,
      protonConcentration] at hbalance
    norm_num [stationaryHBrO2A, sourceRateConstant, bromateConcentration,
      protonConcentration]
    nlinarith
  · intro bromide hbromide
    refine ⟨?_, hbromide, ?_⟩
    · norm_num [stationaryHBrO2B, sourceRateConstant, bromateConcentration,
        protonConcentration]
    · norm_num [step5Rate, step4Rate, stationaryHBrO2B, sourceRateConstant,
        bromateConcentration, protonConcentration]
      ring
  · intro hBrO2 bromide hsteady
    rcases hsteady with ⟨_, hbromide, hbalance⟩
    norm_num [step5Rate, step4Rate, sourceRateConstant, bromateConcentration,
      protonConcentration] at hbalance
    norm_num [stationaryHBrO2B, sourceRateConstant, bromateConcentration,
      protonConcentration]
    nlinarith

/-! ## Current part (T2-A3) -/

/-- The unrounded end-to-end threshold obtained by equating the mass-action
rates of source steps 1 and 4 and cancelling their common positive HBrO₂ and
proton factors. -/
def bromideCriticalRaw : MolarConcentration :=
  sourceRateConstant .step1 * bromateConcentration /
    sourceRateConstant .step4

/-- A bromide concentration is critical when it is nonnegative and the two
competing source rates agree for every positive HBrO₂ concentration at the
maintained proton concentration. -/
def IsCriticalBromide (bromide : MolarConcentration) : Prop :=
  0 ≤ bromide ∧
  ∀ hBrO2 : MolarConcentration, 0 < hBrO2 →
    step1Rate hBrO2 bromateConcentration protonConcentration =
      step4Rate hBrO2 bromide protonConcentration

/-- Problem-specific derivation specification.  It includes the required
inline T2-A2 derivation, equality and uniqueness at the boundary, and both
strict directions of the source's “must exceed ... and vice versa” rule. -/
def BromideCriticalDerivation : Prop :=
  PreviousPartInlineDerivation ∧
  IsCriticalBromide bromideCriticalRaw ∧
  (∀ bromide : MolarConcentration,
    IsCriticalBromide bromide → bromide = bromideCriticalRaw) ∧
  ∀ hBrO2 bromide : MolarConcentration,
    0 < hBrO2 → 0 ≤ bromide →
      (step4Rate hBrO2 bromide protonConcentration >
          step1Rate hBrO2 bromateConcentration protonConcentration ↔
        bromideCriticalRaw < bromide) ∧
      (step1Rate hBrO2 bromateConcentration protonConcentration >
          step4Rate hBrO2 bromide protonConcentration ↔
        bromide < bromideCriticalRaw)

/-- Raw-result contract.  The interval is deliberately nondegenerate and
contains the exact source-derived rational value. -/
theorem bromideCritical_raw_result :
    (BromideCriticalDerivation) ∧
    (((599 : ℝ) / 2000000000) ≤ (bromideCriticalRaw) ∧
      (bromideCriticalRaw) ≤ ((601 : ℝ) / 2000000000)) := by
  refine ⟨?_, ?_⟩
  · refine ⟨previousPart_inline_derivation, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · norm_num [bromideCriticalRaw, sourceRateConstant, bromateConcentration]
      · intro hBrO2 _
        norm_num [step1Rate, step4Rate, bromideCriticalRaw, sourceRateConstant,
          bromateConcentration, protonConcentration]
        ring
    · intro bromide hcritical
      rcases hcritical with ⟨_, hrate⟩
      have heq := hrate 1 (by norm_num)
      norm_num [step1Rate, step4Rate, sourceRateConstant, bromateConcentration,
        protonConcentration] at heq
      norm_num [bromideCriticalRaw, sourceRateConstant, bromateConcentration]
      linarith
    · intro hBrO2 bromide hhBrO2 _
      constructor
      · norm_num [step1Rate, step4Rate, bromideCriticalRaw, sourceRateConstant,
          bromateConcentration, protonConcentration]
        constructor <;> intro h <;> nlinarith
      · norm_num [step1Rate, step4Rate, bromideCriticalRaw, sourceRateConstant,
          bromateConcentration, protonConcentration]
        constructor <;> intro h <;> nlinarith
  · norm_num [bromideCriticalRaw, sourceRateConstant, bromateConcentration]

/-- Reported-result contract: three significant figures at this magnitude use
the quantum `10⁻⁹ mol dm⁻³`, with ties away from zero as fixed by the source
reporting policy. -/
theorem bromideCritical_reported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      (bromideCriticalRaw) ((300 : ℝ) / 1000000000)
      ((1 : ℝ) / 1000000000) := by
  refine ⟨by norm_num, ⟨300, by norm_num⟩, ?_⟩
  rw [if_pos]
  · norm_num [bromideCriticalRaw, sourceRateConstant, bromateConcentration]
  · norm_num [bromideCriticalRaw, sourceRateConstant, bromateConcentration]

/-- The deterministic reporting guard reduces the displayed decimal
`3.00e-7` to the canonical rational `3/10⁷`.  This proved bridge keeps that
machine normal form synchronized with the significant-figure carrier above. -/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"bromide_critical","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"3.00e-7","reporting_quantum":"1e-9","raw_declaration":"IChO2026Problems.T2A3.bromideCriticalRaw","reporting_declaration":"IChO2026Problems.T2A3.bromideCritical_numericReportingCertificate"}
theorem bromideCritical_numericReportingCertificate :
    IChO2026Chem.Reporting.ReportsAtQuantum
      (bromideCriticalRaw) ((3 : ℝ) / 10000000)
      ((1 : ℝ) / 1000000000) := by
  have h : ((300 : ℝ) / 1000000000) = ((3 : ℝ) / 10000000) := by
    norm_num
  simpa only [h] using bromideCritical_reported_result

end
end T2A3
end IChO2026Problems
