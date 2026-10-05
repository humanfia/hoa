import IChO2026Chem

/-!
# IChO 2026, Theory Problem T9 (Q9-1) — Part 9.1: molar mass of β-cyclodextrin

## Source statement (official English PDF, page 84 / printed page Q9-1)

Cyclodextrins (CD) are a family of cyclic oligosaccharides, consisting of
glucose subunits joined by alpha-1,4-glycosidic bonds. The three most common
cyclodextrins (alpha-, beta-, gamma-cyclodextrin) contain 6, 7, and 8
alpha-D-glucopyranoside units, respectively.

9.1 Calculate the molar mass of beta-CD. Assume Mw(glucose) = 180.16 g mol^-1.

The blank student answer sheet (PDF page 89, A9-1) shows the single requested
entry "Mw : beta-CD = ____", so the only requested output is the numeric molar
mass in g mol^-1, displayed at the three-significant-figure default recorded in
TASK.json's reporting_policy.

## Chemistry encoded here

* beta-CD contains 7 glucose units (stated in the shared context; the figure
  on Q9-1 is also labelled "n = 7 beta-CD").
* The ring is closed by 7 alpha-1,4-glycosidic bonds; each bond is formed by
  condensation of the anomeric hydroxy of one unit with the 4-hydroxy of the
  next, eliminating one H2O per bond.  Hence 1 mol of beta-CD corresponds to
  7 mol of glucose minus 7 mol of water, i.e. the beta-CD residue formula is
  (C6H12O6)7 - 7 H2O = C42H70O35.
* M(H2O) is derived from the IChO 2026 data sheet printed on the inside front
  cover of theory_problem.pdf: Ar(H) = 1.008, Ar(O) = 16.00 (printed values,
  treated as exact rational data per the measurement policy).
  So M(H2O) = 2*1.008 + 16.00 = 18.016 g mol^-1 exactly.

No official solution, marking scheme, or prior answer was consulted; the
inputs above come only from the problem page and its data sheet.

## Arithmetic (no intermediate rounding)

M(beta-CD) = 7 * 180.16 - 7 * 18.016 = 1135.008 g mol^-1.

The displayed value consistent with three significant figures is 1135 g mol^-1
(approx. 1.14 x 10^3 g mol^-1), quantum 1 g mol^-1, ties half-away-from-zero,
per the fixed IChO2026Chem.Reporting.ReportsAtQuantum relation.
-/

namespace IChO2026Problems.T9A1

open IChO2026Chem.Reporting

/-! ### Exact rational inputs (actual problem inputs) -/

/-- Printed datum: Mw(glucose) = 180.16 g mol^-1, exact as printed. -/
def glucoseMass : ℚ := 18016 / 100

/-- Printed datum: Ar(H) = 1.008 from the IChO 2026 data sheet. -/
def massH : ℚ := 1008 / 1000

/-- Printed datum: Ar(O) = 16.00 from the IChO 2026 data sheet. -/
def massO : ℚ := 1600 / 100

/-- Number of glucose units in beta-CD (problem context; figure "n = 7 beta-CD"). -/
def betaUnits : ℕ := 7

/-! ### Derived quantities -/

/-- Water mass from the data-sheet atomic masses: 2*Ar(H) + Ar(O). -/
def waterMass : ℚ := 2 * massH + massO

/-- Water derived from the data sheet equals 18.016 g mol^-1 exactly. -/
theorem waterMass_value : (waterMass : ℝ) = 18016 / 1000 := by
  unfold waterMass massH massO
  push_cast
  ring

/-- Raw molar mass of beta-CD: 7 glucoses minus the 7 waters lost on ring closure. -/
def betaCDMolarMassRaw : ℚ :=
  (betaUnits : ℚ) * glucoseMass - (betaUnits : ℚ) * waterMass

/-- The raw molar mass collapses to 1135.008 g mol^-1 exactly. -/
theorem betaCDMolarMass_value : (betaCDMolarMassRaw : ℝ) = 1135008 / 1000 := by
  unfold betaCDMolarMassRaw betaUnits waterMass glucoseMass massH massO
  push_cast
  ring

/-! ### Final reporting at three significant figures -/

/-- At quantum 1 g mol^-1 the raw value rounds (ties half-away-from-zero) to
1135 g mol^-1, the three-significant-figure display required by the
reporting policy. -/
theorem betaCDMolarMass_reports_1135 :
    ReportsAtQuantum (betaCDMolarMassRaw : ℝ) (1135 : ℝ) 1 := by
  unfold ReportsAtQuantum
  refine ⟨by norm_num, ⟨1135, by norm_num⟩, ?_⟩
  rw [betaCDMolarMass_value, if_pos (by norm_num)]
  constructor <;> norm_num

/-- The full numeric submission satisfying the target-independent contract. -/
noncomputable def betaCDSubmission : NumericSubmission where
  rawValue := (betaCDMolarMassRaw : ℝ)
  reportedValue := 1135
  reportingQuantum := 1

/-- The submission is valid: its raw value is the exact symbolic expression and
its reported value is the ReportsAtQuantum-correct three-significant-figure
print. -/
theorem betaCDSubmission_valid :
    ValidNumericSubmission (betaCDMolarMassRaw : ℝ) betaCDSubmission :=
  ⟨rfl, betaCDMolarMass_reports_1135⟩

end IChO2026Problems.T9A1

#print axioms IChO2026Problems.T9A1.waterMass_value
#print axioms IChO2026Problems.T9A1.betaCDMolarMass_value
#print axioms IChO2026Problems.T9A1.betaCDMolarMass_reports_1135
#print axioms IChO2026Problems.T9A1.betaCDSubmission_valid
