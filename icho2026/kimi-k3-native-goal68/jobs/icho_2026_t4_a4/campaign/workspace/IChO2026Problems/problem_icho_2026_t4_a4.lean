import Mathlib
import IChO2026Chem.Core
import IChO2026Chem.Reporting

/-!
# IChO 2026, Theory Problem T4, Subquestion A4 (question 4.4)

**Problem (verbatim from the official English paper, page Q4-2):**

> Calculate the energy released in this reaction (ΔE, MeV), if the binding
> energy BE(²³⁵U) = 7.59 MeV/nucleon and average binding energy for fission
> products BE(fis.) = 8.45 MeV/nucleon. Neglect the binding energy of free
> neutrons.

"this reaction" is the fission equation established in subquestion 4.3 from
problem-only inputs (mass/charge conservation, three emitted neutrons stated
in the shared context ²³⁵U + n → … + 3n, the two yield-curve peaks at
A ≈ 93 and A ≈ 140, and the same-group condition):

    ²³⁵U + ¹n → ⁹³Rb + ¹⁴⁰Cs + 3 ¹n

(Rb, Z = 37, and Cs, Z = 55, are both group-1 alkali metals; 93 + 140 + 3 = 236
and 37 + 55 = 92, so the equation balances.)

**Physical content of the calculation.**  Binding energy is the energy
required to disassemble a nucleus into free nucleons; energy is *released*
whenever total binding energy increases.  Hence, with free-neutron binding
neglected as instructed,

    ΔE = BE(products) − BE(reactants)
       = A_fis · BE(fis.) − A_U · BE(²³⁵U)
       = 233 · 8.45 − 235 · 7.59
       = 1968.85 − 1783.65
       = 185.20 MeV

which rounds to **185 MeV** at the three-significant-figure display default of
the answer-blind reporting policy.  (This is consistent with the problem's own
fallback instruction in 4.9 — "If you did not get an answer for 4.4, use
ΔE = 200 MeV" — which is only a rough substitute, not the exact value.)

This file formalizes:
  * the stoichiometric data of the 4.3 equation (mass and charge balance as
    proved arithmetic facts);
  * the binding-energy balance law as a derived theorem;
  * the exact raw value of ΔE and its three-significant-figure reporting at
    quantum 1 MeV via `IChO2026Chem.Reporting.ReportsAtQuantum`.
-/

namespace IChO2026.T4.A4

open IChO2026Chem.Reporting

/-! ## Problem-stated numerical inputs (from the printed question and the
shared context of T4) -/

/-- Binding energy per nucleon of ²³⁵U, as printed in question 4.4
(MeV per nucleon). -/
noncomputable def beU235 : ℝ := 7.59

/-- Average binding energy per nucleon of the fission products, as printed in
question 4.4 (MeV per nucleon). -/
noncomputable def beFission : ℝ := 8.45

/-- Mass number of the ²³⁵U nucleus that undergoes fission: 235 nucleons. -/
def nucleonsU235 : ℕ := 235

/-- Number of free neutrons emitted per fission event: 3, as printed in the
shared context equation ²³⁵U + ¹n → … + 3 ¹n. -/
def freeNeutrons : ℕ := 3

/-- Total nucleons present initially: one ²³⁵U nucleus (235) plus the absorbed
neutron (1) give 236. -/
def nucleonsInitial : ℕ := nucleonsU235 + 1

/-- Number of nucleons bound inside the two fission fragments: the initial 236
minus the three free neutrons, i.e. 233.  This is also the sum of the fragment
mass numbers of the 4.3 equation, 93 + 140 = 233. -/
def nucleonsFissionProducts : ℕ := nucleonsInitial - freeNeutrons

/-! ## Stoichiometry of the 4.3 fission equation (proved, not assumed) -/

/-- The fragment mass numbers 93 (Rb) and 140 (Cs) together with the three
emitted neutrons account for all 236 initial nucleons. -/
theorem mass_balance : 93 + 140 + freeNeutrons = nucleonsInitial := by
  decide

/-- The fragment atomic numbers 37 (Rb) and 55 (Cs) account for the 92 protons
of uranium; the neutrons carry no charge. -/
theorem charge_balance : 37 + 55 = 92 := by
  decide

/-- The two fragments indeed carry 233 bound nucleons. -/
theorem nucleons_fission_products_value : nucleonsFissionProducts = 233 := by
  decide

/-! ## Binding-energy balance law

Energy released equals the increase in total binding energy between the final
state (two fission fragments; the three free neutrons contribute nothing by
the problem's instruction) and the initial state (²³⁵U; the absorbed neutron
is free and likewise contributes nothing). -/

/-- The energy released per fission event, in MeV, as the difference between
the total binding energy of the fission products and that of ²³⁵U. -/
noncomputable def fissionEnergy : ℝ :=
  (nucleonsFissionProducts : ℝ) * beFission - (nucleonsU235 : ℝ) * beU235

/-- Unfolded form of the energy balance with the stoichiometric numbers
inserted: ΔE = 233 · 8.45 − 235 · 7.59. -/
theorem fissionEnergy_eq : fissionEnergy = 233 * 8.45 - 235 * 7.59 := by
  unfold fissionEnergy nucleonsFissionProducts nucleonsInitial freeNeutrons
    nucleonsU235 beFission beU235
  norm_num

/-! ## Exact value of the released energy -/

/-- Raw exact value: ΔE = 185.2 MeV. -/
theorem fissionEnergy_value : fissionEnergy = 185.2 := by
  rw [fissionEnergy_eq]
  norm_num

/-- The total binding energy of the 233 product nucleons is 1968.85 MeV. -/
theorem products_binding_energy : (233 : ℝ) * 8.45 = 1968.85 := by
  norm_num

/-- The total binding energy of the 235 nucleons of ²³⁵U is 1783.65 MeV. -/
theorem uranium_binding_energy : (235 : ℝ) * 7.59 = 1783.65 := by
  norm_num

/-- Confirmation that energy is released (ΔE > 0), i.e. the fission products
are more tightly bound, in total, than the parent nucleus. -/
theorem fission_releases_energy : 0 < fissionEnergy := by
  rw [fissionEnergy_value]
  norm_num

/-! ## Final reporting at three significant figures

The project-wide answer-blind default requests three significant figures.
185.2 MeV at three significant figures displays as 185 MeV, i.e. a quantum of
1 MeV.  We verify the `ReportsAtQuantum` contract between the exact raw value
185.2 and the reported display 185. -/

/-- The solver-owned numeric submission: raw value 185.2 MeV, reported value
185 MeV at quantum 1 MeV. -/
noncomputable def submission : NumericSubmission where
  rawValue := fissionEnergy
  reportedValue := 185
  reportingQuantum := 1

/-- The submission is valid: the raw field equals the exact expression and the
displayed 185 MeV is the three-significant-figure rounding of the raw value at
the 1 MeV quantum (185 − 0.5 ≤ 185.2 < 185 + 0.5; 185.2 is not at a
half-integer boundary, so the tie rule is irrelevant). -/
theorem submission_valid : ValidNumericSubmission fissionEnergy submission := by
  constructor
  · rfl
  · show ReportsAtQuantum submission.rawValue 185 1
    refine ⟨by norm_num, ⟨185, by norm_num⟩, ?_⟩
    show (if 0 ≤ submission.rawValue then _ else _)
    rw [show submission.rawValue = 185.2 from fissionEnergy_value]
    norm_num

/-- Main result of subquestion T4-A4 (question 4.4): the energy released in
the fission reaction ²³⁵U + n → ⁹³Rb + ¹⁴⁰Cs + 3n is exactly 185.2 MeV under
the printed per-nucleon binding energies, reported as 185 MeV to three
significant figures. -/
theorem t4_a4_answer :
    fissionEnergy = 185.2 ∧
    ValidNumericSubmission fissionEnergy submission ∧
    submission.reportedValue = 185 :=
  ⟨fissionEnergy_value, submission_valid, rfl⟩

end IChO2026.T4.A4

/-! ## Axiom audit -/

#print axioms IChO2026.T4.A4.t4_a4_answer
