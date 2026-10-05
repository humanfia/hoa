import IChO2026Chem

/-!
# IChO 2026, Problem T4 (Q4-2, part 4.4) — Energy released in ²³⁵U fission

**Source contract** (problem_text, Q4-2 box 4.4 on `T4_page-2.png`):

* Reaction under study (shared context, `T4_page-1.png`): the main reactor
  reaction, in which ²³⁵U absorbs a neutron and undergoes fission,
  "releasing energy and producing three additional neutrons", printed as
  `²³⁵U + ¹₀n → … + 3¹₀n`.  Hence 3 free neutrons are emitted per fission.
* Q4-4 stipulates the binding energy per nucleon of ²³⁵U,
  `BE(²³⁵U) = 7.59 MeV/nucleon`, and the average binding energy per nucleon
  of the fission products, `BE(fis.) = 8.45 MeV/nucleon`, and instructs:
  "Neglect the binding energy of free neutrons."  All three values are
  stipulated constants, exact as printed.
* Requested output: the energy released in this reaction, `ΔE`, in MeV.

**Previous-part dependency (T4-A3).**  Part 4.3 asks for the explicit fission
equation (the same-group fragment pair).  The energy balance of 4.4 consumes
only the *nucleon bookkeeping* of that reaction — 235 + 1 nucleons in, 3 free
neutrons out, hence 233 nucleons bound in the fragments — all of which is
stipulated in the shared context equation above.  `BE(fis.)` is stipulated as
the average over the fission products, so the fragment identity does not
enter.  The prerequisite is therefore discharged entirely from problem-stated
material (`problem_text`), per the declared policy
`derive_in_answer_blind_run_or_use_problem_stated_fallback`; no external or
fallback value is used.

**Governing relation** (trusted_general_law: mass–energy conservation for a
nuclear reaction, i.e. the binding-energy balance).  The energy released
equals the total binding energy of the product side minus that of the
reactant side.  With free-neutron binding energies neglected (both the
absorbed and the three emitted neutrons contribute 0):

```
ΔE = BE(fis.) · A(fragments) − BE(²³⁵U) · 235
   = 8.45 · (235 + 1 − 3) − 7.59 · 235
   = 8.45 · 233 − 7.59 · 235
   = 1968.85 − 1783.65 = 185.2 MeV = 926/5 MeV
```

**Reporting** (uniform blind evaluation default; the problem requests no
explicit precision): three significant figures, ties half away from zero.
For a value in [100, 1000) the quantum is 1 MeV; `184.5 ≤ 926/5 < 185.5`, so
the reported energy is `185 MeV`.

The two result contracts at the end are the answer-blind certificates: the
raw contract carries the derivation spec together with a non-degenerate
certified rational interval for the unrounded value, and the reported
contract carries the `ReportsAtQuantum` certificate for `185 MeV`.
-/

namespace IChO2026.T4.A4

/-- Problem-stipulated binding energy per nucleon of ²³⁵U, in MeV/nucleon
(problem_text, Q4-2 box 4.4 on `T4_page-2.png`), exact as printed. -/
def bePerNucleonU235 : ℝ := 7.59

/-- Problem-stipulated average binding energy per nucleon of the fission
products, in MeV/nucleon (problem_text, Q4-2 box 4.4 on `T4_page-2.png`),
exact as printed. -/
def bePerNucleonFissionProducts : ℝ := 8.45

/-- Mass number of the fissioning nucleus ²³⁵U: 235 nucleons (problem_text,
isotope name throughout the shared context and box 4.4). -/
def massNumberU235 : ℕ := 235

/-- Number of free neutrons released per fission event (problem_text, shared
context on `T4_page-1.png`: "producing three additional neutrons" and the
printed equation `²³⁵U + ¹₀n → … + 3¹₀n`). -/
def neutronsEmitted : ℕ := 3

/-- Total number of nucleons bound in the fission fragments: by nucleon
(mass-number) conservation in `²³⁵U + ¹n → fragments + 3¹n`,
`A(fragments) = 235 + 1 − 3 = 233`.  The problem stipulates that the binding
energy of the free neutrons is neglected, so only these 233 nucleons carry
the stipulated fission-product binding energy. -/
def fragmentNucleons : ℕ := massNumberU235 + 1 - neutronsEmitted

/-- Total binding energy of a nucleus (or fragment ensemble) with `a` nucleons
and mean binding energy `be` per nucleon, in MeV. -/
def totalBindingEnergy (be : ℝ) (a : ℕ) : ℝ := be * (a : ℝ)

/-- Nucleon-number conservation in the stipulated fission reaction:
`233 + 3 = 236 = 235 + 1`. -/
theorem nucleon_conservation :
    fragmentNucleons + neutronsEmitted = massNumberU235 + 1 := rfl

/-- **Fission energy-release model** (problem_text box 4.4 together with
mass–energy conservation, a trusted general law): the energy released equals
the total binding energy of the product side minus that of the reactant side.
The reactant side binds 235 nucleons at 7.59 MeV/nucleon (the absorbed free
neutron carries no binding energy); the product side binds 233 nucleons at
8.45 MeV/nucleon, while the 3 emitted free neutrons contribute zero under the
stipulated neglect of free-neutron binding energy. -/
def FissionEnergyRelease (ΔE : ℝ) : Prop :=
  ΔE = totalBindingEnergy bePerNucleonFissionProducts fragmentNucleons -
    totalBindingEnergy bePerNucleonU235 massNumberU235

/-- Raw (unrounded) energy released per fission event, in MeV:
`8.45 · 233 − 7.59 · 235`. -/
noncomputable def fissionEnergyReleasedRaw : ℝ :=
  totalBindingEnergy bePerNucleonFissionProducts fragmentNucleons -
    totalBindingEnergy bePerNucleonU235 massNumberU235

/-- The raw expression is its defining difference (no intermediate rounding). -/
theorem fissionEnergyReleasedRaw_eq :
    fissionEnergyReleasedRaw =
      totalBindingEnergy bePerNucleonFissionProducts fragmentNucleons -
        totalBindingEnergy bePerNucleonU235 massNumberU235 :=
  rfl

/-- The derived raw value satisfies the fission energy-release model. -/
theorem fissionEnergyRelease_candidate :
    FissionEnergyRelease fissionEnergyReleasedRaw :=
  rfl

/-- The model fixes `ΔE` uniquely: it is a direct defining equation. -/
theorem fissionEnergyRelease_unique {ΔE : ℝ} (h : FissionEnergyRelease ΔE) :
    ΔE = fissionEnergyReleasedRaw :=
  h

/-- Exact value of the raw energy release: `926/5 = 185.2` MeV. -/
theorem fissionEnergyReleasedRaw_value : fissionEnergyReleasedRaw = (926 : ℝ) / 5 := by
  norm_num [fissionEnergyReleasedRaw, totalBindingEnergy, bePerNucleonFissionProducts,
    bePerNucleonU235, massNumberU235, fragmentNucleons, neutronsEmitted]

/-- The released energy is strictly positive (the fission is exoergic). -/
theorem fissionEnergyReleasedRaw_pos : (0 : ℝ) < fissionEnergyReleasedRaw := by
  rw [fissionEnergyReleasedRaw_value]
  norm_num

/-- Certified non-degenerate rational interval for the raw energy release,
fixed before any rounding: `1851/10 = 185.1 ≤ 926/5 ≤ 185.3 = 1853/10`. -/
theorem fissionEnergyReleasedRaw_bounds :
    ((1851 : ℝ) / 10) ≤ fissionEnergyReleasedRaw ∧
      fissionEnergyReleasedRaw ≤ ((1853 : ℝ) / 10) := by
  rw [fissionEnergyReleasedRaw_value]
  constructor <;> norm_num

/-- **Raw derivation specification** for the fission energy release: the raw
candidate satisfies — and is uniquely fixed by — the stipulated
binding-energy-balance model, the release is positive, and the fragment
nucleon count obeys nucleon conservation with the three emitted neutrons. -/
def RawFissionEnergySpec : Prop :=
  FissionEnergyRelease fissionEnergyReleasedRaw ∧
    (∀ ΔE : ℝ, FissionEnergyRelease ΔE → ΔE = fissionEnergyReleasedRaw) ∧
    (0 : ℝ) < fissionEnergyReleasedRaw ∧
    fragmentNucleons + neutronsEmitted = massNumberU235 + 1

/-- The derivation specification holds for the derived candidate. -/
theorem rawFissionEnergySpec_holds : RawFissionEnergySpec :=
  ⟨fissionEnergyRelease_candidate, fun _ h => fissionEnergyRelease_unique h,
    fissionEnergyReleasedRaw_pos, nucleon_conservation⟩

/-- **Raw result contract** (answer-blind): the derivation specification
`RawFissionEnergySpec` holds for the source-derived raw expression
`fissionEnergyReleasedRaw = 8.45 · 233 − 7.59 · 235`, together with the
certified non-degenerate interval `1851/10 ≤ raw ≤ 1853/10`. -/
theorem raw_result_contract :
    (IChO2026.T4.A4.RawFissionEnergySpec) ∧
      (((1851 : ℝ) / 10) ≤ (IChO2026.T4.A4.fissionEnergyReleasedRaw) ∧
        (IChO2026.T4.A4.fissionEnergyReleasedRaw) ≤ ((1853 : ℝ) / 10)) :=
  ⟨rawFissionEnergySpec_holds, fissionEnergyReleasedRaw_bounds⟩

/-- **Reported result contract** (answer-blind): at the
three-significant-figure quantum `1 MeV` (ties half away from zero), the raw
value `926/5 = 185.2 MeV` is reported as `185 MeV`, since
`184.5 = 185 − 1/2 ≤ 926/5 < 185 + 1/2 = 185.5`. -/
theorem reported_result_contract :
    IChO2026Chem.Reporting.ReportsAtQuantum (IChO2026.T4.A4.fissionEnergyReleasedRaw)
      (185 : ℝ) (1 : ℝ) := by
  have hraw : (0 : ℝ) ≤ IChO2026.T4.A4.fissionEnergyReleasedRaw := by
    rw [fissionEnergyReleasedRaw_value]
    norm_num
  refine ⟨by norm_num, ⟨185, by norm_num⟩, ?_⟩
  rw [if_pos hraw, fissionEnergyReleasedRaw_value]
  constructor <;> norm_num

end IChO2026.T4.A4
