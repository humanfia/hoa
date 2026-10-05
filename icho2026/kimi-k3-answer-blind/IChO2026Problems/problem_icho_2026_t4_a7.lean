import IChO2026Chem

/-!
# IChO 2026, Problem T4, part 4.7 (target `icho_2026_t4_a7`)

**Source (Q4-3, `icho_2026_source/image/T4_page-3.png`):**
"Calculate Δ_rH_2000 (kJ mol⁻¹) per mole of methane combustion reaction at
2000 K. **Assume** all species are gaseous."

**Shared context (Q4-2, `icho_2026_source/image/T4_page-2.png`, part 4.6 and
its data table):** the reaction is the complete combustion of one mole of
methane,

  CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g),

with problem-stipulated thermodynamic data (all species gaseous):

* ΔfH°₂₉₈(CH₄) = −74.8 kJ mol⁻¹,  ΔfH°₂₉₈(H₂O, gas) = −241.8 kJ mol⁻¹,
  ΔfH°₂₉₈(CO₂) = −393.5 kJ mol⁻¹;
* C_P(CH₄) = 35, C_P(H₂O, gas) = 34, C_P(O₂) = 29, C_P(CO₂) = 37
  J mol⁻¹ K⁻¹ (single values, i.e. taken temperature-independent).

**Previous-part dependency (T4-A6, policy
`derive_in_answer_blind_run_or_use_problem_stated_fallback`):** the 298 K
reaction enthalpy is re-derived here inline from the problem-stipulated
formation enthalpies via Hess's law (provenance `derived_theorem` from
`problem_text`/`problem_image` data). The printed fallback ΔH₂₉₈ = −750
kJ mol⁻¹ is **not** used: it is authorized only when no value is derived,
and a fallback may never justify the part it replaces.

**Governing relations.**

* Hess's law: ΔrH°₂₉₈ = Σ ν·ΔfH°₂₉₈ over the four species.
* Kirchhoff's law with constant heat capacities:
  ΔrH(T) = ΔrH(298 K) + ΔC_P·(T − 298 K), with ΔC_P = Σ ν·C_P.

This file formalizes the problem, with complete proof bodies below.
The raw value carrier `combustionEnthalpy2000kJmol` is the unrounded
end-to-end Kirchhoff expression built from the named problem data; the
reported value follows the source reporting policy (3 significant figures,
ties half away from zero).
-/

namespace IChO2026Problems.problem_icho_2026_t4_a7

/-- The four chemical species of the methane combustion reaction
(problem T4 parts 4.6–4.7). -/
inductive Species where
  | CH4
  | O2
  | CO2
  | H2O
  deriving DecidableEq, Repr

/-- Thermodynamic phase of a species. -/
inductive Phase where
  | gas
  | liquid
  | solid
  deriving DecidableEq, Repr

/-- Problem stipulation ("**Assume** all species are gaseous", parts 4.6 and
4.7): every species of this reaction is in the gas phase. -/
def phaseOf : Species → Phase := fun _ => Phase.gas

/-- Every species is gaseous, as stipulated. -/
theorem all_species_gaseous : ∀ s : Species, phaseOf s = Phase.gas := fun _ => rfl

/-- Stoichiometric coefficients ν of
`CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)`,
signed with products positive and reactants negative. -/
def stoich : Species → ℝ
  | .CH4 => -1
  | .O2 => -2
  | .CO2 => 1
  | .H2O => 2

/-- The reaction enthalpies are per mole of methane: `|ν(CH₄)| = 1`. -/
theorem per_mole_methane_basis : stoich Species.CH4 = -1 := rfl

/-- Problem-stipulated standard molar formation enthalpies at 298 K, in
kJ mol⁻¹ (data table of part 4.6). O₂(g) is the elemental reference state,
so its formation enthalpy is 0 by the standard convention the table relies
on. -/
def formationEnthalpy298 : Species → ℝ
  | .CH4 => -74.8
  | .O2 => 0
  | .CO2 => -393.5
  | .H2O => -241.8

/-- Problem-stipulated molar heat capacities at constant pressure, in
J mol⁻¹ K⁻¹ (data table of part 4.6). The problem supplies one value per
species, so they are used as temperature-independent over 298–2000 K. -/
def heatCapacity : Species → ℝ
  | .CH4 => 35
  | .O2 => 29
  | .CO2 => 37
  | .H2O => 34

/-- Hess's law: standard reaction enthalpy at 298 K,
`ΔrH°₂₉₈ = Σ ν·ΔfH°₂₉₈`, in kJ mol⁻¹.  This is the previous part T4-A6
re-derived inline from the problem's own data. -/
def reactionEnthalpy298kJ : ℝ :=
  stoich .CH4 * formationEnthalpy298 .CH4
    + stoich .O2 * formationEnthalpy298 .O2
    + stoich .CO2 * formationEnthalpy298 .CO2
    + stoich .H2O * formationEnthalpy298 .H2O

/-- Reaction heat capacity `ΔC_P = Σ ν·C_P`, in J mol⁻¹ K⁻¹. -/
def reactionCpJ : ℝ :=
  stoich .CH4 * heatCapacity .CH4
    + stoich .O2 * heatCapacity .O2
    + stoich .CO2 * heatCapacity .CO2
    + stoich .H2O * heatCapacity .H2O

/-- Kirchhoff's law with the problem's constant heat capacities:
`ΔrH(T) = ΔrH(298 K) + ΔC_P·(T − 298 K)`, with the factor `1/1000`
converting the J mol⁻¹ heat-capacity term to kJ mol⁻¹. -/
noncomputable def reactionEnthalpyAtK (T : ℝ) : ℝ :=
  reactionEnthalpy298kJ + reactionCpJ * (T - 298) / 1000

/-- Raw (unrounded) combustion enthalpy of methane at 2000 K, in kJ mol⁻¹:
the end-to-end Hess–Kirchhoff expression built from the named problem data. -/
noncomputable def combustionEnthalpy2000kJmol : ℝ := reactionEnthalpyAtK 2000

/-- Inline T4-A6 evaluation: the Hess-law sum over the problem's formation
enthalpies is −802.3 kJ mol⁻¹. -/
theorem reactionEnthalpy298kJ_value : reactionEnthalpy298kJ = -802.3 := by
  norm_num [reactionEnthalpy298kJ, stoich, formationEnthalpy298]

/-- The reaction heat capacity evaluates to 12 J mol⁻¹ K⁻¹. -/
theorem reactionCpJ_value : reactionCpJ = 12 := by
  norm_num [reactionCpJ, stoich, heatCapacity]

/-- Exact raw value at 2000 K:
`−802.3 + 12·(2000 − 298)/1000 = −781.876` kJ mol⁻¹. -/
theorem combustionEnthalpy2000kJmol_value :
    combustionEnthalpy2000kJmol = -781.876 := by
  unfold combustionEnthalpy2000kJmol reactionEnthalpyAtK
  rw [reactionEnthalpy298kJ_value, reactionCpJ_value]
  norm_num

/-- Derivation specification (governing relation) for the raw carrier: the
2000 K reaction enthalpy is the Kirchhoff temperature correction of the
Hess-law 298 K reaction enthalpy using the problem's constant heat
capacities. -/
def CombustionEnthalpy2000Spec : Prop :=
  combustionEnthalpy2000kJmol
    = reactionEnthalpy298kJ + reactionCpJ * (2000 - 298) / 1000

/-- Raw result contract: the governing relation holds, and the raw value
lies strictly inside the certified non-degenerate rational interval
[−781.877, −781.875] kJ mol⁻¹ (the raw value is exactly −781.876). -/
theorem combustion_enthalpy_2000_raw :
    (CombustionEnthalpy2000Spec) ∧
      (((-781877 : ℝ) / 1000) ≤ (combustionEnthalpy2000kJmol) ∧
        (combustionEnthalpy2000kJmol) ≤ ((-6255 : ℝ) / 8)) := by
  refine ⟨rfl, ?_⟩
  rw [combustionEnthalpy2000kJmol_value]
  exact ⟨by norm_num, by norm_num⟩

/-- Reported result contract: at the source reporting policy of 3
significant figures (quantum 1 kJ mol⁻¹ for a value of magnitude ~10²,
ties half away from zero), the raw value is reported as −782 kJ mol⁻¹. -/
theorem combustion_enthalpy_2000_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      (combustionEnthalpy2000kJmol) (-782 : ℝ) (1 : ℝ) := by
  rw [combustionEnthalpy2000kJmol_value]
  refine ⟨by norm_num, ⟨-782, by norm_num⟩, ?_⟩
  split_ifs with h
  · norm_num at h
  · exact ⟨by norm_num, by norm_num⟩

end IChO2026Problems.problem_icho_2026_t4_a7
