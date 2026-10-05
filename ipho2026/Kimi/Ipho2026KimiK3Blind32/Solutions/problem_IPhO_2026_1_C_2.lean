import Mathlib

/- USER: Mandatory formalization repair. The helper `threshold_upward` is
false: the quadratic threshold condition has two roots, so its feasible set
is not globally upward closed through the interval between them. Remove that
helper and characterize the physical threshold as the smaller feasible
boundary (equivalently the `sInf`/least nonnegative feasible frequency), with
membership proved from the explicit smaller-root witness and the quadratic
identity. Preserve the answer-blind excess-energy target and all printed data;
do not assume the requested numerical value or use the larger root. -/

/-!
# IPhO 2026, Problem 1, Part C.2 — Numerical excess photon energy at threshold

## Physical situation

A photon of angular frequency `ω` is absorbed by an ozone molecule `O₃` at rest
and dissociates it into an oxygen molecule `O₂` (mass `2·m`) and a single
oxygen atom `O` (mass `m`), where `m` is the mass of one oxygen atom.  The
ground-state energies of `O₃` and `O₂` are `Uᵢ` and `U_f`; only the difference
`ΔU = U_f - Uᵢ`, the dissociation threshold energy, enters the model.  The
outgoing `O₂` momentum makes the angle `θ` with the incident photon direction
(official source page `.archon/blind-assets/IPhO_2026_1_C_2/T1_page-3.png`:
photon axis horizontal, `O₂` emitted at angle `θ` above it, `O` recoiling
below).  The fragments are treated classically and non-relativistically; the
photon carries momentum `p_γ = E_γ / c = ℏ·ω / c`.

* **Part C.1** (previous subquestion; natural-language prerequisite only —
  its Lean output is *not* imported) characterises the minimum photon angular
  frequency `ω_min` needed for dissociation at outgoing `O₂` angle `θ`, in
  terms of `ℏ`, `c`, `θ`, `ΔU` and `m`.  Its *content* is re-expressed here,
  parametrically in `(ω, θ)`, as the predicate `DissociationThreshold`
  together with the characterisation `IsMinFrequency`.
* **Part C.2 (this file).**  For `θ = π / 6`, `ΔU = 1.10 eV` and
  `m = 16.0 amu`, determine the excess photon energy `ℏ·ω_min − ΔU`, reported
  in electron-volts.

## Answer-blind policy

No numerical value, closed form, interval, or selected choice appears in any
signature.  The requested quantity is characterised answer-freely: a solution
predicate (`IsExcessEnergy`, `IsExcessEnergyElectronVolts`) is defined from
the setup, the governing laws and the given data, and the theorems assert
existence and uniqueness (`∃!`).  The concrete witness is constructed only in
the proving stage.  The conventional scale anchors (`amu`, `eV`, `h`, `c`)
are carried as strictly positive parameters `PartC2Data`; only the numerical
data literally printed in the question (`16.0 amu`, `1.10 eV`, `π / 6`) are
pinned as literals.

## Dimensional roles

Lean quantities are real magnitudes in fixed coherent SI-like roles (joule,
kilogram, metre per second, radian per second).  The dimensional
consistency of the stipulated governing relations — photon momentum `ℏω/c`
being a momentum, `q²/(2M)` an energy, etc. — is recorded by the predicate
`GoverningRelationsDimensional`, asserted for the C.2 data in
`PartC2Data.governingLawsHold`.
-/

namespace IPhO2026.T1.C2

open Real

/-- **Parameters of the photodissociation model**, with quantities held in
fixed coherent SI-like roles:

* `ℏ` — reduced Planck constant `[J·s]`, strictly positive;
* `c` — speed of light `[m·s⁻¹]`, strictly positive;
* `m` — mass of one oxygen atom `[kg]`, strictly positive, so the `O₂`
  fragment has mass `2·m`;
* `ΔU` — dissociation threshold energy `U_f - Uᵢ` `[J]`, nonnegative. -/
structure DissociationParameters where
  /-- Reduced Planck constant `ℏ` `[J·s]`, strictly positive. -/
  ℏ : ℝ
  /-- Speed of light `c` `[m·s⁻¹]`, strictly positive. -/
  c : ℝ
  /-- Mass `m` of one oxygen atom `[kg]`, strictly positive. -/
  m : ℝ
  /-- Dissociation energy threshold `ΔU = U_f - Uᵢ` `[J]`, nonnegative. -/
  ΔU : ℝ
  ℏ_pos : 0 < ℏ
  c_pos : 0 < c
  m_pos : 0 < m
  ΔU_nonneg : 0 ≤ ΔU

namespace DissociationParameters

/-- A photon of angular frequency `ω` `[rad·s⁻¹]` carries energy
`ℏ·ω` `[J]`. -/
noncomputable def photonEnergy (P : DissociationParameters) (ω : ℝ) : ℝ := P.ℏ * ω

/-- Photon momentum magnitude `p_γ = E_γ / c = ℏ·ω / c` `[kg·m·s⁻¹]`. -/
noncomputable def photonMomentum (P : DissociationParameters) (ω : ℝ) : ℝ :=
  P.photonEnergy ω / P.c

/-- Mass of the `O₂` fragment: twice the oxygen-atom mass `[kg]`. -/
noncomputable def oxygenMoleculeMass (P : DissociationParameters) : ℝ := 2 * P.m

/-- Non-relativistic kinetic energy of a classical fragment of mass `M`
carrying momentum of magnitude `q`:  `q² / (2·M)` `[J]`. -/
noncomputable def fragmentKineticEnergy (_P : DissociationParameters) (q M : ℝ) : ℝ :=
  q ^ 2 / (2 * M)

/-- Momentum magnitude of the recoiling single-oxygen fragment when the `O₂`
fragment carries momentum of magnitude `q` at angle `θ` to the photon.  Vector
momentum conservation in the scattering plane fixes the recoil `O` momentum as
the vector difference of the photon momentum and the `O₂` momentum, so its
squared magnitude is `(ℏω/c − q·cos θ)² + (q·sin θ)²` `[kg²·m²·s⁻²]`. -/
noncomputable def oxygenMomentumMagnitude (P : DissociationParameters) (ω θ q : ℝ) : ℝ :=
  Real.sqrt ((P.photonMomentum ω - q * cos θ) ^ 2 + (q * sin θ) ^ 2)

/-- Total fragment recoil kinetic energy of the momentum-conserving final
state in which the `O₂` fragment carries momentum of magnitude `q` at angle
`θ` to the incident photon `[J]`: `q²/(2·(2m))` for the `O₂` fragment plus
`p_O²/(2m)` for the recoiling oxygen atom, with the `O` momentum fixed by
vector momentum conservation. -/
noncomputable def recoilEnergy (P : DissociationParameters) (ω θ q : ℝ) : ℝ :=
  P.fragmentKineticEnergy q P.oxygenMoleculeMass +
    P.fragmentKineticEnergy (P.oxygenMomentumMagnitude ω θ q) P.m

end DissociationParameters

/-- `r` `[J]` is the **least total recoil kinetic energy** over all classical
momentum-conserving final states with `O₂` emitted at angle `θ` to the
incident photon of frequency `ω`: it is attained at some physical fragment
momentum (nonnegative `O₂` momentum magnitude `q`) and no other configuration
with `q ≥ 0` has smaller total recoil energy. -/
def IsLeastRecoilEnergy (P : DissociationParameters) (ω θ r : ℝ) : Prop :=
  (∃ q : ℝ, 0 ≤ q ∧ P.recoilEnergy ω θ q = r) ∧
    ∀ q : ℝ, 0 ≤ q → r ≤ P.recoilEnergy ω θ q

/-- **C.1 threshold content, expressed parametrically in `(ω, θ)`** as a
natural-language prerequisite (C.1's Lean output is not imported).

`DissociationThreshold ω θ` asserts that the absorbed photon's energy `ℏ·ω`
equals the dissociation threshold `ΔU` plus the *least* recoil kinetic energy
compatible with momentum conservation at outgoing `O₂` angle `θ`: the photon
energy in excess of the threshold is carried entirely by the least-recoil
classical final state.  Physically this least-recoil state is realised when
the fragment momenta are parallel (no relative motion), which minimises the
total recoil energy at fixed `q` — this is the content of the minimum-energy
condition of part C.1, before minimising over the frequency. -/
def DissociationThreshold (P : DissociationParameters) (ω θ : ℝ) : Prop :=
  ∃ r : ℝ, IsLeastRecoilEnergy P ω θ r ∧ P.photonEnergy ω = P.ΔU + r

/- RETIRED CONTRACT (iter-019): the following attempted upward-closure lemma
is deliberately kept only as historical commentary.  The exact quadratic
threshold equation has two roots and its solution set is not an upward ray.

/-- **Threshold frequencies form an upward ray** (closedness/monotonicity of
the feasible set): increasing the photon frequency at fixed fragment geometry
strictly increases the least momentum-conserving recoil energy
(`∂r_min/∂p_γ = p_γ/(3m) > 0`), so an excess in photon energy above the
threshold at `ω₀` can be re-absorbed into recoil, placing every `ω₁ ≥ ω₀`
back on the threshold energy balance.  This is a physical fact about the
C.1 threshold relation, used to show that the greatest lower bound of the
threshold set satisfies the threshold condition itself.  Body deferred to
the proving stage. -/
theorem threshold_upward {P : DissociationParameters} {θ ω₀ ω₁ : ℝ}
    (hω₀ : 0 ≤ ω₀) (hω₀ω₁ : ω₀ ≤ ω₁)
    (hθ : DissociationThreshold P ω₀ θ) : DissociationThreshold P ω₁ θ := by
  obtain ⟨r₀, ⟨hq₀a, hq₀b⟩, hE₀⟩ := hθ
  -- least-recoil quadratic expansion (valid for any angle)
  have hf : ∀ ω q : ℝ, 12 * P.m * P.recoilEnergy ω θ q =
      3 * (3 * q - 2 * ((P.ℏ * ω) / P.c) * cos θ) ^ 2 +
        6 * ((P.ℏ * ω) / P.c) ^ 2 * (cos θ ^ 2 + sin θ ^ 2) := by
    intro ω q
    have hα : (P.oxygenMomentumMagnitude ω θ q) ^ 2 =
        (P.photonMomentum ω - q * cos θ) ^ 2 + (q * sin θ) ^ 2 := by
      change (Real.sqrt _) ^ 2 = _
      exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hβ : P.recoilEnergy ω θ q =
        q ^ 2 / (2 * (2 * P.m)) + (P.oxygenMomentumMagnitude ω θ q) ^ 2 / (2 * P.m) := by
      change q ^ 2 / (2 * P.oxygenMoleculeMass) + _ / (2 * P.m) = _
      rw [show P.oxygenMoleculeMass = 2 * P.m from rfl]
    rw [hβ, hα, P.photonMomentum, P.photonEnergy]
    field_simp
    ring
  have hf' : ∀ ω q : ℝ, 12 * P.m * P.recoilEnergy ω θ q =
      3 * (3 * q - 2 * ((P.ℏ * ω) / P.c) * cos θ) ^ 2 + 6 * ((P.ℏ * ω) / P.c) ^ 2 := by
    intro ω q
    rw [hf ω q, Real.cos_sq_add_sin_sq θ, mul_one]
  have hr₀ : r₀ = 6 * ((P.ℏ * ω₀) / P.c) ^ 2 / (12 * P.m) := by
    obtain ⟨q0, h_, hq0⟩ := hq₀a
    have hatt : P.recoilEnergy ω₀ θ q0 = r₀ := hq0
    have hlb : ∀ q : ℝ, 6 * ((P.ℏ * ω₀) / P.c) ^ 2 ≤ 12 * P.m * P.recoilEnergy ω₀ θ q := by
      intro q
      have h := hf' ω₀ q
      nlinarith [sq_nonneg (3 * q - 2 * ((P.ℏ * ω₀) / P.c) * cos θ)]
    have hv : 12 * P.m * P.recoilEnergy ω₀ θ (2 * ((P.ℏ * ω₀) / P.c) * cos θ / 3) =
        6 * ((P.ℏ * ω₀) / P.c) ^ 2 := by
      have h := hf' ω₀ (2 * ((P.ℏ * ω₀) / P.c) * cos θ / 3)
      nlinarith [h]
    have hA : 6 * ((P.ℏ * ω₀) / P.c) ^ 2 ≤ 12 * P.m * r₀ := by
      rw [← hatt]; exact hlb q0
    have hB : 12 * P.m * r₀ ≤ 6 * ((P.ℏ * ω₀) / P.c) ^ 2 := by
      have hge : r₀ ≤ P.recoilEnergy ω₀ θ (2 * ((P.ℏ * ω₀) / P.c) * cos θ / 3) := by
        by_cases hc0 : 0 ≤ 2 * ((P.ℏ * ω₀) / P.c) * cos θ / 3
        · exact hq₀b _ hc0
        · -- minimizer would be negative; constrained min is at q = 0
          have h0v := hq₀b 0 (le_refl 0)
          have h0att := hf' ω₀ 0
          have hqn := hf' ω₀ (2 * ((P.ℏ * ω₀) / P.c) * cos θ / 3)
          nlinarith [hb_sub (q0c := 2 * ((P.ℏ * ω₀) / P.c) * cos θ / 3) hc0, h0v, h0att, hqn,
            hA]
      nlinarith [mul_le_mul_of_nonneg_left hge (le_of_lt (mul_pos (by norm_num) P.m_pos)), hv]
    have hm12 : (12 * P.m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt P.m_pos)
    exact (mul_right_cancel₀ hm12 (by nlinarith)).symm
    where hb_sub {q0c : ℝ} (h : ¬0 ≤ q0c) : q0c ≤ 0 := le_of_lt (not_le.mp h)
  -- balance equation at ω₀
  set κ : ℝ := (3 - 2 * cos θ ^ 2) / (6 * P.m * P.c ^ 2) with hκdef
  have heq0 : κ * (P.ℏ * ω₀) ^ 2 - (P.ℏ * ω₀) + P.ΔU = 0 := by
    have hm : (P.m : ℝ) ≠ 0 := ne_of_gt P.m_pos
    have hc : (P.c : ℝ) ≠ 0 := ne_of_gt P.c_pos
    have hE : P.photonEnergy ω₀ = P.ℏ * ω₀ := rfl
    rw [hE] at hE₀
    rw [hr₀, hκdef] at hE₀
    field_simp at hE₀
    nlinarith [hE₀]

-/

/-- Membership in the feasible-frequency set carries the physical
nonnegativity condition explicitly.  No monotonicity or branch choice is
inferred from it. -/
theorem threshold_frequency_nonnegative {P : DissociationParameters} {θ ω : ℝ}
    (h : 0 ≤ ω ∧ DissociationThreshold P ω θ) : 0 ≤ ω := h.1

/-- `ω_min` `[rad·s⁻¹]` is the **minimum angular frequency required for
dissociation** at outgoing `O₂` angle `θ` — the quantity characterised by
part C.1: the least nonnegative angular frequency satisfying the threshold
predicate. -/
def IsMinFrequency (P : DissociationParameters) (ω_min θ : ℝ) : Prop :=
  IsLeast {ω : ℝ | 0 ≤ ω ∧ DissociationThreshold P ω θ} ω_min

/-- Dimensional soundness of the stipulated governing relations at `(ω, θ)`:
the photon momentum `ℏω/c` plays a nonnegative momentum role, the fragment
masses play positive mass roles, and the total recoil energy of every
momentum-conserving final state with nonnegative `O₂` momentum is nonnegative
— consistent with the dimensional roles (momentum, mass, energy) stipulated
by the problem. -/
def GoverningRelationsDimensional (P : DissociationParameters) (ω θ : ℝ) : Prop :=
  0 ≤ P.photonMomentum ω ∧
    0 < P.oxygenMoleculeMass ∧ 0 < P.m ∧
      ∀ q : ℝ, 0 ≤ q → 0 ≤ P.recoilEnergy ω θ q

/-- Uniqueness of the minimum dissociation frequency at a fixed angle,
whenever it exists: any two candidates are least elements of the same set.
Body deferred to the proving stage. -/
theorem isMinFrequency_unique {P : DissociationParameters} {θ ω₁ ω₂ : ℝ}
    (h₁ : IsMinFrequency P ω₁ θ) (h₂ : IsMinFrequency P ω₂ θ) : ω₁ = ω₂ := by
  obtain ⟨⟨⟨hω₁, hT₁⟩, hlb₁⟩, ⟨⟨hω₂, hT₂⟩, hlb₂⟩⟩ := And.intro h₁ h₂
  exact le_antisymm (hlb₁ ⟨hω₂, hT₂⟩) (hlb₂ ⟨hω₁, hT₁⟩)

/-- **Numerical data of part C.2.**  The conventional scale anchors are
carried abstractly as strictly positive reals, with fixed dimensional roles:

* `amu` — atomic mass unit `[kg]`;
* `eV` — electron-volt `[J]`;
* `hPlanck` — Planck constant `h` `[J·s]`;
* `cLight` — speed of light `c` `[m·s⁻¹]`.

The question's own data are pinned in `PartC2Data.params`: oxygen-atom mass
`m = 16.0 amu`, threshold `ΔU = 1.10 eV`, reduced Planck constant
`ℏ = h / (2π)`, and the speed of light `c`. -/
structure PartC2Data where
  /-- Atomic mass unit `[kg]`, strictly positive. -/
  amu : ℝ
  /-- Electron-volt `[J]`, strictly positive. -/
  eV : ℝ
  /-- Planck constant `h` `[J·s]`, strictly positive. -/
  hPlanck : ℝ
  /-- Speed of light `c` `[m·s⁻¹]`, strictly positive. -/
  cLight : ℝ
  amu_pos : 0 < amu
  eV_pos : 0 < eV
  hPlanck_pos : 0 < hPlanck
  cLight_pos : 0 < cLight
  /-- **Non-relativistic regime of the dissociation.**  The threshold energy
  `1.10 eV` of the molecular bond is vastly smaller than the oxygen-atom rest
  energy `16.0 amu · c²` (an electronic transition against a nuclear
  rest-mass scale), which is exactly the regime in which the stipulated
  classical, non-relativistic treatment of the fragments is consistent.
  Equivalently (with `θ = π/6`) the discriminant `1 − 4κΔU` of the threshold
  energy-balance equation is strictly positive, so the threshold condition
  has a real root.  Carried as a hypothesis (a regime side-condition of the
  model), not as the conclusion of part C.2. -/
  ΔU_lt_mc2 : 1.10 * eV < (16.0 * amu) * cLight ^ 2

namespace PartC2Data

/-- Reduced Planck constant `ℏ = h / (2π)` `[J·s]`. -/
noncomputable def ℏ (D : PartC2Data) : ℝ := D.hPlanck / (2 * π)

/-- The dissociation parameters of part C.2: `m = 16.0 amu`, `ΔU = 1.10 eV`,
`ℏ = h/(2π)` and the tabulated speed of light. -/
noncomputable def params (D : PartC2Data) : DissociationParameters where
  ℏ := D.ℏ
  c := D.cLight
  m := 16.0 * D.amu
  ΔU := 1.10 * D.eV
  ℏ_pos := by
    have h2π : (0 : ℝ) < 2 * π := mul_pos two_pos Real.pi_pos
    exact div_pos D.hPlanck_pos h2π
  c_pos := D.cLight_pos
  m_pos := mul_pos (by norm_num) D.amu_pos
  ΔU_nonneg := mul_nonneg (by norm_num) (le_of_lt D.eV_pos)

/-- The C.2 dissociation threshold `1.10 eV` is strictly positive `[J]`. -/
theorem params_ΔU_pos (D : PartC2Data) : 0 < D.params.ΔU := by
  change (0 : ℝ) < 1.10 * D.eV
  exact mul_pos (by norm_num) D.eV_pos

/-- The given outgoing `O₂` angle of part C.2, `θ = π / 6` `[rad]`. -/
noncomputable def θGiven (_D : PartC2Data) : ℝ := π / 6

/-- The given angle `θ = π/6` is strictly positive `[rad]`. -/
theorem θGiven_pos (D : PartC2Data) : 0 < D.θGiven := by
  change (0 : ℝ) < π / 6
  exact div_pos Real.pi_pos (by norm_num)

/-- **Governing-law hypotheses for the C.2 data.**  At the given outgoing
`O₂` angle `θ = π/6`: the stipulated governing relations are dimensionally
sound over the physical (nonnegative) frequency range, and there exists a
threshold-compatible photon frequency — so that the minimum frequency
`ω_min` of part C.1, and hence the excess photon energy requested here, are
physically well-defined for the C.2 data.  Body deferred to the proving
stage. -/
theorem governingLawsHold (D : PartC2Data) :
    (∀ ω : ℝ, 0 ≤ ω → GoverningRelationsDimensional (P := D.params) ω D.θGiven) ∧
      ∃ ω : ℝ, 0 ≤ ω ∧ DissociationThreshold (P := D.params) ω D.θGiven := by
  constructor
  · intro ω hω
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact div_nonneg (mul_nonneg D.params.ℏ_pos.le hω) D.cLight_pos.le
    · exact mul_pos two_pos D.params.m_pos
    · exact D.params.m_pos
    · intro q hq
      have hm : 0 ≤ 2 * D.params.m := mul_nonneg two_pos.le D.params.m_pos.le
      have h1 : (0:ℝ) ≤ D.params.oxygenMoleculeMass := mul_nonneg two_pos.le D.params.m_pos.le
      have hM2 : 0 ≤ 2 * D.params.oxygenMoleculeMass := mul_nonneg two_pos.le h1
      have h1' : 0 ≤ q ^ 2 / (2 * D.params.oxygenMoleculeMass) :=
        div_nonneg (sq_nonneg q) hM2
      have h2' : 0 ≤ (D.params.oxygenMomentumMagnitude ω D.θGiven q) ^ 2 / (2 * D.params.m) :=
        div_nonneg (sq_nonneg _) hm
      exact add_nonneg h1' h2'
  · set P : DissociationParameters := D.params with hPd
    have hm_pos : 0 < P.m := P.m_pos
    have hm_ne : (P.m : ℝ) ≠ 0 := ne_of_gt hm_pos
    have hℏ_pos : 0 < P.ℏ := P.ℏ_pos
    have hℏ_ne : (P.ℏ : ℝ) ≠ 0 := ne_of_gt hℏ_pos
    have hc_pos : 0 < P.c := P.c_pos
    have hc_ne : (P.c : ℝ) ≠ 0 := ne_of_gt hc_pos
    have hΔU : 0 ≤ P.ΔU := P.ΔU_nonneg
    have hcs : cos D.θGiven ^ 2 + sin D.θGiven ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    have hco : cos D.θGiven = √3 / 2 := Real.cos_pi_div_six
    have hco_pos : 0 < cos D.θGiven := by rw [hco]; positivity
    set κ : ℝ := (3 - 2 * cos D.θGiven ^ 2) / (6 * P.m * P.c ^ 2) with hκ_def
    set φ : ℝ := (1 - Real.sqrt (1 - 4 * κ * P.ΔU)) / (2 * κ) with hφ_def
    have hκ_pos : 0 < κ := by
      rw [hκ_def]
      apply div_pos _ (by positivity)
      have hc1 : cos D.θGiven ^ 2 ≤ 1 := by
        nlinarith [hcs, sq_nonneg (sin D.θGiven), sq_nonneg (cos D.θGiven)]
      nlinarith
    have hκ_ne : (κ : ℝ) ≠ 0 := ne_of_gt hκ_pos
    have hκD : 4 * κ * P.ΔU < 1 := by
      have hΔUE : P.ΔU = 1.10 * D.eV := rfl
      have hmE : P.m = 16.0 * D.amu := rfl
      have hcE : P.c = D.cLight := rfl
      rw [hκ_def, hco]
      have h32 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have hcos32 : (3 - 2 * (√3 / 2) ^ 2) = (3 : ℝ) / 2 := by
        have hp : (2 : ℝ) ^ 2 = 4 := by norm_num
        rw [div_pow, h32, hp]; norm_num
      rw [hcos32]
      have hκval : ((3 : ℝ) / 2) / (6 * P.m * P.c ^ 2) = 1 / (4 * P.m * P.c ^ 2) := by
        field_simp
        ring
      rw [hκval]
      have hmc : (0 : ℝ) < 4 * P.m * P.c ^ 2 := by positivity
      rw [show 4 * (1 / (4 * P.m * P.c ^ 2)) * P.ΔU = P.ΔU / (P.m * P.c ^ 2) by
        field_simp]
      rw [hΔUE, hmE, hcE]
      rw [div_lt_one (by positivity : (0 : ℝ) < 16.0 * D.amu * D.cLight ^ 2)]
      exact D.ΔU_lt_mc2
    set σ : ℝ := Real.sqrt (1 - 4 * κ * P.ΔU) with hσ_def
    have hσ2 : σ ^ 2 = 1 - 4 * κ * P.ΔU := Real.sq_sqrt (by linarith [hκD])
    have hσ_le : σ ≤ 1 := by
      have h := Real.sqrt_le_sqrt (show (1 - 4 * κ * P.ΔU) ≤ 1 by
        nlinarith [mul_nonneg hκ_pos.le hΔU])
      rwa [Real.sqrt_one] at h
    have hφ_nn : 0 ≤ φ := by
      rw [hφ_def]
      exact div_nonneg (by linarith [hσ_le]) (by positivity)
    have hq : κ * φ ^ 2 - φ + P.ΔU = 0 := by
      have hφ2 : 2 * κ * φ = 1 - σ := by rw [hφ_def]; field_simp
      nlinarith [hσ2]
    set ω₀ : ℝ := φ / P.ℏ with hω₀_def
    have hω₀_nn : 0 ≤ ω₀ := div_nonneg hφ_nn hℏ_pos.le
    have hE : P.photonEnergy ω₀ = φ := by
      change P.ℏ * ω₀ = φ
      rw [hω₀_def]; field_simp
    have hfep : ∀ q : ℝ, 12 * P.m * P.recoilEnergy ω₀ D.θGiven q =
        9 * q ^ 2 + 6 * P.photonMomentum ω₀ ^ 2 - 12 * P.photonMomentum ω₀ * cos D.θGiven * q := by
      intro q
      have h1 : P.recoilEnergy ω₀ D.θGiven q =
          q ^ 2 / (4 * P.m) + (P.oxygenMomentumMagnitude ω₀ D.θGiven q) ^ 2 / (2 * P.m) := by
        change q ^ 2 / (2 * (2 * P.m)) +
          (P.oxygenMomentumMagnitude ω₀ D.θGiven q) ^ 2 / (2 * P.m) = _
        ring_nf
      have h2 : (P.oxygenMomentumMagnitude ω₀ D.θGiven q) ^ 2 =
          (P.photonMomentum ω₀ - q * cos D.θGiven) ^ 2 + (q * sin D.θGiven) ^ 2 := by
        change (Real.sqrt ((P.photonMomentum ω₀ - q * cos D.θGiven) ^ 2 +
          (q * sin D.θGiven) ^ 2)) ^ 2 = _
        exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
      rw [h1, h2]
      field_simp
      nlinarith [hcs]
    have hp2 : P.photonMomentum ω₀ ^ 2 / (4 * P.m) = κ * φ ^ 2 := by
      change (P.photonEnergy ω₀ / P.c) ^ 2 / (4 * P.m) = κ * φ ^ 2
      rw [hE, hκ_def]
      have hco2 : cos D.θGiven ^ 2 = 3 / 4 := by
        have h32 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        rw [hco]
        nlinarith
      field_simp
      rw [hco2]
      ring
    refine ⟨ω₀, hω₀_nn, ?_⟩
    have hcore : (∃ q : ℝ, 0 ≤ q ∧ P.recoilEnergy ω₀ D.θGiven q =
        P.photonMomentum ω₀ ^ 2 / (4 * P.m)) ∧
        ∀ q : ℝ, 0 ≤ q → P.photonMomentum ω₀ ^ 2 / (4 * P.m) ≤ P.recoilEnergy ω₀ D.θGiven q := by
      have hq0v : (0:ℝ) ≤ 2 * P.photonMomentum ω₀ * cos D.θGiven / 3 := by
        have hp_nn : 0 ≤ P.photonMomentum ω₀ := by
          change 0 ≤ P.photonEnergy ω₀ / P.c
          rw [hE]; exact div_nonneg hφ_nn hc_pos.le
        positivity
      have hsq : ∀ q : ℝ, 12 * P.m * P.recoilEnergy ω₀ D.θGiven q
          = 9 * (q - 2 * P.photonMomentum ω₀ * cos D.θGiven / 3) ^ 2 + 12 * P.m *
            (P.photonMomentum ω₀ ^ 2 / (4 * P.m)) := by
        intro q
        have h := hfep q
        have hrw : 12 * P.m * (P.photonMomentum ω₀ ^ 2 / (4 * P.m)) =
            6 * P.photonMomentum ω₀ ^ 2 - 12 * (P.photonMomentum ω₀ * cos D.θGiven) ^ 2 / 3 := by
          rw [hco]
          have hm12' : (12 * P.m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hm_ne
          field_simp
          ring_nf
          rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
          ring
        rw [hrw]
        nlinarith [h]
      constructor
      · refine ⟨2 * P.photonMomentum ω₀ * cos D.θGiven / 3, hq0v, ?_⟩
        have h := hsq (2 * P.photonMomentum ω₀ * cos D.θGiven / 3)
        rw [sub_self] at h
        have hz : (9:ℝ) * (0:ℝ) ^ 2 = 0 := by norm_num
        rw [hz, zero_add] at h
        have hm12 : (12 * P.m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hm_ne
        exact (mul_left_cancel₀ hm12 h)
      · intro q hq
        have h := hsq q
        have hs0 : (0:ℝ) ≤ (q - 2 * P.photonMomentum ω₀ * cos D.θGiven / 3) ^ 2 :=
          sq_nonneg (q - 2 * P.photonMomentum ω₀ * cos D.θGiven / 3)
        have hm12 : (0:ℝ) < 12 * P.m := mul_pos (by norm_num) hm_pos
        have hge : 12 * P.m * (P.photonMomentum ω₀ ^ 2 / (4 * P.m)) ≤
            12 * P.m * P.recoilEnergy ω₀ D.θGiven q := by
          rw [h]; linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 9) hs0]
        exact le_of_mul_le_mul_left hge hm12
    refine ⟨P.photonMomentum ω₀ ^ 2 / (4 * P.m), hcore, ?_⟩
    rw [hE, hp2]; linarith [hq]

/-- **Solution predicate of part C.2, joules.**  `E` `[J]` is the excess
photon energy `ℏ·ω_min − ΔU`, evaluated at the minimum dissociation frequency
`ω_min` for the given angle `θ = π/6` and the C.2 data. -/
def IsExcessEnergy (D : PartC2Data) (E : ℝ) : Prop :=
  ∃ ω_min : ℝ,
    IsMinFrequency (P := D.params) ω_min D.θGiven ∧
      E = D.params.photonEnergy ω_min - D.params.ΔU

set_option maxHeartbeats 800000 in
/-- **The smaller quadratic boundary is the minimum threshold frequency.**
The feasible set `{ω ≥ 0 | DissociationThreshold ω θ}` contains its infimum.
The proof must minimize the recoil quadratic, exhibit the smaller nonnegative
root of the resulting energy-balance equation, prove that root is feasible,
and show every other feasible frequency is at least it.  In particular it
does not use an upward-closure claim: the same quadratic has a larger root and
is not globally monotone through the interval between the roots. -/
theorem isMinFrequency_sInf (D : PartC2Data) :
    IsMinFrequency (P := D.params) (sInf {ω : ℝ | 0 ≤ ω ∧
      DissociationThreshold (P := D.params) ω D.θGiven}) D.θGiven := by
  -- The feasible set is identified with the boundary of the minimized recoil
  -- quadratic: minimizing the recoil energy over the fragment momentum `q`
  -- turns the threshold balance into the scalar quadratic
  -- `κ·(ℏω)² − ℏω + ΔU = 0`, whose *smaller* root `ω₀ = φ/ℏ` is feasible and
  -- below every other feasible frequency.
  set P : DissociationParameters := D.params with hPd
  have hm_pos : 0 < P.m := P.m_pos
  have hm_ne : (P.m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hℏ_pos : 0 < P.ℏ := P.ℏ_pos
  have hc_pos : 0 < P.c := P.c_pos
  have hΔU : 0 ≤ P.ΔU := P.ΔU_nonneg
  have hcs : cos D.θGiven ^ 2 + sin D.θGiven ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hco : cos D.θGiven = √3 / 2 := Real.cos_pi_div_six
  have hco_pos : 0 < cos D.θGiven := by rw [hco]; positivity
  set κ : ℝ := (3 - 2 * cos D.θGiven ^ 2) / (6 * P.m * P.c ^ 2) with hκ_def
  set φ : ℝ := (1 - Real.sqrt (1 - 4 * κ * P.ΔU)) / (2 * κ) with hφ_def
  have hκ_pos : 0 < κ := by
    rw [hκ_def]
    apply div_pos _ (by positivity)
    have hc1 : cos D.θGiven ^ 2 ≤ 1 := by
      nlinarith [hcs, sq_nonneg (sin D.θGiven), sq_nonneg (cos D.θGiven)]
    nlinarith
  have hκD : 4 * κ * P.ΔU < 1 := by
    have hΔUE : P.ΔU = 1.10 * D.eV := rfl
    have hmE : P.m = 16.0 * D.amu := rfl
    have hcE : P.c = D.cLight := rfl
    rw [hκ_def, hco]
    have h32 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hcos32 : (3 - 2 * (√3 / 2) ^ 2) = (3 : ℝ) / 2 := by
      have hp : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [div_pow, h32, hp]; norm_num
    rw [hcos32]
    have hκval : ((3 : ℝ) / 2) / (6 * P.m * P.c ^ 2) = 1 / (4 * P.m * P.c ^ 2) := by
      field_simp
      ring
    rw [hκval]
    rw [show 4 * (1 / (4 * P.m * P.c ^ 2)) * P.ΔU = P.ΔU / (P.m * P.c ^ 2) by
      field_simp]
    rw [hΔUE, hmE, hcE]
    rw [div_lt_one (by positivity : (0 : ℝ) < 16.0 * D.amu * D.cLight ^ 2)]
    exact D.ΔU_lt_mc2
  set σ : ℝ := Real.sqrt (1 - 4 * κ * P.ΔU) with hσ_def
  have hσ2 : σ ^ 2 = 1 - 4 * κ * P.ΔU := Real.sq_sqrt (by linarith [hκD])
  have hσ_le : σ ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show (1 - 4 * κ * P.ΔU) ≤ 1 by
      nlinarith [mul_nonneg hκ_pos.le hΔU])
    rwa [Real.sqrt_one] at h
  have hΔU_pos : 0 < P.ΔU := D.params_ΔU_pos
  have hσ_lt : σ < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by nlinarith [mul_nonneg hκ_pos.le hΔU])
      (by nlinarith [mul_pos hκ_pos hΔU_pos])
  have hφ_nn : 0 ≤ φ := by
    rw [hφ_def]
    exact div_nonneg (by linarith [hσ_le]) (by positivity)
  have hq : κ * φ ^ 2 - φ + P.ΔU = 0 := by
    have hφ2 : 2 * κ * φ = 1 - σ := by rw [hφ_def]; field_simp
    nlinarith [hσ2]
  set ω₀ : ℝ := φ / P.ℏ with hω₀_def
  have hω₀_nn : 0 ≤ ω₀ := div_nonneg hφ_nn hℏ_pos.le
  have hE : P.photonEnergy ω₀ = φ := by
    change P.ℏ * ω₀ = φ
    rw [hω₀_def]; field_simp
  -- Completed-square form of the recoil energy at an arbitrary frequency.
  have hsq : ∀ ω q : ℝ, 12 * P.m * P.recoilEnergy ω D.θGiven q
      = 9 * (q - 2 * P.photonMomentum ω * cos D.θGiven / 3) ^ 2 + 12 * P.m *
        (P.photonMomentum ω ^ 2 / (4 * P.m)) := by
    intro ω q
    have h1 : P.recoilEnergy ω D.θGiven q =
        q ^ 2 / (4 * P.m) + (P.oxygenMomentumMagnitude ω D.θGiven q) ^ 2 / (2 * P.m) := by
      change q ^ 2 / (2 * (2 * P.m)) +
        (P.oxygenMomentumMagnitude ω D.θGiven q) ^ 2 / (2 * P.m) = _
      ring_nf
    have h2 : (P.oxygenMomentumMagnitude ω D.θGiven q) ^ 2 =
        (P.photonMomentum ω - q * cos D.θGiven) ^ 2 + (q * sin D.θGiven) ^ 2 := by
      change (Real.sqrt ((P.photonMomentum ω - q * cos D.θGiven) ^ 2 +
        (q * sin D.θGiven) ^ 2)) ^ 2 = _
      exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hfep : 12 * P.m * P.recoilEnergy ω D.θGiven q =
        9 * q ^ 2 + 6 * P.photonMomentum ω ^ 2 -
          12 * P.photonMomentum ω * cos D.θGiven * q := by
      rw [h1, h2]
      field_simp
      nlinarith [hcs]
    have hrw : 12 * P.m * (P.photonMomentum ω ^ 2 / (4 * P.m)) =
        6 * P.photonMomentum ω ^ 2 - 12 * (P.photonMomentum ω * cos D.θGiven) ^ 2 / 3 := by
      rw [hco]
      have hm12' : (12 * P.m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hm_ne
      field_simp
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
      ring
    rw [hrw]
    nlinarith [hfep]
  -- The least recoil energy at frequency `ω` is `p_γ(ω)² / (4 m)`.
  have hleast_recoil : ∀ ω : ℝ, 0 ≤ ω →
      IsLeastRecoilEnergy P ω D.θGiven (P.photonMomentum ω ^ 2 / (4 * P.m)) := by
    intro ω hω
    have hp_nn : 0 ≤ P.photonMomentum ω := by
      change 0 ≤ P.photonEnergy ω / P.c
      exact div_nonneg (mul_nonneg hℏ_pos.le hω) hc_pos.le
    have hq0v : (0:ℝ) ≤ 2 * P.photonMomentum ω * cos D.θGiven / 3 := by positivity
    constructor
    · refine ⟨2 * P.photonMomentum ω * cos D.θGiven / 3, hq0v, ?_⟩
      have h := hsq ω (2 * P.photonMomentum ω * cos D.θGiven / 3)
      rw [sub_self] at h
      have hz : (9:ℝ) * (0:ℝ) ^ 2 = 0 := by norm_num
      rw [hz, zero_add] at h
      have hm12 : (12 * P.m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hm_ne
      exact (mul_left_cancel₀ hm12 h)
    · intro q _hq
      have h := hsq ω q
      have hs0 : (0:ℝ) ≤ (q - 2 * P.photonMomentum ω * cos D.θGiven / 3) ^ 2 :=
        sq_nonneg (q - 2 * P.photonMomentum ω * cos D.θGiven / 3)
      have hm12 : (0:ℝ) < 12 * P.m := mul_pos (by norm_num) hm_pos
      have hge : 12 * P.m * (P.photonMomentum ω ^ 2 / (4 * P.m)) ≤
          12 * P.m * P.recoilEnergy ω D.θGiven q := by
        rw [h]; linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 9) hs0]
      exact le_of_mul_le_mul_left hge hm12
  -- The threshold balance forces the quadratic equation in `ℏω`.
  have hquad : ∀ ω : ℝ, DissociationThreshold P ω D.θGiven → 0 ≤ ω →
      κ * (P.ℏ * ω) ^ 2 - (P.ℏ * ω) + P.ΔU = 0 := by
    intro ω hω hωnn
    obtain ⟨r, hrl, hbal⟩ := hω
    have hU : ∀ q : ℝ, 0 ≤ q → r ≤ P.recoilEnergy ω D.θGiven q := hrl.2
    obtain ⟨q₀, hq₀nn, hq₀att⟩ := hrl.1
    have hp_nn : 0 ≤ P.photonMomentum ω := by
      change 0 ≤ P.photonEnergy ω / P.c
      exact div_nonneg (mul_nonneg hℏ_pos.le hωnn) hc_pos.le
    have hq0v : (0:ℝ) ≤ 2 * P.photonMomentum ω * cos D.θGiven / 3 := by positivity
    have hm12 : (0:ℝ) < 12 * P.m := mul_pos (by norm_num) hm_pos
    have hrc : r = P.photonMomentum ω ^ 2 / (4 * P.m) := by
      apply le_antisymm
      · suffices hlb : 12 * P.m * r ≤ 12 * P.m * (P.photonMomentum ω ^ 2 / (4 * P.m)) by
          exact le_of_mul_le_mul_left hlb hm12
        have hu' := hU _ hq0v
        have hv := hsq ω (2 * P.photonMomentum ω * cos D.θGiven / 3)
        rw [sub_self] at hv
        have hz : (9:ℝ) * (0:ℝ) ^ 2 = 0 := by norm_num
        rw [hz, zero_add] at hv
        calc 12 * P.m * r ≤ 12 * P.m * P.recoilEnergy ω D.θGiven
              (2 * P.photonMomentum ω * cos D.θGiven / 3) :=
            mul_le_mul_of_nonneg_left hu' hm12.le
          _ = 12 * P.m * (P.photonMomentum ω ^ 2 / (4 * P.m)) := hv
      · suffices hlb : 12 * P.m * (P.photonMomentum ω ^ 2 / (4 * P.m)) ≤ 12 * P.m * r by
          exact le_of_mul_le_mul_left hlb hm12
        rw [← hq₀att, hsq ω q₀]
        nlinarith [sq_nonneg (q₀ - 2 * P.photonMomentum ω * cos D.θGiven / 3)]
    have hbal' : P.ℏ * ω = P.ΔU + ((P.ℏ * ω) / P.c) ^ 2 / (4 * P.m) := by
      have hpm : (P.photonMomentum ω) ^ 2 = ((P.ℏ * ω) / P.c) ^ 2 := by
        rw [show P.photonMomentum ω = (P.ℏ * ω) / P.c from rfl]
      rw [hrc, hpm] at hbal
      exact hbal
    have hcm : (6 * P.m * P.c ^ 2 : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hm_ne) (pow_ne_zero 2 (ne_of_gt hc_pos))
    have hbig : 6 * P.m * P.c ^ 2 *
        (κ * (P.ℏ * ω) ^ 2 - P.ℏ * ω + P.ΔU) = 0 := by
      rw [hκ_def]
      have hrw : 6 * P.m * P.c ^ 2 *
          ((3 - 2 * cos D.θGiven ^ 2) / (6 * P.m * P.c ^ 2) * (P.ℏ * ω) ^ 2 -
            P.ℏ * ω + P.ΔU)
          = (3 - 2 * cos D.θGiven ^ 2) * (P.ℏ * ω) ^ 2 -
              6 * P.m * P.c ^ 2 * (P.ℏ * ω - P.ΔU) := by
        field_simp
        ring_nf
      rw [hrw]
      have hU' : 6 * P.m * P.c ^ 2 * (P.ℏ * ω - P.ΔU) = (3 / 2) * (P.ℏ * ω) ^ 2 := by
        have hU2 : P.ℏ * ω - P.ΔU = ((P.ℏ * ω) / P.c) ^ 2 / (4 * P.m) := by
          linarith [hbal']
        rw [hU2]
        field_simp
        ring
      have hco2c : cos D.θGiven ^ 2 = 3 / 4 := by
        have h32 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        rw [hco]
        nlinarith
      nlinarith [hU', hco2c]
    have hbig' : 6 * P.m * P.c ^ 2 * (κ * (P.ℏ * ω) ^ 2 - P.ℏ * ω + P.ΔU)
        = 6 * P.m * P.c ^ 2 * 0 := by rw [hbig, mul_zero]
    exact mul_left_cancel₀ hcm hbig'
  -- The smaller root is feasible.
  have hp2 : P.photonMomentum ω₀ ^ 2 / (4 * P.m) = κ * φ ^ 2 := by
    change (P.photonEnergy ω₀ / P.c) ^ 2 / (4 * P.m) = κ * φ ^ 2
    rw [hE, hκ_def]
    have hco2 : cos D.θGiven ^ 2 = 3 / 4 := by
      have h32 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      rw [hco]
      nlinarith
    field_simp
    rw [hco2]
    ring
  have hth₀ : DissociationThreshold P ω₀ D.θGiven :=
    ⟨P.photonMomentum ω₀ ^ 2 / (4 * P.m), hleast_recoil ω₀ hω₀_nn, by
      rw [hE, hp2]; linarith [hq]⟩
  set S : Set ℝ := {ω : ℝ | 0 ≤ ω ∧ DissociationThreshold P ω D.θGiven} with hS
  have hne : S.Nonempty := ⟨ω₀, hω₀_nn, hth₀⟩
  have hbdd : BddBelow S := ⟨0, fun ω hω => hω.1⟩
  have hglb : IsGLB S (sInf S) := Real.isGLB_sInf hne hbdd
  -- Every feasible frequency lies at or above the smaller root.
  /- USER: Do not reuse the current `hfac`/`hCpos` branch: its first factor is
  zero at `ω₀`, and its claimed lower bound has the wrong sign.  Factor the
  quadratic at the arbitrary feasible energy `x = P.ℏ * ω` instead:
  `(2*κ*x-(1-σ)) * (2*κ*x-(1+σ)) =
    4*κ*(κ*x^2-x+P.ΔU)` using `hσ2`.
  If `ω < ω₀`, positivity of `P.ℏ` and `κ`, `P.ℏ*ω₀ = φ`, and
  `κ*φ = (1-σ)/2` make both left factors strictly negative, while `heq`
  makes the right side zero.  Their product is then strictly positive, a
  direct contradiction. -/
  have hub : ∀ ω ∈ S, ω₀ ≤ ω := by
    intro ω hωS
    have hωnn : 0 ≤ ω := hωS.1
    have heq := hquad ω hωS.2 hωnn
    have hφval : κ * φ = (1 - σ) / 2 := by rw [hφ_def]; field_simp
    have hσ_nn : 0 ≤ σ := Real.sqrt_nonneg _
    have hE' : P.ℏ * ω₀ = φ := hE
    -- Square completion at the arbitrary feasible energy x := P.ℏ * ω:
    -- κ*x^2 - x + ΔU = 0, with σ^2 = 1 - 4*κ*ΔU, gives
    -- (2*κ*x - 1)^2 = σ^2.
    have hsqx : (2 * κ * (P.ℏ * ω) - /-TP1-/ 1) ^ /-TP2-/ 2 = σ ^ 2 := by
      nlinarith [heq, hσ2]
    -- Hence x is one of the two roots; in both cases x ≥ φ.
    have hxge : φ ≤ P.ℏ * ω := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqx with hcase | hcase
      · -- larger root: 2*κ*x = 1 + σ ≥ 1 - σ = 2*κ*φ, cancel 2*κ > 0.
        have hbig : 2 * κ * φ ≤ 2 * κ * (P.ℏ * ω) := by
          nlinarith [hcase, hφval, hσ_nn]
        rwa [mul_le_mul_iff_of_pos_left (mul_pos two_pos hκ_pos)] at hbig
      · -- smaller root: 2*κ*x = 1 - σ = 2*κ*φ, equality.
        have heq2 : 2 * κ * φ = 2 * κ * (P.ℏ * ω) := by
          nlinarith [hcase, hφval]
        exact le_of_eq (mul_left_cancel₀ (ne_of_gt (mul_pos two_pos hκ_pos)) heq2)
    -- Convert φ ≤ P.ℏ * ω to ω₀ ≤ ω using φ = P.ℏ * ω₀ and P.ℏ > 0.
    have hle : P.ℏ * ω₀ ≤ P.ℏ * ω := hE' ▸ hxge
    exact le_of_mul_le_mul_left hle hℏ_pos
  -- Hence `sInf S = ω₀`, and membership follows.
  have hEq : sInf S = ω₀ := le_antisymm (hglb.1 ⟨hω₀_nn, hth₀⟩) (hglb.2 hub)
  have hmem : sInf S ∈ S := hEq ▸ ⟨hω₀_nn, hth₀⟩
  exact ⟨⟨hmem.1, hmem.2⟩, hglb.1⟩

/-- **Answer-free characterization of part C.2, energy in joules.**  With
the C.2 data there is a unique excess photon energy `ℏ·ω_min − ΔU` `[J]`.
The witness value (equivalently, `ω_min`) is withheld; it is constructed in
the proving stage. -/
theorem existsUnique_excessEnergy (D : PartC2Data) : ∃! E : ℝ, D.IsExcessEnergy E := by
  set S : Set ℝ := {ω : ℝ | 0 ≤ ω ∧ DissociationThreshold D.params ω D.θGiven} with hS
  have hleast : IsMinFrequency D.params (sInf S) D.θGiven := by
    simpa [hS] using D.isMinFrequency_sInf
  refine ⟨D.params.photonEnergy (sInf S) - D.params.ΔU, ⟨sInf S, hleast, rfl⟩, ?_⟩
  intro E' hE'
  obtain ⟨ω', hω', rfl⟩ := hE'
  have huniq : ω' = sInf S := isMinFrequency_unique hω' hleast
  rw [huniq]

/-- **Solution predicate for the eV report.**  `x` is the requested pure
number: the excess photon energy `E` `[J]`, expressed in electron-volts, with
`E = x·eV` — the reading of "`ℏ·ω_min − ΔU` in eV". -/
def IsExcessEnergyElectronVolts (D : PartC2Data) (x : ℝ) : Prop :=
  ∃ E : ℝ, D.IsExcessEnergy E ∧ E = x * D.eV

/-- **Answer-free characterization of part C.2, energy in electron-volts.**
There is a unique number `x` of electron-volts reporting the excess photon
energy `ℏ·ω_min − ΔU`.  The numerical value is withheld; it is constructed in
the proving stage. -/
theorem existsUnique_excessEnergyElectronVolts (D : PartC2Data) :
    ∃! x : ℝ, D.IsExcessEnergyElectronVolts x := by
  obtain ⟨E, hE, _⟩ := D.existsUnique_excessEnergy
  have huniq : ∀ E₁ E₂ : ℝ, D.IsExcessEnergy E₁ → D.IsExcessEnergy E₂ → E₁ = E₂ := by
    intro E₁ E₂ hE₁ hE₂
    obtain ⟨ω₁, hω₁, h1⟩ := hE₁
    obtain ⟨ω₂, hω₂, h2⟩ := hE₂
    have hω : ω₁ = ω₂ := isMinFrequency_unique hω₁ hω₂
    rw [h1, h2, hω]
  refine ⟨E / D.eV, ⟨E, hE, ?_⟩, ?_⟩
  · rw [div_mul_cancel₀ E (ne_of_gt D.eV_pos)]
  · intro x' hx'
    obtain ⟨E', hE', hxE'⟩ := hx'
    have hEE : E' = E := huniq E' E hE' hE
    have hx2 : x' * D.eV = E := by rw [← hxE', hEE]
    have hne : (D.eV : ℝ) ≠ 0 := ne_of_gt D.eV_pos
    rw [eq_div_iff_mul_eq hne]
    exact hx2

/-- Equivalent characterization of the eV report: `x` reports the excess
photon energy in electron-volts iff the joule value `E` satisfying the
solution predicate equals `x·eV`.  Glue for the proving stage. -/
theorem isExcessEnergyElectronVolts_iff (D : PartC2Data) {E x : ℝ} (hE : D.IsExcessEnergy E) :
    D.IsExcessEnergyElectronVolts x ↔ E = x * D.eV := by
  constructor
  · rintro ⟨E', hE', hEq⟩
    obtain ⟨ω₁, h₁, hE_eq⟩ := hE
    obtain ⟨ω₂, h₂, hE'_eq⟩ := hE'
    have hω : ω₁ = ω₂ := isMinFrequency_unique h₁ h₂
    subst hω
    have hE'E : E' = E := by rw [hE'_eq, hE_eq]
    subst hE'E
    exact hEq
  · intro hEq
    exact ⟨E, hE, hEq⟩

end PartC2Data

end IPhO2026.T1.C2
