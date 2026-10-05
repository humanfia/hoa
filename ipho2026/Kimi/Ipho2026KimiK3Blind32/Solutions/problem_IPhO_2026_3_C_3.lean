/-
# IPhO 2026, Theory Question T3 ("Chasing the absolute zero"), Part T3-C3

The paramagnetic torus (Pm-T) executes the Carnot refrigeration cycle
`1 → 2 → 3 → 4 → 1` of Figure 3b in the `H`-versus-`T` plane: vertices `1` and `4`
lie on the vertical (hot, isothermal) branch at the hot-reservoir temperature
`T_h`, vertices `2` and `3` lie on the vertical (cold, isothermal) branch at the
cold-reservoir temperature `T_c`. The Pm-T obeys

* the equation of state `T · M · V = n · K · H`,
* the constant-`M` heat capacity `C_M = n · λ / T²` with `dU = C_M · dT` in any
  process (the data given in the part B table),
* the differential work on the material `dW = μ₀ · V · H · dM` (part A),
* the energy-transfer sign convention: heat `Q > 0` flows **into** the Pm-T and
  heat `Q < 0` flows out of it.

Accordingly the isothermal heat relation from part B.1 is: at fixed temperature
`T`, when the applied field magnitude changes from `H_i` to `H_f`, the heat
transferred **into** the torus is (as a function of the abstract quantities)
`Q T H_i H_f = −(μ₀ · V · n · K / (2 · T)) · (H_f² − H_i²)`（外磁场增大时材料
向外界放热、减小时从外界吸热，与绝热去磁制冷一致）。This relation is
*used* here as a governing law, not proved from a first principle (that was the
task of part B.1; it is imported as a natural-language prerequisite only).

## Current subquestion (T3-C3, 0.8 pts)

Suppose that to cool `1.00 L` of liquid helium initially at `1.00 K` we utilise
`n = 2.0` moles of Pm-T made of potassium chromate, for which
`K = 1.87 × 10⁻⁶ K·m³/mol` (density `2730 kg/m³`, molar mass `0.19 kg/mol`).
The Pm-T performs a Carnot refrigeration cycle with `H₁ = 411624 A/m`,
`H₂ = 311306 A/m`, `H₃ = 204618 A/m` and `H₄ = 240446 A/m`. After one operating
cycle, calculate the final temperature of the liquid helium. Assume that for the
liquid helium both the specific heat capacity `c = 100 J/(kg·K)` and the density
`ρ = 130 kg/m³` remain constant.

The official answer is withheld. Following the answer-free statement design,
the concrete values above are packaged into the parameter structure
`IPhO2026.T3.C3.Setup`, the governing relations are packaged into the predicate
`IPhO2026.T3.C3.FinalHeliumState`, and the main theorem asserts that, for the
supplied data, a final helium temperature with those properties exists and is
unique — without placing the derived value in the signature.
-/
import Mathlib

namespace IPhO2026

namespace T3

/-- Heat (joules) transferred **into** the paramagnetic torus during an
isothermal process at temperature `T` (kelvin) in which the applied field
magnitude changes from `H_i` to `H_f` (amperes per metre).

This is the general isothermal heat relation of part B.1 obtained from the
Pm-T equation of state `T · M · V = n · K · H` together with `dW = μ₀ V H dM`
and `dU = C_M dT`（等温时 `dT = 0`）; here it is taken as the governing law,
with `μ₀` the vacuum permeability (N/A²), `V` the torus volume (m³), `n` the
amount of substance (mol) and `K` the material constant of the equation of
state. The sign convention of the problem applies: the heat is positive when it
flows into the Pm-T and negative when it flows out.

第一定律 `đQ = dU − đW_on`（`đW_on = μ₀·V·H·dM`）在等温下给出
`đQ = −μ₀·V·H·dM = −(μ₀·n·K/T)·H·dH`，积分即得下式：**外场增大（等温磁化）
时 `Q < 0`，材料向外界放热；外场减小（等温去磁）时 `Q > 0`，材料从外界
吸热** —— 与 Figure 3b 绝热去磁制冷（上支去磁降温、下支磁化升温）的
方向一致。制冷循环中等温吸热只能发生在外场回落的去磁支。 -/
noncomputable def isothermalHeatIntoTorus
    (μ₀ V n K T H_i H_f : ℝ) : ℝ :=
  -μ₀ * V * n * K / (2 * T) * (H_f ^ 2 - H_i ^ 2)

/-- A Carnot refrigeration cycle `1 → 2 → 3 → 4 → 1` performed by a
paramagnetic torus, as drawn in the `H`-versus-`T` plane of Figure 3b.

All fields are magnitudes (real numbers);
`H₁, H₂, H₃, H₄` are the applied field magnitudes (A/m) at the four labelled
vertices of the cycle, `M₁, M₂, M₃, M₄` the magnetization magnitudes (A/m)
there, `T_h` the hot-reservoir temperature (K), `T_c` the cold-reservoir
temperature (K), `Q_h` the absolute value of the heat delivered to the hot
reservoir (J) and `Q_c` the absolute value of the heat absorbed from the cold
reservoir (J). -/
structure PmTCarnotCycle where
  H₁ : ℝ
  H₂ : ℝ
  H₃ : ℝ
  H₄ : ℝ
  M₁ : ℝ
  M₂ : ℝ
  M₃ : ℝ
  M₄ : ℝ
  T_h : ℝ
  T_c : ℝ
  Q_h : ℝ
  Q_c : ℝ

namespace PmTCarnotCycle

/-- The cyclic quadruple of vertex field magnitudes, in cycle order
`1 → 2 → 3 → 4`. -/
def vertexFields (c : PmTCarnotCycle) : Fin 4 → ℝ
  | 0 => c.H₁
  | 1 => c.H₂
  | 2 => c.H₃
  | 3 => c.H₄

/-- The cyclic quadruple of vertex magnetization magnitudes, in cycle order
`1 → 2 → 3 → 4`. -/
def vertexMagnetizations (c : PmTCarnotCycle) : Fin 4 → ℝ
  | 0 => c.M₁
  | 1 => c.M₂
  | 2 => c.M₃
  | 3 => c.M₄

end PmTCarnotCycle

/-- The cycle `cyc` is a genuine Carnot refrigeration cycle for a Pm-T with
equation-of-state constant `K` (K·m³/mol), volume `V` (m³) and amount of
substance `n` (mol), equipped with the vacuum permeability `μ₀` (N/A²).

The hypotheses are exactly the geometry of Figure 3b together with the Pm-T
equation of state:

* vertices `1` and `4` lie on the hot isothermal branch, at the common
  temperature `T_h`, and vertices `2` and `3` on the cold isothermal branch, at
  the common temperature `T_c`, with `0 < T_c < T_h`;
* all four vertex states satisfy `T · M · V = n · K · H`;
* the vertex order around the cycle is strict: `H₃ < H₂` on the cold branch and
  `H₄ < H₁` on the hot branch (compare Figure 3b);
* `Q_h` and `Q_c` are the magnitudes, hence nonnegative. -/
structure PmTCarnotCycle.IsCycle (cyc : PmTCarnotCycle) (μ₀ V n K : ℝ) : Prop where
  hot_reservoir_pos : 0 < cyc.T_h
  cold_reservoir_pos : 0 < cyc.T_c
  cold_lt_hot : cyc.T_c < cyc.T_h
  field_one_pos : 0 < cyc.H₁
  field_two_pos : 0 < cyc.H₂
  field_three_pos : 0 < cyc.H₃
  field_four_pos : 0 < cyc.H₄
  magnetization_one_pos : 0 < cyc.M₁
  magnetization_two_pos : 0 < cyc.M₂
  magnetization_three_pos : 0 < cyc.M₃
  magnetization_four_pos : 0 < cyc.M₄
  eos_vertex_one : cyc.T_h * cyc.M₁ * V = n * K * cyc.H₁
  eos_vertex_two : cyc.T_c * cyc.M₂ * V = n * K * cyc.H₂
  eos_vertex_three : cyc.T_c * cyc.M₃ * V = n * K * cyc.H₃
  eos_vertex_four : cyc.T_h * cyc.M₄ * V = n * K * cyc.H₄
  cold_branch_orientation : cyc.H₃ < cyc.H₂
  hot_branch_orientation : cyc.H₄ < cyc.H₁
  heat_hot_nonneg : 0 ≤ cyc.Q_h
  heat_cold_nonneg : 0 ≤ cyc.Q_c

/-- The heat magnitudes `Q_h`, `Q_c` of the cycle are precisely those delivered
by the isothermal heat relation of part B.1, taken as a governing law.

The hot isothermal process `4 → 1` (field increasing from `H₄` to `H₁` at
temperature `T_h`，等温磁化) expels heat into the hot reservoir, so the heat
into the torus is negative and `Q_h` is its negated magnitude; the cold
isothermal process `2 → 3` (field decreasing from `H₂` to `H₃` at temperature
`T_c`，等温去磁) absorbs heat from the cold reservoir, so `Q_c` equals the
part-B.1 heat into the torus, which is positive by the orientation
`H₃ < H₂`. -/
def PmTCarnotCycle.RespectsPartB1Heat (cyc : PmTCarnotCycle) (μ₀ V n K : ℝ) :
    Prop :=
  cyc.Q_h = - isothermalHeatIntoTorus μ₀ V n K cyc.T_h cyc.H₄ cyc.H₁ ∧
  cyc.Q_c = isothermalHeatIntoTorus μ₀ V n K cyc.T_c cyc.H₂ cyc.H₃

/-- The supply data of question T3-C3: the potassium-chromate Pm-T, the
Carnot cycle it performs (with the field values named in the question), and
the liquid helium bath to be cooled. Every quantity listed in the official
statement is represented, with its SI role:

* helium bathing volume `V_He = 1.00 L`, initial temperature `T₀ = 1.00 K`;
* Pm-T amount of substance `n = 2.0 mol`, material constant
  `K = 1.87 × 10⁻⁶ K·m³/mol`, density `2730 kg/m³` (torus volume
  `V = mass / density`), molar mass `0.19 kg/mol`, vacuum permeability `μ₀`;
* vertex field magnitudes `H₁ = 411624 A/m`, `H₂ = 311306 A/m`,
  `H₃ = 204618 A/m`, `H₄ = 240446 A/m`;
* helium specific heat capacity `c = 100 J/(kg·K)` and density
  `ρ_He = 130 kg/m³`, both constant over the process. -/
structure C3.Setup where
  /-- Vacuum permeability `μ₀`, in N/A² = T·m/A. -/
  μ₀ : ℝ
  vacuum_permeability_pos : 0 < μ₀
  /-- Volume `V_helium` of liquid helium, in m³ (`1.00 L` in the question). -/
  V_helium : ℝ
  helium_volume_pos : 0 < V_helium
  /-- Initial helium temperature `T₀`, in K (`1.00 K` in the question). -/
  T_initial : ℝ
  initial_temperature_pos : 0 < T_initial
  /-- Amount of substance `n` of the Pm-T, in mol (`2.0 mol` in the question). -/
  n : ℝ
  amount_pos : 0 < n
  /-- Material constant `K` of potassium chromate, in K·m³/mol
  (`1.87 × 10⁻⁶` in the question). -/
  K : ℝ
  material_constant_pos : 0 < K
  /-- Density `ρ_pmt` of the potassium-chromate Pm-T, in kg/m³
  (`2730` in the question). -/
  ρ_pmt : ℝ
  pmt_density_pos : 0 < ρ_pmt
  /-- Molar mass of potassium chromate, in kg/mol (`0.19` in the question). -/
  molar_mass : ℝ
  molar_mass_pos : 0 < molar_mass
  /-- Applied field magnitude `H₁` at vertex `1`, in A/m
  (`411624` in the question). -/
  H₁ : ℝ
  field_one_pos : 0 < H₁
  /-- Applied field magnitude `H₂` at vertex `2`, in A/m
  (`311306` in the question). -/
  H₂ : ℝ
  field_two_pos : 0 < H₂
  /-- Applied field magnitude `H₃` at vertex `3`, in A/m
  (`204618` in the question). -/
  H₃ : ℝ
  field_three_pos : 0 < H₃
  /-- Applied field magnitude `H₄` at vertex `4`, in A/m
  (`240446` in the question). -/
  H₄ : ℝ
  field_four_pos : 0 < H₄
  /-- Helium specific heat capacity `c`, in J/(kg·K) (`100` in the question),
  constant over the process. -/
  c_helium : ℝ
  helium_specific_heat_pos : 0 < c_helium
  /-- Helium density `ρ_helium`, in kg/m³ (`130` in the question), constant
  over the process. -/
  ρ_helium : ℝ
  helium_density_pos : 0 < ρ_helium

namespace C3.Setup

/-- Volume (m³) of the paramagnetic torus: the mass `n · molar_mass` of the
`2.0` moles of potassium chromate divided by its density, as fixed by the
supplied density and molar-mass data of the question. -/
noncomputable def torusVolume (s : C3.Setup) : ℝ :=
  s.n * s.molar_mass / s.ρ_pmt

/-- The torus volume determined by the supplied data is positive. -/
lemma torusVolume_pos (s : C3.Setup) : 0 < s.torusVolume := by
  unfold torusVolume
  exact div_pos (mul_pos s.amount_pos s.molar_mass_pos) s.pmt_density_pos

/-- The constant thermal capacitance `m c = ρ_He · V_He · c` (J/K) of the
liquid helium bath, well-defined because the helium density `ρ_He` and specific
heat capacity `c` remain constant by assumption. -/
noncomputable def heliumHeatCapacity (s : C3.Setup) : ℝ :=
  s.ρ_helium * s.V_helium * s.c_helium

/-- The helium thermal capacitance is positive. -/
lemma heliumHeatCapacity_pos (s : C3.Setup) : 0 < s.heliumHeatCapacity :=
  mul_pos (mul_pos s.helium_density_pos s.helium_volume_pos)
    s.helium_specific_heat_pos

end C3.Setup

namespace C3.Setup

/-- Cold-leg orientation per Figure 3b: on the cold isothermal branch (left,
at `T_c`) vertex `3` lies below vertex `2`, i.e. `H₃ < H₂`. -/
def ColdLegOriented (s : C3.Setup) : Prop := s.H₃ < s.H₂

/-- Hot-leg orientation per Figure 3b: on the hot isothermal branch (right,
at `T_h`) vertex `4` lies below vertex `1`, i.e. `H₄ < H₁`. -/
def HotLegOriented (s : C3.Setup) : Prop := s.H₄ < s.H₁

/-- Heat the Pm-T absorbs from the cold reservoir on the cold isothermal leg
`2 → 3` when that leg runs at temperature `T` (K), computed from the part-B.1
law with the supplied torus volume. Positive when `ColdLegOriented` holds. -/
noncomputable def coldLegHeatAt (s : C3.Setup) (T : ℝ) : ℝ :=
  isothermalHeatIntoTorus s.μ₀ s.torusVolume s.n s.K T s.H₂ s.H₃

/-- Single-cycle feasibility: one cycle at `T_c = T_initial` absorbs less heat
than the bath can release by cooling toward `0` K, so the post-cycle bath
temperature is still positive. For the supplied data the absorbed heat is a
small fraction of the bath's heat content, hence this holds. -/
def SingleCycleFeasible (s : C3.Setup) : Prop :=
  isothermalHeatIntoTorus s.μ₀ s.torusVolume s.n s.K s.T_initial s.H₂ s.H₃
    < s.heliumHeatCapacity * s.T_initial

end C3.Setup

/-- `C3.FinalHeliumState s cyc T_f` asserts that `cyc` is the Carnot
refrigeration cycle performed by the potassium-chromate Pm-T with the supply
data `s`, and that after one operating cycle the liquid helium — initially at
`s.T_initial = 1.00 K` — reaches the temperature `T_f` (K).

Apart from the cycle itself (whose vertex fields are exactly those named in the
question), the predicate contains only the governing laws:

* the Pm-T cycle is a genuine Figure-3b Carnot cycle whose cold isothermal
  leg runs in thermal contact with the helium bath at its initial temperature
  (`IsCycle` with `T_c = 1.00 K`; the hot-reservoir temperature `T_h > T_c`
  is not supplied by the statement and is left free);
* the heat magnitudes obey the part-B.1 isothermal heat relation
  (`RespectsPartB1Heat`);
* the helium obeys calorimetry with constant `c` and `ρ_He`: the heat it loses,
  `ρ_He · V_He · c · (T₀ − T_f)`, equals the heat `Q_c` absorbed by the Pm-T
  from the cold reservoir;
* the helium is genuinely refrigerated: `0 < T_f < T₀`. -/
structure C3.FinalHeliumState (s : C3.Setup) (cyc : PmTCarnotCycle) (T_f : ℝ) :
    Prop where
  /-- Vertex `1` of the performed cycle carries the stated field `H₁`. -/
  cycle_field_one : cyc.H₁ = s.H₁
  /-- Vertex `2` of the performed cycle carries the stated field `H₂`. -/
  cycle_field_two : cyc.H₂ = s.H₂
  /-- Vertex `3` of the performed cycle carries the stated field `H₃`. -/
  cycle_field_three : cyc.H₃ = s.H₃
  /-- Vertex `4` of the performed cycle carries the stated field `H₄`. -/
  cycle_field_four : cyc.H₄ = s.H₄
  -- (Note: the statement does not pin down the hot-reservoir temperature;
  -- `T_h` stays free and is only constrained by `IsCycle`'s `T_c < T_h`.)
  /-- The cold reservoir is the liquid-helium bath at its initial temperature
  (the cold isothermal leg runs in thermal contact with the bath being
  cooled, at `T_c = T₀`, consistent with part C.4's cycle model). -/
  cold_reservoir_is_bath : cyc.T_c = s.T_initial
  /-- The cycle is a genuine Figure-3b Pm-T Carnot cycle for the supplied
  potassium-chromate torus. -/
  is_cycle : cyc.IsCycle s.μ₀ s.torusVolume s.n s.K
  /-- The heat magnitudes are those of the part-B.1 isothermal heat relation. -/
  respects_part_B1 : cyc.RespectsPartB1Heat s.μ₀ s.torusVolume s.n s.K
  /-- Calorimetry: the heat lost by the helium at constant `c` and `ρ_He`
  equals the heat absorbed from it by the Pm-T on the cold isothermal leg. -/
  helium_calorimetry :
    s.heliumHeatCapacity * (s.T_initial - T_f) = cyc.Q_c
  /-- The final temperature is a positive temperature below the initial one. -/
  final_temperature_pos : 0 < T_f
  /-- After one operating cycle the helium is colder than before. -/
  final_lt_initial : T_f < s.T_initial

/-- Cold-leg absorption is positive under the Figure-3b orientation: the cold
leg is isothermal demagnetization (`H₂ → H₃` with `H₃ < H₂`), which absorbs
heat from the cold reservoir. -/
lemma C3.Setup.coldLegHeatAt_pos (s : C3.Setup) {T : ℝ} (hT : 0 < T)
    (horient : s.ColdLegOriented) : 0 < s.coldLegHeatAt T := by
  have hV : 0 < s.torusVolume := s.torusVolume_pos
  have hsq : s.H₃ ^ 2 < s.H₂ ^ 2 := by
    have h2 := mul_lt_mul_of_pos_right horient (by
      linarith [s.field_two_pos, s.field_three_pos] :
        (0:ℝ) < s.H₂ + s.H₃)
    nlinarith [h2]
  have hnum : 0 < s.μ₀ * s.torusVolume * s.n * s.K :=
    mul_pos (mul_pos (mul_pos s.vacuum_permeability_pos hV) s.amount_pos)
      s.material_constant_pos
  have hfrac : 0 < s.μ₀ * s.torusVolume * s.n * s.K / (2 * T) :=
    div_pos hnum (by linarith)
  unfold coldLegHeatAt isothermalHeatIntoTorus
  have htarget :
      -s.μ₀ * s.torusVolume * s.n * s.K / (2 * T) * (s.H₃ ^ 2 - s.H₂ ^ 2)
        = s.μ₀ * s.torusVolume * s.n * s.K / (2 * T) *
          (s.H₂ ^ 2 - s.H₃ ^ 2) := by ring
  rw [htarget]
  exact mul_pos hfrac (by linarith)

/-- **Question T3-C3 (answer-free form).**

Using the supplied potassium-chromate and liquid-helium data, the liquid
helium after one operating cycle reaches exactly one temperature: if the
stated field values respect the Figure-3b orientation (`H₃ < H₂` on the cold
branch, `H₄ < H₁` on the hot branch) and a single cycle is physically feasible
(the heat absorbed by the Pm-T on the cold isothermal leg at the bath's
initial temperature does not exceed the bath's releasable heat content
`D·T₀`), then there exists a unique post-cycle helium temperature `T_f`,
determined by constant-property calorimetry

  `D·(T₀ − T_f) = (μ₀·V·n·K/(2·T₀))·(H₂² − H₃²)`,

and it satisfies `0 < T_f < T₀` — the helium is genuinely refrigerated after
one cycle.

The cold isothermal leg runs in thermal contact with the liquid-helium bath
being cooled, i.e. at `T_c = T₀`; this matches part C.4's continuous-cycling
model, in which the `T_c` of each cycle is the cooled body's temperature. The
witness value (the numerical final temperature requested in the exam) is
deliberately not part of the statement; the proving stage may construct it as
`T_f = T₀ − coldLegHeatAt T₀ / D`. -/
theorem C3.helium_temperature_after_one_cycle (s : C3.Setup)
    (h_cold_orient : s.ColdLegOriented) (h_hot_orient : s.HotLegOriented)
    (h_feasible : s.SingleCycleFeasible) :
    ∃! T_f : ℝ, 0 < T_f ∧ T_f < s.T_initial ∧
      s.heliumHeatCapacity * (s.T_initial - T_f) =
        s.coldLegHeatAt s.T_initial := by
  set D := s.heliumHeatCapacity with hD
  have hDpos : 0 < D := s.heliumHeatCapacity_pos
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hT0 : 0 < s.T_initial := s.initial_temperature_pos
  -- The cold-leg heat at the bath's initial temperature is positive: the leg
  -- is isothermal demagnetization (`H₂ → H₃` with `H₃ < H₂`), which absorbs
  -- heat from the cold reservoir (proven bridge lemma below).
  have hQc : 0 < s.coldLegHeatAt s.T_initial :=
    s.coldLegHeatAt_pos hT0 h_cold_orient
  -- Single-cycle feasibility: the absorbed heat is below the bath's
  -- releasable heat content `D·T₀`, so the post-cycle temperature is positive.
  have hfeas : s.coldLegHeatAt s.T_initial < D * s.T_initial := h_feasible
  -- The candidate post-cycle temperature, forced by the calorimetry equation:
  -- `D·(T₀ − T_f) = Q_c`  ⟺  `T_f = T₀ − Q_c / D`.
  set Tf := s.T_initial - s.coldLegHeatAt s.T_initial / D with hTf
  have hTpos : 0 < Tf := by
    rw [hTf, sub_pos]
    rw [div_lt_iff₀ hDpos]
    nlinarith [hfeas]
  have hTlt : Tf < s.T_initial := by
    rw [hTf, sub_lt_self_iff]
    exact div_pos hQc hDpos
  have hbal : D * (s.T_initial - Tf) = s.coldLegHeatAt s.T_initial := by
    rw [hTf, sub_sub_self, mul_div_cancel₀ _ hDne]
  refine ⟨Tf, ⟨hTpos, hTlt, hbal⟩, ?_⟩
  intro T hTprop
  obtain ⟨-, -, hbal'⟩ := hTprop
  -- Uniqueness: `T` satisfies the same linear calorimetry equation as `Tf`,
  -- whose only solution is `Tf = T₀ − Q_c / D` (the solver `D ≠ 0`).
  have hTeq : T = s.T_initial - s.coldLegHeatAt s.T_initial / D := by
    have hsub : s.T_initial - T = s.coldLegHeatAt s.T_initial / D := by
      rw [← hbal', mul_div_cancel_left₀ _ hDne]
    linear_combination -hsub
  rw [hTeq, ← hTf]

end T3

end IPhO2026
