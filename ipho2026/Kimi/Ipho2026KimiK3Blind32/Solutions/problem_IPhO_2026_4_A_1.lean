import Mathlib

/-!
# IPhO 2026, Experimental Problem E1, Part A.1 — answer-blind formalization

The apparatus (Fig. 2, Fig. 17, Fig. 18) contains a sealed column of confined
air (**CA**) inside the graduated inner cylinder (**IC**).  With valves **D**
and **E** closed after introducing propylene glycol (**PG**) to the height
`h = 4.5 cm`, the volume of the CA is fixed: it is the air of height
`H` (Fig. 18) above the PG column.  The CA obeys the ideal-gas equation of
state `P * V = n * R * T` (statement eq. (1)).

Subquestion A.1 (0.4 pt): **determine the mass `m`, the number of moles `n`,
and the total number `N` of molecules of the CA.**

The official answer is withheld.  Following the answer-blind policy, the
closed forms and numerical values of `m`, `n`, `N` (and of any CD-reader
trial values such as the trapped air height or its pressure and temperature)
are kept out of the theorem signature: a `Solution` predicate is built from
the stated reference values, the constants table, the figure data, and the
governing laws, and existence and uniqueness of the requested triple is
stated.

## Statement data used

* **Constants and Reference Values** (E1 p. 8): Avogadro constant
  `N_A = 6.022e23 mol⁻¹`, molar mass of air `Mₐ = 28.96 g/mol`, density of
  water `ρ₀ = 1000 kg/m³`, molar volume of an ideal gas at normal conditions
  `V_m = 22.4 L/mol` for `T₀ = 273.15 K` and `P₀ = 101.3 kPa`.
* **Part A ambient datum** (E1 p. 9): time-averaged ambient air density
  `ρₐ = 1.12 kg/m³`.
* **Procedure** (E1 p. 9): PG is introduced to `h = 4.5 cm` and valves D, E
  are closed, so the CA occupies a sealed, constant volume at the ambient
  state filling the trap when it was sealed.
* **Figure 17** (cross-sectional dimensions, tolerances `± 0.1 mm`):
  inner bore of the IC `d_bore = 33.7 mm`, IC outer diameter
  `d_IC = 39.4 mm`, OC diameter `d_OC = 74.8 mm`.
* **Figure 3** (module reading at the displayed instant): internal pressure
  `P = 75.5 kPa`.
* **Fig. 18 notation**: `h` is the height of the liquid in the IC and `H`
  the height of the air above it.

Because the trapped air column is described by internal diameters in the
source figures, the inner-cylinder bore `33.7 mm` is used as the CA diameter;
`39.4 mm` (IC outer) and `74.8 mm` (OC) are kept as geometry fields since
they belong to the stated apparatus data of the experiment.
-/

namespace IPhO_2026_4_A_1

/-- The prescribed constants and reference values of the experiment
(E1 "Constants and Reference Values", p. 8, and the ambient datum of Part A,
p. 9).  All are stated data of the problem, not answers. -/
structure ExperimentConstants where
  /-- Avogadro constant `N_A = 6.022e23 mol⁻¹`. -/
  N_A : ℝ := 6.022e23
  /-- Molar mass of air `Mₐ = 28.96 g/mol = 28.96e-3 kg/mol`. -/
  M_a : ℝ := 28.96e-3
  /-- Density of water `ρ₀ = 1000 kg/m³` (used in later parts of E1). -/
  ρ_water : ℝ := 1000
  /-- Molar mass of water `M₀ = 18.02 g/mol` (used in later parts of E1). -/
  M_water : ℝ := 18.02e-3
  /-- Specific heat of water `c₀ = 4.184e3 J/(kg·K)` (used in later parts). -/
  c_water : ℝ := 4.184e3
  /-- Molar volume of an ideal gas at normal conditions `V_m = 22.4 L/mol`. -/
  V_m : ℝ := 22.4e-3
  /-- Normal-conditions reference temperature `T₀ = 273.15 K`. -/
  T_normal : ℝ := 273.15
  /-- Normal-conditions reference pressure `P₀ = 101.3 kPa = 101.3e3 Pa`. -/
  P_normal : ℝ := 101.3e3
  /-- Time-averaged density of ambient air, `ρₐ = 1.12 kg/m³` (Part A, p. 9). -/
  ρ_a : ℝ := 1.12
  N_A_pos : 0 < N_A := by norm_num
  M_a_pos : 0 < M_a := by norm_num
  V_m_pos : 0 < V_m := by norm_num
  T_normal_pos : 0 < T_normal := by norm_num
  P_normal_pos : 0 < P_normal := by norm_num
  ρ_a_pos : 0 < ρ_a := by norm_num

/-- The universal gas constant, as determined by the stated normal-conditions
reference values: `V_m` is the molar volume at temperature `T_normal` and
pressure `P_normal`, so the equation of state at the reference point gives
`R = P₀ · V_m / T₀`.  This is a definitional combination of stated reference
data, not a derived answer. -/
noncomputable def ExperimentConstants.R (C : ExperimentConstants) : ℝ :=
  C.P_normal * C.V_m / C.T_normal

/-- The universal gas constant is positive. -/
theorem ExperimentConstants.R_pos (C : ExperimentConstants) : 0 < C.R := by
  unfold ExperimentConstants.R
  exact div_pos (mul_pos C.P_normal_pos C.V_m_pos) C.T_normal_pos

/-- The apparatus data of the experiment (Figs. 17 and 18 as stated):
diameters of the cylinders, the PG height `h` and the sealed CA height `H`,
and the tolerances `±0.1 mm` attached to the diameters by Fig. 17. -/
structure Apparatus where
  /-- Inner bore of the inner cylinder, `d_bore = 33.7 mm`: the diameter of
  the confined air column (Fig. 17, innermost arrow). -/
  d_bore : ℝ := 33.7e-3
  /-- Outer diameter of the inner cylinder, `d_IC = 39.4 mm` (Fig. 17). -/
  d_IC : ℝ := 39.4e-3
  /-- Diameter of the outer cylinder, `d_OC = 74.8 mm` (Fig. 17). -/
  d_OC : ℝ := 74.8e-3
  /-- Fig. 17 machining/measurement tolerance `ε = 0.1 mm`, attached to the
  stated diameters as intervals `d ± ε`. -/
  tolerance : ℝ := 0.1e-3
  /-- Height of the propylene-glycol column after sealing, `h = 4.5 cm`
  (Fig. 18: height of the liquid). -/
  h : ℝ := 4.5e-2
  /-- Height of the confined air column above the liquid after sealing
  (Fig. 18: height of the air), read from the IC centimeter scale via CD
  reader; left undetermined here because the CD reader data are withheld. -/
  H : ℝ
  d_bore_pos : 0 < d_bore := by norm_num
  tolerance_pos : 0 < tolerance := by norm_num
  h_pos : 0 < h := by norm_num
  H_pos : 0 < H

/-- The measured internal state of the confined air, as read on the module
(Fig. 3 labels: INT. PRESSURE, INT. TEMPERATURE).  The default pressure
`75.5 kPa` is the internal-pressure reading displayed in Fig. 3. -/
structure ConfinedAirState where
  /-- Absolute pressure of the CA (INT. PRESSURE). -/
  P : ℝ := 75.5e3
  /-- Absolute temperature of the CA (INT. TEMPERATURE). -/
  T : ℝ
  P_pos : 0 < P := by norm_num
  T_pos : 0 < T

namespace Apparatus

/-- Cross-sectional area of the air column, `A = π d²/4` (Fig. 17 geometry). -/
noncomputable def crossSection (A : Apparatus) : ℝ :=
  Real.pi * A.d_bore ^ 2 / 4

/-- **Governing geometry** (Figs. 17–18): the sealed CA is the right-circular
cylinder of air of diameter `d_bore` and height `H` above the PG column,
`V = A · H`.  The hose-volume and temperature-sensor corrections are stated
to compensate each other and are neglected ("Volume corrections", E1 p. 8). -/
noncomputable def airVolume (A : Apparatus) : ℝ :=
  A.crossSection * A.H

theorem airVolume_pos (A : Apparatus) : 0 < A.airVolume := by
  unfold airVolume crossSection
  exact mul_pos
    (div_pos (mul_pos Real.pi_pos (pow_pos A.d_bore_pos 2)) (by norm_num))
    A.H_pos

end Apparatus

/-- **Ambient sealing/consistency condition.**  The CA was trapped while the
IC communicated with the ambient atmosphere (valves D, E open during the PG
introduction), so the air captured in the fixed volume at state `(s.P, s.T)`
is ambient air of Bucaramanga: its molar density `s.P / (C.R · s.T)` equals
the ambient molar density `ρₐ / Mₐ` built from the stated time-averaged
density `ρₐ = 1.12 kg/m³` and the molar mass of air.  Written without
divisions: `s.P * C.M_a = C.ρ_a * C.R * s.T`.  This constrains the state
pair `(s.P, s.T)` using only stated reference data. -/
def AmbientConsistent (C : ExperimentConstants) (s : ConfinedAirState) : Prop :=
  s.P * C.M_a = C.ρ_a * C.R * s.T

/-- **Solution predicate (answer-free).**  A triple `(m, n, N)` — mass,
amount of substance, and number of molecules — is the requested content of
the confined air column iff:

1. **amount from the equation of state:** `n` is the amount of an ideal gas
   occupying the fixed CA volume at the measured internal state,
   `s.P * A.airVolume = n * C.R * s.T` (statement eq. (1), `PV = nRT`);
2. **mass from the molar mass:** the CA is air, so `m = Mₐ · n`;
3. **count from the Avogadro constant:** `N = N_A · n`. -/
def Solution (C : ExperimentConstants) (A : Apparatus) (s : ConfinedAirState)
    (m n N : ℝ) : Prop :=
  s.P * A.airVolume = n * C.R * s.T ∧ m = C.M_a * n ∧ N = C.N_A * n

/-- **Target theorem (answer-free).**  For the stated apparatus `A`, the
stated constants `C`, and any sealed CA state `s` of positive pressure and
temperature that is consistent with the stated ambient datum `ρₐ` (the air
sealed in the trap is local ambient air), the requested mass, amount, and
number of molecules of the CA exist and are uniquely determined. -/
theorem problem_IPhO_2026_4_A_1
    (C : ExperimentConstants) (A : Apparatus) (s : ConfinedAirState) :
    AmbientConsistent C s →
    ∃! (mnN : ℝ × ℝ × ℝ), Solution C A s mnN.1 mnN.2.1 mnN.2.2 := by
  intro _hambient
  -- The witness mass/amount/count are forced by the three governing relations.
  set n₀ := s.P * A.airVolume / (C.R * s.T) with hn_def
  have hR : C.R ≠ 0 := ne_of_gt C.R_pos
  have hT : s.T ≠ 0 := ne_of_gt s.T_pos
  have hV : s.P * A.airVolume = n₀ * C.R * s.T := by
    rw [hn_def]
    field_simp [mul_comm]
  -- The unique solution is the triple built from the ideal-gas amount.
  have hmem : Solution C A s
      ((C.M_a * n₀, n₀, C.N_A * n₀) : ℝ × ℝ × ℝ).1
      ((C.M_a * n₀, n₀, C.N_A * n₀) : ℝ × ℝ × ℝ).2.1
      ((C.M_a * n₀, n₀, C.N_A * n₀) : ℝ × ℝ × ℝ).2.2 := by
    exact ⟨hV, rfl, rfl⟩
  refine ExistsUnique.intro
    ((C.M_a * n₀, n₀, C.N_A * n₀) : ℝ × ℝ × ℝ) hmem ?_
  -- Any solution has the same amount, hence the same mass and count.
  intro q hsol
  have hn_eq : s.P * A.airVolume = q.2.1 * C.R * s.T := hsol.1
  have hm_eq : q.1 = C.M_a * q.2.1 := hsol.2.1
  have hN_eq : q.2.2 = C.N_A * q.2.1 := hsol.2.2
  have hstatement : q.2.1 * C.R * s.T = n₀ * C.R * s.T := hn_eq.symm.trans hV
  have hn_only : q.2.1 = n₀ := by
    have hmul : q.2.1 * (C.R * s.T) = n₀ * (C.R * s.T) := by
      nlinarith [hstatement]
    exact mul_right_cancel₀ (mul_ne_zero hR hT) hmul
  apply Prod.ext
  · exact hm_eq.trans (congrArg (C.M_a * ·) hn_only)
  · apply Prod.ext
    · exact hn_only
    · exact hN_eq.trans (congrArg (C.N_A * ·) hn_only)

end IPhO_2026_4_A_1
