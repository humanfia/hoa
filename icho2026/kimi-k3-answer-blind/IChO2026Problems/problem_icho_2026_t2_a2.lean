import IChO2026Chem
import CRNT

/-!
# IChO 2026, Problem T2 (Kinetics of the Belousov–Zhabotinsky reaction), Subquestion 2.2

Blueprint chapter: `blueprint/src/chapters/IChO2026Problems_problem_icho_2026_t2_a2.tex`.
Source report: `reports/icho_2026/problem_icho_2026_t2_a2.source.json`
(`blind_record_sha256 = a4389b3d6472a287e0e6e08478bd9e57079d6a70360d92c0cef3f9d8869d481b`).

## Problem data (problem text and problem image `T2_page-2.png`)

Mechanism of the BZ reaction (BMA = CHBr(COOH)₂), with mass-action rate constants:

* Process A:
  (1) `HBrO2 + BrO3⁻ + H⁺ → 2 BrO2• + H2O`, `k1 = 1.0 × 10⁴ M⁻² s⁻¹`;
  (2) `BrO2• + Ce³⁺ + H⁺ → HBrO2 + Ce⁴⁺`,        `k2 = 6.2 × 10⁴ M⁻² s⁻¹`;
  (3) `2 HBrO2 → BrO3⁻ + HBrO + H⁺`,             `k3 = 4.0 × 10⁷ M⁻¹ s⁻¹`.
* Process B:
  (4) `HBrO2 + Br⁻ + H⁺ → 2 HBrO`,               `k4 = 2.0 × 10⁹ M⁻² s⁻¹`;
  (5) `BrO3⁻ + Br⁻ + 2 H⁺ → HBrO + HBrO2`,       `k5 = 2.1 M⁻³ s⁻¹`;
  (6) `HBrO + MA → BMA + H2O`,                   `k6 = 8.2 M⁻¹ s⁻¹`.
* Process C:
  (7) `Ce⁴⁺ + BMA → Ce³⁺ + Br⁻ + other products`, `k7 = 1.0 × 10² M⁻¹ s⁻¹`.

Stipulations: Process C occurs continuously while Processes A and B alternate;
when A occurs B practically does not occur, and vice versa.  The buffered
concentrations `[BrO3⁻] = 0.06 M`, `[MA] = 0.1 M`, `[H⁺] = 0.8 M` (pH) are
maintained constant throughout; `[Ce⁴⁺]₀ = 0.001 M` is initial data only.
(The problem prints fallback values `1 × 10⁻⁵ M` and `1 × 10⁻¹⁰ M` for use in
*later* subquestions only; they are **not** used to derive the present results.)

## Assumption / target split

* **Assumptions.** The mass-action rate laws of steps (1)–(6) with the tabulated
  rate constants; the buffered-reactant stipulation; the steady-state
  approximation `d[HBrO2]/dt = 0` (and, in Process A, additionally
  `d[BrO2•]/dt = 0` for the radical intermediate), applied to each process
  separately because the processes alternate.
* **Targets (both in `mol dm⁻³`, reported to three significant figures).**
  * `[HBrO2]_A`, the stationary HBrO₂ concentration while Process A runs;
  * `[HBrO2]_B`, the stationary HBrO₂ concentration while Process B runs.

## Model

The reaction networks are encoded with the configured CRNT library
(`CRNT.Network`, `CRNT.Network.RateConstants`, `CRNT.Network.massActionVectorField`),
so species, reactions and stoichiometry are first-class objects.  The steady-state
predicates are stated as vanishing of the CRNT mass-action vector field on the
intermediates.  Bridge lemmas connect these to the explicit polynomial rate
balances used in the derivation; the algebra and the numerics are proved in full.
-/

namespace IChO2026.T2.A2

/-- The eleven chemical species occurring in the seven elementary steps of the
BZ mechanism stated in the problem (Processes A, B and C). -/
inductive BZSpecies where
  | hbrO2  -- HBrO2, bromous acid: the key intermediate
  | brO2   -- BrO2• radical (intermediate of Process A)
  | brO3   -- BrO3⁻, bromate (buffered at 0.06 M)
  | br     -- Br⁻, bromide
  | hbrO   -- HBrO, hypobromous acid
  | h      -- H⁺ (pH buffered at 0.8 M)
  | h2o    -- H2O (solvent; only ever a product, hence enters no rate law)
  | ce3    -- Ce³⁺
  | ce4    -- Ce⁴⁺
  | ma     -- malonic acid CH2(COOH)2 (buffered at 0.1 M)
  | bma    -- bromomalonic acid CHBr(COOH)2
  deriving DecidableEq, Fintype

/-! ## Tabulated rate constants (problem statement, exact as printed) -/

/-- `k1 = 1.0 × 10⁴ M⁻² s⁻¹`, step (1). -/
def k1 : ℝ := 1.0e4

/-- `k2 = 6.2 × 10⁴ M⁻² s⁻¹`, step (2). -/
def k2 : ℝ := 6.2e4

/-- `k3 = 4.0 × 10⁷ M⁻¹ s⁻¹`, step (3). -/
def k3 : ℝ := 4.0e7

/-- `k4 = 2.0 × 10⁹ M⁻² s⁻¹`, step (4). -/
def k4 : ℝ := 2.0e9

/-- `k5 = 2.1 M⁻³ s⁻¹`, step (5). -/
def k5 : ℝ := 2.1

/-- `k6 = 8.2 M⁻¹ s⁻¹`, step (6). -/
def k6 : ℝ := 8.2

/-- `k7 = 1.0 × 10² M⁻¹ s⁻¹`, step (7). -/
def k7 : ℝ := 1.0e2

/-! ## Buffered concentrations (problem stipulation, exact as printed) -/

/-- Buffered bromate concentration `[BrO3⁻] = 0.06 mol dm⁻³`. -/
def bromateConc : ℝ := 0.06

/-- Buffered proton concentration `[H⁺] = 0.8 mol dm⁻³` (constant pH). -/
def protonConc : ℝ := 0.8

/-- Buffered malonic acid concentration `[MA] = 0.1 mol dm⁻³`. -/
def maConc : ℝ := 0.1

/-- Initial cerium(IV) concentration `[Ce⁴⁺]₀ = 0.001 mol dm⁻³`
(initial data only; cerium is the oscillating catalyst, not buffered). -/
def ce4InitConc : ℝ := 0.001

/-- The problem stipulates that the reactant concentrations `[BrO3⁻]`, `[MA]`
and the pH are maintained constant throughout the BZ reaction. -/
def BufferedConc (x : CRNT.Concentration BZSpecies) : Prop :=
  x .brO3 = 0.06 ∧ x .ma = 0.1 ∧ x .h = 0.8

/-! ## The seven elementary steps as CRNT reactions -/

/-- Step (1): `HBrO2 + BrO3⁻ + H⁺ → 2 BrO2• + H2O`. -/
def stepA1 : CRNT.Reaction BZSpecies where
  source := fun
    | .hbrO2 => 1 | .brO3 => 1 | .h => 1 | _ => 0
  target := fun
    | .brO2 => 2 | .h2o => 1 | _ => 0

/-- Step (2): `BrO2• + Ce³⁺ + H⁺ → HBrO2 + Ce⁴⁺`. -/
def stepA2 : CRNT.Reaction BZSpecies where
  source := fun
    | .brO2 => 1 | .ce3 => 1 | .h => 1 | _ => 0
  target := fun
    | .hbrO2 => 1 | .ce4 => 1 | _ => 0

/-- Step (3): `2 HBrO2 → BrO3⁻ + HBrO + H⁺`. -/
def stepA3 : CRNT.Reaction BZSpecies where
  source := fun
    | .hbrO2 => 2 | _ => 0
  target := fun
    | .brO3 => 1 | .hbrO => 1 | .h => 1 | _ => 0

/-- Step (4): `HBrO2 + Br⁻ + H⁺ → 2 HBrO`. -/
def stepB1 : CRNT.Reaction BZSpecies where
  source := fun
    | .hbrO2 => 1 | .br => 1 | .h => 1 | _ => 0
  target := fun
    | .hbrO => 2 | _ => 0

/-- Step (5): `BrO3⁻ + Br⁻ + 2 H⁺ → HBrO + HBrO2`. -/
def stepB2 : CRNT.Reaction BZSpecies where
  source := fun
    | .brO3 => 1 | .br => 1 | .h => 2 | _ => 0
  target := fun
    | .hbrO => 1 | .hbrO2 => 1 | _ => 0

/-- Step (6): `HBrO + MA → BMA + H2O`. -/
def stepB3 : CRNT.Reaction BZSpecies where
  source := fun
    | .hbrO => 1 | .ma => 1 | _ => 0
  target := fun
    | .bma => 1 | .h2o => 1 | _ => 0

/-- Step (7): `Ce⁴⁺ + BMA → Ce³⁺ + Br⁻ + other products`.  The problem leaves
the additional products unspecified ("other products"); they are not modelled
here, which is harmless because Process C does not enter the HBrO₂ balance of
either Process A or Process B. -/
def stepC1 : CRNT.Reaction BZSpecies where
  source := fun
    | .ce4 => 1 | .bma => 1 | _ => 0
  target := fun
    | .ce3 => 1 | .br => 1 | _ => 0

/-- Process A network: steps (1), (2), (3). -/
def processA : CRNT.Network BZSpecies where
  R := Fin 3
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun
    | 0 => stepA1
    | 1 => stepA2
    | 2 => stepA3

/-- Process B network: steps (4), (5), (6). -/
def processB : CRNT.Network BZSpecies where
  R := Fin 3
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun
    | 0 => stepB1
    | 1 => stepB2
    | 2 => stepB3

/-- Process C network: step (7) (continuous; not part of the HBrO₂ balance). -/
def processC : CRNT.Network BZSpecies where
  R := Fin 1
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun
    | 0 => stepC1

/-- Rate-constant function for Process A: `(k1, k2, k3)`. -/
def kA_fun : Fin 3 → ℝ
  | 0 => k1
  | 1 => k2
  | 2 => k3

/-- Rate-constant function for Process B: `(k4, k5, k6)`. -/
def kB_fun : Fin 3 → ℝ
  | 0 => k4
  | 1 => k5
  | 2 => k6

/-- Rate-constant function for Process C: `(k7)`. -/
def kC_fun : Fin 1 → ℝ
  | 0 => k7

theorem kA_pos : ∀ r : Fin 3, 0 < kA_fun r := by
  intro r
  fin_cases r
  · norm_num [kA_fun, k1]
  · norm_num [kA_fun, k2]
  · norm_num [kA_fun, k3]

theorem kB_pos : ∀ r : Fin 3, 0 < kB_fun r := by
  intro r
  fin_cases r
  · norm_num [kB_fun, k4]
  · norm_num [kB_fun, k5]
  · norm_num [kB_fun, k6]

theorem kC_pos : ∀ r : Fin 1, 0 < kC_fun r := by
  intro r
  fin_cases r
  · norm_num [kC_fun, k7]

/-- Process A rate constants as a CRNT `RateConstants` structure. -/
def κA : processA.RateConstants where
  k := kA_fun
  positive := kA_pos

/-- Process B rate constants as a CRNT `RateConstants` structure. -/
def κB : processB.RateConstants where
  k := kB_fun
  positive := kB_pos

/-- Process C rate constants as a CRNT `RateConstants` structure. -/
def κC : processC.RateConstants where
  k := kC_fun
  positive := kC_pos

/-! ## Steady-state approximation (CRNT form) -/

/-- Steady-state approximation while Process A runs (Process B practically off):
the mass-action vector field of the Process-A network vanishes on both
intermediates, `d[HBrO2]/dt = 0` and `d[BrO2•]/dt = 0`. -/
def ProcessASSA (x : CRNT.Concentration BZSpecies) : Prop :=
  processA.massActionVectorField κA x .hbrO2 = 0 ∧
  processA.massActionVectorField κA x .brO2 = 0

/-- Steady-state approximation while Process B runs (Process A practically off):
`d[HBrO2]/dt = 0` in the Process-B network. -/
def ProcessBSSA (x : CRNT.Concentration BZSpecies) : Prop :=
  processB.massActionVectorField κB x .hbrO2 = 0

/-! ## Explicit polynomial rate balances -/

/-- Net rate of change of `[HBrO2]` under Process A, `−r1 + r2 − 2 r3` with
`r1 = k1 [HBrO2][BrO3⁻][H⁺]`, `r2 = k2 [BrO2•][Ce³⁺][H⁺]`, `r3 = k3 [HBrO2]²`. -/
def dHBrO2_A (x : CRNT.Concentration BZSpecies) : ℝ :=
  -(k1 * x .hbrO2 * x .brO3 * x .h) + k2 * x .brO2 * x .ce3 * x .h
    - 2 * (k3 * (x .hbrO2) ^ 2)

/-- Net rate of change of `[BrO2•]` under Process A, `2 r1 − r2`. -/
def dBrO2_A (x : CRNT.Concentration BZSpecies) : ℝ :=
  2 * (k1 * x .hbrO2 * x .brO3 * x .h) - k2 * x .brO2 * x .ce3 * x .h

/-- Net rate of change of `[HBrO2]` under Process B, `−r4 + r5` with
`r4 = k4 [HBrO2][Br⁻][H⁺]`, `r5 = k5 [BrO3⁻][Br⁻][H⁺]²`. -/
def dHBrO2_B (x : CRNT.Concentration BZSpecies) : ℝ :=
  -(k4 * x .hbrO2 * x .br * x .h) + k5 * x .brO3 * x .br * (x .h) ^ 2

/-- Polynomial form of the Process-A steady-state conditions. -/
def ProcessASSA_poly (x : CRNT.Concentration BZSpecies) : Prop :=
  dHBrO2_A x = 0 ∧ dBrO2_A x = 0

/-- Polynomial form of the Process-B steady-state condition. -/
def ProcessBSSA_poly (x : CRNT.Concentration BZSpecies) : Prop :=
  dHBrO2_B x = 0

/-! ## Bridge: CRNT vector field = textbook polynomial rates

The `Fin 3` reaction sum is evaluated with `Fin.sum_univ_three`; each
`CRNT.Complex.massActionMonomial` is evaluated by reducing `Finset.univ` over
`BZSpecies` (eleven constructors, decidable) with `Finset.prod_insert`; the
stoichiometric coefficients reduce through `CRNT.Network.reactionVector_apply`. -/

/-- The finite enumeration of the eleven BZ species. -/
theorem BZSpecies.univ_eq : (Finset.univ : Finset BZSpecies) =
    {.hbrO2, .brO2, .brO3, .br, .hbrO, .h, .h2o, .ce3, .ce4, .ma, .bma} := by
  decide

/-- Mass-action monomial of the source of step (1): `[HBrO2][BrO3⁻][H⁺]`. -/
theorem monomial_stepA1 (x : CRNT.Concentration BZSpecies) :
    (stepA1.source).massActionMonomial x = x .hbrO2 * x .brO3 * x .h := by
  unfold CRNT.Complex.massActionMonomial
  rw [BZSpecies.univ_eq]
  simp [stepA1]
  ring

/-- Mass-action monomial of the source of step (2): `[BrO2•][Ce³⁺][H⁺]`. -/
theorem monomial_stepA2 (x : CRNT.Concentration BZSpecies) :
    (stepA2.source).massActionMonomial x = x .brO2 * x .ce3 * x .h := by
  unfold CRNT.Complex.massActionMonomial
  rw [BZSpecies.univ_eq]
  simp [stepA2]
  ring

/-- Mass-action monomial of the source of step (3): `[HBrO2]²`. -/
theorem monomial_stepA3 (x : CRNT.Concentration BZSpecies) :
    (stepA3.source).massActionMonomial x = (x .hbrO2) ^ 2 := by
  unfold CRNT.Complex.massActionMonomial
  rw [BZSpecies.univ_eq]
  simp [stepA3]

/-- Mass-action monomial of the source of step (4): `[HBrO2][Br⁻][H⁺]`. -/
theorem monomial_stepB1 (x : CRNT.Concentration BZSpecies) :
    (stepB1.source).massActionMonomial x = x .hbrO2 * x .br * x .h := by
  unfold CRNT.Complex.massActionMonomial
  rw [BZSpecies.univ_eq]
  simp [stepB1]
  ring

/-- Mass-action monomial of the source of step (5): `[BrO3⁻][Br⁻][H⁺]²`. -/
theorem monomial_stepB2 (x : CRNT.Concentration BZSpecies) :
    (stepB2.source).massActionMonomial x = x .brO3 * x .br * (x .h) ^ 2 := by
  unfold CRNT.Complex.massActionMonomial
  rw [BZSpecies.univ_eq]
  simp [stepB2]
  ring

/-- Mass-action monomial of the source of step (6): `[HBrO][MA]`. -/
theorem monomial_stepB3 (x : CRNT.Concentration BZSpecies) :
    (stepB3.source).massActionMonomial x = x .hbrO * x .ma := by
  unfold CRNT.Complex.massActionMonomial
  rw [BZSpecies.univ_eq]
  simp [stepB3]

/-- Rate of step (1): `r1 = k1 [HBrO2][BrO3⁻][H⁺]`. -/
theorem rate_A1 (x : CRNT.Concentration BZSpecies) :
    processA.massActionRate κA (0 : Fin 3) x = k1 * (x .hbrO2 * x .brO3 * x .h) := by
  change k1 * (stepA1.source).massActionMonomial x = _
  rw [monomial_stepA1]

/-- Rate of step (2): `r2 = k2 [BrO2•][Ce³⁺][H⁺]`. -/
theorem rate_A2 (x : CRNT.Concentration BZSpecies) :
    processA.massActionRate κA (1 : Fin 3) x = k2 * (x .brO2 * x .ce3 * x .h) := by
  change k2 * (stepA2.source).massActionMonomial x = _
  rw [monomial_stepA2]

/-- Rate of step (3): `r3 = k3 [HBrO2]²`. -/
theorem rate_A3 (x : CRNT.Concentration BZSpecies) :
    processA.massActionRate κA (2 : Fin 3) x = k3 * (x .hbrO2) ^ 2 := by
  change k3 * (stepA3.source).massActionMonomial x = _
  rw [monomial_stepA3]

/-- Rate of step (4): `r4 = k4 [HBrO2][Br⁻][H⁺]`. -/
theorem rate_B1 (x : CRNT.Concentration BZSpecies) :
    processB.massActionRate κB (0 : Fin 3) x = k4 * (x .hbrO2 * x .br * x .h) := by
  change k4 * (stepB1.source).massActionMonomial x = _
  rw [monomial_stepB1]

/-- Rate of step (5): `r5 = k5 [BrO3⁻][Br⁻][H⁺]²`. -/
theorem rate_B2 (x : CRNT.Concentration BZSpecies) :
    processB.massActionRate κB (1 : Fin 3) x = k5 * (x .brO3 * x .br * (x .h) ^ 2) := by
  change k5 * (stepB2.source).massActionMonomial x = _
  rw [monomial_stepB2]

/-- Rate of step (6): `r6 = k6 [HBrO][MA]`. -/
theorem rate_B3 (x : CRNT.Concentration BZSpecies) :
    processB.massActionRate κB (2 : Fin 3) x = k6 * (x .hbrO * x .ma) := by
  change k6 * (stepB3.source).massActionMonomial x = _
  rw [monomial_stepB3]

/-- Bridge: the Process-A vector field on HBrO₂ is `−r1 + r2 − 2 r3`. -/
theorem vectorField_A_hbrO2 (x : CRNT.Concentration BZSpecies) :
    processA.massActionVectorField κA x .hbrO2 = dHBrO2_A x := by
  have vec0 : processA.reactionVector (0 : Fin 3) BZSpecies.hbrO2 = -1 := by
    change ((stepA1.target BZSpecies.hbrO2 : ℝ) - (stepA1.source BZSpecies.hbrO2 : ℝ)) = -1
    norm_num [stepA1]
  have vec1 : processA.reactionVector (1 : Fin 3) BZSpecies.hbrO2 = 1 := by
    change ((stepA2.target BZSpecies.hbrO2 : ℝ) - (stepA2.source BZSpecies.hbrO2 : ℝ)) = 1
    norm_num [stepA2]
  have vec2 : processA.reactionVector (2 : Fin 3) BZSpecies.hbrO2 = -2 := by
    change ((stepA3.target BZSpecies.hbrO2 : ℝ) - (stepA3.source BZSpecies.hbrO2 : ℝ)) = -2
    norm_num [stepA3]
  change (∑ r : Fin 3, processA.massActionRate κA r x
      * processA.reactionVector r BZSpecies.hbrO2) = dHBrO2_A x
  simp only [Fin.sum_univ_three, rate_A1, rate_A2, rate_A3, vec0, vec1, vec2]
  unfold dHBrO2_A
  ring

/-- Bridge: the Process-A vector field on BrO2• is `2 r1 − r2`. -/
theorem vectorField_A_brO2 (x : CRNT.Concentration BZSpecies) :
    processA.massActionVectorField κA x .brO2 = dBrO2_A x := by
  have vec0 : processA.reactionVector (0 : Fin 3) BZSpecies.brO2 = 2 := by
    change ((stepA1.target BZSpecies.brO2 : ℝ) - (stepA1.source BZSpecies.brO2 : ℝ)) = 2
    norm_num [stepA1]
  have vec1 : processA.reactionVector (1 : Fin 3) BZSpecies.brO2 = -1 := by
    change ((stepA2.target BZSpecies.brO2 : ℝ) - (stepA2.source BZSpecies.brO2 : ℝ)) = -1
    norm_num [stepA2]
  have vec2 : processA.reactionVector (2 : Fin 3) BZSpecies.brO2 = 0 := by
    change ((stepA3.target BZSpecies.brO2 : ℝ) - (stepA3.source BZSpecies.brO2 : ℝ)) = 0
    norm_num [stepA3]
  change (∑ r : Fin 3, processA.massActionRate κA r x
      * processA.reactionVector r BZSpecies.brO2) = dBrO2_A x
  simp only [Fin.sum_univ_three, rate_A1, rate_A2, rate_A3, vec0, vec1, vec2]
  unfold dBrO2_A
  ring

/-- Bridge: the Process-B vector field on HBrO₂ is `−r4 + r5`. -/
theorem vectorField_B_hbrO2 (x : CRNT.Concentration BZSpecies) :
    processB.massActionVectorField κB x .hbrO2 = dHBrO2_B x := by
  have vec0 : processB.reactionVector (0 : Fin 3) BZSpecies.hbrO2 = -1 := by
    change ((stepB1.target BZSpecies.hbrO2 : ℝ) - (stepB1.source BZSpecies.hbrO2 : ℝ)) = -1
    norm_num [stepB1]
  have vec1 : processB.reactionVector (1 : Fin 3) BZSpecies.hbrO2 = 1 := by
    change ((stepB2.target BZSpecies.hbrO2 : ℝ) - (stepB2.source BZSpecies.hbrO2 : ℝ)) = 1
    norm_num [stepB2]
  have vec2 : processB.reactionVector (2 : Fin 3) BZSpecies.hbrO2 = 0 := by
    change ((stepB3.target BZSpecies.hbrO2 : ℝ) - (stepB3.source BZSpecies.hbrO2 : ℝ)) = 0
    norm_num [stepB3]
  change (∑ r : Fin 3, processB.massActionRate κB r x
      * processB.reactionVector r BZSpecies.hbrO2) = dHBrO2_B x
  simp only [Fin.sum_univ_three, rate_B1, rate_B2, rate_B3, vec0, vec1, vec2]
  unfold dHBrO2_B
  ring

theorem processASSA_iff_poly (x : CRNT.Concentration BZSpecies) :
    ProcessASSA x ↔ ProcessASSA_poly x := by
  unfold ProcessASSA ProcessASSA_poly
  rw [vectorField_A_hbrO2, vectorField_A_brO2]

theorem processBSSA_iff_poly (x : CRNT.Concentration BZSpecies) :
    ProcessBSSA x ↔ ProcessBSSA_poly x := by
  unfold ProcessBSSA ProcessBSSA_poly
  rw [vectorField_B_hbrO2]

/-! ## Closed forms forced by the steady-state approximation -/

/-- Stationary `[HBrO2]` in Process A: the SSA forces
`k1 [BrO3⁻][H⁺] = 2 k3 [HBrO2]`, hence `[HBrO2]_A = k1 [BrO3⁻][H⁺] / (2 k3)`. -/
noncomputable def stationaryHBrO2_A : ℝ := k1 * bromateConc * protonConc / (2 * k3)

/-- Stationary `[HBrO2]` in Process B: the SSA forces
`k4 [HBrO2][H⁺] = k5 [BrO3⁻][H⁺]²` (the positive `[Br⁻]` cancels), hence
`[HBrO2]_B = k5 [BrO3⁻][H⁺] / k4`. -/
noncomputable def stationaryHBrO2_B : ℝ := k5 * bromateConc * protonConc / k4

/-- Derivation for Process A from the polynomial SSA balances:
`−r1 + r2 − 2 r3 = 0` and `2 r1 − r2 = 0` give `r1 = 2 r3`, i.e.
`k1 [BrO3⁻][H⁺] = 2 k3 [HBrO2]`; cancelling the positive `[HBrO2]` yields the
closed form. -/
theorem stationary_A_of_polySSA (x : CRNT.Concentration BZSpecies) (hx : 0 < x .hbrO2)
    (hss : ProcessASSA_poly x) (hbro3 : x .brO3 = bromateConc) (hh : x .h = protonConc) :
    x .hbrO2 = stationaryHBrO2_A := by
  obtain ⟨h1, h2⟩ := hss
  unfold dHBrO2_A at h1
  unfold dBrO2_A at h2
  rw [hbro3, hh] at h1 h2
  have hsum : k1 * x .hbrO2 * bromateConc * protonConc = 2 * (k3 * (x .hbrO2) ^ 2) := by
    linear_combination h1 + h2
  have hxne : x .hbrO2 ≠ 0 := ne_of_gt hx
  have e1 : k1 * x .hbrO2 * bromateConc * protonConc
      = x .hbrO2 * (k1 * bromateConc * protonConc) := by ring
  have e2 : 2 * (k3 * (x .hbrO2) ^ 2) = x .hbrO2 * (2 * k3 * x .hbrO2) := by ring
  rw [e1, e2] at hsum
  have hcancel : k1 * bromateConc * protonConc = 2 * k3 * x .hbrO2 :=
    mul_left_cancel₀ hxne hsum
  unfold stationaryHBrO2_A
  rw [eq_div_iff (show (2 : ℝ) * k3 ≠ 0 by norm_num [k3])]
  linear_combination -hcancel

/-- Derivation for Process B from the polynomial SSA balance:
`−r4 + r5 = 0`, i.e. `k4 [HBrO2][Br⁻][H⁺] = k5 [BrO3⁻][Br⁻][H⁺]²`; cancelling the
positive `[Br⁻]` and one factor of `[H⁺]` yields the closed form. -/
theorem stationary_B_of_polySSA (x : CRNT.Concentration BZSpecies) (hbr : 0 < x .br)
    (hss : ProcessBSSA_poly x) (hbro3 : x .brO3 = bromateConc) (hh : x .h = protonConc) :
    x .hbrO2 = stationaryHBrO2_B := by
  have h1 : dHBrO2_B x = 0 := hss
  unfold dHBrO2_B at h1
  rw [hbro3, hh] at h1
  have e1 : -(k4 * x .hbrO2 * x .br * protonConc)
        + k5 * bromateConc * x .br * protonConc ^ 2
      = x .br * (k5 * bromateConc * protonConc ^ 2 - k4 * protonConc * x .hbrO2) := by
    ring
  rw [e1] at h1
  have hfac : k5 * bromateConc * protonConc ^ 2 - k4 * protonConc * x .hbrO2 = 0 :=
    (mul_eq_zero.mp h1).resolve_left (ne_of_gt hbr)
  have hfac2 : k5 * bromateConc * protonConc ^ 2 = k4 * protonConc * x .hbrO2 := by
    linear_combination hfac
  have hcancel : k4 * x .hbrO2 = k5 * bromateConc * protonConc := by
    apply mul_left_cancel₀ (show (protonConc : ℝ) ≠ 0 by norm_num [protonConc])
    linear_combination -hfac2
  unfold stationaryHBrO2_B
  rw [eq_div_iff (show (k4 : ℝ) ≠ 0 by norm_num [k4])]
  linear_combination hcancel

/-- The stationary HBrO₂ concentration in Process A from the CRNT steady-state
model: every positive stationary state of the Process-A network with the
buffered concentrations attains the closed form. -/
theorem stationary_A_of_SSA (x : CRNT.Concentration BZSpecies) (hb : BufferedConc x)
    (hx : 0 < x .hbrO2) (hss : ProcessASSA x) :
    x .hbrO2 = stationaryHBrO2_A :=
  stationary_A_of_polySSA x hx ((processASSA_iff_poly x).mp hss) hb.1 hb.2.2

/-- The stationary HBrO₂ concentration in Process B from the CRNT steady-state
model. -/
theorem stationary_B_of_SSA (x : CRNT.Concentration BZSpecies) (hb : BufferedConc x)
    (hbr : 0 < x .br) (hss : ProcessBSSA x) :
    x .hbrO2 = stationaryHBrO2_B :=
  stationary_B_of_polySSA x hbr ((processBSSA_iff_poly x).mp hss) hb.1 hb.2.2

/-! ## Exact raw values (no intermediate rounding) -/

/-- Exact raw value of `[HBrO2]_A`:
`k1 [BrO3⁻][H⁺] / (2 k3) = (1.0 × 10⁴)(0.06)(0.8) / (2 · 4.0 × 10⁷) = 6 / 10⁶`. -/
theorem stationaryHBrO2_A_exact : stationaryHBrO2_A = (6 : ℝ) / 10 ^ 6 := by
  norm_num [stationaryHBrO2_A, k1, k3, bromateConc, protonConc]

/-- Exact raw value of `[HBrO2]_B`:
`k5 [BrO3⁻][H⁺] / k4 = (2.1)(0.06)(0.8) / (2.0 × 10⁹) = 504 / 10¹³`. -/
theorem stationaryHBrO2_B_exact : stationaryHBrO2_B = (504 : ℝ) / 10 ^ 13 := by
  norm_num [stationaryHBrO2_B, k4, k5, bromateConc, protonConc]

/-- Strict rational enclosure of the raw `[HBrO2]_A` (fixed before rounding). -/
theorem stationaryHBrO2_A_bounds :
    (5 : ℝ) / 10 ^ 6 < stationaryHBrO2_A ∧ stationaryHBrO2_A < (7 : ℝ) / 10 ^ 6 := by
  rw [stationaryHBrO2_A_exact]
  constructor <;> norm_num

/-- Strict rational enclosure of the raw `[HBrO2]_B` (fixed before rounding). -/
theorem stationaryHBrO2_B_bounds :
    (5 : ℝ) / 10 ^ 11 < stationaryHBrO2_B ∧ stationaryHBrO2_B < (51 : ℝ) / 10 ^ 12 := by
  rw [stationaryHBrO2_B_exact]
  constructor <;> norm_num

/-! ## Reporting at the three-significant-figure quantum
(uniform blind evaluation default of the source report; ties half away from zero) -/

/-- `[HBrO2]_A` reported to three significant figures is `6.00 × 10⁻⁶ mol dm⁻³`;
the reporting quantum is `10⁻⁸` and the raw value `6 / 10⁶` lies in the
half-quantum cell around `6.00 × 10⁻⁶`. -/
theorem reportsAtQuantum_A :
    IChO2026Chem.Reporting.ReportsAtQuantum stationaryHBrO2_A (6.0e-6 : ℝ) (1.0e-8 : ℝ) := by
  have hA : stationaryHBrO2_A = (6.0e-6 : ℝ) := by
    rw [stationaryHBrO2_A_exact]
    norm_num
  rw [hA]
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨600, by norm_num⟩, ?_⟩
  rw [if_pos (show (0 : ℝ) ≤ 6.0e-6 by norm_num)]
  exact ⟨by norm_num, by norm_num⟩

/-- `[HBrO2]_B` reported to three significant figures is `5.04 × 10⁻¹¹ mol dm⁻³`;
the reporting quantum is `10⁻¹³` and the raw value `504 / 10¹³` lies in the
half-quantum cell around `5.04 × 10⁻¹¹`. -/
theorem reportsAtQuantum_B :
    IChO2026Chem.Reporting.ReportsAtQuantum stationaryHBrO2_B (5.04e-11 : ℝ) (1.0e-13 : ℝ) := by
  have hB : stationaryHBrO2_B = (5.04e-11 : ℝ) := by
    rw [stationaryHBrO2_B_exact]
    norm_num
  rw [hB]
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨504, by norm_num⟩, ?_⟩
  rw [if_pos (show (0 : ℝ) ≤ 5.04e-11 by norm_num)]
  exact ⟨by norm_num, by norm_num⟩

/-! ## Answer-blind result contracts -/

/-- Raw-result specification: both stationary concentrations, exposed as their
unrounded closed forms with exact rational values, certified strict rational
enclosures, and the statement that they are forced by the steady-state
approximation on the problem's mass-action networks. -/
def RawStationarySpec : Prop :=
  stationaryHBrO2_A = k1 * bromateConc * protonConc / (2 * k3) ∧
  stationaryHBrO2_B = k5 * bromateConc * protonConc / k4 ∧
  stationaryHBrO2_A = (6 : ℝ) / 10 ^ 6 ∧
  stationaryHBrO2_B = (504 : ℝ) / 10 ^ 13 ∧
  (∀ x : CRNT.Concentration BZSpecies,
    BufferedConc x → 0 < x .hbrO2 → ProcessASSA x → x .hbrO2 = stationaryHBrO2_A) ∧
  (∀ x : CRNT.Concentration BZSpecies,
    BufferedConc x → 0 < x .br → ProcessBSSA x → x .hbrO2 = stationaryHBrO2_B) ∧
  (5 : ℝ) / 10 ^ 6 < stationaryHBrO2_A ∧
  stationaryHBrO2_A < (7 : ℝ) / 10 ^ 6 ∧
  (5 : ℝ) / 10 ^ 11 < stationaryHBrO2_B ∧
  stationaryHBrO2_B < (51 : ℝ) / 10 ^ 12

/-- Reported-result specification: both stationary concentrations reported at
their three-significant-figure quanta. -/
def ReportedStationarySpec : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum stationaryHBrO2_A (6.0e-6 : ℝ) (1.0e-8 : ℝ) ∧
  IChO2026Chem.Reporting.ReportsAtQuantum stationaryHBrO2_B (5.04e-11 : ℝ) (1.0e-13 : ℝ)

theorem raw_result_contract :
    ("8b822b23d7960c1c2b7f92f687709554ef750c367c06b519b98d354100f28b23" : String)
      = "8b822b23d7960c1c2b7f92f687709554ef750c367c06b519b98d354100f28b23" ∧
    IChO2026.T2.A2.RawStationarySpec := by
  exact ⟨rfl, rfl, rfl,
    stationaryHBrO2_A_exact, stationaryHBrO2_B_exact,
    stationary_A_of_SSA, stationary_B_of_SSA,
    stationaryHBrO2_A_bounds.1, stationaryHBrO2_A_bounds.2,
    stationaryHBrO2_B_bounds.1, stationaryHBrO2_B_bounds.2⟩

theorem reported_result_contract :
    ("9e38db61eebceec4d0120af6a14700b6790776c9c0d5dc76dd11a0792dae02e4" : String)
      = "9e38db61eebceec4d0120af6a14700b6790776c9c0d5dc76dd11a0792dae02e4" ∧
    IChO2026.T2.A2.ReportedStationarySpec :=
  ⟨rfl, reportsAtQuantum_A, reportsAtQuantum_B⟩

end IChO2026.T2.A2
