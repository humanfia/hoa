/-
Copyright (c) 2026 Archon answer-blind IChO formalization project. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon chemistry-formalize agent
-/
import IChO2026Chem

/-!
# IChO 2026, Problem T8, subquestion 8.9 (target `icho_2026_t8_a9`)

**Problem.** (Sealed problem bundle: T8 page 5, question 8.9, with the
Jablonski diagram on the same page.)  A photosensitiser (PS) undergoes
reductive quenching of its singlet (S1) and triplet (T1) excited states by a
reductant (Red):

* `PS(S1) + Red → PS•− + Red•+` with `kS = 2.7 × 10^9 M⁻¹ s⁻¹`;
* `PS(T1) + Red → PS•− + Red•+` with `kT = 1.5 × 10^8 M⁻¹ s⁻¹`.

The emission lifetimes in the absence of quencher are `τ0(S1) = 2.9 ns` and
`τ0(T1) = 84 μs`.  Question 8.9 asks for the percentage of quenching `ηq`
(in %) of the S1 and T1 states when `[Red] = 0.1 M`, with the printed side
condition `kF ≫ kISC`.

**Requested outputs.** (i) `ηq(S1)` in %; (ii) `ηq(T1)` in % — each reported
to 3 significant figures under the per-requested-output policy
(`uniform_blind_evaluation_default`).

**Governing relation (provenance: trusted_general_law, Stern–Volmer quenching
kinetics, applied to the Jablonski scheme on T8 page 5).**  Each excited state
decays intrinsically with total first-order rate `k0 = 1 / τ0` (the emission
lifetime subsumes every intrinsic channel: for S1 the fluorescence `kF`,
internal conversion `kIC` and intersystem crossing `kISC`; for T1 the
phosphorescence `kP`, non-radiative decay `kN` and reverse intersystem
crossing `kRISC`).  Reductive quenching adds the pseudo-first-order channel
`kq · [Red]`.  The fraction of excited states intercepted by Red is therefore

`ηq = kq · [Red] / (kq · [Red] + 1 / τ0) = kq · [Red] · τ0 / (1 + kq · [Red] · τ0)`.

The printed note `kF ≫ kISC` keeps the S1 → T1 → S1 cycling negligible for the
S1 decay budget, so each state's quenching percentage is the plain two-channel
competition against its own `1 / τ0`.

**Raw derivation (no intermediate rounding).**
* S1: `kS · [Red] · τ0(S1) = 2.7 × 10^9 · 0.1 · 2.9 × 10⁻⁹ = 0.783`, hence
  `ηq(S1) = 0.783 / 1.783 = 783 / 1783` and
  `100 · ηq(S1) = 78300 / 1783 = 43.91475042… %`, enclosed in
  `[4391/100, 4392/100]` %.
* T1: `kT · [Red] · τ0(T1) = 1.5 × 10^8 · 0.1 · 84 × 10⁻⁶ = 1260`, hence
  `ηq(T1) = 1260 / 1261` and
  `100 · ηq(T1) = 126000 / 1261 = 99.92069785… %`, enclosed in
  `[9992/100, 9993/100]` %.

**Reported results (3 significant figures, ties half away from zero; quantum
`0.1 %` for both outputs).**  `ηq(S1) = 43.9 %` and `ηq(T1) = 99.9 %`.
-/

namespace IChO2026Problems.Icho2026T8A9

/-! ## Problem-stipulated constants (T8 page 5; exact as printed) -/

/-- Bimolecular reductive-quenching constant of the S1 state,
`kS = 2.7 × 10^9 M⁻¹ s⁻¹` (printed below the PS(S1) + Red equation). -/
noncomputable def kS : ℝ := 2.7e9

/-- Bimolecular reductive-quenching constant of the T1 state,
`kT = 1.5 × 10^8 M⁻¹ s⁻¹` (printed below the PS(T1) + Red equation). -/
noncomputable def kT : ℝ := 1.5e8

/-- Emission lifetime of S1 in the absence of quencher,
`τ0(S1) = 2.9 ns = 2.9 × 10⁻⁹ s`. -/
noncomputable def tau0S1 : ℝ := 2.9e-9

/-- Emission lifetime of T1 in the absence of quencher,
`τ0(T1) = 84 μs = 84 × 10⁻⁶ s`. -/
noncomputable def tau0T1 : ℝ := 84e-6

/-- Quencher concentration stipulated by question 8.9: `[Red] = 0.1 M`. -/
noncomputable def cRed : ℝ := 0.1

/-! ## Jablonski channel picture (semantic context from the T8 page 5 diagram) -/

/-- Channel decomposition of the unquenched decay rates read off the Jablonski
diagram on T8 page 5: S1 decays intrinsically by fluorescence (`kF`), internal
conversion (`kIC`) and intersystem crossing (`kISC`); T1 by phosphorescence
(`kP`), non-radiative decay (`kN`) and reverse intersystem crossing (`kRISC`).
The emission lifetime is defined by `k0 = 1 / τ0` in each state, so the sums of
intrinsic channels equal `1 / tau0S1` and `1 / tau0T1`.  The printed side
condition `kF ≫ kISC` (fluorescence dominates intersystem crossing) places the
PS in the regime where the measured emission lifetimes already absorb the
ISC/RISC cycling, so each state's quenching percentage is the two-channel
competition against its own `1 / τ0`; `hFdom` records the direct consequence
`kISC ≤ kF`. -/
structure JablonskiChannels where
  kF : ℝ
  kIC : ℝ
  kISC : ℝ
  kP : ℝ
  kN : ℝ
  kRISC : ℝ
  hS1 : kF + kIC + kISC = 1 / tau0S1
  hT1 : kP + kN + kRISC = 1 / tau0T1
  hFdom : kISC ≤ kF

/-! ## Governing relation: Stern–Volmer quenching competition -/

/-- Total intrinsic first-order decay rate of an excited state with unquenched
emission lifetime `τ0`: `k0 = 1 / τ0`. -/
noncomputable def intrinsicRate (τ0 : ℝ) : ℝ := 1 / τ0

/-- Pseudo-first-order quenching rate of an excited state with bimolecular
quenching constant `kq` at quencher concentration `c`: `kq · c`. -/
noncomputable def quenchRate (kq c : ℝ) : ℝ := kq * c

/-- Fraction of an excited state quenched by the reductant: the
Stern–Volmer competition of the quenching channel against the intrinsic decay,
`ηq = kq · c / (kq · c + 1 / τ0)`. -/
noncomputable def quenchedFraction (kq c τ0 : ℝ) : ℝ :=
  quenchRate kq c / (quenchRate kq c + intrinsicRate τ0)

/-- The quenched fraction expressed as a percentage. -/
noncomputable def quenchedPercent (kq c τ0 : ℝ) : ℝ :=
  100 * quenchedFraction kq c τ0

/-- Equivalent Stern–Volmer form `ηq = K / (1 + K)` with
`K = kq · c · τ0` the dimensionless Stern–Volmer product. -/
theorem quenchedFraction_eq_sternVolmer {kq c τ0 : ℝ} (hτ : τ0 ≠ 0) :
    quenchedFraction kq c τ0 = (kq * c * τ0) / (1 + kq * c * τ0) := by
  have h1 : (kq * c + 1 / τ0) * τ0 = kq * c * τ0 + 1 := by
    rw [add_mul, div_mul_cancel₀ 1 hτ]
  unfold quenchedFraction quenchRate intrinsicRate
  rw [← mul_div_mul_right (kq * c) (kq * c + 1 / τ0) hτ, h1, add_comm]

/-! ## State-specific raw quantities -/

/-- Raw quenched fraction of the S1 state at `[Red] = 0.1 M`. -/
noncomputable def s1QuenchingFraction : ℝ := quenchedFraction kS cRed tau0S1

/-- Raw quenched fraction of the T1 state at `[Red] = 0.1 M`. -/
noncomputable def t1QuenchingFraction : ℝ := quenchedFraction kT cRed tau0T1

/-- Raw quenching percentage of the S1 state (unrounded, in %). -/
noncomputable def s1QuenchingPercentRaw : ℝ := 100 * s1QuenchingFraction

/-- Raw quenching percentage of the T1 state (unrounded, in %). -/
noncomputable def t1QuenchingPercentRaw : ℝ := 100 * t1QuenchingFraction

/-- Exact value of the S1 quenched fraction:
`2.7 × 10^9 · 0.1 / (2.7 × 10^9 · 0.1 + 1 / (2.9 × 10⁻⁹)) = 783 / 1783`. -/
theorem s1QuenchingFraction_value : s1QuenchingFraction = 783 / 1783 := by
  norm_num [s1QuenchingFraction, quenchedFraction, quenchRate, intrinsicRate,
    kS, cRed, tau0S1]

/-- Exact value of the T1 quenched fraction:
`1.5 × 10^8 · 0.1 / (1.5 × 10^8 · 0.1 + 1 / (84 × 10⁻⁶)) = 1260 / 1261`. -/
theorem t1QuenchingFraction_value : t1QuenchingFraction = 1260 / 1261 := by
  norm_num [t1QuenchingFraction, quenchedFraction, quenchRate, intrinsicRate,
    kT, cRed, tau0T1]

/-- Exact raw S1 quenching percentage: `78300 / 1783 %`. -/
theorem s1QuenchingPercentRaw_value : s1QuenchingPercentRaw = 78300 / 1783 := by
  unfold s1QuenchingPercentRaw
  rw [s1QuenchingFraction_value]
  norm_num

/-- Exact raw T1 quenching percentage: `126000 / 1261 %`. -/
theorem t1QuenchingPercentRaw_value : t1QuenchingPercentRaw = 126000 / 1261 := by
  unfold t1QuenchingPercentRaw
  rw [t1QuenchingFraction_value]
  norm_num

/-- Certified non-degenerate enclosure of the raw S1 percentage:
`43.91 ≤ 78300/1783 ≤ 43.92`. -/
theorem s1QuenchingPercentRaw_interval :
    (4391 / 100 : ℝ) ≤ s1QuenchingPercentRaw
      ∧ s1QuenchingPercentRaw ≤ (4392 / 100 : ℝ) := by
  rw [s1QuenchingPercentRaw_value]
  constructor <;> norm_num

/-- Certified non-degenerate enclosure of the raw T1 percentage:
`99.92 ≤ 126000/1261 ≤ 99.93`. -/
theorem t1QuenchingPercentRaw_interval :
    (9992 / 100 : ℝ) ≤ t1QuenchingPercentRaw
      ∧ t1QuenchingPercentRaw ≤ (9993 / 100 : ℝ) := by
  rw [t1QuenchingPercentRaw_value]
  constructor <;> norm_num

/-! ## Reported values at the 3-significant-figure quantum 0.1 % -/

/-- The raw S1 percentage `78300/1783 ≈ 43.91475` reports as `43.9` at the
`0.1 %` quantum (3 significant figures): `43.85 ≤ 78300/1783 < 43.95` and
`43.9 = 0.1 · 439`. -/
theorem s1Reported :
    IChO2026Chem.Reporting.ReportsAtQuantum s1QuenchingPercentRaw 43.9 0.1 := by
  have hval := s1QuenchingPercentRaw_value
  have h0 : 0 ≤ s1QuenchingPercentRaw := by rw [hval]; norm_num
  refine ⟨by norm_num, ⟨439, by norm_num⟩, ?_⟩
  rw [if_pos h0, hval]
  constructor <;> norm_num

/-- The raw T1 percentage `126000/1261 ≈ 99.92070` reports as `99.9` at the
`0.1 %` quantum (3 significant figures): `99.85 ≤ 126000/1261 < 99.95` and
`99.9 = 0.1 · 999`. -/
theorem t1Reported :
    IChO2026Chem.Reporting.ReportsAtQuantum t1QuenchingPercentRaw 99.9 0.1 := by
  have hval := t1QuenchingPercentRaw_value
  have h0 : 0 ≤ t1QuenchingPercentRaw := by rw [hval]; norm_num
  refine ⟨by norm_num, ⟨999, by norm_num⟩, ?_⟩
  rw [if_pos h0, hval]
  constructor <;> norm_num

/-! ## Raw and reported result specifications (both requested outputs) -/

/-- Raw derivation spec covering both requested outputs before any reporting
rounding: each state's quenched fraction is the Stern–Volmer competition of
its printed `kq · [Red]` against `1 / τ0`; the exact unrounded values are
`783/1783` (S1) and `1260/1261` (T1); the percentages are `100` times the
fractions; and both raw percentages carry certified non-degenerate enclosures
`[43.91, 43.92]` % and `[99.92, 99.93]` % respectively. -/
def RawResultSpec : Prop :=
  s1QuenchingFraction = kS * cRed / (kS * cRed + 1 / tau0S1)
    ∧ s1QuenchingFraction = 783 / 1783
    ∧ t1QuenchingFraction = kT * cRed / (kT * cRed + 1 / tau0T1)
    ∧ t1QuenchingFraction = 1260 / 1261
    ∧ s1QuenchingPercentRaw = 100 * s1QuenchingFraction
    ∧ t1QuenchingPercentRaw = 100 * t1QuenchingFraction
    ∧ ((4391 / 100 : ℝ) ≤ s1QuenchingPercentRaw
        ∧ s1QuenchingPercentRaw ≤ (4392 / 100 : ℝ))
    ∧ ((9992 / 100 : ℝ) ≤ t1QuenchingPercentRaw
        ∧ t1QuenchingPercentRaw ≤ (9993 / 100 : ℝ))

/-- Reported (final) spec: both quenching percentages reported at the
3-significant-figure quantum `0.1 %` — `ηq(S1) = 43.9 %` and
`ηq(T1) = 99.9 %` — via `IChO2026Chem.Reporting.ReportsAtQuantum`. -/
def ReportedResultSpec : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum s1QuenchingPercentRaw 43.9 0.1
    ∧ IChO2026Chem.Reporting.ReportsAtQuantum t1QuenchingPercentRaw 99.9 0.1

/-- Raw result certificate: binds the answer-blind raw-role payload digest to
`RawResultSpec`. -/
theorem rawResultCertificate :
    ("37fdb1d288db04d99df0ca93e6800a0dad05617f71c0989976bf9f08b2ce412f" : String)
      = "37fdb1d288db04d99df0ca93e6800a0dad05617f71c0989976bf9f08b2ce412f"
      ∧ IChO2026Problems.Icho2026T8A9.RawResultSpec :=
  ⟨rfl, rfl, s1QuenchingFraction_value, rfl, t1QuenchingFraction_value, rfl,
    rfl, s1QuenchingPercentRaw_interval, t1QuenchingPercentRaw_interval⟩

/-- Reported result certificate: binds the answer-blind reported-role payload
digest to `ReportedResultSpec`. -/
theorem reportedResultCertificate :
    ("8e80decfcf406595a1956a70c16234928787e6bdfc4870a0a14e73523c702dc1" : String)
      = "8e80decfcf406595a1956a70c16234928787e6bdfc4870a0a14e73523c702dc1"
      ∧ IChO2026Problems.Icho2026T8A9.ReportedResultSpec :=
  ⟨rfl, s1Reported, t1Reported⟩

end IChO2026Problems.Icho2026T8A9
