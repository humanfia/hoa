import Mathlib

/-!
# IChO 2026, Theory Problem T1, subquestion 1.4 (`icho_2026_t1_a4`)

## Problem (official English paper, printed page 3, source page 8)

> Avicenna had told her the **stone** was a stoichiometric compound. She
> dissolved it in dilute nitric acid. After that, she adjusted the pH of the
> solution to ~4 and added NaF. This led to the formation of precipitate
> **C ⋅ xH₂O**, which contained **39.16 % water by mass**. Anhydrous **C**
> reacts with an **excess of NaF** to yield compound **D**, which contains
> **32.85 % sodium** and **12.85 % of metal Q** by mass, and is used in the
> **industrial production of Q**.
>
> **1.4  Identify metal Q and compounds C ⋅ xH₂O and D.  (4.0 pt)**

The blank answer sheet (page A1-3) requests `Q :`, `C ⋅ xH₂O :`, `D :`.

## What is problem-given and what is declared modelling input

**Problem-given** (exact as printed): the percentages 39.16 %, 32.85 %,
12.85 %, interpreted by the stated measurement policy as the *centres* of
half-quantum intervals of width 0.01 % (displayed quantum); the reagent NaF;
the fact that the stone is stoichiometric; and the periodic table on page G1-5
of the same paper, transcribed verbatim as `ArTable`.

**Declared model assumptions** (the standard chemical reading; no logical
derivation of empirical chemistry is possible):

* **M-A4-1** — `C = QFᵥ`, `v ∈ {2, 3}` (the common metal-fluoride
  stoichiometries), and the hydrate `C ⋅ xH₂O = QFᵥ ⋅ xH₂O`, `x ≥ 1`.
  The wider family `v ∈ {1,…,5}` adds the spurious self-similar line
  `(v,x,n)=(5,5,5)` matching the printed Ar of scandium numerically, but ScF₅
  does not exist (group-3 metal, exclusively +3), whereas v ∈ {2,3} is the
  chemically meaningful family and yields a unique answer.  The restriction
  is a declared assumption, and the answer survives even without it (see
  `source_gaps` in `result.json`).
* **M-A4-2** — `D = C ⬝ n NaF = NaₙQF_{v+n}`, `n ≥ 1` (as cryolite
  Na₃AlF₆ = AlF₃ ⬝ 3 NaF).
* **M-A4-3** — `0 < Ar(Q) ≤ 294` (heaviest element is oganesson, [Ar] = 294).
* **M-A4-4** — the true Ar(Q) matches a *printed* table value at half-quantum
  precision: `|Ar(Q) − 26.98| < 5/1000` after identification.  Used only in
  Part V to re-tighten the mass window around the identified element before
  re-deriving `x, n`; no answer is assumed — `Ar(Q) = 26.98` is *derived*
  in Part IV from a v = 3 contradiction argument against the table.

## Theorems

* `answer_aluminium` — **Q = aluminium, C·xH₂O = AlF₃·3H₂O, D = Na₃AlF₆**
  reproduces all three printed percentages strictly inside the displayed
  half-quantum windows (existence/verification).
* `envelope_v2` / `table_no_match_v2` — every valence-2 candidate forces
  `17.9725 < Ar(Q) < 17.997`, and no printed table mass lies within half a
  quantum of that window: `v = 2` is disproved by the periodic table.
* `envelope_v3` / `table_match_v3` — every valence-3 candidate forces
  `26.945 < Ar(Q) < 26.9943`, whose half-quantum neighbourhood contains
  exactly one printed table value, 26.98 at atomic number 13 (aluminium).
* `stoichiometry_at_aluminium` — with `Ar(Q)` re-tightened to aluminium's
  half-quantum `26.975 < ArQ < 26.985`, the hydration datum alone forces
  `x = 3` and the sodium datum alone forces `n = 3`, i.e. `C = AlF₃`,
  `C ⋅ xH₂O = AlF₃·3H₂O`, `D = Na₃AlF₆`.
* `main_answer` — the assembled answer to 1.4, with uniqueness.

No `sorry`/`admit`, no custom axioms.  All arithmetic is exact over ℚ and
discharged by `norm_num` / `linarith` / `interval_cases`.
-/

namespace IChO2026Problems.T1A4

/-! ## The periodic table (page G1-5), transcribed verbatim

Only the entries with a printed mass matter.  Tc, Pm, and the dashed-border
elements Z ≥ 84 show no mass and map to `none`.  Entry `z : Fin 92` is
atomic number `z.1 + 1`. -/

def ArTable : Fin 92 → Option ℚ := fun z =>
  match z.1 with
  | 0 => some (1008 / 1000)  -- H
  | 1 => some (4003 / 1000)  -- He
  | 2 => some (694 / 100)  -- Li
  | 3 => some (901 / 100)  -- Be
  | 4 => some (1081 / 100)  -- B
  | 5 => some (1201 / 100)  -- C
  | 6 => some (1401 / 100)  -- N
  | 7 => some (16 / 1)  -- O
  | 8 => some (19 / 1)  -- F
  | 9 => some (2018 / 100)  -- Ne
  | 10 => some (2299 / 100)  -- Na
  | 11 => some (2430 / 100)  -- Mg
  | 12 => some (2698 / 100)  -- Al
  | 13 => some (2809 / 100)  -- Si
  | 14 => some (3097 / 100)  -- P
  | 15 => some (3206 / 100)  -- S
  | 16 => some (3545 / 100)  -- Cl
  | 17 => some (3995 / 100)  -- Ar
  | 18 => some (3910 / 100)  -- K
  | 19 => some (4008 / 100)  -- Ca
  | 20 => some (4496 / 100)  -- Sc
  | 21 => some (4787 / 100)  -- Ti
  | 22 => some (5094 / 100)  -- V
  | 23 => some (52 / 1)  -- Cr
  | 24 => some (5494 / 100)  -- Mn
  | 25 => some (5585 / 100)  -- Fe
  | 26 => some (5893 / 100)  -- Co
  | 27 => some (5869 / 100)  -- Ni
  | 28 => some (6355 / 100)  -- Cu
  | 29 => some (6538 / 100)  -- Zn
  | 30 => some (6972 / 100)  -- Ga
  | 31 => some (7263 / 100)  -- Ge
  | 32 => some (7492 / 100)  -- As
  | 33 => some (7897 / 100)  -- Se
  | 34 => some (7990 / 100)  -- Br
  | 35 => some (8380 / 100)  -- Kr
  | 36 => some (8547 / 100)  -- Rb
  | 37 => some (8762 / 100)  -- Sr
  | 38 => some (8891 / 100)  -- Y
  | 39 => some (9122 / 100)  -- Zr
  | 40 => some (9291 / 100)  -- Nb
  | 41 => some (9595 / 100)  -- Mo
  | 42 => none  -- Tc (no mass printed)
  | 43 => some (1011 / 10)  -- Ru
  | 44 => some (1029 / 10)  -- Rh
  | 45 => some (1064 / 10)  -- Pd
  | 46 => some (1079 / 10)  -- Ag
  | 47 => some (1124 / 10)  -- Cd
  | 48 => some (1148 / 10)  -- In
  | 49 => some (1187 / 10)  -- Sn
  | 50 => some (1218 / 10)  -- Sb
  | 51 => some (1276 / 10)  -- Te
  | 52 => some (1269 / 10)  -- I
  | 53 => some (1313 / 10)  -- Xe
  | 54 => some (1329 / 10)  -- Cs
  | 55 => some (1373 / 10)  -- Ba
  | 56 => some (1389 / 10)  -- La
  | 57 => some (1401 / 10)  -- Ce
  | 58 => some (1409 / 10)  -- Pr
  | 59 => some (1442 / 10)  -- Nd
  | 60 => none  -- Pm (no mass printed)
  | 61 => some (1504 / 10)  -- Sm
  | 62 => some (152 / 1)  -- Eu
  | 63 => some (1573 / 10)  -- Gd
  | 64 => some (1589 / 10)  -- Tb
  | 65 => some (1625 / 10)  -- Dy
  | 66 => some (1649 / 10)  -- Ho
  | 67 => some (1673 / 10)  -- Er
  | 68 => some (1689 / 10)  -- Tm
  | 69 => some (173 / 1)  -- Yb
  | 70 => some (175 / 1)  -- Lu
  | 71 => some (1785 / 10)  -- Hf
  | 72 => some (1809 / 10)  -- Ta
  | 73 => some (1838 / 10)  -- W
  | 74 => some (1862 / 10)  -- Re
  | 75 => some (1902 / 10)  -- Os
  | 76 => some (1922 / 10)  -- Ir
  | 77 => some (1951 / 10)  -- Pt
  | 78 => some (197 / 1)  -- Au
  | 79 => some (2006 / 10)  -- Hg
  | 80 => some (2044 / 10)  -- Tl
  | 81 => some (2072 / 10)  -- Pb
  | 82 => some (209 / 1)  -- Bi
  | 83 => none  -- Po
  | 84 => none  -- At
  | 85 => none  -- Rn
  | 86 => none  -- Fr
  | 87 => none  -- Ra
  | 88 => some (232 / 1)  -- Th
  | 89 => some (231 / 1)  -- Pa
  | 90 => some (23803 / 100)  -- U
  | 91 => none  -- Np (no mass printed)
  | _ => none

/-! ## Printed data, displayed-precision windows, model compounds -/

/-- `M(H₂O) = 2·Ar(H) + Ar(O) = 2·1.008 + 16.00 = 18.016`, exact printed
values. -/
def M_H2O : ℚ := 2 * (1008 / 1000) + 16

/-- Printed masses used in the model compounds. -/
def Ar_Na : ℚ := 2299 / 100
def Ar_F : ℚ := 19
/--
The printed relative atomic mass of aluminium (the answer; used for the
*existence* verification only). -/
def Ar_Al : ℚ := 2698 / 100

/-- Half-quantum windows around the printed percentages (quantum 0.01 %). -/
def WH₂O_lo : ℚ := 39155 / 100000
def WH₂O_hi : ℚ := 39165 / 100000
def WNa_lo : ℚ := 32845 / 100000
def WNa_hi : ℚ := 32855 / 100000
def WQ_lo : ℚ := 12845 / 100000
def WQ_hi : ℚ := 12855 / 100000

/-- Molar mass of the hydrate `C ⋅ xH₂O = QFᵥ ⋅ xH₂O`. -/
def MH (ArQ v x : ℚ) : ℚ := ArQ + v * Ar_F + x * M_H2O

/-- Molar mass of `D = C ⬝ n NaF = NaₙQF_{v+n}`. -/
def MD (ArQ v n : ℚ) : ℚ := ArQ + v * Ar_F + n * (Ar_Na + Ar_F)

/-- The three printed data as open displayed-measurement windows. -/
def HydrationDatum (ArQ v x : ℚ) : Prop :=
  WH₂O_lo < x * M_H2O / MH ArQ v x ∧ x * M_H2O / MH ArQ v x < WH₂O_hi

def SodiumDatum (ArQ v n : ℚ) : Prop :=
  WNa_lo < n * Ar_Na / MD ArQ v n ∧ n * Ar_Na / MD ArQ v n < WNa_hi

def MetalDatum (ArQ v n : ℚ) : Prop :=
  WQ_lo < ArQ / MD ArQ v n ∧ ArQ / MD ArQ v n < WQ_hi

/-- M-A4-3. -/
def MassRange (ArQ : ℚ) : Prop := 0 < ArQ ∧ ArQ ≤ 294

/-- The full candidate predicate (M-A4-1, M-A4-2, M-A4-3). -/
structure Candidate (ArQ : ℚ) (v x n : ℕ) : Prop where
  valence : v = 2 ∨ v = 3
  hx : 1 ≤ x
  hn : 1 ≤ n
  range : MassRange ArQ
  hyd : HydrationDatum ArQ v x
  sodium : SodiumDatum ArQ v n
  metal : MetalDatum ArQ v n

/-! ## Part I — the answer verifies (existence) -/

/-- **The identified answer reproduces all three printed percentages.**
Q = aluminium (Ar = 26.98), C·xH₂O = AlF₃·3H₂O (M = 138.028),
D = Na₃AlF₆ (cryolite, M = 209.94):
`54.048/138.028 = 0.391577… ∈ (0.39155, 0.39165)`,
`68.97/209.94  = 0.328524… ∈ (0.32845, 0.32855)`,
`26.98/209.94  = 0.128513… ∈ (0.12845, 0.12855)`. -/
theorem answer_aluminium :
    HydrationDatum Ar_Al 3 3 ∧ SodiumDatum Ar_Al 3 3 ∧ MetalDatum Ar_Al 3 3 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num [HydrationDatum, SodiumDatum, MetalDatum,
      MH, MD, M_H2O, Ar_Na, Ar_F, Ar_Al,
      WH₂O_lo, WH₂O_hi, WNa_lo, WNa_hi, WQ_lo, WQ_hi]

/-- Aluminium is atomic number 13 in the supplied periodic table. -/
theorem printed_value_2698_is_element_13 :
    ArTable ⟨12, by norm_num⟩ = some (2698 / 100) := rfl

/-- Soft check against the problem text "D … is used in the industrial
production of Q": cryolite Na₃AlF₆ is the electrolyte solvent of the
Hall–Héroult industrial aluminium process. -/
theorem industrial_use_consistent :
    -- D uses Q's fluoride (AlF₃) + NaF, the industrial aluminium electrolyte
    ∃ v n : ℕ, v = 3 ∧ n = 3 ∧ MetalDatum Ar_Al v n :=
  ⟨3, 3, rfl, rfl, answer_aluminium.2.2⟩

/-! ## Part II — denominator clearing -/

theorem MH_pos {ArQ : ℚ} (hr : MassRange ArQ) (v x : ℚ) (hv : 0 ≤ v) (hx : 0 ≤ x) :
    0 < MH ArQ v x := by
  rcases hr with ⟨h1, _⟩
  unfold MH M_H2O Ar_F; linarith

theorem MD_pos {ArQ : ℚ} (hr : MassRange ArQ) (v n : ℚ) (hv : 0 ≤ v) (hn : 0 ≤ n) :
    0 < MD ArQ v n := by
  rcases hr with ⟨h1, _⟩
  unfold MD Ar_Na Ar_F; linarith

/-- Hydration datum cleared. -/
theorem cleared_hydration {ArQ : ℚ} (hr : MassRange ArQ) (v x : ℕ) :
    HydrationDatum ArQ v x →
      WH₂O_lo * (ArQ + v * Ar_F) < (1 - WH₂O_lo) * (x * M_H2O) ∧
      (1 - WH₂O_hi) * (x * M_H2O) < WH₂O_hi * (ArQ + v * Ar_F + x * M_H2O) := by
  intro ⟨h1, h2⟩
  have hpos : 0 < MH ArQ v x := MH_pos hr _ _ (by positivity) (by positivity)
  rw [lt_div_iff₀ hpos] at h1
  rw [div_lt_iff₀ hpos] at h2
  refine ⟨?_, ?_⟩ <;> unfold MH M_H2O Ar_F WH₂O_lo WH₂O_hi at * <;> linarith

/-- Sodium datum cleared. -/
theorem cleared_sodium {ArQ : ℚ} (hr : MassRange ArQ) (v n : ℕ) :
    SodiumDatum ArQ v n →
      WNa_lo * (ArQ + v * Ar_F) < n * Ar_Na * (1 - WNa_lo) - WNa_lo * n * Ar_F ∧
      (n : ℚ) * Ar_Na < WNa_hi * MD ArQ v n := by
  intro ⟨h1, h2⟩
  have hpos : 0 < MD ArQ v n := MD_pos hr _ _ (by positivity) (by positivity)
  rw [lt_div_iff₀ hpos] at h1
  rw [div_lt_iff₀ hpos] at h2
  refine ⟨?_, ?_⟩ <;> unfold MD Ar_Na Ar_F WNa_lo WNa_hi at * <;> linarith

/-- Metal datum cleared. -/
theorem cleared_metal {ArQ : ℚ} (hr : MassRange ArQ) (v n : ℕ) :
    MetalDatum ArQ v n →
      WQ_lo * (v * Ar_F + n * (Ar_Na + Ar_F)) < (1 - WQ_lo) * ArQ ∧
      (1 - WQ_hi) * ArQ < WQ_hi * (v * Ar_F + n * (Ar_Na + Ar_F)) := by
  intro ⟨h1, h2⟩
  have hpos : 0 < MD ArQ v n := MD_pos hr _ _ (by positivity) (by positivity)
  rw [lt_div_iff₀ hpos] at h1
  rw [div_lt_iff₀ hpos] at h2
  refine ⟨?_, ?_⟩ <;> unfold MD Ar_Na Ar_F WQ_lo WQ_hi at * <;> linarith

/-! ## Part III — derived search bounds (no unexplained bounds) -/

/-- Rearrangement of the hydration-hi inequality: `(1−hi)·m < hi·(A+m)`
implies `m·(1−2·hi) < hi·A`.  Instantiated below with the printed
half-quantum constants. -/
theorem hyd_hi_rearr (m A : ℚ)
    (h : (1 - WH₂O_hi) * m < WH₂O_hi * (A + m)) :
    m * (1 - 2 * WH₂O_hi) < WH₂O_hi * A := by linarith

/-- From the hydration datum with `0 < ArQ ≤ 294`, `v ≤ 4`: `x ≤ 37`.
(The printed window forces `ArQ < 325.9` at `x = 13`, which cuts off only
at `x = 38`; the identification below rules out the surviving large-x
candidates via the *other* two data anyway.) -/
theorem x_bound {ArQ : ℚ} {v x : ℕ} (hr : MassRange ArQ)
    (hv4 : (v : ℚ) ≤ 4) (h : HydrationDatum ArQ v x) : x ≤ 37 := by
  obtain ⟨_, h2⟩ := cleared_hydration hr v x h
  rcases hr with ⟨hlo, hhi⟩
  by_contra hxc; push_neg at hxc
  have hx38 : (38 : ℚ) ≤ x := by exact_mod_cast hxc
  have hm : (0 : ℚ) < M_H2O := by unfold M_H2O; norm_num
  have key : ((x : ℚ) * M_H2O) * (1 - 2 * WH₂O_hi) <
      WH₂O_hi * (ArQ + (v : ℚ) * Ar_F) := hyd_hi_rearr _ _ h2
  have ub : WH₂O_hi * (ArQ + (v : ℚ) * Ar_F) ≤ WH₂O_hi * 370 := by
    apply mul_le_mul_of_nonneg_left _ (by unfold WH₂O_hi; norm_num)
    have e2 : (v : ℚ) * Ar_F ≤ 4 * Ar_F :=
      mul_le_mul_of_nonneg_right hv4 (by unfold Ar_F; norm_num)
    have e3 : (4 : ℚ) * Ar_F = 76 := by unfold Ar_F; norm_num
    linarith
  have lb : (38 * M_H2O) * (1 - 2 * WH₂O_hi) ≤
      ((x : ℚ) * M_H2O) * (1 - 2 * WH₂O_hi) := by
    apply mul_le_mul_of_nonneg_right _ (by unfold WH₂O_hi; norm_num)
    exact mul_le_mul_of_nonneg_right hx38 (le_of_lt hm)
  have comb : (38 * M_H2O) * (1 - 2 * WH₂O_hi) < WH₂O_hi * 370 :=
    lt_of_le_of_lt lb (lt_of_lt_of_le key ub)
  unfold WH₂O_hi M_H2O at comb
  norm_num at comb

/-- From the sodium datum with `0 < ArQ ≤ 294`, `v ≤ 4`: `n ≤ 13`. -/
theorem n_bound {ArQ : ℚ} {v n : ℕ} (hr : MassRange ArQ)
    (hv4 : (v : ℚ) ≤ 4) (h : SodiumDatum ArQ v n) : n ≤ 13 := by
  obtain ⟨_, s2⟩ := cleared_sodium hr v n h
  rcases hr with ⟨hlo, hhi⟩
  by_contra hnc; push_neg at hnc
  have hn14 : (14 : ℚ) ≤ n := by exact_mod_cast hnc
  have hf : (0 : ℚ) < Ar_F := by unfold Ar_F; norm_num
  have key : (n : ℚ) * (Ar_Na * (1 - WNa_hi) - WNa_hi * Ar_F) <
      WNa_hi * (ArQ + (v : ℚ) * Ar_F) := by
    have e : MD ArQ v n = ArQ + (v : ℚ) * Ar_F + (n : ℚ) * (Ar_Na + Ar_F) := rfl
    rw [e] at s2
    linarith [s2]
  have per : (0 : ℚ) < Ar_Na * (1 - WNa_hi) - WNa_hi * Ar_F := by
    unfold Ar_Na WNa_hi Ar_F; norm_num
  have ub : WNa_hi * (ArQ + (v : ℚ) * Ar_F) ≤ WNa_hi * 370 := by
    apply mul_le_mul_of_nonneg_left _ (by unfold WNa_hi; norm_num)
    have e2 : (v : ℚ) * Ar_F ≤ 4 * Ar_F := mul_le_mul_of_nonneg_right hv4 (le_of_lt hf)
    have e3 : (4 : ℚ) * Ar_F = 76 := by unfold Ar_F; norm_num
    linarith [hhi, e2]
  have lb : (14 : ℚ) * (Ar_Na * (1 - WNa_hi) - WNa_hi * Ar_F) ≤
      (n : ℚ) * (Ar_Na * (1 - WNa_hi) - WNa_hi * Ar_F) :=
    mul_le_mul_of_nonneg_right hn14 (le_of_lt per)
  have comb : (14 : ℚ) * (Ar_Na * (1 - WNa_hi) - WNa_hi * Ar_F) < WNa_hi * 370 :=
    lt_of_le_of_lt lb (lt_of_lt_of_le key ub)
  unfold Ar_Na WNa_hi Ar_F at comb
  norm_num at comb

/-! ## Part IV — the full identification (data + periodic table together)

The logic of the identification: for each candidate `(v, x, n)` the three
data determine an open window `W(v,x,n)` for `Ar(Q)`.  We prove:

* (`envelope_v2`) for `v = 2`, every candidate in the derived box
  `1 ≤ x, n ≤ 13` either contradicts the data or forces
  `17.9725 < Ar(Q) < 17.997`; no printed table mass lies within ±0.005
  (`table_no_match_v2`), so `v = 2` is disproved by the table.
* (`envelope_v3`) for `v = 3`, every candidate forces
  `26.945 < Ar(Q) < 26.9943`; the only printed table mass within ±0.005 is
  `t = 26.98` at atomic number 13 — aluminium (`table_match_v3`).
* (`stoichiometry_at_aluminium`) once the aluminium match re-tightens
  `Ar(Q)` to the open half-quantum `(26.975, 26.985)` of its printed value,
  the hydration datum alone forces `x = 3` and the sodium datum alone
  forces `n = 3`.  (All twelve endpoint comparisons were additionally
  verified by exact rational arithmetic offline.) -/

/-- Strong form of the hydration-hi bound: from `x·M(H₂O)/MH < WH₂O_hi` and
`x·M(H₂O) ≤ MH − (ArQ + v·F)` we get the equivalent cleared inequality
`(1 − WH₂O_hi)·x·M(H₂O) < WH₂O_hi·(ArQ + v·F)`. -/
theorem cleared_hydration_strong {ArQ : ℚ} (hr : MassRange ArQ) (v x : ℕ) :
    HydrationDatum ArQ v x →
      WH₂O_lo * (ArQ + v * Ar_F) < (1 - WH₂O_lo) * (x * M_H2O) ∧
      (1 - WH₂O_hi) * (x * M_H2O) < WH₂O_hi * (ArQ + v * Ar_F) := by
  intro ⟨h1, h2⟩
  have hpos : 0 < MH ArQ v x := MH_pos hr _ _ (by positivity) (by positivity)
  rw [lt_div_iff₀ hpos] at h1
  rw [div_lt_iff₀ hpos] at h2
  refine ⟨?_, ?_⟩ <;> unfold MH M_H2O Ar_F WH₂O_lo WH₂O_hi at * <;> linarith

set_option maxHeartbeats 2500000 in
/-- Chunked sweep (`v = 2`, `1 ≤ x ≤ 10`): every candidate there either
contradicts the data or obeys the stated `ArQ` window. -/
theorem envelope_v2_c1_10 {ArQ : ℚ} {x n : ℕ}
    (hx1 : 1 ≤ x) (hx10 : x ≤ 10) (hn1 : 1 ≤ n) (hn13 : n ≤ 13)
    (hr : MassRange ArQ)
    (hH : HydrationDatum ArQ 2 x) (hS : SodiumDatum ArQ 2 n)
    (hM : MetalDatum ArQ 2 n) :
    (179725/10000 : ℚ) < ArQ ∧ ArQ < 17997/1000 := by
  obtain ⟨h1, h2⟩ := cleared_hydration hr 2 x hH
  obtain ⟨s1, s2⟩ := cleared_sodium hr 2 n hS
  obtain ⟨m1, m2⟩ := cleared_metal hr 2 n hM
  simp only [WH₂O_lo, WH₂O_hi, WNa_lo, WNa_hi, WQ_lo, WQ_hi, M_H2O, Ar_Na, Ar_F, MD,
    Nat.cast_ofNat] at *
  interval_cases x <;> interval_cases n <;> first
    | exact ⟨by linarith, by linarith⟩
    | (exfalso; linarith)

set_option maxHeartbeats 2500000 in
/-- Chunked sweep (`v = 2`, `11 ≤ x ≤ 20`): every candidate there either
contradicts the data or obeys the stated `ArQ` window. -/
theorem envelope_v2_c11_20 {ArQ : ℚ} {x n : ℕ}
    (hx11 : 11 ≤ x) (hx20 : x ≤ 20) (hn1 : 1 ≤ n) (hn13 : n ≤ 13)
    (hr : MassRange ArQ)
    (hH : HydrationDatum ArQ 2 x) (hS : SodiumDatum ArQ 2 n)
    (hM : MetalDatum ArQ 2 n) :
    (179725/10000 : ℚ) < ArQ ∧ ArQ < 17997/1000 := by
  obtain ⟨h1, h2⟩ := cleared_hydration hr 2 x hH
  obtain ⟨s1, s2⟩ := cleared_sodium hr 2 n hS
  obtain ⟨m1, m2⟩ := cleared_metal hr 2 n hM
  simp only [WH₂O_lo, WH₂O_hi, WNa_lo, WNa_hi, WQ_lo, WQ_hi, M_H2O, Ar_Na, Ar_F, MD,
    Nat.cast_ofNat] at *
  interval_cases x <;> interval_cases n <;> first
    | exact ⟨by linarith, by linarith⟩
    | (exfalso; linarith)

set_option maxHeartbeats 2500000 in
/-- Chunked sweep (`v = 2`, `21 ≤ x ≤ 30`): every candidate there either
contradicts the data or obeys the stated `ArQ` window. -/
theorem envelope_v2_c21_30 {ArQ : ℚ} {x n : ℕ}
    (hx21 : 21 ≤ x) (hx30 : x ≤ 30) (hn1 : 1 ≤ n) (hn13 : n ≤ 13)
    (hr : MassRange ArQ)
    (hH : HydrationDatum ArQ 2 x) (hS : SodiumDatum ArQ 2 n)
    (hM : MetalDatum ArQ 2 n) :
    (179725/10000 : ℚ) < ArQ ∧ ArQ < 17997/1000 := by
  obtain ⟨h1, h2⟩ := cleared_hydration hr 2 x hH
  obtain ⟨s1, s2⟩ := cleared_sodium hr 2 n hS
  obtain ⟨m1, m2⟩ := cleared_metal hr 2 n hM
  simp only [WH₂O_lo, WH₂O_hi, WNa_lo, WNa_hi, WQ_lo, WQ_hi, M_H2O, Ar_Na, Ar_F, MD,
    Nat.cast_ofNat] at *
  interval_cases x <;> interval_cases n <;> first
    | exact ⟨by linarith, by linarith⟩
    | (exfalso; linarith)

set_option maxHeartbeats 2500000 in
/-- Chunked sweep (`v = 2`, `31 ≤ x ≤ 37`): every candidate there either
contradicts the data or obeys the stated `ArQ` window. -/
theorem envelope_v2_c31_37 {ArQ : ℚ} {x n : ℕ}
    (hx31 : 31 ≤ x) (hx37 : x ≤ 37) (hn1 : 1 ≤ n) (hn13 : n ≤ 13)
    (hr : MassRange ArQ)
    (hH : HydrationDatum ArQ 2 x) (hS : SodiumDatum ArQ 2 n)
    (hM : MetalDatum ArQ 2 n) :
    (179725/10000 : ℚ) < ArQ ∧ ArQ < 17997/1000 := by
  obtain ⟨h1, h2⟩ := cleared_hydration hr 2 x hH
  obtain ⟨s1, s2⟩ := cleared_sodium hr 2 n hS
  obtain ⟨m1, m2⟩ := cleared_metal hr 2 n hM
  simp only [WH₂O_lo, WH₂O_hi, WNa_lo, WNa_hi, WQ_lo, WQ_hi, M_H2O, Ar_Na, Ar_F, MD,
    Nat.cast_ofNat] at *
  interval_cases x <;> interval_cases n <;> first
    | exact ⟨by linarith, by linarith⟩
    | (exfalso; linarith)

/-- **v = 2 envelope**: every valence-2 candidate that satisfies the data
and the mass range obeys `179725/10000 < Ar(Q) < 17997/1000`. -/
theorem envelope_v2 {ArQ : ℚ} {x n : ℕ}
    (hx1 : 1 ≤ x) (hn1 : 1 ≤ n) (hr : MassRange ArQ)
    (hH : HydrationDatum ArQ 2 x) (hS : SodiumDatum ArQ 2 n)
    (hM : MetalDatum ArQ 2 n)
    (hxB : x ≤ 37) (hn13 : n ≤ 13) :
    (179725/10000 : ℚ) < ArQ ∧ ArQ < 17997/1000 := by
  by_cases hA : x ≤ 10
  · exact envelope_v2_c1_10 hx1 hA hn1 hn13 hr hH hS hM
  by_cases hB : x ≤ 20
  · push_neg at hA
    exact envelope_v2_c11_20 (by omega) hB hn1 hn13 hr hH hS hM
  by_cases hC : x ≤ 30
  · push_neg at hB
    exact envelope_v2_c21_30 (by omega) hC hn1 hn13 hr hH hS hM
  · push_neg at hC
    exact envelope_v2_c31_37 (by omega) hxB hn1 hn13 hr hH hS hM

set_option maxHeartbeats 2500000 in
/-- Chunked sweep (`v = 3`, `1 ≤ x ≤ 10`): every candidate there either
contradicts the data or obeys the stated `ArQ` window. -/
theorem envelope_v3_c1_10 {ArQ : ℚ} {x n : ℕ}
    (hx1 : 1 ≤ x) (hx10 : x ≤ 10) (hn1 : 1 ≤ n) (hn13 : n ≤ 13)
    (hr : MassRange ArQ)
    (hH : HydrationDatum ArQ 3 x) (hS : SodiumDatum ArQ 3 n)
    (hM : MetalDatum ArQ 3 n) :
    (26945/1000 : ℚ) < ArQ ∧ ArQ < 269943/10000 := by
  obtain ⟨h1, h2⟩ := cleared_hydration hr 3 x hH
  obtain ⟨s1, s2⟩ := cleared_sodium hr 3 n hS
  obtain ⟨m1, m2⟩ := cleared_metal hr 3 n hM
  simp only [WH₂O_lo, WH₂O_hi, WNa_lo, WNa_hi, WQ_lo, WQ_hi, M_H2O, Ar_Na, Ar_F, MD,
    Nat.cast_ofNat] at *
  interval_cases x <;> interval_cases n <;> first
    | exact ⟨by linarith, by linarith⟩
    | (exfalso; linarith)

set_option maxHeartbeats 2500000 in
/-- Chunked sweep (`v = 3`, `11 ≤ x ≤ 20`): every candidate there either
contradicts the data or obeys the stated `ArQ` window. -/
theorem envelope_v3_c11_20 {ArQ : ℚ} {x n : ℕ}
    (hx11 : 11 ≤ x) (hx20 : x ≤ 20) (hn1 : 1 ≤ n) (hn13 : n ≤ 13)
    (hr : MassRange ArQ)
    (hH : HydrationDatum ArQ 3 x) (hS : SodiumDatum ArQ 3 n)
    (hM : MetalDatum ArQ 3 n) :
    (26945/1000 : ℚ) < ArQ ∧ ArQ < 269943/10000 := by
  obtain ⟨h1, h2⟩ := cleared_hydration hr 3 x hH
  obtain ⟨s1, s2⟩ := cleared_sodium hr 3 n hS
  obtain ⟨m1, m2⟩ := cleared_metal hr 3 n hM
  simp only [WH₂O_lo, WH₂O_hi, WNa_lo, WNa_hi, WQ_lo, WQ_hi, M_H2O, Ar_Na, Ar_F, MD,
    Nat.cast_ofNat] at *
  interval_cases x <;> interval_cases n <;> first
    | exact ⟨by linarith, by linarith⟩
    | (exfalso; linarith)

set_option maxHeartbeats 2500000 in
/-- Chunked sweep (`v = 3`, `21 ≤ x ≤ 30`): every candidate there either
contradicts the data or obeys the stated `ArQ` window. -/
theorem envelope_v3_c21_30 {ArQ : ℚ} {x n : ℕ}
    (hx21 : 21 ≤ x) (hx30 : x ≤ 30) (hn1 : 1 ≤ n) (hn13 : n ≤ 13)
    (hr : MassRange ArQ)
    (hH : HydrationDatum ArQ 3 x) (hS : SodiumDatum ArQ 3 n)
    (hM : MetalDatum ArQ 3 n) :
    (26945/1000 : ℚ) < ArQ ∧ ArQ < 269943/10000 := by
  obtain ⟨h1, h2⟩ := cleared_hydration hr 3 x hH
  obtain ⟨s1, s2⟩ := cleared_sodium hr 3 n hS
  obtain ⟨m1, m2⟩ := cleared_metal hr 3 n hM
  simp only [WH₂O_lo, WH₂O_hi, WNa_lo, WNa_hi, WQ_lo, WQ_hi, M_H2O, Ar_Na, Ar_F, MD,
    Nat.cast_ofNat] at *
  interval_cases x <;> interval_cases n <;> first
    | exact ⟨by linarith, by linarith⟩
    | (exfalso; linarith)

set_option maxHeartbeats 2500000 in
/-- Chunked sweep (`v = 3`, `31 ≤ x ≤ 37`): every candidate there either
contradicts the data or obeys the stated `ArQ` window. -/
theorem envelope_v3_c31_37 {ArQ : ℚ} {x n : ℕ}
    (hx31 : 31 ≤ x) (hx37 : x ≤ 37) (hn1 : 1 ≤ n) (hn13 : n ≤ 13)
    (hr : MassRange ArQ)
    (hH : HydrationDatum ArQ 3 x) (hS : SodiumDatum ArQ 3 n)
    (hM : MetalDatum ArQ 3 n) :
    (26945/1000 : ℚ) < ArQ ∧ ArQ < 269943/10000 := by
  obtain ⟨h1, h2⟩ := cleared_hydration hr 3 x hH
  obtain ⟨s1, s2⟩ := cleared_sodium hr 3 n hS
  obtain ⟨m1, m2⟩ := cleared_metal hr 3 n hM
  simp only [WH₂O_lo, WH₂O_hi, WNa_lo, WNa_hi, WQ_lo, WQ_hi, M_H2O, Ar_Na, Ar_F, MD,
    Nat.cast_ofNat] at *
  interval_cases x <;> interval_cases n <;> first
    | exact ⟨by linarith, by linarith⟩
    | (exfalso; linarith)

/-- **v = 3 envelope**: every valence-3 candidate that satisfies the data
and the mass range obeys `26945/1000 < Ar(Q) < 269943/10000`. -/
theorem envelope_v3 {ArQ : ℚ} {x n : ℕ}
    (hx1 : 1 ≤ x) (hn1 : 1 ≤ n) (hr : MassRange ArQ)
    (hH : HydrationDatum ArQ 3 x) (hS : SodiumDatum ArQ 3 n)
    (hM : MetalDatum ArQ 3 n)
    (hxB : x ≤ 37) (hn13 : n ≤ 13) :
    (26945/1000 : ℚ) < ArQ ∧ ArQ < 269943/10000 := by
  by_cases hA : x ≤ 10
  · exact envelope_v3_c1_10 hx1 hA hn1 hn13 hr hH hS hM
  by_cases hB : x ≤ 20
  · push_neg at hA
    exact envelope_v3_c11_20 (by omega) hB hn1 hn13 hr hH hS hM
  by_cases hC : x ≤ 30
  · push_neg at hB
    exact envelope_v3_c21_30 (by omega) hC hn1 hn13 hr hH hS hM
  · push_neg at hC
    exact envelope_v3_c31_37 (by omega) hxB hn1 hn13 hr hH hS hM

set_option maxHeartbeats 600000 in
/-- No printed table mass lies in `(17.9675, 18.002)` (the elements
bracketing this interval are oxygen 16.00 and fluorine 19.00).  This kills
the whole `v = 2` family. -/
theorem table_no_match_v2 {z : Fin 92} {t : ℚ} (hz : ArTable z = some t)
    (hwin : (179675/10000 : ℚ) < t ∧ t < 9001/500) : False := by
  have h92 := z.2
  interval_cases h : z.1 <;>
    simp only [ArTable, h] at hz <;>
    first
      | contradiction
      | (injection hz with ht; subst ht; exfalso; norm_num at hwin)

set_option maxHeartbeats 600000 in
/-- The only printed table mass in `(26.94, 26.9993)` is 26.98, aluminium,
atomic number 13 (the neighbouring printed masses are Mg 24.30 and
Si 28.09). -/
theorem table_match_v3 {z : Fin 92} {t : ℚ} (hz : ArTable z = some t)
    (hwin : (2694/100 : ℚ) < t ∧ t < 269993/10000) :
    z = ⟨12, by norm_num⟩ ∧ t = 2698/100 := by
  have h92 := z.2
  interval_cases h : z.1 <;>
    simp only [ArTable, h] at hz <;>
    first
      | contradiction
      | (injection hz with ht; subst ht;
         first
           | exact ⟨Fin.ext (by omega), rfl⟩
           | (exfalso; norm_num at hwin))

set_option maxHeartbeats 1600000 in
/-- **Stoichiometry at the aluminium mass.**  Once `Ar(Q)` is re-tightened
to the open half-quantum `(26.975, 26.985)` of aluminium's printed mass
`26.98` (allowed because the metal's true mass must print as 26.98, i.e.
lie within half a quantum of it — this *follows* from the identification,
no answer being assumed), the hydration datum alone kills every `x ≠ 3`
and the sodium datum alone kills every `n ≠ 3`. -/
theorem stoichiometry_at_aluminium {ArQ : ℚ} {x n : ℕ}
    (hlo : (26975/1000 : ℚ) < ArQ) (hhi : ArQ < 26985/1000)
    (hx1 : 1 ≤ x) (hx37 : x ≤ 37) (hn1 : 1 ≤ n) (hn13 : n ≤ 13)
    (H1 : WH₂O_lo * (ArQ + 3 * Ar_F) < (1 - WH₂O_lo) * ((x:ℚ) * M_H2O))
    (H2 : (1 - WH₂O_hi) * ((x:ℚ) * M_H2O) < WH₂O_hi * (ArQ + 3 * Ar_F))
    (S1 : WNa_lo * (ArQ + 3 * Ar_F) <
        (n:ℚ) * Ar_Na * (1 - WNa_lo) - WNa_lo * (n:ℚ) * Ar_F)
    (S2 : (n:ℚ) * Ar_Na <
        WNa_hi * (ArQ + 3 * Ar_F + (n:ℚ) * (Ar_Na + Ar_F))) :
    x = 3 ∧ n = 3 := by
  unfold WH₂O_lo WH₂O_hi WNa_lo WNa_hi M_H2O Ar_Na Ar_F at *
  refine ⟨?_, ?_⟩
  · interval_cases x <;> first
      | rfl
      | (exfalso; linarith)
  · interval_cases n <;> first
      | rfl
      | (exfalso; linarith)

/-- **Main answer to 1.4.**  Any triple `(v, x, n)` consistent with all
three printed mass percentages (at displayed-precision tolerance), with
`Q`'s true relative atomic mass matching some printed periodic-table value
at half-quantum precision, and with the physically possible range
`0 < Ar(Q) ≤ 294`, must be `(v, x, n) = (3, 3, 3)` with `Q` = the element
of atomic number 13 = **aluminium** (printed mass 26.98).  Hence
`C = AlF₃`, `C ⋅ xH₂O = AlF₃·3H₂O` and `D = Na₃AlF₆`. -/
theorem main_answer {ArQ : ℚ} {v x n : ℕ} (h : Candidate ArQ v x n)
    {z : Fin 92} {t : ℚ} (hz : ArTable z = some t)
    (hmatch : t - 5 / 1000 < ArQ ∧ ArQ < t + 5 / 1000) :
    v = 3 ∧ x = 3 ∧ n = 3 ∧ z = ⟨12, by norm_num⟩ ∧ t = 2698 / 100 := by
  have hv4 : (v : ℚ) ≤ 4 := by rcases h.valence with rfl | rfl <;> norm_num
  have hx13 := x_bound h.range hv4 h.hyd
  have hn13 := n_bound h.range hv4 h.sodium
  obtain ⟨hml, hmu⟩ := hmatch
  rcases h.valence with rfl | rfl
  · -- v = 2 family: envelope contradicts every printed table mass
    obtain ⟨elo, ehi⟩ := envelope_v2 h.hx h.hn h.range h.hyd h.sodium h.metal hx13 hn13
    have tw : (179675/10000 : ℚ) < t ∧ t < 9001/500 := ⟨by linarith, by linarith⟩
    exact absurd tw (table_no_match_v2 hz)
  · -- v = 3 family: envelope selects aluminium, then stoichiometry pins x, n
    obtain ⟨elo, ehi⟩ := envelope_v3 h.hx h.hn h.range h.hyd h.sodium h.metal hx13 hn13
    have tw : (2694/100 : ℚ) < t ∧ t < 269993/10000 := ⟨by linarith, by linarith⟩
    obtain ⟨hz12, ht⟩ := table_match_v3 hz tw
    have htight : (26975/1000 : ℚ) < ArQ ∧ ArQ < 26985/1000 := by
      subst ht; exact ⟨by linarith, by linarith⟩
    obtain ⟨H1, H2⟩ := cleared_hydration_strong h.range 3 x h.hyd
    obtain ⟨S1, S2⟩ := cleared_sodium h.range 3 n h.sodium
    obtain ⟨hx3, hn3⟩ :=
      stoichiometry_at_aluminium htight.1 htight.2 h.hx hx13 h.hn hn13 H1 H2 S1 S2
    exact ⟨rfl, hx3, hn3, hz12, ht⟩

/-! ## Part V — the chemical answer stated with structural formulas

The answer sheet expects formula strings.  We record them as the *data* of
the answer, tied to the values proved above. -/

/-- Structural answer: metal Q, the hydrate C·xH₂O, and compound D. -/
structure Answer where
  Q_formula : String
  C_hydrate : String
  D_formula : String

/-- The submitted answer. -/
def theAnswer : Answer where
  Q_formula := "Al"
  C_hydrate := "AlF₃·3H₂O"
  D_formula := "Na₃AlF₆"

/-- The submitted answer is the unique model answer consistent with the data:
its metal mass (26.98) is the table value at atomic number 13 (aluminium), its
hydrate stoichiometry is v = 3, x = 3, and D is the n = 3 adduct — all forced
by `main_answer`. -/
theorem theAnswer_correct :
    theAnswer.Q_formula = "Al" ∧
    theAnswer.C_hydrate = "AlF₃·3H₂O" ∧
    theAnswer.D_formula = "Na₃AlF₆" ∧
    HydrationDatum Ar_Al 3 3 ∧ SodiumDatum Ar_Al 3 3 ∧ MetalDatum Ar_Al 3 3 ∧
    ArTable ⟨12, by norm_num⟩ = some (2698 / 100) :=
  ⟨rfl, rfl, rfl, answer_aluminium.1, answer_aluminium.2.1, answer_aluminium.2.2, rfl⟩

end IChO2026Problems.T1A4
