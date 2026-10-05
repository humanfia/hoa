import IChO2026Chem

/-!
# IChO 2026, Problem T7 (Nitrogen Fixation), subquestion 7.2 (T7-A2)

Question 7.2 (theory_problem.pdf, source page 63 = image `T7_page-1.png`):

> Calculate the mass of CH₄ (tons) required annually to produce 660 000 tons
> of ammonia, if the Navoiazot operates according to the Fig. 1.

Printed facts used as inputs (nothing else is assumed):

* capacity 660 000 t NH₃ per year; printed overall yield 97.0 % (same page);
* "assume that all reactions in Fig. 1, except NH₃ formation, are
  quantitative";
* the Fig. 1 reaction network itself:
    CH₄ + H₂O → CO + 3H₂      (first unit, feed xCH₄ + yH₂O)
    2CH₄ + O₂ → 2CO + 4H₂     (second unit; air supplied as 4N₂ + 1O₂)
    CO + H₂O → CO₂ + H₂       (water–gas shift; CO₂ then removed by Z)
    N₂ + 3H₂ ⇌ 2NH₃          (synthesis loop; unreacted N₂/H₂ recycled)
* relative atomic masses from the periodic table printed on page 5 (G1-5) of
  the same official PDF: C 12.01, N 14.01, H 1.008, hence M(CH₄) = 16.042 and
  M(NH₃) = 17.034 g mol⁻¹ (`M_CH4_value`, `M_NH3_value`).

Trusted general law (used as `hYieldOverall`, proved-style application):
element balance of N₂ + 3H₂ → 2NH₃ — one N₂ per two NH₃, three H₂ per two
NH₃ — applied at overall yield η.

## Stoichiometric result

Generation balance (all gas-making steps quantitative):
  H₂ generated  h2Gen = 3·f + 2·e (reforming) + (f + e) (shift: 1 H₂ per CO)
                      = 4·f + 3·e,
where f is the CH₄ fed to the first unit and e the CH₄ fed to the second.
Air balance (printed 4N₂ + 1O₂ against printed 2CH₄ + O₂):  n2 = 2·e.

The H₂ inventory above the synthesis 3 : 1 ratio, excess = h2Gen − 3·n2, is a
free crowd variable: neither the CO₂ scrubber nor the N₂/H₂ recycle of Fig. 1
consumes a persistent H₂ reserve.  The conservation tiles are proved with
excess variable; the plant "operates according to Fig. 1" with every printed
flow at its stoichiometric destination exactly when excess = 0, which forces
4·f = 3·e, i.e. the feed split f : e = 3 : 4 — the H₂-exact operation whose
net reaction is 7CH₄ + 7H₂O + 8N₂ → 16NH₃ + 7CO₂ (check: per 8 N₂, f = 3,
e = 4 gives 16 NH₃ at full conversion).

  n(NH₃) = 660 000 / 17.034 kmol
  n(CH₄) = (7/16) · n(NH₃) / 0.970      (16 NH₃ per 7 CH₄ at yield 1; /η)
  m(CH₄) = 16.042 · n(CH₄) kg
         = (7 · 16.042 / (16 · 17.034)) · 660 000 / 0.970 t
         ≈ 280 344.6 t  ≈  2.80×10⁵ tons (3 s.f., quantum 1000 t).

The 3-s.f. cell boundary is 279 500 / 280 500 t; the exact printed-table
masses 16.042 / 17.034 give 280 344.56 t, which lies strictly inside the
2.80×10⁵ cell (proved below).  Even the integer-mass shortcut M = 16, 17
(280 169.8 t) would land in the same cell, so the rounded answer is robust;
the raw chain below nevertheless keeps 16.042 / 17.034 exact as printed.
-/

namespace IChO2026T7A2

open IChO2026Chem.Reporting

/-! ## Printed inputs, exact as printed on the problem sheet -/

/-- Printed annual ammonia capacity: 660 000 tons (page 1 of T7). -/
def printedAmmoniaCapacityTons : ℝ := 660000

/-- Printed overall yield 97.0 %, exact as printed (page 1 of T7). -/
def printedOverallYield : ℝ := 0.970

/-- Printed air composition in the title of the second unit: 4N₂ + 1O₂. -/
def printedAirN2PerO2 : ℝ := 4

/-- Relative atomic masses from the periodic table printed on page 5 (G1-5)
of the same official PDF. -/
def ArC : ℝ := 12.01
def ArN : ℝ := 14.01
def ArH : ℝ := 1.008

/-- Molar mass of methane from the printed table (g mol⁻¹ ≡ kg kmol⁻¹). -/
def M_CH4 : ℝ := ArC + 4 * ArH

/-- Molar mass of ammonia from the printed table (g mol⁻¹ ≡ kg kmol⁻¹). -/
def M_NH3 : ℝ := ArN + 3 * ArH

theorem M_CH4_value : M_CH4 = 16.042 := by
  rw [M_CH4, ArC, ArH]; norm_num

theorem M_NH3_value : M_NH3 = 17.034 := by
  rw [M_NH3, ArN, ArH]; norm_num

theorem M_CH4_pos : 0 < M_CH4 := by rw [M_CH4_value]; norm_num

theorem M_NH3_pos : 0 < M_NH3 := by rw [M_NH3_value]; norm_num

/-! ## Stoichiometric state of the Fig. 1 plant

Flows (mol units per batch):

* `feed`  : CH₄ fed to the first reforming unit;
* `extra` : CH₄ fed to the second (autothermal) unit;
* `n2`    : N₂ entering with the air of the second unit;
* `h2Gen` : H₂ delivered to the synthesis section after the quantitative
  reforming, autothermal and shift steps;
* `nh3`   : NH₃ actually produced at overall yield `overallYield`.

`excess = h2Gen − 3·n2` is the H₂ reserve above the 3 : 1 synthesis ratio. -/

structure PlantState where
  feed : ℝ
  extra : ℝ
  n2 : ℝ
  h2Gen : ℝ
  nh3 : ℝ
  overallYield : ℝ

/-- Total methane consumed (both units): feed + extra. -/
def PlantState.methane (s : PlantState) : ℝ := s.feed + s.extra

/-- H₂ inventory above the synthesis 3 : 1 requirement. -/
def PlantState.excess (s : PlantState) : ℝ := s.h2Gen - 3 * s.n2

/-- **Generation balance of Fig. 1** ("all reactions … are quantitative").
Primary reforming gives 3 H₂ per CH₄; the autothermal unit gives 2 H₂ per CH₄
(2CH₄ + O₂ → 2CO + 4H₂); the shift gives one further H₂ per CO, and CO from
reforming totals feed + extra.  Hence h2Gen = 3·f + 2·e + (f + e) =
4·feed + 3·extra. -/
def GenerationBalance (s : PlantState) : Prop :=
  s.h2Gen = 4 * s.feed + 3 * s.extra

/-- **Air balance.** Printed air ratio 4N₂ + 1O₂ against the printed unit
stoichiometry 2CH₄ + O₂:  n2 = 4·(extra/2) = 2·extra. -/
def AirBalance (s : PlantState) : Prop := s.n2 = 2 * s.extra

/-- **Haber stoichiometry** (trusted general law: element balance of
N₂ + 3H₂ → 2NH₃ applied at overall yield η): the nitrogen fed equals half the
ammonia that would be produced at full conversion, n2 = nh3/(2η). -/
def HaberStoichiometry (s : PlantState) : Prop :=
  s.n2 = s.nh3 / (2 * s.overallYield)

/-- Full Fig. 1 model: every reaction except NH₃ formation is quantitative. -/
def OperatesPerFig1 (s : PlantState) : Prop :=
  GenerationBalance s ∧ AirBalance s ∧ HaberStoichiometry s

/-! ### Chain 1: the H₂ reserve is fixed by generation and air alone -/

/-- With the printed 4N₂ + 1O₂ air ratio and the printed network, the
generation and air balances force  excess = 4·methane − (7/2)·n2 :
h2Gen − 3·n2 = (4·f + 3·e) − 3·n2 with n2 = 2·e, methane = f + e. -/
theorem excess_eq_of_generation_air (s : PlantState)
    (hg : GenerationBalance s) (ha : AirBalance s) :
    s.excess = 4 * s.methane - (7 / 2) * s.n2 := by
  show s.h2Gen - 3 * s.n2 = 4 * (s.feed + s.extra) - (7 / 2) * s.n2
  have hg' : s.h2Gen = 4 * s.feed + 3 * s.extra := hg
  have ha' : s.n2 = 2 * s.extra := ha
  linarith

/-! ### Chain 2: conservation tiles (excess held variable) -/

/-- Methane vs. N₂: methane = (7/8)·n2 + excess/4. -/
theorem tile_methane_N2 (s : PlantState)
    (hg : GenerationBalance s) (ha : AirBalance s) :
    s.methane = (7 / 8) * s.n2 + s.excess / 4 := by
  show s.feed + s.extra = (7 / 8) * s.n2 + (s.h2Gen - 3 * s.n2) / 4
  have hg' : s.h2Gen = 4 * s.feed + 3 * s.extra := hg
  have ha' : s.n2 = 2 * s.extra := ha
  linarith

/-- Nitrogen vs. methane: n2 = (8/7)·methane − (2/7)·excess. -/
theorem tile_N2_methane (s : PlantState)
    (hg : GenerationBalance s) (ha : AirBalance s) :
    s.n2 = (8 / 7) * s.methane - (2 / 7) * s.excess := by
  show s.n2 = (8 / 7) * (s.feed + s.extra) - (2 / 7) * (s.h2Gen - 3 * s.n2)
  have hg' : s.h2Gen = 4 * s.feed + 3 * s.extra := hg
  have ha' : s.n2 = 2 * s.extra := ha
  linarith

/-- Hydrogen generated vs. methane: h2Gen = (24/7)·methane + excess/7. -/
theorem tile_H2_methane (s : PlantState)
    (hg : GenerationBalance s) (ha : AirBalance s) :
    s.h2Gen = (24 / 7) * s.methane + s.excess / 7 := by
  show s.h2Gen = (24 / 7) * (s.feed + s.extra) + (s.h2Gen - 3 * s.n2) / 7
  have hg' : s.h2Gen = 4 * s.feed + 3 * s.extra := hg
  have ha' : s.n2 = 2 * s.extra := ha
  linarith

/-! ### Chain 3: theoretical NH₃ tile -/

/-- Full-conversion ammonia: 2·n2 = (16/7)·methane − (4/7)·excess, so the
theoretical NH₃ is 16·methane/7 at excess = 0. -/
theorem tile_NH3_theoretical (s : PlantState)
    (hg : GenerationBalance s) (ha : AirBalance s) :
    2 * s.n2 = (16 / 7) * s.methane - (4 / 7) * s.excess := by
  change 2 * s.n2 = (16 / 7) * (s.feed + s.extra) - (4 / 7) * (s.h2Gen - 3 * s.n2)
  have hg' : s.h2Gen = 4 * s.feed + 3 * s.extra := hg
  have ha' : s.n2 = 2 * s.extra := ha
  linarith

/-! ### Chain 4: raw identity at the H₂-exact operation (excess = 0) -/

/-- At the H₂-exact operation of Fig. 1 (no persistent H₂ reserve), the
generation and air balances alone force  8·methane = 7·n2 :  per 8 N₂ the
gas-making section consumes exactly 7 CH₄, i.e. the net reaction
7CH₄ + 7H₂O + 8N₂ → 16NH₃ + 7CO₂ at full conversion. -/
theorem methane_ratio_H2_exact (s : PlantState)
    (h : OperatesPerFig1 s) (hex : s.excess = 0) :
    8 * s.methane = 7 * s.n2 := by
  have h1 : s.methane = (7 / 8) * s.n2 + s.excess / 4 :=
    tile_methane_N2 s h.1 h.2.1
  -- methane = (7/8)·n2 + excess/4; at excess = 0: 8·methane = 7·n2
  change 8 * (s.feed + s.extra) = 7 * s.n2
  have h1' : s.feed + s.extra = (7 / 8) * s.n2 + (s.h2Gen - 3 * s.n2) / 4 := by
    simpa [PlantState.methane, PlantState.excess] using h1
  have hx' : s.h2Gen - 3 * s.n2 = 0 := by
    simpa [PlantState.excess] using hex
  linarith

/-- The H₂-exact split of the methane feed: 4·feed = 3·extra. -/
theorem feed_split_H2_exact (s : PlantState)
    (hg : GenerationBalance s) (ha : AirBalance s) (hex : s.excess = 0) :
    4 * s.feed = 3 * s.extra := by
  have ha' : s.n2 = 2 * s.extra := ha
  have hg' : s.h2Gen = 4 * s.feed + 3 * s.extra := hg
  have h2ex : s.h2Gen = 4 * s.feed + 3 * s.extra := hg'
  have h2n2 : 2 * s.n2 = 4 * s.extra := by linarith [ha']
  have hex' : s.h2Gen - 3 * s.n2 = 0 := hex
  nlinarith [h2ex, h2n2, hex']

/-- Ammonia produced at overall yield η: nh3 = 2η·n2. -/
theorem nh3_eq_yield (s : PlantState) (hy : 0 < s.overallYield)
    (hh : HaberStoichiometry s) :
    s.nh3 = s.overallYield * 2 * s.n2 := by
  have hh' : s.n2 = s.nh3 / (2 * s.overallYield) := hh
  have hη : s.overallYield ≠ 0 := ne_of_gt hy
  have h2η : (2 : ℝ) * s.overallYield ≠ 0 := mul_ne_zero two_ne_zero hη
  have h2 : s.n2 * (2 * s.overallYield) = s.nh3 := by
    rw [eq_div_iff h2η] at hh'
    linear_combination hh'
  linarith [h2]

/-- **Mol chain theorem.** At the H₂-exact operation of Fig. 1,
    methane (mol) = (7/16)·nh3 / η. -/
theorem methane_mol_chain (s : PlantState)
    (h : OperatesPerFig1 s) (hex : s.excess = 0) (hy : 0 < s.overallYield) :
    s.methane = (7 / 16) * s.nh3 / s.overallYield := by
  have hr := methane_ratio_H2_exact s h hex
  have hh : s.n2 = s.nh3 / (2 * s.overallYield) := h.2.2
  have hη : s.overallYield ≠ 0 := ne_of_gt hy
  have h2η : (2 : ℝ) * s.overallYield ≠ 0 := mul_ne_zero two_ne_zero hη
  -- from HaberStoichiometry: 2·η·n2 = nh3
  have hy1 : 2 * s.overallYield * s.n2 = s.nh3 := by
    have : s.n2 * (2 * s.overallYield) = s.nh3 := by
      rw [eq_div_iff h2η] at hh
      linarith [hh]
    linarith
  -- hr : 8·methane = 7·n2  ⇒  in mole units: methane = (7/8)·n2
  have hm : s.feed + s.extra = (7 / 8) * s.n2 := by
    have hr' : 8 * s.methane = 7 * s.n2 := hr
    simp only [PlantState.methane] at hr'
    linarith [hr']
  -- combine: 8·methane·η = 7·n2·η = (7/2)·nh3  ⇒  methane = 7·nh3/(16·η)
  have key : 8 * s.methane * s.overallYield = (7 / 2) * s.nh3 := by
    nlinarith [hm, hy1]
  rw [eq_div_iff hη]
  -- goal: s.methane * s.overallYield = (7/16) * s.nh3
  nlinarith [key]

/-! ## Numerical raw chain for the printed data (printed-table molar masses) -/

/-- Kilomoles of NH₃ per year (tons ÷ kg kmol⁻¹; the 10³ scale cancels). -/
noncomputable def n_NH3_kmol : ℝ := printedAmmoniaCapacityTons / M_NH3

/-- Methane required, kmol per year, at the H₂-exact Fig. 1 operation. -/
noncomputable def n_CH4_kmol : ℝ := (7 / 16) * n_NH3_kmol / printedOverallYield

/-- The requested raw answer: methane mass in tons. -/
noncomputable def methaneMassTons_raw : ℝ := M_CH4 * n_CH4_kmol

/-- Closed numerical value of the raw expression with all printed decimals
cleared: raw = 77202125000/275383 tons ≈ 280 344.56 t. -/
theorem methaneMassTons_raw_value :
    methaneMassTons_raw = 77202125000 / 275383 := by
  rw [methaneMassTons_raw, n_CH4_kmol, n_NH3_kmol,
    printedAmmoniaCapacityTons, printedOverallYield, M_CH4_value, M_NH3_value]
  field_simp
  norm_num

/-- The raw value (≈ 280 344.6 t) lies strictly inside the 3-significant-figure
reporting cell 2.80×10⁵ ± 500, so it reports half away from zero as
280 000 tons. -/
theorem methaneMassTons_reports_280e3 :
    ReportsAtQuantum methaneMassTons_raw 280000 1000 := by
  have hv := methaneMassTons_raw_value
  have hraw_pos : 0 ≤ methaneMassTons_raw := by rw [hv]; norm_num
  refine ⟨by norm_num, ⟨280, by norm_num⟩, ?_⟩
  rw [if_pos hraw_pos]
  rw [hv]
  constructor <;> norm_num

/-- Bundle of the full raw chain for the printed 660 000 t / 97.0 % problem,
with the printed periodic-table molar masses. -/
theorem annual_methane_mass_chain :
    ∃ m n_ch4 n_nh3 : ℝ,
      n_nh3 = printedAmmoniaCapacityTons / M_NH3 ∧
      n_ch4 = (7 / 16) * n_nh3 / printedOverallYield ∧
      m = M_CH4 * n_ch4 ∧
      ReportsAtQuantum m 280000 1000 :=
  ⟨methaneMassTons_raw, n_CH4_kmol, n_NH3_kmol,
    rfl, rfl, rfl, methaneMassTons_reports_280e3⟩

end IChO2026T7A2
