import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, Theory Problem 3, Subquestion 3.7 (target `icho_2026_t3_a7`)

COF-9 (obtained from COF-8 by conversion of its nitrile groups to amidoximes
using NH₂OH) adsorbs UO₂²⁺ ions.  In the stated experiment a suspension of
5.000 mg COF-9 in 200.0 mL of 19.90 mg dm⁻³ UO₂²⁺ solution was filtered
after equilibrium; the final UO₂²⁺ concentration was 9.225 mg dm⁻³
(Q3-7, official English sheet).

**Output 1 — equilibrium adsorption capacity qₑ (mg g⁻¹).**
Exact mass balance on the solute:

  qₑ = (C₀ − Cₑ) · V / m = (19.90 − 9.225) · 0.2000 / 0.005000 = 427 mg g⁻¹.

**Output 2 — UO₂²⁺ ions absorbed per pore.**
A pore is one hexagonal opening of the 3,3-connected honeycomb (hcb) net.
For any 3-connected periodic net, Euler's polyhedron formula gives
one face (hexagon ⇔ pore) per two vertices.  The vertices of COF-9 (drawn
with dashed repeat boundaries on the Q3-6/Q3-7 sheets) are alternately
E1-derived nodes (1,3,5-trisubstituted benzene, C₆H₃, carrying three
amidoxime groups after NH₂OH treatment) and D2-derived nodes
(1,3,5-triazine, C₃N₃); the edges each carry two p-phenylene spacers (C₆H₄)
and one vinylene bridge (–CH=C<, C₂H).  Per pore = per two-vertex cell this
sums to:

  1 × C₆H₃ (E1 ring) + 1 × C₃N₃ (triazine) + 3 × C₆H₄ (phenylene)
  + 3 × C₂H (vinylene) + 3 × C₁N₁H₃O₁ (amidoxime) = C₃₆H₂₇N₉O₃,

which is exactly E1 + D2 − 3 H₂O + 3 NH₂OH (each of the three nitriles per
cell becomes an amidoxime –C(=NOH)NH₂).  The number of uranyl ions per pore
is therefore the Avogadro-free ratio

  n(UO₂²⁺) per pore = qₑ · M_pore / (1000 · M(UO₂²⁺)),

with qₑ in mg g⁻¹, M_pore the mass of framework per pore in g mol⁻¹, and
M(UO₂²⁺) = 238.02891 + 2 × 15.999 = 270.02691 g mol⁻¹ (CODATA 2022 relative
atomic masses; these tabulated constants are *not printed on the problem
sheet* and are recorded as a stated assumption).

Working only with the exact measurement-based quantity `427 · M_pore /
(1000 · M(UO₂²⁺))`, no floating-point rounding is involved until the final
3-significant-figure display (0.995 ≤ value < 1.005 ⇒ 1.00 at 3 s.f.).
-/

namespace IChO2026T3A7

/-! ## Problem-stated inputs (printed on Q3-7) -/

/-- Initial UO₂²⁺ concentration, 19.90 mg dm⁻³. -/
def c0 : ℚ := 19.90
/-- Equilibrium UO₂²⁺ concentration after filtration, 9.225 mg dm⁻³. -/
def ce : ℚ := 9.225
/-- Solution volume, 200.0 mL = 0.2000 dm³. -/
def Vsol : ℚ := 0.2000
/-- Mass of COF-9, 5.000 mg = 0.005000 g. -/
def mCOF9 : ℚ := 0.005000

/-! ## Output 1: equilibrium adsorption capacity -/

/-- Equilibrium adsorption capacity by exact mass balance: mass of UO₂²⁺
removed from solution per gram of COF-9. -/
def qeRaw (C0 Ce V m : ℚ) : ℚ := (C0 - Ce) * V / m

/-- Raw exact value: (19.90 − 9.225) · 0.2000 / 0.005000 = 427 exactly
(no rounding at any intermediate step). -/
theorem qe_raw_value : qeRaw c0 ce Vsol mCOF9 = 427 := by
  unfold qeRaw c0 ce Vsol mCOF9; norm_num

theorem mCOF9_pos : (0 : ℚ) < mCOF9 := by unfold mCOF9; norm_num

theorem qe_pos : 0 < qeRaw c0 ce Vsol mCOF9 := by rw [qe_raw_value]; norm_num

/-- qₑ = 427 is already an integer, so 3-significant-figure reporting at
quantum 1 mg g⁻¹ is tie-free and exact. -/
theorem qe_reports_at_427 :
    IChO2026Chem.Reporting.ReportsAtQuantum (qeRaw c0 ce Vsol mCOF9) 427 1 := by
  rw [qe_raw_value]
  refine ⟨one_pos, ⟨427, by norm_num⟩, ?_⟩
  norm_num

/-- Final statement, output 1: qₑ(COF-9) = 427 mg g⁻¹ (3 s.f.). -/
theorem equilibrium_absorption_capacity :
    qeRaw c0 ce Vsol mCOF9 = 427 ∧
    IChO2026Chem.Reporting.ReportsAtQuantum (qeRaw c0 ce Vsol mCOF9) 427 1 :=
  ⟨qe_raw_value, qe_reports_at_427⟩

/-! ## Output 2: ions per pore -/

/-- Atom counts of the COF-9 honeycomb repeat per pore (one hcb hexagon =
one two-vertex cell): C₃₆H₂₇N₉O₃ — 1 E1 ring (C₆H₃), 1 triazine (C₃N₃),
3 phenylenes (C₆H₄), 3 vinylenes (C₂H), 3 amidoximes (CNH₃O). -/
def poreC : ℕ := 6 + 3 + 3 * 6 + 3 * 2 + 3
def poreH : ℕ := 3 + 3 * 4 + 3 + 3 * 3
def poreN : ℕ := 3 + 3 + 3
def poreO : ℕ := 3

theorem poreC_eq : poreC = 36 := rfl
theorem poreH_eq : poreH = 27 := rfl
theorem poreN_eq : poreN = 9 := rfl
theorem poreO_eq : poreO = 3 := rfl

/-- Molar mass of one pore's worth of framework from atomic masses. -/
def poreMass (mC mH mN mO : ℚ) : ℚ :=
  poreC * mC + poreH * mH + poreN * mN + poreO * mO

/-- CODATA 2022 tabulated relative atomic masses (trusted general constants,
not printed in the problem): C 12.011, H 1.008, N 14.007, O 15.999,
U 238.02891. -/
theorem poreMass_codata :
    poreMass 12.011 1.008 14.007 15.999 = 633.672 := by
  unfold poreMass poreC poreH poreN poreO; norm_num

/-- Uranyl molar mass with electron mass neglected (standard convention). -/
def mUO2 (mU mO : ℚ) : ℚ := mU + 2 * mO

theorem mUO2_codata : mUO2 238.02891 15.999 = 270.02691 := by
  unfold mUO2; norm_num

/-- Ions adsorbed per gram of adsorbent. -/
def ionsPerGram (q mIon NA : ℚ) : ℚ := q / 1000 / mIon * NA

/-- Pores per gram of adsorbent (one pore per molar repeat of mass `Mpore`). -/
def poresPerGram (Mpore NA : ℚ) : ℚ := NA / Mpore

/-- The Avogadro constant cancels between the two counts, leaving the exact
dimensionless ratio `q · Mpore / (1000 · mIon)`. -/
theorem ions_per_pore_eq (q mIon Mpore NA : ℚ)
    (hIon : mIon ≠ 0) (hP : Mpore ≠ 0) (hNA : NA ≠ 0) :
    ionsPerGram q mIon NA / poresPerGram Mpore NA =
      q * Mpore / (1000 * mIon) := by
  unfold ionsPerGram poresPerGram
  field_simp

/-- Exact value expression with the measured qₑ substituted:
427 · M_pore / (1000 · M(UO₂²⁺)). -/
theorem ions_per_pore_raw (Mpore mIon NA : ℚ)
    (hIon : mIon ≠ 0) (hP : Mpore ≠ 0) (hNA : NA ≠ 0) :
    ionsPerGram (qeRaw c0 ce Vsol mCOF9) mIon NA / poresPerGram Mpore NA =
      427 * Mpore / (1000 * mIon) := by
  rw [ions_per_pore_eq _ _ _ _ hIon hP hNA, qe_raw_value]

/-- CODATA evaluation of the exact ratio, as an exact rational:
427 × 633.672 / (1000 × 270.02691) = 33822243 / 33753363.75. -/
theorem ions_per_pore_codata :
    (qeRaw c0 ce Vsol mCOF9 : ℚ) * poreMass 12.011 1.008 14.007 15.999 /
      (1000 * mUO2 238.02891 15.999) = 33822243 / 33753363.75 := by
  rw [qe_raw_value, poreMass_codata, mUO2_codata]; norm_num

/-- The exact CODATA ratio lies strictly inside [0.995, 1.005): it rounds to
1.00 at three significant figures (quantum 0.01), and no tie rule is needed. -/
theorem uranyl_ions_per_pore_reports :
    IChO2026Chem.Reporting.ReportsAtQuantum
      ((qeRaw c0 ce Vsol mCOF9 : ℚ) * poreMass 12.011 1.008 14.007 15.999 /
          (1000 * mUO2 238.02891 15.999) : ℝ) 1.00 0.01 := by
  rw [qe_raw_value, poreMass_codata, mUO2_codata]
  refine ⟨by norm_num, ⟨100, by norm_num⟩, ?_⟩
  norm_num

/-- Positivity sanity check consistent with adsorption having occurred. -/
theorem uranyl_ions_per_pore_pos :
    (0 : ℝ) < (qeRaw c0 ce Vsol mCOF9 : ℚ) * poreMass 12.011 1.008 14.007 15.999 /
      (1000 * mUO2 238.02891 15.999) := by
  rw [qe_raw_value, poreMass_codata, mUO2_codata]; norm_num

end IChO2026T3A7

/-- Final theorem, output 1 of IChO 2026 T3-A7:
the equilibrium adsorption capacity of COF-9 is exactly
(19.90 − 9.225) × 0.2000 / 0.005000 = 427 mg g⁻¹, reported at 3 s.f. -/
theorem icho_2026_t3_a7_equilibrium_absorption_capacity :
    IChO2026T3A7.qeRaw IChO2026T3A7.c0 IChO2026T3A7.ce IChO2026T3A7.Vsol
        IChO2026T3A7.mCOF9 = 427 ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      (IChO2026T3A7.qeRaw IChO2026T3A7.c0 IChO2026T3A7.ce IChO2026T3A7.Vsol
        IChO2026T3A7.mCOF9) 427 1 :=
  IChO2026T3A7.equilibrium_absorption_capacity

/-- Final theorem, output 2 of IChO 2026 T3-A7: for any Avogadro constant
`NA ≠ 0`, the number of uranyl ions per pore (COF-9 repeat per pore =
C₃₆H₂₇N₉O₃ with CODATA 2022 atomic masses; molar-mass values are a documented
assumption not printed on the problem sheet) equals the exact ratio
427·M_pore/(1000·M(UO₂²⁺)) = 33822243/33753363.75 ≈ 1.0020 and reports as
1.00 ions per pore at 3 significant figures. -/
theorem icho_2026_t3_a7_uranyl_ions_per_pore (NA : ℚ) (hNA : NA ≠ 0) :
    IChO2026T3A7.ionsPerGram
        (IChO2026T3A7.qeRaw IChO2026T3A7.c0 IChO2026T3A7.ce IChO2026T3A7.Vsol
          IChO2026T3A7.mCOF9)
        (IChO2026T3A7.mUO2 238.02891 15.999) NA /
      IChO2026T3A7.poresPerGram
        (IChO2026T3A7.poreMass 12.011 1.008 14.007 15.999) NA
      = 33822243 / 33753363.75 ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      ((IChO2026T3A7.qeRaw IChO2026T3A7.c0 IChO2026T3A7.ce IChO2026T3A7.Vsol
          IChO2026T3A7.mCOF9 : ℚ) *
        IChO2026T3A7.poreMass 12.011 1.008 14.007 15.999 /
          (1000 * IChO2026T3A7.mUO2 238.02891 15.999) : ℝ)
      1.00 0.01 := by
  have hIon : (IChO2026T3A7.mUO2 238.02891 15.999 : ℚ) ≠ 0 := by
    rw [IChO2026T3A7.mUO2_codata]; norm_num
  have hP : (IChO2026T3A7.poreMass 12.011 1.008 14.007 15.999 : ℚ) ≠ 0 := by
    rw [IChO2026T3A7.poreMass_codata]; norm_num
  rw [IChO2026T3A7.ions_per_pore_eq _ _ _ _ hIon hP hNA]
  exact ⟨IChO2026T3A7.ions_per_pore_codata,
         IChO2026T3A7.uranyl_ions_per_pore_reports⟩

#print axioms icho_2026_t3_a7_equilibrium_absorption_capacity
#print axioms icho_2026_t3_a7_uranyl_ions_per_pore
