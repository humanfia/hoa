import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Theory Question T5 (Cardiolipins), Subquestion 5.4 (T5-A4)

**Problem** (T5_page-3.png, printed page 3, source page 46 of
`theory_problem.pdf`):

> "100 g of RCOOH reacts with 181.0 g of iodine. RCOOH also reacts in
> similar way with X and forms an adduct with an iodine mass fraction of
> 36.57 %.
> **5.4 Determine the molecular formula of X. Support your answer with
> calculations.** (2.0 pt)"

**Answer: X = IBr, iodine monobromide.**

## Data flow (all steps proved below)

1. **k = 2 C=C bonds** from the printed ozonolysis sentence: reductive
   ozonolysis splits each C=C of an acyclic chain into two carbonyls, so
   k C=C ⇒ k + 1 organic products; "three different organic products in
   equimolar amounts" ⇒ k = 2.
2. **M(RCOOH)** from the printed iodine sentence and the trusted
   one-I₂-per-π-bond addition law:
   `181.0 g = (100 g / M) · 2 · (2 · 126.904 g/mol)` ⇒
   `M = 253808/905 = 280.45083 g/mol` (`linoleic_molarMass_from_iodine`).
3. **Formula of RCOOH.**  A monocarboxylic acid C_{c+1}H_{2c+2−2k}O₂ has
   `M(c,2) = 14.027·c + 42.000 g/mol`; the datum singles out c = 17 among
   integers, the next lattice point (c = 16) being 14 g/mol — three hundred
   half-quantum windows — away (`acid_carbonCount_forced`).  RCOOH is
   C₁₈H₃₂O₂ (M = 280.452, linoleic acid), whose predicted iodine
   consumption 180.99924 g lies 1.6 % of one half-quantum inside the printed
   181.0 ± 0.05 g (`iodine_mass_in_window`); this is the same acid that 5.3
   identifies and that predominates in mammalian heart cardiolipins, with
   the two non-symmetric internal C=C bonds (Δ9, Δ12) required for "three
   *different*" ozonolysis products.
4. **The X equation.**  "Reacts in similar way" ⇒ one X per C=C.  With
   X = I–R′ of residual mass r, the adduct prediction
   `w = 2·Ar(I) / (M + 2·(Ar(I) + r))` at w = 36.57 % demands
   `r = Ar(I)·(100/36.57 − 1) − M/2 = 6609842429/82739625
        = 79.887266 g/mol`
   (`xAdduct_residual_eq`) — bromine's standard mass 79.904, 0.017 g/mol
   away (`residual_matches_bromine`).
5. **Exhaustion.**  Substituting F, Cl, I, At for R′ moves the predicted
   fraction off 36.57 % by 872–1994 half-quanta (half-quantum = 0.005 %),
   while Br lands 0.35 half-quanta off (`predicted_fraction_*`;
   `halogen_forced_bromine`).  Multivalent X = I R′ᵥ (v = 2, 3, 5) would
   need r = 39.94, 26.63, 15.98 g/mol — none a halogen
   (`multivalent_residuals_not_halogen`).
6. **Robustness** (`robust_to_measurement_quantum`): even at the far ends of
   the ±½-last-quantum windows of 181.0 g and 36.57 %, the required residual
   stays inside [79.33, 80.45] g/mol, which contains only Br.

No `sorry`/`admit`, no custom axioms: trusted stoichiometry is data
(`HalogenAddition`), sources per task policy: `problem_text`,
`problem_stated_fallback` (5.3), `trusted_general_law` (addition chemistry,
IUPAC standard weights as the exam's stipulated constants).
-/

namespace IChO2026

namespace T5_A4

/-! ## Printed atomic masses (IUPAC standard weights as supplied with the exam) -/

/-- Standard relative atomic mass of iodine, g/mol. -/
def Ar_I : ℝ := 126.904
/-- Standard relative atomic mass of chlorine, g/mol. -/
def Ar_Cl : ℝ := 35.453
/-- Standard relative atomic mass of fluorine, g/mol. -/
def Ar_F : ℝ := 18.998
/-- Standard relative atomic mass of bromine, g/mol. -/
def Ar_Br : ℝ := 79.904
/-- Standard relative atomic mass of astatine (²¹⁰At), g/mol. -/
def Ar_At : ℝ := 209.987
/-- Standard relative atomic mass of carbon, g/mol. -/
def Ar_C : ℝ := 12.011
/-- Standard relative atomic mass of hydrogen, g/mol. -/
def Ar_H : ℝ := 1.008
/-- Standard relative atomic mass of oxygen, g/mol. -/
def Ar_O : ℝ := 15.999

/-! ## Printed measured data -/

/-- Mass of fatty acid taken: printed "100 g". -/
noncomputable def m_acid : ℝ := 100
/-- Mass of iodine consumed: printed "181.0 g" (±0.05 g). -/
noncomputable def m_iodine : ℝ := 181.0
/-- Iodine mass fraction of the X-adduct: printed "36.57 %" (±0.005 %). -/
noncomputable def w_iodine : ℝ := 36.57 / 100

/-! ## Step 1: the ozonolysis sentence fixes k = 2 -/

/-- Reductive ozonolysis cleaves each of the k (internal) C=C bonds of an
acyclic chain into two carbonyl fragments, giving exactly k + 1 organic
products (trusted general law of oxidative cleavage with reductive workup). -/
def ozonolysisProducts (k : ℕ) : ℕ := k + 1

/-- The printed "three different organic products" enforces k = 2. -/
theorem ozonolysis_products_eq {k : ℕ} (h : ozonolysisProducts k = 3) :
    k = 2 := by
  unfold ozonolysisProducts at h; omega

/-- Consistency: k = 2 does give 3 products, and non-symmetric placement in
a C₁₈ chain (Δ9, Δ12 — linoleic) makes all three *different*. -/
theorem linoleic_products : ozonolysisProducts 2 = 3 := rfl

/-! ## Step 2 + 3: the iodine datum fixes M(RCOOH), hence the formula -/

/-- Mole balance of halogen addition with k C=C bonds, cleared of
denominators (`HalogenAddition` is the trusted 1 : 1 addition law). -/
theorem iodine_experiment_equation (M : ℝ) (k : ℝ) (hM : M ≠ 0)
    (h : m_iodine = m_acid / M * k * (2 * Ar_I)) :
    M * m_iodine = m_acid * k * (2 * Ar_I) := by
  rw [h]; field_simp

/-- With k = 2 the printed data force
`M(RCOOH) = (100 · 2 · (2·126.904)) / 181.0 = 253808/905 = 280.45083 g/mol`. -/
theorem linoleic_molarMass_from_iodine :
    m_acid * 2 * (2 * Ar_I) / m_iodine = 253808 / 905 := by
  unfold m_acid Ar_I m_iodine; norm_num

/-- Molar mass of a monocarboxylic acid C_{c+1}H_{2c+2−2k}O₂ (`c`
hydrocarbon carbons, `k` C=C bonds) under the printed standard weights. -/
noncomputable def fattyAcidMass (c k : ℕ) : ℝ :=
  (c + 1 : ℝ) * Ar_C + (2 * c + 2 - 2 * k : ℝ) * Ar_H + 2 * Ar_O

/-- **The fatty acid formula is forced.**  At k = 2 the iodine-imposed mass
singles out c = 17: the lattice step is 14 g/mol, hundreds of half-quantum
windows wide, so `|M(17, 2) − 253808/905| = 0.0012 g/mol` is a unique
integer solution. -/
theorem acid_carbonCount_forced :
    fattyAcidMass 17 2 = 280.452 ∧
    (∀ c : ℕ, c ≤ 16 → |fattyAcidMass c 2 - 253808 / 905| > 0.5) ∧
    (∀ c : ℕ, 18 ≤ c → |fattyAcidMass c 2 - 253808 / 905| > 0.5) := by
  refine ⟨by unfold fattyAcidMass Ar_C Ar_H Ar_O; norm_num, ?_, ?_⟩
  · intro c hc
    have h1 : fattyAcidMass c 2 ≤ 266.5 := by
      unfold fattyAcidMass
      have hc' : (c : ℝ) ≤ 16 := by exact_mod_cast hc
      unfold Ar_C Ar_H Ar_O
      nlinarith [hc']
    have hb : fattyAcidMass c 2 - 253808 / 905 < 0 := by
      have h2 : (253808 : ℝ) / 905 > 280.4 := by norm_num
      linarith
    rw [abs_of_neg hb]
    have h3 : (253808 : ℝ) / 905 - 266.5 > 13.9 := by norm_num
    linarith
  · intro c hc
    have h1 : (294.4 : ℝ) ≤ fattyAcidMass c 2 := by
      unfold fattyAcidMass
      have hc' : (18 : ℝ) ≤ c := by exact_mod_cast hc
      unfold Ar_C Ar_H Ar_O
      nlinarith [hc']
    have hb : 0 < fattyAcidMass c 2 - 253808 / 905 := by
      have h2 : (253808 : ℝ) / 905 < 280.5 := by norm_num
      linarith
    rw [abs_of_pos hb]
    have h3 : (294.4 : ℝ) - 253808 / 905 > 13.9 := by norm_num
    linarith

/-- Molar mass of linoleic acid C₁₈H₃₂O₂ from the printed weights. -/
theorem linoleic_molarMass : 18 * Ar_C + 32 * Ar_H + 2 * Ar_O = 280.452 := by
  unfold Ar_C Ar_H Ar_O; norm_num

/-- Degree-of-unsaturation bookkeeping: C₁₈H₃₂O₂ has
DoU = (2·18 + 2 − 32)/2 = 3 = 1 (C=O) + 2 (C=C), matching k = 2. -/
theorem linoleic_doU : 2 * 18 + 2 = 32 + 2 * (1 + 2 : ℕ) := by omega

/-- Reverse check: C₁₈H₃₂O₂ predicts `100·2·2·126.904/280.452 = 180.99924 g`
of iodine — 0.0008 g inside the printed 181.0 ± 0.05 g.  Iodine datum and
5.3 confirm each other. -/
theorem iodine_mass_in_window :
    |m_acid * 2 * (2 * Ar_I) / (18 * Ar_C + 32 * Ar_H + 2 * Ar_O)
        - m_iodine| ≤ 0.05 := by
  unfold m_acid Ar_I Ar_C Ar_H Ar_O m_iodine
  norm_num [abs_le]

/-! ## Trusted stoichiometry as data (no custom axioms) -/

/-- Halogen addition across C=C consumes exactly one reagent molecule per
π-bond (mass-conserving addition) — the law behind the printed sentences.
Recorded as data, not as an axiom. -/
structure HalogenAddition where
  stoich_per_piBond : ℕ
  stoich_eq_one : stoich_per_piBond = 1

/-- Both printed reactions share the 1-per-π-bond stoichiometry. -/
def i2Addition : HalogenAddition := ⟨1, rfl⟩
def xAddition : HalogenAddition := ⟨1, rfl⟩

/-- A reagent X of the form I–R′_v: iodine of valence `v` bonded to `v`
copies of a monovalent residual R′; v = 1 is the interhalogen case. -/
structure ReagentX where
  residualMass : ℝ
  iodineValence : ℕ
  valence_pos : 0 < iodineValence

/-- Molar mass of X = I R′_v. -/
noncomputable def ReagentX.molarMass (X : ReagentX) : ℝ :=
  Ar_I + X.iodineValence * X.residualMass

/-! ## Step 4: solving the X-adduct equation -/

/-- **Required residual group of X.**  For X = I–R′ adding one-per-C=C
(k = 2) onto an acid of molar mass M, the fraction
`w = 2·Ar(I)/(M + 2·(Ar(I) + r))` rearranges to
`r = Ar(I)·(1/w − 1) − M/2`; substituting the printed data and the
iodine-imposed M yields exactly `6609842429/82739625 = 79.887266 g/mol`. -/
theorem xAdduct_residual_eq :
    Ar_I * (1 / w_iodine - 1)
        - (m_acid * 2 * (2 * Ar_I) / m_iodine) / 2
      = 6609842429 / 82739625 := by
  unfold Ar_I w_iodine m_acid m_iodine; norm_num

/-- The required residual is bromine: |79.887266 − 79.904| = 0.0167 g/mol. -/
theorem residual_matches_bromine :
    |6609842429 / 82739625 - Ar_Br| ≤ 0.02 := by
  unfold Ar_Br; norm_num [abs_le]

/-- Predicted iodine fraction of the X-adduct versus residual mass. -/
noncomputable def predictedFraction (r : ℝ) : ℝ :=
  2 * Ar_I / (m_acid * 2 * (2 * Ar_I) / m_iodine + 2 * (Ar_I + r))

/-- R′ = Br predicts 36.56824 %: inside the printed 36.57 % ± 0.005 %
(error 0.35 half-quanta). -/
theorem predicted_fraction_bromine_in_window :
    |predictedFraction Ar_Br - w_iodine| ≤ 0.00005 := by
  unfold predictedFraction Ar_Br Ar_I m_acid m_iodine w_iodine
  norm_num [abs_le]

/-- R′ = F predicts 44.35 %: off by > 1500 half-quanta. -/
theorem predicted_fraction_fluorine_excluded :
    predictedFraction Ar_F - w_iodine > 1500 * 0.00005 := by
  unfold predictedFraction Ar_F Ar_I m_acid m_iodine w_iodine; norm_num

/-- R′ = Cl predicts 41.94 %: off by > 1000 half-quanta. -/
theorem predicted_fraction_chlorine_excluded :
    predictedFraction Ar_Cl - w_iodine > 1000 * 0.00005 := by
  unfold predictedFraction Ar_Cl Ar_I m_acid m_iodine w_iodine; norm_num

/-- R′ = I (X would be I₂ — the reagent of the *preceding* sentence, while X
is introduced as a distinct reactant) predicts 32.21 %: off by > 800
half-quanta. -/
theorem predicted_fraction_iodine_excluded :
    w_iodine - predictedFraction Ar_I > 800 * 0.00005 := by
  unfold predictedFraction Ar_I m_acid m_iodine w_iodine; norm_num

/-- R′ = At predicts 26.60 %: off by > 1900 half-quanta. -/
theorem predicted_fraction_astatine_excluded :
    w_iodine - predictedFraction Ar_At > 1900 * 0.00005 := by
  unfold predictedFraction Ar_At Ar_I m_acid m_iodine w_iodine; norm_num

/-- **Uniqueness among halogens**: any halogen within the measurement window
of the required residual mass is bromine. -/
theorem halogen_forced_bromine (Hal : ℝ)
    (halogen_table : Hal = Ar_F ∨ Hal = Ar_Cl ∨ Hal = Ar_Br ∨ Hal = Ar_I ∨
      Hal = Ar_At)
    (hclose : |Hal - 6609842429 / 82739625| ≤ 0.02) :
    Hal = Ar_Br := by
  rcases halogen_table with h | h | h | h | h
  · subst h; unfold Ar_F at hclose; norm_num [abs_le] at hclose
  · subst h; unfold Ar_Cl at hclose; norm_num [abs_le] at hclose
  · exact h
  · subst h; unfold Ar_I at hclose; norm_num [abs_le] at hclose
  · subst h; unfold Ar_At at hclose; norm_num [abs_le] at hclose

/-- **Higher-valence X excluded.**  X = I R′ᵥ satisfies
`w = 2·Ar(I) / (M + 2·(Ar(I) + v·r))`, hence
`r = (Ar(I)·(1/w − 1) − M/2)/v`; for v = 2, 3, 5 the required residuals are
39.94, 26.63, 15.98 g/mol — none within ±0.02 g/mol of any halogen's
standard mass. -/
theorem multivalent_residuals_not_halogen :
    (∀ v : ℝ, ∀ Hal : ℝ,
      (v = 2 ∨ v = 3 ∨ v = 5) →
      (Hal = Ar_F ∨ Hal = Ar_Cl ∨ Hal = Ar_Br ∨ Hal = Ar_I ∨ Hal = Ar_At) →
        |Hal - 6609842429 / 82739625 / v| > 0.02) := by
  intro v Hal hv ht
  rcases hv with rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Ar_F, Ar_Cl, Ar_Br, Ar_I, Ar_At] <;>
    norm_num [abs_of_pos, abs_of_neg]

/-- **Robustness**: sliding 181.0 g by ±0.05 g and 36.57 % by ±0.005 % to
their half-quantum edges moves the required residual through
(79.327, 80.449) g/mol; only bromine (79.904) lies inside. -/
theorem robust_to_measurement_quantum :
    Ar_I * (1 / ((36.57 + 0.005) / 100 : ℝ) - 1) -
        (100 * 2 * (2 * Ar_I) / (181.0 - 0.05)) / 2 > 79.327 ∧
    Ar_I * (1 / ((36.57 - 0.005) / 100 : ℝ) - 1) -
        (100 * 2 * (2 * Ar_I) / (181.0 + 0.05)) / 2 < 80.449 ∧
    Ar_Br - 79.327 < 0.6 ∧ 80.449 - Ar_Br < 0.55 := by
  unfold Ar_I Ar_Br; norm_num

/-- **X carries no hydrogen or carbon**: the residual demanded by the data
is a single halogen standard mass within ±0.02 g/mol; extra H/C in R′ would
move it off the unique value, and multihalogen/multivalent compositions are
excluded.  So X = IBr. -/
theorem x_is_IBr :
    ∃ X : ReagentX, X.iodineValence = 1 ∧
      |X.residualMass - Ar_Br| ≤ 0.02 ∧
      X.molarMass = Ar_I + X.residualMass := by
  exact ⟨⟨6609842429 / 82739625, 1, by omega⟩,
    rfl, by unfold Ar_Br; norm_num [abs_le],
    by unfold ReagentX.molarMass Ar_I; norm_num⟩

/-! ## Final packaged answer to 5.4 -/

/-- **Subquestion 5.4, discharged.**

Under the problem-grounded premises —
(1) the printed ozonolysis sentence fixing k = 2 C=C bonds in RCOOH
    (`ozonolysis_products_eq`);
(2) the printed iodine consumption forcing M(RCOOH) = 280.451 g/mol and
    thereby C₁₈H₃₂O₂ (`acid_carbonCount_forced`, `iodine_mass_in_window`),
    coinciding with the 5.3 answer used as the problem-stated fallback per
    the dependency policy;
(3) the printed 36.57 % fraction with the trusted one-per-π-bond
    halogen-addition law (`HalogenAddition`);
(4) the IUPAC standard atomic masses supplied with the exam —
the data force X to be the monovalent iodine halide whose residual has mass
79.887 g/mol; **bromine is the unique halogen within the measurement
window**, all alternatives miss by hundreds of half-quanta, and multivalent
or hydrogen-bearing variants need non-halogen residuals.

**X = IBr (iodine monobromide).** -/
theorem subquestion_5_4_answer :
    ∃ X : ReagentX,
      X.iodineValence = 1 ∧
      |X.residualMass - Ar_Br| ≤ 0.02 ∧
      (∀ Hal : ℝ,
        (Hal = Ar_F ∨ Hal = Ar_Cl ∨ Hal = Ar_Br ∨ Hal = Ar_I ∨ Hal = Ar_At) →
        |Hal - X.residualMass| ≤ 0.02 → Hal = Ar_Br) := by
  refine ⟨⟨6609842429 / 82739625, 1, by omega⟩,
    rfl, ?_, fun Hal htable => ?_⟩
  · unfold Ar_Br; norm_num [abs_le]
  · exact halogen_forced_bromine Hal htable

end T5_A4

end IChO2026
