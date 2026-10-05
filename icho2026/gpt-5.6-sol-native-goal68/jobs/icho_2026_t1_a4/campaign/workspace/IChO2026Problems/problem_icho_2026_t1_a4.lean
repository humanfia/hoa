import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026 T1-A4: the mysterious stone

This file keeps three kinds of information separate.

* `Formula`, `atomicMass`, and the percentage functions are the mathematical
  model.  The atomic masses are exactly the displayed values in the periodic
  table supplied with the problem.
* `IndustrialFluoridePair` and the sodium-free precursor condition state the
  ordinary chemistry used to interpret the prose clues: cryolite is the
  sodium aluminium fluoride used in industrial aluminium production, while
  precipitated anhydrous C is the metal fluoride rather than a sodium salt.
* The theorems then check all three printed percentages, balance the NaF
  conversion, and prove without a search bound that the hydration number is
  uniquely three.

No numerical result is postulated.
-/

namespace IChO2026Problems.T1A4

open IChO2026Chem.Reporting

/-- Elements needed for this subproblem. -/
inductive Element where
  | H | O | F | Na | Al
  deriving DecidableEq, Repr

/-- Atomic masses printed in the problem's periodic table, in g mol⁻¹. -/
def atomicMass : Element → ℝ
  | .H  => 1.008
  | .O  => 16.00
  | .F  => 19.00
  | .Na => 22.99
  | .Al => 26.98

/-- Molecular formula, represented by atom counts for the five relevant
elements. -/
structure Formula where
  hydrogen : ℕ
  oxygen : ℕ
  fluorine : ℕ
  sodium : ℕ
  aluminum : ℕ
  deriving DecidableEq, Repr

namespace Formula

def atomCount (f : Formula) : Element → ℕ
  | .H  => f.hydrogen
  | .O  => f.oxygen
  | .F  => f.fluorine
  | .Na => f.sodium
  | .Al => f.aluminum

def add (a b : Formula) : Formula :=
  ⟨a.hydrogen + b.hydrogen,
   a.oxygen + b.oxygen,
   a.fluorine + b.fluorine,
   a.sodium + b.sodium,
   a.aluminum + b.aluminum⟩

def scale (n : ℕ) (f : Formula) : Formula :=
  ⟨n * f.hydrogen, n * f.oxygen, n * f.fluorine,
   n * f.sodium, n * f.aluminum⟩

def molarMass (f : Formula) : ℝ :=
  (f.hydrogen : ℝ) * atomicMass .H +
  (f.oxygen : ℝ) * atomicMass .O +
  (f.fluorine : ℝ) * atomicMass .F +
  (f.sodium : ℝ) * atomicMass .Na +
  (f.aluminum : ℝ) * atomicMass .Al

noncomputable def elementMassPercent (f : Formula) (e : Element) : ℝ :=
  100 * ((f.atomCount e : ℝ) * atomicMass e) / f.molarMass

end Formula

/-- H₂O. -/
def water : Formula := ⟨2, 1, 0, 0, 0⟩

/-- NaF. -/
def sodiumFluoride : Formula := ⟨0, 0, 1, 1, 0⟩

/-- Anhydrous aluminium fluoride, AlF₃. -/
def aluminumFluoride : Formula := ⟨0, 0, 3, 0, 1⟩

/-- Add `x` waters of crystallisation to an anhydrous formula. -/
def hydrate (c : Formula) (x : ℕ) : Formula :=
  Formula.add c (Formula.scale x water)

/-- Aluminium fluoride trihydrate, AlF₃·3H₂O. -/
def aluminumFluorideTrihydrate : Formula := hydrate aluminumFluoride 3

/-- Cryolite (trisodium hexafluoroaluminate), Na₃AlF₆. -/
def cryolite : Formula := ⟨0, 0, 6, 3, 1⟩

/-- The formal atom-count composition Na₂AlF₅.  This is used below only to
exhibit why the printed arithmetic and bare atom balance do not, by
themselves, prove that C is sodium-free; no claim that its hexahydrate is the
precipitated phase is built into the model. -/
def sodiumPentafluoroaluminateComposition : Formula := ⟨0, 0, 5, 2, 1⟩

/-- Mass percentage attributable to waters of crystallisation. -/
noncomputable def waterMassPercent (c : Formula) (x : ℕ) : ℝ :=
  100 * ((x : ℝ) * water.molarMass) / (hydrate c x).molarMass

/-- One unit in the last printed decimal place of a percentage. -/
def percentQuantum : ℝ := 0.01

/-- The standard chemical classification behind the industrial clue.
Among the fluoride pair discussed in this problem, cryolite Na₃AlF₆ is the
electrolyte/solvent used in industrial aluminium production.  Making this a
closed inductive relation exposes the domain fact as part of the model. -/
inductive IndustrialFluoridePair : Formula → Element → Prop where
  | hallHeroult : IndustrialFluoridePair cryolite .Al

/-- A formula is the neutral binary fluoride of one atom of `q` in oxidation
state `charge`.  Fluoride has charge -1, so charge balance fixes its count. -/
def NeutralBinaryFluoride
    (c : Formula) (q : Element) (charge : ℕ) : Prop :=
  c.hydrogen = 0 ∧ c.oxygen = 0 ∧ c.sodium = 0 ∧
  c.fluorine = charge ∧ c.atomCount q = 1

/-- Formal atom balance for conversion by adding only NaF. -/
def ConvertsWithNaF (c d : Formula) : Prop :=
  ∃ n : ℕ, Formula.add c (Formula.scale n sodiumFluoride) = d

theorem water_molarMass : water.molarMass = 18.016 := by
  norm_num [water, Formula.molarMass, atomicMass]

theorem aluminumFluoride_molarMass : aluminumFluoride.molarMass = 83.98 := by
  norm_num [aluminumFluoride, Formula.molarMass, atomicMass]

theorem cryolite_molarMass : cryolite.molarMass = 209.95 := by
  norm_num [cryolite, Formula.molarMass, atomicMass]

/-- The proposed D reproduces the displayed sodium percentage to its printed
precision (32.85 ± 0.005 percentage points). -/
theorem cryolite_sodium_percentage :
    ConsistentMeasurement
      (cryolite.elementMassPercent .Na) 32.85 percentQuantum := by
  norm_num [ConsistentMeasurement, percentQuantum,
    Formula.elementMassPercent, Formula.atomCount, cryolite,
    Formula.molarMass, atomicMass, abs_le]

/-- The same proposed D reproduces the displayed Q = Al percentage to its
printed precision (12.85 ± 0.005 percentage points). -/
theorem cryolite_aluminum_percentage :
    ConsistentMeasurement
      (cryolite.elementMassPercent .Al) 12.85 percentQuantum := by
  norm_num [ConsistentMeasurement, percentQuantum,
    Formula.elementMassPercent, Formula.atomCount, cryolite,
    Formula.molarMass, atomicMass, abs_le]

/-- Three waters give the displayed 39.16% water to its printed precision. -/
theorem aluminumFluoride_trihydrate_water_percentage :
    ConsistentMeasurement
      (waterMassPercent aluminumFluoride 3) 39.16 percentQuantum := by
  norm_num [ConsistentMeasurement, percentQuantum, waterMassPercent,
    hydrate, Formula.add, Formula.scale, water, aluminumFluoride,
    Formula.molarMass, atomicMass, abs_le]

/-- The conversion stated in the question is atom-balanced as
AlF₃ + 3 NaF → Na₃AlF₆. -/
theorem aluminumFluoride_converts_to_cryolite :
    ConvertsWithNaF aluminumFluoride cryolite := by
  refine ⟨3, ?_⟩
  decide

/-- A source-gap witness: if all phase-identity chemistry is erased and one
keeps only formula arithmetic, the distinct composition Na₂AlF₅·6H₂O also
has the same rounded water percentage and takes up one NaF to reach cryolite.
Thus the sodium-free metal-fluoride interpretation must remain explicit. -/
theorem bare_arithmetic_does_not_identify_C :
    sodiumPentafluoroaluminateComposition ≠ aluminumFluoride ∧
    ConvertsWithNaF sodiumPentafluoroaluminateComposition cryolite ∧
    ConsistentMeasurement
      (waterMassPercent sodiumPentafluoroaluminateComposition 6)
      39.16 percentQuantum := by
  refine ⟨by decide, ?_, ?_⟩
  · refine ⟨1, ?_⟩
    decide
  · norm_num [ConsistentMeasurement, percentQuantum, waterMassPercent,
      hydrate, Formula.add, Formula.scale, water,
      sodiumPentafluoroaluminateComposition,
      Formula.molarMass, atomicMass, abs_le]

/-- A neutral fluoride of one Al(III) centre is necessarily AlF₃ in the
formula model. -/
theorem neutral_aluminum_III_fluoride_eq
    {c : Formula} (h : NeutralBinaryFluoride c .Al 3) :
    c = aluminumFluoride := by
  rcases h with ⟨hH, hO, hNa, hF, hAl⟩
  rcases c with ⟨hydrogen, oxygen, fluorine, sodium, aluminum⟩
  simp_all [Formula.atomCount, aluminumFluoride]

/-- If sodium-free C takes up only NaF to give cryolite, atom balance forces
C = AlF₃ and the reacting amount of NaF is three formula units.  This uses the
reaction clue directly rather than assuming the formula of C. -/
theorem sodium_free_precursor_eq_aluminumFluoride
    {c : Formula}
    (hSodiumFree : c.sodium = 0)
    (hConversion : ConvertsWithNaF c cryolite) :
    c = aluminumFluoride := by
  rcases hConversion with ⟨n, hn⟩
  have hNa := congrArg Formula.sodium hn
  simp [Formula.add, Formula.scale, sodiumFluoride, cryolite,
    hSodiumFree] at hNa
  have hnThree : n = 3 := by omega
  subst n
  rcases c with ⟨hydrogen, oxygen, fluorine, sodium, aluminum⟩
  simp_all [Formula.add, Formula.scale, sodiumFluoride, cryolite,
    aluminumFluoride]

/-- The hydration number is determined without imposing any finite search
bound: every natural number consistent with 39.16% at the printed precision
is exactly 3. -/
theorem hydration_number_eq_three
    {x : ℕ}
    (h : ConsistentMeasurement
      (waterMassPercent aluminumFluoride x) 39.16 percentQuantum) :
    x = 3 := by
  have hb := h.2
  rw [abs_le] at hb
  have hlow : (39.155 : ℝ) ≤ waterMassPercent aluminumFluoride x := by
    norm_num [percentQuantum] at hb ⊢
    linarith [hb.1]
  have hupp : waterMassPercent aluminumFluoride x ≤ (39.165 : ℝ) := by
    norm_num [percentQuantum] at hb ⊢
    linarith [hb.2]
  have hformula :
      waterMassPercent aluminumFluoride x =
        100 * ((x : ℝ) * 18.016) / (83.98 + (x : ℝ) * 18.016) := by
    norm_num [waterMassPercent, hydrate, Formula.add, Formula.scale,
      water, aluminumFluoride, Formula.molarMass, atomicMass]
    ring
  rw [hformula] at hlow hupp
  have hxnonneg : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
  have hden : 0 < (83.98 : ℝ) + (x : ℝ) * 18.016 := by
    positivity
  have hlowCross :
      (39.155 : ℝ) * (83.98 + (x : ℝ) * 18.016) ≤
        100 * ((x : ℝ) * 18.016) :=
    (le_div_iff₀ hden).mp hlow
  have huppCross :
      100 * ((x : ℝ) * 18.016) ≤
        (39.165 : ℝ) * (83.98 + (x : ℝ) * 18.016) :=
    (div_le_iff₀ hden).mp hupp
  have hxlowReal : (2 : ℝ) < (x : ℝ) := by
    norm_num at hlowCross
    nlinarith
  have hxuppReal : (x : ℝ) < (4 : ℝ) := by
    norm_num at huppCross
    nlinarith
  have hxlow : 2 < x := by exact_mod_cast hxlowReal
  have hxupp : x < 4 := by exact_mod_cast hxuppReal
  omega

/-- The complete requested identification from the explicitly separated
chemical interpretation and the measured hydrate percentage. -/
theorem identify_metal_C_and_D
    {q : Element} {c d : Formula} {x : ℕ}
    (hIndustrial : IndustrialFluoridePair d q)
    (hSodiumFree : c.sodium = 0)
    (hConversion : ConvertsWithNaF c d)
    (hWater : ConsistentMeasurement
      (waterMassPercent c x) 39.16 percentQuantum) :
    q = .Al ∧
    c = aluminumFluoride ∧
    x = 3 ∧
    hydrate c x = aluminumFluorideTrihydrate ∧
    d = cryolite := by
  cases hIndustrial
  have hc : c = aluminumFluoride :=
    sodium_free_precursor_eq_aluminumFluoride hSodiumFree hConversion
  subst c
  have hx : x = 3 := hydration_number_eq_three hWater
  subst x
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Requested output 1: the metal selected by the industrial-use clue. -/
theorem metal_q_identity
    {q : Element} {d : Formula}
    (hIndustrial : IndustrialFluoridePair d q) :
    q = .Al := by
  cases hIndustrial
  rfl

/-- Requested output 3: the industrial fluoride is Na₃AlF₆. -/
theorem compound_d_formula
    {q : Element} {d : Formula}
    (hIndustrial : IndustrialFluoridePair d q) :
    d = cryolite := by
  cases hIndustrial
  rfl

/-- Requested output 2: the precipitate is AlF₃·3H₂O. -/
theorem hydrated_c_formula
    {q : Element} {c d : Formula} {x : ℕ}
    (hIndustrial : IndustrialFluoridePair d q)
    (hSodiumFree : c.sodium = 0)
    (hConversion : ConvertsWithNaF c d)
    (hWater : ConsistentMeasurement
      (waterMassPercent c x) 39.16 percentQuantum) :
    hydrate c x = aluminumFluorideTrihydrate := by
  exact (identify_metal_C_and_D hIndustrial hSodiumFree hConversion hWater).2.2.2.1

/-- The identified formulas jointly satisfy every quantitative and reaction
check printed in T1-A4. -/
theorem identified_answer_satisfies_problem_data :
    ConsistentMeasurement
        (waterMassPercent aluminumFluoride 3) 39.16 percentQuantum ∧
    ConsistentMeasurement
        (cryolite.elementMassPercent .Na) 32.85 percentQuantum ∧
    ConsistentMeasurement
        (cryolite.elementMassPercent .Al) 12.85 percentQuantum ∧
    ConvertsWithNaF aluminumFluoride cryolite := by
  exact ⟨aluminumFluoride_trihydrate_water_percentage,
    cryolite_sodium_percentage,
    cryolite_aluminum_percentage,
    aluminumFluoride_converts_to_cryolite⟩

end IChO2026Problems.T1A4

#print axioms IChO2026Problems.T1A4.hydration_number_eq_three
#print axioms IChO2026Problems.T1A4.identify_metal_C_and_D
#print axioms IChO2026Problems.T1A4.metal_q_identity
#print axioms IChO2026Problems.T1A4.hydrated_c_formula
#print axioms IChO2026Problems.T1A4.compound_d_formula
#print axioms IChO2026Problems.T1A4.identified_answer_satisfies_problem_data
#print axioms IChO2026Problems.T1A4.bare_arithmetic_does_not_identify_C
