import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026 T1-A6: thermogravimetry of the mysterious stone

This file formalizes the problem-only derivation.  Formulae are composition
vectors in the six elements that occur in the relevant part of T1.  Atomic
weights are the values printed on page G1-5 of `theory_problem.pdf`.

The earlier clues are checked rather than imported as answers:

* `Na3AlF6` has the displayed Na and Al mass percentages and is obtained from
  `AlF3 + 3 NaF`; `AlF3 . 3 H2O` has the displayed water percentage.
* hexamethylbenzene and mellitic anhydride have the displayed H and O mass
  percentages, and their oxidation/dehydration equations are atom-balanced.

The first TGA step then uniquely determines 16 waters from the measurement
intervals.  Complete combustion in open air, with carbon and hydrogen leaving
as carbon dioxide and water, uniquely determines the remaining solid as
`Al2O3`; the second TGA mass is an independent interval check.
-/

namespace IChO2026Problems.T1A6

open IChO2026Chem.Reporting

/-- Element counts in the order needed for the compounds in T1-A4--A6. -/
@[ext]
structure Formula where
  al : ℕ
  c : ℕ
  h : ℕ
  o : ℕ
  na : ℕ
  f : ℕ
deriving DecidableEq, Repr

namespace Formula

def add (a b : Formula) : Formula :=
  ⟨a.al + b.al, a.c + b.c, a.h + b.h, a.o + b.o,
    a.na + b.na, a.f + b.f⟩

def scale (n : ℕ) (a : Formula) : Formula :=
  ⟨n * a.al, n * a.c, n * a.h, n * a.o, n * a.na, n * a.f⟩

/-- Molar mass from the atomic weights printed in the supplied periodic table. -/
noncomputable def molarMass (a : Formula) : ℝ :=
  (a.al : ℝ) * (2698 / 100 : ℝ) +
    (a.c : ℝ) * (1201 / 100 : ℝ) +
    (a.h : ℝ) * (1008 / 1000 : ℝ) +
    (a.o : ℝ) * 16 +
    (a.na : ℝ) * (2299 / 100 : ℝ) +
    (a.f : ℝ) * 19

end Formula

def water : Formula := ⟨0, 0, 2, 1, 0, 0⟩
def oxygen : Formula := ⟨0, 0, 0, 2, 0, 0⟩
def carbonDioxide : Formula := ⟨0, 1, 0, 2, 0, 0⟩
def sodiumFluoride : Formula := ⟨0, 0, 0, 0, 1, 1⟩
def aluminumFluoride : Formula := ⟨1, 0, 0, 0, 0, 3⟩
def aluminumFluorideTrihydrate : Formula :=
  Formula.add aluminumFluoride (Formula.scale 3 water)
def cryolite : Formula := ⟨1, 0, 0, 0, 3, 6⟩

/-- Hexamethylbenzene, the six-fold-symmetric precursor `E`. -/
def hexamethylbenzene : Formula := ⟨0, 12, 18, 0, 0, 0⟩
/-- Mellitic acid, `C6(COOH)6`, the highly symmetric acid `F`. -/
def melliticAcid : Formula := ⟨0, 12, 6, 12, 0, 0⟩
/-- Mellitic trianhydride `C12O9`, the binary three-fold-symmetric compound `G`. -/
def melliticAnhydride : Formula := ⟨0, 12, 0, 9, 0, 0⟩

/-- Anhydrous aluminium mellitate, fixed by Al(III) and mellitate(6-). -/
def anhydrousStone : Formula := ⟨2, 12, 0, 12, 0, 0⟩
/-- Aluminium mellitate with an initially unknown integral hydration number. -/
def hydratedStone (waters : ℕ) : Formula :=
  Formula.add anhydrousStone (Formula.scale waters water)
/-- Alumina, the stable aluminium-containing solid after combustion in air. -/
def alumina : Formula := ⟨2, 0, 0, 3, 0, 0⟩

/-- Exact formula vectors corresponding to the two fields on answer sheet A1-5. -/
def stoneAnswer : Formula := hydratedStone 16
def compoundHAnswer : Formula := alumina

noncomputable def massPercent (part whole : Formula) : ℝ :=
  100 * Formula.molarMass part / Formula.molarMass whole

/-! ## Checks deriving the A4 and A5 dependencies -/

theorem aluminumFluoride_to_cryolite_balanced :
    Formula.add aluminumFluoride (Formula.scale 3 sodiumFluoride) = cryolite := by
  decide

/-- One mellitate(6-) anion requires exactly two Al(III) ions. -/
theorem aluminum_mellitate_charge_balance_unique
    {aluminumCount : ℕ} (hCharge : 3 * aluminumCount = 6) :
    aluminumCount = 2 := by
  omega

theorem aluminumFluorideTrihydrate_water_percent :
    ConsistentMeasurement
      (massPercent (Formula.scale 3 water) aluminumFluorideTrihydrate)
      39.16 0.01 := by
  norm_num [ConsistentMeasurement, massPercent, Formula.molarMass,
    aluminumFluorideTrihydrate, aluminumFluoride, Formula.add, Formula.scale, water,
    abs_of_nonpos, abs_of_nonneg]

/-- Sodium-only and aluminium-only composition vectors for mass-percent checks. -/
def sodium3 : Formula := ⟨0, 0, 0, 0, 3, 0⟩
def aluminum1 : Formula := ⟨1, 0, 0, 0, 0, 0⟩

theorem cryolite_sodium_percent :
    ConsistentMeasurement (massPercent sodium3 cryolite) 32.85 0.01 := by
  norm_num [ConsistentMeasurement, massPercent, Formula.molarMass,
    sodium3, cryolite, abs_of_nonpos, abs_of_nonneg]

theorem cryolite_aluminum_percent :
    ConsistentMeasurement (massPercent aluminum1 cryolite) 12.85 0.01 := by
  norm_num [ConsistentMeasurement, massPercent, Formula.molarMass,
    aluminum1, cryolite, abs_of_nonpos, abs_of_nonneg]

theorem hexamethylbenzene_oxidation_balanced :
    Formula.add hexamethylbenzene (Formula.scale 9 oxygen) =
      Formula.add melliticAcid (Formula.scale 6 water) := by
  decide

theorem melliticAcid_dehydration_balanced :
    melliticAcid = Formula.add melliticAnhydride (Formula.scale 3 water) := by
  decide

def hydrogen18 : Formula := ⟨0, 0, 18, 0, 0, 0⟩
def oxygen9 : Formula := ⟨0, 0, 0, 9, 0, 0⟩

theorem hexamethylbenzene_hydrogen_percent :
    ConsistentMeasurement
      (massPercent hydrogen18 hexamethylbenzene) 11.18 0.01 := by
  norm_num [ConsistentMeasurement, massPercent, Formula.molarMass,
    hydrogen18, hexamethylbenzene, abs_of_nonpos, abs_of_nonneg]

theorem melliticAnhydride_oxygen_percent :
    ConsistentMeasurement
      (massPercent oxygen9 melliticAnhydride) 49.98 0.01 := by
  norm_num [ConsistentMeasurement, massPercent, Formula.molarMass,
    oxygen9, melliticAnhydride, abs_of_nonpos, abs_of_nonneg]

/-! ## TGA interval calculation and the hydration number -/

noncomputable def dryFraction (waters : ℕ) : ℝ :=
  Formula.molarMass anhydrousStone / Formula.molarMass (hydratedStone waters)

noncomputable def aluminaFraction : ℝ :=
  Formula.molarMass alumina / Formula.molarMass (hydratedStone 16)

theorem molarMass_anhydrousStone :
    Formula.molarMass anhydrousStone = 390.08 := by
  norm_num [Formula.molarMass, anhydrousStone]

theorem molarMass_water : Formula.molarMass water = 18.016 := by
  norm_num [Formula.molarMass, water]

theorem molarMass_hydratedStone (waters : ℕ) :
    Formula.molarMass (hydratedStone waters) =
      390.08 + (waters : ℝ) * 18.016 := by
  simp [Formula.molarMass, hydratedStone, anhydrousStone, Formula.add,
    Formula.scale, water]
  ring

/-- The two displayed masses imply these exact bounds on the dry/initial ratio.
The endpoints come from `(5.75 +/- 0.005)/(10.00 -/+ 0.005)`. -/
theorem dry_ratio_bounds_from_measurements
    {initial dry : ℝ}
    (hInitial : ConsistentMeasurement initial 10.00 0.01)
    (hDry : ConsistentMeasurement dry 5.75 0.01) :
    (1149 : ℝ) / 2001 ≤ dry / initial ∧
      dry / initial ≤ (1151 : ℝ) / 1999 := by
  rcases hInitial with ⟨_, hInitial⟩
  rcases hDry with ⟨_, hDry⟩
  rw [abs_le] at hInitial hDry
  have hInitialLower : (9.995 : ℝ) ≤ initial := by nlinarith
  have hInitialUpper : initial ≤ (10.005 : ℝ) := by nlinarith
  have hDryLower : (5.745 : ℝ) ≤ dry := by nlinarith
  have hDryUpper : dry ≤ (5.755 : ℝ) := by nlinarith
  have hInitialPos : 0 < initial := by nlinarith
  constructor
  · apply (le_div_iff₀ hInitialPos).2
    nlinarith
  · apply (div_le_iff₀ hInitialPos).2
    nlinarith

theorem dryFraction_sixteen_in_measurement_bounds :
    (1149 : ℝ) / 2001 ≤ dryFraction 16 ∧
      dryFraction 16 ≤ (1151 : ℝ) / 1999 := by
  norm_num [dryFraction, Formula.molarMass, anhydrousStone, hydratedStone,
    Formula.add, Formula.scale, water]

/-- No search bound is used: integrality plus the measured interval forces the
hydration number to lie strictly between 15 and 17. -/
theorem hydration_number_unique
    {waters : ℕ}
    (hRatio : (1149 : ℝ) / 2001 ≤ dryFraction waters ∧
      dryFraction waters ≤ (1151 : ℝ) / 1999) :
    waters = 16 := by
  have hDenom : 0 < (390.08 : ℝ) + (waters : ℝ) * 18.016 := by positivity
  rw [dryFraction, molarMass_anhydrousStone,
    molarMass_hydratedStone] at hRatio
  have hUpperWaters := (le_div_iff₀ hDenom).1 hRatio.1
  have hLowerWaters := (div_le_iff₀ hDenom).1 hRatio.2
  have hAtLeast : 16 ≤ waters := by
    by_contra h
    have hw : waters ≤ 15 := by omega
    have hwReal : (waters : ℝ) ≤ 15 := by exact_mod_cast hw
    norm_num at hLowerWaters
    nlinarith
  have hAtMost : waters ≤ 16 := by
    by_contra h
    have hw : 17 ≤ waters := by omega
    have hwReal : (17 : ℝ) ≤ waters := by exact_mod_cast hw
    norm_num at hUpperWaters
    nlinarith
  omega

theorem displayed_dry_step_determines_sixteen_waters
    {initial dry : ℝ} {waters : ℕ}
    (hInitial : ConsistentMeasurement initial 10.00 0.01)
    (hDry : ConsistentMeasurement dry 5.75 0.01)
    (hModel : dry / initial = dryFraction waters) :
    waters = 16 := by
  apply hydration_number_unique
  simpa [hModel] using dry_ratio_bounds_from_measurements hInitial hDry

/-! ## The high-temperature residue -/

/-- The doubled complete-combustion equation avoids fractional oxygen:
`2 stone.nH2O + 15 O2 -> 2 H + 24 CO2 + 2n H2O`.
`H` is deliberately unknown in this predicate. -/
def combustionBalance (waters : ℕ) (H : Formula) : Prop :=
  Formula.add (Formula.scale 2 (hydratedStone waters))
      (Formula.scale 15 oxygen) =
    Formula.add (Formula.scale 2 H)
      (Formula.add (Formula.scale 24 carbonDioxide)
        (Formula.scale (2 * waters) water))

/-- Conservation of every element in complete combustion uniquely fixes the
unknown nonvolatile formula unit; the conclusion is not a premise. -/
theorem combustion_product_unique
    {waters : ℕ} {H : Formula}
    (hBalance : combustionBalance waters H) :
    H = alumina := by
  have hAl := congrArg Formula.al hBalance
  have hC := congrArg Formula.c hBalance
  have hH := congrArg Formula.h hBalance
  have hO := congrArg Formula.o hBalance
  have hNa := congrArg Formula.na hBalance
  have hF := congrArg Formula.f hBalance
  simp [Formula.add, Formula.scale, hydratedStone,
    anhydrousStone, oxygen, carbonDioxide, water] at hAl hC hH hO hNa hF
  apply Formula.ext <;> simp [alumina] <;> omega

theorem proposed_combustion_is_balanced : combustionBalance 16 alumina := by
  rfl

/-- The final displayed masses imply these exact ratio bounds. -/
theorem residue_ratio_bounds_from_measurements
    {initial residue : ℝ}
    (hInitial : ConsistentMeasurement initial 10.00 0.01)
    (hResidue : ConsistentMeasurement residue 1.50 0.01) :
    (299 : ℝ) / 2001 ≤ residue / initial ∧
      residue / initial ≤ (301 : ℝ) / 1999 := by
  rcases hInitial with ⟨_, hInitial⟩
  rcases hResidue with ⟨_, hResidue⟩
  rw [abs_le] at hInitial hResidue
  have hInitialLower : (9.995 : ℝ) ≤ initial := by nlinarith
  have hInitialUpper : initial ≤ (10.005 : ℝ) := by nlinarith
  have hResidueLower : (1.495 : ℝ) ≤ residue := by nlinarith
  have hResidueUpper : residue ≤ (1.505 : ℝ) := by nlinarith
  have hInitialPos : 0 < initial := by nlinarith
  constructor
  · apply (le_div_iff₀ hInitialPos).2
    nlinarith
  · apply (div_le_iff₀ hInitialPos).2
    nlinarith

theorem aluminaFraction_in_measurement_bounds :
    (299 : ℝ) / 2001 ≤ aluminaFraction ∧
      aluminaFraction ≤ (301 : ℝ) / 1999 := by
  norm_num [aluminaFraction, Formula.molarMass, alumina, hydratedStone,
    anhydrousStone, Formula.add, Formula.scale, water]

/-- The exact nominal masses, retained without intermediate rounding. -/
theorem nominal_tga_predictions :
    10 * dryFraction 16 = (60950 : ℝ) / 10599 ∧
      10 * aluminaFraction = (63725 : ℝ) / 42396 := by
  norm_num [dryFraction, aluminaFraction, Formula.molarMass, anhydrousStone,
    hydratedStone, alumina, Formula.add, Formula.scale, water]

/-- Final theorem covering both formula fields requested on answer sheet A1-5.
It uses the first TGA interval to determine hydration and the atom-balanced
open-air combustion law to determine `H`. -/
theorem icho_2026_t1_a6_formulae
    {initial dry residue : ℝ} {waters : ℕ} {H : Formula}
    (hInitial : ConsistentMeasurement initial 10.00 0.01)
    (hDry : ConsistentMeasurement dry 5.75 0.01)
    (hResidue : ConsistentMeasurement residue 1.50 0.01)
    (hDryModel : dry / initial = dryFraction waters)
    (hResidueModel : residue / initial =
      Formula.molarMass H / Formula.molarMass (hydratedStone waters))
    (hCombustion : combustionBalance waters H) :
    waters = 16 ∧ hydratedStone waters = stoneAnswer ∧
      H = compoundHAnswer ∧
      (299 : ℝ) / 2001 ≤
        Formula.molarMass H / Formula.molarMass (hydratedStone waters) ∧
      Formula.molarMass H / Formula.molarMass (hydratedStone waters) ≤
        (301 : ℝ) / 1999 := by
  have hWaters := displayed_dry_step_determines_sixteen_waters
    hInitial hDry hDryModel
  have hH := combustion_product_unique hCombustion
  have hResidueBounds := residue_ratio_bounds_from_measurements hInitial hResidue
  rw [hResidueModel] at hResidueBounds
  exact ⟨hWaters, by simp [stoneAnswer, hWaters], by simpa [compoundHAnswer] using hH,
    hResidueBounds⟩

#print axioms icho_2026_t1_a6_formulae
#print axioms hydration_number_unique
#print axioms combustion_product_unique
#print axioms aluminaFraction_in_measurement_bounds

end IChO2026Problems.T1A6
