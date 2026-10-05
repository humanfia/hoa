import Mathlib

/-!
# IChO 2026, theory problem 6.3: halogen selection

The problem applies a potential difference of `2.5 V` to electrons and asks
which of four printed C-X bond dissociation energies can be met.  For one mole
of electrons, `E = qV` becomes `E = FV`.  Since a volt-coulomb is a joule,
division by `1000` expresses the result in the same `kJ mol⁻¹` unit as the
table.

All numerical data below are exact encodings of the values printed in the
problem booklet (including its physical-constants page).  The later theorems
derive the energetic classification; no answer is included as an axiom or
input.
-/

namespace IChO2026Problems.T6A3

/-- The four candidate halogens listed in the question's C-X table. -/
inductive Halogen where
  | fluorine
  | chlorine
  | bromine
  | iodine
  deriving DecidableEq, Fintype, Repr

/-! ## Problem data and the energy conversion -/

/-- Applied voltage in volts: the printed value `2.5 V`. -/
def appliedVoltage_V : ℚ := 5 / 2

/-- Faraday constant in coulombs per mole, as printed on the constants page. -/
def faradayConstant_C_per_mol : ℚ := 96485

/-- Exact conversion factor from joules to kilojoules. -/
def joulesPerKilojoule : ℚ := 1000

/-- The printed C-X bond dissociation energies, in `kJ mol⁻¹`. -/
def bondDissociationEnergy_kJ_per_mol : Halogen → ℚ
  | .fluorine => 467
  | .chlorine => 346
  | .bromine => 290
  | .iodine => 228

/-- Molar electrical energy delivered to singly charged electrons, in
`kJ mol⁻¹`.  This is `FV / 1000`, using `1 V C = 1 J`. -/
def availableEnergy_kJ_per_mol : ℚ :=
  appliedVoltage_V * faradayConstant_C_per_mol / joulesPerKilojoule

/-- A candidate C-X bond is energetically accessible precisely when the
available molar electron energy meets or exceeds its dissociation energy. -/
def EnergeticallyAccessible (x : Halogen) : Prop :=
  bondDissociationEnergy_kJ_per_mol x ≤ availableEnergy_kJ_per_mol

instance (x : Halogen) : Decidable (EnergeticallyAccessible x) := by
  unfold EnergeticallyAccessible
  infer_instance

/-! ## Derived calculation and classification -/

/-- `2.5 × 96485 / 1000 = 241.2125 kJ mol⁻¹`, kept exactly as a rational. -/
theorem availableEnergy_exact :
    availableEnergy_kJ_per_mol = 19297 / 80 := by
  norm_num [availableEnergy_kJ_per_mol, appliedVoltage_V,
    faradayConstant_C_per_mol, joulesPerKilojoule]

theorem fluorine_not_accessible :
    ¬ EnergeticallyAccessible .fluorine := by
  norm_num [EnergeticallyAccessible, bondDissociationEnergy_kJ_per_mol,
    availableEnergy_kJ_per_mol, appliedVoltage_V,
    faradayConstant_C_per_mol, joulesPerKilojoule]

theorem chlorine_not_accessible :
    ¬ EnergeticallyAccessible .chlorine := by
  norm_num [EnergeticallyAccessible, bondDissociationEnergy_kJ_per_mol,
    availableEnergy_kJ_per_mol, appliedVoltage_V,
    faradayConstant_C_per_mol, joulesPerKilojoule]

theorem bromine_not_accessible :
    ¬ EnergeticallyAccessible .bromine := by
  norm_num [EnergeticallyAccessible, bondDissociationEnergy_kJ_per_mol,
    availableEnergy_kJ_per_mol, appliedVoltage_V,
    faradayConstant_C_per_mol, joulesPerKilojoule]

theorem iodine_accessible :
    EnergeticallyAccessible .iodine := by
  norm_num [EnergeticallyAccessible, bondDissociationEnergy_kJ_per_mol,
    availableEnergy_kJ_per_mol, appliedVoltage_V,
    faradayConstant_C_per_mol, joulesPerKilojoule]

/-- Complete classification of the four candidates, not just a proof that
iodine happens to work. -/
theorem energeticallyAccessible_iff (x : Halogen) :
    EnergeticallyAccessible x ↔ x = .iodine := by
  cases x <;>
    norm_num [EnergeticallyAccessible, bondDissociationEnergy_kJ_per_mol,
      availableEnergy_kJ_per_mol, appliedVoltage_V,
      faradayConstant_C_per_mol, joulesPerKilojoule] <;>
    decide

/-- The finite set requested by the problem. -/
def possibleHalogens : Finset Halogen :=
  Finset.univ.filter EnergeticallyAccessible

/-- Requested output: iodine is the unique possible halogen. -/
theorem possibleHalogens_eq_singleton :
    possibleHalogens = {.iodine} := by
  ext x
  simp only [possibleHalogens, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, energeticallyAccessible_iff]

#print axioms availableEnergy_exact
#print axioms fluorine_not_accessible
#print axioms chlorine_not_accessible
#print axioms bromine_not_accessible
#print axioms iodine_accessible
#print axioms energeticallyAccessible_iff
#print axioms possibleHalogens_eq_singleton

end IChO2026Problems.T6A3
