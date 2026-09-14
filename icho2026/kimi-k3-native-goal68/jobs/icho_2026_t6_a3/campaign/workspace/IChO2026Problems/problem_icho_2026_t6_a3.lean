import Mathlib

/-!
# IChO 2026 T6-A3 — Halogen choice for C18 synthesis (classification)

## Problem statement (official, Q6-2, "6.3", 2.0 pt)

"The voltages applied during the AFM-mediated synthesis of C𝑛 may vary.
Using the given C–X bond energies, **choose** the possible halogen(s) in the
halogenated reagent for C18 synthesis via a retro-Bergman reaction with a
voltage of 2.5 V acting on the electrons."

    Bond (C–X) : C–F  C–Cl  C–Br  C–I
    BDE kJ mol⁻¹: 467  346   290   228

The constant sheet (G1-3) supplies: electron charge `e = 1.602 × 10⁻¹⁹ C`,
`1 eV = 1.602 × 10⁻¹⁹ J`, and Avogadro constant `N_A = 6.022 × 10²³ mol⁻¹`.

## Physical reasoning

An electron accelerated through a potential difference of `V = 2.5 V` acquires
kinetic energy `e·V = 2.5 eV`. The retro-Bergman ring-opening of the
halogenated precursor requires cleavage of the C–X bond(s); a single electron
can drive the cleavage of a C–X bond only if its kinetic energy is at least
the C–X bond dissociation energy (energy conservation / trusted general law).
Hence a halogen X is possible iff

    BDE(C–X) ≤ e·V·N_A  (per-mole form).

Here `e·V·N_A = 2.5 × 1.602 × 10⁻¹⁹ × 6.022 × 10²³ J mol⁻¹ = 241.1811 kJ mol⁻¹`,
so only C–I (228 kJ mol⁻¹) lies at or below the available electron energy;
C–Br (290), C–Cl (346) and C–F (467) do not.

## Answer boxed on the official answer sheet (A6-2): `X = I` (iodine)

Problem inputs and derived quantities are separated below: the table values,
the voltage and the physical constants are problem inputs; the per-mole
electron energy and the possibility criterion are derived.
-/

namespace IChO2026T6A3

/-- The four candidate halogens appearing in the problem table. -/
inductive Halogen where
  | F | Cl | Br | I
  deriving DecidableEq, Repr

/-! ### Problem inputs (data printed in the question and constant sheet) -/

/-- Bond dissociation energies of the C–X bonds as printed in the question
table, in kJ mol⁻¹. -/
def bdeKJ : Halogen → ℝ
  | .F  => 467
  | .Cl => 346
  | .Br => 290
  | .I  => 228

/-- Applied voltage acting on the electrons, in volts (problem input). -/
def voltageV : ℝ := 2.5

/-- Elementary charge, C (constant sheet: e = 1.602 × 10⁻¹⁹ C). -/
def electronChargeC : ℝ := 1.602e-19

/-- Avogadro constant, mol⁻¹ (constant sheet: N_A = 6.022 × 10²³ mol⁻¹). -/
def avogadro : ℝ := 6.022e23

/-! ### Derived quantities -/

/-- Kinetic energy delivered by one electron accelerated through `voltageV`,
expressed per mole of electrons in kJ mol⁻¹: `V·e·N_A / 1000`. -/
noncomputable def electronEnergyKJ : ℝ :=
  voltageV * electronChargeC * avogadro / 1000

/-- The per-mole kinetic energy of the 2.5 V electrons is exactly
241.1811 kJ mol⁻¹ (using the constants as printed, e and N_A to 4 s.f.). -/
theorem electronEnergyKJ_value : electronEnergyKJ = 241.1811 := by
  unfold electronEnergyKJ voltageV electronChargeC avogadro
  norm_num

/-- The electron energy lies strictly between the C–I and C–Br bond
dissociation energies. -/
theorem electronEnergyKJ_bounds : 228 ≤ electronEnergyKJ ∧ electronEnergyKJ < 290 := by
  rw [electronEnergyKJ_value]
  norm_num

/-! ### Possibility criterion and classification -/

/-- A halogen is a possible substituent in the halogenated reagent iff the
2.5 V electron carries at least the C–X bond dissociation energy (per mole). -/
def Possible (X : Halogen) : Prop := bdeKJ X ≤ electronEnergyKJ

/-- Iodine is possible: BDE(C–I) = 228 ≤ 241.1811 kJ mol⁻¹. -/
theorem possible_I : Possible .I := by
  unfold Possible bdeKJ
  rw [electronEnergyKJ_value]
  norm_num

/-- Fluorine is not possible: BDE(C–F) = 467 > 241.1811 kJ mol⁻¹. -/
theorem not_possible_F : ¬ Possible .F := by
  unfold Possible bdeKJ
  rw [electronEnergyKJ_value]
  norm_num

/-- Chlorine is not possible: BDE(C–Cl) = 346 > 241.1811 kJ mol⁻¹. -/
theorem not_possible_Cl : ¬ Possible .Cl := by
  unfold Possible bdeKJ
  rw [electronEnergyKJ_value]
  norm_num

/-- Bromine is not possible: BDE(C–Br) = 290 > 241.1811 kJ mol⁻¹. -/
theorem not_possible_Br : ¬ Possible .Br := by
  unfold Possible bdeKJ
  rw [electronEnergyKJ_value]
  norm_num

/-- **Main classification theorem.** Exactly one halogen passes the energy
criterion. A halogen X is possible in the halogenated reagent for C18
synthesis via retro-Bergman at 2.5 V if and only if X = iodine. -/
theorem possible_halogens (X : Halogen) : Possible X ↔ X = .I := by
  cases X with
  | F =>
      constructor
      · intro h; exact absurd h not_possible_F
      · intro h; cases h
  | Cl =>
      constructor
      · intro h; exact absurd h not_possible_Cl
      · intro h; cases h
  | Br =>
      constructor
      · intro h; exact absurd h not_possible_Br
      · intro h; cases h
  | I =>
      constructor
      · intro _; rfl
      · intro _; exact possible_I

/-- The possible-halogen set, given as the answer on the official answer
sheet (`X = _______`), is the singleton `{I}`. -/
theorem possible_set : {X : Halogen | Possible X} = {.I} := by
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact possible_halogens X

--+ Axioms used: standard Lean logical axioms only (`propext`,
--  `Classical.choice`, `Quot.sound`); no custom axioms.
#print axioms possible_halogens
#print axioms possible_set

end IChO2026T6A3
