import Mathlib

/-!
# IChO 2026, Theory Problem 8.4 (target `icho_2026_t8_a4`)

Formalization of the seven iron cycle intermediates **9–15** of the
photocatalytic CO₂ reduction by catalyst **1** on crystalline C₃N₄.

## Sources used (problem-only materials)

* Printed page 2 (`T8_page-2.png`, `theory_problem.pdf` p. 73): the catalytic
  cycle with edge labels `+2H₂O −2Cl⁻` (1→9), `+hν +1e⁻ −H₂O` (9→10),
  `−H₂O +CO₂` (10→11), `+hν +1e⁻ +H⁺` (11→12), `+H₂O` (12→13),
  `+H⁺ −H₂O` (13→14), `−CO` (14→15), `+H₂O` (15→9).
* Printed page 1: cartoon of ligand **8** shows four nitrogen donors (a linear
  tetradentate quaterpyridine-type N₄ ligand with a benzoic-acid anchor), and
  the synthesis 8 + FeCl₂ → 1.
* Question 8.5 (same page) stipulates `M_cat = 557.21 g mol⁻¹`, matching
  `[Fe(C₂₇H₁₈N₄O₂)Cl₂]` exactly (see `mcat_consistent`), confirming the
  tetradentate formula C₂₇H₁₈N₄O₂ for ligand 8.
* Blank answer sheet (A8-3/A8-4, `theory_problem.pdf` pp. 79–80) pre-prints:
  11: OS = +3, CN = 6;  12: CN = 5;  13: OS = +2;  15: VE = 16.

## Electron-counting conventions (trusted general chemistry law)

Ionic model: each coordinated donor atom supplies a 2-electron σ bond,
  VE = (group number of Fe − OS) + 2·CN,  group(Fe) = 8,
  Z  = OS + Σ (formal ligand charges).
Ligand formal charges: 8 (neutral N₄ donor) 0; H₂O 0; Cl⁻ −1; CO 0;
C-bound carboxyl −C(=O)OH −1; η²-C,O bound CO₂²⁻ (metallacarboxylate) −2.
Oxidative addition of CO₂ to Fe(I) is described as Fe(III)–CO₂²⁻, which is why
the answer sheet prints OS = +3 for 11.
-/

namespace IChO2026T8A4

/-- Group number of iron (valence electrons of a neutral Fe atom). -/
def groupFe : ℤ := 8

/-- Ionic electron-counting rule: VE = (group − OS) + 2·CN. -/
def veCount (os cn : ℤ) : ℤ := (groupFe - os) + 2 * cn

/-- A coordinated ligand: formal charge, number of donor atoms bound to Fe,
the identity of those donor atoms (connectivity), and internal bond orders
(atom1, atom2, order). -/
structure Ligand where
  name : String
  charge : ℤ
  sites : ℕ
  donors : List String
  bonds : List (String × String × ℕ)
  hDonors : donors.length = sites

/-- Elemental composition used for the stoichiometric cycle check. -/
structure Formula where
  C : ℤ
  H : ℤ
  N : ℤ
  O : ℤ
  Cl : ℤ
  Fe : ℤ
  deriving DecidableEq, Repr

def Formula.add (a b : Formula) : Formula :=
  ⟨a.C + b.C, a.H + b.H, a.N + b.N, a.O + b.O, a.Cl + b.Cl, a.Fe + b.Fe⟩

def Formula.sub (a b : Formula) : Formula :=
  ⟨a.C - b.C, a.H - b.H, a.N - b.N, a.O - b.O, a.Cl - b.Cl, a.Fe - b.Fe⟩

instance : Add Formula where add := Formula.add
instance : Sub Formula where sub := Formula.sub

/-- Atomic masses (conventional standard values) used only for the
M_cat grounding check. -/
def mC : ℝ := 12.011
def mH : ℝ := 1.008
def mN : ℝ := 14.007
def mO : ℝ := 15.999
def mCl : ℝ := 35.45
def mFe : ℝ := 55.845

/-! ### Fragment formulas -/

def lig8Formula : Formula := ⟨27, 18, 4, 2, 0, 0⟩
def h2oF : Formula := ⟨0, 2, 0, 1, 0, 0⟩
def coF : Formula := ⟨1, 0, 0, 1, 0, 0⟩
def co2F : Formula := ⟨1, 0, 0, 2, 0, 0⟩
def clF : Formula := ⟨0, 0, 0, 0, 1, 0⟩
def hF : Formula := ⟨0, 1, 0, 0, 0, 0⟩
def feF : Formula := ⟨0, 0, 0, 0, 0, 1⟩
/-- Formula of the C-bound carboxyl ligand −C(=O)OH, i.e. CO₂ + H. -/
def coohF : Formula := co2F + hF

/-! ### Ligands of the cycle -/

/-- Ligand 8: tetradentate, linear N₄ (quaterpyridine with a benzoic-acid
anchor), neutral.  Connectivity: four pyridinic N donors in a chain. -/
def lig8 : Ligand :=
  ⟨"8 (tetradentate N4 quaterpyridine, benzoic-acid anchor)", 0, 4,
   ["N", "N", "N", "N"], [], rfl⟩

/-- Coordinated water. -/
def h2o : Ligand :=
  ⟨"H2O", 0, 1, ["O"], [("O", "H", 1), ("O", "H", 1)], rfl⟩

/-- Chloride (present only in catalyst 1). -/
def clL : Ligand := ⟨"Cl", -1, 1, ["Cl"], [], rfl⟩

/-- Carbon monoxide, bound through C with a C≡O triple bond. -/
def coL : Ligand := ⟨"CO", 0, 1, ["C"], [("C", "O", 3)], rfl⟩

/-- C-bound carboxyl (hydroxycarbonyl) ligand −C(=O)OH: η¹ through carbon,
C=O double bond retained, one C–O and one O–H single bond; charge −1. -/
def coohL : Ligand :=
  ⟨"C(=O)OH, eta1-C bound", -1, 1, ["C"],
   [("C", "O", 2), ("C", "O", 1), ("O", "H", 1)], rfl⟩

/-- Side-on bound carbon dioxide, η²-C,O metallacarboxylate / CO₂²⁻: two donor
atoms (C and O), one C=O double bond and one C–O single bond; charge −2. -/
def co2h2 : Ligand :=
  ⟨"CO2, eta2-C,O bound (metallacarboxylate)", -2, 2, ["C", "O"],
   [("C", "O", 2), ("C", "O", 1)], rfl⟩

/-! ### Complexes -/

/-- An iron complex: Fe oxidation state plus coordinated ligands, each paired
with its elemental formula. -/
structure FeComplex where
  os : ℤ
  ligands : List (Ligand × Formula)

/-- Coordination number: total number of donor atoms bound to Fe. -/
def FeComplex.cn (c : FeComplex) : ℤ :=
  (c.ligands.map fun p => (p.1.sites : ℤ)).sum

/-- Total complex charge: Fe oxidation state plus ligand formal charges. -/
def FeComplex.z (c : FeComplex) : ℤ :=
  c.os + (c.ligands.map fun p => p.1.charge).sum

/-- Valence electron count at Fe, ionic 2-electron-donor model. -/
def FeComplex.ve (c : FeComplex) : ℤ := veCount c.os c.cn

/-- Elemental formula of the whole complex (Fe included). -/
def FeComplex.formula (c : FeComplex) : Formula :=
  c.ligands.foldl (fun acc p => acc.add p.2) feF

/-- The number of N donors of ligand 8 in the complex (connectivity:
ligand 8 stays fully bound through the whole cycle). -/
def FeComplex.nDonorsOf8 (c : FeComplex) : ℕ :=
  c.ligands.foldl
    (fun acc p => acc + (if p.1.name = lig8.name then p.1.sites else 0)) 0

/-! #### Catalyst 1 and intermediates 9–15 -/

/-- Catalyst 1: [Fe(8)Cl₂], from 8 + FeCl₂ → 1 on printed page 1. -/
def cat1 : FeComplex := ⟨2, [(lig8, lig8Formula), (clL, clF), (clL, clF)]⟩

/-- **9**: [Fe(8)(H₂O)₂]²⁺  (1 + 2H₂O − 2Cl⁻). -/
def c9 : FeComplex :=
  ⟨2, [(lig8, lig8Formula), (h2o, h2oF), (h2o, h2oF)]⟩

/-- **10**: [Fe(8)(H₂O)]⁺  (9 + hν + 1e⁻ − H₂O): Fe(I), d⁷. -/
def c10 : FeComplex :=
  ⟨1, [(lig8, lig8Formula), (h2o, h2oF)]⟩

/-- **11**: [Fe(8)(η²-CO₂)]⁺  (10 − H₂O + CO₂): oxidative addition of CO₂ to
Fe(I) gives Fe(III)–CO₂²⁻, CN 6 (4 N of 8 + η²-C,O), matching the printed
OS = +3, CN = 6 on the answer sheet. -/
def c11 : FeComplex :=
  ⟨3, [(lig8, lig8Formula), (co2h2, co2F)]⟩

/-- **12**: [Fe(8)(C(=O)OH)]⁺  (11 + hν + 1e⁻ + H⁺): reduction of Fe(III) back
to Fe(II) and protonation at the distal O opens η²-CO₂ to the η¹-C carboxyl;
CN 5, matching the printed CN = 5. -/
def c12 : FeComplex :=
  ⟨2, [(lig8, lig8Formula), (coohL, coohF)]⟩

/-- **13**: [Fe(8)(C(=O)OH)(H₂O)]⁺  (12 + H₂O): the C-bound carboxyl plus an
aqua ligand; OS = +2, matching the printed value. -/
def c13 : FeComplex :=
  ⟨2, [(lig8, lig8Formula), (coohL, coohF), (h2o, h2oF)]⟩

/-- **14**: [Fe(8)(CO)(H₂O)]²⁺  (13 + H⁺ − H₂O): protonation of the carboxyl OH
cleaves the C–O bond releasing water; the iron carbonyl is retained. -/
def c14 : FeComplex :=
  ⟨2, [(lig8, lig8Formula), (coL, coF), (h2o, h2oF)]⟩

/-- **15**: [Fe(8)(H₂O)]²⁺  (14 − CO): the product CO has dissociated, leaving
the monoaqua Fe(II) complex; VE = 16, matching the printed value. -/
def c15 : FeComplex :=
  ⟨2, [(lig8, lig8Formula), (h2o, h2oF)]⟩

/-! ## Requested outputs: total charge Z of complexes 9–15 -/

theorem complex_9_total_charge : c9.z = 2 := rfl
theorem complex_10_total_charge : c10.z = 1 := rfl
theorem complex_11_total_charge : c11.z = 1 := rfl
theorem complex_12_total_charge : c12.z = 1 := rfl
theorem complex_13_total_charge : c13.z = 1 := rfl
theorem complex_14_total_charge : c14.z = 2 := rfl
theorem complex_15_total_charge : c15.z = 2 := rfl

/-! ## Requested outputs: oxidation state OS of Fe in 9–15 -/

theorem complex_9_oxidation_state : c9.os = 2 := rfl
theorem complex_10_oxidation_state : c10.os = 1 := rfl
theorem complex_11_oxidation_state : c11.os = 3 := rfl
theorem complex_12_oxidation_state : c12.os = 2 := rfl
theorem complex_13_oxidation_state : c13.os = 2 := rfl
theorem complex_14_oxidation_state : c14.os = 2 := rfl
theorem complex_15_oxidation_state : c15.os = 2 := rfl

/-! ## Requested outputs: coordination number CN of Fe in 9–15 -/

theorem complex_9_coordination_number : c9.cn = 6 := rfl
theorem complex_10_coordination_number : c10.cn = 5 := rfl
theorem complex_11_coordination_number : c11.cn = 6 := rfl
theorem complex_12_coordination_number : c12.cn = 5 := rfl
theorem complex_13_coordination_number : c13.cn = 6 := rfl
theorem complex_14_coordination_number : c14.cn = 6 := rfl
theorem complex_15_coordination_number : c15.cn = 5 := rfl

/-! ## Requested outputs: valence electron count VE of Fe in 9–15 -/

theorem complex_9_valence_electrons : c9.ve = 18 := rfl
theorem complex_10_valence_electrons : c10.ve = 17 := rfl
theorem complex_11_valence_electrons : c11.ve = 17 := rfl
theorem complex_12_valence_electrons : c12.ve = 16 := rfl
theorem complex_13_valence_electrons : c13.ve = 18 := rfl
theorem complex_14_valence_electrons : c14.ve = 18 := rfl
theorem complex_15_valence_electrons : c15.ve = 16 := rfl

/-! ## Consistency with the information pre-printed on the answer sheet -/

/-- Sheet anchor: 11 has OS = +3 and CN = 6. -/
theorem sheet_anchor_11 : c11.os = 3 ∧ c11.cn = 6 := ⟨rfl, rfl⟩

/-- Sheet anchor: 12 has CN = 5. -/
theorem sheet_anchor_12 : c12.cn = 5 := rfl

/-- Sheet anchor: 13 has OS = +2. -/
theorem sheet_anchor_13 : c13.os = 2 := rfl

/-- Sheet anchor: 15 has VE = 16. -/
theorem sheet_anchor_15 : c15.ve = 16 := rfl

/-! ## Ligand-8 connectivity invariant -/

/-- Ligand 8 keeps all four N donors bound in 1 and in every intermediate
9–15, as implied by the problem instruction to reuse its cartoon throughout. -/
theorem ligand8_stays_bound :
    cat1.nDonorsOf8 = 4 ∧ c9.nDonorsOf8 = 4 ∧ c10.nDonorsOf8 = 4 ∧
    c11.nDonorsOf8 = 4 ∧ c12.nDonorsOf8 = 4 ∧ c13.nDonorsOf8 = 4 ∧
    c14.nDonorsOf8 = 4 ∧ c15.nDonorsOf8 = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Step-by-step conservation laws from the printed edge labels -/

/-- 9 → 10: `+hν +1e⁻ −H₂O`.  The added electron changes OS and Z, not atoms;
one water is lost. -/
theorem step_9_10 : c10.formula = c9.formula - h2oF := by
  native_decide

theorem step_9_10_redox : c10.os = c9.os - 1 ∧ c10.z = c9.z - 1 := ⟨rfl, rfl⟩

/-- 10 → 11: `−H₂O +CO₂`. -/
theorem step_10_11 : c11.formula = (c10.formula - h2oF) + co2F := by
  native_decide

theorem step_10_11_oxidative_addition :
    c11.os = c10.os + 2 ∧ c11.z = c10.z := ⟨rfl, rfl⟩

/-- 11 → 12: `+hν +1e⁻ +H⁺`.  One H atom appears in the formula. -/
theorem step_11_12 : c12.formula = c11.formula + hF := by
  native_decide

theorem step_11_12_pcet : c12.os = c11.os - 1 ∧ c12.z = c11.z := ⟨rfl, rfl⟩

/-- 12 → 13: `+H₂O`. -/
theorem step_12_13 : c13.formula = c12.formula + h2oF := by
  native_decide

theorem step_12_13_neutral : c13.os = c12.os ∧ c13.z = c12.z := ⟨rfl, rfl⟩

/-- 13 → 14: `+H⁺ −H₂O`: protonative C–O cleavage releases a water. -/
theorem step_13_14 : c14.formula = (c13.formula + hF) - h2oF := by
  native_decide

theorem step_13_14_charge : c14.os = c13.os ∧ c14.z = c13.z + 1 := ⟨rfl, rfl⟩

/-- 14 → 15: `−CO`, loss of the product CO. -/
theorem step_14_15 : c15.formula = c14.formula - coF := by
  native_decide

theorem step_14_15_loss :
    c15.os = c14.os ∧ c15.z = c14.z ∧ c15.cn = c14.cn - 1 ∧ c15.ve = c14.ve - 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- 15 → 9: `+H₂O` closes the cycle. -/
theorem step_15_9 : c9.formula = c15.formula + h2oF := by
  native_decide

/-! ## Net catalytic stoichiometry -/

/-- Atom balance of the net half reaction: CO₂ + 2H⁺ → CO + H₂O. -/
theorem net_half_reaction_atoms : co2F + hF + hF = coF + h2oF := by
  native_decide

/-- Left-hand side of the full-cycle bookkeeping: 9 with all eight printed
edge transformations applied in sequence. -/
def cycleApplied : Formula :=
  (((((((c9.formula - h2oF) - h2oF) + co2F) + hF) + h2oF)
      + (hF - h2oF)) - coF) + h2oF

/-- Right-hand side: 9 with the net half reaction CO₂ + 2H⁺ → CO + H₂O. -/
def cycleNet : Formula :=
  ((c9.formula + co2F) + (hF + hF)) - (coF + h2oF)

/-- A full turnover is a true catalytic cycle: the complex is regenerated. -/
theorem cycle_net_stoichiometry : cycleApplied = cycleNet := by
  native_decide

theorem two_electron_cycle :
    c10.os = c9.os - 1 ∧ c11.os = c10.os + 2 ∧ c12.os = c11.os - 1 ∧
    c13.os = c12.os ∧ c14.os = c13.os ∧ c15.os = c14.os ∧ c9.os = c15.os :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Grounding of the ligand formula via the stipulated M_cat -/

def mcatCalc : ℝ :=
  27 * mC + 18 * mH + 4 * mN + 2 * mO + 1 * mFe + 2 * mCl

theorem mcat_consistent : |mcatCalc - 557.21| ≤ 0.005 := by
  rw [abs_le]
  constructor <;> norm_num [mcatCalc, mC, mH, mN, mO, mFe, mCl]

end IChO2026T8A4
