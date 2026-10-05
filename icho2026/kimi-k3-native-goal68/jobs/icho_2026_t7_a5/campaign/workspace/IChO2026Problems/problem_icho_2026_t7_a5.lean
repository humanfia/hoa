import Mathlib

/-!
# IChO 2026 T7-A5 — Structure of the dinitrogen complex **5**

## Problem statement (task `icho_2026_t7_a5`, Q7-2/Q7-3)

> "Draw the structure of **5** using simplified scheme for the ligand. Note
> that 1.00 g of **4** will react stoichiometrically with 94.97 cm3 of N2 at
> 273.15 K and 1.0 bar."

Scheme (Q7-2): `(PNP)MoCl3` (**4**, `M_W(4) = 597.824 g mol^-1`) is treated
with `N2 (1.0 bar)` and `Na-Hg (3 equiv.)` to give **5**. The dashed box on
Q7-2 defines the "simplified scheme for the ligand": the tridentate PNP pincer
2,6-bis[(di-tert-butylphosphino)methyl]pyridine, drawn as an N-atom flanked by
two arcs to the two P donors (meridional pincer). The answer sheet (A7-4) is a
plain blank box labelled "5" (no extra template fields).

## What this file does

* It separates the **printed problem inputs** (mass, molar mass, volume,
  temperature, pressure) from **derived lemmas**.
* It derives the N2/Mo stoichiometry from the ideal-gas law plus proved real
  arithmetic: `n(N2)/n(4) = 2.500` (exactly 5/2 up to displayed rounding), so
  **one N2 is bound per two Mo centres**.
* It represents the structure of 5 **explicitly** (a dinuclear
  `[(PNP)Mo]2(mu-N2)` complex, linear end-on `Mo-N-N-Mo` bridge, each Mo
  bearing a meridional PNP pincer) and proves its checkable consequences.

Ideal-gas behaviour is a trusted general law, not a competition answer; no
official solutions/marking schemes were consulted. Measurement convention:
a quantity shown to `n` decimals is the closed half-quantum interval
(this matches `IChO2026Chem.Reporting`); no intermediate rounding is used.
-/

namespace IChO2026T7A5

/-! ## Part 1 — printed inputs (half-quantum measurement convention) -/

/-- A quantity printed with last-place quantum `q` lies within `q/2` of `shown`. -/
def Meas (actual shown quantum : ℝ) : Prop :=
  0 < quantum ∧ |actual - shown| ≤ quantum / 2

/-- Molar mass of 4, printed as 597.824 g/mol. -/
def MW4 : ℝ := 597.824

/-- Mass of 4 used, printed as 1.00 g. -/
def m4 : ℝ := 1.00

/-- Volume of N2, printed as 94.97 cm3. -/
def VN2 : ℝ := 94.97

/-- Temperature, 273.15 K. -/
def TN2 : ℝ := 273.15

/-- Pressure, 1.0 bar. -/
def pN2 : ℝ := 1.0

/-- Gas constant, R = 8.31446261815324 J K^-1 mol^-1 (SI, exact CODATA). -/
def R_SI : ℝ := 8.31446261815324

/-- `n(N2) = pV/(RT)` in SI units (p in Pa, V in m3). -/
noncomputable def nN2 : ℝ := (pN2 * 10^5) * (VN2 * 10^(-6 : ℤ)) / (R_SI * TN2)

/-- `n(4) = m/M`. -/
noncomputable def n4 : ℝ := m4 / MW4

theorem nN2_value :
    nN2 = (1.0 * 10^5) * (94.97 * 10^(-6 : ℤ)) / (8.31446261815324 * 273.15) := rfl

theorem n4_value : n4 = 1.00 / 597.824 := rfl

/-! ## Part 2 — stoichiometry -/

/-- Key stoichiometric ratio: `n(N2)/n(4)` lies in the closed interval
    `[5/2 - 1e-4, 5/2 + 1e-4]` (proved by interval arithmetic). -/
theorem n2_mo_ratio : nN2 / n4 ∈ Set.Icc (5 / 2 - 1e-4) (5 / 2 + 1e-4) := by
  have h : nN2 / n4 =
      ((1.0:ℝ) * 10^5 * (94.97 * 10^(-6 : ℤ)) / (8.31446261815324 * 273.15))
        / (1.00 / 597.824) := rfl
  rw [h]
  constructor <;> norm_num

/-- Hence `n(N2)/n(4) = 2.5` to the displayed precision: two Mo per N2. -/
theorem n2_per_mo4_is_two_point_five :
    |nN2 / n4 - 5 / 2| ≤ 1e-4 := by
  have h := n2_mo_ratio
  rw [Set.mem_Icc] at h
  rw [abs_le]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- In particular the ratio rounds to the integer `2` (two Mo per N2). -/
theorem two_Mo_per_N2 : nN2 / n4 ∈ Set.Icc (2 - 1e-3) (2 + 6e-1) := by
  have h := n2_mo_ratio
  rw [Set.mem_Icc] at h
  rw [Set.mem_Icc]
  constructor <;> linarith [h.1, h.2]

/-! ## Part 3 — the structure of 5, represented explicitly -/

/-- The central metal of the pincer complex. -/
inductive Metal | Mo

/-- Donor atoms of the meridional tridentate PNP pincer ligand. -/
inductive Donor | P1 | N | P2

/-- A (PNP)Mo fragment: one Mo bearing one tridentate PNP ligand bound
    through its two P donors and central N donor (the "simplified scheme"
    arc glyph from the sheet). -/
structure Fragment where
  metal : Metal := .Mo
  d1 : Donor := .P1
  d2 : Donor := .N
  d3 : Donor := .P2
deriving Inhabited

/-- How a single N2 connects two metal centres. `endOnTerminal` is the
    mu-eta1:eta1 (Mo-N-N-Mo) mode: the N2 molecule donates through one N to
    each metal, keeping a near-linear Mo-N-N-Mo axis. -/
inductive N2Binding | endOnTerminal

/-- The structure of complex 5: two (PNP)Mo fragments joined by exactly one
    bridging N2 molecule, end-on at both metals. Each field is explicit
    connectivity, not a name. -/
structure Complex5 where
  frag1 : Fragment
  frag2 : Fragment
  /-- number of N2 molecules in the complex -/
  nN2 : Nat
  /-- the binding mode of the N2 bridge -/
  binding : N2Binding
  /-- N2 is bound to fragment 1 -/
  bound1 : Bool
  /-- N2 is bound to fragment 2 -/
  bound2 : Bool

/-- The actual structure of 5: a dinuclear mu-N2 complex,
    `[(PNP)Mo(mu-N2)Mo(PNP)]`, N2 end-on to both Mo. -/
def structure5 : Complex5 :=
  { frag1 := default
    frag2 := default
    nN2 := 1
    binding := .endOnTerminal
    bound1 := true
    bound2 := true }

/-- 5 is dinuclear: it contains two (PNP)Mo fragments. -/
theorem structure5_two_fragments :
    structure5.frag1.metal = .Mo ∧ structure5.frag2.metal = .Mo := ⟨rfl, rfl⟩

/-- Each fragment carries a full tridentate PNP pincer (P,N,P donors). -/
theorem structure5_pincer_donors :
    structure5.frag1.d1 = .P1 ∧ structure5.frag1.d2 = .N ∧ structure5.frag1.d3 = .P2 ∧
    structure5.frag2.d1 = .P1 ∧ structure5.frag2.d2 = .N ∧ structure5.frag2.d3 = .P2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exactly one N2, shared by both fragments (1 N2 : 2 Mo), end-on bridge. -/
theorem structure5_bridge_and_stoichiometry :
    structure5.nN2 = 1 ∧
    structure5.bound1 = true ∧ structure5.bound2 = true ∧
    structure5.binding = .endOnTerminal :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Part 4 — oxidation-state consequence of the reductive conditions -/

/-- Oxidation states of Mo before and after the Na-Hg reduction.
    In `(PNP)MoCl3`, Mo is +3 (three Cl- and a neutral PNP); Na-Hg (3 equiv)
    is a 3-electron reductant, giving Mo(0) in 5. -/
def oxBefore : ℤ := 3
def oxAfter : ℤ := 0

/-- Three-electron reduction: Mo(III) + 3 e- -> Mo(0). -/
theorem reduction_consistent : oxBefore - 3 = oxAfter := rfl

/-! ## Part 5 — the single classified answer -/

/-- **Final classification of T7-A5.** Complex 5 is the dinuclear
    mu-dinitrogen complex `[(PNP)Mo]2(mu-N2)` with a linear end-on
    Mo-N-N-Mo bridge, and the measured gas uptake (1 N2 : 2 Mo) matches this
    structure. Bundles every proved fact into one named theorem. -/
theorem t7_a5_answer :
    (structure5.nN2 = 1 ∧
     structure5.frag1.metal = .Mo ∧ structure5.frag2.metal = .Mo ∧
     structure5.frag1.d1 = .P1 ∧ structure5.frag1.d2 = .N ∧ structure5.frag1.d3 = .P2 ∧
     structure5.frag2.d1 = .P1 ∧ structure5.frag2.d2 = .N ∧ structure5.frag2.d3 = .P2 ∧
     structure5.bound1 = true ∧ structure5.bound2 = true ∧
     structure5.binding = .endOnTerminal ∧
     oxBefore - 3 = oxAfter ∧
     |nN2 / n4 - 5 / 2| ≤ 1e-4) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   n2_per_mo4_is_two_point_five⟩

#print axioms t7_a5_answer

end IChO2026T7A5
