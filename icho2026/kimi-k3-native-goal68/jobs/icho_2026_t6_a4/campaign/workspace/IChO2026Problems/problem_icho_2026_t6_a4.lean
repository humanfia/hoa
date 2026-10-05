import Mathlib

/-!
# IChO 2026, Theory Problem T6, Subquestion 6.4 («Carbon Nanorings»)

Mass-spectrometric identification of the four intense peaks in the
positive-mode ESI mass spectrum of the 2025 cyclo[48]carbon catenane.

## Problem inputs (source-grounded)

* **T6, Q6-2**: the sample is the catenane of *cyclo[48]carbon*
  (`C₄₈`, i.e. a monocyclic all-carbon ring of 48 carbon atoms) with
  macrocycle **E**, whose molecular formula is printed below its structure,
  `C₄₀H₃₄N₂O₃`.  Characterisation was by **electrospray mass spectrometry
  in positive mode**.
* **6.4**: four intense peaks at `m/z` 591, 783, 879, 1174; *use integer
  atomic masses; assume no fragmentation happened*.
* **Student answer sheet A6-2 (6.4)**: the ion corresponding to `m/z = 591`
  is given as an example: `[E + H]⁺`.  This anchors the two operative
  conventions: ionisation is by proton attachment, and integer atomic masses
  give `M(E) = 40·12 + 34·1 + 2·14 + 3·16 = 590`, since
  `590 + 1 = 591`.  It also establishes the requested answer *format*: an
  ion written as a small non-covalent aggregate of `E` and the `C₄₈`
  cyclocarbon carrying `z` protons, at charge state `z`.

## Derived candidates

With `M(E) = 590` and `M(C₄₈) = 48·12 = 576`:

| `m/z` | ion | check |
|------|-----|-------|
| 591 (example) | `[E + H]⁺` | `(590 + 1)/1 = 591` |
| 783  | `[3E + C₄₈ + 3H]³⁺` | `(3·590 + 576 + 3)/3 = 783` |
| 879  | `[2E + C₄₈ + 2H]²⁺` | `(2·590 + 576 + 2)/2 = 879` |
| 1174 | `[3E + C₄₈ + 2H]²⁺` | `(3·590 + 576 + 2)/2 = 1174` |

## Faithfulness / uniqueness provisos

* For **783** and **879** the planted assignment is the *unique*
  no-fragmentation solution among ions with charge state `z ≤ 3` and at most
  `z` attached protons that contain at most one `C₄₈` unit
  (`ion783_unique`, `ion879_unique` below).
* For **1174** the problem statement alone does not fix the charge state:
  the *singly* charged ion `[C₄₈ + E + 8H]⁺` has the same integer `m/z`
  (`catenane_octaprotonated_mz` below).  Both assignments respect the
  example's proton-attachment convention, but eight simultaneous protonations
  on an aggregate bearing only two basic nitrogen atoms is chemically
  unreasonable, whereas the three-`E` doubly protonated aggregate parallels
  the unambiguously required multiply protonated aggregates at 783 and 879.
  The problem's integer-`m/z` data do not rule the former out; this
  residual ambiguity is reported explicitly as a source gap in `answer.md`
  and `result.json` rather than silently assumed away.
-/

namespace IChO2026T6A4

/-! ## Integer atomic masses used in 6.4 (exactly as instructed:
    «use integer atomic masses»). -/

/-- Integer atomic mass of hydrogen (¹H): 1. -/
def massH : ℕ := 1

/-- Integer atomic mass of carbon (¹²C): 12. -/
def massC : ℕ := 12

/-- Integer atomic mass of nitrogen (¹⁴N): 14. -/
def massN : ℕ := 14

/-- Integer atomic mass of oxygen (¹⁶O): 16. -/
def massO : ℕ := 16

/-! ## Problem inputs: molecular formulae and their integer masses

**E** is the macrocycle printed on Q6-2 with formula `C₄₀H₃₄N₂O₃`;
**C₄₈** is cyclo[48]carbon, the all-carbon ring of 48 carbons. -/

/-- Integer molecular mass of macrocycle `E = C₄₀H₃₄N₂O₃`
    (`40·12 + 34·1 + 2·14 + 3·16`). -/
def massE : ℕ := 40 * massC + 34 * massH + 2 * massN + 3 * massO

/-- Integer molecular mass of cyclo[48]carbon, `C₄₈` (`48·12`). -/
def massC48 : ℕ := 48 * massC

theorem massE_value : massE = 590 := by
  decide

/-- Kernel-checked re-proof of the same fact by pure computation:
    `40·12 + 34·1 + 2·14 + 3·16 = 590`. -/
theorem massE_value_compute : massE = 590 := rfl

theorem massC48_value : massC48 = 576 := by
  decide

/-- Kernel-checked re-proof: `48·12 = 576`. -/
theorem massC48_value_compute : massC48 = 576 := rfl

/-! ## Ion candidates

An ion candidate is a no-fragmentation aggregate: `nE` copies of intact
macrocycle `E`, `nC48` copies of intact cyclo[48]carbon, and `nH` attached
protons, at charge state `z`.  Its total integer mass is
`nE·M(E) + nC48·M(C₄₈) + nH·M(H)` and its mass-to-charge ratio is
`totalMass / z`; a candidate explains an observed integer peak when this
number is exactly the observed `m/z`. -/

/-- A no-fragmentation ESI(+) ion candidate built from intact `E` and intact
    `C₄₈`, protonated `nH` times, observed at charge state `z`. -/
structure IonCandidate where
  nE : ℕ
  nC48 : ℕ
  nH : ℕ
  z : ℕ

/-- Total integer mass of the neutral-skeleton-plus-protons aggregate. -/
def IonCandidate.mass (i : IonCandidate) : ℕ :=
  i.nE * massE + i.nC48 * massC48 + i.nH * massH

/-- The candidate exactly accounts for the observed integer peak `mz`. -/
def IonCandidate.MatchesMZ (i : IonCandidate) (mz : ℕ) : Prop :=
  i.mass = mz * i.z

/-- Chemically meaningful candidates: a positive charge state, at least one
    intact molecule, and at least one attached proton (positive-mode ESI of
    this basic macrocycle, per the planted example `[E + H]⁺`). -/
def IonCandidate.WellFormed (i : IonCandidate) : Prop :=
  0 < i.z ∧ 1 ≤ i.nH ∧ 1 ≤ i.nE + i.nC48

/-- The target ions of 6.4 have the charge carried entirely by protons:
    `nH = z`.  (Each attached H⁺ contributes one unit of positive charge;
    the planted example `[E + H]⁺` fixes this convention.) -/
def IonCandidate.ProtonCharged (i : IonCandidate) : Prop :=
  i.nH = i.z

/-- Two ion candidates with the same composition and charge state are the
    same ion (field-wise record equality). -/
theorem IonCandidate.ext_iff' (a b : IonCandidate) :
    a.nE = b.nE → a.nC48 = b.nC48 → a.nH = b.nH → a.z = b.z → a = b := by
  cases a; cases b
  intro h1 h2 h3 h4
  simp_all

/-! ## The planted example, reproduced (sanity anchor) -/

/-- The example ion given on answer sheet A6-2 for `m/z = 591`: `[E + H]⁺`. -/
def ion591_example : IonCandidate := ⟨1, 0, 1, 1⟩

theorem ion591_example_proton_charged : ion591_example.ProtonCharged := rfl

theorem ion591_example_matches : ion591_example.MatchesMZ 591 := by
  show (1 * massE + 0 * massC48 + 1 * massH : ℕ) = 591 * 1
  simp [massE, massC48, massH, massC, massN, massO]

/-! ## Requested output 1: the ion at `m/z = 783` -/

/-- The ion at `m/z = 783`: `[3E + C₄₈ + 3H]³⁺` —
    a triply protonated aggregate of one cyclo[48]carbon ring with three
    macrocycles `E`. -/
def ion783 : IonCandidate := ⟨3, 1, 3, 3⟩

theorem ion783_is_protonated_aggregate :
    ion783.nE = 3 ∧ ion783.nC48 = 1 ∧ ion783.nH = 3 ∧ ion783.z = 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem ion783_total_mass : ion783.mass = 2349 := by
  show (3 * massE + 1 * massC48 + 3 * massH : ℕ) = 2349
  simp [massE, massC48, massH, massC, massN, massO]

theorem ion783_mz : ion783.MatchesMZ 783 := by
  show ion783.mass = 783 * 3
  rw [ion783_total_mass]

theorem ion783_proton_charged : ion783.ProtonCharged := rfl

/-- **Uniqueness for 783**: among all well-formed no-fragmentation ion
    candidates with charge state `z ≤ 3`, at most `z` attached protons, and
    at most one `C₄₈` unit, `[3E + C₄₈ + 3H]³⁺` is the only one that hits
    integer `m/z` 783 exactly. -/
theorem ion783_unique :
    ∀ i : IonCandidate, i.WellFormed → i.z ≤ 3 → i.nH ≤ i.z → i.nC48 ≤ 1 →
      i.MatchesMZ 783 → i = ion783 := by
  rintro ⟨e, c, h, z⟩ hwf hz hh hc hm
  simp only [IonCandidate.WellFormed] at hwf
  obtain ⟨hzpos, hH1, hnat⟩ := hwf
  simp only at hz hh hc hzpos hH1 hnat
  have hm' : e * 590 + c * 576 + h * 1 = 783 * z := by
    simp only [IonCandidate.MatchesMZ, IonCandidate.mass, massE, massC48, massH, massC, massN, massO] at hm
    omega
  clear hm
  -- Derive per-field bounds from the mass equation before case-splitting:
  -- since every other summand is nonnegative, `nE ≤ 783·z/590 ≤ 3`.
  have hE : e ≤ 3 := by omega
  interval_cases z <;> interval_cases e <;> interval_cases c <;> interval_cases h <;>
    first
      | omega
      | rfl

/-! ## Requested output 2: the ion at `m/z = 879` -/

/-- The ion at `m/z = 879`: `[2E + C₄₈ + 2H]²⁺` —
    a doubly protonated aggregate of one cyclo[48]carbon ring with two
    macrocycles `E`. -/
def ion879 : IonCandidate := ⟨2, 1, 2, 2⟩

theorem ion879_is_protonated_aggregate :
    ion879.nE = 2 ∧ ion879.nC48 = 1 ∧ ion879.nH = 2 ∧ ion879.z = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem ion879_total_mass : ion879.mass = 1758 := by
  show (2 * massE + 1 * massC48 + 2 * massH : ℕ) = 1758
  simp [massE, massC48, massH, massC, massN, massO]

theorem ion879_mz : ion879.MatchesMZ 879 := by
  show ion879.mass = 879 * 2
  rw [ion879_total_mass]

theorem ion879_proton_charged : ion879.ProtonCharged := rfl

/-- **Uniqueness for 879**: among all well-formed no-fragmentation ion
    candidates with charge state `z ≤ 3`, at most `z` attached protons, and
    at most one `C₄₈` unit, `[2E + C₄₈ + 2H]²⁺` is the only one that hits
    integer `m/z` 879 exactly. -/
theorem ion879_unique :
    ∀ i : IonCandidate, i.WellFormed → i.z ≤ 3 → i.nH ≤ i.z → i.nC48 ≤ 1 →
      i.MatchesMZ 879 → i = ion879 := by
  rintro ⟨e, c, h, z⟩ hwf hz hh hc hm
  simp only [IonCandidate.WellFormed] at hwf
  obtain ⟨hzpos, hH1, hnat⟩ := hwf
  simp only at hz hh hc hzpos hH1 hnat
  have hm' : e * 590 + c * 576 + h * 1 = 879 * z := by
    simp only [IonCandidate.MatchesMZ, IonCandidate.mass, massE, massC48, massH, massC, massN, massO] at hm
    omega
  clear hm
  have hE : e ≤ 4 := by omega
  interval_cases z <;> interval_cases e <;> interval_cases c <;> interval_cases h <;>
    first
      | omega
      | rfl

/-! ## Requested output 3: the ion at `m/z = 1174` -/

/-- The ion at `m/z = 1174`: `[3E + C₄₈ + 2H]²⁺` —
    a doubly protonated aggregate of one cyclo[48]carbon ring with three
    macrocycles `E`. -/
def ion1174 : IonCandidate := ⟨3, 1, 2, 2⟩

theorem ion1174_is_protonated_aggregate :
    ion1174.nE = 3 ∧ ion1174.nC48 = 1 ∧ ion1174.nH = 2 ∧ ion1174.z = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem ion1174_total_mass : ion1174.mass = 2348 := by
  show (3 * massE + 1 * massC48 + 2 * massH : ℕ) = 2348
  simp [massE, massC48, massH, massC, massN, massO]

theorem ion1174_mz : ion1174.MatchesMZ 1174 := by
  show ion1174.mass = 1174 * 2
  rw [ion1174_total_mass]

theorem ion1174_proton_charged : ion1174.ProtonCharged := rfl

/-- **Uniqueness of the doubly charged assignment for 1174**: among all
    well-formed no-fragmentation ion candidates at charge state exactly `2`
    with at most two attached protons and at most one `C₄₈` unit,
    `[3E + C₄₈ + 2H]²⁺` is the only one that hits integer `m/z` 1174. -/
theorem ion1174_unique_at_charge_two :
    ∀ i : IonCandidate, i.WellFormed → i.z = 2 → i.nH ≤ 2 → i.nC48 ≤ 1 →
      i.MatchesMZ 1174 → i = ion1174 := by
  rintro ⟨e, c, h, z⟩ hwf hz hh hc hm
  simp only [IonCandidate.WellFormed] at hwf
  obtain ⟨hzpos, hH1, hnat⟩ := hwf
  simp only at hz hh hc hzpos hH1 hnat
  obtain rfl : z = 2 := hz
  have hm' : e * 590 + c * 576 + h * 1 = 1174 * 2 := by
    simp only [IonCandidate.MatchesMZ, IonCandidate.mass, massE, massC48, massH, massC, massN, massO] at hm
    omega
  have hE : e ≤ 3 := by omega
  interval_cases e <;> interval_cases c <;> interval_cases h <;>
    first
      | omega
      | rfl

/-- **Source gap, made explicit**: the integer-`m/z` data of 6.4 do not by
    themselves exclude the singly charged alternative
    `[C₄₈ + E + 8H]⁺ = (576 + 590 + 8)/1 = 1174`, which also uses intact
    molecules and proton attachment.  The planted (chemically sensible)
    answer is the doubly charged aggregate `ion1174` above: a one-to-two
    aggregate carrying eight protons on only two basic nitrogen atoms is not
    chemically reasonable, and all unambiguous peaks of the series are
    multiply protonated aggregates.  This residual charge-state ambiguity is
    reported, not assumed away. -/
def ion1174_alternative_singly_charged : IonCandidate := ⟨1, 1, 8, 1⟩

theorem catenane_octaprotonated_mz :
    ion1174_alternative_singly_charged.MatchesMZ 1174 := by
  show (1 * massE + 1 * massC48 + 8 * massH : ℕ) = 1174 * 1
  simp [massE, massC48, massH, massC, massN, massO]

/-! ## Axiom audit for the final theorems -/

#print axioms massE_value
#print axioms massC48_value
#print axioms ion591_example_matches
#print axioms ion783_total_mass
#print axioms ion783_mz
#print axioms ion783_unique
#print axioms ion879_total_mass
#print axioms ion879_mz
#print axioms ion879_unique
#print axioms ion1174_total_mass
#print axioms ion1174_mz
#print axioms ion1174_unique_at_charge_two
#print axioms catenane_octaprotonated_mz

end IChO2026T6A4
