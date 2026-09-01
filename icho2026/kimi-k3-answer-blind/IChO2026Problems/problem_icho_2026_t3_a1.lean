import IChO2026Chem

/-!
# IChO 2026, Problem T3-A1 — COF-1 empirical formula and carbon mass percent

Answer-blind formalization of target `icho_2026_t3_a1`.

## Chemistry recorded from the sealed problem page (`T3_page-1.png`)

The scheme builds COF-1 by co-condensing two monomers drawn in the problem:

* **HHTP** (building block B3): hexahydroxytriphenylene, `C18H12O6`; the
  triphenylene core carries six phenolic OH groups, i.e. three catechol pairs.
* **BDBA** (building block A2): benzene-1,4-diboronic acid, `C6H8B2O4`;
  each boronic acid group `B(OH)2` caps one catechol pair as a five-membered
  boronate-ester ring.

Each ring closure expels two water molecules (one `H2O` per B–O linkage
formed).  Site bookkeeping per framework repeat unit:

* every HHTP closes 3 rings and every BDBA closes 2 rings, so the honeycomb
  composition is `2 HHTP : 3 BDBA`, closing `6` rings and releasing `12 H2O`;
* net repeat unit `2*C18H12O6 + 3*C6H8B2O4 - 12*H2O = C54H24B6O12`;
* dividing by `gcd(54, 24, 6, 12) = 6` gives the empirical formula `C9H4BO2`.

Atomic weights are the pinned offline dataset values (CIAAW abridged 2024
subset, recorded through the sanctioned CLI): C 12.011, H 1.0080, B 10.81,
O 15.999.  The raw carbon mass percentage of `C9H4BO2` (molar mass 154.939)
is the exact rational `10809900/154939` percent (`69.768747...`), and
reporting at the problem-requested quantum of two decimal places with ties
away from zero gives `69.77 %`.

The two `...ResultContract` theorems at the end bind the answer-blind payload
digests to the semantic specifications `Cof1RawSpec` / `Cof1ReportedSpec`;
the low-privilege verifier probes them by name.
-/

namespace IChO2026Problems.problem_icho_2026_t3_a1

/-- Atom inventory of a C/H/B/O formula unit. -/
structure AtomCounts where
  C : ℕ
  H : ℕ
  B : ℕ
  O : ℕ

namespace AtomCounts

/-- Scale every count by a common factor. -/
def scale (k : ℕ) (f : AtomCounts) : AtomCounts := ⟨k * f.C, k * f.H, k * f.B, k * f.O⟩

/-- Componentwise join of two inventories (a formal reactant sum). -/
def add (f g : AtomCounts) : AtomCounts := ⟨f.C + g.C, f.H + g.H, f.B + g.B, f.O + g.O⟩

/-- Common divisor of the four counts. -/
def gcd (f : AtomCounts) : ℕ := Nat.gcd (Nat.gcd f.C f.H) (Nat.gcd f.B f.O)

theorem scale_gcd (k : ℕ) (f : AtomCounts) : (f.scale k).gcd = k * f.gcd := by
  simp [AtomCounts.gcd, AtomCounts.scale, Nat.gcd_mul_left]

/-- Two reduced empirical formulas that scale to the same unit cell agree. -/
theorem empirical_unique {fbig f₁ f₂ : AtomCounts} {k₁ k₂ : ℕ}
    (hk₂ : 0 < k₂)
    (h₁ : fbig = f₁.scale k₁) (h₂ : fbig = f₂.scale k₂)
    (hg₁ : f₁.gcd = 1) (hg₂ : f₂.gcd = 1) : f₁ = f₂ := by
  have hk : k₁ = k₂ := by
    have e₁ : fbig.gcd = k₁ := by rw [h₁, scale_gcd, hg₁, mul_one]
    have e₂ : fbig.gcd = k₂ := by rw [h₂, scale_gcd, hg₂, mul_one]
    rw [← e₁, ← e₂]
  obtain ⟨C₁, H₁, B₁, O₁⟩ := f₁
  obtain ⟨C₂, H₂, B₂, O₂⟩ := f₂
  rw [hk] at h₁
  rw [h₁] at h₂
  simp only [AtomCounts.scale, AtomCounts.mk.injEq] at h₂
  obtain ⟨hC, hH, hB, hO⟩ := h₂
  simp only [AtomCounts.mk.injEq]
  exact ⟨Nat.eq_of_mul_eq_mul_left hk₂ hC, Nat.eq_of_mul_eq_mul_left hk₂ hH,
    Nat.eq_of_mul_eq_mul_left hk₂ hB, Nat.eq_of_mul_eq_mul_left hk₂ hO⟩

end AtomCounts

/-- HHTP monomer (building block B3): hexahydroxytriphenylene, `C18H12O6`. -/
def hhtpFree : AtomCounts := ⟨18, 12, 0, 6⟩

/-- BDBA monomer (building block A2): benzene-1,4-diboronic acid, `C6H8B2O4`. -/
def bdbaFree : AtomCounts := ⟨6, 8, 2, 4⟩

/-- Water, `H2O`. -/
def waterCounts : AtomCounts := ⟨0, 2, 0, 1⟩

/-- Framework repeat unit of COF-1, `C54H24B6O12`. -/
def cof1UnitCell : AtomCounts := ⟨54, 24, 6, 12⟩

/-- Empirical formula of COF-1, `C9H4BO2`. -/
def cof1Empirical : AtomCounts := ⟨9, 4, 1, 2⟩

/-- Site bookkeeping for the boronate-ester honeycomb: `hhtp` HHTP monomers and
`bdba` BDBA monomers close `rings` boronate-ester rings and release `water`
water molecules.  Each HHTP contributes three catechol pairs (hence three
rings), each BDBA contributes two boronic acid groups (hence two rings), and
each ring expels two water molecules. -/
def SiteBalance (hhtp bdba rings water : ℕ) : Prop :=
  3 * hhtp = rings ∧ 2 * bdba = rings ∧ water = 2 * rings

theorem siteBalance_ratio {hhtp bdba rings water : ℕ}
    (h : SiteBalance hhtp bdba rings water) :
    2 * bdba = 3 * hhtp ∧ water = 6 * hhtp := by
  obtain ⟨h1, h2, h3⟩ := h
  omega

/-- Composition of a site-balanced honeycomb fragment: the monomer inventory
equals the framework inventory plus the expelled water. -/
theorem siteBalance_composition {v e r w : ℕ} (h : SiteBalance v e r w) :
    (hhtpFree.scale v).add (bdbaFree.scale e) =
      (AtomCounts.mk (18 * v + 6 * e) (12 * v + 8 * e - 2 * w) (2 * e)
        (6 * v + 4 * e - w)).add (waterCounts.scale w) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [AtomCounts.scale, AtomCounts.add, hhtpFree, bdbaFree, waterCounts,
    AtomCounts.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The COF-1 repeat satisfies the site bookkeeping with 2 HHTP, 3 BDBA,
6 rings and 12 water molecules. -/
theorem cof1_siteBalance : SiteBalance 2 3 6 12 := ⟨rfl, rfl, rfl⟩

/-- Explicit atom inventory of the COF-1 repeat unit. -/
theorem cof1_unitCell_composition : cof1UnitCell = ⟨54, 24, 6, 12⟩ := rfl

/-- Net stoichiometry: `2*C18H12O6 + 3*C6H8B2O4 = C54H24B6O12 + 12*H2O`. -/
theorem cof1_condensation_balance :
    (hhtpFree.scale 2).add (bdbaFree.scale 3) =
      cof1UnitCell.add (waterCounts.scale 12) := rfl

/-- The repeat unit is six empirical units. -/
theorem cof1_unitCell_eq_scale : cof1UnitCell = cof1Empirical.scale 6 := rfl

/-- The empirical formula is reduced (coprime counts). -/
theorem cof1_empirical_reduced : cof1Empirical.gcd = 1 := by decide

/-- Any reduced formula that scales by 6 to the repeat unit is the empirical
formula: `C9H4BO2` is the unique empirical formula of COF-1. -/
theorem cof1_empirical_unique {f : AtomCounts}
    (hg : f.gcd = 1) (h : cof1UnitCell = f.scale 6) : f = cof1Empirical :=
  AtomCounts.empirical_unique (by decide : (0 : ℕ) < 6) h cof1_unitCell_eq_scale hg
    cof1_empirical_reduced

/-- Pinned dataset atomic weight of carbon, g/mol. -/
def atomicWeightC : ℝ := 12.011

/-- Pinned dataset atomic weight of hydrogen, g/mol. -/
def atomicWeightH : ℝ := 1.0080

/-- Pinned dataset atomic weight of boron, g/mol. -/
def atomicWeightB : ℝ := 10.81

/-- Pinned dataset atomic weight of oxygen, g/mol. -/
def atomicWeightO : ℝ := 15.999

/-- Molar mass of a C/H/B/O formula unit from the pinned atomic weights. -/
def molarMass (f : AtomCounts) : ℝ :=
  ↑f.C * atomicWeightC + ↑f.H * atomicWeightH + ↑f.B * atomicWeightB + ↑f.O * atomicWeightO

/-- Molar mass of the empirical formula `C9H4BO2`: 154.939 g/mol. -/
theorem molarMass_cof1Empirical : molarMass cof1Empirical = (154.939 : ℝ) := by
  norm_num [molarMass, cof1Empirical, atomicWeightC, atomicWeightH, atomicWeightB, atomicWeightO]

/-- Raw (unrounded) carbon mass percentage of COF-1. -/
noncomputable def cof1CarbonMassPercentRaw : ℝ :=
  100 * (↑cof1Empirical.C * atomicWeightC) / molarMass cof1Empirical

theorem cof1Empirical_C_cast : (↑cof1Empirical.C : ℝ) = 9 := by
  norm_num [cof1Empirical]

/-- The raw percentage is exactly `100*(9*12.011)/M(C9H4BO2)`. -/
theorem cof1_raw_expression :
    cof1CarbonMassPercentRaw = 100 * ((9 : ℝ) * atomicWeightC) / molarMass cof1Empirical := by
  unfold cof1CarbonMassPercentRaw
  rw [cof1Empirical_C_cast]

/-- Exact rational value of the raw carbon mass percentage:
`100*(9*12.011)/154.939 = 10809900/154939`. -/
theorem cof1_carbonMassPercentRaw_value :
    cof1CarbonMassPercentRaw = (10809900 : ℝ) / 154939 := by
  norm_num [cof1CarbonMassPercentRaw, molarMass, cof1Empirical, atomicWeightC, atomicWeightH,
    atomicWeightB, atomicWeightO]

/-- Certified interval for the raw value: `69.7687 ≤ w(C) ≤ 69.7688`. -/
theorem cof1_carbonMassPercentRaw_bounds :
    (69.7687 : ℝ) ≤ cof1CarbonMassPercentRaw ∧ cof1CarbonMassPercentRaw ≤ (69.7688 : ℝ) := by
  rw [cof1_carbonMassPercentRaw_value]
  constructor <;> norm_num

/-- Reporting certificate: at the problem-requested quantum `0.01` (two
decimal places, ties away from zero), the raw value is reported as `69.77`. -/
theorem cof1_carbonMassPercent_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum cof1CarbonMassPercentRaw 69.77 0.01 := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  rw [cof1_carbonMassPercentRaw_value]
  refine ⟨by norm_num, ⟨6977, by norm_num⟩, ?_⟩
  split_ifs with hpos
  · constructor <;> norm_num
  · norm_num at hpos

/-- Semantic specification of the COF-1 stoichiometric derivation. -/
def Cof1DerivationSpec : Prop :=
  SiteBalance 2 3 6 12 ∧
  (∀ v e r w : ℕ, SiteBalance v e r w →
    (hhtpFree.scale v).add (bdbaFree.scale e) =
      (AtomCounts.mk (18 * v + 6 * e) (12 * v + 8 * e - 2 * w) (2 * e)
        (6 * v + 4 * e - w)).add (waterCounts.scale w)) ∧
  (hhtpFree.scale 2).add (bdbaFree.scale 3) = cof1UnitCell.add (waterCounts.scale 12) ∧
  cof1UnitCell = cof1Empirical.scale 6 ∧
  cof1Empirical.gcd = 1 ∧
  (∀ f : AtomCounts, f.gcd = 1 → cof1UnitCell = f.scale 6 → f = cof1Empirical) ∧
  cof1Empirical = ⟨9, 4, 1, 2⟩

/-- Semantic specification of the raw result: the stoichiometric derivation
plus the exact raw carbon mass percentage and its certified interval. -/
def Cof1RawSpec : Prop := Cof1DerivationSpec ∧
  cof1CarbonMassPercentRaw = 100 * ((9 : ℝ) * atomicWeightC) / molarMass cof1Empirical ∧
  cof1CarbonMassPercentRaw = (10809900 : ℝ) / 154939 ∧
  (69.7687 : ℝ) ≤ cof1CarbonMassPercentRaw ∧
  cof1CarbonMassPercentRaw ≤ (69.7688 : ℝ)

/-- Semantic specification of the reported result: the empirical formula
`C9H4BO2` and the reported carbon mass percentage `69.77 %`. -/
def Cof1ReportedSpec : Prop :=
  cof1Empirical = ⟨9, 4, 1, 2⟩ ∧
  IChO2026Chem.Reporting.ReportsAtQuantum cof1CarbonMassPercentRaw 69.77 0.01

/-- The raw specification is satisfied by the derivation above. -/
theorem cof1RawSpecHolds : Cof1RawSpec := by
  refine ⟨⟨cof1_siteBalance, ?_, cof1_condensation_balance, cof1_unitCell_eq_scale,
      cof1_empirical_reduced, fun f hg h => cof1_empirical_unique hg h, rfl⟩,
    cof1_raw_expression, cof1_carbonMassPercentRaw_value,
    cof1_carbonMassPercentRaw_bounds.1, cof1_carbonMassPercentRaw_bounds.2⟩
  intro v e r w h
  exact siteBalance_composition h

/-- Answer-blind payload binding for the raw result. -/
theorem cof1RawResultContract :
    ("924f336e083bb3a2ee720954244b5e087e4ec6dd5a1610c74fa6d9c5572bf605" : String) =
      "924f336e083bb3a2ee720954244b5e087e4ec6dd5a1610c74fa6d9c5572bf605" ∧ Cof1RawSpec :=
  ⟨rfl, cof1RawSpecHolds⟩

/-- Answer-blind payload binding for the reported result. -/
theorem cof1ReportedResultContract :
    ("18b400f70355b8e1489e3e59625786659e43d37f90ffabdf0f466658c115ab70" : String) =
      "18b400f70355b8e1489e3e59625786659e43d37f90ffabdf0f466658c115ab70" ∧ Cof1ReportedSpec :=
  ⟨rfl, rfl, cof1_carbonMassPercent_reported⟩

end IChO2026Problems.problem_icho_2026_t3_a1
