import Mathlib
import IChO2026Chem

/-!
# IChO 2026 · Problem T6 (Carbon Nanorings) · Part 6.4 — target `icho_2026_t6_a4`

## Problem (answer-blind source contract)

Question 6.4 (T6 page 2, `T6_page-2.png`):

> In the mass spectrum obtained, four intense peaks were observed m/z: 591, 783, 879, and
> 1174. **Suggest** the identity of these ions. **Use** integer atomic masses and **assume**
> no fragmentation happened. The ion corresponding to m/z = 591 is given as an example.

Shared context (T6 page 2, directly above question 6.4): in 2025 the first relatively stable
cyclo[48]carbon was synthesised; the molecule was stabilised by **catenation** (forming
interlocking rings) with **macrocycle E** and was first characterised by **electrospray mass
spectrometry in positive mode**. T6 page 2 depicts the C₄₈ ring and the structure of E with
the printed formula **C₄₀H₃₄N₂O₃** beneath it.

## Assumption / target split

**Assumptions (problem-side evidence only).**

1. *Integer-mass convention* (`problem_text`, question 6.4: "Use integer atomic masses"):
   C = 12, H = 1, N = 14, O = 16; the electron mass is neglected at integer precision.
2. *Stated components* (`problem_text` + `problem_image` T6 page 2): the sample contains the
   cyclo[48]carbon ring C₄₈ (integer mass 48·12 = 576) and macrocycle E = C₄₀H₃₄N₂O₃ (integer
   mass 40·12 + 34·1 + 2·14 + 3·16 = 590), catenated together.
3. *Ion model* (`problem_text`: catenation, electrospray positive mode, "assume no
   fragmentation happened"): observed ions are protonated intact assemblies
   `[a·C48 + b·E + zH]ᶻ⁺`, `a, b ≥ 0`, `z ≥ 1`, with `m/z = (576·a + 590·b + z)/z`.
4. *Example anchor* (`problem_text`): the m/z 591 ion is given as the example; `[E + H]⁺` has
   integer mass 590 + 1 = 591, fixing the intact-assembly protonation model (and selecting the
   primitive member among the degenerate `[E_z + zH]ᶻ⁺` cluster scalings that also match 591).
5. *Charge ladder* (ESI model assumption): the search charges are z = 1, 2, 3. For these four
   printed peaks every z ≥ 4 match is an integer scaling `(k·a, k·b, k·z)` of a primitive
   z ≤ 3 member — chemically the same assembly reported at a higher charge.
6. *Data-derived box bounds* (`derived_theorem` `candidateIons_complete`): for any peak
   m/z = m ≤ 1174 and charge z ≤ 3, the assembly mass `(m−1)·z ≤ 1173·3 = 3519` forces
   `a ≤ ⌊3519/576⌋ = 6` and `b ≤ ⌊3519/590⌋ = 5`. The finite box `0 ≤ a ≤ 6`, `0 ≤ b ≤ 5`,
   `1 ≤ z ≤ 3` is therefore *complete* for every observed peak — it is derived from the printed
   data, not fitted to any candidate.

**Targets (requested outputs `ion_783`, `ion_879`, `ion_1174`, kind `formula`, reporting
`exact_symbolic`).** Exhaustive uniform filtering of the complete box:

| peak | box matches | assignment |
|---|---|---|
| 591 (printed example) | (0,1,1), (0,2,2), (0,3,3) | `[E + H]⁺` (primitive member) |
| 783 | (1,3,3) only | `[C48(E)3 + 3H]³⁺` = `[C₁₆₈H₁₀₅N₆O₉]³⁺` |
| 879 | (1,2,2) only | `[C48(E)2 + 2H]²⁺` = `[C₁₂₈H₇₀N₄O₆]²⁺` |
| 1174 | (1,3,2) only | `[C48(E)3 + 2H]²⁺` = `[C₁₆₈H₁₀₄N₆O₉]²⁺` |

Reading: the free macrocycle E gives the printed example 591; the [3]catenane C48(E)₂ appears
as its doubly protonated ion at 879; the [4]catenane C48(E)₃ appears as its triply protonated
ion at 783 and its doubly protonated ion at 1174.

The pinned offline registry was used for corroboration only (the problem-stipulated integer
masses govern): dataset `ciaaw-abridged-2024+ame2020-subset+archon-templates-v1` +
`contest-interpretation-v1+trusted-empirical-rules-v1` (id split at a `+` for line width),
sha256 `11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`; `atomic_weight`
C = 12.011 (record `0f558fc7…be4b8a`), H = 1.0080 (`8e5f2e51…64b4bce5`), N = 14.007
(`5ca62d43…b6f065c`), O = 15.999 (`d55ad559…efcc0588`); `molar_mass` C₄₀H₃₄N₂O₃ = 590.723
(record `6dc36e88…e985a7`). No `reaction_template`, `contest_interpretation`, or
`empirical_rule` applies to this target; none was probed.
-/

namespace Icho2026T6A4

/-- An empirical formula over the four elements appearing in this problem (carbon, hydrogen,
nitrogen, oxygen), as atom counts. Provenance: `problem_image` T6 page 2 (C₄₈ ring; macrocycle
E with printed formula C₄₀H₃₄N₂O₃). -/
structure Formula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
deriving DecidableEq, Repr

/-- Integer mass of a formula under the problem-stipulated integer atomic masses
(`problem_text`, question 6.4: "Use integer atomic masses"): C = 12, H = 1, N = 14, O = 16. -/
def Formula.integerMass (f : Formula) : ℕ :=
  12 * f.carbon + 1 * f.hydrogen + 14 * f.nitrogen + 16 * f.oxygen

/-- The formula of `k` copies of `f` (an assembly of repeated intact units). -/
def Formula.scale (k : ℕ) (f : Formula) : Formula :=
  ⟨k * f.carbon, k * f.hydrogen, k * f.nitrogen, k * f.oxygen⟩

/-- The combined formula of two co-present intact components (mass-additive). -/
def Formula.append (f g : Formula) : Formula :=
  ⟨f.carbon + g.carbon, f.hydrogen + g.hydrogen, f.nitrogen + g.nitrogen, f.oxygen + g.oxygen⟩

/-- Integer mass is additive over repetition. -/
theorem Formula.integerMass_scale (k : ℕ) (f : Formula) :
    (f.scale k).integerMass = k * f.integerMass := by
  simp [Formula.scale, Formula.integerMass]; ring

/-- Integer mass is additive over combination. -/
theorem Formula.integerMass_append (f g : Formula) :
    (f.append g).integerMass = f.integerMass + g.integerMass := by
  simp [Formula.append, Formula.integerMass]; ring

/-- Cyclo[48]carbon, the all-carbon ring (`problem_text` shared context; `problem_image`
T6 page 2). -/
def cycloC48 : Formula := ⟨48, 0, 0, 0⟩

/-- Macrocycle E as printed under its structure on T6 page 2: C₄₀H₃₄N₂O₃ (`problem_image`). -/
def macrocycleE : Formula := ⟨40, 34, 2, 3⟩

/-- Integer mass of cyclo[48]carbon: 48·12 = 576. -/
theorem cycloC48_mass : cycloC48.integerMass = 576 := rfl

/-- Integer mass of macrocycle E: 40·12 + 34·1 + 2·14 + 3·16 = 590. -/
theorem macrocycleE_mass : macrocycleE.integerMass = 590 := rfl

/-- A positive-mode ESI cluster ion built from `c48` intact cyclo[48]carbon rings and `e`
intact macrocycles E, protonated by `protons` protons (the charge state). Provenance of the
model: `problem_text` (catenation of C₄₈ with E; electrospray mass spectrometry in positive
mode; "assume no fragmentation happened"). -/
@[ext]
structure ClusterIon where
  c48 : ℕ
  e : ℕ
  protons : ℕ
deriving DecidableEq, Repr

/-- The neutral assembly formula: `c48` copies of C₄₈ combined with `e` copies of E. -/
def ClusterIon.assemblyFormula (i : ClusterIon) : Formula :=
  (cycloC48.scale i.c48).append (macrocycleE.scale i.e)

/-- The neutral assembly integer mass. -/
def ClusterIon.assemblyMass (i : ClusterIon) : ℕ := i.assemblyFormula.integerMass

/-- The assembly mass is `576·c48 + 590·e`. -/
theorem ClusterIon.assemblyMass_eq (i : ClusterIon) :
    i.assemblyMass = i.c48 * 576 + i.e * 590 := by
  simp [ClusterIon.assemblyMass, ClusterIon.assemblyFormula, Formula.integerMass_append,
    Formula.integerMass_scale, cycloC48_mass, macrocycleE_mass]

/-- Total ion mass at integer masses: the assembly mass plus one mass unit per attached
proton (electron mass neglected at integer precision). -/
def ClusterIon.ionMass (i : ClusterIon) : ℕ := i.assemblyMass + i.protons

/-- The summed ion formula, with the attached protons counted as hydrogen atoms. -/
def ClusterIon.ionFormula (i : ClusterIon) : Formula :=
  i.assemblyFormula.append ⟨0, i.protons, 0, 0⟩

/-- The summed ion formula mass equals the ion mass. -/
theorem ClusterIon.ionFormula_mass (i : ClusterIon) :
    i.ionFormula.integerMass = i.ionMass := by
  rw [ClusterIon.ionFormula, Formula.integerMass_append]
  simp [Formula.integerMass, ClusterIon.ionMass, ClusterIon.assemblyMass]

/-- m/z matching at integer masses: an ion has m/z = `m` iff it carries at least one proton
(positive mode) and its ion mass equals `m * z` with `z` its proton count. Reducible
(`abbrev`) so that membership in the filtered candidate box stays decidable. -/
abbrev ClusterIon.MatchesMz (i : ClusterIon) (m : ℕ) : Prop :=
  1 ≤ i.protons ∧ i.ionMass = m * i.protons

/-- The printed example ion at m/z 591: the protonated free macrocycle `[E + H]⁺`
(`problem_text`: "The ion corresponding to m/z = 591 is given as an example"). -/
def exampleIon591 : ClusterIon := ⟨0, 1, 1⟩

/-- The derived ion at m/z 783: `[C48(E)3 + 3H]³⁺`, the triply protonated [4]catenane
C₄₈(E)₃ (derived by `ionsAt_783`, not assumed). -/
def ion783 : ClusterIon := ⟨1, 3, 3⟩

/-- The derived ion at m/z 879: `[C48(E)2 + 2H]²⁺`, the doubly protonated [3]catenane
C₄₈(E)₂ (derived by `ionsAt_879`, not assumed). -/
def ion879 : ClusterIon := ⟨1, 2, 2⟩

/-- The derived ion at m/z 1174: `[C48(E)3 + 2H]²⁺`, the doubly protonated [4]catenane
C₄₈(E)₃ (derived by `ionsAt_1174`, not assumed). -/
def ion1174 : ClusterIon := ⟨1, 3, 2⟩

/-- The finite search box of cluster ions: up to 6 C₄₈ rings, up to 5 macrocycles E, and
charge states 1–3. The bounds are data-derived, not answer-fitted: any ion matching an
observed peak `m ≤ 1174` with charge `z ≤ 3` has assembly mass `(m−1)·z ≤ 3519`, forcing
`c48 ≤ ⌊3519/576⌋ = 6` and `e ≤ ⌊3519/590⌋ = 5` (see `candidateIons_complete`). -/
def candidateIons : Finset ClusterIon :=
  (Finset.Icc (0 : ℕ) 6 ×ˢ (Finset.Icc (0 : ℕ) 5 ×ˢ Finset.Icc 1 3)).image
    (fun x : ℕ × ℕ × ℕ => ⟨x.1, x.2.1, x.2.2⟩)

/-- The ions in the search box matching a given integer m/z value. -/
def ionsAt (m : ℕ) : Finset ClusterIon :=
  candidateIons.filter (fun i => i.MatchesMz m)

/-- Membership in the search box, unpacked to explicit bounds on the three components. -/
theorem mem_candidateIons {i : ClusterIon} :
    i ∈ candidateIons ↔ i.c48 ≤ 6 ∧ i.e ≤ 5 ∧ 1 ≤ i.protons ∧ i.protons ≤ 3 := by
  simp only [candidateIons, Finset.mem_image, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨a, b, z⟩, ⟨⟨_, ha⟩, ⟨_, hb⟩, hz1, hz2⟩, h⟩
    subst h
    exact ⟨ha, hb, hz1, hz2⟩
  · rintro ⟨ha, hb, hz1, hz2⟩
    exact ⟨(i.c48, i.e, i.protons), ⟨⟨Nat.zero_le _, ha⟩, ⟨Nat.zero_le _, hb⟩, hz1, hz2⟩, rfl⟩

/-- The search box is complete for every observed peak: any cluster ion matching a peak
`m ≤ 1174` at a searched charge `z ≤ 3` lies in the box, because its assembly mass
`(m−1)·z ≤ 1173·3 = 3519` bounds `c48 ≤ 6` and `e ≤ 5`. -/
theorem candidateIons_complete {i : ClusterIon} {m : ℕ} (hm : m ≤ 1174) (hz : i.protons ≤ 3)
    (h : i.MatchesMz m) : i ∈ candidateIons := by
  obtain ⟨hz1, hmz⟩ := h
  have h1 : i.c48 * 576 + i.e * 590 = i.assemblyMass := (ClusterIon.assemblyMass_eq i).symm
  have h2 : i.assemblyMass + i.protons = m * i.protons := hmz
  have h3 : m * i.protons ≤ 3522 := by
    calc m * i.protons ≤ 1174 * 3 := Nat.mul_le_mul hm hz
      _ = 3522 := rfl
  have ha : i.c48 ≤ 6 := by omega
  have hb : i.e ≤ 5 := by omega
  exact mem_candidateIons.mpr ⟨ha, hb, hz1, hz⟩

/-- The integer-mass matching equation at m/z 591, solved over the complete box: exactly the
protonated free-macrocycle cluster scalings `(0,1,1)`, `(0,2,2)`, `(0,3,3)`. Proved by
splitting the finitely many data-derived bounds and checking each ground equation. -/
theorem mass_eq_591 {a b z : ℕ} (ha : a ≤ 6) (hb : b ≤ 5) (hz1 : 1 ≤ z) (hz2 : z ≤ 3)
    (h : a * 576 + b * 590 + z = 591 * z) :
    (a = 0 ∧ b = 1 ∧ z = 1) ∨ (a = 0 ∧ b = 2 ∧ z = 2) ∨ (a = 0 ∧ b = 3 ∧ z = 3) := by
  interval_cases z <;> interval_cases a <;> interval_cases b <;> omega

/-- The integer-mass matching equation at m/z 783, solved over the complete box: the unique
solution is `(1,3,3)`. -/
theorem mass_eq_783 {a b z : ℕ} (ha : a ≤ 6) (hb : b ≤ 5) (hz1 : 1 ≤ z) (hz2 : z ≤ 3)
    (h : a * 576 + b * 590 + z = 783 * z) : a = 1 ∧ b = 3 ∧ z = 3 := by
  interval_cases z <;> interval_cases a <;> interval_cases b <;> omega

/-- The integer-mass matching equation at m/z 879, solved over the complete box: the unique
solution is `(1,2,2)`. -/
theorem mass_eq_879 {a b z : ℕ} (ha : a ≤ 6) (hb : b ≤ 5) (hz1 : 1 ≤ z) (hz2 : z ≤ 3)
    (h : a * 576 + b * 590 + z = 879 * z) : a = 1 ∧ b = 2 ∧ z = 2 := by
  interval_cases z <;> interval_cases a <;> interval_cases b <;> omega

/-- The integer-mass matching equation at m/z 1174, solved over the complete box: the unique
solution is `(1,3,2)`. -/
theorem mass_eq_1174 {a b z : ℕ} (ha : a ≤ 6) (hb : b ≤ 5) (hz1 : 1 ≤ z) (hz2 : z ≤ 3)
    (h : a * 576 + b * 590 + z = 1174 * z) : a = 1 ∧ b = 3 ∧ z = 2 := by
  interval_cases z <;> interval_cases a <;> interval_cases b <;> omega

/-- The printed example, audited: within the search box, m/z 591 is matched exactly by the
protonated macrocycle cluster scalings `(0,1,1)`, `(0,2,2)`, `(0,3,3)`; the printed example
selects the primitive member `[E + H]⁺ = (0,1,1)`. -/
theorem ionsAt_591 : ionsAt 591 = {exampleIon591, ⟨0, 2, 2⟩, ⟨0, 3, 3⟩} := by
  ext i
  simp only [ionsAt, Finset.mem_filter, mem_candidateIons, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨ha, hb, hz1, hz2⟩, -, hm⟩
    simp only [ClusterIon.ionMass, ClusterIon.assemblyMass_eq] at hm
    rcases mass_eq_591 ha hb hz1 hz2 hm with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left; exact ClusterIon.ext h1 h2 h3
    · right; left; exact ClusterIon.ext h1 h2 h3
    · right; right; exact ClusterIon.ext h1 h2 h3
  · rintro (rfl | rfl | rfl)
    all_goals exact ⟨⟨by decide, by decide, by decide, by decide⟩, by decide⟩

/-- Exhaustive box filter at m/z 783: the unique match is `[C48(E)3 + 3H]³⁺`. -/
theorem ionsAt_783 : ionsAt 783 = {ion783} := by
  ext i
  simp only [ionsAt, Finset.mem_filter, mem_candidateIons, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨ha, hb, hz1, hz2⟩, -, hm⟩
    simp only [ClusterIon.ionMass, ClusterIon.assemblyMass_eq] at hm
    obtain ⟨h1, h2, h3⟩ := mass_eq_783 ha hb hz1 hz2 hm
    exact ClusterIon.ext h1 h2 h3
  · rintro rfl
    exact ⟨⟨by decide, by decide, by decide, by decide⟩, by decide⟩

/-- Exhaustive box filter at m/z 879: the unique match is `[C48(E)2 + 2H]²⁺`. -/
theorem ionsAt_879 : ionsAt 879 = {ion879} := by
  ext i
  simp only [ionsAt, Finset.mem_filter, mem_candidateIons, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨ha, hb, hz1, hz2⟩, -, hm⟩
    simp only [ClusterIon.ionMass, ClusterIon.assemblyMass_eq] at hm
    obtain ⟨h1, h2, h3⟩ := mass_eq_879 ha hb hz1 hz2 hm
    exact ClusterIon.ext h1 h2 h3
  · rintro rfl
    exact ⟨⟨by decide, by decide, by decide, by decide⟩, by decide⟩

/-- Exhaustive box filter at m/z 1174: the unique match is `[C48(E)3 + 2H]²⁺`. -/
theorem ionsAt_1174 : ionsAt 1174 = {ion1174} := by
  ext i
  simp only [ionsAt, Finset.mem_filter, mem_candidateIons, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨ha, hb, hz1, hz2⟩, -, hm⟩
    simp only [ClusterIon.ionMass, ClusterIon.assemblyMass_eq] at hm
    obtain ⟨h1, h2, h3⟩ := mass_eq_1174 ha hb hz1 hz2 hm
    exact ClusterIon.ext h1 h2 h3
  · rintro rfl
    exact ⟨⟨by decide, by decide, by decide, by decide⟩, by decide⟩

/-- The printed example is consistent with the model: `[E + H]⁺` has m/z 591. -/
theorem exampleIon591_matches : exampleIon591.MatchesMz 591 := by decide

/-- `[C48(E)3 + 3H]³⁺` has m/z (576 + 3·590 + 3)/3 = 2349/3 = 783. -/
theorem ion783_matches : ion783.MatchesMz 783 := by decide

/-- `[C48(E)2 + 2H]²⁺` has m/z (576 + 2·590 + 2)/2 = 1758/2 = 879. -/
theorem ion879_matches : ion879.MatchesMz 879 := by decide

/-- `[C48(E)3 + 2H]²⁺` has m/z (576 + 3·590 + 2)/2 = 2348/2 = 1174. -/
theorem ion1174_matches : ion1174.MatchesMz 1174 := by decide

/-- Summed ion formula of the printed example: `[C₄₀H₃₅N₂O₃]⁺`. -/
theorem exampleIon591_formula : exampleIon591.ionFormula = ⟨40, 35, 2, 3⟩ := rfl

/-- Summed ion formula of the m/z 783 ion: `[C₁₆₈H₁₀₅N₆O₉]³⁺`. -/
theorem ion783_formula : ion783.ionFormula = ⟨168, 105, 6, 9⟩ := rfl

/-- Summed ion formula of the m/z 879 ion: `[C₁₂₈H₇₀N₄O₆]²⁺`. -/
theorem ion879_formula : ion879.ionFormula = ⟨128, 70, 4, 6⟩ := rfl

/-- Summed ion formula of the m/z 1174 ion: `[C₁₆₈H₁₀₄N₆O₉]²⁺`. -/
theorem ion1174_formula : ion1174.ionFormula = ⟨168, 104, 6, 9⟩ := rfl

/-- Raw-result specification: the integer-mass data, the printed-example anchor, and the
exhaustive box filter that derives each ion assignment. -/
def IonIdentitiesRawSpec : Prop :=
  cycloC48.integerMass = 576
    ∧ macrocycleE.integerMass = 590
    ∧ exampleIon591.MatchesMz 591
    ∧ ionsAt 591 = {exampleIon591, ⟨0, 2, 2⟩, ⟨0, 3, 3⟩}
    ∧ ionsAt 783 = {ion783}
    ∧ ionsAt 879 = {ion879}
    ∧ ionsAt 1174 = {ion1174}

/-- Reported-result specification covering the three requested outputs `ion_783`, `ion_879`,
`ion_1174`: the identity of each ion as a concrete protonated intact assembly, with its m/z
match and its summed ion formula (the charge state is the assembly's proton count). -/
def IonIdentitiesReportedSpec : Prop :=
  (ion783.MatchesMz 783 ∧ ion783.ionFormula = ⟨168, 105, 6, 9⟩)
    ∧ (ion879.MatchesMz 879 ∧ ion879.ionFormula = ⟨128, 70, 4, 6⟩)
    ∧ (ion1174.MatchesMz 1174 ∧ ion1174.ionFormula = ⟨168, 104, 6, 9⟩)

/-- Raw-result certificate for the answer-blind submission. Its type is the
controller-generated exact contract for role `raw_result`: the role payload digest bound as a
(reflexive) string equation, conjoined with the semantic raw specification
`IonIdentitiesRawSpec`. -/
theorem ion_identities_raw_certificate :
    ("159da402783ecde5633c716dc7e96bb79bf4f5da3dcf1791bc57c646edc3b14a" : String)
      = "159da402783ecde5633c716dc7e96bb79bf4f5da3dcf1791bc57c646edc3b14a"
      ∧ IonIdentitiesRawSpec :=
  ⟨rfl, cycloC48_mass, macrocycleE_mass, exampleIon591_matches, ionsAt_591, ionsAt_783,
    ionsAt_879, ionsAt_1174⟩

/-- Reported-result certificate for the answer-blind submission. Its type is the
controller-generated exact contract for role `reported_result`: the role payload digest bound
as a (reflexive) string equation, conjoined with the semantic reported specification
`IonIdentitiesReportedSpec`. -/
theorem ion_identities_reported_certificate :
    ("a9f1bc9324ec633b003c5fba5807fd190ddad92085c6e463a9873b1c5b1b0a57" : String)
      = "a9f1bc9324ec633b003c5fba5807fd190ddad92085c6e463a9873b1c5b1b0a57"
      ∧ IonIdentitiesReportedSpec :=
  ⟨rfl, ⟨ion783_matches, ion783_formula⟩, ⟨ion879_matches, ion879_formula⟩,
    ⟨ion1174_matches, ion1174_formula⟩⟩

end Icho2026T6A4
