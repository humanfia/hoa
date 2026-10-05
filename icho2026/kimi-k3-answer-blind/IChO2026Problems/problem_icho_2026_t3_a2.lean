import IChO2026Chem

/-!
# IChO 2026, Problem T3 (Q3-2) — Internal diameter of the COF-2 honeycomb

**Source contract** (problem_text, Q3-2 box on `T3_page-2.png`; COF-2 topology
panel on `T3_page-1.png`):

* COF-2 is the honeycomb 2D-COF whose vertices are boroxine (B₃O₃) rings and
  whose edges are single para-phenylene linkers (building block A2,
  benzene-1,4-diboronic acid, self-condenses to boroxine rings, −H₂O).
* Stipulated bond lengths (exact as printed): C–C/C=C (arenes) = 1.39 Å,
  C–B = 1.56 Å, B–O = 1.38 Å.
* The diameter `d` of the circle inscribed in a hexagon of side `a` is
  `d = √3 * a`.
* Neglect the width of the linkers.

**Derivation (answer-blind, no intermediate rounding).** One side of the pore
hexagon runs from the centre of one boroxine vertex ring to the centre of the
next: ring centre → B vertex (the radius of a regular hexagon equals its side,
here the B–O bond 1.38 Å), B–C bond (1.56 Å), para span of the benzene linker
(two aromatic C–C bonds, 2·1.39 Å), C–B bond (1.56 Å), B → ring centre
(1.38 Å). Hence `a = 2·1.38 + 2·1.56 + 2·1.39 = 8.66 Å` and
`d = 8.66·√3 Å ≈ 14.99956 Å`, which reports to `15.0 Å` at three significant
figures (ties half away from zero; quantum 0.1 Å).
-/

namespace IChO2026.T3.A2

/-- Problem-stipulated aromatic C–C/C=C bond length in ångström, exact as
printed (problem_text, Q3-2 bullet 1). -/
def bondLengthCC : ℝ := 1.39

/-- Problem-stipulated C–B bond length in ångström, exact as printed
(problem_text, Q3-2 bullet 2). -/
def bondLengthCB : ℝ := 1.56

/-- Problem-stipulated B–O bond length in ångström, exact as printed
(problem_text, Q3-2 bullet 3). -/
def bondLengthBO : ℝ := 1.38

/-- Radius (centre-to-boron distance) of a boroxine B₃O₃ vertex ring. The ring
is a regular hexagon whose every edge is a B–O bond, so its centre-to-vertex
distance equals the B–O bond length (trusted_general_law: regular-hexagon
radius equals side length). -/
def boroxineVertexRadius : ℝ := bondLengthBO

/-- Distance between the two para carbons of a benzene linker: a benzene ring
is a regular hexagon of side `bondLengthCC`, so its para span is two side
lengths (trusted_general_law: regular-hexagon diameter is twice the side). -/
def phenyleneParaSpan : ℝ := 2 * bondLengthCC

/-- Side length `a` of the COF-2 pore hexagon (problem_image, `T3_page-1.png`
COF-2 panel): boroxine centre → B → para-phenylene → B → boroxine centre, with
linker widths neglected (problem_text). -/
def cof2HoneycombSide : ℝ :=
  boroxineVertexRadius + bondLengthCB + phenyleneParaSpan + bondLengthCB + boroxineVertexRadius

/-- Internal diameter `d` of the COF-2 honeycomb via the problem-stipulated
inscribed-circle relation `d = √3 * a`. -/
noncomputable def cof2InternalDiameter : ℝ := Real.sqrt 3 * cof2HoneycombSide

/-- Raw derivation specification: the pore side decomposes into the three
stipulated bond lengths, the diameter is `√3` times the side, and the
unrounded value lies in the strict rational interval (14.99, 15.00) Å. -/
def RawDiameterSpec : Prop :=
  cof2HoneycombSide = 2 * bondLengthBO + 2 * bondLengthCB + 2 * bondLengthCC ∧
    cof2InternalDiameter = Real.sqrt 3 * cof2HoneycombSide ∧
    (14.99 : ℝ) < cof2InternalDiameter ∧ cof2InternalDiameter < (15.00 : ℝ)

/-- The pore side decomposes into the stipulated bond lengths:
`a = 2·(B–O) + 2·(C–B) + 2·(C–C)`. -/
theorem cof2HoneycombSide_eq :
    cof2HoneycombSide = 2 * bondLengthBO + 2 * bondLengthCB + 2 * bondLengthCC := by
  unfold cof2HoneycombSide boroxineVertexRadius phenyleneParaSpan
  ring

/-- Numerically the pore side is exactly 8.66 Å under the stipulated
constants. -/
theorem cof2HoneycombSide_value : cof2HoneycombSide = (8.66 : ℝ) := by
  rw [cof2HoneycombSide_eq]
  unfold bondLengthBO bondLengthCB bondLengthCC
  norm_num

/-- The internal diameter is strictly positive. -/
theorem cof2InternalDiameter_pos : 0 < cof2InternalDiameter := by
  have hside : (0 : ℝ) < cof2HoneycombSide := by
    rw [cof2HoneycombSide_value]
    norm_num
  unfold cof2InternalDiameter
  exact mul_pos (Real.sqrt_pos.2 (by norm_num)) hside

/-- Certified strict rational bounds for the unrounded diameter:
`14.99 < 8.66·√3 < 15.00`, since `(14.99/8.66)² < 3 < (15/8.66)²`. -/
theorem cof2InternalDiameter_bounds :
    (14.99 : ℝ) < cof2InternalDiameter ∧ cof2InternalDiameter < (15.00 : ℝ) := by
  have hval : cof2InternalDiameter = Real.sqrt 3 * (8.66 : ℝ) := by
    unfold cof2InternalDiameter
    rw [cof2HoneycombSide_value]
  have hsq : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  rw [hval]
  constructor <;> nlinarith [hsq, hnn]

/-- **Raw result contract** (answer-blind): the derivation specification
`RawDiameterSpec` holds for the source-derived raw expression
`cof2InternalDiameter = 8.66·√3`, together with the certified non-degenerate
interval `1499/100 ≤ d ≤ 15`. -/
theorem raw_result_contract :
    (IChO2026.T3.A2.RawDiameterSpec) ∧
      (((1499 : ℝ) / 100) ≤ (IChO2026.T3.A2.cof2InternalDiameter) ∧
        (IChO2026.T3.A2.cof2InternalDiameter) ≤ (15 : ℝ)) := by
  refine ⟨⟨cof2HoneycombSide_eq, rfl, cof2InternalDiameter_bounds.1,
      cof2InternalDiameter_bounds.2⟩, ?_, ?_⟩ <;>
    linarith [cof2InternalDiameter_bounds.1, cof2InternalDiameter_bounds.2]

/-- **Reported result contract** (answer-blind): the reported value `15.0 Å`
is the nearest multiple of the three-significant-figure quantum `0.1 Å` to the
raw value `8.66·√3 ≈ 14.99956 Å` (ties half away from zero). -/
theorem reported_result_contract :
    IChO2026Chem.Reporting.ReportsAtQuantum (IChO2026.T3.A2.cof2InternalDiameter)
      ((150 : ℝ) / 10) ((1 : ℝ) / 10) := by
  have hraw : (0 : ℝ) ≤ IChO2026.T3.A2.cof2InternalDiameter :=
    le_of_lt cof2InternalDiameter_pos
  refine ⟨by norm_num, ⟨150, by norm_num⟩, ?_⟩
  rw [if_pos hraw]
  constructor <;> linarith [cof2InternalDiameter_bounds.1, cof2InternalDiameter_bounds.2]

end IChO2026.T3.A2
