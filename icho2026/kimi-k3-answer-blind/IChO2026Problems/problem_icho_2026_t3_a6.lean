import IChO2026Chem

/-!
# IChO 2026, Problem T3 (Q3-6) — π–π stacking energies of COF-8 bilayer arrangements

**Source contract** (problem_text and problem_image `T3_page-6.png`; structure panels
`T3_page-6.png`; page `T3_page-5.png` inspected for shared context only):

* COF-8 is synthesised from **E1 + D2** by Knoevenagel-type C=C condensation
  (problem_image): D2 is 2,4,6-tris(4-formylphenyl)-1,3,5-triazine (a triazine-core
  node with three para-phenylene arms) and E1 is 1,3,5-tris(cyanomethyl)benzene
  (a benzene-core node with three –CH₂–CN arms).  COF-8 is the honeycomb 2D-COF
  whose vertices alternate between D2-derived nodes (1 triazine ring + 3
  para-phenylene rings) and E1-derived nodes (1 benzene ring), joined by
  –CH=C(CN)– vinylene links.
* π–π interaction energies between stacked aromatic rings are stipulated by the
  printed table (problem_image/problem_text, exact as printed), in kJ mol⁻¹, for
  the two printed geometries — eclipsed face-to-face (first data column) and
  slightly shifted slipped (second data column):

  | pair                 | eclipsed | shifted |
  |----------------------|----------|---------|
  | benzene–benzene (b-b)|  −7.9    | −12.6   |
  | benzene–triazine (b-t)| −49.8   | −55.6   |
  | triazine–triazine (t-t)| −6.7   | −16.7   |

* Stipulated calibration datum (problem_text): the **AA′ slightly shifted** mode of
  a COF-8 bilayer has π–π stacking interaction energy **−67.1 kJ mol⁻¹** between
  two layers of one repeat unit.
* Question 3.6: calculate the π–π stacking energy between two layers of one repeat
  unit of COF-8 for the **AA**, **AB** and **AB′** arrangements, assuming π–π
  stacking happens only between aromatic units.

**Repeat-unit aromatic inventory** (problem_image, COF-8 panel; repeat-unit dashed
convention of the shared context: vertices shared by 3 hexagons, edges by 2).
Per hexagon: 6 vertices × 1/3 = 2 nodes = 1 D2 node (1 triazine + 3 phenylene rings)
+ 1 E1 node (1 benzene ring); the 6 × 1/2 = 3 vinylene links are non-aromatic.
So one repeat unit carries **5 aromatic rings: 4 benzene (b) + 1 triazine (t)**.

**Model validation (calibration).**  In AA′ every aromatic ring stacks, slightly
shifted, over its counterpart: 4 b-b + 1 t-t at the shifted column gives
4·(−12.6) + (−16.7) = −67.1 kJ mol⁻¹, exactly the stipulated datum.  This fixes
the inventory (4 b + 1 t) and binds the second table column to the shifted
geometry; alternatives fail (1 b + 1 t → −29.3; 3 b + 2 t → −71.2; 5 b → −63.0).

**Requested outputs (each to 3 significant figures, ties half away from zero).**

* **AA** (eclipsed, all five ring pairs stacked over their counterparts):
  `E_AA = 4·(−7.9) + (−6.7) = −38.3 kJ mol⁻¹`.
* **AB** (Bernal registry of the honeycomb, problem_image panel (c)): exactly one
  node sublattice of the second layer lies over the first layer's nodes, the other
  over hexagon pore centres; the unique stacked node pair per repeat unit is one
  triazine over one benzene = **1 eclipsed b-t contact** (either registry sense
  gives the same count and kind).  The phenylene arm rings then sit ≈ 0.41 of the
  node–node distance (≈ 4.3 Å) from the nearest first-layer ring, outside either
  printed table geometry, so they contribute nothing:
  `E_AB = −49.8 kJ mol⁻¹`.
* **AB′** (the slightly shifted variant of AB, by the problem's own prime
  convention — AA′ is described as the slightly shifted AA mode): the same single
  b-t node contact per repeat unit at the shifted column:
  `E_AB′ = −55.6 kJ mol⁻¹`.

The two `...Certificate` theorems at the end bind the answer-blind payload digests
to the semantic specifications `RawResultSpec` / `ReportedResultSpec`.
-/

namespace IChO2026.T3.A6

/-- Aromatic ring kinds of COF-8: benzenoid rings (X = CH) and triazine rings
(X = N), the two ring types distinguished in the problem's interaction table
(problem_text, table row labels, `T3_page-6.png`). -/
inductive AromaticRingKind where
  | benzene
  | triazine
  deriving DecidableEq

/-- The two discrete stacking geometries printed in the problem's interaction-energy
table (problem_image, `T3_page-6.png` table header): eclipsed face-to-face stacking
(first data column) and the slightly shifted slipped stacking (second data column).
The problem's own calibration ("the AA′ slightly shifted mode ... −67.1 kJ mol⁻¹")
binds AA′ to the second column and hence AA to the first. -/
inductive StackingGeometry where
  | eclipsed
  | shifted
  deriving DecidableEq

/-- Pairwise π–π interaction energy (kJ mol⁻¹) between two stacked aromatic rings,
by ring kinds and stacking geometry; every value is stipulated by the problem's
interaction table (problem_text/problem_image, `T3_page-6.png`), exact as printed.
The table is symmetric in the two rings, which the `b-t` branches record. -/
def pairEnergy : StackingGeometry → AromaticRingKind → AromaticRingKind → ℝ
  | .eclipsed, .benzene, .benzene => -7.9
  | .eclipsed, .benzene, .triazine => -49.8
  | .eclipsed, .triazine, .benzene => -49.8
  | .eclipsed, .triazine, .triazine => -6.7
  | .shifted, .benzene, .benzene => -12.6
  | .shifted, .benzene, .triazine => -55.6
  | .shifted, .triazine, .benzene => -55.6
  | .shifted, .triazine, .triazine => -16.7

/-- Tally of pairwise aromatic stacking contacts between one repeat unit of each
of the two bilayer layers, by ring-kind pair (b-b, b-t, t-t). -/
structure ContactTally where
  benzeneBenzene : ℕ
  benzeneTriazine : ℕ
  triazineTriazine : ℕ
  deriving DecidableEq

/-- Total π–π stacking energy (kJ mol⁻¹) contributed by a contact tally in a given
geometry: count × stipulated pair energy, summed over the three ring-kind pairs
(problem_text assumption: π–π stacking happens only between aromatic units, so
non-aromatic vinylene links contribute no term). -/
def tallyEnergy (g : StackingGeometry) (t : ContactTally) : ℝ :=
  (t.benzeneBenzene : ℝ) * pairEnergy g .benzene .benzene +
    (t.benzeneTriazine : ℝ) * pairEnergy g .benzene .triazine +
      (t.triazineTriazine : ℝ) * pairEnergy g .triazine .triazine

/-- Benzene-type aromatic rings per COF-8 repeat unit: 3 para-phenylene rings of
the D2-derived node plus the 1 benzene ring of the E1-derived node (problem_image,
COF-8 panel; 1/3 vertex sharing per hexagon). -/
def repeatUnitBenzeneRings : ℕ := 4

/-- Triazine rings per COF-8 repeat unit: the single triazine core of the
D2-derived node (problem_image, COF-8 panel; 1/3 vertex sharing per hexagon). -/
def repeatUnitTriazineRings : ℕ := 1

/-- Contact tally of the AA and AA′ arrangements: every aromatic ring of the second
layer stacks over its counterpart in the first layer, so all five repeat-unit rings
pair up — 4 benzene–benzene and 1 triazine–triazine contacts (problem_image,
panel (a) AA and the stipulated AA′ datum). -/
def aaContactTally : ContactTally where
  benzeneBenzene := repeatUnitBenzeneRings
  benzeneTriazine := 0
  triazineTriazine := repeatUnitTriazineRings

/-- Contact tally of the AB and AB′ arrangements (Bernal registry of the honeycomb,
problem_image panel (c)): one node sublattice of the second layer lies over the
first layer's nodes, the other over hexagon pore centres.  The sublattices are the
triazine (D2) and benzene (E1) nodes, so exactly one node–node pair per repeat unit
stacks, and it is always one triazine with one benzene: 1 benzene–triazine contact,
0 benzene–benzene, 0 triazine–triazine.  The phenylene arm rings project ≈ 0.41 of
the node–node distance away from the nearest first-layer ring (≈ 4.3 Å), outside
either printed interaction geometry, so they contribute no contact. -/
def abContactTally : ContactTally where
  benzeneBenzene := 0
  benzeneTriazine := 1
  triazineTriazine := 0

/-- The stacking arrangements asked about in Q3-6 together with the stipulated AA′
calibration mode.  The prime denotes the slightly shifted (slipped) variant of the
corresponding registry, following the problem's own usage ("the AA′ slightly
shifted mode", problem_text). -/
inductive StackingArrangement where
  | AA
  | AAprime
  | AB
  | ABprime
  deriving DecidableEq

/-- Geometry column of each arrangement: AA and AB stack their contacts eclipsed;
the primed (slightly shifted) modes use the slipped column. -/
def arrangementGeometry : StackingArrangement → StackingGeometry
  | .AA => .eclipsed
  | .AAprime => .shifted
  | .AB => .eclipsed
  | .ABprime => .shifted

/-- Contact tally of each arrangement: AA and AA′ stack all repeat-unit rings;
AB and AB′ stack only the single node–node pair per repeat unit. -/
def arrangementTally : StackingArrangement → ContactTally
  | .AA => aaContactTally
  | .AAprime => aaContactTally
  | .AB => abContactTally
  | .ABprime => abContactTally

/-- π–π stacking energy (kJ mol⁻¹) between two layers of one repeat unit of COF-8
in a given arrangement: the tally energy at the arrangement's geometry. -/
def stackingEnergy (s : StackingArrangement) : ℝ :=
  tallyEnergy (arrangementGeometry s) (arrangementTally s)

/-- Raw π–π stacking energy of the AA arrangement (kJ mol⁻¹). -/
def stackingEnergyAA : ℝ := stackingEnergy .AA

/-- Raw π–π stacking energy of the AB arrangement (kJ mol⁻¹). -/
def stackingEnergyAB : ℝ := stackingEnergy .AB

/-- Raw π–π stacking energy of the AB′ arrangement (kJ mol⁻¹). -/
def stackingEnergyABprime : ℝ := stackingEnergy .ABprime

/-- Raw π–π stacking energy of the stipulated AA′ slightly shifted calibration mode
(kJ mol⁻¹). -/
def stackingEnergyAAprime : ℝ := stackingEnergy .AAprime

/-- Problem-stipulated calibration datum (problem_text, `T3_page-6.png`): the AA′
slightly shifted mode of a COF-8 bilayer has π–π stacking interaction energy
−67.1 kJ mol⁻¹ between two layers of one repeat unit. -/
def givenAAprimeEnergy : ℝ := -67.1

/-- The AA contact count exhausts the repeat-unit aromatic inventory:
4 + 0 + 1 = 4 + 1 rings. -/
theorem aaContactTally_covers_repeat_unit :
    aaContactTally.benzeneBenzene + aaContactTally.benzeneTriazine +
        aaContactTally.triazineTriazine =
      repeatUnitBenzeneRings + repeatUnitTriazineRings := rfl

/-- The AA contact tally is 4 b-b, 0 b-t, 1 t-t. -/
theorem aaContactTally_eq : aaContactTally = ⟨4, 0, 1⟩ := rfl

/-- The AB contact tally is 0 b-b, 1 b-t, 0 t-t. -/
theorem abContactTally_eq : abContactTally = ⟨0, 1, 0⟩ := rfl

/-- **Exact value of the AA stacking energy**: `4·(−7.9) + (−6.7) = −38.3 kJ mol⁻¹`. -/
theorem stackingEnergyAA_value : stackingEnergyAA = (-38.3 : ℝ) := by
  norm_num [stackingEnergyAA, stackingEnergy, arrangementGeometry, arrangementTally,
    tallyEnergy, aaContactTally, pairEnergy, repeatUnitBenzeneRings, repeatUnitTriazineRings]

/-- **Exact value of the AB stacking energy**: one eclipsed benzene–triazine node
contact per repeat unit, `−49.8 kJ mol⁻¹`. -/
theorem stackingEnergyAB_value : stackingEnergyAB = (-49.8 : ℝ) := by
  norm_num [stackingEnergyAB, stackingEnergy, arrangementGeometry, arrangementTally,
    tallyEnergy, abContactTally, pairEnergy]

/-- **Exact value of the AB′ stacking energy**: the same single benzene–triazine
node contact per repeat unit at the shifted geometry, `−55.6 kJ mol⁻¹`. -/
theorem stackingEnergyABprime_value : stackingEnergyABprime = (-55.6 : ℝ) := by
  norm_num [stackingEnergyABprime, stackingEnergy, arrangementGeometry, arrangementTally,
    tallyEnergy, abContactTally, pairEnergy]

/-- **Model validation (calibration)**: the same counting model applied to the AA′
slightly shifted mode gives `4·(−12.6) + (−16.7) = −67.1 kJ mol⁻¹`, exactly the
problem-stipulated datum. -/
theorem aaPrime_calibration : stackingEnergyAAprime = givenAAprimeEnergy := by
  norm_num [stackingEnergyAAprime, givenAAprimeEnergy, stackingEnergy, arrangementGeometry,
    arrangementTally, tallyEnergy, aaContactTally, pairEnergy, repeatUnitBenzeneRings,
    repeatUnitTriazineRings]

/-- Certified non-degenerate rational interval for the AA energy. -/
theorem stackingEnergyAA_interval :
    (-38.4 : ℝ) ≤ stackingEnergyAA ∧ stackingEnergyAA ≤ (-38.2 : ℝ) := by
  rw [stackingEnergyAA_value]; constructor <;> norm_num

/-- Certified non-degenerate rational interval for the AB energy. -/
theorem stackingEnergyAB_interval :
    (-49.9 : ℝ) ≤ stackingEnergyAB ∧ stackingEnergyAB ≤ (-49.7 : ℝ) := by
  rw [stackingEnergyAB_value]; constructor <;> norm_num

/-- Certified non-degenerate rational interval for the AB′ energy. -/
theorem stackingEnergyABprime_interval :
    (-55.7 : ℝ) ≤ stackingEnergyABprime ∧ stackingEnergyABprime ≤ (-55.5 : ℝ) := by
  rw [stackingEnergyABprime_value]; constructor <;> norm_num

/-- The AA counting formula as an unrounded expression over the stipulated table:
`E_AA = 4·(b-b eclipsed) + (t-t eclipsed)`. -/
theorem stackingEnergyAA_formula :
    stackingEnergyAA =
      4 * pairEnergy .eclipsed .benzene .benzene + pairEnergy .eclipsed .triazine .triazine := by
  norm_num [stackingEnergyAA, stackingEnergy, arrangementGeometry, arrangementTally,
    tallyEnergy, aaContactTally, pairEnergy, repeatUnitBenzeneRings, repeatUnitTriazineRings]

/-- The AB counting formula: `E_AB = (b-t eclipsed)`. -/
theorem stackingEnergyAB_formula :
    stackingEnergyAB = pairEnergy .eclipsed .benzene .triazine := by
  norm_num [stackingEnergyAB, stackingEnergy, arrangementGeometry, arrangementTally,
    tallyEnergy, abContactTally, pairEnergy]

/-- The AB′ counting formula: `E_AB′ = (b-t shifted)`. -/
theorem stackingEnergyABprime_formula :
    stackingEnergyABprime = pairEnergy .shifted .benzene .triazine := by
  norm_num [stackingEnergyABprime, stackingEnergy, arrangementGeometry, arrangementTally,
    tallyEnergy, abContactTally, pairEnergy]

/-- Reporting certificate for AA: at the three-significant-figure quantum
`0.1 kJ mol⁻¹` (magnitude in [10, 100); ties half away from zero), the raw value
`−38.3` is reported as `−38.3`. -/
theorem stackingEnergyAA_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum stackingEnergyAA (-38.3 : ℝ) (0.1 : ℝ) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  rw [stackingEnergyAA_value]
  refine ⟨by norm_num, ⟨-383, by norm_num⟩, ?_⟩
  split_ifs with hpos
  · norm_num at hpos
  · constructor <;> norm_num

/-- Reporting certificate for AB: at the three-significant-figure quantum
`0.1 kJ mol⁻¹`, the raw value `−49.8` is reported as `−49.8`. -/
theorem stackingEnergyAB_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum stackingEnergyAB (-49.8 : ℝ) (0.1 : ℝ) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  rw [stackingEnergyAB_value]
  refine ⟨by norm_num, ⟨-498, by norm_num⟩, ?_⟩
  split_ifs with hpos
  · norm_num at hpos
  · constructor <;> norm_num

/-- Reporting certificate for AB′: at the three-significant-figure quantum
`0.1 kJ mol⁻¹`, the raw value `−55.6` is reported as `−55.6`. -/
theorem stackingEnergyABprime_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum stackingEnergyABprime (-55.6 : ℝ) (0.1 : ℝ) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  rw [stackingEnergyABprime_value]
  refine ⟨by norm_num, ⟨-556, by norm_num⟩, ?_⟩
  split_ifs with hpos
  · norm_num at hpos
  · constructor <;> norm_num

/-- **Raw result specification** (answer-blind, all three requested outputs before
any reporting rounding): the unrounded counting formulas over the stipulated table,
the exact rational values, certified non-degenerate rational intervals, and the
calibration of the model against the problem-stipulated AA′ datum. -/
def RawResultSpec : Prop :=
  stackingEnergyAA =
      4 * pairEnergy .eclipsed .benzene .benzene + pairEnergy .eclipsed .triazine .triazine ∧
    stackingEnergyAB = pairEnergy .eclipsed .benzene .triazine ∧
    stackingEnergyABprime = pairEnergy .shifted .benzene .triazine ∧
    stackingEnergyAA = (-38.3 : ℝ) ∧
    stackingEnergyAB = (-49.8 : ℝ) ∧
    stackingEnergyABprime = (-55.6 : ℝ) ∧
    ((-38.4 : ℝ) ≤ stackingEnergyAA ∧ stackingEnergyAA ≤ (-38.2 : ℝ)) ∧
    ((-49.9 : ℝ) ≤ stackingEnergyAB ∧ stackingEnergyAB ≤ (-49.7 : ℝ)) ∧
    ((-55.7 : ℝ) ≤ stackingEnergyABprime ∧ stackingEnergyABprime ≤ (-55.5 : ℝ)) ∧
    stackingEnergyAAprime = givenAAprimeEnergy

/-- **Reported result specification** (answer-blind): each of the three requested
stacking energies reported at its three-significant-figure quantum `0.1 kJ mol⁻¹`
(ties half away from zero). -/
def ReportedResultSpec : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum stackingEnergyAA (-38.3 : ℝ) (0.1 : ℝ) ∧
    IChO2026Chem.Reporting.ReportsAtQuantum stackingEnergyAB (-49.8 : ℝ) (0.1 : ℝ) ∧
    IChO2026Chem.Reporting.ReportsAtQuantum stackingEnergyABprime (-55.6 : ℝ) (0.1 : ℝ)

/-- The raw specification is satisfied by the derivation above. -/
theorem rawResultSpecHolds : RawResultSpec := by
  exact ⟨stackingEnergyAA_formula, stackingEnergyAB_formula, stackingEnergyABprime_formula,
    stackingEnergyAA_value, stackingEnergyAB_value, stackingEnergyABprime_value,
    stackingEnergyAA_interval, stackingEnergyAB_interval, stackingEnergyABprime_interval,
    aaPrime_calibration⟩

/-- The reported specification is satisfied by the three reporting certificates. -/
theorem reportedResultSpecHolds : ReportedResultSpec :=
  ⟨stackingEnergyAA_reported, stackingEnergyAB_reported, stackingEnergyABprime_reported⟩

/-- Raw result certificate: binds the answer-blind raw-role payload digest to
`RawResultSpec`. -/
theorem rawResultCertificate :
    ("2b6a7610d1f77159103e9ed66dfc42e192e4a5905339243f1502ba6ab46da883" : String)
      = "2b6a7610d1f77159103e9ed66dfc42e192e4a5905339243f1502ba6ab46da883"
      ∧ RawResultSpec :=
  ⟨rfl, rawResultSpecHolds⟩

/-- Reported result certificate: binds the answer-blind reported-role payload digest
to `ReportedResultSpec`. -/
theorem reportedResultCertificate :
    ("2e8757f1729c840a30968e50828f5c0dfb1ac63fde5afe8456a9644dc6b8d1df" : String)
      = "2e8757f1729c840a30968e50828f5c0dfb1ac63fde5afe8456a9644dc6b8d1df"
      ∧ ReportedResultSpec :=
  ⟨rfl, reportedResultSpecHolds⟩

end IChO2026.T3.A6
