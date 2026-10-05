import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, theory problem 3.6

The energy unit throughout this file is kJ mol⁻¹.  The formalization keeps the
data printed in the question separate from the overlap model read from its
COF-8 and stacking diagrams.  The total energies and their decimal reports are
then proved from those inputs.
-/

namespace IChO2026Problems.T3A6

open IChO2026Chem.Reporting

/-- The two aromatic ring classes distinguished by the source energy table. -/
inductive RingKind
  | benzene
  | triazine
  deriving DecidableEq, Repr

/-- The unprimed (centred) and primed (slipped) table geometries. -/
inductive PairGeometry
  | centred
  | slipped
  deriving DecidableEq, Repr

/-- The four layer arrangements relevant to the source data and question. -/
inductive Arrangement
  | AA
  | AAprime
  | AB
  | ABprime
  deriving DecidableEq, Repr

/--
The five aromatic sites in one repeat unit read from the displayed COF-8
structure: the benzene core of E1, the three phenylene rings of D2, and the
triazine core of D2.
-/
inductive AromaticSite
  | e1CoreBenzene
  | d2Phenylene₁
  | d2Phenylene₂
  | d2Phenylene₃
  | d2CoreTriazine
  deriving DecidableEq, Repr

def ringKind : AromaticSite → RingKind
  | .e1CoreBenzene => .benzene
  | .d2Phenylene₁ => .benzene
  | .d2Phenylene₂ => .benzene
  | .d2Phenylene₃ => .benzene
  | .d2CoreTriazine => .triazine

def repeatUnitSites : List AromaticSite :=
  [.e1CoreBenzene, .d2Phenylene₁, .d2Phenylene₂,
   .d2Phenylene₃, .d2CoreTriazine]

/-! ## Printed problem inputs -/

/--
One entry of the question's interaction-energy table, in kJ mol⁻¹.  The first
geometry column is `centred`; the laterally offset column is `slipped`.
-/
noncomputable def pairEnergy : PairGeometry → RingKind → RingKind → ℝ
  | .centred, .benzene, .benzene => (-79 : ℝ) / 10
  | .centred, .benzene, .triazine => (-498 : ℝ) / 10
  | .centred, .triazine, .benzene => (-498 : ℝ) / 10
  | .centred, .triazine, .triazine => (-67 : ℝ) / 10
  | .slipped, .benzene, .benzene => (-126 : ℝ) / 10
  | .slipped, .benzene, .triazine => (-556 : ℝ) / 10
  | .slipped, .triazine, .benzene => (-556 : ℝ) / 10
  | .slipped, .triazine, .triazine => (-167 : ℝ) / 10

/-! ## Overlap model derived from the source diagrams -/

/-- A prime selects the slipped column of the source table. -/
def geometry : Arrangement → PairGeometry
  | .AA => .centred
  | .AAprime => .slipped
  | .AB => .centred
  | .ABprime => .slipped

/--
Only aromatic sites are included.  AA/AA′ pair every aromatic site with its
counterpart.  The AB translation leaves one E1-benzene/D2-triazine overlap per
repeat area; AB′ is its slipped version.
-/
def overlaps : Arrangement → List (AromaticSite × AromaticSite)
  | .AA => repeatUnitSites.map fun site => (site, site)
  | .AAprime => repeatUnitSites.map fun site => (site, site)
  | .AB => [(.e1CoreBenzene, .d2CoreTriazine)]
  | .ABprime => [(.e1CoreBenzene, .d2CoreTriazine)]

noncomputable def overlapEnergy (a : Arrangement)
    (p : AromaticSite × AromaticSite) : ℝ :=
  pairEnergy (geometry a) (ringKind p.1) (ringKind p.2)

/-- Total π-π energy between the two layers for one repeat unit, in kJ mol⁻¹. -/
noncomputable def totalEnergy (a : Arrangement) : ℝ :=
  ((overlaps a).map (overlapEnergy a)).sum

/-! ## Checks of the inventory and diagram-derived pair enumeration -/

theorem repeat_unit_has_five_aromatic_sites : repeatUnitSites.length = 5 := by
  rfl

theorem repeat_unit_has_four_benzenes :
    (repeatUnitSites.filter fun s => ringKind s = .benzene).length = 4 := by
  rfl

theorem repeat_unit_has_one_triazine :
    (repeatUnitSites.filter fun s => ringKind s = .triazine).length = 1 := by
  rfl

theorem aa_has_five_aromatic_overlaps : (overlaps .AA).length = 5 := by
  rfl

theorem ab_has_one_aromatic_overlap : (overlaps .AB).length = 1 := by
  rfl

theorem pairEnergy_symmetric (g : PairGeometry) (x y : RingKind) :
    pairEnergy g x y = pairEnergy g y x := by
  cases g <;> cases x <;> cases y <;> rfl

/-!
This is the numerical cross-check supplied by the statement itself: the
model must reproduce its stated AA′ energy of −67.1 kJ mol⁻¹.
-/
theorem aa_prime_matches_stated_energy :
    totalEnergy .AAprime = (-671 : ℝ) / 10 := by
  norm_num [totalEnergy, overlaps, overlapEnergy, repeatUnitSites, pairEnergy,
    geometry, ringKind]

/-! ## Requested raw outputs -/

/-- AA: `4 × (−7.9) + 1 × (−6.7) = −38.3` kJ mol⁻¹. -/
theorem stacking_energy_aa : totalEnergy .AA = (-383 : ℝ) / 10 := by
  norm_num [totalEnergy, overlaps, overlapEnergy, repeatUnitSites, pairEnergy,
    geometry, ringKind]

/-- AB: one centred benzene-triazine pair gives `−49.8` kJ mol⁻¹. -/
theorem stacking_energy_ab : totalEnergy .AB = (-498 : ℝ) / 10 := by
  norm_num [totalEnergy, overlaps, overlapEnergy, pairEnergy, geometry, ringKind]

/-- AB′: one slipped benzene-triazine pair gives `−55.6` kJ mol⁻¹. -/
theorem stacking_energy_ab_prime :
    totalEnergy .ABprime = (-556 : ℝ) / 10 := by
  norm_num [totalEnergy, overlaps, overlapEnergy, pairEnergy, geometry, ringKind]

/-! ## Three-significant-figure reporting certificates -/

noncomputable def aaSubmission : NumericSubmission where
  rawValue := totalEnergy .AA
  reportedValue := (-383 : ℝ) / 10
  reportingQuantum := (1 : ℝ) / 10

noncomputable def abSubmission : NumericSubmission where
  rawValue := totalEnergy .AB
  reportedValue := (-498 : ℝ) / 10
  reportingQuantum := (1 : ℝ) / 10

noncomputable def abPrimeSubmission : NumericSubmission where
  rawValue := totalEnergy .ABprime
  reportedValue := (-556 : ℝ) / 10
  reportingQuantum := (1 : ℝ) / 10

theorem aa_submission_valid :
    ValidNumericSubmission ((-383 : ℝ) / 10) aaSubmission := by
  rw [ValidNumericSubmission]
  constructor
  · exact stacking_energy_aa
  · change ReportsAtQuantum (totalEnergy .AA) ((-383 : ℝ) / 10) ((1 : ℝ) / 10)
    rw [stacking_energy_aa, ReportsAtQuantum]
    refine ⟨by norm_num, ?_, ?_⟩
    · exact ⟨(-383 : ℤ), by norm_num⟩
    · norm_num

theorem ab_submission_valid :
    ValidNumericSubmission ((-498 : ℝ) / 10) abSubmission := by
  rw [ValidNumericSubmission]
  constructor
  · exact stacking_energy_ab
  · change ReportsAtQuantum (totalEnergy .AB) ((-498 : ℝ) / 10) ((1 : ℝ) / 10)
    rw [stacking_energy_ab, ReportsAtQuantum]
    refine ⟨by norm_num, ?_, ?_⟩
    · exact ⟨(-498 : ℤ), by norm_num⟩
    · norm_num

theorem ab_prime_submission_valid :
    ValidNumericSubmission ((-556 : ℝ) / 10) abPrimeSubmission := by
  rw [ValidNumericSubmission]
  constructor
  · exact stacking_energy_ab_prime
  · change ReportsAtQuantum (totalEnergy .ABprime) ((-556 : ℝ) / 10) ((1 : ℝ) / 10)
    rw [stacking_energy_ab_prime, ReportsAtQuantum]
    refine ⟨by norm_num, ?_, ?_⟩
    · exact ⟨(-556 : ℤ), by norm_num⟩
    · norm_num

#print axioms stacking_energy_aa
#print axioms stacking_energy_ab
#print axioms stacking_energy_ab_prime
#print axioms aa_submission_valid
#print axioms ab_submission_valid
#print axioms ab_prime_submission_valid

end IChO2026Problems.T3A6
