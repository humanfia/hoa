import AFPS2017.Analytics.MassObservation

/-!
# Arithmetic mass-agreement certificates

This module implements the narrow arithmetic contract recorded by
`afps2017.analytics.contract:question`. The ALFALFA 750.43/750.43 fields are
transcribed from `afps2017.supplement:Supplementary-Figure-1A`. The
source-addressed 0.193 Da datum is independently computed from the 25 rows in
`afps2017.supplement:Supplementary-Figure-8`. Both locations are in the
supplement identified by
`afps2017.supplement:sha256-f7baa2cd59141ec38d95c9980e60117b596a9a78a9f4cbd4ae4e2cd4a2c8044e`.

A `MassAgreementCert` proves only that an absolute displayed-mass residual is
within an explicit nonnegative tolerance. Likewise, a `CheckedMassTable` carries
both a rowwise upper-bound proof and a proof that some row attains its stated
maximum. Consequently, the source-addressed derived `0.193` Da value alone
proves no claim about
an unverified table. None of these certificates establishes sequence identity,
product identity, structure, purity, or yield.
-/

namespace AFPS2017.Analytics

/-- A certificate that one reported mass observation is within a stated tolerance. -/
structure MassAgreementCert (datum : ReportedDatum MassObservation) : Type where
  /-- The absolute tolerance, measured in daltons. -/
  toleranceDaltons : ℝ
  /-- A mass tolerance is nonnegative. -/
  tolerance_nonnegative : 0 ≤ toleranceDaltons
  /-- The displayed-mass residual is bounded by the stated tolerance. -/
  residual_le_tolerance : massResidualDaltons datum.value ≤ toleranceDaltons

/--
A finite reported-mass table together with the arithmetic evidence needed to
justify its stated maximum residual.
-/
structure CheckedMassTable (n : Nat) : Type where
  /-- The source-addressed rows of the table. -/
  rows : Fin n → ReportedDatum MassObservation
  /-- Each row has its own explicit mass-agreement certificate. -/
  agreementAt : (i : Fin n) → MassAgreementCert (rows i)
  /-- The table's checked maximum absolute residual, measured in daltons. -/
  maximumResidualDaltons : ℝ
  /-- At least one row attains the checked maximum. -/
  maximum_attained :
    ∃ i, massResidualDaltons (rows i).value = maximumResidualDaltons
  /-- The checked maximum is nonnegative. -/
  maximum_nonnegative : 0 ≤ maximumResidualDaltons
  /-- Every row's residual is bounded by the checked maximum. -/
  residual_le_maximum :
    (i : Fin n) → massResidualDaltons (rows i).value ≤ maximumResidualDaltons

/-- A checked table for the 25 conotoxin rows in the public supplement. -/
abbrev CheckedConotoxinTable : Type := CheckedMassTable 25

/-- A bound on a checked maximum gives the same bound for every table row. -/
theorem CheckedMassTable.within_of_maximum_le {n : Nat}
    (table : CheckedMassTable n) {toleranceDaltons : ℝ}
    (maximum_le : table.maximumResidualDaltons ≤ toleranceDaltons) :
    ∀ i, massResidualDaltons (table.rows i).value ≤ toleranceDaltons := by
  intro i
  exact le_trans (table.residual_le_maximum i) maximum_le

/--
The ALFALFA-CONH2 mass record transcribed from Supplementary Figure 1A, with
expected and observed displayed masses both equal to 750.43 Da.
-/
noncomputable def alfalfaMassObservation : ReportedDatum MassObservation :=
  { source := afps2017Supplement "Supplementary-Figure-1A: ALFALFA-CONH2 mass"
    value :=
      { expectedMass := ofDaltons (75043 / 100) (by norm_num)
        observedMass := ofDaltons (75043 / 100) (by norm_num)
        productForm := .unspecified
        displayedPrecision :=
          { expectedDecimalPlaces := 2
            observedDecimalPlaces := 2 } } }

/-- The equal displayed ALFALFA-CONH2 masses have residual zero. -/
theorem alfalfa_massResidual_eq_zero :
    massResidualDaltons alfalfaMassObservation.value = 0 := by
  norm_num [massResidualDaltons, alfalfaMassObservation, ofDaltons,
    Chemlib.Units.NonnegativeQuantity.ofReal,
    Chemlib.Units.Quantity.ofReal]

/-- The ALFALFA-CONH2 observation agrees at zero-dalton tolerance. -/
def alfalfaMassAgreement : MassAgreementCert alfalfaMassObservation :=
  { toleranceDaltons := 0
    tolerance_nonnegative := by norm_num
    residual_le_tolerance := by
      rw [alfalfa_massResidual_eq_zero] }

/-- The source-addressed maximum independently computed from the 25 conotoxin rows. -/
noncomputable def reportedConotoxinMaximumResidual : ReportedDatum ℝ :=
  { source := afps2017Supplement
      "Supplementary Figure 8, 25-row table; independently computed maximum \
      absolute expected/observed mass residual"
    value := 193 / 1000 }

/--
A checked 25-row conotoxin table whose independently computed maximum agrees
with the source-addressed derived maximum value.
-/
structure ConotoxinMassCheck : Type where
  /-- The checked, source-addressed 25-row table. -/
  table : CheckedConotoxinTable
  /-- The table calculation agrees with the source-addressed derived 0.193 Da maximum. -/
  computedMaximum_eq_reported :
    table.maximumResidualDaltons = reportedConotoxinMaximumResidual.value

/-- Every row of a checked conotoxin table is within 0.2 Da. -/
theorem conotoxin_all_within_pointTwo (check : ConotoxinMassCheck) :
    ∀ i : Fin 25,
      massResidualDaltons (check.table.rows i).value ≤ (1 / 5 : ℝ) := by
  intro i
  calc
    massResidualDaltons (check.table.rows i).value
        ≤ check.table.maximumResidualDaltons :=
      check.table.residual_le_maximum i
    _ = reportedConotoxinMaximumResidual.value :=
      check.computedMaximum_eq_reported
    _ ≤ (1 / 5 : ℝ) := by
      norm_num [reportedConotoxinMaximumResidual]

end AFPS2017.Analytics
