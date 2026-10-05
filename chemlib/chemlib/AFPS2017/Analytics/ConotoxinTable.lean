import AFPS2017.Analytics.MassAgreement

/-!
# Source-addressed conotoxin mass table

The 25 expected and observed masses below are transcribed row by row from
`afps2017.supplement:Supplementary-Figure-8` in the public supplement with
content identifier
`afps2017.supplement:sha256-f7baa2cd59141ec38d95c9980e60117b596a9a78a9f4cbd4ae4e2cd4a2c8044e`.
Expected and observed displayed precisions are recorded independently, and the
source does not specify a product form for these table entries.

The checked table establishes only exact arithmetic facts about the displayed
masses: entry 14 attains the independently computed maximum absolute residual
of `0.193` Da, and every residual is at most `0.2` Da. It makes no conclusion
about molecular identity, structure, purity, folding, or yield.
-/

namespace AFPS2017.Analytics

/--
The 25 Supplementary Figure 8 rows together with a finite, exact check that
their maximum displayed-mass residual is `0.193` Da.
-/
noncomputable def checkedConotoxinMassData : ConotoxinMassCheck := by
  let row (locator : String) (expected observed : ℝ)
      (expected_nonnegative : 0 ≤ expected) (observed_nonnegative : 0 ≤ observed)
      (expectedDecimalPlaces observedDecimalPlaces : Nat) :
      ReportedDatum MassObservation :=
    { source := afps2017Supplement locator
      value :=
        { expectedMass := ofDaltons expected expected_nonnegative
          observedMass := ofDaltons observed observed_nonnegative
          productForm := .unspecified
          displayedPrecision :=
            { expectedDecimalPlaces := expectedDecimalPlaces
              observedDecimalPlaces := observedDecimalPlaces } } }
  let rows : Fin 25 → ReportedDatum MassObservation := ![
    row "Supplementary-Figure-8: entry 1" (1252435 / 1000) (125244 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 2" (1477583 / 1000) (147757 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 3" (1450572 / 1000) (145058 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 4" (1498503 / 1000) (149852 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 5" (1702803 / 1000) (17028 / 10)
      (by norm_num) (by norm_num) 3 1,
    row "Supplementary-Figure-8: entry 6" (1516489 / 1000) (15165 / 10)
      (by norm_num) (by norm_num) 3 1,
    row "Supplementary-Figure-8: entry 7" (93229 / 100) (93228 / 100)
      (by norm_num) (by norm_num) 2 2,
    row "Supplementary-Figure-8: entry 8" (1396402 / 1000) (139641 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 9" (129441 / 100) (129441 / 100)
      (by norm_num) (by norm_num) 2 2,
    row "Supplementary-Figure-8: entry 10" (1645745 / 1000) (164577 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 11" (951362 / 1000) (95134 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 12" (1746507 / 1000) (174652 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 13" (1738647 / 1000) (173866 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 14" (2156723 / 1000) (215653 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 15" (1840684 / 1000) (18407 / 10)
      (by norm_num) (by norm_num) 3 1,
    row "Supplementary-Figure-8: entry 16" (172859 / 100) (172856 / 100)
      (by norm_num) (by norm_num) 2 2,
    row "Supplementary-Figure-8: entry 17" (1854699 / 1000) (185471 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 18" (2028628 / 1000) (202861 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 19" (1596548 / 1000) (159656 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 20" (2820162 / 1000) (282002 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 21" (1832627 / 1000) (183259 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 22" (2763141 / 1000) 2763
      (by norm_num) (by norm_num) 3 0,
    row "Supplementary-Figure-8: entry 23" (993358 / 1000) (99338 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 24" (2491992 / 1000) (249197 / 100)
      (by norm_num) (by norm_num) 3 2,
    row "Supplementary-Figure-8: entry 25" (1800786 / 1000) (180079 / 100)
      (by norm_num) (by norm_num) 3 2]
  let table : CheckedConotoxinTable :=
    { rows := rows
      agreementAt := fun i =>
        { toleranceDaltons := 193 / 1000
          tolerance_nonnegative := by norm_num
          residual_le_tolerance := by
            fin_cases i <;>
              norm_num [rows, row, massResidualDaltons, ofDaltons,
                Chemlib.Units.NonnegativeQuantity.ofReal,
                Chemlib.Units.Quantity.ofReal] }
      maximumResidualDaltons := 193 / 1000
      maximum_attained := by
        refine ⟨⟨13, by norm_num⟩, ?_⟩
        norm_num [rows, row, massResidualDaltons, ofDaltons,
          Chemlib.Units.NonnegativeQuantity.ofReal,
          Chemlib.Units.Quantity.ofReal]
      maximum_nonnegative := by norm_num
      residual_le_maximum := by
        intro i
        fin_cases i <;>
          norm_num [rows, row, massResidualDaltons, ofDaltons,
            Chemlib.Units.NonnegativeQuantity.ofReal,
            Chemlib.Units.Quantity.ofReal] }
  exact
    { table := table
      computedMaximum_eq_reported := by
        norm_num [table, reportedConotoxinMaximumResidual] }

/-- The checked 25-row conotoxin mass table. -/
noncomputable def checkedConotoxinMassTable : CheckedConotoxinTable :=
  checkedConotoxinMassData.table

/-- The source-addressed rows of the checked conotoxin mass table. -/
noncomputable def conotoxinMassRows : Fin 25 → ReportedDatum MassObservation :=
  checkedConotoxinMassTable.rows

/-- Every transcribed conotoxin mass row has displayed-mass residual at most `0.2` Da. -/
theorem conotoxinMassRows_all_within_pointTwo :
    ∀ i : Fin 25, massResidualDaltons (conotoxinMassRows i).value ≤ (1 / 5 : ℝ) := by
  exact conotoxin_all_within_pointTwo checkedConotoxinMassData

end AFPS2017.Analytics
