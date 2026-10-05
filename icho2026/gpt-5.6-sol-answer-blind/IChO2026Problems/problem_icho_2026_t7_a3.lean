import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, T7-A3: recycle-loop nitrogen accounting

The source describes a quantitative material stage.  Every cycle receives a
fresh four-mole stoichiometric `N₂ : H₂ = 1 : 3` feed, converts exactly 15% of
the available reactants, removes all produced ammonia by liquefaction, and
recycles only unreacted nitrogen and hydrogen.  The declarations below keep
the species ledger, the recurrence, its geometric closed form, and the final
reporting operation separate.
-/

namespace IChO2026Problems.ProblemIcho2026T7A3

noncomputable section

/-- Species that occur in the source streams relevant to this subproblem. -/
inductive Species where
  | nitrogen
  | hydrogen
  | ammonia
  | carbonDioxide
  deriving DecidableEq, Repr

/-- Phases distinguished by the cooler/liquefaction step in Figure 2. -/
inductive Phase where
  | gas
  | liquid
  deriving DecidableEq, Repr

/-- Every directed stream in the outcome-relevant ammonia loop of Figure 2.
This finite type rules out an unnamed purge or catch-all material stream. -/
inductive LoopStream where
  | freshFeed
  | mixtureTwo
  | recycle
  | separatedAmmonia
  deriving DecidableEq, Repr

/-- Figure 1 identifies mixture M1 as `N₂`, `CO₂`, and `H₂`. -/
def mixtureOneContains (s : Species) : Prop :=
  s = .nitrogen ∨ s = .carbonDioxide ∨ s = .hydrogen

/-- Figure 2 identifies mixture M2, before cooling, as the reactor mixture
containing unreacted `N₂`, unreacted `H₂`, and produced `NH₃`. -/
def mixtureTwoContains (s : Species) : Prop :=
  s = .nitrogen ∨ s = .hydrogen ∨ s = .ammonia

/-- The return line after the cooler contains only unreacted `N₂` and `H₂`. -/
def recycleStreamContains (s : Species) : Prop :=
  s = .nitrogen ∨ s = .hydrogen

/-- The part of T7-A1 needed here is rederived directly from Figures 1 and 2;
no answer from the earlier target is imported. -/
def PreviousPartA1RelevantSpec : Prop :=
  (∀ s, mixtureOneContains s ↔
    s = .nitrogen ∨ s = .carbonDioxide ∨ s = .hydrogen) ∧
  (∀ s, mixtureTwoContains s ↔
    s = .nitrogen ∨ s = .hydrogen ∨ s = .ammonia) ∧
  (∀ s, recycleStreamContains s ↔ s = .nitrogen ∨ s = .hydrogen)

theorem previous_part_a1_relevant_derived : PreviousPartA1RelevantSpec := by
  simp [PreviousPartA1RelevantSpec, mixtureOneContains, mixtureTwoContains,
    recycleStreamContains]

/-- The upstream quantitative balance visible in Figure 1.  Here `x` and `y`
are the printed methane and steam coefficients.  One mole of oxygen consumes
two moles of the methane left after steam reforming, and the final synthesis
feed contains four moles `N₂` and twelve moles `H₂`. -/
def UpstreamQuantitativeBalance (x y : ℝ) : Prop :=
  0 ≤ y ∧
  x - y = 2 ∧
  3 * y + 4 + (y + 2) = 12

/-- This is an inline derivation of the `x,y` relation requested in T7-A1. -/
theorem previous_part_a1_xy_relation {x y : ℝ}
    (h : UpstreamQuantitativeBalance x y) :
    x = 7 / 2 ∧ y = 3 / 2 ∧ x > y := by
  rcases h with ⟨hy, hxy, hbalance⟩
  refine ⟨?_, ?_, ?_⟩
  · norm_num at hbalance ⊢
    linarith
  · norm_num at hbalance ⊢
    linarith
  · linarith

/-- Complete problem-only carrier for the previous-part prerequisite.  The
stream identities are read directly from the labelled arrows in Figure 1,
whereas the relation between `x` and `y` is derived uniformly from the four
quantitative upstream reactions. -/
def PreviousPartA1FullSpec : Prop :=
  PreviousPartA1RelevantSpec ∧
  ∀ x y : ℝ, UpstreamQuantitativeBalance x y → x > y

theorem previous_part_a1_fully_derived : PreviousPartA1FullSpec := by
  refine ⟨previous_part_a1_relevant_derived, ?_⟩
  intro x y h
  exact (previous_part_a1_xy_relation h).2.2

/-- Molar composition of one fresh feed portion. -/
structure FeedComposition where
  totalMoles : ℝ
  nitrogenMoles : ℝ
  hydrogenMoles : ℝ

/-- The problem-stipulated fresh portion for part (a). -/
def freshFeed : FeedComposition where
  totalMoles := 4
  nitrogenMoles := 1
  hydrogenMoles := 3

/-- A nonnegative `N₂ : H₂ = 1 : 3` feed whose component amounts sum to its
total amount. -/
def IsStoichiometricFeed (f : FeedComposition) : Prop :=
  0 ≤ f.nitrogenMoles ∧
  0 ≤ f.hydrogenMoles ∧
  f.totalMoles = f.nitrogenMoles + f.hydrogenMoles ∧
  f.hydrogenMoles = 3 * f.nitrogenMoles

theorem fresh_feed_spec : IsStoichiometricFeed freshFeed := by
  norm_num [IsStoichiometricFeed, freshFeed]

/-- Exact per-cycle conversion stipulated as `η = 0.150`. -/
def perCycleConversion : ℝ := 150 / 1000

/-- Fraction of each available reactant returned after one cycle. -/
def recycleFraction : ℝ := 1 - perCycleConversion

theorem conversion_and_recycle_fraction :
    perCycleConversion = 3 / 20 ∧
    recycleFraction = 17 / 20 ∧
    0 < perCycleConversion ∧ perCycleConversion < 1 := by
  norm_num [perCycleConversion, recycleFraction]

/-- Nitrogen inventory (mol) after `n` completed cycles and before adding the
next fresh portion.  The initial reactor inventory is zero. -/
def nitrogenInventory : ℕ → ℝ
  | 0 => 0
  | n + 1 => recycleFraction * (nitrogenInventory n + freshFeed.nitrogenMoles)

/-- Because every admitted stream is stoichiometric, the returned hydrogen
inventory remains three times the returned nitrogen inventory. -/
def hydrogenInventory (n : ℕ) : ℝ := 3 * nitrogenInventory n

/-- Complete outcome-relevant molar ledger for one reactor/cooler cycle. -/
structure CycleMaterialLedger where
  nitrogenBeforeReaction : ℝ
  hydrogenBeforeReaction : ℝ
  nitrogenReacted : ℝ
  hydrogenReacted : ℝ
  ammoniaProduced : ℝ
  nitrogenRecycled : ℝ
  hydrogenRecycled : ℝ
  ammoniaLiquefied : ℝ

/-- Moles of a named species at a named phase/stream location in Figure 2.
The definition accounts for every constructor of the finite species, phase,
and stream domains. -/
def loopStreamAmount (L : CycleMaterialLedger) :
    LoopStream → Phase → Species → ℝ
  | .freshFeed, .gas, .nitrogen => freshFeed.nitrogenMoles
  | .freshFeed, .gas, .hydrogen => freshFeed.hydrogenMoles
  | .mixtureTwo, .gas, .nitrogen => L.nitrogenRecycled
  | .mixtureTwo, .gas, .hydrogen => L.hydrogenRecycled
  | .mixtureTwo, .gas, .ammonia => L.ammoniaProduced
  | .recycle, .gas, .nitrogen => L.nitrogenRecycled
  | .recycle, .gas, .hydrogen => L.hydrogenRecycled
  | .separatedAmmonia, .liquid, .ammonia => L.ammoniaLiquefied
  | _, _, _ => 0

/-- Source-permitted species/phase locations.  In particular, carbon dioxide
is absent after the scrubber, M2 is a gas stream, the recycle contains only
unreacted reagents, and the separated carrier is liquid ammonia. -/
def StreamLocationAdmissible : LoopStream → Phase → Species → Prop
  | .freshFeed, .gas, .nitrogen => True
  | .freshFeed, .gas, .hydrogen => True
  | .mixtureTwo, .gas, .nitrogen => True
  | .mixtureTwo, .gas, .hydrogen => True
  | .mixtureTwo, .gas, .ammonia => True
  | .recycle, .gas, .nitrogen => True
  | .recycle, .gas, .hydrogen => True
  | .separatedAmmonia, .liquid, .ammonia => True
  | _, _, _ => False

/-- Closed staged-species-domain certificate for one cycle. -/
def LoopStreamDomainSpec (L : CycleMaterialLedger) : Prop :=
  ∀ stream phase species,
    loopStreamAmount L stream phase species ≠ 0 →
      StreamLocationAdmissible stream phase species

theorem loop_stream_domain_closed (L : CycleMaterialLedger) :
    LoopStreamDomainSpec L := by
  intro stream phase species h
  cases stream <;> cases phase <;> cases species <;>
    simp_all [loopStreamAmount, StreamLocationAdmissible]

/-- The ledger for the cycle following `n` already completed cycles. -/
def cycleMaterialLedger (n : ℕ) : CycleMaterialLedger where
  nitrogenBeforeReaction := nitrogenInventory n + freshFeed.nitrogenMoles
  hydrogenBeforeReaction := hydrogenInventory n + freshFeed.hydrogenMoles
  nitrogenReacted :=
    perCycleConversion * (nitrogenInventory n + freshFeed.nitrogenMoles)
  hydrogenReacted :=
    3 * perCycleConversion * (nitrogenInventory n + freshFeed.nitrogenMoles)
  ammoniaProduced :=
    2 * perCycleConversion * (nitrogenInventory n + freshFeed.nitrogenMoles)
  nitrogenRecycled :=
    recycleFraction * (nitrogenInventory n + freshFeed.nitrogenMoles)
  hydrogenRecycled :=
    3 * recycleFraction * (nitrogenInventory n + freshFeed.nitrogenMoles)
  ammoniaLiquefied :=
    2 * perCycleConversion * (nitrogenInventory n + freshFeed.nitrogenMoles)

/-- Conservation, stoichiometry, nonnegativity, and phase-separation contract
for a cycle.  There are no anonymous material streams: the only products in
the ledger are recycled `N₂`, recycled `H₂`, and liquefied `NH₃`. -/
def ValidCycleMaterialLedger (n : ℕ) (L : CycleMaterialLedger) : Prop :=
  0 ≤ L.nitrogenBeforeReaction ∧
  0 ≤ L.hydrogenBeforeReaction ∧
  0 ≤ L.nitrogenReacted ∧
  0 ≤ L.hydrogenReacted ∧
  0 ≤ L.ammoniaProduced ∧
  0 ≤ L.nitrogenRecycled ∧
  0 ≤ L.hydrogenRecycled ∧
  0 ≤ L.ammoniaLiquefied ∧
  L.nitrogenBeforeReaction = nitrogenInventory n + freshFeed.nitrogenMoles ∧
  L.hydrogenBeforeReaction = hydrogenInventory n + freshFeed.hydrogenMoles ∧
  L.nitrogenReacted = perCycleConversion * L.nitrogenBeforeReaction ∧
  L.hydrogenReacted = 3 * L.nitrogenReacted ∧
  L.ammoniaProduced = 2 * L.nitrogenReacted ∧
  L.nitrogenRecycled = L.nitrogenBeforeReaction - L.nitrogenReacted ∧
  L.hydrogenRecycled = L.hydrogenBeforeReaction - L.hydrogenReacted ∧
  L.ammoniaLiquefied = L.ammoniaProduced ∧
  2 * L.nitrogenBeforeReaction =
    2 * L.nitrogenRecycled + L.ammoniaLiquefied ∧
  2 * L.hydrogenBeforeReaction =
    2 * L.hydrogenRecycled + 3 * L.ammoniaLiquefied

/-- A cycle ledger stated over arbitrary inventory functions.  Unlike the
canonical calculator below, this is a genuine source assumption: it fixes the
fresh feed, the 15% conversion of each reagent, Haber--Bosch stoichiometry,
atom conservation, complete ammonia liquefaction, and the closed staged
species/phase domain without mentioning either requested answer. -/
def ValidSourceCycleMaterialLedger
    (nitrogen hydrogen : ℕ → ℝ) (n : ℕ) (L : CycleMaterialLedger) : Prop :=
  0 ≤ nitrogen n ∧
  0 ≤ hydrogen n ∧
  0 ≤ L.nitrogenBeforeReaction ∧
  0 ≤ L.hydrogenBeforeReaction ∧
  0 ≤ L.nitrogenReacted ∧
  0 ≤ L.hydrogenReacted ∧
  0 ≤ L.ammoniaProduced ∧
  0 ≤ L.nitrogenRecycled ∧
  0 ≤ L.hydrogenRecycled ∧
  0 ≤ L.ammoniaLiquefied ∧
  L.nitrogenBeforeReaction = nitrogen n + freshFeed.nitrogenMoles ∧
  L.hydrogenBeforeReaction = hydrogen n + freshFeed.hydrogenMoles ∧
  L.nitrogenReacted = perCycleConversion * L.nitrogenBeforeReaction ∧
  L.hydrogenReacted = perCycleConversion * L.hydrogenBeforeReaction ∧
  L.hydrogenReacted = 3 * L.nitrogenReacted ∧
  L.ammoniaProduced = 2 * L.nitrogenReacted ∧
  L.nitrogenRecycled = L.nitrogenBeforeReaction - L.nitrogenReacted ∧
  L.hydrogenRecycled = L.hydrogenBeforeReaction - L.hydrogenReacted ∧
  L.ammoniaLiquefied = L.ammoniaProduced ∧
  2 * L.nitrogenBeforeReaction =
    2 * L.nitrogenRecycled + L.ammoniaLiquefied ∧
  2 * L.hydrogenBeforeReaction =
    2 * L.hydrogenRecycled + 3 * L.ammoniaLiquefied ∧
  LoopStreamDomainSpec L

/-- All source conditions for the infinite sequence of completed cycles.  The
inventory at index `n` is the gas present after `n` cycles and before adding
portion `n+1`; hence the requested part-(a) value is index 58. -/
def SourceRecycleModel
    (nitrogen hydrogen : ℕ → ℝ) (ledgers : ℕ → CycleMaterialLedger) : Prop :=
  nitrogen 0 = 0 ∧
  hydrogen 0 = 0 ∧
  ∀ n,
    ValidSourceCycleMaterialLedger nitrogen hydrogen n (ledgers n) ∧
    nitrogen (n + 1) = (ledgers n).nitrogenRecycled ∧
    hydrogen (n + 1) = (ledgers n).hydrogenRecycled

lemma nitrogen_inventory_nonnegative (n : ℕ) :
    0 ≤ nitrogenInventory n := by
  induction n with
  | zero => simp [nitrogenInventory]
  | succ n ih =>
      rw [nitrogenInventory]
      have hrecycle : (0 : ℝ) ≤ recycleFraction := by
        norm_num [recycleFraction, perCycleConversion]
      have hfresh : (0 : ℝ) ≤ freshFeed.nitrogenMoles := by
        norm_num [freshFeed]
      positivity

/-- Named quantitative-material-stage carrier used by both requested outputs. -/
theorem cycle_material_ledger_valid (n : ℕ) :
    ValidCycleMaterialLedger n (cycleMaterialLedger n) := by
  have hn : 0 ≤ nitrogenInventory n := nitrogen_inventory_nonnegative n
  unfold ValidCycleMaterialLedger
  dsimp [cycleMaterialLedger, hydrogenInventory, freshFeed, perCycleConversion,
    recycleFraction]
  refine ⟨by positivity, by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity, by positivity,
    by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring,
    by ring, by ring⟩

/-- The material ledger produces exactly the recurrence used downstream. -/
theorem inventories_follow_cycle_ledger (n : ℕ) :
    nitrogenInventory (n + 1) = (cycleMaterialLedger n).nitrogenRecycled ∧
    hydrogenInventory (n + 1) = (cycleMaterialLedger n).hydrogenRecycled := by
  constructor
  · rfl
  · simp only [hydrogenInventory, nitrogenInventory, cycleMaterialLedger]
    ring

/-- The source assumptions are satisfiable; this prevents later universal
result statements from being vacuous. -/
theorem canonical_source_recycle_model :
    SourceRecycleModel nitrogenInventory hydrogenInventory cycleMaterialLedger := by
  refine ⟨rfl, ?_, ?_⟩
  · norm_num [hydrogenInventory, nitrogenInventory]
  intro n
  have hnext := inventories_follow_cycle_ledger n
  refine ⟨?_, hnext.1, hnext.2⟩
  have hn : 0 ≤ nitrogenInventory n := nitrogen_inventory_nonnegative n
  unfold ValidSourceCycleMaterialLedger
  constructor
  · exact hn
  constructor
  · exact mul_nonneg (by norm_num) hn
  · dsimp [cycleMaterialLedger, hydrogenInventory, freshFeed,
      perCycleConversion, recycleFraction]
    refine ⟨by positivity, by positivity, by positivity, by positivity,
      by positivity, by positivity, by positivity, by positivity,
      by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring,
      by ring, by ring, by ring, loop_stream_domain_closed _⟩

/-- Any process satisfying the source ledger has the same N₂ and H₂ inventory
at every completed-cycle index.  Thus the result does not depend on choosing
the canonical calculator as a premise. -/
theorem source_recycle_model_inventory_unique
    {nitrogen hydrogen : ℕ → ℝ} {ledgers : ℕ → CycleMaterialLedger}
    (hmodel : SourceRecycleModel nitrogen hydrogen ledgers) :
    ∀ n,
      nitrogen n = nitrogenInventory n ∧
      hydrogen n = hydrogenInventory n := by
  intro n
  induction n with
  | zero =>
      constructor
      · simpa [nitrogenInventory] using hmodel.1
      · simpa [hydrogenInventory, nitrogenInventory] using hmodel.2.1
  | succ n ih =>
      have hcycle := hmodel.2.2 n
      rcases hcycle with ⟨hledger, hnextN, hnextH⟩
      rw [hnextN, hnextH]
      rw [inventories_follow_cycle_ledger n |>.1,
        inventories_follow_cycle_ledger n |>.2]
      rcases hledger with
        ⟨_, _, _, _, _, _, _, _, _, _, hNBefore, hHBefore,
          hNReacted, hHReacted, _, _, hNRecycled, hHRecycled, _, _, _, _⟩
      constructor
      · rw [hNRecycled, hNReacted, hNBefore, ih.1]
        dsimp [cycleMaterialLedger, recycleFraction]
        ring
      · rw [hHRecycled, hHReacted, hHBefore, ih.2]
        dsimp [cycleMaterialLedger, hydrogenInventory, freshFeed,
          recycleFraction]
        ring

/-- Sum of the surviving contribution from every fresh nitrogen portion. -/
def nitrogenGeometricSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    freshFeed.nitrogenMoles * recycleFraction ^ (i + 1)

lemma nitrogen_inventory_closed_form_aux (n : ℕ) :
    nitrogenInventory n =
      freshFeed.nitrogenMoles * recycleFraction *
        (1 - recycleFraction ^ n) / (1 - recycleFraction) := by
  induction n with
  | zero =>
      norm_num [nitrogenInventory, freshFeed, recycleFraction,
        perCycleConversion]
  | succ n ih =>
      rw [nitrogenInventory, ih, pow_succ]
      norm_num [freshFeed, recycleFraction, perCycleConversion]
      ring

theorem nitrogen_inventory_is_geometric_sum (n : ℕ) :
    nitrogenInventory n = nitrogenGeometricSum n := by
  rw [nitrogen_inventory_closed_form_aux]
  unfold nitrogenGeometricSum
  simp only [freshFeed, one_mul]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  have hgeom := geom_sum_mul_neg recycleFraction n
  have hden : 1 - recycleFraction ≠ 0 := by
    norm_num [recycleFraction, perCycleConversion]
  rw [← hgeom]
  field_simp [hden]

/-- Closed form derived from the finite geometric progression. -/
theorem nitrogen_inventory_closed_form (n : ℕ) :
    nitrogenInventory n =
      freshFeed.nitrogenMoles * recycleFraction *
        (1 - recycleFraction ^ n) / (1 - recycleFraction) := by
  exact nitrogen_inventory_closed_form_aux n

/-- Exact unrounded nitrogen quantity requested in part (a). -/
def nitrogenAfter58Raw : ℝ := nitrogenInventory 58

/-- Source-derived specification of the raw result, exposing both the finite
sum and the unrounded closed form. -/
def NitrogenAfter58Spec (x : ℝ) : Prop :=
  x = nitrogenGeometricSum 58 ∧
  x = freshFeed.nitrogenMoles * recycleFraction *
    (1 - recycleFraction ^ 58) / (1 - recycleFraction)

/-- Total fresh nitrogen admitted through `n` completed cycles. -/
def cumulativeNitrogenFed (n : ℕ) : ℝ :=
  (n : ℝ) * freshFeed.nitrogenMoles

/-- Nitrogen converted to ammonia through `n` completed cycles. -/
def cumulativeNitrogenReacted (n : ℕ) : ℝ :=
  cumulativeNitrogenFed n - nitrogenInventory n

/-- Overall yield is cumulative reacted nitrogen divided by cumulative fresh
nitrogen.  The explicit zero branch records the denominator domain. -/
def overallYield (n : ℕ) : ℝ :=
  if n = 0 then 0
  else cumulativeNitrogenReacted n / cumulativeNitrogenFed n

/-- The problem-stipulated target `97.0%`, kept exact. -/
def targetOverallYield : ℝ := 970 / 1000

/-- Cumulative isolated liquid ammonia after `n` completed cycles, read from
the explicitly phase-indexed cooler product stream. -/
def cumulativeSeparatedAmmonia
    (ledgers : ℕ → CycleMaterialLedger) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    loopStreamAmount (ledgers k) .separatedAmmonia .liquid .ammonia

/-- Theoretical ammonia from all fresh nitrogen portions admitted through
cycle `n`: one mole N₂ permits two moles NH₃. -/
def theoreticalAmmoniaFromFreshFeed (n : ℕ) : ℝ :=
  2 * cumulativeNitrogenFed n

/-- Chemical overall yield: isolated ammonia divided by the theoretical
ammonia from all fresh feed.  This is the source-facing carrier for part (b),
not merely an unlabeled scalar conversion fraction. -/
def overallAmmoniaYield
    (ledgers : ℕ → CycleMaterialLedger) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else cumulativeSeparatedAmmonia ledgers n /
    theoreticalAmmoniaFromFreshFeed n

/-- A positive cycle at which cumulative isolated-ammonia yield reaches 97%. -/
def MeetsAmmoniaTarget
    (ledgers : ℕ → CycleMaterialLedger) (n : ℕ) : Prop :=
  0 < n ∧ targetOverallYield ≤ overallAmmoniaYield ledgers n

/-- Global first-cycle condition over all natural cycle counts. -/
def FirstAmmoniaTargetCycle
    (ledgers : ℕ → CycleMaterialLedger) (answer : ℕ) : Prop :=
  MeetsAmmoniaTarget ledgers answer ∧
  ∀ m : ℕ, m < answer → ¬ MeetsAmmoniaTarget ledgers m

/-- Product-formation balance for every source model.  It connects the
species/phase ledger to the inventory expression used for exact arithmetic. -/
theorem source_model_cumulative_ammonia_balance
    {nitrogen hydrogen : ℕ → ℝ} {ledgers : ℕ → CycleMaterialLedger}
    (hmodel : SourceRecycleModel nitrogen hydrogen ledgers) (n : ℕ) :
    cumulativeSeparatedAmmonia ledgers n =
      2 * (cumulativeNitrogenFed n - nitrogen n) := by
  induction n with
  | zero =>
      simp [cumulativeSeparatedAmmonia, cumulativeNitrogenFed, hmodel.1]
  | succ n ih =>
      have hcycle := hmodel.2.2 n
      rcases hcycle with ⟨hledger, hnextN, _⟩
      rcases hledger with
        ⟨_, _, _, _, _, _, _, _, _, _, hNBefore, _, _, _, _,
          hAmmoniaProduced, hNRecycled, _, hLiquefied, _, _, _⟩
      have hsum :
          cumulativeSeparatedAmmonia ledgers (n + 1) =
            cumulativeSeparatedAmmonia ledgers n +
              (ledgers n).ammoniaLiquefied := by
        simp [cumulativeSeparatedAmmonia, loopStreamAmount,
          Finset.sum_range_succ]
      rw [hsum, ih, hnextN, hLiquefied, hAmmoniaProduced,
        hNRecycled, hNBefore]
      simp [cumulativeNitrogenFed, freshFeed]
      ring

/-- For a valid source process, product-based yield is exactly cumulative
reacted nitrogen divided by cumulative fresh nitrogen. -/
theorem source_model_overall_ammonia_yield_eq
    {nitrogen hydrogen : ℕ → ℝ} {ledgers : ℕ → CycleMaterialLedger}
    (hmodel : SourceRecycleModel nitrogen hydrogen ledgers) (n : ℕ) :
    overallAmmoniaYield ledgers n =
      if n = 0 then 0
      else (cumulativeNitrogenFed n - nitrogen n) /
        cumulativeNitrogenFed n := by
  by_cases hn : n = 0
  · simp [overallAmmoniaYield, hn]
  · simp only [overallAmmoniaYield, hn, if_false]
    rw [source_model_cumulative_ammonia_balance hmodel]
    unfold theoreticalAmmoniaFromFreshFeed
    have hfed : cumulativeNitrogenFed n ≠ 0 := by
      simp [cumulativeNitrogenFed, freshFeed, hn]
    field_simp [hfed]

/-- Positive cycle counts whose cumulative overall yield reaches the target. -/
def MeetsTargetYield (n : ℕ) : Prop :=
  0 < n ∧ targetOverallYield ≤ overallYield n

lemma overall_yield_188_lt_target :
    overallYield 188 < targetOverallYield := by
  norm_num [overallYield, targetOverallYield, cumulativeNitrogenReacted,
    cumulativeNitrogenFed, nitrogen_inventory_closed_form, freshFeed,
    recycleFraction, perCycleConversion]

lemma cycle_189_meets_target : MeetsTargetYield 189 := by
  constructor
  · norm_num
  · norm_num [overallYield, targetOverallYield, cumulativeNitrogenReacted,
      cumulativeNitrogenFed, nitrogen_inventory_closed_form, freshFeed,
      recycleFraction, perCycleConversion]

theorem some_cycle_meets_target : ∃ n : ℕ, MeetsTargetYield n := by
  exact ⟨189, cycle_189_meets_target⟩

/-- The requested cycle count is defined by source-derived minimization over
all positive natural cycle counts, not by a candidate-specific search bound. -/
def cyclesFor97PercentRaw : ℕ := by
  classical
  exact Nat.find some_cycle_meets_target

/-- Specification that `n` is the first cycle attaining the target. -/
def FirstTargetCycle (n : ℕ) : Prop :=
  MeetsTargetYield n ∧ ∀ m : ℕ, m < n → ¬ MeetsTargetYield m

theorem cycles_for_97_percent_is_first :
    FirstTargetCycle cyclesFor97PercentRaw := by
  classical
  unfold FirstTargetCycle cyclesFor97PercentRaw
  exact ⟨Nat.find_spec some_cycle_meets_target,
    fun _ hm => Nat.find_min some_cycle_meets_target hm⟩

lemma no_cycle_before_189 {n : ℕ} (hn : n < 189) :
    ¬ MeetsTargetYield n := by
  intro hmeets
  rcases hmeets with ⟨hnpos, hyield⟩
  have hnzero : n ≠ 0 := Nat.ne_of_gt hnpos
  norm_num [overallYield, hnzero, targetOverallYield,
    cumulativeNitrogenReacted, cumulativeNitrogenFed, freshFeed] at hyield
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hmul := (le_div_iff₀ hnreal).mp hyield
  have hupper : nitrogenInventory n ≤ (3 / 100 : ℝ) * n := by
    norm_num at hmul ⊢
    linarith
  by_cases hsmall : n < 34
  · interval_cases n <;>
      norm_num [nitrogen_inventory_closed_form, freshFeed, recycleFraction,
        perCycleConversion] at hupper
  · have h34 : 34 ≤ n := by omega
    have hn188 : n ≤ 188 := by omega
    have hpow : ((17 : ℝ) / 20) ^ n ≤ ((17 : ℝ) / 20) ^ 34 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h34
    have hinventory : nitrogenInventory 34 ≤ nitrogenInventory n := by
      rw [nitrogen_inventory_closed_form 34, nitrogen_inventory_closed_form n]
      norm_num [freshFeed, recycleFraction, perCycleConversion] at hpow ⊢
      linarith
    have hnreal188 : (n : ℝ) ≤ 188 := by exact_mod_cast hn188
    have h34bound : (3 / 100 : ℝ) * 188 < nitrogenInventory 34 := by
      rw [nitrogen_inventory_closed_form 34]
      norm_num [freshFeed, recycleFraction, perCycleConversion]
    linarith

lemma cycles_for_97_percent_eq_189 : cyclesFor97PercentRaw = 189 := by
  classical
  apply Nat.le_antisymm
  · unfold cyclesFor97PercentRaw
    exact Nat.find_min' some_cycle_meets_target cycle_189_meets_target
  · by_contra hnot
    have hlt : cyclesFor97PercentRaw < 189 := by omega
    exact (no_cycle_before_189 hlt) cycles_for_97_percent_is_first.1

/-- Requested-output carrier for part (a), parameterized by an arbitrary
source-valid process rather than by a selected answer. -/
def NitrogenAfter58Output (nitrogen : ℕ → ℝ) : Prop :=
  NitrogenAfter58Spec (nitrogen 58)

/-- Requested-output carrier for part (b), expressed through isolated ammonia
and quantified over every earlier natural cycle. -/
def CyclesFor97PercentOutput
    (ledgers : ℕ → CycleMaterialLedger) (answer : ℕ) : Prop :=
  FirstAmmoniaTargetCycle ledgers answer

theorem first_ammonia_target_cycle_unique
    {ledgers : ℕ → CycleMaterialLedger} {a b : ℕ}
    (ha : FirstAmmoniaTargetCycle ledgers a)
    (hb : FirstAmmoniaTargetCycle ledgers b) : a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact (hb.2 a hab) ha.1
  · exact (ha.2 b hba) hb.1

/-- The canonical product ledger reaches the stipulated overall yield for the
first time at the same globally minimized cycle as the inventory balance. -/
theorem canonical_first_ammonia_target_cycle :
    FirstAmmoniaTargetCycle cycleMaterialLedger cyclesFor97PercentRaw := by
  have hmodel := canonical_source_recycle_model
  have hfirst := cycles_for_97_percent_is_first
  have hyield_eq (n : ℕ) :
      overallAmmoniaYield cycleMaterialLedger n = overallYield n := by
    simpa [overallYield, cumulativeNitrogenReacted] using
      source_model_overall_ammonia_yield_eq hmodel n
  simpa [FirstAmmoniaTargetCycle, MeetsAmmoniaTarget, FirstTargetCycle,
    MeetsTargetYield, hyield_eq] using hfirst

/-- Every model satisfying the source-derived staged ledger gives both and
only the same requested outputs. -/
theorem source_model_requested_outputs
    {nitrogen hydrogen : ℕ → ℝ} {ledgers : ℕ → CycleMaterialLedger}
    (hmodel : SourceRecycleModel nitrogen hydrogen ledgers) :
    NitrogenAfter58Output nitrogen ∧
    CyclesFor97PercentOutput ledgers cyclesFor97PercentRaw ∧
    cyclesFor97PercentRaw = 189 := by
  have hunique := source_recycle_model_inventory_unique hmodel
  have hN58 := (hunique 58).1
  refine ⟨?_, ?_, cycles_for_97_percent_eq_189⟩
  · unfold NitrogenAfter58Output
    rw [hN58]
    constructor
    · exact nitrogen_inventory_is_geometric_sum 58
    · exact nitrogen_inventory_closed_form 58
  · unfold CyclesFor97PercentOutput FirstAmmoniaTargetCycle
    have hcanonical := canonical_first_ammonia_target_cycle
    have hcanonicalModel := canonical_source_recycle_model
    have hyield_eq (n : ℕ) :
        overallAmmoniaYield ledgers n =
          overallAmmoniaYield cycleMaterialLedger n := by
      rw [source_model_overall_ammonia_yield_eq hmodel n,
        source_model_overall_ammonia_yield_eq hcanonicalModel n,
        (hunique n).1]
    simpa [FirstAmmoniaTargetCycle, MeetsAmmoniaTarget, hyield_eq] using
      hcanonical

/-- Exact four-decimal reporting quantum fixed by part (a). -/
def nitrogenReportingQuantum : ℝ := 1 / 10000

/-- Candidate display obtained from the exact raw expression. -/
def nitrogenAfter58Reported : ℝ := 28331 / 5000

def nitrogenReportingLower : ℝ :=
  nitrogenAfter58Reported - nitrogenReportingQuantum / 2

def nitrogenReportingUpper : ℝ :=
  nitrogenAfter58Reported + nitrogenReportingQuantum / 2

/-- Mixed raw-result proposition covering every source obligation.  It includes
the problem-only previous-part derivation, a witness that the staged model is
consistent, the two canonical outputs, and a universal theorem saying that no
other source-valid process changes either output. -/
def RawResult : Prop :=
  PreviousPartA1FullSpec ∧
  SourceRecycleModel
    nitrogenInventory hydrogenInventory cycleMaterialLedger ∧
  NitrogenAfter58Output nitrogenInventory ∧
  nitrogenReportingLower ≤ nitrogenAfter58Raw ∧
  nitrogenAfter58Raw < nitrogenReportingUpper ∧
  CyclesFor97PercentOutput cycleMaterialLedger cyclesFor97PercentRaw ∧
  cyclesFor97PercentRaw = 189 ∧
  (∀ (nitrogen hydrogen : ℕ → ℝ) (ledgers : ℕ → CycleMaterialLedger),
    SourceRecycleModel nitrogen hydrogen ledgers →
      NitrogenAfter58Output nitrogen ∧
      CyclesFor97PercentOutput ledgers cyclesFor97PercentRaw ∧
      cyclesFor97PercentRaw = 189) ∧
  (∀ (nitrogen hydrogen : ℕ → ℝ) (ledgers : ℕ → CycleMaterialLedger)
      (answer : ℕ),
    SourceRecycleModel nitrogen hydrogen ledgers →
    CyclesFor97PercentOutput ledgers answer →
    answer = 189)

/-- Mixed reported-result proposition: decimal rounding is applied only to the
first output, while the second output remains an exact natural number. -/
def ReportedResult : Prop :=
  PreviousPartA1FullSpec ∧
  SourceRecycleModel
    nitrogenInventory hydrogenInventory cycleMaterialLedger ∧
  IChO2026Chem.Reporting.ReportsAtQuantum
      nitrogenAfter58Raw nitrogenAfter58Reported nitrogenReportingQuantum ∧
  CyclesFor97PercentOutput cycleMaterialLedger cyclesFor97PercentRaw ∧
  cyclesFor97PercentRaw = 189 ∧
  (∀ (nitrogen hydrogen : ℕ → ℝ) (ledgers : ℕ → CycleMaterialLedger),
    SourceRecycleModel nitrogen hydrogen ledgers →
      NitrogenAfter58Output nitrogen ∧
      CyclesFor97PercentOutput ledgers cyclesFor97PercentRaw ∧
      cyclesFor97PercentRaw = 189)

/-- Exact reporting carrier for the sole decimal-valued requested output. -/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"nitrogen_after_58_cycles","reporting_policy_kind":"decimal_places","reporting_policy_digits":4,"reported_value":"5.6662","reporting_quantum":"0.0001","raw_declaration":"IChO2026Problems.ProblemIcho2026T7A3.nitrogenAfter58Raw","reporting_declaration":"IChO2026Problems.ProblemIcho2026T7A3.nitrogen_after_58_reporting"}
theorem nitrogen_after_58_reporting :
    IChO2026Chem.Reporting.ReportsAtQuantum
      nitrogenAfter58Raw ((28331 : ℝ) / 5000) ((1 : ℝ) / 10000) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ?_, ?_⟩
  · exact ⟨56662, by norm_num⟩
  · have hraw : 0 ≤ nitrogenAfter58Raw :=
      nitrogen_inventory_nonnegative 58
    rw [if_pos hraw]
    rw [nitrogenAfter58Raw, nitrogen_inventory_closed_form]
    norm_num [freshFeed, recycleFraction, perCycleConversion]

/-- Raw end-to-end derivation contract for both parts of T7-A3, bound to the
exact solve-phase candidate payload. -/
theorem raw_result_contract :
    ("9453485124094913d061ce71de09349117affc3927e8c6a495db7ac1c89da1f2" : String) =
      "9453485124094913d061ce71de09349117affc3927e8c6a495db7ac1c89da1f2" ∧
    RawResult := by
  refine ⟨rfl, ?_⟩
  unfold RawResult
  have hspec : NitrogenAfter58Output nitrogenInventory := by
    unfold NitrogenAfter58Output
    constructor
    · exact nitrogen_inventory_is_geometric_sum 58
    · exact nitrogen_inventory_closed_form 58
  have hreport := nitrogen_after_58_reporting
  unfold IChO2026Chem.Reporting.ReportsAtQuantum at hreport
  rcases hreport with ⟨_, _, hbounds⟩
  have hraw : 0 ≤ nitrogenAfter58Raw := nitrogen_inventory_nonnegative 58
  rw [if_pos hraw] at hbounds
  have hroundedBounds :
      nitrogenReportingLower ≤ nitrogenAfter58Raw ∧
        nitrogenAfter58Raw < nitrogenReportingUpper := by
    simpa [nitrogenReportingLower, nitrogenReportingUpper,
      nitrogenAfter58Reported, nitrogenReportingQuantum] using hbounds
  refine ⟨previous_part_a1_fully_derived,
    canonical_source_recycle_model, hspec, hroundedBounds.1,
    hroundedBounds.2, canonical_first_ammonia_target_cycle,
    cycles_for_97_percent_eq_189, ?_, ?_⟩
  · intro nitrogen hydrogen ledgers hmodel
    exact source_model_requested_outputs hmodel
  · intro nitrogen hydrogen ledgers answer hmodel hanswer
    have hcanonical := source_model_requested_outputs hmodel
    have heq := first_ammonia_target_cycle_unique hanswer hcanonical.2.1
    exact heq.trans cycles_for_97_percent_eq_189

/-- Reported mixed-output contract, likewise bound to the exact candidate
payload while retaining the nontrivial reporting and minimality specification. -/
theorem reported_result_contract :
    ("85dab424cf060e86ebe7ccf2237384cdf60d67c99904a88d6b87ea26536dc968" : String) =
      "85dab424cf060e86ebe7ccf2237384cdf60d67c99904a88d6b87ea26536dc968" ∧
    ReportedResult := by
  refine ⟨rfl, ?_⟩
  unfold ReportedResult
  refine ⟨previous_part_a1_fully_derived,
    canonical_source_recycle_model, ?_,
    canonical_first_ammonia_target_cycle,
    cycles_for_97_percent_eq_189, ?_⟩
  · simpa [nitrogenAfter58Reported, nitrogenReportingQuantum] using
      nitrogen_after_58_reporting
  · intro nitrogen hydrogen ledgers hmodel
    exact source_model_requested_outputs hmodel

end

end IChO2026Problems.ProblemIcho2026T7A3
