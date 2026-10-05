import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, theory problem 2, part 7

This file formalizes the qualitative choice of a graph for `dG/dt` in a
closed oscillatory reaction.  The six constructors below are the six boxes in
the supplied answer panel, read from left to right and top to bottom.

The functions in `panelRate` are canonical representatives of the visibly
drawn qualitative classes; they are not numerical measurements extracted from
the figure.  In particular, the constants only make the sign, limiting
behaviour, and modulation of each pictured class mathematically explicit.
-/

open Filter

namespace IChO2026Problems.T2A7

/-- The six graph boxes on the student-visible answer sheet. -/
inductive GibbsRateGraphPanel where
  | topLeft
  | topRight
  | middleLeft
  | middleRight
  | bottomLeft
  | bottomRight
  deriving DecidableEq, Fintype

/-- A rate has a repeated down/up modulation at a specified positive period on
the nonnegative time axis.  The two samples in every period encode genuine
repeated modulation without requiring an undamped exactly-periodic rate. -/
def ModulatedAtPeriod (rate : ℝ → ℝ) (period : ℝ) : Prop :=
  0 < period ∧
  ∀ n : ℕ,
    rate ((n : ℝ) * period + period / 4) < rate ((n : ℝ) * period) ∧
    rate ((n : ℝ) * period + 3 * period / 4) >
      rate ((n : ℝ) * period + period / 4)

/-- Modulation at some positive period. -/
def PeriodicallyModulated (rate : ℝ → ℝ) : Prop :=
  ∃ period : ℝ, ModulatedAtPeriod rate period

/-- The qualitative constraints on `dG/dt` used by the graph question:

* the second law keeps the rate nonpositive;
* a closed reacting system approaches equilibrium, so the rate tends to zero;
* the oscillatory kinetics repeatedly modulate the dissipation rate.
-/
def DampedDissipativeOscillation (rate : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → rate t ≤ 0) ∧
  Tendsto rate atTop (nhds 0) ∧
  PeriodicallyModulated rate

/-- Explicit qualitative representatives of the six curves in the answer
panel.  Their scale and frequency are immaterial to the classification. -/
noncomputable def panelRate : GibbsRateGraphPanel → ℝ → ℝ
  | .topLeft => fun t => -t
  | .topRight => fun t => Real.sin (2 * Real.pi * t)
  | .middleLeft => fun t => -Real.exp (-t)
  | .middleRight => fun t =>
      -t - (1 + Real.sin (2 * Real.pi * t)) / 2
  | .bottomLeft => fun t =>
      Real.exp (t / 10) * Real.sin (2 * Real.pi * t)
  | .bottomRight => fun t =>
      -Real.exp (-t) * (2 + Real.sin (2 * Real.pi * t))

/-- A local interface for the constant-temperature, constant-pressure Gibbs
criterion.  Closedness and the fixed external conditions are represented by
the type; the decisive thermodynamic bridge is exposed as the standard
entropy-production identity rather than assumed as the desired sign. -/
structure ClosedIsothermalIsobaricEvolution where
  gibbsEnergy : ℝ → ℝ
  gibbsRate : ℝ → ℝ
  entropyProductionRate : ℝ → ℝ
  boundarySpeciesFlux : ℕ → ℝ → ℝ
  absoluteTemperature : ℝ
  pressure : ℝ
  temperaturePositive : 0 < absoluteTemperature
  closedBoundary :
    ∀ speciesIndex : ℕ, ∀ t : ℝ, 0 ≤ t →
      boundarySpeciesFlux speciesIndex t = 0
  gibbsRateIsDerivative :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt gibbsEnergy (gibbsRate t) (Set.Ici 0) t
  entropyProductionNonnegative :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ entropyProductionRate t
  gibbsEntropyProductionIdentity :
    ∀ t : ℝ, 0 ≤ t →
      gibbsRate t = -absoluteTemperature * entropyProductionRate t

/-- The additional source-level qualitative information for a closed
oscillatory reaction: its kinetic cycling modulates dissipation, while finite
driving forces vanish as equilibrium is approached. -/
structure ClosedOscillatoryReactionEvolution
    extends ClosedIsothermalIsobaricEvolution where
  kineticPeriod : ℝ
  kineticPeriodPositive : 0 < kineticPeriod
  dissipationTracksKineticPeriod : ModulatedAtPeriod gibbsRate kineticPeriod
  entropyProductionVanishesAtEquilibrium :
    Tendsto entropyProductionRate atTop (nhds 0)

/-- The entropy-production identity and the second law imply that Gibbs energy
cannot have a positive instantaneous rate along the reaction. -/
theorem closedSystem_gibbsRate_nonpositive
    (system : ClosedIsothermalIsobaricEvolution) :
    ∀ t : ℝ, 0 ≤ t → system.gibbsRate t ≤ 0 := by
  intro t ht
  rw [system.gibbsEntropyProductionIdentity t ht]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr system.temperaturePositive.le)
    (system.entropyProductionNonnegative t ht)

/-- Equivalently, the Gibbs energy itself cannot rise on physical time. -/
theorem closedSystem_gibbsEnergy_antitoneOn
    (system : ClosedIsothermalIsobaricEvolution) :
    AntitoneOn system.gibbsEnergy (Set.Ici 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := system.gibbsRate)
    (convex_Ici 0) ?_ ?_ ?_
  · intro t ht
    exact (system.gibbsRateIsDerivative t ht).continuousWithinAt
  · intro t ht
    exact (system.gibbsRateIsDerivative t (interior_subset ht)).mono interior_subset
  · intro t ht
    exact closedSystem_gibbsRate_nonpositive system t (interior_subset ht)

/-- Vanishing entropy production at equilibrium and the Gibbs dissipation
identity force `dG/dt` itself to tend to zero. -/
theorem closedOscillatorySystem_gibbsRate_tendsto_zero
    (system : ClosedOscillatoryReactionEvolution) :
    Tendsto system.toClosedIsothermalIsobaricEvolution.gibbsRate
      atTop (nhds 0) := by
  have hproduct :
      Tendsto
        (fun t : ℝ =>
          -system.toClosedIsothermalIsobaricEvolution.absoluteTemperature *
            system.toClosedIsothermalIsobaricEvolution.entropyProductionRate t)
        atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds
        (x := -system.toClosedIsothermalIsobaricEvolution.absoluteTemperature)
        (f := atTop)).mul system.entropyProductionVanishesAtEquilibrium)
  apply hproduct.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (system.toClosedIsothermalIsobaricEvolution.gibbsEntropyProductionIdentity t ht).symm

/-- Every modeled closed oscillatory reaction has the three qualitative
features required of the answer graph. -/
theorem closedOscillatorySystem_requiredShape
    (system : ClosedOscillatoryReactionEvolution) :
    DampedDissipativeOscillation
      system.toClosedIsothermalIsobaricEvolution.gibbsRate := by
  exact ⟨
    closedSystem_gibbsRate_nonpositive system.toClosedIsothermalIsobaricEvolution,
    closedOscillatorySystem_gibbsRate_tendsto_zero system,
    ⟨system.kineticPeriod, system.dissipationTracksKineticPeriod⟩⟩

/-- The lower-right trace satisfies all source-derived qualitative
constraints. -/
theorem bottomRight_satisfies_requiredShape :
    DampedDissipativeOscillation (panelRate .bottomRight) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t _ht
    dsimp [panelRate]
    have hs : -1 ≤ Real.sin (2 * Real.pi * t) := Real.neg_one_le_sin _
    have he : 0 < Real.exp (-t) := Real.exp_pos _
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr he.le) (by linarith)
  · apply squeeze_zero_norm
    · intro t
      calc
        ‖-Real.exp (-t) * (2 + Real.sin (2 * Real.pi * t))‖ =
            Real.exp (-t) * (2 + Real.sin (2 * Real.pi * t)) := by
              rw [Real.norm_eq_abs, abs_mul, abs_neg,
                abs_of_pos (Real.exp_pos _), abs_of_nonneg]
              linarith [Real.neg_one_le_sin (2 * Real.pi * t)]
        _ ≤ Real.exp (-t) * 3 := by
          gcongr
          linarith [Real.sin_le_one (2 * Real.pi * t)]
        _ = 3 * Real.exp (-t) := by ring
    · simpa using
        (tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero :
          Tendsto (fun t : ℝ => 3 * Real.exp (-t)) atTop (nhds (3 * 0)))
  · refine ⟨1, by norm_num, ?_⟩
    intro n
    have hbase :
        panelRate .bottomRight ((n : ℝ) * 1) =
          -(Real.exp (-(n : ℝ)) * 2) := by
      dsimp [panelRate]
      simp only [mul_one]
      have hs : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
        simpa using Real.sin_add_nat_mul_two_pi 0 n
      rw [show 2 * Real.pi * (n : ℝ) =
        (n : ℝ) * (2 * Real.pi) by ring, hs]
      ring
    have hquarter :
        panelRate .bottomRight ((n : ℝ) * 1 + 1 / 4) =
          -(Real.exp (-((n : ℝ) + 1 / 4)) * 3) := by
      dsimp [panelRate]
      simp only [mul_one]
      have hs :
          Real.sin (Real.pi / 2 + (n : ℝ) * (2 * Real.pi)) = 1 := by
        rw [Real.sin_add_nat_mul_two_pi]
        exact Real.sin_pi_div_two
      rw [show 2 * Real.pi * ((n : ℝ) + 1 / 4) =
        Real.pi / 2 + (n : ℝ) * (2 * Real.pi) by ring, hs]
      ring
    have hthreeQuarter :
        panelRate .bottomRight ((n : ℝ) * 1 + 3 * 1 / 4) =
          -(Real.exp (-((n : ℝ) + 3 / 4)) * 1) := by
      dsimp [panelRate]
      simp only [mul_one]
      have hs :
          Real.sin (3 * Real.pi / 2 + (n : ℝ) * (2 * Real.pi)) = -1 := by
        rw [Real.sin_add_nat_mul_two_pi]
        rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring]
        simp
      rw [show 2 * Real.pi * ((n : ℝ) + 3 / 4) =
        3 * Real.pi / 2 + (n : ℝ) * (2 * Real.pi) by ring, hs]
      ring
    rw [hbase, hquarter, hthreeQuarter]
    constructor
    · have hq : Real.exp (1 / 4 : ℝ) < 3 / 2 := by
        calc
          Real.exp (1 / 4 : ℝ) < 1 / (1 - (1 / 4 : ℝ)) :=
            Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
          _ < 3 / 2 := by norm_num
      have hpos : 0 < Real.exp (-(n : ℝ) - 1 / 4) := Real.exp_pos _
      have heq :
          Real.exp (-(n : ℝ)) =
            Real.exp (-(n : ℝ) - 1 / 4) * Real.exp (1 / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show -((n : ℝ) + 1 / 4) = -(n : ℝ) - 1 / 4 by ring, heq]
      nlinarith
    · have hlt :
          Real.exp (-((n : ℝ) + 3 / 4)) <
            Real.exp (-((n : ℝ) + 1 / 4)) := by
        rw [Real.exp_lt_exp]
        norm_num
      have hpos : 0 < Real.exp (-((n : ℝ) + 1 / 4)) := Real.exp_pos _
      nlinarith

/-- A complete audit of the six source-visible boxes: exactly the lower-right
representative is nonpositive, repeatedly modulated, and convergent to zero. -/
theorem panelRate_satisfies_requiredShape_iff
    (panel : GibbsRateGraphPanel) :
    DampedDissipativeOscillation (panelRate panel) ↔
      panel = .bottomRight := by
  constructor
  · intro hshape
    rcases hshape with ⟨hnonpositive, hlimit, hmodulated⟩
    cases panel with
    | topLeft =>
        exfalso
        rcases hmodulated with ⟨period, hp, htrack⟩
        have h := (htrack 0).2
        dsimp [panelRate] at h
        norm_num at h
        linarith
    | topRight =>
        exfalso
        have h := hnonpositive (1 / 4) (by norm_num)
        dsimp [panelRate] at h
        rw [show 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 by ring,
          Real.sin_pi_div_two] at h
        norm_num at h
    | middleLeft =>
        exfalso
        rcases hmodulated with ⟨period, hp, htrack⟩
        have h := (htrack 0).1
        dsimp [panelRate] at h
        norm_num at h
        have hexp : Real.exp (-(period / 4)) < 1 := by
          rw [Real.exp_lt_one_iff]
          linarith
        nlinarith
    | middleRight =>
        exfalso
        have hevent :
            ∀ᶠ t in atTop, (-1 : ℝ) < panelRate .middleRight t :=
          (tendsto_order.1 hlimit).1 (-1) (by norm_num)
        rcases eventually_atTop.1 hevent with ⟨a, ha⟩
        let t : ℝ := max a 2
        have h := ha t (le_max_left a 2)
        have ht : 2 ≤ t := le_max_right a 2
        dsimp [panelRate] at h
        nlinarith [Real.neg_one_le_sin (2 * Real.pi * t)]
    | bottomLeft =>
        exfalso
        have h := hnonpositive (1 / 4) (by norm_num)
        dsimp [panelRate] at h
        rw [show 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 by ring,
          Real.sin_pi_div_two] at h
        norm_num at h
        exact (not_le_of_gt (Real.exp_pos _)) h
    | bottomRight =>
        rfl
  · rintro rfl
    exact bottomRight_satisfies_requiredShape

/-- Raw classification contract: the finite source-visible panel contains a
unique trace with the thermodynamically required qualitative shape. -/
def GibbsRateGraphRawResult : Prop :=
  ∃! panel : GibbsRateGraphPanel,
    DampedDissipativeOscillation (panelRate panel)

/-- Reported exact-symbolic contract: that unique trace is the bottom-right
box of the supplied panel.  The candidate occurs only in the conclusion. -/
def GibbsRateGraphReportedResult : Prop :=
  DampedDissipativeOscillation (panelRate .bottomRight) ∧
    ∀ panel : GibbsRateGraphPanel,
      DampedDissipativeOscillation (panelRate panel) →
        panel = .bottomRight

/-- The raw, answer-independent unique-choice derivation. -/
theorem gibbsRateGraphRawDerivation : GibbsRateGraphRawResult := by
  exact ⟨.bottomRight, bottomRight_satisfies_requiredShape,
    fun panel hpanel => (panelRate_satisfies_requiredShape_iff panel).mp hpanel⟩

/-- The requested exact symbolic graph selection. -/
theorem gibbsRateGraphReportedDerivation : GibbsRateGraphReportedResult := by
  exact ⟨bottomRight_satisfies_requiredShape,
    fun panel hpanel => (panelRate_satisfies_requiredShape_iff panel).mp hpanel⟩

end IChO2026Problems.T2A7
