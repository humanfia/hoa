import AFPS2017.Flow.Protocol

/-!
# Idealized AFPS throughput

This module separates the published nominal cycle timing from the explicit
idealizations needed to turn it into an annual throughput calculation.  The
timing model records that setup, switching, maintenance, purification, and
downtime add no time; the annual model separately supplies nonnegative uptime
and a number of parallel synthesis lines.  Consequently, no annual production
claim is unconditional.

Source references:

* Published article (`afps2017.main:DOI-10.1038/nchembio.2318`).
* Sanitized yield contract (`afps2017.yield.contract:question`).
-/

namespace AFPS2017.Yield

/-- The explicit zero-overhead idealization of the reported nominal cycle. -/
structure IdealTimingModel : Type where
  /-- Time beyond the per-residue nominal cycles. -/
  additionalSeconds : ℝ
  /-- Setup, switching, maintenance, purification, and downtime are excluded. -/
  excludesSetupSwitchingMaintenancePurificationDowntime : additionalSeconds = 0
  /-- Nominal synthesis time assigned to each residue. -/
  secondsPerResidue : ℝ
  /-- The per-residue value is the paper's reported nominal timing. -/
  matchesReportedNominal :
    secondsPerResidue = (AFPS2017.Flow.reportedNominalCycle.seconds : ℝ)

/-- Inputs needed to turn nominal chain duration into conditional throughput. -/
structure AnnualThroughputModel : Type where
  /-- Number of synthesis lines operating in parallel. -/
  parallelLines : Nat
  /-- Ideal timing assumptions used for each line. -/
  timing : IdealTimingModel
  /-- Supplied annual uptime, measured in seconds. -/
  uptimeSeconds : ℝ
  /-- The supplied uptime cannot be negative. -/
  uptimeNonnegative : 0 ≤ uptimeSeconds

/-- Nominal synthesis duration for a residue count under zero added overhead. -/
def nominalSynthesisSeconds (model : IdealTimingModel) (residueCount : Nat) : ℝ :=
  (residueCount : ℝ) * model.secondsPerResidue + model.additionalSeconds

/-- Conditional chain-equivalent output from uptime and parallel-line inputs. -/
noncomputable def annualNominalChains
    (model : AnnualThroughputModel) (residueCount : Nat) : ℝ :=
  (model.parallelLines : ℝ) * model.uptimeSeconds /
    nominalSynthesisSeconds model.timing residueCount

/-- Thirty nominal residue cycles take exactly 1200 seconds. -/
theorem thirtyResidues_nominalSeconds (model : IdealTimingModel) :
    nominalSynthesisSeconds model 30 = 1200 := by
  rw [nominalSynthesisSeconds, model.matchesReportedNominal,
    model.excludesSetupSwitchingMaintenancePurificationDowntime]
  norm_num [AFPS2017.Flow.reportedNominalCycle]

/-- The same thirty-residue nominal duration is exactly twenty minutes. -/
theorem thirtyResidues_nominalMinutes (model : IdealTimingModel) :
    nominalSynthesisSeconds model 30 / 60 = 20 := by
  rw [thirtyResidues_nominalSeconds model]
  norm_num

end AFPS2017.Yield
