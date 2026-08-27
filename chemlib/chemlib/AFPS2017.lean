import AFPS2017.Analytics.ConotoxinTable
import AFPS2017.Analytics.MassAgreement
import AFPS2017.Analytics.MassObservation
import AFPS2017.Analytics.Provenance
import AFPS2017.Analytics.SignalObservation
import AFPS2017.Flow.ChemistryAdapters
import AFPS2017.Flow.ContinuityAdapter
import AFPS2017.Flow.Protocol
import AFPS2017.Flow.Quantity
import AFPS2017.Flow.ScalarComposability
import AFPS2017.Flow.SourceLint
import AFPS2017.Sequence.Assembly
import AFPS2017.Sequence.Coupling
import AFPS2017.Sequence.Cycle
import AFPS2017.Sequence.Deprotection
import AFPS2017.Sequence.Residue
import AFPS2017.Sequence.State
import AFPS2017.Sequence.StoichiometryAdapter
import AFPS2017.Sequence.Target
import AFPS2017.Sequence.Wash
import AFPS2017.Yield.StepYield
import AFPS2017.Yield.Throughput

/-!
# AFPS 2017 formal benchmark

This is the public entrypoint for the source-grounded formalization of the
automated flow peptide synthesis protocol reported by Mijalis et al. (2017).
Generated modules are added here only after their API, proof, axiom, and build
gates have passed.
-/
