# ChemistryLib — verified mathematical chemistry

ChemistryLib is a source-grounded Lean library for reaction networks,
thermodynamics, kinetics, stochastic chemistry, photochemistry, and selected
chemical models. It is generated and checked through Archon's clean-room
library campaign without importing legacy Chemistry or CRNT implementations.

`AFPS2017` adds a source-grounded formalization of selected sequence, flow,
yield, and analytical claims from the automated flow peptide synthesis work
reported by Mijalis et al. (2017).

## Install and build

Install [elan](https://github.com/leanprover/elan), then clone the release
branch and enter this Lake project:

```bash
git clone https://github.com/humanfia/chemlib.git
cd chemlib/chemistrylib
lake build
lake env lean ChemistryLib.lean
lake env lean AFPS2017.lean
```

The checked-in toolchain and manifest pin Lean, Mathlib, and Physlib. The first
build fetches those dependencies; subsequent builds reuse `.lake/`.

To consume ChemistryLib from another Lake project, use the repository's
`chemistrylib` subdirectory as the Git dependency and import `ChemistryLib`.
The repository-root README contains the exact `lakefile.toml` declaration.
To use the AFPS extension, import `AFPS2017`; both barrels may be imported in
the same downstream project.

## Release status

All thirteen ordinary capability families in the declared campaign DAG are
verified. The synthetic `chemistrylib.complete` root is also verified after its
independent sealed-holdout, standalone-extraction, clean-room, coverage, and
aggregate-build gates passed. It remains an aggregate root, not a fourteenth
ordinary family. The canonical global release-certificate hash is
`8f90fb79cb3c729eb77e99ad2842483860369032995fb92f1c3aaf8d691884fc`.

The current release adds the `autocatalysis.oscillation` family: integer
hyperflows, stoichiometric autocatalysis criteria, Milo/Nghe witnesses and
one-way dual-certificate soundness, an exact Oregonator Jacobian, separate
spectral-crossing and exact periodic-orbit certificates, and sealed-frontier
transfer under explicit dynamics-compatibility premises. A crossing certificate
alone is not presented as proof of a Hopf bifurcation or periodic motion.

`AFPS2017` is independently verified as four ordinary capability families:
solid-phase sequence assembly; dimensioned flow, yield, and throughput;
provenance-tagged mass and signal analytics; and scalar-composability proofs
that preserve a reported-versus-computed source conflict while keeping actual
flow conditional on an explicit constant-flow model.

Its synthetic `pentelute.afps2017.complete` root passed the aggregate build,
clean-room, source-coverage, standalone-extraction, and independently frozen
sealed-holdout gates. The canonical AFPS2017 global release-certificate hash is
`650beec3d11a440c0aa89e19ae8833d584d9ddada2f65894d2a689598e14bfae`.

Experimental observations are represented as source-addressed data or explicit
model inputs. The library does not turn reported masses, peak intensities,
timings, or step records into unconditional claims of molecular identity,
purity, yield, experimental success, reactor performance, or a complete
chemical mechanism.

## Grounding boundary

Mathlib is the general mathematical foundation. Physlib is reused through the
exact, hash-locked imports recorded in `campaign/grounding-policy.json`,
including units, quantum adapters, thermodynamic and statistical-mechanics
interfaces, and `Physlib.Mathematics.FDerivCurry`. The Physlib umbrella and
legacy Chemistry/CRNT implementations are forbidden dependencies.

The AFPS grounding policy additionally admits Physlib's continuity interface
only through the explicit conditional adapter recorded in its evidence bundle.

## Verification

```bash
lake build
lake env lean ChemistryLib.lean
lake env lean AFPS2017.lean
```

The public release can be compiled without Archon. Maintainers with the
separate generation controller can additionally replay the campaign-specific
validation workflow.

The reviewed CapabilityIR, module DAG, API lock, grounding policy, global-goal
binding, and release certificate are published under `campaign/`. The release
passes API ownership, axiom, symbol-DAG, migration, and full-build gates with no
`sorry`, `admit`, or project-defined axioms.

The AFPS2017 evidence is namespaced under `campaign/afps2017/`. It includes the
four locked family plans and bindings, the append-only goal revision, aggregate
external-pass certificates, and the finalized synthetic-root certificate.
