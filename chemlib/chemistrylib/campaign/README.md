# ChemistryLib campaign status

This directory publishes the reviewed, source-grounded state of the long-running
Archon ChemistryLib build. Runtime locks, sanitized corpus views, evidence logs,
and queues remain under ignored `.archon/` directories; the files here are the
public, reviewable snapshot.

## Released capability families

All thirteen ordinary capability families are verified. The synthetic
`chemistrylib.complete` release root is not included in that denominator.

1. `reaction_network.core`: finite indexed complexes and reactions, reaction
   quivers and linkage, composition and incidence matrices, stoichiometric
   matrices and conservation covectors, and algebraic mass-action systems.
2. `reaction_network.balance`: reaction-network-native weighted Laplacians,
   mass-action factorization, detailed and complex balance, and the proved
   implications from positive balanced fluxes to weak reversibility.
3. `chemistry.foundations`: amount-aware dimensions and typed quantities,
   amount of substance, concentration, signed stoichiometric numbers, and
   reaction progress.
4. `reaction_network.deficiency`: network-native linkage classes, incidence and
   stoichiometric ranks, and a natural-valued deficiency with exact
   reconstruction theorems under an explicit incidence-rank certificate.
5. `reaction_network.incidence_rank`: the incidence image as the
   linkage-class-wise zero-sum subspace, the universal incidence-rank formula,
   unconditional deficiency reconstruction, and deficiency as the dimension of
   the complex-composition kernel restricted to the incidence image.
6. `reaction_network.terminal_kernel`: terminal strong components, one
   nonnegative positive-on-support weighted-Laplacian kernel generator per
   terminal component, a basis and spanning theorem for the full kernel, and
   exact kernel and image dimensions.
7. `reaction_network.deficiency_zero_stability`: the deficiency-zero bridge,
   pseudo-Helmholtz nonnegativity and complex-balance dissipation, positive
   compatibility-class geometry and uniqueness, and complex-balanced existence
   for weakly reversible deficiency-zero networks with positive rates.
8. `kinetics.closed_form`: positive mass-action rate switching, first-order and
   scalar steady-state closed forms, approximate steady states, reaction
   enthalpy and temperature correction, ideal-gas combustion energy,
   adsorption capacity, production yield, and finite-run recycle formulas.
9. `models.sbml_ode`: source-shaped finite SBML records, parameterized real
   composition over a fixed natural reaction skeleton, symbolic incidence
   compilation, curated Oregonator endpoints and stoichiometry, and exact
   mass-action flux and three-coordinate ODE identities.
10. `stochastic.reaction_networks`: guarded count-state firing, stochastic
    mass-action propensities, finite jump generators and stationary measures,
    order-coupling certificates, Poisson product weights, and normalized
    finite-class product-form stationary distributions from complex balance
    and the deficiency-zero theorem.
11. `photochemistry.quantum_adapters`: absorbed-photon observations and explicit
    differential and integral quantum-yield domains, together with thin,
    axiom-audited Physlib adapters for quantum systems, the Planck constant,
    hydrogen, and tight-binding chains.
12. `thermodynamics.open_networks`: chemostat partitions, broken conservation
    laws, affinities and entropy production, open-network energy and free-energy
    balances, emergent-cycle ranks, relative entropy, and chemical-work
    inequalities, with exact Physlib thermodynamic and statistical-mechanics
    adapters where their assumptions match chemistry.
13. `autocatalysis.oscillation`: integer hyperflows and stoichiometric
    autocatalysis criteria; Milo/Nghe witness structures and one-way
    dual-certificate soundness; an exact Oregonator Jacobian with a Physlib
    derivative adapter; separate spectral-crossing and exact periodic-orbit
    certificates; and sealed-frontier transfer under an explicit dynamics-
    compatibility premise.

`global-goal-state.json` records the exact campaign ID, capability list, plan
hash, and release-certificate hash for each verified family. The current
autocatalysis and oscillation evidence is published in `api-lock.json`,
`release-certificate.json`, and `library-plan.json`; the original v0.1 core
binding remains available in `reaction-network-core-binding.json`.
`lean-symbol-dag.json` is derived from Lean `.olean` metadata, and
`lean-symbol-dag-validation.json` checks that those real symbol dependencies
agree with the locked module/API ownership.

The Family 13 release certificate has canonical hash
`f2915d28c25522ddc7d9ec8fe7e54e28c9a28f5317a5b346b1e31b3cb9ea0c68`.
Its global-goal binding has canonical hash
`e244efa3dd4c2cc20971ea28434d2d3c2c330ec76d2aa46139f12b6b0afad81d`.

The synthetic `chemistrylib.complete` root is verified. Its global release
certificate is published in `global-release-certificate.json` and has canonical
hash `8f90fb79cb3c729eb77e99ad2842483860369032995fb92f1c3aaf8d691884fc`.

## Mathlib and Physlib grounding

Mathlib remains the general mathematical foundation. ChemistryLib now also has
an exact, reproducible Physlib dependency:

- repository: `https://github.com/leanprover-community/physlib`;
- revision: `1706ae68b63996f1d97717e672e50c9e3933d933`;
- admitted modules: the exact, hash-locked set in `grounding-policy.json`,
  covering units, the four quantum adapters, temperature and ideal-gas
  interfaces, a finite canonical ensemble, and
  `Physlib.Mathematics.FDerivCurry`.

The chemical-dimension layer reuses Physlib's five physical exponents and adds
only the missing amount-of-substance exponent. The photochemistry,
thermodynamics, and Oregonator derivative adapters use only the explicitly
admitted modules. They do not import the Physlib umbrella or treat LeanExplore
search visibility as import authorization.
`grounding-policy.json` contains the exact import and package allowlists. Legacy
`CRNT`, `Chemistry`, and `IChO2026Chem` dependencies remain forbidden.

## Completed dependency cones

The released `autocatalysis.oscillation` family keeps its logical boundaries
explicit: an imaginary-eigenpair crossing certificate does not by itself imply
a Hopf bifurcation or periodic motion; integer dual certificates establish the
proved soundness direction only; and sealed-frontier transfer requires the
recorded pointwise dynamics compatibility and nonconstancy premises.

`global-goal.json` describes the thirteen-family Capability DAG plus its
synthetic completion root. `global-goal-state.json` is the current public state
snapshot: all thirteen ordinary families and the synthetic completion root are
verified. The synthetic root is a separate aggregate state and is not counted
as a fourteenth ordinary family.

## AFPS2017 extension

The independent AFPS2017 formalization and its four-family goal are published
under [`afps2017/`](afps2017/). That namespaced bundle preserves the original
campaign evidence files byte-for-byte, publishes the AFPS source
grounding, exact family locks and bindings, append-only goal revision, aggregate
external-pass certificates, and finalized synthetic-root certificate without
mixing either campaign's evidence.
