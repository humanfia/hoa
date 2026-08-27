# Minimal reproduction

This guide rebuilds the public Chemlib release and checks both public
entrypoints, including the AFPS2017 formalization of selected claims from
Mijalis et al. (2017), A Fully Automated Flow-Based Approach for Accelerated
Peptide Synthesis.

## Requirements

- Git
- a POSIX shell (Linux, macOS, or WSL)
- elan: https://github.com/leanprover/elan
- network access for the first dependency and Mathlib cache download

No Python package, Archon runtime, private dataset, or private credential is
required. Lean, Mathlib, and Physlib versions are fixed by lean-toolchain,
lakefile.toml, and lake-manifest.json.

## One-command check

Run:

    git clone https://github.com/humanfia/chemlib.git
    cd chemlib
    ./reproduce.sh

The script prints the selected Lean version, fetches the Mathlib binary cache
when available, builds both Lake targets, and elaborates the two public barrel
files directly. Success means every command exits with status zero. The
selected toolchain is leanprover/lean4:v4.31.0.

To run the steps manually:

    cd chemistrylib
    lake exe cache get
    lake build
    lake env lean Chemlib.lean
    lake env lean AFPS2017.lean

## What is reproduced

- the complete general Chemlib Lean build;
- all 22 AFPS2017 modules in the sequence, flow/yield, analytics, and scalar
  composability families;
- the public entrypoint AFPS2017.lean;
- the checked release evidence under chemistrylib/campaign/afps2017/.

The AFPS2017 release certificate records four of four verified families, zero
sorry declarations, complete declared-source coverage, a successful aggregate
Lake build, and independent sealed-holdout and standalone-extraction passes.
Its canonical certificate hash is
650beec3d11a440c0aa89e19ae8833d584d9ddada2f65894d2a689598e14bfae.

## Scientific boundary

This reproduction checks typed models, conditional deductions, and
source-addressed arithmetic. It does not infer molecular identity, purity,
experimental success, reactor performance, or a complete chemical mechanism
from reported measurements alone. Those distinctions are explicit in the Lean
interfaces and in the published verification bundle.
