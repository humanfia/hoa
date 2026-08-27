# Chemlib

Chemlib is a verified Lean 4 library for mathematical chemistry. This
release also includes `AFPS2017`, a source-grounded formalization of selected
sequence, flow, yield, and analytical claims from the automated flow peptide
synthesis work reported by Mijalis et al. (2017).

The buildable Lake project is in [`chemistrylib/`](chemistrylib/). This public
repository contains release sources and reviewable verification metadata; it
does not contain generation agents, private holdout cases, or controller logs.

## Requirements

- Git
- [elan](https://github.com/leanprover/elan), which installs the Lean toolchain
  selected by `chemistrylib/lean-toolchain`
- Network access on the first build so Lake can fetch the pinned Mathlib and
  Physlib revisions

## Clone and compile

```bash
git clone https://github.com/humanfia/chemlib.git
cd chemlib
./reproduce.sh
```

Verify either public entrypoint directly:

```bash
cd chemistrylib
lake env lean Chemlib.lean
lake env lean AFPS2017.lean
```

The first build downloads and compiles the locked dependencies. Later builds
reuse `.lake/` and are incremental.

## Use from another Lake project

Add this dependency to the downstream project's `lakefile.toml`:

```toml
[[require]]
name = "chemistrylib_v1"
git = { url = "https://github.com/humanfia/chemlib.git", subDir = "chemistrylib" }
rev = "main"
```

Then update the manifest and build:

```bash
lake update
lake build
```

Import the general library, the AFPS formalization, or both:

```lean
import Chemlib
import AFPS2017
```

For reproducible downstream releases, replace `main` with a release tag or a
specific commit hash. The project targets Lean `v4.31.0` and pins both Mathlib
and Physlib in `lake-manifest.json`. See [REPRODUCE.md](REPRODUCE.md) for a
fresh-machine walkthrough.

## AFPS2017 scope and boundary

The AFPS extension contains 22 modules in four verified capability families:

- conditional solid-phase sequence assembly;
- dimensioned flow accounting, source arithmetic, step yield, and idealized
  throughput;
- provenance-tagged mass and signal observations, including the checked
  25-row conotoxin mass table;
- scalar composition theorems that preserve the reported-versus-computed
  amino-acid amount conflict and keep actual flow conditional on an explicit
  constant-flow model.

The formalization proves typed models and source-addressed arithmetic. It does
not infer molecular identity, purity, yield, experimental success, reactor
performance, or a complete chemical mechanism unless those conclusions are
supplied by explicit hypotheses.

## Verification evidence

The original Chemlib evidence remains under
[`chemistrylib/campaign/`](chemistrylib/campaign/). AFPS2017 has an independent,
namespaced evidence chain under
[`chemistrylib/campaign/afps2017/`](chemistrylib/campaign/afps2017/), including
all four family locks and bindings, the goal revision, aggregate external-pass
certificates, and the synthetic-root release certificate.

Machine-generated JSON and JSONL evidence is preserved byte-for-byte from the
pre-rename generation run so its hash chains remain valid. Any old library
identifier inside those immutable records is historical provenance, not the
current Lean module name.

The AFPS2017 global release-certificate hash is
`650beec3d11a440c0aa89e19ae8833d584d9ddada2f65894d2a689598e14bfae`.
See [`chemistrylib/README.md`](chemistrylib/README.md) for the detailed scope and
verification boundary.
