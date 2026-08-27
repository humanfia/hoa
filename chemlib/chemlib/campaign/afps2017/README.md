# AFPS2017 verification snapshot

This directory is the public, reviewable evidence bundle for the independent
`AFPS2017` formalization. Runtime queues, agent logs, source PDFs, and private
holdout cases are intentionally excluded.

## Release status

- Goal: `pentelute.afps2017.formal_benchmark.v1`
- Goal spec: `aaf1261e7a195a9e27b4e6e335ed13e66a22ca11a18ad21cadf14add174f794b`
- Ordinary families: 4/4 verified
- Synthetic root: `pentelute.afps2017.complete`
- Global certificate: `650beec3d11a440c0aa89e19ae8833d584d9ddada2f65894d2a689598e14bfae`
- Root binding: `db98705889ec6fe2f9ff44abdf82d1ad42e8aa24b61b877e4a4df6812c10b0b8`
- Entrypoint: 22 unique imports, source SHA-256 `299b329b41864b67e0cf3c0827e139feb9153b652e23824656ed7c390b0773c7`
- Source corpus: `cd8e8eccec6e2c32aff66d6af4c96b392fd832db5b0b0a333c34d84d99027e73`
- External certificates: holdout `f73cacc332cbdd5b4a5a0c9f1356dc8e11da711666a67652ce34f6a4e30d21f4`, extract
  `a213d251eab3156015f45d2c6fe49657a0d0dca11350365653278d9a0162cd7b`

The root certificate records a clean-room pass, zero `sorry`, full source
coverage, a successful aggregate Lake build, and both external-pass hashes. The
synthetic root is an aggregate state and is not a fifth ordinary family.

## Verified families

| Family | Modules | Plan hash | Release certificate |
| --- | ---: | --- | --- |
| `afps2017.sequence_solid_phase` | 9 | `be67aa408f356e084c73d5ffd93f1b5f8d88b276e61a38730c2aa745dda50c48` | `bb9a4c1c19505391c950da63b18e7f9d5f67062116b39e4c90939a8f21ea6a91` |
| `afps2017.flow_yield` | 7 | `720e71ab5e7a12159586cc353dd7b6f9040fa24beff79d9c41bdc787a0a4a8a3` | `c17360aa9ea96ddb27923a5aea05049a47bf48056bd82f5170807094e6de62ec` |
| `afps2017.analytics_cert` | 5 | `1615625c19f7f4a28f9849451a188cd16a4139d0d3d7b87c9afac2cfec73d0f5` | `257a51c91e876db50c913228ab2b06af44fd377995076c8cfd22c76f7c081bcf` |
| `afps2017.scalar_composability` | 1 | `1c43e040cd821f7f400e28e283a17d332c3bdbf16c12b4a06768dadd50a8201e` | `3f755e9c8f3adf3f143ee1bc3c8365caa5046332c69b3c0ed001ac95bc7a6a6a` |

Each family directory publishes the reviewed capabilities, locked module plan,
exact API lock, Lean-derived symbol DAG and validation, and release certificate.
The `bindings/` directory publishes the four family bindings and root binding.

## Evidence layout

- `global-goal.json` is the stable revised goal contract.
- `global-goal-state.json` is the finalized 4/4-plus-root state.
- `goal-revisions/` contains the single prior spec needed to authenticate the
  three bindings preserved across the append-only scalar-composability repair.
- `grounding-policy.json` freezes the exact Mathlib/Physlib boundary.
- `families/` contains the four family-specific release bundles.
- `bindings/` contains four ordinary bindings and the synthetic-root binding.
- `external/` contains only the two aggregate, context-bound pass certificates;
  no private holdout cases or evaluator logs are published.

## Formalization boundary

The sequence and flow models are conditional where chemistry or hardware
behavior is not established by the sources. Analytical values remain
source-addressed observations, and the arithmetic source conflict is preserved.
Nothing in this release upgrades those records to unconditional claims about
molecular identity, purity, yield, experimental success, reactor performance,
or a complete chemical mechanism.
