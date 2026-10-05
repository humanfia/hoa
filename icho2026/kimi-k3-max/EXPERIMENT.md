# IChO 2026 Humanize experiment: Kimi-K3 max

## Objective

Solve all nine official IChO 2026 theoretical problems with nine isolated
natural-language workers, one problem per worker, using Kimi-K3 at maximum
reasoning for both implementation and every Humanize review.

## Configuration

- Codex home: `/root/.codex-magikcloud`
- Worker model: `Kimi-K3`
- Worker reasoning effort: `max`
- Humanize reviewer: `Kimi-K3` at `max`
- Focused image-aware auditor: `Kimi-K3` at `max`
- Provider URL: `https://api.magikcloud.cn/v1` (unchanged, direct)
- Parallelism: nine isolated Git worktrees and branches
- Maximum implementation/review rounds per problem: 8
- Maximum original-review call time: 7200 seconds
- Maximum focused-audit call time: 10800 seconds
- Maximum worker session time: 43200 seconds
- Response format: natural-language Markdown with calculations and textual
  representations of chemical structures
- Formal prover: none
- Original-worker sources: only the assigned official problem PDF text/page
  images and the local general booklet; prior answers, external keys, web
  search, and cross-worker communication were prohibited
- Post-run audit source: the same official material, plus the preserved
  GPT-5.6 result solely as a non-authoritative discrepancy detector; every
  discrepancy still had to be adjudicated from the official source and
  chemistry by Kimi-K3

## Methodological precedent

This run follows the preserved GPT-5.6 max experiment on branch
`gpt56-sol-max-results`: an unsolved scaffold, one branch/worktree per problem,
the same nine tracked natural-language plans, iterative independent review,
structural validation, and final consolidation only after all loops complete.
The prior experiment used Humanize's native Stop-hook state machine. This run
uses Humanize's `ask-codex` consultation workflow and records its own explicit
round ledger; it does not claim native RLCR state files that it did not create.

## Direct natural-language workflow

Every implementation turn is a direct, tool-free request through the specified
MagikCloud home. The official extracted source is embedded and all official
page images are attached. The runner writes the returned Markdown externally.
Each candidate is then sent to Kimi-K3 through Humanize's `ask-codex`
consultation workflow. Actionable feedback triggers another complete
natural-language implementation turn; only a review whose final nonempty line
is `COMPLETE` advances the solution to validation and commit.

The same-model text reviews sometimes accepted diagram-heavy mistakes. To
avoid treating those false positives as success, every original result was
then subjected to a focused post-run gate: an image-aware Kimi-K3/max audit and
a separate Humanize Kimi-K3/max audit both had to end in `COMPLETE`. The prior
GPT-5.6 solution was visible only inside this post-run gate to identify points
of disagreement; it was not treated as an answer key.

Two transport accommodations were necessary without changing the provider,
model, or reasoning level. Q6 and Q9 were relaunched without the nested
Bubblewrap sandbox so all official images could be attached. When model-side
image-tool calls made Q9's Codex transport return HTTP 400, Q9 and the affected
focused audits used a no-tools Responses client that reads the same Codex home
and asserts the exact configured URL before every call. Raw response ledgers
record `model: Kimi-K3`,
`provider_url: https://api.magikcloud.cn/v1`, and
`tools_advertised: false`.

## Outcome

All nine original workers completed, all nine focused post-run gates completed,
and all nine final solutions are consolidated. The worker launch wave began at
2026-08-11 13:07 UTC; the last corrective audit completed at
2026-08-11 14:58 UTC.

The original text-only Humanize loops all reached `COMPLETE`, but that was not
accepted as sufficient evidence. The focused gate corrected eight solutions;
Q2 was the only solution that remained unchanged. Q9 received an additional
round-0 gate after a manually noticed `imidazole`/official-`pyridine`
transcription discrepancy. Both reviewers accepted the corrected reagent.

Round numbers below are zero-based. “Original” is the isolated worker's final
implementation/review round; “focused” is the final image-aware plus Humanize
audit round.

| Problem | Preserved source branch | Original | Focused | Final source head | Bytes | Result |
|---|---|---:|---:|---:|---:|---|
| Q1 | `humanize-kimi-k3max-q01` | 4 | 1 | `f3405ff2` | 10092 | Corrected; COMPLETE |
| Q2 | `humanize-kimi-k3max-q02` | 2 | 0 | `b28054c9` | 9238 | Unchanged; COMPLETE |
| Q3 | `humanize-kimi-k3max-q03` | 3 | 1 | `e9a988e3` | 16716 | Corrected; COMPLETE |
| Q4 | `humanize-kimi-k3max-q04` | 0 | 0 | `b8a900fc` | 7270 | Corrected; COMPLETE |
| Q5 | `humanize-kimi-k3max-q05` | 1 | 1 | `b8d8658c` | 16764 | Corrected; COMPLETE |
| Q6 | `humanize-kimi-k3max-q06` | 0 | 3 | `1b859e6f` | 18671 | Corrected; COMPLETE |
| Q7 | `humanize-kimi-k3max-q07` | 1 | 0 | `e9a600f7` | 12018 | Corrected; COMPLETE |
| Q8 | `humanize-kimi-k3max-q08` | 0 | 0 | `85bb1b47` | 13053 | Corrected; COMPLETE |
| Q9 | `humanize-kimi-k3max-q09` | 2 | 1 + final 0 | `ed504bb4` | 18145 | Corrected twice; COMPLETE |

## Material corrections found by the focused gate

- Q1: identified X as linalool (compound 6), retained cineole as Y, and
  synchronized the terpene structures and symmetry arguments.
- Q3: restored the printed monomer-label/topology table; replaced the invented
  COF-7 dia framework with the Kagome-derived `cyclo[V-L]6`; corrected AB and
  AB-prime stacking energies to -49.8 and -55.6 kJ/mol; corrected uptake to
  1.00 uranyl ion per pore.
- Q4: corrected the fission products to Rb-93 and Cs-140.
- Q5: corrected the odd-fragment count, proton relay, lipid structures,
  halogen reagent, PL3 ethyl phosphate, and hydrolysis balance.
- Q6: corrected the triplet aromaticity table, dehalogenation radicals,
  catenane mass assignments, F-L route, zinc-porphyrin labels, and global
  82-electron aromaticity; later rounds removed three detailed-explanation
  inconsistencies.
- Q7: corrected the process-flow interpretation, methane demand, amine CO2
  capture, Mo-PNP dimer, and yield ranking `B > C > D > A`.
- Q8: corrected the catalyst structures/electron counts, surface density,
  trend explanation, and light mapping to `a=N, b=B, c=G, d=R` from the
  official energy diagram.
- Q9: replaced ordinary protected CD structures with the printed 3,6-anhydro
  K and 2,3-anhydro Y; corrected X to 21 stereocentres, the dimer linkages,
  sodium-adduct peaks to 1299/1731, and the complete shared `J_X(2,5)` bridge
  sequence; a final pass restored the printed pyridine reagent.

## Verification

The final audit established all of the following:

- all nine original `runtime/status.json` ledgers have `state=complete`,
  `ok=true`, `humanize_complete=true`, validator exit 0, `model=Kimi-K3`,
  `effort=max`, Codex home `/root/.codex-magikcloud`, and the exact MagikCloud
  URL;
- all nine final post-audit ledgers have both `image_audit_complete=true` and
  `humanize_complete=true`, and both final review files end in `COMPLETE`;
- all 48 retained Humanize metadata records report `model: Kimi-K3`,
  `effort: max`, and `status: success`;
- all 22 retained current/final no-tools response ledgers report
  `model=Kimi-K3`, `status=completed`, the exact provider URL, and
  `tools_advertised=false`;
- `scripts/validate_solution.py` passes for Q1-Q9 on the consolidated branch,
  and `git diff --check` passes;
- each consolidated solution's SHA-256 digest exactly matches its final worker
  head, and every isolated worktree has no tracked changes; and
- no worker or post-audit process remains active.

During Q9's first focused round, the image and text audits disagreed on two
values. The conflict was resolved directly from the official local pages.
Page 2 places X on the separate
periodate-cleavage branch, leaving three stereocentres per residue (21 total).
Page 4 explicitly prints `C27H28O5` and `C22H25O4`; adding the drawn acetate cap
gives the 1299 and 1731 sodium-adduct peaks. The final candidate, image audit,
and Humanize audit all agree on those values.

## Provider integrity and preservation

The temporary localhost relay explored before the recorded worker wave was
removed before launch and is not part of this experiment. During the recorded
run, `/root/.codex-magikcloud/config.toml` remained configured as:

```toml
model_provider = "magikcloud"
model = "Kimi-K3"
model_reasoning_effort = "max"

[model_providers.magikcloud]
base_url = "https://api.magikcloud.cn/v1"
```

The final configuration contains no localhost or `127.0.0.1` provider entry.

- Consolidated branch: `kimi-k3-max-results`
- Consolidated worktree:
  `/root/zhengyang-workspace/icho-2026-humanize-kimi-k3-max-results`
- Audited solution snapshot before this report/index commit: `8f0610d`
- Preserved prior comparison branch: `gpt56-sol-max-results`

The consolidated branch starts from the clean unsolved Kimi scaffold and
preserves the nine reviewed solutions, audit method, discrepancy ledgers, and
this report without overwriting the earlier experiment.
