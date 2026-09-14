# Humanfia at IChO 2026

> [!NOTE]
> This is part of RSI Effort at NVIDIA Research. [Humanize](https://github.com/humanfia/humanize2) is an open agent loop/flow framework that led by [NVIDIA Research](https://www.nvidia.com/en-us/research), [UCLA PolyArch](https://polyarch.cs.ucla.edu), and [MIT HAN Lab](https://hanlab.mit.edu). We are skying the limit with the power of agents with community members.

The **GPT full-theory experiment has completed all 68/68 Lean formalization targets across the 9 IChO 2026 theory problems**, under their declared input scopes: **66 original-input results and 2 explicitly conditional results**. See the [complete formalization release](gpt-5.6-sol-full68-formalization/). This is a formalization-completion result, **not a claim of 100% official-answer accuracy**.

**Kimi-K3 has now also completed all 68 numbered theory subquestions**: the earlier [32-target answer-blind run](kimi-k3-answer-blind/) plus the [remaining 36 formalizations](kimi-k3-nl-36-formalization/). Combined coverage is **68/68** under those two releases' disclosed scopes. This is likewise formalization completion, **not a claim of 100% official-answer accuracy**.

The earlier GPT selected-set experiment remains **32/32 answer-blind**. The projects are pinned to Lean 4.31.0 and Mathlib v4.31.0.

We build with open source, and build for open source. We **release everything** including:

* the [complete GPT full-theory formalization: 68 subquestions](gpt-5.6-sol-full68-formalization/), including the latest T8-A8 contest-model proof and its 12 checked lemmas;
* the [GPT-5.6 Sol native Codex `/goal` baseline](gpt-5.6-sol-native-goal68/): 68/68 compiled, **32/68 (47.06%)** independently accepted;
* the [Kimi-K3 remaining 36 formalizations](kimi-k3-nl-36-formalization/), which together with the [earlier 32 answer-blind targets](kimi-k3-answer-blind/) cover all 68 theory subquestions;
* the final answer-blind Lean 4 statements and proofs [Kimi-K3](./kimi-k3-answer-blind) and [GPT-5.6 Sol](./gpt-5.6-sol-answer-blind);
* the final worked solutions [Kimi-K3](./kimi-k3-max/solutions) and [GPT-5.6 Sol](./gpt-5.6-sol-max/solutions);
* the grading reports, experiment records, checksums, and provenance used to audit the results.

Notably, humanize enables **open source models like Kimi-K3** to achieve **68/68 Lean formalization coverage at IChO 2026** (32 answer-blind + 36 remaining) as well! As [Jensen shared](https://x.com/JensenHuang/status/2080643682408321103), We all love _open models X open harness_ 🎉 and the combination achieves full score at every competition:
* [IMO2026](https://github.com/humanfia/imo2026) / [IOI2026](https://github.com/humanfia/ioi2026) / [IPhO2026](https://github.com/humanfia/ipho2026) / [IChO2026](https://github.com/humanfia/icho2026) / [IBO2024](https://github.com/humanfia/ibo2024)


## Results

### Separate native Codex `/goal` baseline

| Experiment | Scope | Lean compilation | Semantic review | Combined acceptance | Official-answer score |
|---|---:|---:|---:|---:|---|
| [GPT-5.6 Sol native `/goal`](gpt-5.6-sol-native-goal68/) | 68 subquestions, peak 32 concurrent | 68/68 | 45/68 | **32/68 (47.06%)** | Incomplete; no aggregate score claimed |

This fresh answer-blind baseline uses native persisted goals, **not the Humanize
review/redraft solver loop**. Independent post-run reviews did not feed back into
the solvers. All 68 original outputs, including rejected and conditional results,
are preserved. The 47.06% figure is formalization acceptance, not official-answer
accuracy. See the [protocol, scoring limitations and per-target evidence](gpt-5.6-sol-native-goal68/).

### Full theory formalization: 68/68 targets accepted

| Experiment | Theory coverage | Formalization review | Proof review | Declared scope |
|---|---:|---:|---:|---|
| [GPT-5.6 Sol full68](gpt-5.6-sol-full68-formalization/) | **9 problems / 68 numbered subquestions** | **68/68** | **68/68** | **66 original-input + 2 conditional** |
| [Kimi-K3 32+36](kimi-k3-nl-36-formalization/) | **9 problems / 68 numbered subquestions** | **68/68** | **68/68** | **32 answer-blind + 31 original Kimi-NL + 3 conditional + 2 authorized corrections** |

All theoretical-paper formalization targets have passed the experiment's
acceptance gates. **T4-A8** supplements the printed flow unit with `m³/day`.
**T8-A8** uses two user-authorized, experiment-local contest-model axioms: the
dark condition has no drawn H₂/CO product stack, and higher photon energy among
the three illuminated conditions implies a strictly larger H₂ mole fraction.
These are disclosed model inputs, not additional facts proved from the problem
figures or universal chemistry laws. The latest T8 proof concludes
`a=N, b=B, c=G, d=R` and includes 12 rechecked lemmas.

Kimi-K3's **68/68** is the union of two published campaigns, not a fresh
full-paper answer-blind rerun. The additional [36-target release](kimi-k3-nl-36-formalization/)
formalizes supplied Kimi natural-language answers. Its disclosed scopes are
**T2-A6**, **T7-A6** and **T8-A8** (conditional contest-model inputs) plus
authorized answer corrections on **T1-A1** and **T8-A4**. The remaining 31 of
those 36 preserve the original Kimi answers. Combined with the earlier 32
answer-blind targets, that is **68** distinct numbered subquestions.

Lean checks deductions from the encoded inputs; it does not itself certify
that every encoding matches the official chemical answer. Post-run answer
scoring is separate and is not represented by **68/68**. The historical
selected-set scores in their own section belong to different experiments.

### Full68 answer scoring — generous, non-official

| Run | Raw points | Raw accuracy | Weighted theory score | Weighted accuracy |
|---|---:|---:|---:|---:|
| [GPT-5.6 Sol full68](gpt-5.6-sol-full68-formalization/grading/GRADING.md) | **424.5/437** | **97.14%** | **58.736/60** | **97.89%** |
| [Kimi-K3](kimi-k3-max/GRADING.md) | **417.5/437** | **95.54%** | **58.209/60** | **97.02%** |

This user-requested generous grading accepts equivalent representations,
reasonable rounding and justified partial credit, without erasing substantive
chemical errors. It is **not an official IChO jury score**. GPT's remaining
deductions are T3-A3 (15/23) and T8-A4 (24.5/29). Kimi's published score is the
independent official-key regrade of the nine natural-language solutions; the
32+36 Lean artifacts were not given a second generous marking. Formalization
**68/68** and these answer scores measure different things.

### Historical selected-set answer-blind Lean results

The models received the official problem statements and images, but not the
official solutions. Official-answer comparison happened only after generation
and review had finished.

The independent post-run comparison reports an expected **168/168 raw rubric
points (100%) on the 32 selected theory subquestions** for both GPT-5.6 Sol
and Kimi-K3, covering 47 requested outputs. This selected-set score is
separate from the full theoretical-paper run; it does not cover the remaining
theory subquestions or the practical examination. See the [GPT validation report](gpt-5.6-sol-answer-blind/RESULTS.md)
for the numerical precision notes, known auxiliary-carrier limitation, and
source provenance. The score is a rubric-based reconstruction, not an official
IChO jury score.

| Run | Expected raw rubric points (selected set) | Formalization review | Proof review | Lean build | Placeholders | Official-answer comparison |
|---|---:|---:|---:|---:|---:|---:|
| [GPT-5.6 Sol](gpt-5.6-sol-answer-blind/) | **168/168 (100%)** | **32/32** | **32/32** | passed | 0 | **47/47 outputs** |
| [Kimi-K3](kimi-k3-answer-blind/) | **168/168 (100%)** | **32/32** | **32/32** | passed | 0 | **47/47 outputs** |

The normalized records are published in the
[`humanfia-lab/icho-2026`](https://huggingface.co/datasets/humanfia-lab/icho-2026)
dataset. Those records include official solution and rubric text as post-run
evaluation metadata; those fields were never model inputs.

### Historical natural-language runs

The earlier natural-language-only experiments are separate from the full68
formalization release. Their original grading reports remain available:
[GPT-5.6 Sol max](gpt-5.6-sol-max/GRADING.md) and
[Kimi-K3 max](kimi-k3-max/GRADING.md). Their scores are not reused for full68.

The historical Kimi campaign used `anthropic-kimi-k3` through Claude Code as
the model client, with Humanize providing the agent loop and review workflow.
Its four grounding-log completeness warnings are disclosed in the run README;
they do not change the compile or proof-review results.

## Reproduce the verified result

Clone the repository and verify the released files:

```bash
git clone https://github.com/humanfia/icho2026.git
cd icho2026

for run in gpt-5.6-sol-answer-blind kimi-k3-answer-blind kimi-k3-nl-36-formalization gpt-5.6-sol-native-goal68; do
  (cd "$run" && sha256sum -c CHECKSUMS.sha256)
done
```

Build the pinned Lean projects:

```bash
for run in gpt-5.6-sol-answer-blind kimi-k3-answer-blind kimi-k3-nl-36-formalization; do
  (
    cd "$run"
    lake exe cache get
    lake build
  )
done
```

A successful `lake build` type-checks the released formalizations and proofs
under the toolchain pinned inside each project.

For the complete 68-question GPT project and its separate 13-module T8 audit,
follow the [full68 reproduction instructions](gpt-5.6-sol-full68-formalization/#reproduce).
The Kimi remaining-36 project has its own [reproduction notes](kimi-k3-nl-36-formalization/#reproduce).
The native `/goal` baseline is separate per-target Lean projects; see its
[verification notes](gpt-5.6-sol-native-goal68/#released-files-and-local-verification).

## Released artifacts

- [`gpt-5.6-sol-max`](gpt-5.6-sol-max/solutions/) and
  [`kimi-k3-max`](kimi-k3-max/solutions/) contain `Q1.md` through `Q9.md`.
- Each full-paper run includes `GRADING.md` and `EXPERIMENT.md`.
- [`gpt-5.6-sol-answer-blind`](gpt-5.6-sol-answer-blind/) and
  [`kimi-k3-answer-blind`](kimi-k3-answer-blind/) are standalone Lean 4
  projects with pinned dependencies and checksums.
- [`kimi-k3-nl-36-formalization`](kimi-k3-nl-36-formalization/) is the
  remaining 36-target Kimi Lean project; together with
  [`kimi-k3-answer-blind`](kimi-k3-answer-blind/) it covers all 68 theory
  subquestions.
- [`gpt-5.6-sol-native-goal68`](gpt-5.6-sol-native-goal68/) is the separate
  native Codex `/goal` baseline over all 68 theory subquestions.
- [`FIRST_TURN_ABLATION.md`](kimi-k3-max/FIRST_TURN_ABLATION.md) compares the
  nine unreviewed Kimi round-0 outputs with the final Humanize result under the
  same grading convention.

## Scope

The preserved runs cover the nine **theoretical** problems. The separate
practical laboratory examination is not part of these model runs or scores.
