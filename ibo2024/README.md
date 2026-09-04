# Humanfia at IBO 2024

> This is part of RSI Effort at NVIDIA Research. [Humanize](https://github.com/humanfia/humanize2) is an open agent loop/flow framework that led by [NVIDIA Research](https://www.nvidia.com/en-us/research), [UCLA PolyArch](https://polyarch.cs.ucla.edu), and [MIT HAN Lab](https://hanlab.mit.edu). We are skying the limit with the power of agents with community members.

The **Humanfia team have aced all 100/100 theory tasks in the
International Biology Olympiad (IBO) 2024 Theoretical Exam** using a *fully
agentic, YOLO-style approach*. All 400/400 statement verdicts match the official
answer key, giving 100% agreement on the published grading target.

We build with open source, and build for open source. We **release everything**
including:

* the complete natural-language worked solutions for [Theory A](theory-a-solutions.md) and [Theory B](theory-b-solutions.md);
* the [official-answer summary](answers.md) and complete [grading evidence](GRADING.md);
* the [task plan](plan.md), [worker assignments](WORKERS.md), and [validation scripts](scripts/) used for problem solving.

## Results

The Humanfia (GPT-5.6) workers solved all 100 Theory A and Theory B tasks. The
results below report exact agreement with the answer sections embedded in the
official English exam papers.

| Part | Humanfia (GPT-5.6) | Official verdict agreement |
| --- | ---: | ---: |
| Theory A | ✅ 50/50 tasks | ✅ 200/200 (100%) |
| Theory B | ✅ 50/50 tasks | ✅ 200/200 (100%) |
| **Total** | **✅ 100/100 tasks** | **✅ 400/400 (100%)** |

The extraction and format error count is **0**. The complete grading evidence
is in [GRADING.md](GRADING.md).

This is an answer-key agreement grade for the 100 theory tasks, not an official
Olympiad points calculation. The repository intentionally excludes every
practical exam. The natural-language explanations were reviewed separately
against the local official questions and are protected by the reviewed-solution
manifest.

# Quick start

## Launch with the reproduction prompt

The complete launch prompt is checked in as [plan.md](plan.md).
[AGENTS.md](AGENTS.md) supplies the offline worker policy. The launch shell
creates a clean workspace containing the prompt, policy, and official PDFs, but
none of the published solutions:

```bash
bash scripts/run-ibo2024.sh \
  --prompt plan.md \
  --model gpt-5.6-sol
```

The shell passes `plan.md` directly to `codex exec`. The prompt assigns one
distinct worker to each of the 100 Theory A/B tasks and runs the review and
assembly workflow. Add `--dry-run` to validate the inputs without creating a
workspace or launching Codex.

## Reproduce the public result

Place the two official English exam PDFs at these exact local paths:

- `source/IBO2024 Theory A.pdf`
- `source/IBO2024 Theory B.pdf`

Create the pinned local text extracts used by the offline validator:

```bash
mkdir -p source
pdftotext -layout "source/IBO2024 Theory A.pdf" source/part-a.txt
pdftotext -layout "source/IBO2024 Theory B.pdf" source/part-b.txt
```

Then regenerate the derived collection, check that committed outputs are
current, and run the complete offline validation gate:

```bash
python3 scripts/build.py
python3 scripts/build.py --check
python3 scripts/validate.py
python3 scripts/test_validate.py
python3 -m py_compile scripts/build.py scripts/validate.py scripts/test_validate.py
git diff --check
```

The validator compares all 400 declared verdicts with the answer sections
embedded in the official PDFs. It invokes only local tools and files: it does
not browse, query a network service, or consult a third-party answer key.

The one-worker assignment contract in [plan.md](plan.md), the canonical
coordinates in [WORKERS.md](WORKERS.md), and the validation commands above
define how the 100 isolated results are assembled and accepted.

## Reproduce with Kimi-K3

The published solution corpus was produced by distinct `gpt-5.6-sol:max`
workers and reviewed with Humanize RLCR, as recorded in [WORKERS.md](WORKERS.md).
This repository does not label those files as Kimi-generated.

Kimi-K3 uses the same Codex harness, task contract, offline boundary, and review
loop as the archived GPT-5.6 runs. No separate Kimi launcher or Kimi CLI is
needed. In the existing Codex harness configuration, make only these two
changes:

- replace the API key in the Codex auth file with the Kimi API key;
- replace the Codex model name with the Kimi model name.

Then run the same checked-in prompt through the same Codex harness:

```bash
CODEX_HOME=/path/to/codex-home-with-kimi-api-key \
bash scripts/run-ibo2024.sh \
  --prompt plan.md \
  --model your-kimi-model-name
```

Keep the 100 task assignments, local official PDFs, prompts, output paths, and
validation commands unchanged. Each worker still receives one coordinate from
[WORKERS.md](WORKERS.md), follows [AGENTS.md](AGENTS.md), and is accepted only
after the repository-wide validation passes.

## Read the collection

- [Official answer summary](answers.md)
- [Theory Part A consolidated solutions](theory-a-solutions.md)
- [Theory Part B consolidated solutions](theory-b-solutions.md)
- [Part A individual solutions](solutions/part-a/)
- [Part B individual solutions](solutions/part-b/)
- [One-worker assignment ledger](WORKERS.md)

## Offline methodology and ownership

Exactly one distinct `gpt-5.6-sol:max` solver worker was assigned to each task,
as recorded in [WORKERS.md](WORKERS.md). Every solver worked offline, inspected
the corresponding question and embedded official answer in the local PDF, and
wrote one Markdown file. Humanize RLCR reviewers also work offline from the same
local official sources.

The explicit official verdict controls each answer pattern. If the printed
graph, a label, a unit, or the official prose appears inconsistent, the solution
retains the official T/F value and adds a clearly labeled discrepancy note
instead of silently changing the key. The prose explanations are original
educational derivations, not copies of the embedded explanations.

The reviewed corpus is locked by `reviewed-solutions.sha256`. The invariant is:
Do not update a hash merely to make validation pass. If an individual solution
changes, first compare that complete file again with its local official question
and embedded answer; only after that direct review may its manifest hash be
regenerated.

## Repository structure

- `solutions/part-a/` and `solutions/part-b/`: the 100 independently authored source solutions.
- `official-answers.tsv`: official A-D patterns derived from the embedded answer sections.
- `task-map.tsv`: canonical source-grounded topic identity for every coordinate.
- `reviewed-solutions.sha256`: integrity manifest for the source-reviewed solution corpus.
- `answers.md`: generated 100-row answer and navigation index.
- `theory-a-solutions.md` and `theory-b-solutions.md`: generated ordered volumes.
- [scripts/build.py](scripts/build.py): deterministic collection builder and freshness check.
- [scripts/run-ibo2024.sh](scripts/run-ibo2024.sh): isolated Codex launcher for the checked-in reproduction prompt.
- [scripts/validate.py](scripts/validate.py): end-to-end offline source, ownership, content, document, and navigation validator.
- [scripts/test_validate.py](scripts/test_validate.py): isolated negative fixtures for the validation contract.
