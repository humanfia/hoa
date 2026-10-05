# HOA

Humanfia Olympiad Agents: olympiad and benchmark problems solved by agents, with the answers
machine-checked in Lean 4 wherever the subject allows it.

HOA is part of the RSI effort at NVIDIA Research. Every run here is driven by
[Humanize](https://github.com/humanfia/humanize), an open agent loop and flow framework led by
[NVIDIA Research](https://www.nvidia.com/en-us/research),
[UCLA PolyArch](https://polyarch.cs.ucla.edu) and [MIT HAN Lab](https://hanlab.mit.edu). The
project page is [humanfia.ai/projects/hoa](https://humanfia.ai/projects/hoa).

## Results

| Project | Result | Written up |
| --- | --- | --- |
| [PutnamBench](putnambench/) | 672/672 formal statements, joint #1 on the [official leaderboard](https://trishullab.github.io/PutnamBench/leaderboard.html) | [670 of 672 on PutnamBench](https://humanfia.ai/blog/2026-06-26-putnambench) |
| [IMO 2026](imo2026/) | 6/6 problems, every solution verified by Lean 4 | [Six of six at IMO 2026](https://humanfia.ai/blog/2026-07-22-imo-2026) |
| [IOI 2026](ioi2026/) | 6/6 tasks at 100%, judged on Codeforces | |
| [IPhO 2026](ipho2026/) | 30/30 theory points for the natural-language solutions; Lean 4 formalizations of all subparts | [Physics and quantum, formalized end to end](https://humanfia.ai/blog/2026-07-29-physics-and-quantum) |
| [IChO 2026](icho2026/) | 68/68 theory subquestions formalized in Lean 4 | |
| [IBO 2024](ibo2024/) | 100/100 theory tasks; 400/400 statement verdicts match the official key | |
| [QIT + QAlg](lean-qit-qlg/) | 76/76 tasks formalized and proved in Lean 4 | [Physics and quantum, formalized end to end](https://humanfia.ai/blog/2026-07-29-physics-and-quantum) |
| [Chemlib](chemlib/) | A verified Lean 4 library for mathematical chemistry, with the AFPS2017 formalization | |

Each result means exactly what its own README says, and each README states its limits. In
particular:

- The PutnamBench post reports the earlier 670/672 run; the 672/672 figure is the later result
  verified by the PutnamBench team.
- The IPhO 2026 and IBO 2024 scores are grades against the official solutions and answer keys,
  not official jury scores.
- The IChO 2026 figure is formalization completion under each run's declared input scope, not
  official-answer accuracy; two targets are explicitly conditional.
- The QIT and QAlg semantic scores come from automated review, not an independent human audit.

## Layout

Each directory is a self-contained release with its own README, reproduction steps and pinned
toolchain. Run its commands from inside that directory.

| Directory | Contents |
| --- | --- |
| [`putnambench/`](putnambench/) | Solver, pinned statements and toolchain, and scripts to re-run all 672 problems |
| [`imo2026/`](imo2026/) | Lean statements, GPT-5.6 and Kimi-K3 solutions, validators and run harness |
| [`ioi2026/`](ioi2026/) | Official problem packages, submissions, annotated solutions and orchestration |
| [`ipho2026/`](ipho2026/) | Natural-language solutions, grading reports and Lean formalizations |
| [`icho2026/`](icho2026/) | Lean formalization releases, native `/goal` baselines and grading reports |
| [`ibo2024/`](ibo2024/) | Worked theory solutions, grading evidence and validation scripts |
| [`lean-qit-qlg/`](lean-qit-qlg/) | QIT and QAlg datasets with their Lake projects |
| [`chemlib/`](chemlib/) | The Chemlib Lake project and its verification evidence |

Each directory keeps the full Git history of the repository it came from: run
`git log -- imo2026` to see it.

To use Chemlib from another Lake project:

```toml
[[require]]
name = "chemistrylib_v1"
git = { url = "https://github.com/humanfia/hoa-qed.git", subDir = "chemlib/chemlib" }
rev = "main"
```

## Contributing

Pull requests are welcome; open an issue first for anything large. The
[contributing guide](https://github.com/humanfia/.github/blob/main/CONTRIBUTING.md),
[security policy](https://github.com/humanfia/.github/blob/main/SECURITY.md) and
[Code of Conduct](https://github.com/humanfia/.github/blob/main/CODE_OF_CONDUCT.md) are shared
across Humanfia. [CODEOWNERS](.github/CODEOWNERS) lists who maintains each directory.

## Citation

[CITATION.cff](CITATION.cff) describes how to cite this repository.

## License

Code and Lean proofs are licensed under [Apache-2.0](LICENSE). Natural-language solutions,
write-ups and grading reports are licensed under [CC-BY-4.0](LICENSE-CC-BY-4.0). Chemlib,
`lean-qit-qlg` and the IChO 2026 Lake projects keep the Apache-2.0 `LICENSE` files they shipped
with.

Third-party material keeps its owner's terms: official olympiad problems and packages, the
AxiomMath IMO 2026 statements, the PutnamBench statements, the QIT and QAlg benchmark sources,
and vendored tools. [NOTICE](NOTICE) lists each one.
