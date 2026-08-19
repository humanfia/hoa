# IBO 2024 Theory A/B Worked Solutions

This repository contains natural-language worked solutions for all 100 independent tasks in the official English International Biology Olympiad (IBO) 2024 Theoretical Exam: 50 tasks from Part A and 50 from Part B. It intentionally excludes every practical exam.

## Read the collection

- [Official answer summary](answers.md)
- [Theory Part A consolidated solutions](theory-a-solutions.md)
- [Theory Part B consolidated solutions](theory-b-solutions.md)
- [Part A individual solutions](solutions/part-a/)
- [Part B individual solutions](solutions/part-b/)
- [One-worker assignment ledger](WORKERS.md)

## Source and license

The questions, figures, and embedded official solutions come from the International Biology Olympiad's official English IBO 2024 Theory A and Theory B papers. Those examination sources are the authority for task identity and T/F verdicts.

The source examination material and this derived solution set are shared under **CC BY-NC-SA 4.0**. Reuse must provide attribution, must be noncommercial, and must distribute adaptations under the same share-alike license.

The official PDFs are kept locally and ignored by Git. Place them at these exact paths before validation:

- `source/IBO2024 Theory A.pdf`
- `source/IBO2024 Theory B.pdf`

The local `pdftotext -layout` extracts are `source/part-a.txt` and `source/part-b.txt`; validation regenerates text from each PDF and requires the stored extract to agree byte-for-byte.

## Offline methodology and ownership

Exactly one distinct `gpt-5.6-sol:max` solver worker was assigned to each task, as recorded in [WORKERS.md](WORKERS.md). Every solver worked offline, inspected the corresponding question and embedded official answer in the local PDF, and wrote one Markdown file. Humanize RLCR reviewers also work offline from the same local official sources.

The explicit official verdict controls each answer pattern. If the printed graph, a label, a unit, or the official prose appears inconsistent, the solution retains the official T/F value and adds a clearly labeled discrepancy note instead of silently changing the key. The prose explanations are original educational derivations, not copies of the embedded explanations.

The reviewed corpus is locked by `reviewed-solutions.sha256`. Do not update a hash merely to make validation pass. If an individual solution changes, first compare that complete file again with its local official question and embedded answer; only after that direct review may its manifest hash be regenerated.

## Repository structure

- `solutions/part-a/` and `solutions/part-b/`: the 100 independently authored source solutions.
- `official-answers.tsv`: official A-D patterns derived from the embedded answer sections.
- `task-map.tsv`: canonical source-grounded topic identity for every coordinate.
- `reviewed-solutions.sha256`: integrity manifest for the source-reviewed solution corpus.
- `answers.md`: generated 100-row answer and navigation index.
- `theory-a-solutions.md` and `theory-b-solutions.md`: generated ordered volumes.
- [scripts/build.py](scripts/build.py): deterministic collection builder and freshness check.
- [scripts/validate.py](scripts/validate.py): end-to-end offline source, ownership, content, document, and navigation validator.
- [scripts/test_validate.py](scripts/test_validate.py): isolated negative fixtures for the validation contract.

## Build and validate

Generate the three derived collection documents:

```bash
python scripts/build.py
```

Check that committed generated documents are byte-for-byte current without writing:

```bash
python scripts/build.py --check
```

Run the complete offline gate and its adversarial fixtures:

```bash
python scripts/validate.py
python scripts/test_validate.py
python -m py_compile scripts/build.py scripts/validate.py scripts/test_validate.py
git diff --check
```

The validator invokes only local tools and files. It does not browse, query a network service, or consult a third-party answer key.
