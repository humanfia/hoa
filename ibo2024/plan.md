# IBO 2024 Theory A/B Worked Solutions

## Goal Description

Produce a complete, accurate, natural-language solution set for all 100 independent tasks in the official English IBO 2024 Theoretical Exams, Parts A and B. Assign exactly one solver worker to each task. Every solver and every Humanize RLCR reviewer must work offline and must be able to inspect both the original task and the embedded official answer in the local official PDF. Use `gpt-5.6-sol` at `max` reasoning effort for workers and RLCR review.

## Acceptance Criteria

- AC-1: All 100 independent tasks are covered once.
  - Positive Tests (expected to PASS):
    - `solutions/part-a/q01.md` through `q50.md` all exist.
    - `solutions/part-b/q01.md` through `q50.md` all exist.
    - The worker ledger records one distinct worker assignment for every task.
  - Negative Tests (expected to FAIL):
    - Any task is missing, duplicated, or assigned to the same worker as another task.

- AC-2: Every answer agrees with the official embedded answer key.
  - Positive Tests (expected to PASS):
    - Each problem file gives an explicit four-letter T/F pattern.
    - Each of A-D is checked against the corresponding official answer section in the local PDF.
  - Negative Tests (expected to FAIL):
    - A truth value differs from the official key without an explicit discrepancy note.
    - A worker relies on an unofficial answer source.

- AC-3: Every task has an understandable worked explanation.
  - Positive Tests (expected to PASS):
    - Every file separately explains A, B, C, and D in natural language.
    - Calculations, causal chains, graph readings, and experimental controls are shown when relevant.
    - False statements identify the precise faulty premise or inference.
  - Negative Tests (expected to FAIL):
    - A file merely repeats `T/F` or paraphrases the official answer without explaining it.
    - Lean, formal-proof syntax, or unexplained jargon replaces prose reasoning.

- AC-4: Solvers and reviewers remain offline.
  - Positive Tests (expected to PASS):
    - Worker prompts and repository instructions prohibit internet access.
    - All cited ground truth comes from `source/IBO2024 Theory A.pdf` and `source/IBO2024 Theory B.pdf`.
  - Negative Tests (expected to FAIL):
    - A worker or reviewer invokes web search, a browser, a network tool, or an external API.

- AC-5: The final collection is easy to use.
  - Positive Tests (expected to PASS):
    - `answers.md` lists all 100 official T/F patterns in order.
    - `theory-a-solutions.md` and `theory-b-solutions.md` assemble the individual files in task order.
    - `README.md` identifies the source, license, structure, and offline methodology.
    - Internal links and task numbering are correct.
  - Negative Tests (expected to FAIL):
    - Consolidated documents omit or reorder tasks.
    - The answer summary disagrees with an individual problem file.

- AC-6: Humanize RLCR review is completed.
  - Positive Tests (expected to PASS):
    - Implementation rounds are committed with required Humanize summaries.
    - The `gpt-5.6-sol:max` reviewer checks completeness, official-key agreement, reasoning quality, and formatting.
    - All review findings are resolved before finalization.
  - Negative Tests (expected to FAIL):
    - The loop is bypassed, manually marked complete, or left with unresolved findings.

## Path Boundaries

### Upper Bound (Maximum Scope)

A polished educational solution set for all 100 theory tasks, including concise restatements where useful, complete reasoning for each statement, answer tables, consolidated documents, provenance, and automated structural checks. It does not include the four practical exams.

### Lower Bound (Minimum Scope)

One accurate natural-language Markdown solution per theory task, all official T/F patterns, an assignment ledger proving one worker per task, two consolidated papers, and a successful RLCR review.

### Allowed Choices

- Can use: the two local official PDFs, local PDF/text/image utilities, Markdown, shell scripts for deterministic validation, and collaboration workers using `gpt-5.6-sol:max`.
- Cannot use: internet access, web search, remote APIs, third-party answer keys, practical-exam material, Lean, or formal theorem-prover output.

## Dependencies and Sequence

### Milestones

1. Establish authoritative local sources and task map.
   - Copy the two official PDFs into ignored `source/` storage.
   - Extract searchable text locally and confirm 50 tasks plus embedded answers per part.
   - Create a 100-row worker ledger.
2. Solve Part A.
   - Launch one distinct offline worker for each of A1-A50 as concurrency becomes available.
   - Validate each returned file against its task and official answer.
3. Solve Part B.
   - Launch one distinct offline worker for each of B1-B50 as concurrency becomes available.
   - Validate each returned file against its task and official answer.
4. Assemble and validate.
   - Generate the answer summary and consolidated Part A/B documents.
   - Run deterministic checks for filenames, sections, T/F patterns, ordering, and cross-document consistency.
5. Complete Humanize review.
   - Commit the implementation round and write its required summary.
   - Address every RLCR finding, re-run checks, and finalize only after the reviewer reports completion.

## Implementation Notes

- The PDFs are licensed CC BY-NC-SA 4.0. The final README and derived solution set must retain attribution and the same noncommercial share-alike license.
- Workers should inspect figures locally with PDF rendering tools when text extraction is insufficient.
- A worker may quote only small labels or values needed for explanation; worked prose should be original.
- The official answer controls the final T/F pattern. Any suspected error in the official material belongs in a clearly labeled note for review.
