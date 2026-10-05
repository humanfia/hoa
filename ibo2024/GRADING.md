# Answer-Key Grading Report

Graded on 2026-08-20 (UTC).

## Scope and authority

This report grades the declared answers in all 100 Theory A/B solution files against the answer sections embedded in the two local official English examination PDFs. Practical examinations are excluded.

The grading pass extracted the official A-D true/false pattern for every task directly from the local PDFs, compared it with `official-answers.tsv`, and then compared both with the answer declared in the corresponding solution file. No external answer source or network lookup was used.

## Results

| Part | Matching task patterns | Matching statement verdicts | Agreement |
|---|---:|---:|---:|
| Theory A | 50 / 50 | 200 / 200 | 100% |
| Theory B | 50 / 50 | 200 / 200 | 100% |
| **Overall** | **100 / 100** | **400 / 400** | **100%** |

The extraction and format error count was **0**.

## Interpretation

The collection receives an **answer-key agreement grade of 100%**: every declared four-statement pattern matches the corresponding embedded official answer.

This is not an official Olympiad points calculation. It measures exact agreement with the embedded true/false key. The natural-language reasoning was reviewed separately against the local task statements and is protected by the reviewed solution manifest.

## Verification

The following offline checks passed after grading:

```bash
python scripts/build.py --check
python scripts/validate.py
```

The complete adversarial validation suite is available through:

```bash
python scripts/test_validate.py
```
