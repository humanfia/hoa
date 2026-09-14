# Kimi-K3 formalizations: remaining 36 targets, 68/68 combined

**36/36 additional targets passed formalization review, proof review and Lean
verification.** Together with the earlier
[32-target answer-blind experiment](../kimi-k3-answer-blind/), this covers all
**68 numbered theory subquestions (32 + 36)**. The earlier 32 were not rerun.

The natural-language answers, Lean formalizations, proofs and reviews in this
36-target release were all produced with **Kimi-K3** through the existing
Humanize/Archon harness, initially at concurrency 32 with scoped single-target
recoveries.

| Measure | Result |
|---|---:|
| Additional numbered subquestions in this directory | 36 |
| Combined Kimi theory coverage with the earlier 32 | **68/68** |
| Formalization review passed | 36/36 |
| Proof review solved | 36/36 |
| Source-campaign independent Lean checks | 36/36 |
| Explicitly conditional targets | 3 |
| Targets with authorized Kimi-answer corrections | 2 |
| Official-answer accuracy of this release | Not scored |

This campaign formalizes supplied Kimi natural-language answers, **not fresh
answer-blind solving**. Combined **68/68** is formalization completion under the
disclosed scopes below, not official-answer accuracy. The historical 417.5/437
natural-language score must not be presented as the score of these modified and
formalized artifacts.

## Provenance and declared scopes

- **T2-A6:** M201 is sufficient continuous bromide feed; M202/M203 authorize
  concrete initial-state/dose/time conditions for the Ce and Ag perturbations.
  The accepted proof derives the threshold consequences under those conditions.
- **T7-A6:** M701/M702 are finite contest-model assumptions about an activity
  cutoff and transfer of calibrated pKa/yield comparisons.
- **T8-A8:** M001 is the absence of a drawn dark-condition product stack;
  M002 is the local LED-energy/H₂-fraction ordering model.
- **T1-A1 and T8-A4:** narrowly authorized corrections were made to the supplied
  Kimi answers/representations. These two results are corrected Kimi drafts, not
  unchanged original Kimi answers. Original Q1–Q9 drafts are retained in
  `kimi-original-answers/`; exact correction scopes are in `assumptions/`.
- **T8-A3:** missing blank student input was restored. The final artifact passed
  both formalization and proof review using a scoped, checked qpy-planarity
  literature bridge; it is no longer counted solely by the earlier manual acceptance.
- **T6-A6:** the combined result explicitly uses the independently verified
  same-run T6-A5 theorem. The exact imported copy is `IChO2026Chem/VerifiedA5.lean`.

The remaining **31 targets preserve the Kimi answers** without the three
explicit conditional-model supplements or the two correction exceptions above.
Acceptance certifies the experiment's reviewed formalization under its disclosed
scope; it does not establish 100% official-answer accuracy or empirical truth.

## Files

- `IChO2026Problems/`: 36 original accepted target files plus a generated umbrella.
- `IChO2026Chem/`, `IChO2026Run/`: supporting Lean modules and the verified A5 copy.
- `answers/`: all 36 structured answer submissions.
- `reports/`: available original task reports; not all historical tasks retained
  a standalone report. Every target has its full review records below.
- `verification/targets.json`: target IDs, hashes, acceptance and scope flags.
- `verification/reviews/`: exact formalization/proof review records.
- `verification/kernel/`: all 36 independent source-campaign Lean logs.
- `verification/accepted36-receipt.json`: final all-target acceptance/build receipt.
- `verification/release-build.json`: publication-copy build outcome.
- `assumptions/`: target-scoped model and correction authorization receipts.
- `CHECKSUMS.sha256`: public artifact checksums, excluding local build caches.

No model homes, authentication files, credentials, raw conversation logs or
dependency caches are included. The source experiments were not edited.

## Reproduce

```bash
cd kimi-k3-nl-gpt36-formalization
sha256sum -c CHECKSUMS.sha256
lake exe cache get
lake build
lake env lean IChO2026Problems/problem_icho_2026_t6_a5.lean
```

T6-A6 imports `VerifiedA5`, an exact byte-identical copy of the accepted T6-A5
source. The umbrella therefore does not also import the original A5 module,
which would redeclare the same theorem names. The final command independently
checks the original A5 file. This is still **36 distinct target IDs**, not an
extra target for the copied dependency. Library helpers are not subquestions.

Historical reports retain original absolute paths for provenance. Use the
relative release paths above to reproduce compilation locally.
