# Humanize impact report: first worker round versus final result

## Executive result

This report compares the **first answer produced by each of the nine Kimi-K3
workers in round 0** with the final consolidated answer after the Humanize and
focused image-aware review process. It does not use the earlier GPT experiment
as a baseline.

Against the official English IChO 2026 marking schemes, the first worker
round scores **233.0/437 raw points (53.32%)**. The final result scores
**418.5/437 raw points (95.77%)**.

After applying the official problem weights, the score changes from
**37.667/60 (62.78%)** to **58.341/60 (97.24%)**. The Humanize workflow
therefore produces a net change of:

- **+185.5 raw points**;
- **+42.45 raw percentage points**;
- **+20.674 weighted points out of 60**; and
- **+34.46 percentage points on the weighted theory scale**.

No problem has a lower final score than its first-round score.

## Score comparison

The weighted score for a problem is calculated as

`official problem weight × raw score / raw maximum`.

| Problem | Official weight | First-round raw | First-round weighted | Final raw | Final weighted | Raw change | Weighted change |
|---|---:|---:|---:|---:|---:|---:|---:|
| Q1 | 7 | 23/25 | 6.440/7 | 25/25 | 7.000/7 | +2.0 | +0.560 |
| Q2 | 6 | 35/35 | 6.000/6 | 35/35 | 6.000/6 | 0.0 | 0.000 |
| Q3 | 7 | 17/63 | 1.889/7 | 59/63 | 6.556/7 | +42.0 | +4.667 |
| Q4 | 6 | 22/22 | 6.000/6 | 22/22 | 6.000/6 | 0.0 | 0.000 |
| Q5 | 6 | 15/18 | 5.000/6 | 18/18 | 6.000/6 | +3.0 | +1.000 |
| Q6 | 7 | 12/83 | 1.012/7 | 77/83 | 6.494/7 | +65.0 | +5.482 |
| Q7 | 7 | 29.5/54 | 3.824/7 | 54/54 | 7.000/7 | +24.5 | +3.176 |
| Q8 | 7 | 61.5/84 | 5.125/7 | 75.5/84 | 6.292/7 | +14.0 | +1.167 |
| Q9 | 7 | 18/53 | 2.377/7 | 53/53 | 7.000/7 | +35.0 | +4.623 |
| **Total** | **60** | **233.0/437** | **37.667/60** | **418.5/437** | **58.341/60** | **+185.5** | **+20.674** |

The largest raw gains are Q6 (+65), Q3 (+42), Q9 (+35), and Q7 (+24.5).
Together, these four diagram- and structure-heavy problems account for
**166.5 of the 185.5 recovered raw points (89.8%)**.

## Definition of the two endpoints

### First worker round

The baseline is the first complete implementation response emitted by each
isolated worker, before that response received its first Humanize review:

- Q1-Q8:
  `.worktrees/qXX/runtime/round-0-attempt-1-implementation-output.md`
- Q9:
  `.worktrees/q09/runtime/round-0-attempt-1-raw-implementation-output.md`

These responses were produced independently, one problem per worker, through
`/root/.codex-magikcloud` using `Kimi-K3` with reasoning effort `max` and the
unchanged MagikCloud URL `https://api.magikcloud.cn/v1`.

### Final result

The endpoint is `solutions/Q1.md` through `solutions/Q9.md` on branch
`kimi-k3-max-results`, assessed at commit
`f6360bafbaf7f9d95034d8d75171c3415e013f23`.

The endpoint includes the ordinary Humanize text-review rounds and the later
focused gate requiring both an image-aware audit and a Humanize audit. The
focused gate used the official problem pages as evidence. A preserved prior
solution was available only as a discrepancy detector, not as the grading
authority or the baseline for this report.

## Problem-by-problem analysis

### Q1: 23/25 to 25/25

The first response correctly found Y and all of parts 1.2-1.6, but identified
X as alpha-terpineol. The official X is compound 6, linalool. The final audit
corrected X while retaining the valid cineole mechanism and the remaining
answers. Gain: **2 raw, 0.560 weighted**.

### Q2: 35/35 to 35/35

The first response already matched all seven official answers. Humanize fixed
minor dimensional notation and presentation issues, but these did not change
the official score. Gain: **0**.

### Q3: 17/63 to 59/63

First-round subpart score:

| Part | First | Final | Main change |
|---|---:|---:|---|
| 3.1 | 2/2 | 2/2 | Unchanged and correct |
| 3.2 | 3/3 | 3/3 | Unchanged and correct |
| 3.3 | 0/23 | 19/23 | Reconstructed the printed monomer-label topology table |
| 3.4 | 6/12 | 12/12 | Corrected the COF-3/4 precursor pair and made all repeat units explicit |
| 3.5 | 0/6 | 6/6 | Replaced the invented dia fragment with the fluorinated, aldehyde-bearing macrocycle repeat |
| 3.6 | 4/12 | 12/12 | Corrected AB and AB-prime from -81.4/-106.0 to -49.8/-55.6 kJ mol-1 |
| 3.7 | 2/5 | 5/5 | Corrected uptake from 0.77 to 1.00 uranyl ion per pore |

The final answer still loses four points in 3.3: both cells under Tetragonal 2
should be `XXX`, but the final table inserts `A4+B1` and `C3+D3`.
Gain: **42 raw, 4.667 weighted**.

### Q4: 22/22 to 22/22

The first response wrote Rb-95 and Cs-138 rather than the official Rb-93 and
Cs-140. However, the official 4.3 rubric awards the mass-number credit when
the submitted masses have the correct sum, 233; it separately awards the
correct Rb/Cs identities and a balanced fission equation. The first response
therefore retains full rubric credit. The focused audit improved factual
precision without increasing the score. Gain: **0**.

### Q5: 15/18 to 18/18

First-round subpart score:

| Part | First | Final | Main change |
|---|---:|---:|---|
| 5.1 | 0/1 | 1/1 | Corrected `n` from even to odd, specifically `n=1` |
| 5.2 | 5/6 | 6/6 | Replaced the phosphate-phosphate tautomer with the official phosphate-central-alcohol proton relay |
| 5.3 | 4/4 | 4/4 | Unchanged and correct |
| 5.4 | 2/2 | 2/2 | Unchanged and correct |
| 5.5 | 2/2 | 2/2 | Unchanged and correct |
| 5.6 | 2/3 | 3/3 | Corrected PL3 to the official monoethyl-phosphate structure and completed stereochemistry |

Gain: **3 raw, 1.000 weighted**.

### Q6: 12/83 to 77/83

First-round subpart score:

| Part | First | Final | Main change |
|---|---:|---:|---|
| 6.1 | 8/10 | 10/10 | Corrected triplet C13 from two aromatic systems to zero |
| 6.2 | 0/11 | 5/11 | Reconstructed explicit chlorine, bond, and radical patterns for B-D |
| 6.3 | 2/2 | 2/2 | Unchanged and correct |
| 6.4 | 0/12 | 12/12 | Corrected all four catenane mass-spectral assignments |
| 6.5 | 0/24 | 24/24 | Replaced the unrelated CPP route with the official F-L sequence |
| 6.6 | 0/20 | 20/20 | Replaced the misread nanoring labels with the official M-R porphyrin precursors |
| 6.7 | 2/4 | 4/4 | Corrected the global count from 34 to 82 pi electrons |

The final 6.2 answer receives C = 3/3, but B and D receive 1/4 each under the
official partial-credit rules. B does not reproduce the official radical and
chlorine placement; D gives a monocyclic single-radical graph instead of the
official open/fused structure with three radical centres. Thus Q6 is
**77/83**, not 80/83. Gain: **65 raw, 5.482 weighted**.

### Q7: 29.5/54 to 54/54

First-round subpart score:

| Part | First | Final | Main change |
|---|---:|---:|---|
| 7.1 | 0.5/3 | 3/3 | Corrected M1/M2 contents and the `x>y` relation |
| 7.2 | 1/8 | 8/8 | Included air oxidation and corrected methane demand from 240,000 to 280,000 t |
| 7.3 | 15/15 | 15/15 | Unchanged and correct |
| 7.4 | 0/3 | 3/3 | Replaced potassium carbonate with the given MDEA bicarbonate reaction |
| 7.5 | 0/6 | 6/6 | Corrected the 5:2 N2/complex ratio and the dinuclear Mo-PNP structure |
| 7.6 | 0/6 | 6/6 | Replaced the absent ranking with `B>C>D>A` |
| 7.7 | 13/13 | 13/13 | Unchanged and correct |

Gain: **24.5 raw, 3.176 weighted**.

### Q8: 61.5/84 to 75.5/84

First-round subpart score:

| Part | First | Final | Main change |
|---|---:|---:|---|
| 8.1 | 2/2 | 2/2 | Unchanged and correct |
| 8.2 | 16/16 | 16/16 | Unchanged and correct |
| 8.3 | 2/2 | 2/2 | Unchanged and correct |
| 8.4 | 16.5/29 | 24.5/29 | Corrected VE semantics, ligand steps, species 12-15, and most bookkeeping |
| 8.5 | 3/5 | 5/5 | Corrected the catalyst/support area basis to about 2.4 molecules nm-2 |
| 8.6 | 6/10 | 6/10 | The 10 mg loading-basis error remained |
| 8.7 | 2/2 | 2/2 | Correct answer retained; explanation repaired |
| 8.8 | 0/4 | 4/4 | Corrected mapping to `a=N, b=B, c=G, d=R` |
| 8.9 | 12/12 | 12/12 | Unchanged and correct |
| 8.10 | 2/2 | 2/2 | Unchanged and correct |

The final answer still misidentifies official intermediate 11 and retains the
8.6 loading error, producing the remaining 8.5-point deduction. Gain:
**14 raw, 1.167 weighted**.

### Q9: 18/53 to 53/53

First-round subpart score:

| Part | First | Final | Main change |
|---|---:|---:|---|
| 9.1 | 2/2 | 2/2 | Unchanged; ordinary molar-mass rounding accepted |
| 9.2 | 0/6 | 6/6 | Replaced protected beta-CD with the official inverted 3,6-anhydro K |
| 9.3 | 4/8 | 8/8 | Corrected stereocentres from 35 to 21 |
| 9.4 | 0/3 | 3/3 | Replaced the altro-diol assignment with the TBS-protected epoxide Y |
| 9.5 | 2/2 | 2/2 | Unchanged and correct |
| 9.6 | 4/4 | 4/4 | Correct number retained |
| 9.7 | 0/6 | 6/6 | Corrected sodium-adduct peaks from 1229/1661 to 1299/1731 |
| 9.8 | 2/18 | 18/18 | Reconstructed the complete O-S primary-rim sequence and shared bridge |
| 9.9 | 4/4 | 4/4 | Unchanged and correct |

Gain: **35 raw, 4.623 weighted**.

## What the score change says about Humanize

The result supports the value of iterative review, but the gain should be
attributed to the **complete review system**, not to the original text-only
reviewer in isolation.

The text-only Humanize loops often fixed algebra, units, or internal wording,
but they also issued false `COMPLETE` judgments on diagram-heavy errors. The
large gains in Q3, Q6, Q7, Q8, and Q9 occurred after the workflow added the
focused image-aware discrepancy gate and further corrective rounds. This is
consistent with the distribution of gains: nearly 90% of recovered raw points
came from the four most structure- and diagram-dependent problems.

Humanize also increased answer length. Across Q1-Q9, the first outputs contain
approximately 16,815 whitespace-separated words, while the final solutions
contain approximately 19,701 words, an increase of about **17.2%**. The score
gain is therefore a correctness and explicitness gain, not a concision gain.

## Grading conventions and limitations

- The official English solution PDFs under
  `/root/zhengyang-workspace/icho-2026-answers/theoretical/` are the grading
  authority.
- The same interpretation standard is used at both endpoints: a textual
  structure receives drawing credit only when it unambiguously specifies the
  official connectivity, substituents, and required stereochemistry.
- Official negative-marking and explicit partial-credit rules are applied.
  A subpart is not allowed to become negative unless the official rubric says
  otherwise.
- Q9.1 receives full credit at both endpoints because 1134.98 versus 1135.01
  g mol-1 is solely the result of using 18.02 versus 18.016 g mol-1 for water.
- Some drawing scores necessarily involve evaluator judgment. The report
  records the adopted interpretation in every affected problem so that the
  result can be reproduced or adjusted under a stricter drawing policy.

## Reproducibility

Raw totals:

`23 + 35 + 17 + 22 + 15 + 12 + 29.5 + 61.5 + 18 = 233.0`

`25 + 35 + 59 + 22 + 18 + 77 + 54 + 75.5 + 53 = 418.5`

Weighted totals:

`7(23/25) + 6(35/35) + 7(17/63) + 6(22/22) + 6(15/18)`

`+ 7(12/83) + 7(29.5/54) + 7(61.5/84) + 7(18/53)`

`= 37.667/60`

and

`7(25/25) + 6(35/35) + 7(59/63) + 6(22/22) + 6(18/18)`

`+ 7(77/83) + 7(54/54) + 7(75.5/84) + 7(53/53)`

`= 58.341/60`.
