#!/usr/bin/env python3
"""Summarize frozen artifacts; never equate goal completion with acceptance."""
from collections import Counter
import json
import time
from pathlib import Path
import run_icho_native_goal68 as run
import validate_icho_native_goal68 as validator


def report():
    state=validator.summary();rows=[]
    for task in state['targets']:
        target=task['target'];work=run.BASE/'jobs'/target/'campaign/workspace'
        kp=run.BASE/'controller/validation'/target/'receipt.json'
        rp=run.BASE/'reviews'/target/'status.json'
        kernel=json.loads(kp.read_text()) if kp.exists() else {}
        review=json.loads(rp.read_text()) if rp.exists() else {}
        fresh=False
        if review.get('status')=='reviewed':
            receipt=json.loads((rp.parent/'input-receipt.json').read_text())
            fresh=all((work/name).is_file() and run.infra.sha(work/name)==digest
                      for name,digest in receipt['candidate_hashes'].items())
        kernel_fresh=bool(kernel.get('output_hashes')) and all((work/name).is_file() and
            run.infra.sha(work/name)==digest for name,digest in kernel.get('output_hashes',{}).items())
        accepted=bool(review.get('accepted') and fresh and kernel_fresh and kernel.get('kernel_check')=='passed')
        rows.append(dict(task,kernel=kernel.get('kernel_check','pending'),kernel_hashes_fresh=kernel_fresh,
            semantic=review.get('semantic_status','pending'),proof=review.get('proof_status','pending'),
            review_state=review.get('status','pending'),review_hashes_fresh=fresh,accepted=accepted))
    summary=dict(updated_at=time.time(),model=run.MODEL,reasoning_effort='xhigh',total=68,
        native_goal_counts=state['counts'],kernel_counts=dict(Counter(r['kernel'] for r in rows)),
        semantic_counts=dict(Counter(r['semantic'] for r in rows)),accepted=sum(r['accepted'] for r in rows),
        proof_counts=dict(Counter(r['proof'] for r in rows)),
        review_counts=dict(Counter(r['review_state'] for r in rows)),
        reported_goal_tokens=sum(r.get('tokens_used') or 0 for r in rows),
        official_answer_comparison='not_performed',feedback_to_solver=False,targets=rows)
    run.save(run.BASE/'controller/results-summary.json',summary)
    lines=['# Native /goal + GPT-5.6 Sol — IChO 68-subquestion baseline','',
        '**In progress: not a final score.**' if any(r['review_state']!='reviewed' for r in rows) else '**Post-run audit summary.**','',
        'Fresh answer-blind solving; native persisted goals; maximum 32 solver workers. '
        'Independent post-run semantic/proof reviews do not feed back into the solver. '
        'No historical GPT/Kimi answers or supplementary user model assumptions were supplied.','',
        f"Independently accepted: **{summary['accepted']}/68**. Goal termination and clean Lean compilation are not acceptance by themselves.",'',
        f"Native goal outcomes: `{summary['native_goal_counts']}`. Independent Lean checks: `{summary['kernel_counts']}`.",
        f"Review completion: `{summary['review_counts']}`. Semantic outcomes: `{summary['semantic_counts']}`. Proof outcomes: `{summary['proof_counts']}`.",'',
        'Official-answer comparison: **not performed**. These are formalization/verification outcomes, not official rubric scores.','',
        'Environment amendment: PyMuPDF 1.28.2 was added after startup to support reading the already-supplied original PDF; see `pdf-dependency-amendment.json`. '
        'No scientific input or solver objective was changed.','',
        '| Target | Native goal | Lean | Semantic review | Proof review | Accepted |',
        '|---|---|---|---|---|---|']
    lines += [f"| {r['target']} | {r['status']} | {r['kernel']} | {r['semantic']} | {r['proof']} | {'yes' if r['accepted'] else 'no'} |" for r in rows]
    lines += ['', '## Per-target evidence', '',
        'Each review below is a single independent model assessment, not an infallible judgment. '
        'Conditional and rejected outputs are retained unchanged. No review feedback was sent to solver goals.', '']
    for r in rows:
        target=r['target']
        lines += [f"- {target}: [solver outputs](../jobs/{target}/campaign/workspace/), "
                  f"[kernel receipt](validation/{target}/receipt.json), "
                  f"[review input hashes](../reviews/{target}/input-receipt.json)."]
        if r['review_state']=='reviewed':
            result=json.loads((run.BASE/'reviews'/target/'campaign/review.json').read_text())
            reason=' '.join(str(result.get('reason','')).split())
            lines += [f"  [Independent review](../reviews/{target}/campaign/review.json): {reason}"]
    (run.BASE/'controller/RESULTS.md').write_text('\n'.join(lines)+'\n')
    return {k:v for k,v in summary.items() if k!='targets'}


if __name__=='__main__':print(json.dumps(report(),ensure_ascii=False))
