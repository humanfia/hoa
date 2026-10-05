"""Current Kimi baseline evidence; no historical scores or solver feedback."""
from collections import Counter
import json
import time

import review_icho_native_kimi_goal68 as reviewer

run = reviewer.kimi.native
BASE = reviewer.kimi.BASE


def read(path):
    return json.loads(path.read_text()) if path.exists() else {}


def hashes_match(work, hashes):
    return bool(hashes) and all((work / name).is_file() and
        run.infra.sha(work / name) == digest for name, digest in hashes.items())


def report():
    manifest = read(BASE / 'manifest.json')
    dispositions = read(BASE / 'controller/final-dispositions.json')
    rows = []
    for target in manifest['targets']:
        job = BASE / 'jobs' / target
        work = job / 'campaign/workspace'
        status = read(job / 'status.json')
        validation = BASE / 'controller/validation' / target
        kernel = read(validation / 'receipt.json')
        review_root = BASE / 'reviews' / target
        review = read(review_root / 'status.json')
        inputs = read(review_root / 'input-receipt.json')
        terminal = status.get('status') in ('goal_complete', 'goal_blocked')
        kernel_current = terminal and kernel.get('checked_at', 0) >= status.get('updated', 0)
        kernel_fresh = kernel_current and hashes_match(work, kernel.get('output_hashes', {}))
        review_fresh = terminal and hashes_match(work, inputs.get('candidate_hashes', {}))
        accepted = bool(review.get('accepted') and review_fresh and kernel_fresh and
                        kernel.get('kernel_check') == 'passed')
        rows.append(dict(target=target, native_status=status.get('status', 'queued'),
            reported_goal_tokens=(status.get('goal') or {}).get('tokensUsed'),
            reported_goal_seconds=(status.get('goal') or {}).get('timeUsedSeconds'),
            kernel=kernel.get('kernel_check', 'pending') if kernel_current else 'pending',
            kernel_hashes_fresh=kernel_fresh,
            alternate_path_receipt=(validation / 'alternate-path-receipt.json').exists(),
            review_status=review.get('status', 'pending'), review_hashes_fresh=review_fresh,
            semantic=review.get('semantic_status', 'pending'),
            proof=review.get('proof_status', 'pending'), accepted=accepted,
            final_disposition=dispositions.get(target)))
    jobs_terminal = bool(rows) and all(r['native_status'] in ('goal_complete', 'goal_blocked')
                                      and r['review_status'] in ('reviewed', 'review_error') for r in rows)
    summary = dict(updated_at=time.time(), model=reviewer.kimi.MODEL,
        execution_status='finished_with_review_errors' if jobs_terminal and any(
            r['review_status'] == 'review_error' for r in rows) else 'finished' if jobs_terminal else 'in_progress',
        total=len(rows), maximum_solver_concurrency=32, fresh_answer_blind=True,
        native_counts=dict(Counter(r['native_status'] for r in rows)),
        kernel_counts=dict(Counter(r['kernel'] for r in rows)),
        fresh_kernel_passed=sum(r['kernel'] == 'passed' and r['kernel_hashes_fresh'] for r in rows),
        review_counts=dict(Counter(r['review_status'] for r in rows)),
        semantic_counts=dict(Counter(r['semantic'] for r in rows)),
        proof_counts=dict(Counter(r['proof'] for r in rows)),
        accepted=sum(r['accepted'] for r in rows),
        final_disposition_counts=dict(Counter(r['final_disposition']['outcome']
            for r in rows if r['final_disposition'])),
        reported_goal_tokens=sum(r['reported_goal_tokens'] or 0 for r in rows),
        official_answer_comparison='not_performed', feedback_to_solver=False, targets=rows)
    run.save(BASE / 'controller/results-summary.json', summary)
    lines = ['# Kimi-K3 + native /goal — fresh answer-blind IChO 68', '',
        f"Execution status: `{summary['execution_status']}`; this is not an official-answer score.", '',
        f"Model: `{summary['model']}`. Maximum 32 solver jobs. Independent reviews use fresh Kimi contexts, without feedback to solvers.", '',
        f"Native goal outcomes: `{summary['native_counts']}`.",
        f"Fresh canonical-path Lean passes: {summary['fresh_kernel_passed']}/{len(rows)}.",
        f"Review states: `{summary['review_counts']}`. Accepted with fresh evidence: {summary['accepted']}/{len(rows)}.", '',
        'Goal completion and Lean compilation alone do not establish chemistry correctness. '
        'Pending reviews are not failures. Conditional findings will remain conditional. '
        'No official-answer comparison has been performed for this run.', '',
        'Review errors mean no valid structured verdict was obtained, not a scientific failure or acceptance. '
        'A semantic/proof passed pair can still fail the aggregate gate (for example, a nonempty unsupported-assumptions field). '
        'Original reviewer fields are preserved, including inconsistencies.', '',
        'Original problem PDF and blank student answer sheets were supplied before launch. '
        'PyMuPDF was installed before this Kimi run. Historical answers and supplementary user model assumptions were not supplied.', '',
        'Transport-only recoveries preserve existing threads and candidates: see [transport audit](TRANSPORT.md). '
        'Reviewer interface preflight and host JSON validation are recorded in [interface amendment](../reviews/interface-amendment.json). '
        'These amendments do not change scientific inputs or acceptance criteria.', '',
        'An alternate-path receipt is a filename exception, not a canonical artifact pass. '
        'Reported goal tokens are not a provider billing total and exclude separate reviewer/preflight usage.', '',
        '| Target | Goal | Canonical Lean | Fresh hashes | Semantic | Proof | Accepted |',
        '|---|---|---|---|---|---|---|']
    if dispositions:
        index = lines.index('| Target | Goal | Canonical Lean | Fresh hashes | Semantic | Proof | Accepted |')
        notes = ['## Final dispositions', '']
        for target, disposition in dispositions.items():
            notes.append(f"- {target}: **{disposition['outcome']}**; rerun: {disposition['rerun']}. {disposition['reason']}")
        notes += ['', 'Original native statuses and reviewer verdicts are preserved; these terminal failures are not pending solver work.', '']
        lines[index:index] = notes
    for r in rows:
        target = r['target']
        lean = r['kernel'] + (' (alternate-path receipt)' if r['alternate_path_receipt'] else '')
        lines.append(f"| [{target}](../jobs/{target}/campaign/workspace/) | {r['native_status']} | {lean} | {r['kernel_hashes_fresh']} | {r['semantic']} | {r['proof']} | {r['accepted']} |")
    (BASE / 'controller/RESULTS.md').write_text('\n'.join(lines) + '\n')
    return {key: value for key, value in summary.items() if key != 'targets'}


if __name__ == '__main__':
    print(json.dumps(report(), ensure_ascii=False))
