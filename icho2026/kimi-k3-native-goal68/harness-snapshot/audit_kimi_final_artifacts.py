"""Read-only candidate/review audit, writing only a host evidence receipt."""
import json
import time
import report_icho_native_kimi_goal68 as report


def audit():
    report.report()
    base = report.BASE
    run = report.run
    reviewer = report.reviewer
    summary = report.read(base / 'controller/results-summary.json')
    rows = []
    for row in summary['targets']:
        target = row['target']
        work = base / 'jobs' / target / 'campaign/workspace'
        root = base / 'reviews' / target
        hashes = report.read(root / 'input-receipt.json')['candidate_hashes']
        copy_fresh = report.hashes_match(root / 'campaign/workspace', hashes)
        source_fresh = report.hashes_match(work, hashes)
        kernel = report.read(base / 'controller/validation' / target / 'receipt.json')
        state = report.read(root / 'status.json')
        payload_ok = None
        if state['status'] == 'reviewed':
            payload = reviewer.load_review((root / 'campaign/review.json').read_text())
            expected = [x['id'] for x in report.read(work / 'TASK.json')['requested_outputs']]
            accepted = bool(reviewer.review.assess(target, payload, expected, kernel,
                                                   copy_fresh and source_fresh))
            payload_ok = (accepted == row['accepted'] and
                          payload['semantic_status'] == row['semantic'] and
                          payload['proof_status'] == row['proof'])
        alternate = report.read(base / 'controller/validation' / target / 'alternate-path-receipt.json')
        alternate_ok = None
        if alternate:
            alternate_ok = (alternate.get('exit_code', alternate.get('lean_exit_code')) == 0 and
                            run.infra.sha(work / alternate['actual_path']) == alternate['source_sha256'])
        rows.append(dict(target=target, original_hashes_fresh=source_fresh,
                         reviewer_copy_hashes_fresh=copy_fresh, verdict_reproduced=payload_ok,
                         alternate_source_fresh=alternate_ok,
                         review_status=state['status']))
    result = dict(at=time.time(), targets=len(rows),
                  all_original_and_copy_hashes_fresh=all(r['original_hashes_fresh'] and r['reviewer_copy_hashes_fresh'] for r in rows),
                  all_structured_verdicts_reproduced=all(r['verdict_reproduced'] is not False for r in rows),
                  all_alternate_receipts_fresh=all(r['alternate_source_fresh'] is not False for r in rows),
                  review_errors=[r['target'] for r in rows if r['review_status'] == 'review_error'],
                  scope='All 68 candidate and review-copy receipt hashes; strict review schema and aggregate gate replay; alternate Lean source hashes. Not official-answer grading.',
                  rows=rows)
    run.save(base / 'controller/final-artifact-audit.json', result)
    return {k:v for k,v in result.items() if k != 'rows'}


if __name__ == '__main__':
    print(json.dumps(audit()))
