"""Host-only recovery of an unambiguous review payload; no model/solver feedback."""
import argparse
import json
import time

import review_icho_native_kimi_goal68 as kimi_review


def recover(target):
    review = kimi_review.review
    root = review.REVIEW_ROOT / target
    state = json.loads((root / 'status.json').read_text())
    error=state.get('error','')
    format_error=(error=='Expected exactly one review JSON payload' or
                  error.startswith('Expecting property name enclosed in double quotes:') or
                  error.startswith('Expecting value:'))
    if state.get('status') != 'review_error' or not format_error:
        raise ValueError('Only the exact audited format error is recoverable')
    raw_path = root / 'campaign/review.json'
    raw_hash = review.run.infra.sha(raw_path)
    result = kimi_review.load_review(raw_path.read_text())
    files = json.loads((root / 'input-receipt.json').read_text())['candidate_hashes']
    work = root / 'campaign/workspace'
    source = review.run.BASE / 'jobs' / target / 'campaign/workspace'
    fresh = all((source / p).is_file() and review.run.infra.sha(source / p) == h
                and review.run.infra.sha(work / p) == h for p, h in files.items())
    kernel = review.validation.verify(target)
    expected = [x['id'] for x in json.loads((work / 'TASK.json').read_text())['requested_outputs']]
    accepted = review.assess(target, result, expected, kernel, fresh)
    assert review.run.infra.sha(raw_path) == raw_hash, 'Raw review changed during recovery'
    review.run.save(root / 'format-recovery.json', dict(
        at=time.time(), previous_status=state, original_review_sha256=raw_hash,
        recovered_payload=result, model_rerun=False, verdict_changed=False,
        parser_policy='single payload; optional JSON trailing-comma removal; strict schema',
        feedback_to_solver=False))
    final = dict(status='reviewed', target=target, accepted=accepted,
                 semantic_status=result['semantic_status'], proof_status=result['proof_status'],
                 input_hashes_fresh=fresh, kernel_check=kernel.get('kernel_check'),
                 format_recovered=True, finished=time.time())
    review.run.save(root / 'status.json', final)
    return final


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('target')
    args = parser.parse_args()
    if args.target not in json.loads((kimi_review.kimi.BASE / 'manifest.json').read_text())['targets']:
        parser.error('Target is not in this experiment')
    print(json.dumps(recover(args.target)))
