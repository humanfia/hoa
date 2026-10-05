#!/usr/bin/env python3
"""Controller-side checks only. Never send validation feedback into baseline goals."""
import argparse
import fcntl
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
import time

import run_icho_native_goal68 as run


def summary():
    manifest=json.loads((run.BASE/'manifest.json').read_text())
    rows=[]
    for target in manifest['targets']:
        root=run.BASE/'jobs'/target
        state=json.loads((root/'status.json').read_text()) if (root/'status.json').exists() else {'status':'queued'}
        goal=state.get('goal') or {}
        rows.append(dict(target=target,status=state['status'],thread_id=state.get('thread_id'),
            goal_status=goal.get('status'),tokens_used=goal.get('tokensUsed'),
            time_used_seconds=goal.get('timeUsedSeconds'),updated=state.get('updated')))
    result=dict(at=time.time(),total=len(rows),counts=dict(Counter(r['status'] for r in rows)),targets=rows)
    run.save(run.BASE/'controller/summary.json',result)
    return result


def verify(target):
    manifest=json.loads((run.BASE/'manifest.json').read_text())
    assert target in manifest['targets']
    directory=run.BASE/'controller/validation'/target
    directory.mkdir(parents=True,exist_ok=True)
    with (directory/'validation.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        return _verify(target)


def _verify(target):
    manifest=json.loads((run.BASE/'manifest.json').read_text())
    assert target in manifest['targets']
    root=run.BASE/'jobs'/target
    status=json.loads((root/'status.json').read_text())
    if status['status'] not in ['goal_complete','goal_blocked']:
        return dict(target=target,status='not_terminal')
    work=root/'campaign/workspace'
    rel=Path('IChO2026Problems')/f'problem_{target}.lean'
    output=run.BASE/'controller/validation'/target
    output.mkdir(parents=True,exist_ok=True)
    required=[Path('answer.md'),Path('verification.md'),Path('result.json'),rel]
    missing=[str(p) for p in required if not (work/p).is_file()]
    hashes={str(p.relative_to(work)):run.infra.sha(p) for p in work.rglob('*.lean') if '.lake' not in p.parts}
    for p in required:
        if (work/p).is_file():hashes[str(p)]=run.infra.sha(work/p)
    record=dict(target=target,goal_status=status['status'],checked_at=time.time(),missing=missing,
        output_hashes=hashes,semantic_review='pending',official_answer_comparison='not_performed',
        accepted=False)
    source_ok=all(run.infra.sha(run.BASE/'seed'/p)==h for p,h in manifest['files'].items())
    record['source_hashes_match']=source_ok
    existing=output/'receipt.json'
    if source_ok and not missing and existing.exists():
        previous=json.loads(existing.read_text())
        if (previous.get('kernel_check')=='passed' and previous.get('output_hashes')==hashes
                and previous.get('output_hashes_still_match') is True):
            return previous
    if missing or not source_ok:
        record['kernel_check']='not_run'
        run.save(output/'receipt.json',record);return record
    try:
        result=json.loads((work/'result.json').read_text())
        record['model_result']=result
        record['target_id_matches']=result.get('target_id')==target
    except (ValueError,AttributeError) as exc:
        record['result_error']=str(exc)
    args=run.args_for(root)
    cmd=run.command(args,[str(args.lean_bin/'lake'),'-d',str(work),'env','lean',str(work/rel)])
    with (output/'lean.log').open('w') as log:
        try:
            proc=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=600)
            record['lean_exit_code']=proc.returncode
        except subprocess.TimeoutExpired:
            record['lean_exit_code']=None;record['kernel_check']='timeout'
    text=(output/'lean.log').read_text()
    record['lean_sorry_warning']=bool(re.search(r'declaration uses [\x27`]?sorry',text))
    record['kernel_check']=record.get('kernel_check', 'passed' if record.get('lean_exit_code')==0
        and not record['lean_sorry_warning'] else 'failed')
    # Lexical findings are flags for the independent semantic reviewer, not a proof of soundness.
    record['source_flags']={}
    for name in hashes:
        if not name.endswith('.lean'):continue
        findings=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',(work/name).read_text())
        if findings:record['source_flags'][name]=dict(Counter(findings))
    record['output_hashes_still_match']=all((work/p).is_file() and run.infra.sha(work/p)==h for p,h in hashes.items())
    # A clean compile is intentionally never elevated to semantic/official-answer success here.
    run.save(output/'receipt.json',record)
    return record


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--verify',nargs='*');args=parser.parse_args()
    state=summary();print(json.dumps({'counts':state['counts'],'total':state['total']}))
    if args.verify is not None:
        targets=args.verify or [r['target'] for r in state['targets'] if r['status'] in ['goal_complete','goal_blocked']]
        for target in targets:
            record=verify(target)
            print(json.dumps({k:record.get(k) for k in ['target','status','kernel_check','semantic_review','accepted']},ensure_ascii=False),flush=True)
