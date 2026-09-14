#!/usr/bin/env python3
"""Read-only run evidence audit; writes only a controller receipt, never candidates."""
from collections import Counter
import json
from pathlib import Path
import re
import time
import run_icho_native_goal68 as run


def solver_interval_audit(base, targets, observed_at):
    """Reconstruct recorded attempts, including pre-recovery snapshots.

    These are controller timestamp intervals, not a process-level trace.
    Running attempts end at observation time; equal-time ends precede starts.
    """
    allowed = set(targets)
    attempts = {}
    skipped = []
    threads = {}
    paths = sorted((base/'controller').glob('transport-recovery-*/icho_2026_*.json'))
    paths += sorted((base/'jobs').glob('*/status.json'))
    for path in paths:
        target = path.parent.name if path.name == 'status.json' else path.stem
        if target not in allowed:
            continue
        state = json.loads(path.read_text())
        start = state.get('started')
        end = observed_at if state.get('status') == 'running' else state.get('updated')
        if start is None or end is None or end < start:
            skipped.append(str(path.relative_to(base)))
            continue
        attempts[(target, start)] = (start, end)
        if state.get('thread_id'):
            threads.setdefault(target, set()).add(state['thread_id'])
    events = []
    for start, end in attempts.values():
        if end > start:
            events.extend([(start, 1), (end, -1)])
    active = peak = 0
    for _, delta in sorted(events):
        active += delta
        peak = max(peak, active)
    return dict(
        observed_peak_solver_intervals=peak,
        recorded_solver_attempts=len(attempts),
        interval_records_skipped=skipped,
        recovery_threads_preserved=(set(threads) == allowed and
                                    all(len(ids) == 1 for ids in threads.values())),
        interval_scope='Current per-job status timestamps plus saved transport-recovery snapshots; running intervals end at observation time. Not a process-level trace.')


def audit():
    manifest=json.loads((run.BASE/'manifest.json').read_text())
    source_ok=all(run.infra.sha(run.BASE/'seed'/p)==h for p,h in manifest['files'].items())
    rows=[]; searches=[]; flags=[]
    pattern=re.compile(r'icho|olympiad|humanfia|science-mango|marking.scheme',re.I)
    for target in manifest['targets']:
        root=run.BASE/'jobs'/target
        state=json.loads((root/'status.json').read_text())
        thread=state['thread_id'];goals=[];web=0;malformed=0
        for line in (root/'events.jsonl').open():
            try:event=json.loads(line)
            except ValueError:malformed+=1;continue
            params=event.get('params',{})
            if event.get('method')=='thread/goal/updated' and params.get('threadId')==thread:
                goals.append(params['goal'])
            if event.get('method')=='item/completed' and params.get('threadId')==thread:
                item=params.get('item',{})
                if item.get('type')=='webSearch':
                    web+=1
                    record=dict(target=target,query=item.get('query'),action=item.get('action'),
                        results=[{k:r.get(k) for k in ('title','url','domain')} for r in item.get('results',[])])
                    searches.append(record)
                    if pattern.search(json.dumps({k:v for k,v in record.items() if k!='target'})):flags.append(record)
        work=root/'campaign/workspace'
        task=json.loads((work/'TASK.json').read_text())
        terminal=goals[-1] if goals else {}
        rows.append(dict(target=target,thread_id=thread,status=state['status'],
            task_id_matches=task.get('id')==target,
            goal_events=len(goals),native_terminal=terminal.get('status'),
            objective_matches=terminal.get('objective')==run.objective(target),
            usage_matches=terminal.get('tokensUsed')==state['goal'].get('tokensUsed'),
            malformed_event_lines=malformed,web_searches=web))
    observed_at=time.time()
    interval_audit=solver_interval_audit(run.BASE,manifest['targets'],observed_at)
    result=dict(at=observed_at,targets=len(rows),source_hashes_match=source_ok,
        terminal_counts=dict(Counter(r['native_terminal'] for r in rows)),
        distinct_threads=len({r['thread_id'] for r in rows}),**interval_audit,
        model=manifest['model'],concurrency=manifest['concurrency'],
        all_objectives_match=all(r['objective_matches'] for r in rows),
        all_task_ids_match=all(r['task_id_matches'] for r in rows),
        all_usage_matches=all(r['usage_matches'] for r in rows),
        malformed_lines=sum(r['malformed_event_lines'] for r in rows),
        web_search_count=len(searches),web_screening_flags=flags,
        web_screening_scope='Native webSearch completed items for each exact solver thread; keyword screening is not proof of complete network isolation.',
        rows=rows,searches=searches)
    run.save(run.BASE/'controller/native-record-audit.json',result)
    return {k:v for k,v in result.items() if k not in ('rows','searches','web_screening_flags')},flags


if __name__=='__main__':
    result,flags=audit();print(json.dumps(result));print('screening_flags',len(flags))
