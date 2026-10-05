"""Read-only post-terminal validation watcher; never sends solver feedback."""
import concurrent.futures
import json
import os
import time
from pathlib import Path

import run_icho_native_kimi_goal68 as kimi
import validate_icho_native_goal68 as validation

validation.run.BASE = kimi.BASE
validation.run.command = kimi.command


def main():
    active = {}
    attempted = set()
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        while True:
            summary = validation.summary()
            for target, (future, signature) in list(active.items()):
                if future.done():
                    try:
                        future.result()
                    except Exception as exc:
                        validation.run.save(kimi.BASE/'controller/validation'/target/'watcher-error.json',
                                            {'exception_type':type(exc).__name__, 'at':time.time()})
                    attempted.add((target, signature))
                    del active[target]
            for row in summary['targets']:
                target = row['target']
                if len(active) >= 2:
                    break
                signature=(row['status'],row.get('tokens_used'))
                if row['status'] in ('goal_complete','goal_blocked') and (target,signature) not in attempted and target not in active:
                    active[target] = (pool.submit(validation.verify, target),signature)
            state = json.loads((kimi.BASE/'status.json').read_text())
            controller_pid = state.get('pid')
            controller_live = False
            if controller_pid:
                try:
                    os.kill(controller_pid, 0)
                    controller_live = True
                except ProcessLookupError:
                    pass
            records = [json.loads(p.read_text()) for p in (kimi.BASE/'controller/validation').glob('*/receipt.json')]
            waiting = any(row['status'] in ('goal_complete','goal_blocked') and
                          (row['target'],(row['status'],row.get('tokens_used'))) not in attempted
                          for row in summary['targets'])
            done = not controller_live and not active and not waiting and not any(
                row['status'] in ('running','transport_resume_pending') for row in summary['targets'])
            validation.run.save(kimi.BASE/'controller/validation-watcher.json', {
                'status':'finished' if done else 'monitoring', 'pid':os.getpid(),
                'controller_live':controller_live,'active':list(active),'attempted':len(attempted),
                'kernel_passed':sum(x.get('kernel_check')=='passed' for x in records),
                'semantic_review':'not_started', 'feedback_to_solver':False, 'updated':time.time()})
            if done:
                return
            time.sleep(30)


if __name__ == '__main__':
    main()
