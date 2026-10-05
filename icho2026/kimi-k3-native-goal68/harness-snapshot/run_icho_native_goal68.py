#!/usr/bin/env python3
"""Native Codex goal baseline. Host scheduler does not generate review/redraft prompts."""
import argparse
import asyncio
import hashlib
import json
import os
from pathlib import Path
import shutil
import time
from types import SimpleNamespace

import run_kimi_nl_gpt_remaining36 as infra

BASE = Path('/home/jing/icho-native-goal-gpt68-20260913-01')
MODEL = 'gpt-5.6-sol'
CONCURRENCY = 32


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    infra.save(path, data)


def args_for(root):
    return SimpleNamespace(runtime=BASE/'runtime', seed=BASE/'seed', campaign=root/'campaign',
        private_home=root/'private-home', packages=Path('/home/jing/icho-full68-dependencies/.lake/packages'),
        lean_bin=Path('/home/jing/.elan/toolchains/leanprover--lean4---v4.31.0/bin'), python=infra.PYTHON,
        codex=Path('/home/jing/.codex/packages/standalone/releases/0.153.4-x86_64-unknown-linux-musl/bin/codex'),
        bwrap=Path('/home/jing/icho-full68-runtime/tools/bubblewrap/usr/bin/bwrap'))


def command(args, argv):
    cmd = infra.namespace(args, argv)
    index = cmd.index('--chdir')
    work = args.campaign/'workspace'
    protected = [work/'TASK.json', work/'GOAL.txt']
    protected += [work/p.relative_to(BASE/'seed') for p in (BASE/'seed').rglob('*')
                  if p.is_file() and 'icho_2026_source' not in p.parts]
    mounts = []
    for path in protected:
        mounts += ['--ro-bind', str(path), str(path)]
    cmd[index:index] = mounts
    return cmd


class RPC:
    def __init__(self, process, log):
        self.process, self.log = process, log
        self.serial = 0
        self.pending = {}
        self.events = asyncio.Queue()
        self.reader = asyncio.create_task(self.read())

    async def read(self):
        try:
            while line := await self.process.stdout.readline():
                self.log.write(line.decode()); self.log.flush()
                obj = json.loads(line)
                if 'id' in obj and ('result' in obj or 'error' in obj):
                    future = self.pending.pop(obj['id'], None)
                    if future and not future.done():
                        if 'error' in obj: future.set_exception(RuntimeError(str(obj['error'])))
                        else: future.set_result(obj['result'])
                elif 'id' in obj:
                    # No human approvals, external writes or extra information are supplied.
                    self.process.stdin.write((json.dumps({'id':obj['id'], 'error':{'code':-32601,
                        'message':'Unattended baseline: client requests unavailable'}})+'\n').encode())
                    await self.process.stdin.drain()
                else:
                    await self.events.put(obj)
        finally:
            for future in self.pending.values():
                if not future.done(): future.set_exception(RuntimeError('app-server closed'))
            await self.events.put({'method':'controller/server_closed'})

    async def call(self, method, params):
        self.serial += 1
        future = asyncio.get_running_loop().create_future()
        self.pending[self.serial] = future
        self.process.stdin.write((json.dumps({'id':self.serial,'method':method,'params':params})+'\n').encode())
        await self.process.stdin.drain()
        return await asyncio.wait_for(future, 60)


def objective(target):
    return f'''Independently solve and faithfully formalize IChO 2026 subquestion {target} from the problem-only inputs in this workspace. Read TASK.json, the relevant question images, and original theory_problem.pdf including the blank student answer sheets. Write answer.md with a complete natural-language answer and source-grounding explanation, and IChO2026Problems/problem_{target}.lean with substantive Lean 4 proofs of every requested output. Use the native goal lifecycle to continue until the deliverables are complete and Lean verification succeeds, or report a genuine source/technical blocker honestly. Do not use Humanize/Archon, external solver agents, official solutions, marking schemes, grading reports, historical experiment answers/proofs, or answer repositories. Other question statements in the provided bundle may establish prerequisites; prove any required dependencies yourself. Ordinary scientific references are allowed but not competition answers. Do not assume a final answer, weaken the requested statement, introduce unsupported scientific premises, or use sorry/admit/unsafe proof shortcuts. No supplementary user model assumptions have been authorized for this fresh baseline. Separate actual problem inputs from derived lemmas; if the problem does not ground a necessary condition, explicitly report the gap instead of claiming unconditional success. Compile using lake env lean on the final file, inspect #print axioms for final theorems, and record exact commands and results in verification.md. Standard Lean logical axioms are allowed; custom unchecked axioms are not. Maintain result.json with target_id, status (completed or blocked), answer_summary, theorem_names, assumptions, source_gaps, and verification_commands. A successful build alone does not establish semantic faithfulness; independently check that the theorem states and proves the requested chemistry. Do not modify source inputs or generic infrastructure. Work only on this target; do not run git push or other external writes.'''


def prepare():
    if (BASE/'manifest.json').exists():
        return
    if BASE.exists(): raise RuntimeError('Partial preparation exists; inspect before resuming')
    BASE.mkdir()
    for rel in ['runtime/bin','runtime/src','controller','jobs']:
        (BASE/rel).mkdir(parents=True, exist_ok=True)
    bundle = Path('/home/jing/icho-full68-controller-v2/questions_only.jsonl')
    rows = [json.loads(s) for s in bundle.read_text().splitlines()]
    assert len(rows) == len({r['id'] for r in rows}) == 68
    images = sorted({Path(a['path']).name for r in rows for a in r['problem_assets'] if a['kind']=='problem_page'})
    infra.B.build_seed(source_root=infra.REPO, questions_only=bundle,
        problem_pdf=infra.REPO/'icho_2026_source/raw/theory_problem.pdf',
        image_root=infra.REPO/'icho_2026_source/image', problem_images=images, output_dir=BASE/'seed')
    # Include already verified blank student answer-sheet images, never solved sheets.
    assets = infra.REPO/'src/archon/commands/loop/student_problem_page_assets'
    for page in [79, 80]:
        shutil.copy2(assets/f'icho_2026_t8_a4-page-{page}.png', BASE/'seed/icho_2026_source/image')
    for row in rows:
        root = BASE/'jobs'/row['id']
        a = args_for(root)
        work = a.campaign/'workspace'
        shutil.copytree(BASE/'seed', work, ignore=shutil.ignore_patterns('icho_2026_source'))
        (work/'icho_2026_source').symlink_to(BASE/'seed/icho_2026_source', target_is_directory=True)
        (work/'.lake').mkdir(exist_ok=True)
        (work/'.lake/packages').symlink_to(a.packages, target_is_directory=True)
        (work/'IChO2026Problems').mkdir(exist_ok=True)
        (a.private_home/'.codex').mkdir(parents=True, mode=0o700)
        save(work/'TASK.json',row)
        (work/'GOAL.txt').write_text(objective(row['id'])+'\n')
    shutil.copy2(__file__, BASE/'controller/launcher.py')
    save(BASE/'manifest.json',dict(model=MODEL, reasoning_effort='xhigh', concurrency=32,
        targets=[r['id'] for r in rows], protocol='native-codex-thread-goal-v1',
        fresh_answer_blind=True, humanize_solver_loop=False, supplementary_assumptions=[],
        token_budget=None, source_sha256=infra.sha(bundle), created=time.time(),
        files={str(p.relative_to(BASE/'seed')):infra.sha(p) for p in (BASE/'seed').rglob('*') if p.is_file()}))


async def open_rpc(root):
    a = args_for(root)
    err = (root/'app-server.stderr.log').open('a')
    proc = await asyncio.create_subprocess_exec(*command(a, ['/tools/codex','app-server','--stdio',
        '--enable','goals','-c','model="gpt-5.6-sol"','-c','model_reasoning_effort="xhigh"']),
        stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE, stderr=err, limit=16*1024*1024)
    log = (root/'events.jsonl').open('a')
    rpc = RPC(proc, log)
    await rpc.call('initialize', {'clientInfo':{'name':'icho_native_goal_baseline','version':'1.0'},
                                 'capabilities':{'experimentalApi':True}})
    proc.stdin.write(b'{"method":"initialized","params":{}}\n')
    await proc.stdin.drain()
    return rpc, log, err


async def preflight():
    root=BASE/'jobs/icho_2026_t1_a1'
    rpc,log,err=await open_rpc(root)
    try:
        response=await rpc.call('thread/start', {'model':MODEL,'cwd':str(root/'campaign/workspace'),
            'approvalPolicy':'never','sandbox':'danger-full-access'})
        thread=response['thread']['id']
        goal=await rpc.call('thread/goal/set',{'threadId':thread,'objective':'API preflight only; do not run any task.','status':'paused'})
        check=await rpc.call('thread/goal/get',{'threadId':thread})
        assert check['goal']['status']=='paused'
        await rpc.call('thread/goal/clear',{'threadId':thread})
        save(BASE/'controller/preflight.json',dict(status='passed',thread=thread,goal=goal,at=time.time()))
    finally:
        rpc.process.terminate(); await rpc.process.wait(); await rpc.reader
        log.close();err.close()


async def run_target(target, sem):
    root=BASE/'jobs'/target
    async with sem:
        previous=json.loads((root/'status.json').read_text()) if (root/'status.json').exists() else {}
        if previous.get('status') in ['goal_complete','goal_blocked']: return
        rpc=None
        try:
            rpc,log,err=await open_rpc(root)
            params={'model':MODEL,'cwd':str(root/'campaign/workspace'),
                    'approvalPolicy':'never','sandbox':'danger-full-access'}
            if previous.get('thread_id'):
                params['threadId']=previous['thread_id']
                response=await rpc.call('thread/resume',params)
            else:
                response=await rpc.call('thread/start',params)
            thread=response['thread']['id']
            state=dict(status='running',target=target,thread_id=thread,pid=rpc.process.pid,started=time.time())
            save(root/'status.json',state)
            current=await rpc.call('thread/goal/get',{'threadId':thread})
            if not current.get('goal'):
                await rpc.call('thread/goal/set',{'threadId':thread,'objective':objective(target),'status':'active'})
            elif previous.get('status') == 'transport_resume_pending':
                # Explicit controller recovery only after an audited API failure;
                # preserve the goal, thread and candidate, without review feedback.
                assert current['goal']['status'] == 'blocked'
                await rpc.call('thread/goal/set',{'threadId':thread,
                    'objective':current['goal']['objective'],'status':'active'})
            await rpc.call('turn/start',{'threadId':thread,'effort':'xhigh','input':[{'type':'text',
                'text':'Carry out the persisted goal. Read GOAL.txt and TASK.json first. Continue existing work if present.'}]})
            last_check = 0
            while True:
                try: event=await asyncio.wait_for(rpc.events.get(),30)
                except asyncio.TimeoutError: event={}
                if event.get('method')=='controller/server_closed': raise RuntimeError('app-server exited')
                if time.monotonic()-last_check < 30 and event.get('method') not in ['thread/goal/updated','turn/completed']:
                    continue
                last_check = time.monotonic()
                # Native app-server owns continuation. The scheduler never injects retry/review prompts.
                goal=(await rpc.call('thread/goal/get',{'threadId':thread})).get('goal')
                state['updated']=time.time();state['goal']=goal
                if goal and goal['status'] in ['complete','blocked','paused','budgetLimited','usageLimited']:
                    # Goal completion can occur before the last tool/final response finishes.
                    info = await rpc.call('thread/read', {'threadId':thread,'includeTurns':False})
                    if info['thread']['status']['type'] != 'active':
                        state['status']='goal_'+goal['status'];save(root/'status.json',state)
                        break
                save(root/'status.json',state)
        except Exception as exc:
            state=locals().get('state',dict(target=target))
            state.update(status='controller_error',error=str(exc),updated=time.time())
            save(root/'status.json',state)
        finally:
            if rpc:
                if rpc.process.returncode is None:
                    rpc.process.terminate();await rpc.process.wait()
                await rpc.reader;log.close();err.close()


async def main(mode):
    prepare()
    if mode=='prepare': return
    if mode=='preflight': return await preflight()
    assert (BASE/'controller/preflight.json').exists(), 'preflight required before models'
    targets=json.loads((BASE/'manifest.json').read_text())['targets']
    save(BASE/'status.json',dict(status='running',pid=os.getpid(),concurrency=32,model=MODEL,total=68,started=time.time()))
    sem=asyncio.Semaphore(CONCURRENCY)
    await asyncio.gather(*(run_target(t,sem) for t in targets))
    save(BASE/'status.json',dict(status='all_jobs_returned_pending_independent_validation',total=68,at=time.time()))


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('mode',choices=['prepare','preflight','run'])
    asyncio.run(main(parser.parse_args().mode))
