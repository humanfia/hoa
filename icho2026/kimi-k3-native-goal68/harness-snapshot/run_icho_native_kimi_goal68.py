#!/usr/bin/env python3
"""Native persisted Kimi-K3 goals, NVIDIA Responses with ordering relay; no answer reuse."""
import asyncio
import argparse
import json
import os
from pathlib import Path
import shutil
import time
import run_icho_native_goal68 as native
from kimi_responses_transport import start_relay

BASE=Path('/home/jing/icho-native-goal-kimi68-20260914-01')
MODEL='nvidia/moonshotai/kimi-k3'
native.BASE=BASE
native.MODEL=MODEL
ORIGINAL_COMMAND=native.command
PROVIDER_URL='https://inference-api.nvidia.com/v1'


def command(args,argv):
    cmd=ORIGINAL_COMMAND(args,argv)
    # Do not mount the user's unrelated OpenAI login. Only this provider key is
    # inherited through the subprocess environment, never a command-line value.
    i=cmd.index('/home/jing/.codex/auth.json')
    assert cmd[i-1]=='--ro-bind'
    del cmd[i-1:i+2]
    cmd.remove('--clearenv')
    return cmd


def provider_config():
    return ['model='+json.dumps(MODEL),'model_provider="nvidia_icho"',
        'model_providers.nvidia_icho.name="NVIDIA IChO Kimi"',
        'model_providers.nvidia_icho.base_url='+json.dumps(PROVIDER_URL),
        'model_providers.nvidia_icho.env_key="ICHO_KIMI_API_KEY"',
        'model_providers.nvidia_icho.wire_api="responses"',
        'model_providers.nvidia_icho.requires_openai_auth=false',
        'model_providers.nvidia_icho.supports_websockets=false',
        'model_providers.nvidia_icho.stream_idle_timeout_ms=600000',
        'model_providers.nvidia_icho.request_max_retries=8',
        'model_catalog_json='+json.dumps(str(BASE/'runtime/kimi-model-catalog.json')),
        'model_reasoning_effort="xhigh"','web_search="disabled"']


async def open_rpc(root):
    args=native.args_for(root)
    config=provider_config()
    argv=['/tools/codex','app-server','--stdio','--enable','goals','--disable','multi_agent']
    for value in config:argv+=['-c',value]
    err=(root/'app-server.stderr.log').open('a')
    env={'PATH':'/usr/bin:/bin','LANG':'C.UTF-8','ICHO_KIMI_API_KEY':os.environ['ICHO_KIMI_API_KEY']}
    proc=await asyncio.create_subprocess_exec(*command(args,argv),env=env,
        stdin=asyncio.subprocess.PIPE,stdout=asyncio.subprocess.PIPE,stderr=err,limit=16*1024*1024)
    log=(root/'events.jsonl').open('a');rpc=native.RPC(proc,log)
    await rpc.call('initialize',{'clientInfo':{'name':'icho_native_kimi_baseline','version':'1.0'},'capabilities':{'experimentalApi':True}})
    proc.stdin.write(b'{"method":"initialized","params":{}}\n');await proc.stdin.drain()
    return rpc,log,err


def prepare():
    assert not BASE.exists(),'Existing experiment must be inspected, not overwritten'
    native.prepare()
    # Dependency available before the first Kimi model call, not added mid-run.
    pdfcache=Path('/home/jing/.cache/uv/archive-v0/wDOgr5V0cDEN5-3z')
    for name in ('pymupdf','fitz'):
        shutil.copytree(pdfcache/name,BASE/'runtime/src'/name)
    m=json.loads((BASE/'manifest.json').read_text())
    m.update(provider='nvidia_icho',base_url='https://inference-api.nvidia.com/v1',
        wire_api='responses',reasoning_effort_requested='xhigh',
        reasoning_effort_effect='provider-dependent; not assumed equivalent to GPT effort',
        built_in_web_search=False,ordinary_scientific_http_from_shell=True,
        credential_policy='environment-only NVIDIA key; no OpenAI auth mount; never exported',
        pdf_dependency_available_before_launch=True)
    native.save(BASE/'manifest.json',m)
    shutil.copy2(__file__,BASE/'controller/kimi-launcher.py')


async def preflight(attempt='preflight'):
    root=BASE/attempt;args=native.args_for(root);work=args.campaign/'workspace'
    shutil.copytree(BASE/'seed',work,ignore=shutil.ignore_patterns('icho_2026_source'))
    (work/'icho_2026_source').symlink_to(BASE/'seed/icho_2026_source',target_is_directory=True)
    (work/'.lake').mkdir();(work/'.lake/packages').symlink_to(args.packages,target_is_directory=True)
    (args.private_home/'.codex').mkdir(parents=True,mode=0o700)
    objective='Preflight only, not chemistry solving. Use a shell tool to write Probe.lean containing `example : 2 + 2 = 4 := by decide`, verify it with `lake env lean Probe.lean`, inspect the supplied question-page image using an image-viewing tool, then write preflight.txt containing PREFLIGHT_OK and the exact large blue numbered problem title read from the image pixels. Do not substitute an inferred generic document title. Never read credentials or solve competition questions. Mark this native goal complete only after those checks.'
    native.save(work/'TASK.json',{'id':'preflight','image':'icho_2026_source/image/T8_page-1.png'})
    (work/'GOAL.txt').write_text(objective+'\n')
    rpc,log,err=await open_rpc(root)
    try:
        response=await rpc.call('thread/start',{'model':MODEL,'cwd':str(work),'approvalPolicy':'never','sandbox':'danger-full-access'})
        thread=response['thread']['id']
        await rpc.call('thread/goal/set',{'threadId':thread,'objective':objective,'status':'active'})
        await rpc.call('turn/start',{'threadId':thread,'effort':'xhigh','input':[{'type':'text','text':objective}]})
        native.save(BASE/'status.json',dict(status='preflight_running',pid=os.getpid(),model=MODEL,thread_id=thread,started=time.time()))
        deadline=time.monotonic()+900
        while time.monotonic()<deadline:
            try:event=await asyncio.wait_for(rpc.events.get(),20)
            except asyncio.TimeoutError:event={}
            if event.get('method')=='controller/server_closed':raise RuntimeError('preflight app-server exited')
            goal=(await rpc.call('thread/goal/get',{'threadId':thread})).get('goal')
            if goal and goal['status']=='complete':
                info=await rpc.call('thread/read',{'threadId':thread,'includeTurns':False})
                if info['thread']['status']['type']=='active':continue
                assert (work/'preflight.txt').exists() and 'PREFLIGHT_OK' in (work/'preflight.txt').read_text()
                assert 'carbon dioxide' in (work/'preflight.txt').read_text().lower(),'Image-title check failed'
                assert (work/'Probe.lean').exists()
                proc=await asyncio.create_subprocess_exec(*command(args,['lake','-d',str(work),'env','lean',str(work/'Probe.lean')]),
                    env={'PATH':'/usr/bin:/bin','LANG':'C.UTF-8'},stdout=asyncio.subprocess.PIPE,stderr=asyncio.subprocess.STDOUT)
                output,_=await proc.communicate();assert proc.returncode==0,output.decode(errors='replace')[:300]
                native.save(BASE/'controller/preflight.json',dict(status='passed',model=MODEL,thread_id=thread,goal=goal,lean_exit_code=0,at=time.time()))
                return
            if goal and goal['status'] in ('blocked','paused'):raise RuntimeError('preflight goal '+goal['status'])
        raise RuntimeError('Preflight did not finish within 900 seconds; no solver jobs started')
    finally:
        if rpc.process.returncode is None:rpc.process.terminate();await rpc.process.wait()
        await rpc.reader;log.close();err.close()


def configure_catalog():
    # Copy public Codex capability metadata and its coding-agent template, never
    # session messages or credentials. The explicit image modality prevents text-only fallback for
    # this non-built-in model ID. Context size is a conservative client setting.
    cache=json.loads(Path('/home/jing/.codex/models_cache.json').read_text())
    template=next(m for m in cache['models'] if m['slug']=='gpt-5.6-sol')
    keys=('default_reasoning_level','supported_reasoning_levels','shell_type','visibility',
          'supported_in_api','priority','default_reasoning_summary','support_verbosity',
          'default_verbosity','apply_patch_tool_type','web_search_tool_type','truncation_policy',
          'effective_context_window_percent','experimental_supported_tools')
    model={k:template[k] for k in keys if k in template}
    model.update(slug=MODEL,display_name='Kimi-K3 (NVIDIA)',description='User-selected Kimi-K3 through NVIDIA Responses',
        input_modalities=['text','image'],supports_image_detail_original=False,
        context_window=128000,max_context_window=128000,supports_search_tool=False,
        model_messages={
            'instructions_template':template['model_messages']['instructions_template'].replace(
                'You are Codex, an agent based on GPT-5.', 'You are Codex, a coding agent powered by Kimi-K3.'),
            'instructions_variables':template['model_messages']['instructions_variables']},
        default_reasoning_level='xhigh')
    native.save(BASE/'runtime/kimi-model-catalog.json',{'models':[model]})
    m=json.loads((BASE/'manifest.json').read_text());m.update(explicit_model_input_modalities=['text','image'],client_context_window=128000,
        model_catalog_sha256=native.infra.sha(BASE/'runtime/kimi-model-catalog.json'))
    native.save(BASE/'manifest.json',m)


async def main(resume_preflight=False,attempt=None,preflight_only=False,launch_after_preflight=False):
    global PROVIDER_URL
    assert os.environ.get('ICHO_KIMI_API_KEY'),'Provider credential missing'
    if launch_after_preflight:
        assert not resume_preflight and not preflight_only
        assert json.loads((BASE/'status.json').read_text())['status']=='preflight_passed_pending_launch'
        assert json.loads((BASE/'controller/preflight.json').read_text())['status']=='passed'
        assert not list((BASE/'jobs').glob('*/status.json')),'Solver jobs already initialized'
    elif resume_preflight:
        assert (BASE/'status.json').exists()
        assert json.loads((BASE/'status.json').read_text())['status']=='preflight_or_controller_error'
        assert not list((BASE/'jobs').glob('*/status.json')),'Solver jobs already initialized'
    else:prepare()
    configure_catalog()
    relay=start_relay(os.environ['ICHO_KIMI_API_KEY'],BASE/'controller/transport-structure.jsonl')
    PROVIDER_URL=f'http://127.0.0.1:{relay.server_port}/v1'
    native.command=command
    native.open_rpc=open_rpc
    if not launch_after_preflight:
        await preflight(attempt or ('preflight-02' if resume_preflight else 'preflight'))
    if preflight_only:
        native.save(BASE/'status.json',dict(status='preflight_passed_pending_launch',at=time.time()))
        return
    # Successful native lifecycle plus independent kernel check required first.
    relay_source=Path(__file__).with_name('kimi_responses_transport.py')
    shutil.copy2(__file__,BASE/'controller/kimi-launcher.py')
    shutil.copy2(relay_source,BASE/'controller/kimi_responses_transport.py')
    m=json.loads((BASE/'manifest.json').read_text())
    m.update(transport_adapter='loopback Responses relay; move same-turn assistant prose before tool calls',
             transport_preserves='all original messages, reasoning, tool arguments, results and images; no scientific changes',
             transport_sha256=native.infra.sha(relay_source),
             solver_model=MODEL,solver_concurrency=native.CONCURRENCY)
    native.save(BASE/'manifest.json',m)
    await native.main('run')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--resume-preflight',action='store_true');parser.add_argument('--preflight-attempt');parser.add_argument('--preflight-only',action='store_true');parser.add_argument('--launch-after-preflight',action='store_true');args=parser.parse_args()
    try:asyncio.run(main(args.resume_preflight,args.preflight_attempt,args.preflight_only,args.launch_after_preflight))
    except Exception as exc:
        if BASE.exists():native.save(BASE/'status.json',dict(status='preflight_or_controller_error',error=type(exc).__name__+': '+str(exc),at=time.time()))
        raise
