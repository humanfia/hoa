"""Separate Kimi assessments of frozen submissions, without solver feedback."""
import asyncio
import json
import os
import re
import time
import jsonschema
import run_icho_native_kimi_goal68 as kimi
import review_icho_native_goal68 as review
from kimi_responses_transport import start_relay
from resume_kimi_native_transport import recoverable

review.REVIEW_ROOT=kimi.BASE/'reviews'


def strip_json_trailing_commas(text):
    """Remove only commas before closing brackets outside JSON strings."""
    out=[]
    quoted=False
    escaped=False
    for i, char in enumerate(text):
        if quoted:
            out.append(char)
            if escaped:
                escaped=False
            elif char=='\\':
                escaped=True
            elif char=='"':
                quoted=False
            continue
        if char=='"':
            quoted=True
        if char==',':
            j=i+1
            while j<len(text) and text[j] in ' \t\r\n':
                j+=1
            if j<len(text) and text[j] in '}]':
                continue
        out.append(char)
    return ''.join(out)


def decode_review_json(text):
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        return json.loads(strip_json_trailing_commas(text))


def is_review_schema(value):
    return (isinstance(value,dict) and value.get('type')=='object' and
            set(value)<= {'$schema','type','additionalProperties','properties','required'} and
            isinstance(value.get('properties'),dict) and
            set(value['properties'])==set(review.SCHEMA['properties']) and
            isinstance(value.get('required'),list) and
            set(value['required'])==set(review.SCHEMA['required']))


def load_review(text):
    """Accept a single JSON payload, optionally fenced; never repair its verdict."""
    try:
        result=decode_review_json(text)
    except json.JSONDecodeError:
        blocks=re.findall(r'```(?:json)?\s*\n(.*?)\n```',text,re.DOTALL)
        if len(blocks)==1:
            result=decode_review_json(blocks[0])
        elif blocks:
            values=[decode_review_json(block) for block in blocks]
            # A schema echo describes fields; it is not a second assessment.
            # Only discard schema-shaped documentation of this exact field set.
            values=[value for value in values if not is_review_schema(value)]
            if len(values)!=1:
                raise ValueError('Expected exactly one review JSON payload')
            result=values[0]
        else:
            # Some final messages contain a prose preamble then one unfenced
            # JSON object. Extract, never rewrite, only an unambiguous payload.
            candidates=[]
            consumed_until=0
            for match in re.finditer(r'(?m)^\s*\{',text):
                start=match.end()-1
                if start<consumed_until:
                    continue
                suffix=text[start:]
                try:
                    value,end=json.JSONDecoder().raw_decode(suffix)
                except json.JSONDecodeError:
                    continue
                candidates.append((value,suffix[end:].strip()))
                consumed_until=start+end
                # Some responses concatenate the echoed schema and verdict
                # without a newline. Decode each complete adjacent object;
                # never choose between two actual verdicts.
                while text[consumed_until:].lstrip().startswith('{'):
                    remaining=text[consumed_until:]
                    offset=len(remaining)-len(remaining.lstrip())
                    next_start=consumed_until+offset
                    try:
                        value,end=json.JSONDecoder().raw_decode(text[next_start:])
                    except json.JSONDecodeError:
                        break
                    consumed_until=next_start+end
                    candidates.append((value,text[consumed_until:].strip()))
            candidates=[entry for entry in candidates if not is_review_schema(entry[0])]
            if len(candidates)!=1 or candidates[0][1]:
                raise ValueError('Expected exactly one review JSON payload')
            result=candidates[0][0]
    jsonschema.validate(result,review.SCHEMA)
    return result


def command(args, argv):
    argv=list(argv)
    if argv[:2]==['/tools/codex','exec']:
        # NVIDIA forced-schema mode returned final placeholders without tool use
        # in two toy probes. Keep identical schema validation on the host, while
        # permitting ordinary tool execution before the final JSON submission.
        if '--output-schema' in argv:
            i=argv.index('--output-schema')
            del argv[i:i+2]
            argv[-1]+=('\nExecute the source and proof checks with tools BEFORE issuing '
                       'a final review. Do not submit a provisional review. Return one '
                       'JSON object matching this schema:\n'+json.dumps(review.SCHEMA))
        extra=['--disable','multi_agent']
        for value in kimi.provider_config():
            extra+=['-c',value]
        argv[2:2]=extra
    return kimi.command(args,argv)


async def main():
    assert os.environ.get('ICHO_KIMI_API_KEY')
    root=review.REVIEW_ROOT
    root.mkdir(exist_ok=True)
    relay=start_relay(os.environ['ICHO_KIMI_API_KEY'],root/'transport-structure.jsonl')
    kimi.PROVIDER_URL=f'http://127.0.0.1:{relay.server_port}/v1'
    review.run.command=command
    active={}
    while True:
        # The kernel watcher owns summary.json. This waiter is a read-only
        # consumer, avoiding concurrent replacement of the shared .tmp path.
        summary=review.validation.summary(persist=False)
        unfinished=[r for r in summary['targets'] if r['status'] not in ('goal_complete','goal_blocked')]
        technical=[r['target'] for r in summary['targets'] if r['status']=='goal_blocked' and
                   recoverable(kimi.BASE/'jobs'/r['target'])]
        for target,task in list(active.items()):
            if task.done():
                await task
                del active[target]
        for row in summary['targets']:
            if len(active)>=2:
                break
            target=row['target']
            if (row['status'] not in ('goal_complete','goal_blocked') or
                target in technical or target in active or (root/target).exists()):
                continue
            active[target]=asyncio.create_task(review.review(target,result_loader=load_review))
        statuses=[json.loads(p.read_text()) for p in root.glob('*/status.json')]
        finished=(not unfinished and not technical and not active and
                  len(statuses)==len(summary['targets']) and
                  all(s['status'] in ('reviewed','review_error') for s in statuses))
        kimi.native.save(root/'status.json',{'status':'review_batch_finished' if finished else 'monitoring',
            'pid':os.getpid(),'unfinished':len(unfinished),'transport_blocked':technical,
            'active':list(active),'concurrency':2,
            'reviewed':sum(s['status']=='reviewed' for s in statuses),
            'errors':sum(s['status']=='review_error' for s in statuses),
            'accepted':sum(s.get('accepted',False) for s in statuses),
            'model':kimi.MODEL,'feedback_to_solver':False,'updated':time.time()})
        if finished:
            return
        await asyncio.sleep(30)


if __name__=='__main__':asyncio.run(main())
