#!/usr/bin/env python3
"""Replay immutable exposure submissions in the unchanged offline executor.
No researcher-supplied code executes in the host; the local provider is scripted.
"""
import argparse,asyncio,base64,hashlib,importlib.util,json,os,re,shlex,time
from pathlib import Path
from types import SimpleNamespace
from audit_generator import audit_source
S=Path(__file__).resolve().parents[2]
D=Path('/data/ivy-rh080-next-20261125')
TRIALS=['fixed_width-B_named-r1','fixed_width-C_network-r0','prime_index-B_named-r1']
BACKEND=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-deep-tertiary-exposure-a-20261117/scripts/native_controller_v2.py')
BACKEND_SHA='89784de8153c616219a4a93d23f1859845d18924ad472d0d6321fb0eb2661091'
def need(ok,message):
    if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def unique(items):
    result={}
    for key,value in items:
        need(key not in result,'Duplicate JSON key');result[key]=value
    return result
def load(p):return json.loads(p.read_bytes(),object_pairs_hook=unique,parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))
def module_at(name,path):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
def save(p,j):
    need(not p.exists(),'Fresh receipt required');tmp=p.with_name('.'+p.name+'.tmp')
    with tmp.open('x') as f:json.dump(j,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(tmp,p)
    finally:tmp.unlink()

def worker_source(trial,module,source,audit):
    data=dict(trial=trial,module=module,source=base64.b64encode(source).decode(),source_sha256=hashlib.sha256(source).hexdigest(),audit=base64.b64encode(audit.encode()).decode())
    return 'DATA='+repr(data)+'\n'+r'''
import os,json,base64,hashlib,subprocess,time
from pathlib import Path
def need(ok,message):
    if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
work=Path('/work');out=work/'submission';out.mkdir();(work/'objects').mkdir(exist_ok=True)
probe=dict(host_absent=not Path('/ryu/hyunsik/playground/independence/codex/ivy/memory').exists(),auth_absent=not Path('/home/worker/.codex/auth.json').exists(),controller_canary_absent=not Path('host-only-canary.txt').exists(),pid_namespace=os.readlink('/proc/self/ns/pid'),net_namespace=os.readlink('/proc/self/ns/net'),genericLean_available=Path('/opt/lean/bin/lean').is_file())
need(all(probe[k] for k in ['host_absent','auth_absent','controller_canary_absent','genericLean_available']),'Isolation probe failed')
source=work/(DATA['module']+'.lean');source.write_bytes(base64.b64decode(DATA['source'],validate=True));need(sha(source)==DATA['source_sha256'],'Exact submission bytes differ')
audit=work/'IndependentAudit.lean';audit.write_bytes(base64.b64decode(DATA['audit'],validate=True))
records=[]
for name,path in [(DATA['module'],source),('IndependentAudit',audit)]:
    obj=work/'objects'/(name+'.olean');command=['/bin/lean','-j2','--root=/work','-o',str(obj),str(path)];start=time.monotonic()
    try:
        p=subprocess.run(command,capture_output=True,text=True,timeout=540)
        stdout=p.stdout;stderr=p.stderr;code=p.returncode
    except subprocess.TimeoutExpired as e:
        stdout=(e.stdout or b'').decode() if isinstance(e.stdout,bytes) else e.stdout or '';stderr=(e.stderr or b'').decode() if isinstance(e.stderr,bytes) else e.stderr or '';code=124
    (out/(name+'.stdout')).write_text(stdout);(out/(name+'.stderr')).write_text(stderr)
    row=dict(module=name,source_sha256=sha(path),command=command,exitcode=code,seconds=time.monotonic()-start,stdout_sha256=sha(out/(name+'.stdout')),stderr_sha256=sha(out/(name+'.stderr')),object_sha256=sha(obj) if obj.exists() else None)
    records.append(row)
    if code:break
result=dict(status='COMPILED_AND_INDEPENDENTLY_AUDITED' if len(records)==2 and all(x['exitcode']==0 for x in records) else 'COMPILER_OR_AUDIT_FAILED',trial=DATA['trial'],source_sha256=sha(source),audit_sha256=sha(audit),isolation=probe,records=records,lean_version=subprocess.check_output(['/bin/lean','--version'],text=True).strip(),lean_path=os.environ.get('LEAN_PATH'),external_model_inference_calls=0,scope='SUPPLEMENTAL_INDEPENDENT_REVIEW_PRIMARY_TRIAL_UNCHANGED')
(out/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');(out/(DATA['module']+'.lean')).write_bytes(source.read_bytes());(out/'IndependentAudit.lean').write_bytes(audit.read_bytes())
files=[dict(path=p.name,sha256=sha(p)) for p in sorted(out.iterdir()) if p.is_file()]
(out/'LOCK.json').write_text(json.dumps(dict(files=files),indent=2)+'\n')
print(json.dumps(dict(trial=DATA['trial'],status=result['status'],checks=len(records),probe=probe)),flush=True)
'''

def scripted_handler(base,script):
    class Review(base):
        def do_POST(self):
            data=json.loads(self.rfile.read(int(self.headers['Content-Length'])));self.server.requests.append(data)
            n=len(self.server.requests);offered={t.get('name'):t.get('type') for t in data.get('tools',[])}
            if n==1:
                name='exec_command';arguments=dict(cmd='/usr/bin/python3.10 -I -c '+shlex.quote(script),shell='/bin/bash',login=False,yield_time_ms=30000,max_output_tokens=1500)
            else:
                raw=json.dumps(data)
                matches=re.findall(r'(?:session_id\\?"\s*:\s*|session ID\s*:?\s*)([0-9]+)',raw,re.I)
                if matches and n<36:
                    name='write_stdin';arguments=dict(session_id=int(matches[-1]),chars='',yield_time_ms=30000,max_output_tokens=1500)
                else:name=None
            if name:
                if offered.get(name)=='function':item=dict(id='review'+str(n),type='function_call',call_id='review'+str(n),name=name,arguments=json.dumps(arguments))
                else:item=dict(id='review'+str(n),type='custom_tool_call',call_id='review'+str(n),name='exec',namespace='functions',input='text(await tools.'+name+'('+json.dumps(arguments)+'));')
            else:item=dict(id='final',type='message',role='assistant',status='completed',content=[dict(type='output_text',text='SCRIPTED_INDEPENDENT_REVIEW_COMPLETE',annotations=[])])
            usage=dict(input_tokens=7,output_tokens=3,total_tokens=10,output_tokens_details=dict(reasoning_tokens=1));response=dict(id='review'+str(n),object='response',created_at=int(time.time()),model=data['model'],status='completed',output=[item],usage=usage)
            events=[dict(type='response.created',response={**response,'status':'in_progress','output':[]}),dict(type='response.output_item.added',output_index=0,item=item),dict(type='response.output_item.done',output_index=0,item=item),dict(type='response.completed',response=response)]
            payload=''.join('event: '+e['type']+'\ndata: '+json.dumps(e)+'\n\n' for e in events).encode();self.send_response(200);self.send_header('Content-Type','text/event-stream');self.send_header('Content-Length',str(len(payload)));self.end_headers();self.wfile.write(payload)
    return Review

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--trial',required=True,choices=TRIALS);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    need(a.out.resolve().is_relative_to(D/'exposure-independent-review-v1') and not a.out.exists(),'Fresh owned review output required')
    summary=load(D/'exposure-matched-v2/EXPOSURE_RESEARCH_EXECUTION.json');rows=summary['rows'];need(len(rows)==16,'Primary universe changed')
    need({x['trial'] for x in rows if x['discovery_admissible_for_evaluation']}==set(TRIALS),'Admissible universe differs')
    need(sum(x['stop_reason']=='GENERATED_OUTPUT_ADMISSION_CEILING' for x in rows)==13,'Ceiling-stop universe changed')
    trial=D/'exposure-controller-v2/trials'/a.trial/'research-v1';result=load(trial/'result.json');selected=next(x for x in rows if x['trial']==a.trial)
    need(sha(trial/'result.json')==selected['result_sha256'],'Primary trial result changed')
    lock=trial/'submission/LOCK.json';need(sha(lock)==result['artifact_export']['lock_sha256']==selected['artifact_export']['lock_sha256'],'Exact primary LOCK bytes changed')
    files=load(lock)['files'];need(len(files)==len({x['path'] for x in files}),'Duplicate payload identity')
    for row in files:
        p=trial/'submission'/row['path'];need(p.name==row['path'] and p.is_file() and not p.is_symlink() and sha(p)==row['sha256'],'Payload identity changed')
    lean=[r for r in files if r['path'].endswith('.lean')];need(len(lean)==1,'Exactly one Lean payload expected')
    source=(trial/'submission'/lean[0]['path']).read_bytes();module=Path(lean[0]['path']).stem
    audit=audit_source(a.trial,module);script=worker_source(a.trial,module,source,audit)
    packet=a.out.parent/(a.out.name+'-packet');packet.mkdir();(packet/'TASK.md').write_text('Scripted independent compilation/audit only. No research inference. Exact primary submissions are immutable.\n')
    (packet/'WORKER_SCRIPT.py').write_text(script);(packet/'IndependentAudit.lean').write_text(audit)
    runtime_path=D/'exposure-controller-v2/trials/fixed_width-B_named-r1/runtime.json';runtime=load(runtime_path)
    adapter=module_at('review_pinned_adapter',S/'ablation/native_trial.py')
    need(sha(BACKEND)==BACKEND_SHA,'Pinned executor changed')
    for mount in runtime['mounts']:adapter.check_tree(Path(mount['source']),mount['manifest'])
    need(runtime['external_network'] is False and runtime['host_tools'] is False,'Runtime boundary differs')
    args=SimpleNamespace(out=a.out,packet=packet,model='gpt-6.2-sol',effort='high',fixture=True,wall=1200,output=18000,operations=180,responses=96,memory_gib=64,scratch_gib=12,cpus=4,per_response_max_output_tokens=None,phase='SUPPLEMENTAL_INDEPENDENT_REVIEW',fixture_hook_fault=False,fixture_artifact_name='REVIEW.json',fixture_boundary_steps=1,fixture_draft_at=1,fixture_budget_prefix=False,paired_task_seed=0,compiler=False,python_only=False,environment='',python_optimization=0)
    core=adapter.import_backend();core.configure_runtime(runtime,args);core.Fixture=scripted_handler(core.Fixture,script);core.make_prompt=lambda p:(p/'TASK.md').read_text()
    input_pins=dict(trial=a.trial,primary_result_sha256=sha(trial/'result.json'),primary_lock_sha256=sha(lock),source_sha256=hashlib.sha256(source).hexdigest(),runtime_sha256=sha(runtime_path),worker_script_sha256=sha(packet/'WORKER_SCRIPT.py'),audit_sha256=sha(packet/'IndependentAudit.lean'),backend_sha256=sha(BACKEND),review_controller_sha256=sha(Path(__file__)),common_final_runtime=str(runtime_path),scope='SUPPLEMENTAL_ONLY_ZERO_INFERENCE')
    save(a.out.parent/(a.out.name+'.INPUTS.json'),input_pins)
    asyncio.run(core.main(args))
    need(sha(lock)==input_pins['primary_lock_sha256'] and sha(trial/'result.json')==input_pins['primary_result_sha256'],'Primary evidence changed during review')
    for row in files:need(sha(trial/'submission'/row['path'])==row['sha256'],'Frozen payload changed during review')
    print('INDEPENDENT_REVIEW_FINISHED',a.trial,flush=True)
if __name__=='__main__':main()
