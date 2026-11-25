"""Fresh native study client using the existing restricted executor only.

No model credentials are read by this code or mounted into the worker. Login is
used by the native trusted controller from a temporary external private profile.
"""
from pathlib import Path
import argparse,asyncio,datetime,hashlib,http.server,json,os,re,shlex,shutil,tempfile,threading,time
from existing_executor_adapter import ExistingExecutorAdapter

C=Path(__file__).resolve().parents[1];V=C.parent
MODEL='gpt-6.1-sol'
BASE='You are a mathematical research agent. Follow the assigned task and its common resource and premise policy. Use only the provided offline materials. Do not delegate or request outside information.'
DEVELOPER='Use only the assigned offline executor and packet. No agent, human-input, goal, clock, MCP, connector, browser or network capability is authorized. Use non-login /bin/bash and /usr/bin/python3.10. Do not provide private reasoning transcripts. The complete packet text is also supplied below without editing its mathematics.'

def digest(data):return hashlib.sha256(data).hexdigest()
def make_prompt(packet):
    text=(V/'WORKER_PROMPT.txt').read_text();sections=[]
    for p in sorted(packet.iterdir()):
        if not p.is_file() or p.is_symlink():raise ValueError('packet must contain regular flat files')
        if p.name not in {'LICENSE.txt','VISIBLE_MANIFEST.json'}:
            sections.append('\n\n===== EXACT FILE /task/'+p.name+' =====\n'+p.read_text()+'\n===== END FILE =====')
    return text+''.join(sections)

def sanitize_public(value):
    if isinstance(value,dict):
        kind=value.get('type')
        if isinstance(kind,str) and kind.lower().startswith('reasoning'):
            return {'type':kind,'private_body_redacted':True}
        return {k:sanitize_public(v) for k,v in value.items()}
    if isinstance(value,list):return [sanitize_public(v) for v in value]
    return value

def boundary_fault(obj,root_thread_id):
    params=obj.get('params',{});item=params.get('item',{})
    if item.get('type')=='subAgentActivity' or obj.get('method')=='subAgentActivity' or 'subagent' in obj.get('method','').lower():
        return 'UNAPPROVED_DESCENDANT_QUARANTINE'
    if root_thread_id is not None:
        observed=params.get('threadId')
        if observed is None and obj.get('method')=='thread/started':observed=params.get('thread',{}).get('id')
        if observed is not None and observed!=root_thread_id:return 'FOREIGN_THREAD_QUARANTINE'
    return None

class Fixture(http.server.BaseHTTPRequestHandler):
    def do_POST(self):
        data=json.loads(self.rfile.read(int(self.headers['Content-Length'])));self.server.requests.append(data)
        n=len(self.server.requests)
        if n==getattr(self.server,'draft_at',1):
            script='import os,json,hashlib;os.makedirs("/work/submission",exist_ok=True);b=b"NEUTRAL_FIXTURE_NOT_A_MATHEMATICAL_CANDIDATE\\n";open("/work/submission/canary.txt","wb").write(b);json.dump({"files":[{"path":"canary.txt","sha256":hashlib.sha256(b).hexdigest()}]},open("/work/submission/LOCK.json","w"));print(json.dumps({"task_bytes":len(open("/task/task.md","rb").read()),"host_absent":not os.path.exists("/ryu/hyunsik/playground/independence/codex/ivy/memory"),"controller_canary_absent":not os.path.exists("host-only-canary.txt"),"auth_absent":not os.path.exists("/home/worker/.codex/auth.json"),"pid_namespace":os.readlink("/proc/self/ns/pid"),"net_namespace":os.readlink("/proc/self/ns/net"),"genericLean_available":os.path.isfile("/opt/lean/bin/lean"),"cache_probe":"neutral"}))'
            script=script.replace('canary.txt',getattr(self.server,'artifact_name','canary.txt'))
            code='text({fresh_cache:load("study_cache")===undefined});text(await tools.exec_command('+json.dumps({'cmd':'/usr/bin/python3.10 -I -c '+shlex.quote(script),'shell':'/bin/bash','login':False,'yield_time_ms':1000,'max_output_tokens':1000})+'));'
            item={'id':'ctc1','type':'custom_tool_call','call_id':'fixture1','name':'exec','namespace':'functions','input':code}
        elif n<=getattr(self.server,'boundary_steps',1):
            item={'id':'neutral'+str(n),'type':'custom_tool_call','call_id':'neutral'+str(n),'name':'exec','namespace':'functions','input':'text({neutral_budget_fixture:true});'}
        else:item={'id':'final','type':'message','role':'assistant','status':'completed','content':[{'type':'output_text','text':'NEUTRAL_CONTROLLER_FIXTURE_COMPLETE','annotations':[]}]}
        usage={'input_tokens':7,'output_tokens':3,'total_tokens':10,'output_tokens_details':{'reasoning_tokens':1}}
        response={'id':'fixture'+str(n),'object':'response','created_at':int(time.time()),'model':data['model'],'status':'completed','output':[item],'usage':usage}
        events=[{'type':'response.created','response':{**response,'status':'in_progress','output':[]}},{'type':'response.output_item.added','output_index':0,'item':item},{'type':'response.output_item.done','output_index':0,'item':item},{'type':'response.completed','response':response}]
        payload=''.join('event: '+e['type']+'\ndata: '+json.dumps(e)+'\n\n' for e in events).encode()
        if getattr(self.server,'boundary_steps',1)>1:time.sleep(.3)
        self.send_response(200);self.send_header('Content-Type','text/event-stream');self.send_header('Content-Length',str(len(payload)));self.end_headers();self.wfile.write(payload)
    def log_message(self,*args):pass

async def main(args):
    out=Path(args.out).resolve();packet=Path(args.packet).resolve()
    if out.exists():raise RuntimeError('session directory exists; never overwrite a run')
    out.mkdir(parents=True);private=Path(tempfile.mkdtemp(prefix='ieantn-study-controller-'));private.chmod(0o700)
    state=private/'state';state.mkdir(mode=0o700);cwd=private/'cwd';cwd.mkdir(mode=0o700)
    (cwd/'host-only-canary.txt').write_text('HOST_ONLY_NOT_WORKER\n')
    prompt=make_prompt(packet);(out/'worker_prompt.txt').write_text(prompt)
    adapter=ExistingExecutorAdapter(out/'executor',packet,working_directory=str(cwd),operation_limit=args.operations);url=await adapter.start()
    server=None
    config=(C/'controller-effective-off.toml').read_text().replace('shell_tool = false','shell_tool = true').replace('code_mode_host = false','code_mode_host = true').replace('hooks = false','hooks = true').replace('max_concurrent_threads_per_session = 0','max_concurrent_threads_per_session = 1\nmax_depth = 0')
    config=config.replace('workspace_dependencies = false','workspace_dependencies = false\nsubagent_thread_environments = true')
    config='allow_login_shell = false\nhide_agent_reasoning = true\nshow_raw_agent_reasoning = false\n'+config+'\n[skills]\ninclude_instructions = false\n[skills.bundled]\nenabled = false\n[analytics]\nenabled = false\n[shell_environment_policy]\ninherit = "none"\n[shell_environment_policy.set]\nPATH = "/bin:/usr/bin"\nHOME = "/home/worker"\nLANG = "C"\nLC_ALL = "C"\nCODEX_HOME = "/home/worker/.codex"\n'
    if args.fixture:
        server=http.server.ThreadingHTTPServer(('127.0.0.1',0),Fixture);server.requests=[];server.boundary_steps=getattr(args,'fixture_boundary_steps',1);server.draft_at=getattr(args,'fixture_draft_at',1);server.artifact_name=getattr(args,'fixture_artifact_name','canary.txt');threading.Thread(target=server.serve_forever,daemon=True).start()
        config='model_provider = "preflight_capture"\n'+config+'\n[model_providers.preflight_capture]\nname = "No-auth final study configuration fixture"\nbase_url = "http://127.0.0.1:'+str(server.server_port)+'/v1"\nwire_api = "responses"\nrequires_openai_auth = false\nrequest_max_retries = 0\nstream_max_retries = 0\nsupports_websockets = false\n'
    else:
        auth=Path(os.environ.get('CODEX_HOME',str(Path.home()/'.codex')))/'auth.json'
        if not auth.is_file():raise RuntimeError('existing native auth unavailable')
        (state/'auth.json').symlink_to(auth)
    policy=(C/'research/deny_unapproved_tool.py').read_text()
    definition={'description':'Externally reviewed offline runtime restriction; no task mathematics.','hooks':{'PreToolUse':[{'matcher':'.*','hooks':[{'type':'command','command':'/usr/bin/python3.10 -I -B -c '+shlex.quote(policy),'timeout':30}]}]}}
    data=(json.dumps(definition,indent=2)+'\n').encode();trust=json.loads((C/'evidence/native-hook-trust/receipt.json').read_text())
    if digest(data)!=trust['definition_sha256']:raise RuntimeError('native reviewed hook definition changed')
    trusted={r['trusted_hash'] for r in trust['native_state_entries'].values()}
    if len(trusted)!=1:raise RuntimeError('ambiguous native trust')
    trusted_hash=next(iter(trusted));(state/'hooks.json').write_bytes(data)
    config+='\n[hooks.state.'+json.dumps(str(state/'hooks.json')+':pre_tool_use:0:0')+']\ntrusted_hash = '+json.dumps(trusted_hash)+'\n'
    (state/'config.toml').write_text(config);(out/'controller-config.toml').write_text(config)
    env=os.environ.copy();env.update(CODEX_HOME=str(state),TOKIO_WORKER_THREADS='2',RAYON_NUM_THREADS='2',MALLOC_ARENA_MAX='2')
    proc=await asyncio.create_subprocess_exec('codex','app-server','--strict-config','--listen','stdio://',cwd=cwd,env=env,stdin=asyncio.subprocess.PIPE,stdout=asyncio.subprocess.PIPE,stderr=asyncio.subprocess.PIPE,limit=4*1024**2)
    responses={};events=[];serial=0;usage=[];foreign_usage=[];milestones=[];stop=None;started=time.monotonic();tid=None;turnid=None
    journal=(out/'events.jsonl').open('a');stderr_task=asyncio.create_task(proc.stderr.read())
    record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'mode':'NOAUTH_FINAL_CONFIG_FIXTURE' if args.fixture else args.phase,'task_packet':str(packet),'prompt_sha256':digest(prompt.encode()),'model':MODEL,'effort':'high','service_tier':'default','source_sha256':digest(Path(__file__).read_bytes()),'credentials_mounted_in_worker':False,'private_reasoning_collected':False,'limits':vars(args)}
    async def reader():
        nonlocal stop
        while line:=await proc.stdout.readline():
            obj=json.loads(line)
            if 'id' in obj and ('result' in obj or 'error' in obj):responses[obj['id']]=obj;continue
            method=obj.get('method','');item=obj.get('params',{}).get('item',{})
            if method.startswith('account/') or 'reasoning' in method.lower() or item.get('type')=='reasoning':continue
            obj=sanitize_public(obj);events.append(obj);journal.write(json.dumps(obj)+'\n');journal.flush()
            fault=boundary_fault(obj,tid)
            if fault:stop=fault
            if method=='thread/tokenUsage/updated':
                u=obj['params']['tokenUsage']
                if obj['params'].get('threadId')!=tid:
                    foreign_usage.append({'thread_id':obj['params'].get('threadId'),'tokenUsage':u});stop='FOREIGN_THREAD_QUARANTINE';continue
                usage.append(u)
                if u['total']['outputTokens']>args.output:stop='GENERATED_OUTPUT_ADMISSION_CEILING'
                if len(usage)>=args.responses:stop='COMPLETED_USAGE_BOUNDARY_CEILING'
            if method=='hook/completed':
                run=obj.get('params',{}).get('run',{})
                if run.get('status') not in {'completed','blocked'}:stop='HOOK_FAULT_QUARANTINE'
            if 'id' in obj and 'method' in obj:stop='UNAPPROVED_CONTROLLER_CALLBACK_QUARANTINE'
    read_task=asyncio.create_task(reader())
    async def rpc(method,params,timeout=30):
        nonlocal serial
        serial+=1;key=serial;proc.stdin.write((json.dumps({'id':key,'method':method,'params':params})+'\n').encode());await proc.stdin.drain()
        for _ in range(timeout*10):
            if key in responses:return responses.pop(key)
            if proc.returncode is not None:raise RuntimeError('native controller exited')
            await asyncio.sleep(.1)
        raise TimeoutError(method)
    try:
        record['initialize']=await rpc('initialize',{'clientInfo':{'name':'ieantn-qsl-study-controller','version':'1'},'capabilities':{'experimentalApi':True}})
        proc.stdin.write(b'{"method":"initialized","params":{}}\n');await proc.stdin.drain()
        await rpc('environment/add',{'environmentId':'assigned-offline-runtime','execServerUrl':url,'connectTimeoutMs':3000});await asyncio.sleep(.4)
        record['environment_status']=await rpc('environment/status',{'environmentId':'assigned-offline-runtime'})
        if record['environment_status'].get('result',{}).get('status')!='ready':raise RuntimeError('restricted executor not ready')
        catalog=await rpc('model/list',{});models=catalog.get('result',{}).get('data',[]);selected=next((m for m in models if m['id']==MODEL),None)
        if selected is None:raise RuntimeError('fixed model not offered in current native catalog')
        record['model_catalog_selection']=selected
        environment=[{'environmentId':'assigned-offline-runtime','cwd':str(cwd),'runtimeWorkspaceRoots':[str(cwd),'/work']}]
        thread=await rpc('thread/start',{'model':MODEL,'allowProviderModelFallback':False,'serviceTier':'default','cwd':str(cwd),'ephemeral':True,'environments':environment,'sandbox':'danger-full-access','approvalPolicy':'never','baseInstructions':BASE,'developerInstructions':DEVELOPER,'config':{'web_search':'disabled'}})
        record['thread_start']=thread;tid=thread.get('result',{}).get('thread',{}).get('id')
        if not tid:raise RuntimeError('fresh thread not created')
        record['hooks']=await rpc('hooks/list',{'threadId':tid});hooks=[h for r in record['hooks'].get('result',{}).get('data',[]) for h in r.get('hooks',[])]
        if len(hooks)!=1 or hooks[0].get('currentHash')!=trusted_hash or hooks[0].get('trustStatus')!='trusted':raise RuntimeError('exact hook not trusted')
        record['mcp_registry']=await rpc('mcpServerStatus/list',{'threadId':tid,'detail':'toolsAndAuthOnly'})
        if record['mcp_registry'].get('result',{}).get('data')!=[]:raise RuntimeError('MCP registry is not empty')
        if args.fixture_hook_fault:
            if not args.fixture:raise RuntimeError('fault injection is fixture-only')
            shutil.rmtree(cwd)
        turn=await rpc('turn/start',{'threadId':tid,'input':[{'type':'text','text':prompt}],'environments':environment,'effort':'high','summary':'none','serviceTierForTurn':'default'})
        record['turn_start']=turn;turnid=turn.get('result',{}).get('turn',{}).get('id')
        while time.monotonic()-started<args.wall-8:
            if adapter.budget_exceeded:stop='RUNTIME_OPERATION_BUDGET'
            if stop:break
            if any(e.get('method')=='turn/completed' and e.get('params',{}).get('threadId')==tid for e in events):break
            if proc.returncode is not None:stop='CONTROLLER_EXIT';break
            if usage:
                used=usage[-1]['total']['outputTokens']
                for fraction in [.5,.75]:
                    if used>=args.output*fraction and not any(m['fraction']==fraction for m in milestones):
                        snapshot=await adapter.snapshot_submission(out/('milestone-'+str(int(fraction*100))))
                        milestones.append({'fraction':fraction,'observed_generated_tokens':used,'elapsed_seconds':time.monotonic()-started,'mode':'PASSIVE_READONLY_SNAPSHOT_NO_MODEL_FEEDBACK','snapshot':snapshot})
            await asyncio.sleep(.1)
        else:stop='WALL_BUDGET_PRETEARDOWN'
        if stop and tid and turnid:
            try:record['interrupt']=await rpc('turn/interrupt',{'threadId':tid,'turnId':turnid},timeout=2)
            except Exception as e:record['interrupt_error']=str(e)
        # Seal the original candidate before any independent proof engineering.
        record['worker_quiescence'] = await adapter.freeze_work()
        exported=out/'submission';exported.mkdir();files=[]
        try:
            lock=await adapter.read_export('/work/submission/LOCK.json');(exported/'LOCK.json').write_bytes(lock);manifest=json.loads(lock)
            if not isinstance(manifest,dict) or set(manifest)!={'files'} or not isinstance(manifest['files'],list) or len(manifest['files'])>16:raise ValueError('invalid lock schema')
            seen=set()
            for row in manifest['files']:
                if not isinstance(row,dict) or set(row)!={'path','sha256'} or not isinstance(row['path'],str) or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,127}',row['path']) or row['path']=='LOCK.json' or row['path'] in seen:raise ValueError('invalid/duplicate artifact name')
                seen.add(row['path']);body=await adapter.read_export('/work/submission/'+row['path']);(exported/row['path']).write_bytes(body)
                if digest(body)!=row['sha256']:raise ValueError('artifact hash mismatch')
                files.append({'path':row['path'],'sha256':digest(body),'bytes':len(body)})
            if await adapter.read_export('/work/submission/LOCK.json')!=lock:raise ValueError('lock changed during export')
            record['artifact_export']={'consistent':True,'lock_sha256':digest(lock),'files':files}
        except Exception as e:record['artifact_export']={'consistent':False,'error':str(e),'partial_files':files}
        if not record['artifact_export']['consistent']:
            record['deadline_snapshot'] = await adapter.snapshot_submission(out/'deadline-sealed')
            record['deadline_snapshot']['controller_locked_incomplete_candidate'] = True
        if args.fixture:
            record['submission_listing_probe']=await adapter.list_submission()
            record['submission_metadata_probe']=await adapter.export_metadata('canary.txt')
        completed=[e.get('params',{}).get('turn',{}) for e in events if e.get('method')=='turn/completed' and e.get('params',{}).get('threadId')==tid]
        record['turn_completion_statuses']=[t.get('status') for t in completed]
        record['mechanical_submission_gate_passed']=not stop and any(t.get('status')=='completed' for t in completed) and record['artifact_export']['consistent'] and bool(usage) and usage[-1]['total']['outputTokens']<=args.output
    except Exception as e:record['infrastructure_error']={'type':type(e).__name__,'message':str(e)}
    finally:
        record.update(stop_reason=stop,usage=usage,elapsed_seconds=time.monotonic()-started,operation_count=adapter.operation_count,operation_budget_exceeded=adapter.budget_exceeded,executor_rpc_counts=dict(adapter.method_counts),controller_cgroup=Path('/proc/self/cgroup').read_text())
        if server:
            (out/'INITIAL_MODEL_CONTEXT.json').write_text(json.dumps(server.requests[0],indent=2)+'\n' if server.requests else 'null\n');record['fixture_requests_count']=len(server.requests)
            (out/'fixture_requests.json').write_text(json.dumps(server.requests,indent=2)+'\n')
            if server.requests:record['fixture_reasoning_setting']=server.requests[0].get('reasoning')
            server.shutdown()
        if proc.returncode is None:proc.terminate()
        try:await asyncio.wait_for(proc.wait(),2)
        except asyncio.TimeoutError:proc.kill();await proc.wait()
        await read_task;journal.close();stderr=await stderr_task
        # Recheck after all trailing public usage/events have drained.
        if adapter.budget_exceeded:stop='RUNTIME_OPERATION_BUDGET'
        if usage and usage[-1]['total']['outputTokens']>args.output:stop='GENERATED_OUTPUT_ADMISSION_CEILING'
        record['stop_reason']=stop;record['usage']=usage;record['foreign_usage']=foreign_usage;record['budget_milestones']=milestones
        record['mechanical_submission_gate_passed']=bool(record.get('mechanical_submission_gate_passed')) and stop is None
        record['discovery_admissible_for_evaluation']=record['mechanical_submission_gate_passed'] and not args.fixture
        record['native_stderr_metadata']={'bytes':len(stderr),'sha256':digest(stderr)}
        await adapter.close();shutil.rmtree(private);record['private_profile_removed']=not private.exists()
        temp=out/'result.tmp';temp.write_text(json.dumps(sanitize_public(record),indent=2)+'\n');temp.replace(out/'result.json')
        print(json.dumps({k:record.get(k) for k in ['mode','stop_reason','infrastructure_error','elapsed_seconds','operation_count','artifact_export','discovery_admissible_for_evaluation']}))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--packet',required=True);p.add_argument('--out',required=True);p.add_argument('--phase',choices=['PILOT','EXPLORATORY_MAIN','LIVE_INFRA_PREFLIGHT'],default='PILOT');p.add_argument('--fixture',action='store_true');p.add_argument('--fixture-hook-fault',action='store_true');p.add_argument('--fixture-boundary-steps',type=int,default=1);p.add_argument('--fixture-draft-at',type=int,default=1);p.add_argument('--fixture-artifact-name',default='canary.txt');p.add_argument('--wall',type=int,default=600);p.add_argument('--output',type=int,default=12000);p.add_argument('--operations',type=int,default=64);p.add_argument('--responses',type=int,default=60)
    asyncio.run(main(p.parse_args()))
