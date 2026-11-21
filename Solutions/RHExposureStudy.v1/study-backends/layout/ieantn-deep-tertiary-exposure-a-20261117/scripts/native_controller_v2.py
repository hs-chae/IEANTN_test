# Copyright (c) 2026 IEANTN contributors. Apache-2.0.
# Additive adaptation of pinned existing controller; original source SHA256 068bd4b7df8bd215d498f1e9b881f6cceddbb704c84e9ec965dd2b31b15e8df8
"""Fresh native study client using the existing restricted executor only.

No model credentials are read by this code or mounted into the worker. Login is
used by the native trusted controller from a temporary external private profile.
"""
from pathlib import Path
import argparse,asyncio,datetime,hashlib,http.server,json,os,re,shlex,shutil,tempfile,threading,time
import sys
_VENDOR=Path(__file__).resolve().parents[2]/"ieantn-exposure-maximal-20261109/sources/controller/continuation-20261108/research"
sys.path.insert(0,str(_VENDOR))
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
        if n==getattr(self.server,'draft_at',1) or (getattr(self.server,'budget_prefix_fixture',False) and n in (4,6)):
            script='import os,json,hashlib;os.makedirs("/work/submission",exist_ok=True);b=b"NEUTRAL_FIXTURE_NOT_A_MATHEMATICAL_CANDIDATE\\n";open("/work/submission/canary.txt","wb").write(b);json.dump({"files":[{"path":"canary.txt","sha256":hashlib.sha256(b).hexdigest()}]},open("/work/submission/LOCK.json","w"));print(json.dumps({"task_bytes":len(open("/task/task.md"if os.path.isfile("/task/task.md")else"/task/TASK.md","rb").read()),"host_absent":not os.path.exists("/ryu/hyunsik/playground/independence/codex/ivy/memory"),"controller_canary_absent":not os.path.exists("host-only-canary.txt"),"auth_absent":not os.path.exists("/home/worker/.codex/auth.json"),"pid_namespace":os.readlink("/proc/self/ns/pid"),"net_namespace":os.readlink("/proc/self/ns/net"),"genericLean_available":os.path.isfile("/opt/lean/bin/lean"),"cache_probe":"neutral"}))'
            script=script.replace('canary.txt',getattr(self.server,'artifact_name','canary.txt'))
            code='text({fresh_cache:load("study_cache")===undefined});text(await tools.exec_command('+json.dumps({'cmd':'/usr/bin/python3.10 -I -c '+shlex.quote(script),'shell':'/bin/bash','login':False,'yield_time_ms':1000,'max_output_tokens':1000})+'));'
            offered={tool.get('name'):tool.get('type')for tool in data.get('tools',[])}
            if offered.get('exec_command')=='function':
                item={'id':'fc1','type':'function_call','call_id':'fixture1','name':'exec_command','arguments':json.dumps({'cmd':'/usr/bin/python3.10 -I -c '+shlex.quote(script),'shell':'/bin/bash','login':False,'yield_time_ms':1000,'max_output_tokens':1000})}
            else:
                item={'id':'ctc1','type':'custom_tool_call','call_id':'fixture1','name':'exec','namespace':'functions','input':code}
        elif n==2 and any(tool.get('name')=='get_goal' and tool.get('type')=='function'for tool in data.get('tools',[])):
            item={'id':'denied1','type':'function_call','call_id':'fixture-denied','name':'get_goal','arguments':'{}'}
        elif n<=getattr(self.server,'boundary_steps',1):
            offered={tool.get('name'):tool.get('type')for tool in data.get('tools',[])}
            if offered.get('exec_command')=='function':
                item={'id':'neutral'+str(n),'type':'function_call','call_id':'neutral'+str(n),'name':'exec_command','arguments':json.dumps({'cmd':'/usr/bin/python3.10 -I -c \"print(123)\"','shell':'/bin/bash','login':False,'yield_time_ms':1000,'max_output_tokens':1000})}
            else:
                item={'id':'neutral'+str(n),'type':'custom_tool_call','call_id':'neutral'+str(n),'name':'exec','namespace':'functions','input':'text({neutral_budget_fixture:true});'}
        elif False:
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
    if args.per_response_max_output_tokens is not None:
        config='model_max_output_tokens = '+str(args.per_response_max_output_tokens)+'\n'+config
    if args.fixture:
        server=http.server.ThreadingHTTPServer(('127.0.0.1',0),Fixture);server.requests=[];server.boundary_steps=getattr(args,'fixture_boundary_steps',1);server.draft_at=getattr(args,'fixture_draft_at',1);server.artifact_name=getattr(args,'fixture_artifact_name','canary.txt');server.budget_prefix_fixture=getattr(args,'fixture_budget_prefix',False);threading.Thread(target=server.serve_forever,daemon=True).start()
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
    responses={};events=[];serial=0;usage=[];foreign_usage=[];milestones=[];stop=None;started=time.monotonic();tid=None;turnid=None;continued_turns=0;budget_notices=[];budget_notice_fractions=[.25,.5,.75,.9]
    adapter.budget_started=started
    journal=(out/'events.jsonl').open('a');stderr_task=asyncio.create_task(proc.stderr.read())
    record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'mode':'NOAUTH_FINAL_CONFIG_FIXTURE' if args.fixture else args.phase,'task_packet':str(packet),'prompt_sha256':digest(prompt.encode()),'model':MODEL,'effort':args.effort,'service_tier':'default','source_sha256':digest(Path(__file__).read_bytes()),'credentials_mounted_in_worker':False,'private_reasoning_collected':False,'limits':{k:str(v)if isinstance(v,Path)else v for k,v in vars(args).items()}}
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
                usage_fault=adapter.observe_usage(u)
                if usage_fault:stop=usage_fault
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
        record['model_catalog_observation']={'fixture_provider':args.fixture,'offered_ids':[row.get('id')for row in models]}
        if selected is None and not args.fixture:raise RuntimeError('fixed model not offered in current native catalog')
        record['model_catalog_selection']=selected if selected is not None else {'id':MODEL,'fixture_only_requested_alias':True,'not_live_provider_availability':True}
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
        turn=await rpc('turn/start',{'threadId':tid,'input':[{'type':'text','text':prompt}],'environments':environment,'effort':args.effort,'summary':'none','serviceTierForTurn':'default'})
        record['turn_start']=turn;turnid=turn.get('result',{}).get('turn',{}).get('id')
        while time.monotonic()-started<args.wall-8:
            if adapter.budget_exceeded:stop='RUNTIME_OPERATION_BUDGET'
            if stop:break
            used=usage[-1]['total']['outputTokens']if usage else 0
            for fraction in [.25,.5]:
                elapsed=time.monotonic()-started
                if (used>=args.output*fraction or elapsed>=args.wall*fraction) and not any(m['fraction']==fraction for m in milestones):
                    snapshot=await adapter.snapshot_submission(out/('milestone-'+str(int(fraction*100))))
                    milestones.append({'fraction':fraction,'observed_generated_tokens':used,'elapsed_seconds':time.monotonic()-started,'trigger_basis':'tokens_or_active_wall_first_observed_boundary','mode':'PASSIVE_READONLY_SNAPSHOT_NO_MODEL_FEEDBACK','snapshot':snapshot})
            await adapter.capture_timely_lock('PASSIVE_ACCOUNTED_USAGE_BOUNDARY')
            completions=[e for e in events if e.get('method')=='turn/completed' and e.get('params',{}).get('threadId')==tid]
            if len(completions)>continued_turns:
                last=completions[-1].get('params',{}).get('turn',{})
                used=usage[-1]['total']['outputTokens'] if usage else 0
                if last.get('status')!='completed' or used>=args.output*.95 or args.fixture:
                    break
                continued_turns=len(completions)
                follow=await rpc('turn/start',{'threadId':tid,'input':[{'type':'text','text':'Continue independent mathematical research within the unchanged packet and original total budget. Preserve existing results, investigate stronger conclusions or other admissible applications, document failures, and update the final artifact lock. No evaluation feedback is supplied.'}],'environments':environment,'effort':args.effort,'summary':'none','serviceTierForTurn':'default'})
                turnid=follow.get('result',{}).get('turn',{}).get('id')
                require(bool(turnid),'neutral continuation did not start')
                record.setdefault('neutral_continuations',[]).append({'prior_completed_turns':continued_turns,'observed_generated_tokens':used,'elapsed_seconds':time.monotonic()-started})
            if proc.returncode is not None:stop='CONTROLLER_EXIT';break
            await asyncio.sleep(.1)
        else:stop='WALL_BUDGET_PRETEARDOWN'
        if stop and tid and turnid:
            try:record['interrupt']=await rpc('turn/interrupt',{'threadId':tid,'turnId':turnid},timeout=2)
            except Exception as e:record['interrupt_error']=str(e)
        # Seal the original candidate before any independent proof engineering.
        record['candidate_frozen_elapsed_seconds'] = time.monotonic()-started
        record['worker_quiescence'] = await adapter.freeze_work()
        await adapter.capture_timely_lock('FINAL_QUIESCED_IF_WITHIN_ADMISSION')
        final_snapshot=await adapter.snapshot_submission(out/'milestone-100')
        milestones.append({'fraction':1.0,'observed_generated_tokens':usage[-1]['total']['outputTokens']if usage else None,'elapsed_seconds':time.monotonic()-started,'mode':'FINAL_QUIESCED_SNAPSHOT_NO_MODEL_FEEDBACK','snapshot':final_snapshot})
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
        allowed_stops={None,'WALL_BUDGET_PRETEARDOWN','COMPLETED_USAGE_BOUNDARY_CEILING'}
        require(digest(Path(__file__).read_bytes())==record['source_sha256'],'controller source changed during execution')
        record['original_valid_submission_for_evaluation']=bool(
            not args.fixture and not record.get('infrastructure_error') and
            stop in allowed_stops and record.get('artifact_export',{}).get('consistent') and usage and
            usage[-1]['total']['outputTokens']<=args.output and len(usage)<=args.responses and
            adapter.operation_count<=args.operations and not adapter.budget_exceeded and not foreign_usage and
            record.get('candidate_frozen_elapsed_seconds',args.wall+1)<=args.wall)
        record['budget_qualification']='Mechanical early-completion gate and within-budget locked mathematical submission are distinct; an over-token final is never admitted.'
        record['budget_notices']=adapter.budget_notices
        record['budget_notice_delivery']='LABELED_CONTROLLER_STDERR_BEFORE_ORDINARY_TOOL_EXIT_V1'
        record['raw_program_output_preservation']='executor/transport.json retains every original program output notification without controller notice/sequence alterations; notice ledger is separate.'
        record['timely_locked_execution_prefixes']=adapter.timely_checkpoints
        record['timely_prefix_skip_counts']=adapter.timely_checkpoint_skips
        record['usage_ordering_witnesses']=adapter.usage_ordering_witnesses
        record['within_budget_locked_execution_prefix_available']=not args.fixture and bool(adapter.timely_checkpoints) and not foreign_usage and not record.get('infrastructure_error') and not(stop and 'QUARANTINE'in stop)
        record['over_budget_final_is_admissible']=False
        record['per_response_output_cap_request']=args.per_response_max_output_tokens
        record['per_response_cap_support']='NOT_ESTABLISHED; inspect no-auth wire evidence before using or claiming a physical cap.'
        record['native_stderr_metadata']={'bytes':len(stderr),'sha256':digest(stderr)}
        if args.fixture:(out/'fixture-native.stderr').write_bytes(stderr)
        await adapter.close();record['raw_program_transport_sha256']=file_sha(out/'executor/transport.json');shutil.rmtree(private);record['private_profile_removed']=not private.exists()
        temp=out/'result.tmp';temp.write_text(json.dumps(sanitize_public(record),indent=2)+'\n');temp.replace(out/'result.json')
        print(json.dumps({k:record.get(k) for k in ['mode','stop_reason','infrastructure_error','elapsed_seconds','operation_count','artifact_export','discovery_admissible_for_evaluation']}))


# Additive study adapter. This file never invokes an inference call on import.
import importlib.util
import resource
import stat
import sys
from types import SimpleNamespace

STUDY = Path(__file__).resolve().parents[1]
WORKSPACE = STUDY.parent
OLD = WORKSPACE / 'ieantn-exposure-maximal-20261109'
VENDOR = OLD / 'sources/controller/continuation-20261108'
SOURCE_PINS = {'ieantn-exposure-maximal-20261109/scripts/research_session.py': '173d57f73e8e97642b694c8554f3854a87b8cb9d6cd6a4aa6383b59407575571', 'ieantn-qrh-pv-synergy-20261114/exposure/scripts/native_session_core_current_account.py': '068bd4b7df8bd215d498f1e9b881f6cceddbb704c84e9ec965dd2b31b15e8df8', 'ieantn-exposure-maximal-20261109/sources/controller/continuation-20261108/research/existing_executor_adapter.py': '5c0fcde16bceaac67605b25f91c8f926ac2c1280014d5ad2093173b29d7ca8f7', 'ieantn-exposure-maximal-20261109/sources/ieantn-protected-workspace-20260925-NrAB5O/app/IEANTN/web/server/agent-sandbox.py': '79c1428403befb974bf4daeada0c130addd60ff952cef4b62ca74ef18ae6d79d', 'ieantn-exposure-maximal-20261109/sources/controller/evidence/execution-preflight/spec-v2.json': '64f397aba3875a331f05ed36a09f938654053137774f334a48a035e8e287abf8', 'ieantn-exposure-maximal-20261109/sources/controller/continuation-20261108/controller-effective-off.toml': '1dabb72e46b5470d7d71186090291e647b46c2a062cecfcdc184f8ec8963241f', 'ieantn-exposure-maximal-20261109/sources/controller/continuation-20261108/research/deny_unapproved_tool.py': 'd4c0e1bc08e6eab315102a49c2c2e3ad3cfa73af126e7c9495e30883cc045ad5', 'ieantn-exposure-maximal-20261109/sources/controller/continuation-20261108/evidence/native-hook-trust/receipt.json': '118b112ed027c03a174f229f5ae588deab53dee8595bdf48f282f0b5f391dbeb'}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def strict_json(path):
    def pairs(rows):
        out = {}
        for key, value in rows:
            require(key not in out, 'duplicate JSON key')
            out[key] = value
        return out
    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs,
        parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))

def file_sha(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as handle:
        for block in iter(lambda: handle.read(1024 ** 2), b''):
            value.update(block)
    return value.hexdigest()

def check_pin(row):
    path = Path(row['path'])
    if not path.is_absolute():
        path = WORKSPACE / path
    require(path.is_file() and not path.is_symlink(), 'pinned regular file required: ' + str(path))
    require(file_sha(path) == row['sha256'], 'pinned file changed: ' + str(path))
    return path

def check_sources():
    for path, expected in SOURCE_PINS.items():
        check_pin({'path': path, 'sha256': expected})
    generic = strict_json(check_pin({'path': '/ryu/hyunsik/playground/independence/codex/ivy/ieantn-deep-tertiary-exposure-a-20261117/evidence/runner_python_package_trees.json', 'sha256': '5202f92cb9a0b0a98233735eaab11bc78308190d7428d12074035ff6b88b51ac'}))
    for package in generic['packages']:
        require(package['files'] == tree_inventory(package['copy']), 'generic Python package source changed')

def tree_inventory(root):
    root = Path(root).resolve()
    require(root.is_dir(), 'tree directory absent')
    rows = []
    for parent, dirs, files in os.walk(root, followlinks=False):
        for name in sorted(dirs + files):
            p = Path(parent) / name
            rel = p.relative_to(root).as_posix()
            require('.git' not in p.relative_to(root).parts, 'Git data is forbidden in an exposed tree')
            if p.is_symlink():
                target = os.readlink(p)
                require(p.resolve().is_relative_to(root), 'exposed symlink leaves its tree')
                rows.append({'path': rel, 'symlink': target})
            elif p.is_file():
                rows.append({'path': rel, 'bytes': p.stat().st_size, 'sha256': file_sha(p)})
            elif not p.is_dir():
                raise ValueError('nonregular exposed tree entry: ' + rel)
    return sorted(rows, key=lambda row: row['path'])

def check_tree(manifest_path, expected_root=None):
    manifest = strict_json(manifest_path)
    require(manifest.get('schema') == 'DEEP_TERTIARY_TREE_V1', 'tree manifest schema')
    root = Path(manifest['root'])
    require(root.is_absolute() and root.resolve() == root, 'canonical exposed tree root required')
    if expected_root is not None:
        require(root == Path(expected_root).resolve(), 'tree root does not match assigned path')
    require(manifest['files'] == tree_inventory(root), 'exposed tree differs from its exhaustive manifest')
    return root

def validate_runtime(runtime_path, packet_manifest_path):
    check_sources()
    packet = check_tree(packet_manifest_path)
    runtime = strict_json(runtime_path)
    require(runtime.get('schema') == 'DEEP_TERTIARY_RUNTIME_V1', 'runtime manifest schema')
    require(runtime.get('arm') in {'NL', 'PNT', 'IEANTN'}, 'unknown arm')
    require(isinstance(runtime.get('mounts'), list), 'runtime mounts list')
    seen = set()
    allowed = ('/opt/lean', '/evaldeps/', '/generic-source/', '/baseline/', '/corpus/', '/generic-python/')
    for mount in runtime['mounts']:
        target = mount['target']
        require(isinstance(target, str) and target.startswith('/') and os.path.normpath(target) == target,
                'canonical mount target required')
        require(target == '/opt/lean' or any(target.startswith(prefix) for prefix in allowed[1:]),
                'mount outside explicit runtime roots')
        require(target not in seen, 'duplicate runtime mount target')
        require(not any(target.startswith(x + '/') or x.startswith(target + '/') for x in seen),
                'overlapping runtime mount targets')
        seen.add(target)
        manifest = check_pin(mount['manifest'])
        check_tree(manifest, mount['source'])
        require(mount.get('role') in {'toolchain', 'generic', 'native', 'corpus'}, 'unknown runtime mount role')
        if runtime['arm'] == 'NL':
            require(mount['role'] != 'native', 'NL cannot expose native project material')
    lean_paths = runtime.get('lean_path', [])
    require(isinstance(lean_paths, list) and len(set(lean_paths)) == len(lean_paths), 'Lean path list')
    for value in lean_paths:
        require(value in seen or any(value.startswith(x + '/') for x in seen), 'Lean path outside mounted closure')
        require('..' not in Path(value).parts and os.path.normpath(value) == value, 'noncanonical Lean path')
    if runtime['arm'] in {'PNT', 'IEANTN'}:
        require('/opt/lean' in seen and lean_paths, 'native arm requires its working compiler and native closure')
        require(isinstance(runtime.get('required_imports'),list) and bool(runtime['required_imports']), 'native arm requires explicit working import canaries')
        require(all(isinstance(name,str) and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',name) for name in runtime['required_imports']), 'invalid native import canary')
        audit = strict_json(check_pin(runtime['native_closure_audit']))
        require(audit.get('status') == 'PASS_ALLOWED_NATIVE_CLOSURE_NO_HELDOUT_ANSWERS', 'native closure/leakage audit incomplete')
        require(audit.get('arm') == runtime['arm'], 'native audit arm mismatch')
        require(audit.get('runtime_mount_manifests') == [m['manifest']['sha256'] for m in runtime['mounts']],
                'native audit does not bind all mounted closure manifests')
    require(runtime.get('external_network') is False and runtime.get('host_tools') is False,
            'runtime must forbid external network and host tools')
    return packet, runtime

def check_scope(resources):
    cg = Path('/sys/fs/cgroup') / Path('/proc/self/cgroup').read_text().strip().split('::')[1].lstrip('/')
    require(cg.is_relative_to('/sys/fs/cgroup'), 'invalid cgroup')
    require((cg / 'memory.max').is_file(), 'actual bounded cgroup required for discovery')
    maximum = (cg / 'memory.max').read_text().strip()
    require(maximum != 'max' and int(maximum) <= resources['memory_gib'] * 1024 ** 3,
            'discovery cgroup memory cap absent or too high')
    require((cg / 'memory.swap.max').read_text().strip() == '0', 'discovery swap must be disabled')
    affinity = sorted(os.sched_getaffinity(0))
    require(0 < len(affinity) <= resources['cpus'], 'discovery CPU affinity exceeds the locked CPU count')
    quota_path = cg / 'cpu.max'
    quota_record = None
    if quota_path.is_file():
        quota, period = quota_path.read_text().split()
        require(quota != 'max' and int(quota) <= int(period) * resources['cpus'], 'discovery CPU quota too high')
        quota_record = {'quota': quota, 'period': period}
    return {'cgroup': str(cg), 'memory_max_bytes': int(maximum), 'swap_max_bytes': 0,
            'CPU_affinity': affinity, 'cpu_max': quota_record,
            'CPU_enforcement': 'fixed inherited affinity; cpu.max additionally checked where exposed'}

def validate_launch(args):
    packet, runtime = validate_runtime(args.runtime, args.packet_manifest)
    args.packet = str(packet)
    if args.fixture:
        return runtime
    require(args.lock is not None, 'no discovery inference without a reviewed execution lock')
    lock = strict_json(args.lock)
    require(lock.get('schema') == 'DEEP_TERTIARY_EXECUTION_LOCK_V1', 'execution lock schema')
    require(lock.get('phase') in {'PILOT', 'MAIN', 'ADDITIONAL'}, 'execution phase')
    require(lock.get('arm') == runtime['arm'], 'execution arm mismatch')
    require(lock.get('run_id') == Path(args.out).name, 'run id/output association mismatch')
    require(lock.get('phase') == args.phase, 'phase differs from its execution lock')
    require(check_pin(lock['packet_manifest']) == Path(args.packet_manifest).resolve(), 'assigned packet lock mismatch')
    require(check_pin(lock['runtime_manifest']) == Path(args.runtime).resolve(), 'assigned runtime lock mismatch')
    check_pin(lock['protocol'])
    for row in lock['source_pins']:
        check_pin(row)
    require(any(Path(row['path']).resolve() == Path(__file__).resolve() for row in lock['source_pins']),
            'controller source must itself be pinned by the execution lock')
    preflight = strict_json(check_pin(lock['preflight']))
    require(preflight.get('status') == 'PASS_EXACT_PACKET_RUNTIME_ACTUAL_OS_AND_MODEL_TOOL_ISOLATION',
            'exact OS and native tool preflight has not passed')
    require(preflight.get('runtime_manifest_sha256') == file_sha(args.runtime) and
            preflight.get('packet_manifest_sha256') == file_sha(args.packet_manifest),
            'preflight belongs to another packet/runtime')
    require(preflight.get('controller_sha256') == file_sha(__file__), 'preflight tested a different controller')
    require(lock.get('model') == args.model and lock.get('effort') == args.effort, 'common model settings mismatch')
    require(lock.get('provider') == 'existing_native_codex_account' and lock.get('paid_external_service') is False,
            'paid/external provider is not authorized by this execution lock')
    require(lock.get('checkpoint_fractions') == [0.25, 0.5, 1.0], 'required fixed checkpoint schedule')
    require(lock.get('budget_notice_fractions') == [0.25,0.5,0.75,0.9], 'required common neutral budget notices')
    require(lock.get('timely_lock_policy') == 'CONSISTENT_ACCOUNTED_EXECUTOR_PREFIX_FROM_50_PERCENT_V1','required accounted execution-prefix policy')
    require(lock.get('budget_notice_delivery') == 'LABELED_CONTROLLER_STDERR_BEFORE_ORDINARY_TOOL_EXIT_V1','required noncancelling neutral notice delivery')
    require(args.per_response_max_output_tokens is None,'no physical cap claim or production cap setting without verified wire support')
    require(lock.get('continuation_policy') == 'NEUTRAL_CONTINUE_UNTIL_95_PERCENT_OR_WALL',
            'fixed neutral continuation policy required')
    expected = {'wall_seconds': args.wall, 'generated_tokens': args.output, 'operations': args.operations,
                'responses': args.responses, 'memory_gib': args.memory_gib, 'scratch_gib': args.scratch_gib,
                'cpus': args.cpus}
    require(lock.get('resources') == expected, 'resource settings differ from lock')
    require(1 <= args.wall <= 7200 and 1 <= args.memory_gib <= 300 and 1 <= args.scratch_gib <= 300,
            'invalid discovery allowance')
    require(1 <= args.cpus <= 32 and args.output > 0 and args.operations > 0 and args.responses > 0,
            'invalid CPU/token/operation/response allowance')
    args.actual_bounded_cgroup = check_scope(expected)
    return runtime

def make_prompt(packet):
    task = packet / 'TASK.md' if (packet / 'TASK.md').is_file() else packet / 'task.md'
    require(task.is_file(), 'neutral task is missing')
    # Long corpus/library content remains fully searchable offline; never silently inline/truncate it.
    return (task.read_text() + '\n\nRead all permitted material through the assigned offline filesystem. '
            'The complete packet is mounted read-only at /task. The only additional read-only sources '
            'are those explicitly listed by /task/RUNTIME_PATHS.json, if supplied. Do not use external '
            'sources or prior sessions. Save drafts early under /work/submission, then submit exact '
            'file hashes in LOCK.json. Checkpoints are passive and provide no evaluation feedback. '
            'Continue investigating stronger valid conclusions throughout the fixed research budget; '
            'a first success is not the stopping rule.\n')

_research = None
RuntimeExecutor = None

def configure_runtime(runtime, args):
    global ExistingExecutorAdapter, RuntimeExecutor, C, V, MODEL, BASE, DEVELOPER
    spec = importlib.util.spec_from_file_location('deep_tertiary_existing_research', OLD / 'scripts/research_session.py')
    research = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(research)
    research.ARGS = args
    parent_adapter = research.ExistingExecutorAdapter
    class AssignedRuntime(research.ResearchExecutor):
        async def start(self):
            self.address_space_limit = args.memory_gib * 1024 ** 3
            self.cpu_limit = args.wall
            self.file_size_limit = 64 * 1024 ** 2
            url = await parent_adapter.start(self)
            spec = strict_json(self.spec_path)
            spec.update(tmpfsSize=str(args.scratch_gib) + 'g', tmpSize='1g', network='offline')
            for row in runtime['mounts']:
                spec['entries'].append({'kind': 'ro', 'path': row['target'], 'source': row['source']})
            for name in ['gcc', 'g++', 'as', 'ld']:
                executable = shutil.which(name)
                if executable:
                    spec['entries'].append({'kind': 'ro', 'path': '/usr/bin/' + name,
                                            'source': str(Path(executable).resolve())})
            for path in ['/usr/lib/gcc', '/usr/include']:
                if Path(path).is_dir():
                    spec['entries'].append({'kind': 'ro', 'path': path, 'source': path})
            # Only these two pinned generic packages, never a shared site-packages directory.
            for name in ['mpmath', 'sympy']:
                spec['entries'].append({'kind': 'ro', 'path': '/usr/lib/python3/dist-packages/' + name,
                    'source': str(STUDY / 'coordinator/runner-generic-python' / name)})
            paths = runtime.get('lean_path', [])
            if any(row['target'] == '/opt/lean' for row in runtime['mounts']):
                wrapper = self.directory / 'lean-wrapper.sh'
                wrapper.write_text('#!/bin/bash\nexport LEAN_PATH=' + shlex.quote(':'.join(paths) + ':/work/objects') +
                                   '\nexec /opt/lean/bin/lean -j' + str(args.cpus) + ' "$@"\n')
                wrapper.chmod(0o555)
                spec['entries'].append({'kind': 'ro', 'path': '/bin/lean', 'source': str(wrapper)})
            spec['env'].update(HOME='/home/worker', LANG='C', LC_ALL='C',
                               LEAN_PATH=':'.join(paths) + ':/work/objects',
                               PATH='/opt/lean/bin:/bin:/usr/bin')
            self.spec_path.write_text(json.dumps(spec, indent=2) + '\n')
            return url
    ExistingExecutorAdapter = AssignedRuntime
    RuntimeExecutor = AssignedRuntime
    C = VENDOR
    V = C.parent
    MODEL = args.model
    BASE = research.CORE.BASE
    DEVELOPER = ('Use only the assigned offline executor and sources. No delegation, human-input, goals, '
                 'MCP, connectors, browser, external network or host tools. Use non-login /bin/bash and '
                 '/usr/bin/python3.10. Do not provide private reasoning transcripts. Publish mathematical '
                 'statements, reproducible derivations, code, tests, exact source locators and limitations. '
                 'Save regular flat files under /work/submission, each at most2MiB. LOCK.json must be '
                 '{"files":[{"path":"candidate.md","sha256":"..."}]}, at most15 payloads plus LOCK.json. '
                 'An unverified numerical observation is not a theorem. Continue research through the fixed '
                 'budget, including after an initial success. Keep unsuccessful attempts and incomplete work.')

async def catalog_only(path):
    require(not path.exists(), 'fresh catalog receipt required')
    private = Path(tempfile.mkdtemp(prefix='deep-tertiary-catalog-', dir=STUDY / 'coordinator'))
    private.chmod(0o700)
    auth = Path(os.environ.get('CODEX_HOME', str(Path.home() / '.codex'))) / 'auth.json'
    require(auth.is_file(), 'existing native authentication is unavailable')
    (private / 'auth.json').symlink_to(auth)
    (private / 'config.toml').write_text('[analytics]\nenabled=false\n[skills]\ninclude_instructions=false\n[skills.bundled]\nenabled=false\n[features]\napps=false\nplugins=false\nmemories=false\nmulti_agent=false\nbrowser_use=false\n')
    env = os.environ.copy()
    env.update(CODEX_HOME=str(private), TOKIO_WORKER_THREADS='2', RAYON_NUM_THREADS='2')
    proc = await asyncio.create_subprocess_exec('codex', 'app-server', '--strict-config', '--listen', 'stdio://',
        env=env, cwd=private, stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE, limit=4 * 1024 ** 2)
    stderr_task = asyncio.create_task(proc.stderr.read())
    async def rpc(number, method, params):
        proc.stdin.write((json.dumps({'id': number, 'method': method, 'params': params}) + '\n').encode())
        await proc.stdin.drain()
        while True:
            line = await asyncio.wait_for(proc.stdout.readline(), 25)
            require(bool(line), 'native catalog controller exited')
            obj = json.loads(line)
            if obj.get('id') == number:
                require('error' not in obj, 'catalog RPC rejected')
                return obj['result']
    try:
        initialization = await rpc(1, 'initialize', {'clientInfo': {'name': 'deep-tertiary-live-catalog', 'version': '1'}, 'capabilities': {'experimentalApi': True}})
        proc.stdin.write(b'{"method":"initialized","params":{}}\n')
        await proc.stdin.drain()
        models = await rpc(2, 'model/list', {})
        capacity_status = 'UNKNOWN_OR_UNSUPPORTED'
        capacity = None
        try:
            raw_capacity = await rpc(3, 'account/rateLimits/read', {})
            def safe_capacity(value):
                if isinstance(value, dict):
                    return {key: safe_capacity(item) for key, item in value.items()
                            if key in {'rateLimits', 'rateLimitsByLimitId', 'primary', 'secondary',
                                       'usedPercent', 'windowDurationMins', 'resetsAt', 'limitId', 'limitName'}
                            or isinstance(item, (dict, list))}
                if isinstance(value, list):
                    return [safe_capacity(item) for item in value]
                if isinstance(value, (int, float, bool)) or value is None:
                    return value
                return value if isinstance(value, str) and len(value) <= 120 else None
            capacity = safe_capacity(raw_capacity)
            capacity_status = 'READ_ONLY_EXISTING_ACCOUNT_CAPACITY_REPORTED'
        except (ValueError, TimeoutError, asyncio.TimeoutError):
            pass
        data = models.get('data', [])
        record = {'status': 'LIVE_NATIVE_MODEL_CATALOG_NO_INFERENCE', 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  'initialization': initialization, 'catalog': models, 'inference_calls': 0,
                  'immutable_backend_revision_exposed': any('revision' in row for row in data), 'capacity_status': capacity_status, 'rate_limits': capacity}
        path.write_text(json.dumps(record, indent=2) + '\n')
        print(json.dumps({'status': record['status'], 'model_aliases': [row.get('id') for row in data],
                          'immutable_backend_revision_exposed': record['immutable_backend_revision_exposed'], 'capacity_status': capacity_status, 'rate_limits': capacity}))
    finally:
        if proc.returncode is None:
            proc.terminate()
        try:
            await asyncio.wait_for(proc.wait(), 3)
        except asyncio.TimeoutError:
            proc.kill()
            await proc.wait()
        await stderr_task
        shutil.rmtree(private)

def cli():
    parser = argparse.ArgumentParser(description='Pinned existing native controller with exact per-arm read-only packets.')
    parser.add_argument('--catalog-only', type=Path)
    parser.add_argument('--lock', type=Path)
    parser.add_argument('--packet-manifest', type=Path)
    parser.add_argument('--runtime', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--fixture', action='store_true')
    parser.add_argument('--per-response-max-output-tokens',type=int)
    parser.add_argument('--fixture-boundary-steps',type=int,default=1)
    parser.add_argument('--fixture-budget-prefix',action='store_true')
    parser.add_argument('--fixture-draft-at',type=int,default=1)
    parser.add_argument('--model', default='gpt-6.1-sol')
    parser.add_argument('--effort', choices=['low', 'medium', 'high', 'xhigh'], default='high')
    parser.add_argument('--wall', type=int, default=7200)
    parser.add_argument('--output', type=int, default=80000)
    parser.add_argument('--operations', type=int, default=300)
    parser.add_argument('--responses', type=int, default=256)
    parser.add_argument('--memory-gib', type=int, default=48)
    parser.add_argument('--scratch-gib', type=int, default=24)
    parser.add_argument('--cpus', type=int, default=4)
    parser.add_argument('--phase', default='MAIN')
    args = parser.parse_args()
    check_sources()
    if args.catalog_only:
        require(not args.lock and not args.fixture, 'catalog query cannot also launch a worker')
        require(args.catalog_only.resolve().is_relative_to(STUDY), 'catalog receipt outside own study')
        asyncio.run(catalog_only(args.catalog_only.resolve()))
        return
    require(args.out is not None and args.packet_manifest is not None and args.runtime is not None,
            'packet manifest, runtime manifest and fresh output are required')
    args.out = args.out.resolve()
    require(args.out.is_relative_to(STUDY) and not args.out.exists(), 'fresh output under this study required')
    runtime = validate_launch(args)
    args.fixture_hook_fault = False
    args.fixture_artifact_name = 'canary.txt'
    args.paired_task_seed = 0
    args.compiler = False
    args.python_only = False
    args.environment = ''
    args.python_optimization = sys.flags.optimize
    temporary_root = STUDY / 'coordinator/controller-temp'
    temporary_root.mkdir(exist_ok=True)
    tempfile.tempdir = str(temporary_root)
    configure_runtime(runtime, args)
    asyncio.run(main(args))

_prompt_before_v2 = make_prompt
def make_prompt(packet):
    return _prompt_before_v2(packet) + '\nOperational budget policy: neutral usage notices arrive at25%,50%,75%,90%. From50%maintain a complete consistent LOCK.json for supported current work. At75%finalize and preserve that lock before further improvements. Never discard the prior valid lock until its replacement is ready. These notices provide no mathematical evaluation feedback.\n'

# V2 additive budget-prefix adapter; old production controller remains immutable.
_original_configure_runtime = configure_runtime

READONLY_EXECUTOR_METHODS = frozenset({
    'initialize', 'initialized', 'environment/status', 'environmentConfig/read',
    'fs/readFile', 'fs/readDirectory', 'fs/getMetadata', 'fs/watch', 'fs/watchMissing', 'fs/unwatch',
    'process/poll', 'process/getOutput', 'process/getStatus',
})

def _strict_lock(raw):
    def unique(rows):
        d = {}
        for key, value in rows:
            require(key not in d, 'duplicate lock JSON key')
            d[key] = value
        return d
    return json.loads(raw, object_pairs_hook=unique,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))

def configure_runtime(runtime, args):
    global ExistingExecutorAdapter, RuntimeExecutor
    _original_configure_runtime(runtime, args)
    Parent = ExistingExecutorAdapter
    class BudgetPrefixRuntime(Parent):
        async def start(self):
            self.mutation_gate = asyncio.Lock()
            self.last_mutation_forward = 0.0
            self.last_mutation_ack = 0.0
            self.mutation_sequence = 0
            self.mutation_ack_sequence = 0
            self.pending_mutation_ids = {}
            self.usage_observation = None
            self.usage_observation_index = 0
            self.usage_ordering_witnesses = []
            self.timely_checkpoints = []
            self.timely_checkpoint_skips = {}
            self.last_saved_lock_sha256 = None
            self.budget_notices = []
            self.process_sequence_offsets = {}
            self.budget_started = time.monotonic()
            self.timely_root = Path(args.out) / 'timely-locked-prefixes'
            return await super().start()

        def observe_usage(self, value):
            output = value['total']['outputTokens']
            prior = self.usage_observation
            if prior is not None and output < prior['output_tokens']:
                return 'USAGE_COUNTER_REGRESSION_QUARANTINE'
            self.usage_observation_index += 1
            self.usage_ordering_witnesses.append({'output_tokens':output,'usage_monotonic':time.monotonic(),'mutation_sequence':self.mutation_sequence,'ack_sequence':self.mutation_ack_sequence,'pending_ids':list(self.pending_mutation_ids),'last_ack_monotonic':self.last_mutation_ack})
            self.usage_observation = {'output_tokens': output, 'usage_event_index': self.usage_observation_index,
                                     'received_monotonic': time.monotonic()}
            return None

        def skip(self, reason):
            self.timely_checkpoint_skips[reason] = self.timely_checkpoint_skips.get(reason, 0) + 1

        async def capture_timely_lock(self, trigger):
            async with self.mutation_gate:
                return await self._capture_timely_lock_while_gated(trigger)

        async def _capture_timely_lock_while_gated(self, trigger):
            before = self.usage_observation
            if before is None or before['output_tokens'] < args.output * .5:
                return None
            if before['output_tokens'] > args.output:
                self.skip('OVER_ADMISSION_CEILING')
                return None
            if self.pending_mutation_ids or before['received_monotonic'] < self.last_mutation_forward:
                self.skip('MUTATION_FORWARD_NOT_COVERED_BY_USAGE_OBSERVATION')
                return None
            if self.operation_count > args.operations or self.budget_exceeded:
                self.skip('OPERATION_ADMISSION_EXCEEDED')
                return None
            sequence = self.mutation_sequence
            if self.mutation_ack_sequence != sequence:
                self.skip('UNACKNOWLEDGED_MUTATION_PREFIX')
                return None
            started = time.monotonic()
            if started - self.budget_started > args.wall:
                self.skip('AFTER_ACTIVE_WALL_ADMISSION')
                return None
            try:
                meta = (await self.export_metadata('LOCK.json')).get('result', {})
                require(meta.get('isFile') and not meta.get('isSymlink') and isinstance(meta.get('size'), int)
                        and 0 < meta['size'] <= 65536, 'regular bounded lock required')
                lock_raw = await self.read_export('/work/submission/LOCK.json')
                lock_sha = digest(lock_raw)
                if lock_sha == self.last_saved_lock_sha256:
                    return None
                lock = _strict_lock(lock_raw)
                require(isinstance(lock, dict) and set(lock) == {'files'} and isinstance(lock['files'], list)
                        and 0 < len(lock['files']) <= 15, 'consistent lock schema')
                copied = []
                identities = []
                seen = set()
                for item in lock['files']:
                    require(isinstance(item, dict) and set(item) == {'path', 'sha256'}, 'lock row schema')
                    name = item['path']
                    require(isinstance(name, str) and re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,127}', name)
                            and name != 'LOCK.json' and name not in seen, 'flat unique payload name')
                    require(isinstance(item['sha256'], str) and re.fullmatch(r'[a-f0-9]{64}', item['sha256']),
                            'exact payload SHA256 required')
                    seen.add(name)
                    metadata = (await self.export_metadata(name)).get('result', {})
                    require(metadata.get('isFile') and not metadata.get('isSymlink') and
                            isinstance(metadata.get('size'), int) and 0 <= metadata['size'] <= 2 * 1024 ** 2,
                            'regular bounded payload required')
                    body = await self.read_export('/work/submission/' + name)
                    require(len(body) == metadata['size'] and digest(body) == item['sha256'], 'payload hash mismatch')
                    copied.append((name, body))
                    identities.append({'path': name, 'bytes': len(body), 'sha256': item['sha256']})
                require(await self.read_export('/work/submission/LOCK.json') == lock_raw, 'lock changed during capture')
                after = self.usage_observation
                finished = time.monotonic()
                require(after is not None and after['output_tokens'] <= args.output and
                        finished - self.budget_started <= args.wall, 'snapshot outside token/wall admission')
                require(not self.pending_mutation_ids and self.mutation_sequence == sequence and
                        self.mutation_ack_sequence == sequence and
                        before['received_monotonic'] >= self.last_mutation_forward,
                        'executor mutation ordering uncertain')
                self.timely_root.mkdir(exist_ok=True)
                directory = self.timely_root / ('prefix-' + str(len(self.timely_checkpoints) + 1).zfill(4))
                require(not directory.exists(), 'fresh immutable prefix required')
                temporary = Path(tempfile.mkdtemp(prefix='.prefix-', dir=self.timely_root))
                try:
                    (temporary / 'LOCK.json').write_bytes(lock_raw)
                    for name, body in copied:
                        (temporary / name).write_bytes(body)
                    receipt = {'schema': 'CONSISTENT_ACCOUNTED_EXECUTOR_PREFIX_V2',
                        'status': 'HASHED_LOCKED_ARTIFACT_FROM_WITHIN_ADMISSION_EXECUTION_PREFIX',
                        'trigger': trigger, 'controller_source_sha256': file_sha(__file__),
                        'lock_sha256': lock_sha, 'files': identities,
                        'usage_before': before, 'usage_after': after,
                        'admission_generated_token_ceiling': args.output, 'admission_wall_seconds': args.wall,
                        'runtime_operation_count': self.operation_count, 'runtime_operation_ceiling': args.operations,
                        'last_mutation_sequence': sequence, 'last_mutation_ack_sequence': self.mutation_ack_sequence,
                        'last_mutation_forward_monotonic': self.last_mutation_forward,
                        'last_mutation_ack_monotonic': self.last_mutation_ack,
                        'capture_started_monotonic': started, 'capture_finished_monotonic': finished,
                        'capture_finished_elapsed_seconds': finished - self.budget_started,
                        'model_mutations_forwarded_during_capture': 0, 'pending_mutations': 0,
                        'internal_snapshot_RPC_charged_to_worker': False,
                        'mathematical_validity': 'NOT_ASSESSED',
                        'trust_boundary': 'Pinned native serialized cumulative-usage notifications account the previously forwarded execution prefix; every RPC acknowledgement must finish before capture, but a cleanup acknowledgement may follow its usage notification. OS/runtime and SHA256 remain trusted. No mathematical truth follows from this provenance receipt. Uncertain ordering or an over-budget observation rejects the capture.'}
                    (temporary / 'RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
                    os.rename(temporary, directory)
                finally:
                    if temporary.exists():
                        shutil.rmtree(temporary)
                record = {'path': str(directory), 'receipt_sha256': file_sha(directory / 'RECEIPT.json'),
                          'lock_sha256': lock_sha, 'output_tokens_before': before['output_tokens'],
                          'output_tokens_after': after['output_tokens'], 'usage_event_index': after['usage_event_index'],
                          'mutation_sequence': sequence, 'elapsed_seconds': finished - self.budget_started}
                self.timely_checkpoints.append(record)
                self.last_saved_lock_sha256 = lock_sha
                return record
            except (ValueError, RuntimeError, TimeoutError, asyncio.TimeoutError, OSError) as error:
                # Missing/partially written LOCK is incomplete research, never an accepted candidate.
                self.skip(type(error).__name__)
                return None

        async def _bridge(self, ws):
            adapter = self
            class GatedConnection:
                async def __aiter__(self):
                    async for frame in ws:
                        data = frame.encode() if isinstance(frame, str) else frame
                        message = json.loads(data)
                        method = message.get('method')
                        if method in READONLY_EXECUTOR_METHODS:
                            yield frame
                        else:
                            async with adapter.mutation_gate:
                                await adapter._capture_timely_lock_while_gated('BEFORE_NEXT_EXECUTOR_MUTATION')
                                adapter.mutation_sequence += 1
                                adapter.last_mutation_forward = time.monotonic()
                                key = message.get('id')
                                # Unknown mutating notifications cannot establish an acknowledged prefix.
                                key = key if key is not None else 'unacknowledged-notification-' + str(adapter.mutation_sequence)
                                adapter.pending_mutation_ids[key] = adapter.mutation_sequence
                                yield frame
                async def send(self, payload):
                    data = payload.encode() if isinstance(payload, str) else payload
                    message = json.loads(data)
                    key = message.get('id')
                    if key in adapter.pending_mutation_ids:
                        sequence = adapter.pending_mutation_ids.pop(key)
                        adapter.last_mutation_ack = time.monotonic()
                        adapter.mutation_ack_sequence = max(adapter.mutation_ack_sequence, sequence)
                    method=message.get('method')
                    params=message.get('params',{})
                    if method in {'process/output','process/exited','process/closed'} and isinstance(params,dict):
                        process_id=params.get('processId')
                        original_seq=params.get('seq')
                        offset=adapter.process_sequence_offsets.get(process_id,0)
                        if method=='process/exited' and isinstance(original_seq,int):
                            observed=adapter.usage_observation
                            due=[]
                            if observed is not None and observed['output_tokens']<=args.output:
                                for fraction in [.25,.5,.75,.9]:
                                    if observed['output_tokens']>=args.output*fraction and not any(r['fraction']==fraction for r in adapter.budget_notices):
                                        due.append(fraction)
                            if due:
                                used=observed['output_tokens']
                                advice=('Maintain a complete consistent LOCK.json for current supported work; continue improving under the unchanged budget.' if max(due)<.75 else
                                        'Finalize and atomically preserve a complete consistent LOCK.json immediately before further research; keep the prior valid locked version until its replacement is ready. Further improvement remains allowed within the remaining budget.')
                                notice=('\n[CONTROLLER_BUDGET_METADATA: this is not program stderr; no mathematical evaluation feedback]\n'
                                        'Last reported cumulative generated output: '+str(used)+' of '+str(args.output)+'. The current tool-response cost is not yet reflected in that counter. Crossed fractions: '+','.join(str(v)for v in due)+'. '+advice+
                                        '\n[END_CONTROLLER_BUDGET_METADATA]\n')
                                import base64
                                injected={'method':'process/output','params':{'processId':process_id,'seq':original_seq+offset,'stream':'stderr','chunk':base64.b64encode(notice.encode()).decode()}}
                                await ws.send(json.dumps(injected))
                                offset+=1
                                adapter.process_sequence_offsets[process_id]=offset
                                for fraction in due:
                                    adapter.budget_notices.append({'fraction':fraction,'observed_generated_tokens':used,'usage_event_index':observed['usage_event_index'],'elapsed_seconds':time.monotonic()-adapter.budget_started,'delivery':'LABELED_CONTROLLER_STDERR_BEFORE_ORDINARY_TOOL_EXIT_V1','process_id':process_id,'original_exit_seq':original_seq,'inserted_display_seq':original_seq+offset-1,'display_seq_offset_after':offset,'notice_sha256':digest(notice.encode()),'no_evaluation_feedback':True,'provider_request_cancelled_by_notice':False})
                                ledger=Path(args.out)/'CONTROLLER_NOTICE_TRANSPORT.jsonl'
                                with ledger.open('a')as handle:handle.write(json.dumps({'injected_notification':injected,'controller_metadata_only':True,'raw_program_notifications_preserved_in':'executor/transport.json'})+'\n')
                        if isinstance(original_seq,int) and offset:
                            outgoing=dict(message);outgoing['params']=dict(params);outgoing['params']['seq']=original_seq+offset
                            payload=json.dumps(outgoing)
                    await ws.send(payload)
            return await super()._bridge(GatedConnection())
    ExistingExecutorAdapter = BudgetPrefixRuntime
    RuntimeExecutor = BudgetPrefixRuntime

if __name__ == '__main__':
    cli()
