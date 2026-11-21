"""Source-preserving follow-up over the existing isolated native executor.

Planning milestones never terminate/disqualify. Research ends on its own explicit
both-family submission; review and repair are separate independently recorded stages.
"""
from pathlib import Path
import argparse,asyncio,base64,datetime,hashlib,http.server,importlib.util,json,os,re,resource,shlex,shutil,signal,sys,tempfile,threading,time
from types import SimpleNamespace
S=Path(__file__).resolve().parents[1]
W=S.parent
OLD_STUDY=W/'ieantn-deep-tertiary-exposure-a-20261117'
ORIGINAL=OLD_STUDY/'scripts/native_controller_v2.py'
ORIGINAL_SHA='89784de8153c616219a4a93d23f1859845d18924ad472d0d6321fb0eb2661091'

def require(ok,message):
    if not ok:raise ValueError(message)
def digest(data):return hashlib.sha256(data).hexdigest()
def file_sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1024**2),b''):h.update(b)
    return h.hexdigest()
def strict_loads(raw):
    def pairs(items):
        d={}
        for k,v in items:
            require(k not in d,'duplicate JSON key');d[k]=v
        return d
    return json.loads(raw,object_pairs_hook=pairs,parse_constant=lambda v:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def strict_json(path):return strict_loads(Path(path).read_bytes())
def atomic(path,value):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    fd,name=tempfile.mkstemp(prefix='.'+path.name+'.',dir=path.parent);temp=Path(name)
    try:
        with os.fdopen(fd,'w') as f:json.dump(value,f,indent=2,allow_nan=False);f.write('\n')
        os.replace(temp,path)
    finally:
        if temp.exists():temp.unlink()
require(file_sha(ORIGINAL)==ORIGINAL_SHA,'pinned old controller changed')
spec=importlib.util.spec_from_file_location('followup_original_controller',ORIGINAL)
core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
sanitize_public=core.sanitize_public
boundary_fault=core.boundary_fault
def advertised_tools(request):
    result={}
    def visit(rows,namespace=None):
        for row in rows:
            if row.get('type')=='namespace':visit(row.get('tools',[]),row.get('name'))
            elif isinstance(row.get('name'),str):result[(namespace,row['name'])]=row.get('type')
    visit(request.get('tools',[]))
    for item in request.get('input',[]):
        if item.get('type')=='additional_tools':visit(item.get('tools',[]))
    return result

class Fixture(http.server.BaseHTTPRequestHandler):
    def do_POST(self):
        data=json.loads(self.rfile.read(int(self.headers['Content-Length'])));self.server.requests.append(data)
        n=len(self.server.requests)
        if n==getattr(self.server,'draft_at',1) or (getattr(self.server,'budget_prefix_fixture',False) and n in (4,6)):
            script='import os,json,hashlib,resource\nif resource.getrlimit(resource.RLIMIT_CPU)!=(resource.RLIM_INFINITY,resource.RLIM_INFINITY):raise RuntimeError(\"CPU planning shadow cap\")\nif resource.getrlimit(resource.RLIMIT_FSIZE)[0]<25769803776:raise RuntimeError(\"FSIZE below24GiB resource contract\")\nos.makedirs("/work/submission",exist_ok=True);b=b"NEUTRAL_FIXTURE_NOT_A_MATHEMATICAL_CANDIDATE\\n";open("/work/submission/canary.txt","wb").write(b);json.dump({"files":[{"path":"canary.txt","sha256":hashlib.sha256(b).hexdigest()}]},open("/work/submission/LOCK.json","w"));print(json.dumps({"task_bytes":len(open("/task/task.md"if os.path.isfile("/task/task.md")else"/task/TASK.md","rb").read()),"host_absent":not os.path.exists("/ryu/hyunsik/playground/independence/codex/ivy/memory"),"controller_canary_absent":not os.path.exists("host-only-canary.txt"),"auth_absent":not os.path.exists("/home/worker/.codex/auth.json"),"pid_namespace":os.readlink("/proc/self/ns/pid"),"net_namespace":os.readlink("/proc/self/ns/net"),"genericLean_available":os.path.isfile("/opt/lean/bin/lean"),"CPU_limit":list(resource.getrlimit(resource.RLIMIT_CPU)),"FSIZE_limit":list(resource.getrlimit(resource.RLIMIT_FSIZE)),"cache_probe":"neutral"}))'
            script=script.replace('canary.txt',getattr(self.server,'artifact_name','canary.txt'))
            code='text({fresh_cache:load("study_cache")===undefined});text(await tools.exec_command('+json.dumps({'cmd':'/usr/bin/python3.10 -I -c '+shlex.quote(script),'shell':'/bin/bash','login':False,'yield_time_ms':1000,'max_output_tokens':1000})+'));'
            offered={name:kind for (namespace,name),kind in advertised_tools(data).items()}
            if offered.get('exec_command')=='function':
                item={'id':'fc1','type':'function_call','call_id':'fixture1','name':'exec_command','arguments':json.dumps({'cmd':'/usr/bin/python3.10 -I -c '+shlex.quote(script),'shell':'/bin/bash','login':False,'yield_time_ms':1000,'max_output_tokens':1000})}
            else:
                item={'id':'ctc1','type':'custom_tool_call','call_id':'fixture1','name':'exec','namespace':'functions','input':code}
        elif n==2:
            offered=advertised_tools(data)
            choices=[(None,'get_goal','{}'),('clock','sleep','{"duration_ms":1}'),('collaboration','list_agents','{}')]
            chosen=next((row for row in choices if offered.get((row[0],row[1]))=='function'),None)
            if chosen is None:raise RuntimeError('No actual advertised harmless negative tool is available')
            item={'id':'denied1','type':'function_call','call_id':'fixture-denied','name':chosen[1],'arguments':chosen[2]}
            if chosen[0] is not None:item['namespace']=chosen[0]
        elif n<=getattr(self.server,'boundary_steps',1):
            offered={name:kind for (namespace,name),kind in advertised_tools(data).items()}
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
OLD=core.OLD
validate_runtime=core.validate_runtime
RuntimeExecutor=None
TERMINATION_REQUESTED=False

def make_prompt(packet):
    task=packet/'TASK.md'
    require(task.is_file(),'TASK.md missing')
    return task.read_text()+'\n\nThe actual read-only packet mount is /task. Only mounts in /task/RUNTIME_PATHS.json are accessible. Read the full allowed corpus offline. Save research state and self-contained mathematical outputs under /work/submission, with current exact hashes in LOCK.json. The allocation is a planning milestone, not a deadline: continue automatically when meaningful work remains. Crossing token/time/operation milestones does not invalidate results. No other arm or coordinator answer is accessible.\n'

def continuation_message(args,readiness):
    return ('Continue your own research or assessment under the unchanged source/task boundary. Planning milestones automatically extend; there is no token, response or operation rejection. Preserve all valid earlier branches and document substantial improvement attempts and the precise remaining mathematical bottleneck. Supply both-family STAGE_STATUS.json and exact LOCK.json when ready for independent review. No mathematical feedback or other-arm results are supplied. Last mechanical export status: '+json.dumps(readiness,sort_keys=True))

async def snapshot_flat(adapter,directory,quiesced):
    directory=Path(directory);require(not directory.exists(),'fresh checkpoint directory required');directory.mkdir(parents=True);(directory/'files').mkdir()
    receipt={'schema':'FOLLOWUP_PASSIVE_SOURCE_SNAPSHOT_V1','quiesced':quiesced,'atomic_directory_snapshot_claimed':False,'files':[],'skipped':[],'mathematical_validity':'UNASSESSED'}
    try:
        listed=await adapter.list_submission();receipt['listing']=listed
        entries=listed.get('result',{}).get('entries')
        if not isinstance(entries,list):
            receipt['status']='SUBMISSION_NOT_YET_AVAILABLE'
        else:
            for entry in entries:
                name=entry.get('fileName')
                if not isinstance(name,str) or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,127}',name) or not entry.get('isFile'):
                    receipt['skipped'].append({'name':name,'reason':'nonflat_path_retained_in_worker'});continue
                meta=(await adapter.export_metadata(name)).get('result',{})
                if not meta.get('isFile') or meta.get('isSymlink'):
                    receipt['skipped'].append({'name':name,'reason':'nonregular'});continue
                body=await adapter.read_export('/work/submission/'+name)
                (directory/'files'/name).write_bytes(body)
                receipt['files'].append({'path':name,'bytes':len(body),'sha256':digest(body)})
            receipt['status']='SAVED_ALL_AVAILABLE_FLAT_SOURCE_FILES' if not receipt['skipped'] else 'SAVED_WITH_EXPLICIT_FORMAT_RECOVERY_PENDING'
    except Exception as e:receipt.update(status='PARTIAL_CHECKPOINT_PRESERVED',error_type=type(e).__name__,error=str(e))
    atomic(directory/'SNAPSHOT.json',receipt);return receipt

async def stage_ready(adapter,args):
    try:
        lock_raw=await adapter.read_export('/work/submission/LOCK.json')
        lock=strict_loads(lock_raw)
        require(isinstance(lock,dict) and isinstance(lock.get('files'),list),'LOCK files list missing')
        seen=set()
        for row in lock['files']:
            require(isinstance(row,dict) and isinstance(row.get('path'),str),'LOCK row missing path')
            name=row['path'];require(re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,127}',name) is not None and name not in seen and name!='LOCK.json','flat unique source file required')
            seen.add(name);metadata=(await adapter.export_metadata(name)).get('result',{})
            require(metadata.get('isFile') and not metadata.get('isSymlink'),'regular submitted source required')
            require(digest(await adapter.read_export('/work/submission/'+name))==row.get('sha256'),'source hash not current: '+name)
        require('STAGE_STATUS.json' in seen,'STAGE_STATUS.json must be listed in LOCK')
        status=strict_loads(await adapter.read_export('/work/submission/STAGE_STATUS.json'))
        require(status.get('ready_for_review') is True,'worker marks research still incomplete')
        families=status.get('families',{})
        require(set(families)=={'Ramanujan','Mertens'},'both family assessments required')
        allowed={'supported','incomplete','no_additional_improvement','false_with_counterexample','unassessed','supported_at_stated_trust_tier'}
        require(all(isinstance(v,dict) and v.get('status') in allowed for v in families.values()),'explicit family status required')
        require(status.get('serious_attempts_documented') is True,'improvement attempts/bottlenecks not yet documented')
        require(await adapter.read_export('/work/submission/LOCK.json')==lock_raw,'LOCK changed during readiness read')
        return {'ready':True,'status':status,'lock_sha256':digest(lock_raw),'files':len(lock['files']),'mathematical_validity':'UNASSESSED_REQUIRES_INDEPENDENT_REVIEW'}
    except Exception as e:return {'ready':False,'mechanical_or_worker_readiness_reason':str(e),'no_mathematical_judgment':True}

def configure_runtime(runtime,args):
    global RuntimeExecutor
    # Only the original pre-budget-prefix runtime constructor is reused. It writes
    # new per-run specs; old STUDY paths are read-only generic-package sources.
    args.wall=86400
    args.compiler=False;args.python_only=False;args.environment=''
    core._original_configure_runtime(runtime,args)
    Parent=core.ExistingExecutorAdapter
    class FollowupAssignedRuntime(Parent):
        async def start(self):
            url=await super().start()
            self.operation_limit=None
            self.cpu_limit=resource.RLIM_INFINITY
            self.file_size_limit=args.scratch_gib*1024**3
            return url
        async def _bridge(self,ws):
            # Reassign immediately before the inherited bridge spawns its process.
            self.operation_limit=None
            self.cpu_limit=resource.RLIM_INFINITY
            self.file_size_limit=args.scratch_gib*1024**3
            return await super()._bridge(ws)
        async def read_export(self,path):
            require(path.startswith('/work/submission/') and '..' not in Path(path).parts,'export outside own submission')
            p=getattr(self,'active_process',None);require(p is not None and p.returncode is None,'executor unavailable')
            self.serial+=1;key='trusted-export-'+str(self.serial);future=asyncio.get_running_loop().create_future();self.waiters[key]=future
            message={'id':key,'method':'fs/readFile','params':{'path':'file://'+path,'sandbox':None}}
            p.stdin.write((json.dumps(message)+'\n').encode());await p.stdin.drain()
            try:response=await asyncio.wait_for(future,30)
            finally:self.waiters.pop(key,None)
            self.logs.append({'trusted_export':path,'response':response})
            require('error' not in response,'source export read failed')
            encoded=response.get('result',{}).get('dataBase64');require(isinstance(encoded,str),'readFile response schema')
            return base64.b64decode(encoded,validate=True)
    core.ExistingExecutorAdapter=FollowupAssignedRuntime;RuntimeExecutor=FollowupAssignedRuntime
    core.DEVELOPER=('Use only the assigned offline executor and source packet. No delegation, human-input, goals, MCP, connectors, browser, external network or host tools. Use non-login /bin/bash and /usr/bin/python3.10. Do not provide private reasoning transcripts. Publish mathematical statements, derivations, executable source, evidence, exact source locators, failed attempts and limitations. Save regular flat files under /work/submission; prefer files below2MiB for convenient transfer but a harmless format issue does not invalidate mathematics. LOCK.json example: {"files":[{"path":"candidate.md","sha256":"64 lowercase hex characters"},{"path":"STAGE_STATUS.json","sha256":"64 lowercase hex characters"}]}. Planning milestones auto-extend; they are not output, response, operation or active-time caps. Finish when the complete both-family portfolio and serious improvement attempts are ready for independent review, with exact remaining bottlenecks documented. Do not claim a numerical sample proves a whole-domain theorem.')


async def main(args):
    out=Path(args.out).resolve();packet=Path(args.packet).resolve()
    if out.exists():raise RuntimeError('session directory exists; never overwrite a run')
    out.mkdir(parents=True);private=Path(tempfile.mkdtemp(prefix='ieantn-study-controller-'));private.chmod(0o700)
    state=private/'state';state.mkdir(mode=0o700);cwd=private/'cwd';cwd.mkdir(mode=0o700)
    (cwd/'host-only-canary.txt').write_text('HOST_ONLY_NOT_WORKER\n')
    prompt=make_prompt(packet);(out/'worker_prompt.txt').write_text(prompt)
    adapter=core.ExistingExecutorAdapter(out/'executor',packet,working_directory=str(cwd),operation_limit=None);url=await adapter.start()
    server=None
    config=(core.C/'controller-effective-off.toml').read_text().replace('shell_tool = false','shell_tool = true').replace('code_mode_host = false','code_mode_host = true').replace('hooks = false','hooks = true').replace('max_concurrent_threads_per_session = 0','max_concurrent_threads_per_session = 1\nmax_depth = 0')
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
    policy=(core.C/'research/deny_unapproved_tool.py').read_text()
    definition={'description':'Externally reviewed offline runtime restriction; no task mathematics.','hooks':{'PreToolUse':[{'matcher':'.*','hooks':[{'type':'command','command':'/usr/bin/python3.10 -I -B -c '+shlex.quote(policy),'timeout':30}]}]}}
    data=(json.dumps(definition,indent=2)+'\n').encode();trust=json.loads((core.C/'evidence/native-hook-trust/receipt.json').read_text())
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
    checkpoints=[]
    journal=(out/'events.jsonl').open('a');stderr_task=asyncio.create_task(proc.stderr.read())
    record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'mode':'NOAUTH_FINAL_CONFIG_FIXTURE' if args.fixture else args.phase,'task_packet':str(packet),'prompt_sha256':digest(prompt.encode()),'model':args.model,'effort':args.effort,'service_tier':'default','source_sha256':digest(Path(__file__).read_bytes()),'credentials_mounted_in_worker':False,'private_reasoning_collected':False,'limits':{k:str(v)if isinstance(v,Path)else v for k,v in vars(args).items()}}
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
                atomic(out/'LIVE_USAGE.json', {'generated_tokens':u['total']['outputTokens'],'usage_events':len(usage),'milestone_generated_tokens':args.output,'milestone_is_hard_cap':False,'operations':adapter.operation_count,'elapsed_seconds':time.monotonic()-started,'thread_id':tid})
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
        await rpc('environment/add',{'environmentId':'assigned-offline-runtime','execServerUrl':url,'connectTimeoutMs':3000})
        for attempt in range(120):
            record['environment_status']=await rpc('environment/status',{'environmentId':'assigned-offline-runtime'})
            status=record['environment_status'].get('result',{}).get('status')
            if status=='ready':break
            if status not in {'pending','starting','connecting'}:raise RuntimeError('restricted executor unavailable:'+str(status))
            await asyncio.sleep(.25)
        else:raise RuntimeError('restricted executor readiness interrupted before research')
        catalog=await rpc('model/list',{});models=catalog.get('result',{}).get('data',[]);selected=next((m for m in models if m['id']==args.model),None)
        record['model_catalog_observation']={'fixture_provider':args.fixture,'offered_ids':[row.get('id')for row in models]}
        if selected is None and not args.fixture:raise RuntimeError('fixed model not offered in current native catalog')
        record['model_catalog_selection']=selected if selected is not None else {'id':args.model,'fixture_only_requested_alias':True,'not_live_provider_availability':True}
        environment=[{'environmentId':'assigned-offline-runtime','cwd':str(cwd),'runtimeWorkspaceRoots':[str(cwd),'/work']}]
        thread=await rpc('thread/start',{'model':args.model,'allowProviderModelFallback':False,'serviceTier':'default','cwd':str(cwd),'ephemeral':True,'environments':environment,'sandbox':'danger-full-access','approvalPolicy':'never','baseInstructions':core.BASE,'developerInstructions':core.DEVELOPER,'config':{'web_search':'disabled'}})
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
        next_checkpoint=60.0
        next_milestone=args.output
        while True:
            if TERMINATION_REQUESTED:stop='EXTERNAL_INTERRUPTION_CHECKPOINT_PRESERVED'
            if adapter.budget_exceeded:raise RuntimeError('unexpected operation limit in unlimited followup')
            if stop:break
            used=usage[-1]['total']['outputTokens']if usage else 0
            elapsed=time.monotonic()-started
            if used>=next_milestone:
                milestones.append({'milestone':next_milestone,'observed_generated_tokens':used,'elapsed_seconds':elapsed,'action':'AUTOMATIC_PLANNING_EXTENSION_NO_TERMINATION_NO_INVALIDATION'})
                next_milestone+=args.increment
                atomic(out/'PLANNING_EXTENSIONS.json',{'milestones':milestones,'next':next_milestone,'hard_cap':False})
            if elapsed>=next_checkpoint:
                folder=out/('checkpoint-'+str(len(checkpoints)+1).zfill(5))
                snapshot=await snapshot_flat(adapter,folder,quiesced=False)
                checkpoints.append({'path':str(folder),'elapsed_seconds':elapsed,'generated_tokens':used,'receipt':snapshot})
                atomic(out/'CHECKPOINTS.json',{'snapshots':checkpoints,'mathematical_selection':False,'non_atomic_while_active':True})
                next_checkpoint=elapsed+60.0
            completions=[e for e in events if e.get('method')=='turn/completed' and e.get('params',{}).get('threadId')==tid]
            if len(completions)>continued_turns:
                last=completions[-1].get('params',{}).get('turn',{})
                used=usage[-1]['total']['outputTokens'] if usage else 0
                if last.get('status')!='completed':
                    stop='NATIVE_TURN_INTERRUPTED'
                    break
                if args.fixture:
                    break
                ready=await stage_ready(adapter,args)
                record['last_submission_readiness']=ready
                if ready['ready']:
                    record['research_submission_ready']=True
                    break
                continued_turns=len(completions)
                follow=await rpc('turn/start',{'threadId':tid,'input':[{'type':'text','text':continuation_message(args,record.get('last_submission_readiness'))}],'environments':environment,'effort':args.effort,'summary':'none','serviceTierForTurn':'default'})
                turnid=follow.get('result',{}).get('turn',{}).get('id')
                require(bool(turnid),'neutral continuation did not start')
                record.setdefault('neutral_continuations',[]).append({'prior_completed_turns':continued_turns,'observed_generated_tokens':used,'elapsed_seconds':time.monotonic()-started})
            if proc.returncode is not None:stop='CONTROLLER_EXIT';break
            await asyncio.sleep(.1)
        if stop and tid and turnid:
            try:record['interrupt']=await rpc('turn/interrupt',{'threadId':tid,'turnId':turnid},timeout=2)
            except Exception as e:record['interrupt_error']=str(e)
        # Seal the original candidate before any independent proof engineering.
        record['candidate_frozen_elapsed_seconds'] = time.monotonic()-started
        record['worker_quiescence'] = await adapter.freeze_work()
        final_snapshot=await snapshot_flat(adapter,out/'final-quiesced-snapshot',quiesced=True)
        milestones.append({'fraction':1.0,'observed_generated_tokens':usage[-1]['total']['outputTokens']if usage else None,'elapsed_seconds':time.monotonic()-started,'mode':'FINAL_QUIESCED_SNAPSHOT_NO_MODEL_FEEDBACK','snapshot':final_snapshot})
        exported=out/'submission';exported.mkdir();files=[]
        try:
            lock=await adapter.read_export('/work/submission/LOCK.json');(exported/'LOCK.json').write_bytes(lock);manifest=strict_loads(lock)
            if not isinstance(manifest,dict) or not isinstance(manifest.get('files'),list):raise ValueError('invalid lock schema; final bytes preserved for mechanical format repair')
            seen=set()
            for row in manifest['files']:
                if not isinstance(row,dict) or not {'path','sha256'}.issubset(row) or not isinstance(row['path'],str) or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,127}',row['path']) or row['path']=='LOCK.json' or row['path'] in seen:raise ValueError('invalid/duplicate artifact name')
                seen.add(row['path']);body=await adapter.read_export('/work/submission/'+row['path']);(exported/row['path']).write_bytes(body)
                if digest(body)!=row['sha256']:raise ValueError('artifact hash mismatch')
                files.append({'path':row['path'],'sha256':digest(body),'bytes':len(body)})
            if await adapter.read_export('/work/submission/LOCK.json')!=lock:raise ValueError('lock changed during export')
            record['artifact_export']={'consistent':True,'lock_sha256':digest(lock),'files':files}
        except Exception as e:record['artifact_export']={'consistent':False,'error':str(e),'partial_files':files}
        if not record['artifact_export']['consistent']:
            record['deadline_snapshot'] = await snapshot_flat(adapter,out/'format-recovery-snapshot',quiesced=True)
            record['deadline_snapshot']['controller_locked_incomplete_candidate'] = True
        if args.fixture:
            record['submission_listing_probe']=await adapter.list_submission()
            record['submission_metadata_probe']=await adapter.export_metadata('canary.txt')
        completed=[e.get('params',{}).get('turn',{}) for e in events if e.get('method')=='turn/completed' and e.get('params',{}).get('threadId')==tid]
        record['turn_completion_statuses']=[t.get('status') for t in completed]
        record['mechanical_submission_gate_passed']=not stop and any(t.get('status')=='completed' for t in completed) and record['artifact_export']['consistent'] and bool(usage)
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
        record['stop_reason']=stop;record['usage']=usage;record['foreign_usage']=foreign_usage
        record['planning_milestones']=milestones;record['checkpoints']=checkpoints
        record['mechanical_submission_gate_passed']=bool(record.get('mechanical_submission_gate_passed')) and stop is None
        record['research_stage_submitted']=not args.fixture and record['mechanical_submission_gate_passed'] and record.get('research_submission_ready') is True
        record['assessment_status']='UNREVIEWED' if record['research_stage_submitted'] else ('INTERRUPTED' if stop or record.get('infrastructure_error') else 'FORMAT_REPAIR_PENDING')
        record['milestone_is_hard_cap']=False;record['generated_token_disqualification']=False
        record['operation_limit']=None;record['response_limit']=None;record['wall_admission_limit']=None
        record['mathematical_validity']='NOT_INFERRED_FROM_RESEARCH_SUBMISSION'
        require(digest(Path(__file__).read_bytes())==record['source_sha256'],'controller source changed during execution')
        record['native_stderr_metadata']={'bytes':len(stderr),'sha256':digest(stderr)}
        if args.fixture:(out/'fixture-native.stderr').write_bytes(stderr)
        await adapter.close();record['executor_rpc_counts']=dict(adapter.method_counts);record['raw_program_transport_sha256']=file_sha(out/'executor/transport.json');shutil.rmtree(private);record['private_profile_removed']=not private.exists()
        temp=out/'result.tmp';temp.write_text(json.dumps(sanitize_public(record),indent=2)+'\n');temp.replace(out/'result.json')
        print(json.dumps({k:record.get(k) for k in ['mode','stop_reason','infrastructure_error','elapsed_seconds','operation_count','artifact_export','research_stage_submitted','assessment_status']}))

def validate_lock(args,runtime):
    if args.fixture:return
    require(args.lock is not None,'reviewed new execution lock required')
    lock=strict_json(args.lock)
    require(lock.get('schema')=='FOLLOWUP_EXECUTION_LOCK_V1' and lock.get('reviewed_by')=='/root' and lock.get('status')=='ROOT_APPROVED_FOLLOWUP_STAGE','ROOT reviewed follow-up stage required')
    require(lock.get('run_id')==args.out.name and lock.get('arm')==runtime['arm'],'stage identity differs')
    require(lock.get('model')==args.model and lock.get('effort')==args.effort and lock.get('service_tier')=='default','matched model/effort/default tier required')
    require(lock.get('milestone_policy')=={'initial':args.output,'increment':args.increment,'hard_cap':False,'operation_cap':None,'response_cap':None,'wall_admission_cap':None},'planning milestone policy differs')
    for key,path in [('packet_manifest',args.packet_manifest),('runtime_manifest',args.runtime),('controller_source',Path(__file__).resolve())]:
        row=lock[key];require(Path(row['path']).resolve()==path.resolve() and row['sha256']==file_sha(path),'execution pin differs:'+key)
    preflight=strict_json(core.check_pin(lock['preflight']))
    require(preflight.get('status')=='PASS_EXACT_PACKET_RUNTIME_ACTUAL_OS_AND_MODEL_TOOL_ISOLATION' and preflight.get('controller_sha256')==file_sha(__file__) and preflight.get('packet_manifest_sha256')==file_sha(args.packet_manifest) and preflight.get('runtime_manifest_sha256')==file_sha(args.runtime),'actual exact source/runtime/tool preflight required')
    core.check_pin(lock['protocol'])

def signal_stop(number,frame):
    global TERMINATION_REQUESTED
    TERMINATION_REQUESTED=True

def cli():
    p=argparse.ArgumentParser(description=__doc__,allow_abbrev=False)
    p.add_argument('--packet-manifest',type=Path,required=True);p.add_argument('--runtime',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--lock',type=Path)
    p.add_argument('--fixture',action='store_true');p.add_argument('--check',action='store_true')
    p.add_argument('--model',default='gpt-6.2-sol');p.add_argument('--effort',choices=['low','medium','high','xhigh'],default='high')
    p.add_argument('--initial-milestone',dest='output',type=int,default=500000);p.add_argument('--increment',type=int,default=250000)
    p.add_argument('--memory-gib',type=int,default=64);p.add_argument('--scratch-gib',type=int,default=24);p.add_argument('--cpus',type=int,default=8);p.add_argument('--phase',default='FOLLOWUP_RESEARCH')
    args=p.parse_args();args.out=args.out.resolve();args.packet_manifest=args.packet_manifest.resolve();args.runtime=args.runtime.resolve()
    require(args.out.is_relative_to(S) and not args.out.exists(),'fresh output in new follow-up root required')
    require(args.output>0 and args.increment>0 and 1<=args.memory_gib<=300 and 1<=args.scratch_gib<=300 and 1<=args.cpus<=32,'valid planning/resources required')
    packet,runtime=validate_runtime(args.runtime,args.packet_manifest);args.packet=str(packet)
    validate_lock(args,runtime)
    if args.check:
        print(json.dumps({'status':'PASS_FOLLOWUP_SOURCE_RUNTIME_PACKET_LOCK_METADATA_ONLY','model_calls':0,'milestones_hard_caps':False}));return
    args.wall=86400;args.operations=None;args.responses=None
    args.fixture_hook_fault=False;args.fixture_artifact_name='canary.txt';args.fixture_boundary_steps=1;args.fixture_draft_at=1;args.fixture_budget_prefix=False
    args.per_response_max_output_tokens=None;args.paired_task_seed=0;args.compiler=False;args.python_only=False;args.environment='';args.python_optimization=sys.flags.optimize
    temporary_root=S/'coordinator-private/controller-temp';temporary_root.mkdir(exist_ok=True);tempfile.tempdir=str(temporary_root)
    configure_runtime(runtime,args)
    signal.signal(signal.SIGTERM,signal_stop);signal.signal(signal.SIGINT,signal_stop)
    if not args.fixture:core.check_scope({'memory_gib':args.memory_gib,'cpus':args.cpus})
    asyncio.run(main(args))
if __name__=='__main__':cli()
