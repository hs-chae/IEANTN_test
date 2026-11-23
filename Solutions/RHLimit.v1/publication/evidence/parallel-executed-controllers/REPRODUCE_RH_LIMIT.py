#!/usr/bin/env python3
"""Rebuild all RHLimit routes with at most three independent prover jobs.

The spectral extension waits for pi. Canonical consumers wait for all five
components. Only the main thread writes joined logs and acceptance receipts.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
import argparse,os,shutil,subprocess,sys,time
sys.dont_write_bytecode=True
from prepare_bundle import need,strict,safe,sha,save,verify
GIB=1024**3
COMPONENTS=['pi','analytic-absolute','octic','analytic-box','spectral']
BUDGETS={'pi':48,'analytic-absolute':80,'octic':80,'analytic-box':80,'spectral':80,'canonical':48}


def available_ram():
 return next(int(line.split()[1])*1024 for line in Path('/proc/meminfo').read_text().splitlines()if line.startswith('MemAvailable:'))


def admit(mem_reader=available_ram):
 observed=mem_reader();required=(512+240)*GIB
 need(observed>=required,'host requires 512GiB reserve plus 240GiB admitted group before launching prover routes')
 return {'available_RAM_bytes':observed,'required_RAM_bytes':required,'host_reserve_GiB':512,'admitted_group_GiB':240,'observed_monotonic':time.monotonic()}


def execute(label,route,env):
 start=time.monotonic();run=subprocess.run(route['command'],env=env,text=True,capture_output=True)
 return {'component':label,'command':route['command'],'returncode':run.returncode,'stdout':run.stdout,'stderr':run.stderr,'seconds':time.monotonic()-start}


def collect(out,label,route,result,state):
 # Called only on the scheduling/main thread. Child routes own their own files.
 (out/(label+'.stdout')).write_text(result.pop('stdout'));(out/(label+'.stderr')).write_text(result.pop('stderr'))
 row={**result,'expected_status':route['expected'],'receipt_path':str(route['receipt'])}
 try:
  need(row['returncode']==0,'source child returned nonzero')
  j=strict(route['receipt']);need(j['status']==route['expected'],'unexpected child mathematical status')
  row.update(status=j['status'],receipt_sha256=sha(route['receipt']),accepted=True)
 except Exception as ex:row.update(accepted=False,validation_error=str(ex))
 state['steps'].append(row);save(out/'RESULT.json',state)
 return row['accepted']


def schedule(out,routes,env,state,workers=3,admission=admit):
 need(workers in {1,3},'only one or three workers supported')
 need(set(routes)==set(COMPONENTS+['canonical']),'exact six active child routes')
 for label,route in routes.items():need(route['command']and route['expected']and isinstance(route['receipt'],Path),'complete child route:'+label)
 state.update(max_workers=workers,planned_group_memory_GiB=240,host_reserve_GiB=512,component_memory_caps_GiB=BUDGETS,join_writer='main thread only',resource_admissions=[],schedule_events=[])
 state['resource_admissions'].append(admission());save(out/'RESULT.json',state)
 pending=['pi','analytic-absolute','octic','analytic-box'];inflight={};accepted=set();failed=False
 with ThreadPoolExecutor(max_workers=workers)as pool:
  while pending or inflight:
   while pending and len(inflight)<workers and not failed:
    label=pending.pop(0)
    try:
     reservation=sum(BUDGETS[x]for x in inflight.values())+BUDGETS[label];need(reservation<=240,'concurrent resource reservation exceeds240GiB')
     state['resource_admissions'].append(admission())
     state['schedule_events'].append({'component':label,'event':'submitted','monotonic':time.monotonic(),'reserved_group_GiB':reservation})
     inflight[pool.submit(execute,label,routes[label],env)]=label;save(out/'RESULT.json',state)
    except Exception as ex:
     failed=True;state['steps'].append({'component':label,'accepted':False,'validation_error':str(ex),'launched':False});save(out/'RESULT.json',state)
   if not inflight:break
   completed,_=wait(inflight,return_when=FIRST_COMPLETED)
   for future in sorted(completed,key=lambda f:inflight[f]):
    label=inflight.pop(future)
    try:result=future.result()
    except Exception as ex:result={'component':label,'command':routes[label]['command'],'returncode':None,'stdout':'','stderr':str(ex),'seconds':None}
    good=collect(out,label,routes[label],result,state)
    state['schedule_events'].append({'component':label,'event':'accepted'if good else'rejected','monotonic':time.monotonic()})
    if good:accepted.add(label);print('PASS_TOY'if state.get('mathematical_replay_performed')is False else'PASS',label,flush=True)
    else:failed=True
    if label=='pi'and good and not failed:pending.insert(0,'spectral')
   if failed:
    # Already running source jobs finish and retain receipts. No new work starts.
    state['not_launched_after_failure']=list(pending);pending.clear()
   save(out/'RESULT.json',state)
 need(not failed and accepted==set(COMPONENTS),'one or more source routes failed; completed receipts preserved and canonical route was not launched')
 state['resource_admissions'].append(admission());state['schedule_events'].append({'component':'canonical','event':'submitted','monotonic':time.monotonic(),'reserved_group_GiB':BUDGETS['canonical']});save(out/'RESULT.json',state)
 result=execute('canonical',routes['canonical'],env);good=collect(out,'canonical',routes['canonical'],result,state)
 state['schedule_events'].append({'component':'canonical','event':'accepted'if good else'rejected','monotonic':time.monotonic()});save(out/'RESULT.json',state)
 need(good,'final canonical route failed')


def toy_self_test(out):
 # Explicit toy status; this path can never issue mathematical replay acceptance.
 need(not out.exists(),'fresh toy controls output');out.mkdir(parents=True);source=out/'toy_child.py'
 source.write_text('''from pathlib import Path
import argparse,json,os,time
p=argparse.ArgumentParser();p.add_argument('--label');p.add_argument('--out');p.add_argument('--events');p.add_argument('--deps',nargs='*',default=[]);p.add_argument('--behavior',default='pass');p.add_argument('--barrier',type=int,default=1);a=p.parse_args();o=Path(a.out);o.mkdir()
def event(kind):
 raw=(json.dumps({'label':a.label,'event':kind,'time_ns':time.monotonic_ns()})+'\\n').encode();fd=os.open(a.events,os.O_WRONLY|os.O_CREAT|os.O_APPEND,0o600);os.write(fd,raw);os.close(fd)
event('start')
(Path(a.events).parent/(a.label+'.started')).touch(exist_ok=False)
deadline=time.monotonic()+10
while len(list(Path(a.events).parent.glob('*.started')))<a.barrier:
 if time.monotonic()>deadline:raise ValueError('toy concurrency barrier timed out')
 time.sleep(.005)
for raw in a.deps:
 q=Path(raw)/'RESULT.json'
 if not q.is_file()or json.loads(q.read_text())['status']!='TOY_COMPONENT_PASS':raise ValueError('dependency started too early')
time.sleep(.12 if a.label=='pi'else .06)
if a.behavior=='missing':event('end');raise SystemExit(0)
(o/'RESULT.json').write_text(json.dumps({'status':'TOY_COMPONENT_PASS'if a.behavior=='pass'else'TOY_WRONG_STATUS'}))
event('end')
raise SystemExit(7 if a.behavior=='fail'else 0)
''')
 cases=[]
 for name,workers,bad,behavior,low in [('parallel',3,None,'pass',False),('serial',1,None,'pass',False),('pi-failure',3,'pi','fail',False),('status-failure',3,'analytic-box','wrong',False),('missing-receipt',3,'octic','missing',False),('memory-admission',3,None,'pass',True)]:
  dest=out/name;dest.mkdir();events=dest/'events.jsonl';routes={}
  for label in COMPONENTS+['canonical']:
   deps=['pi']if label=='spectral'else COMPONENTS if label=='canonical'else[]
   cmd=[sys.executable,str(source),'--label',label,'--out',str(dest/label),'--events',str(events),'--deps',*[str(dest/x)for x in deps],'--behavior',behavior if label==bad else'pass','--barrier',str(workers)]
   routes[label]={'command':cmd,'expected':'TOY_COMPONENT_PASS','receipt':dest/label/'RESULT.json'}
  state={'status':'TOY_RUNNING','steps':[],'mathematical_replay_performed':False};good=False
  try:schedule(dest,routes,os.environ.copy(),state,workers,lambda:admit(lambda:0 if low else(1024*GIB)));good=True
  except Exception as ex:state['caught_expected_or_actual_error']=str(ex)
  expected=bad is None and not low;need(good==expected,'toy scheduler accepted wrong result:'+name)
  trace=[]
  if events.exists():
   import json
   trace=[json.loads(x)for x in events.read_text().splitlines()]
  active=set();max_active=0;began={};ended={}
  for event in sorted(trace,key=lambda r:r['time_ns']):
   label=event['label']
   if event['event']=='start':need(label not in active,'duplicate active toy');active.add(label);began[label]=event['time_ns'];max_active=max(max_active,len(active))
   else:need(label in active,'toy end without start');active.remove(label);ended[label]=event['time_ns']
  need(not active and max_active<=workers,'toy child concurrency bound violated')
  if good:
   need(set(began)==set(routes),'toy source route omitted');need(ended['pi']<=began['spectral'],'spectral started beforepi')
   need(all(ended[x]<=began['canonical']for x in COMPONENTS),'canonical started beforeallfive')
   need(max_active==workers,'toy did not actually exercise requested concurrency')
  else:need('canonical'not in began,'canonical launched after failure')
  if low:need(not began,'low-memory guard launched child')
  state.update(status='PASS_TOY_EXPECTED_SCHEDULING_AND_FAILURE_BEHAVIOR',max_observed_children=max_active,expected_success=expected,events=trace);save(dest/'RESULT.json',state);cases.append({'case':name,'receipt_sha256':sha(dest/'RESULT.json'),'max_observed_children':max_active})
 save(out/'TOY_RESULT.json',{'status':'PASS_TOY_PARALLEL_SERIAL_FAILURE_AND_MEMORY_CONTROLS','mathematical_replay_performed':False,'cases':cases,'controller_sha256':sha(Path(__file__))});print('PASS_TOY_PARALLEL_SERIAL_FAILURE_AND_MEMORY_CONTROLS')


def main():
 here=Path(__file__).resolve().parent;net=here/'network';s=net/'Solutions/RHLimit.v1'
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path);p.add_argument('--out',type=Path,required=True);p.add_argument('--check',action='store_true');p.add_argument('--serial',action='store_true');p.add_argument('--self-test',action='store_true');a=p.parse_args()
 if a.self_test:
  need(a.context is None and not a.check and not a.serial,'toy test runs parallel and serial internally, without production context');toy_self_test(a.out.resolve());return
 need(a.context is not None,'--context required for actual source replay');need(sys.version_info>=(3,11),'Python3.11 or newer required');verify(here);out=a.out.resolve();need(not out.exists()and not out.is_relative_to(here),'fresh scratch outside package required')
 for cmd in ['git','gcc']:need(shutil.which(cmd),'missing system prerequisite:'+cmd)
 need(Path('/usr/bin/time').is_file(),'GNUtime required');ctx=strict(a.context);reference=strict(net/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')
 need(sha(Path(ctx['compiler']))==ctx['compiler_sha256']==reference['compiler_sha256'],'exact compiler identity')
 need([(x['name'],x['revision'])for x in ctx['generic_dependencies']]==[(x['name'],x['revision'])for x in reference['generic_dependencies']],'generic source pins')
 for d in ctx['generic_dependencies']:
  need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=d['path'],text=True).strip()==d['revision'],'generic checkout revision')
  need(subprocess.run(['git','diff','--quiet','HEAD','--'],cwd=d['path']).returncode==0,'modified pinned generic source')
 final=strict(here/'REPLAY_ROUTES.json');need(final['schema']=='RH_LIMIT_FINAL_CANONICAL_REPLAY_ROUTE_V1','canonical route schema');can=final['canonical'];script=here/safe(can['script']);need(script.is_file(),'missing final canonical replay script')
 need(isinstance(can['argv'],list)and all(isinstance(x,str)for x in can['argv']),'structured canonical arguments');need(can['expected_status']and safe(can['receipt']),'canonical final gate')
 specs=[('pi',s/'scripts/reproduce_pi_complete.py','PASS_COLD_ALL_261_SOURCE_MODULES_AND_FINAL_PI_CONSUMERS'),('analytic-absolute',s/'analytic/reproduce_absolute.py','PASS_SOURCE_LINKED_ACTUAL_OCTIC_ABSOLUTE_STIELTJES'),('octic',s/'octic/reproduce.py','PASS_COMPLETE_SAME_SOURCE111_PLUS_FOUR_CLOSED_OCTIC_CONTRACTS'),('analytic-box',s/'analytic/reproduce.py','PASS_ACTUAL_STIELTJES_CLOSURE_AND_SOURCE_LINKED_FOUR_INPUT_PNT'),('spectral',s/'spectral/reproduce_cold_append.py','PASS_COLD261_PLUS_ALL55_SPECTRAL_SOURCES_AND_ACTUAL_CONSUMERS')]
 routes={}
 for label,path,expected in specs:
  need(path.is_file(),'active proof route absent:'+str(path));cmd=[sys.executable,str(path),'--out',str(out/label)]
  if label=='spectral':cmd+=['--basis',str(out/'pi')]
  routes[label]={'command':cmd,'expected':expected,'receipt':out/label/'RESULT.json'}
 replacements={'{pi}':str(out/'pi'),'{spectral}':str(out/'spectral'),'{analytic-box}':str(out/'analytic-box'),'{analytic-absolute}':str(out/'analytic-absolute'),'{octic}':str(out/'octic'),'{out}':str(out/'canonical'),'{context}':str(a.context.resolve()),'{network}':str(net)};args=[]
 for raw in can['argv']:
  value=raw
  for token,repl in replacements.items():value=value.replace(token,repl)
  need('{'not in value and'}'not in value,'unknown canonical argument placeholder');args.append(value)
 routes['canonical']={'command':[sys.executable,str(script),*args],'expected':can['expected_status'],'receipt':out/'canonical'/safe(can['receipt'])}
 env=os.environ.copy();env['IEANTN_GENERIC_CONTEXT']=str(a.context.resolve());env['PYTHONDONTWRITEBYTECODE']='1';env.pop('LEAN_PATH',None);env.pop('PYTHONOPTIMIZE',None)
 out.mkdir(parents=True);start=time.monotonic();state={'status':'RUNNING','controller_sha256':sha(Path(__file__)),'bundle_manifest_sha256':sha(here/'BUNDLE_MANIFEST.json'),'generic_context_sha256':sha(a.context),'route_controller_sha256':{label:sha(Path(route['command'][1]))for label,route in routes.items()},'steps':[]};save(out/'RESULT.json',state)
 if a.check:
  for label,path,_ in specs:
   if label=='spectral':continue
   cp=subprocess.run([sys.executable,str(path),'--out',str(out/(label+'-unused')),'--check'],env=env,text=True,capture_output=True);(out/(label+'.stdout')).write_text(cp.stdout);(out/(label+'.stderr')).write_text(cp.stderr);need(cp.returncode==0,'child source/dependency preflight:'+label)
  state.update(status='PASS_PACKAGE_AND_FOUR_BANK_FREE_SOURCE_PREFLIGHTS_ONLY',mathematical_replay_performed=False,bank_dependent_routes_pending=['spectral','canonical']);save(out/'RESULT.json',state);print(state['status']);return
 try:
  schedule(out,routes,env,state,1 if a.serial else 3)
  verify(here);state.update(status='PASS_ALL_RH_LIMIT_FRESH_SOURCE_NUMERICAL_AND_CANONICAL_ROUTES',seconds=time.monotonic()-start,planned_source_compile_commands=620,unique_pi_spectral_canonical_source_modules=340,whole_pipeline_source_first_PV=False,trust='Only identified actualC components are source-firstPV; allnew interval/kernel proofs ordinary kernel mathematics; RH/literature/open analytic inputs remain explicit.')
  save(out/'RESULT.json',state);print(state['status'])
 except BaseException as ex:state.update(status='FAIL_OR_PARTIAL_NO_FINAL_REPLAY_ACCEPTANCE',error=str(ex),seconds=time.monotonic()-start);save(out/'RESULT.json',state);raise
if __name__=='__main__':main()
