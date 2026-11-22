#!/usr/bin/env python3
"""Fresh actual-C/Mellin/PNT network replay, all application sources rebuilt.
Only the pinned compiler and generic Mathlib/dependency caches may be reused.
The numeric source identity and the validator identity are recorded separately.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
import argparse,hashlib,json,os,re,resource,subprocess,sys,time
B=Path(__file__).resolve().parent;N=B.parents[2];PV=N/'Solutions/RamanujanSourcePV.v1'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 def unique(rows):
  result={}
  for k,v in rows:need(k not in result,'duplicate JSON key');result[k]=v
  return result
 return json.loads(Path(p).read_bytes(),object_pairs_hook=unique,
  parse_constant=lambda x:(_ for _ in()).throw(ValueError('nonfinite JSON')))
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();O=a.out.resolve();need(not O.exists(),'fresh output required');O.mkdir(parents=True);start=time.monotonic();pinned=read(B.parent/'scripts/GENERIC_CONTEXT.json');context_path=Path(os.environ.get('IEANTN_GENERIC_CONTEXT',str(B.parent/'scripts/GENERIC_CONTEXT.json')));ctx=read(context_path);need(ctx['compiler_sha256']==pinned['compiler_sha256']and[(r['name'],r['revision'])for r in ctx['generic_dependencies']]==[(r['name'],r['revision'])for r in pinned['generic_dependencies']],'relocation changes pinned identities');need(sha(ctx['compiler'])==ctx['compiler_sha256'],'compiler identity')
for dep in ctx['generic_dependencies']:
 actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=dep['path'],text=True).strip()
 need(actual==dep['revision'],'generic dependency identity:'+dep['name'])
# Follow every actual active child CLI in all optimization modes, including rejection paths.
def numeric_mode(mode):
 flags=[]if mode==0 else['-O']if mode==1 else['-OO'];rows=[]
 for script in ['native_log_workload.py','box_mellin_trapezoid.py','box_mellin_series.py']:
  name=script.removesuffix('.py')+'-'+str(mode);dest=O/name if script.startswith('native')else O/(name+'.json');res=O/(name+'.resources');cmd=['/usr/bin/time','-v','-o',str(res),sys.executable,*flags,str(B/script),'--out',str(dest)];r=subprocess.run(cmd,cwd=B,text=True,capture_output=True);(O/(name+'.stdout')).write_text(r.stdout);(O/(name+'.stderr')).write_text(r.stderr);need(r.returncode==0,'numeric child failed:'+name)
  receipt=dest/'NATIVE.json'if script.startswith('native')else dest;j=read(receipt);need(j['python_optimization']==mode,'optimization identity')
  if script.startswith('native'):
   need(j['status']=='NATIVE_SOURCE_BUILD_RUN_COMPLETE_FORMAL_ACCEPTANCE_SEPARATE','native status');need(j['harness_sha256']==sha(B/script),'native harness identity');need(j['C_source_sha256']==sha(PV/'c/verified_finite_log.c'),'C source identity');need([v['n']for v in j['rows']]==list(range(2,129)),'all127 nontrivial input calls');need(sha(dest/'CLogNativeRows.lean')==sha(B/'CLogNativeRows.lean'),'native rows equal source-proved canonical rows')
  else:
   need(j['status']=='PASS'and j['source_sha256']==sha(B/script)and j['rational_sha256']==sha(B/'rational.py'),'directed source identity');need('UPPER-BOUND EXPRESSION'in j['interval_semantics'],'one-sided moment semantics');need(Fraction(j['actual_J1_upper_expression']['lower'])<=Fraction(j['actual_J1_upper_expression']['upper'])<Fraction('.70875'if'trapezoid'in script else'.710'),'actual upper-expression cap')
  controls=[]
  for label,args in [('missing-output',[]),('unknown-argument',['--out',str(O/'never-produced'),'--unexpected']),('existing-output',['--out',str(dest)])]:
   invalid=subprocess.run([sys.executable,*flags,str(B/script),*args],cwd=B,text=True,capture_output=True);need(invalid.returncode!=0,'invalid CLI accepted:'+name+':'+label);controls.append({'label':label,'returncode':invalid.returncode,'stderr':invalid.stderr})
  (O/(name+'-controls.json')).write_text(json.dumps(controls,indent=2)+'\n');m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',res.read_text());rows.append({'script':script,'mode':mode,'receipt':str(receipt),'receipt_sha256':sha(receipt),'peak_RSS_kib':int(m[1])if m else None,'rejected_invalid_CLI_routes':len(controls)})
 return rows
with ThreadPoolExecutor(max_workers=3)as pool:numeric=[row for group in pool.map(numeric_mode,[0,1,2])for row in group]
for script in ['box_mellin_trapezoid.py','box_mellin_series.py']:
 values=[read(r['receipt'])['actual_J1_upper_expression']for r in numeric if r['script']==script];need(values[0]==values[1]==values[2],'exact expression mode invariance')
native=[read(r['receipt'])for r in numeric if r['script']=='native_log_workload.py'];need(native[0]['rows']==native[1]['rows']==native[2]['rows'],'actual C outputs mode invariant')
# Discover the entire source closure, never substitute historical application oleans.
roots=[B,PV,N,B.parent/'integration/source'];seen={};order=[]
def visit(module):
 if module=='Mathlib'or module.startswith(('Mathlib.','Init','Lean','Std')):return
 if module in seen:return
 candidates=([(N/'Solutions/RHSmoothingInputs.v1/Solution.lean',N/'Solutions/RHSmoothingInputs.v1')]if module=='Solution'else[])+[(root/(module.replace('.','/')+'.lean'),root)for root in roots];found=[item for item in candidates if item[0].is_file()];need(bool(found),'missing application source:'+module);src,root=found[0];seen[module]=(src,root)
 for line in src.read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():
    if dep.startswith('--'):break
    visit(dep)
 order.append(module)
visit('Solution');sources=[{'module':m,'source':str(seen[m][0]),'sha256':sha(seen[m][0])}for m in order];(O/'SOURCE_CLOSURE.json').write_text(json.dumps(sources,indent=2)+'\n');frozen=O/'frozen-source';frozen.mkdir();frozen_rows=[]
for entry in sources:
 target=frozen/(entry['module'].replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(Path(entry['source']).read_bytes());need(sha(target)==entry['sha256'],'source freeze identity');frozen_rows.append({**entry,'frozen':str(target)})
(frozen/'c').mkdir();(frozen/'c/verified_finite_log.c').write_bytes((PV/'c/verified_finite_log.c').read_bytes());(O/'FROZEN_SOURCE_CLOSURE.json').write_text(json.dumps(frozen_rows,indent=2)+'\n');(O/'reproduce_clog.executed.py').write_bytes(Path(__file__).read_bytes());objects=O/'objects';objects.mkdir();logs=O/'logs';logs.mkdir();env=os.environ.copy();env['LEAN_PATH']=':'.join([str(objects),*ctx['generic_libraries']]);compiled=[]
for module in order:
 src,root=seen[module];obj=objects/(module.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);limit=(48 if module=='RamanujanPV.FiniteLogSource' else 16)*1024**3;available=int(next(v.split()[1]for v in Path('/proc/meminfo').read_text().splitlines()if v.startswith('MemAvailable:')))*1024;need(available>=512*1024**3+limit,'host reserve plus admitted process limit');before=sha(src);cmd=['/usr/bin/time','-v','-o',str(logs/(module+'.resources')),ctx['compiler'],'-j1','-R',str(root),'-o',str(obj),str(src)];t=time.monotonic()
 def limits():resource.setrlimit(resource.RLIMIT_AS,(limit,limit))
 r=subprocess.run(cmd,cwd=root,env=env,text=True,capture_output=True,preexec_fn=limits);(logs/(module+'.stdout')).write_text(r.stdout);(logs/(module+'.stderr')).write_text(r.stderr);need(sha(src)==before,'source changed during compile');compiled.append({'module':module,'source_sha256':before,'returncode':r.returncode,'seconds':time.monotonic()-t,'command':cmd,'memory_limit_bytes':limit,'host_available_before':available});(O/'BUILD.json').write_text(json.dumps({'status':'RUNNING'if r.returncode==0 else'FAILED','modules':compiled},indent=2)+'\n');print(module,r.returncode,round(compiled[-1]['seconds'],2),flush=True);need(r.returncode==0,'source compile failed:'+module)
(O/'BUILD.json').write_text(json.dumps({'status':'PASS','modules':compiled},indent=2)+'\n')
raw=(logs/'CLogMomentNetwork.stdout').read_text();matches=re.findall(r"'RHContinuation.CLogMomentNetwork.box_moments' depends on axioms: \[([^\]]*)\]",raw);need(len(matches)==1,'unique final actual node theorem axiom audit');need({v.strip()for v in matches[0].split(',')}=={'propext','Classical.choice','Quot.sound'},'unexpected final theorem axiom');need('sorryAx'not in raw and 'Lean.ofReduceBool'not in raw,'native or sorry final fact');
for theorem,content in [('RHContinuation.CLogMomentNetwork.box_psi',raw),('RHSmoothingInputs.v1.challenge_box_moments',(logs/'Solution.stdout').read_text())]:
 hits=re.findall(r"'"+re.escape(theorem)+r"' depends on axioms: \[([^\]]*)\]",content);need(len(hits)==1 and{v.strip()for v in hits[0].split(',')}=={'propext','Classical.choice','Quot.sound'},'actual composed consumer/wrapper axiom audit:'+theorem)
need(sha(PV/'c/verified_finite_log.c')==native[0]['C_source_sha256'],'source unchanged through acceptance')
peak=[]
for f in logs.glob('*.resources'):
 m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',f.read_text());peak.append(int(m[1])if m else 0)
result={'schema':'SOURCE_FIRST_C_LOG_TO_ACTUAL_PSI_NETWORK_REPLAY_V2','status':'PASS','elapsed_seconds':time.monotonic()-start,'numeric_rows':numeric,'actual_child_routes':len(numeric),'rejected_invalid_CLI_routes':sum(r['rejected_invalid_CLI_routes']for r in numeric),'application_source_modules':len(compiled),'no_prebuilt_application_objects':True,'compiler_sha256':ctx['compiler_sha256'],'C_source_sha256':native[0]['C_source_sha256'],'native_binary_sha256':[j['binary_sha256']for j in native],'source_closure_sha256':sha(O/'SOURCE_CLOSURE.json'),'validator_sha256':sha(__file__),'max_Lean_peak_RSS_kib':max(peak),'OOM_events':0,'accepted_numeric_cap':'567/800','final_theorem':'RHContinuation.CLogMomentNetwork.box_psi','canonical_node_wrapper':'RHSmoothingInputs.v1.challenge_box_moments','generic_context_sha256':sha(context_path),'generic_context_file':str(context_path),'remaining_analytic_inputs':['RHSmoothingInputs.v1.box_explicit_formula','RHSmoothingInputs.v1.box_zero_estimate','BoxMellinInputs.v1.first_moment','BoxMellinInputs.v1.second_moment_identity','BoxMellinInputs.v1.stieltjes_trapezoid'],'trust_boundary':'Actual restrictedC function source/AST/arithmetic/termination correctness and all127 required returned log words linked to kernel aggregation and actual moment node. Mellin identities and trapezoid limit remain analytic premises. Python harness, GCC/ABI/runtime/OS/hardware association is documented execution trust; this is not source verification of the Python harness or whole analytic quadrature.'};tmp=O/'RESULT.pending.json';tmp.write_text(json.dumps(result,indent=2)+'\n');os.replace(tmp,O/'RESULT.json');print(json.dumps({'status':'PASS','modules':len(compiled),'seconds':result['elapsed_seconds'],'peak_RSS_kib':max(peak)},indent=2))
