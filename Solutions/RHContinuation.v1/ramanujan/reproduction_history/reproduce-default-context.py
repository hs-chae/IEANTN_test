#!/usr/bin/env python3
"""Rebuild the actual bridge-free Ramanujan consumers from pinned source.

Default builds the full historical146-module source/checker closure first.
--base-replay explicitly reuses a separately completed fresh source replay.
No original application/checker objects or native numerical facts are admitted.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,shutil,subprocess,sys,time
S=Path(__file__).resolve().parent
MODULES=['LiSeriesDerivative','LiPVDefinition','LiRelativeSeries','ActualAnchors',
 'ActualGlobalW','ActualAnalytic','ActualPrimePowers','ActualFinite','ActualTail','ActualResult']
def need(ok,msg):
 if not ok:raise ValueError(msg)
def read(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,
  parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def save(p,j):
 tmp=p.with_suffix(p.suffix+'.tmp');tmp.write_text(json.dumps(j,indent=2)+'\n');os.replace(tmp,p)
def base_check(B,package):
 j=read(B/'RESULT.json');need(j['status']=='PASS_PORTABLE_ALL_APPLICATION_AND_LEANCERT_SOURCE_GENERIC_CACHE_ONLY','base did not finish')
 need(j['application_cached_objects_used']is False and j['leancert_cached_objects_used']is False and j['new_proof_cached_objects_used']is False,'base source-only flags')
 need(len(j['modules'])==146,'complete146-module base')
 need(j['source_manifest_sha256']==sha(package/'SOURCE_MANIFEST.json'),'base source selection changed')
 need(sha(j['compiler'])==j['compiler_sha256'],'compiler changed')
 sources={x['path']:x for x in read(package/'SOURCE_MANIFEST.json')['files']}
 records=[]
 for row in j['modules']:
  need(row['returncode']==0,'failed base module')
  rel=Path(*row['module'].split('.')).with_suffix('.lean');src=B/'source'/rel;obj=B/'objects'/rel.with_suffix('.olean')
  need(src.is_file()and obj.is_file()and sha(src)==row['source_sha256'],'base source or object missing/changed')
  need(sha(package/'source'/rel)==row['source_sha256'],'base source differs from pinned publication')
  records.append({'module':row['module'],'source_sha256':row['source_sha256'],'object_sha256':sha(obj),'object_bytes':obj.stat().st_size})
 return j,records
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path);p.add_argument('--base-replay',type=Path);p.add_argument('--check',action='store_true');a=p.parse_args()
package=S.parents[1]/'RHExposureStudy.v1/Ramanujan640'
need(package.is_dir(),'run inside the published IEANTN checkout or restore the full study tree')
ctx=read(S.parent/'scripts/GENERIC_CONTEXT.json');need(sha(ctx['compiler'])==ctx['compiler_sha256'],'compiler pin changed')
if a.check:
 if a.base_replay:base_check(a.base_replay.resolve(),package)
 print('PASS_SOURCE_LAYOUT_AND_COMPILER_PINS_ONLY');raise SystemExit(0)
need(a.out is not None,'--out required');O=a.out.resolve();need(not O.exists(),'fresh output required')
for name in ['source','objects','logs','resources']:(O/name).mkdir(parents=True,exist_ok=True)
started=time.monotonic();result={'schema':'RH_RAMANUJAN_ACTUAL_SOURCE_REPLAY_V1','status':'RUNNING','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'compiler':ctx['compiler'],'compiler_sha256':ctx['compiler_sha256'],'modules':[],'source_first_PV':False,'actual_quantity':'actual IEANTN primeCounting and principal-value li','mathematical_inputs':['MathlibRH','ButheTable2','ButheEq1.8','ButheEq1.9','ButheEq1.10','Buthe2016Eq7.2'],'li_definition_hypotheses':[]}
save(O/'RESULT.json',result)
try:
 if a.base_replay:B=a.base_replay.resolve();result['base_mode']='EXPLICIT_PREVIOUS_COMPLETED_FRESH_SOURCE_REPLAY'
 else:
  B=O/'base';cmd=[sys.executable,str(package/'REPRODUCE.py'),'--out',str(B)];r=subprocess.run(cmd,cwd=package,text=True,capture_output=True);(O/'logs/base.stdout').write_text(r.stdout);(O/'logs/base.stderr').write_text(r.stderr);need(r.returncode==0,'base fresh source replay failed');result['base_mode']='REBUILT_ALL146_SOURCE_MODULES_IN_THIS_COMMAND'
 bj,br=base_check(B,package);result['base_replay']=str(B);result['base_result_sha256']=sha(B/'RESULT.json');result['base_objects']=br
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(O/'objects'),str(B/'objects'),*ctx['generic_libraries']])
 allowed=[(O/'objects').resolve(),(B/'objects').resolve(),Path(ctx['compiler']).resolve().parent.parent/'lib/lean',*[Path(x).resolve()for x in ctx['generic_libraries']]]
 for mod in MODULES:
  src=S/(mod+'.lean');frozen=O/'source'/src.name;shutil.copyfile(src,frozen);t=time.monotonic();cmd=[ctx['compiler'],'--root='+str(O/'source'),'-j8','-o',str(O/'objects'/(mod+'.olean')),str(frozen)];res=O/'resources'/(mod+'.txt')
  run=subprocess.run(['/usr/bin/time','-f','%e %M','-o',str(res),*cmd],cwd=O/'source',env=env,text=True,capture_output=True)
  stdout=O/'logs'/(mod+'.stdout');stderr=O/'logs'/(mod+'.stderr');stdout.write_text(run.stdout);stderr.write_text(run.stderr)
  row={'module':mod,'source_sha256':sha(frozen),'command':cmd,'returncode':run.returncode,'seconds':time.monotonic()-t,'stdout_sha256':sha(stdout),'stderr_sha256':sha(stderr),'resources':res.read_text()if res.exists()else None};result['modules'].append(row);save(O/'RESULT.json',result)
  need(run.returncode==0,'Lean failed:'+mod);need(sha(src)==row['source_sha256'],'source changed while compiling')
  need('sorryAx'not in run.stdout and 'Lean.ofReduce'not in run.stdout,'unaccepted execution/proof axiom')
  probe=subprocess.run([ctx['compiler'],'--root='+str(O/'source'),'--deps',str(frozen)],cwd=O/'source',env=env,text=True,capture_output=True)
  need(probe.returncode==0,'dependency probe failed:'+mod)
  for line in probe.stdout.splitlines():
   dep=Path(line.strip()).resolve();need(any(dep.is_relative_to(root)for root in allowed),'undeclared object dependency:'+str(dep))
  row['dependency_probe']=probe.stdout;row['object_sha256']=sha(O/'objects'/(mod+'.olean'));row['object_bytes']=(O/'objects'/(mod+'.olean')).stat().st_size
  save(O/'RESULT.json',result);print('PASS',mod,round(row['seconds'],2),flush=True)
 final=(O/'logs/ActualResult.stdout').read_text()
 for name in ['actual_ramanujan_640b','actual_ramanujan_profile','actual_gap_profile']:
  matches=[line for line in final.splitlines()if "RHContinuation.Ramanujan."+name+"' depends on axioms:"in line]
  need(len(matches)==1,'missing exact final axiom audit:'+name)
  values=re.findall(r'\[(.*?)\]',matches[0]);need(len(values)==1 and set(x.strip()for x in values[0].split(','))=={'propext','Classical.choice','Quot.sound'},'final axiom set differs')
 result['status']='PASS_COMPLETE_BRIDGE_FREE_ACTUAL_RAMANUJAN_SOURCE_CLOSURE';result['elapsed_seconds']=time.monotonic()-started;result['completed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save(O/'RESULT.json',result)
 print(result['status'],str(O/'RESULT.json'),flush=True)
except BaseException as ex:
 result['status']='FAIL';result['error']=str(ex);result['elapsed_seconds']=time.monotonic()-started;save(O/'RESULT.json',result);raise
