#!/usr/bin/env python3
"""Fail-closed independent receipt/artifact validation (normal/-O/-OO)."""
from pathlib import Path
import argparse,hashlib,json,os,re,sys,datetime
S=Path(__file__).resolve().parent
EXPECTED=['LiSeriesDerivative','LiPVDefinition','LiRelativeSeries','ActualAnchors','ActualGlobalW','ActualAnalytic','ActualPrimePowers','ActualFinite','ActualTail','ActualResult']
def need(c,m):
 if not c:raise ValueError(m)
def read(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate key:'+k);d[k]=v
  return d
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--run-dir',type=Path,required=True);p.add_argument('--receipt',type=Path);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
need(not a.out.exists(),'fresh output required');R=a.run_dir.resolve();P=a.receipt.resolve()if a.receipt else R/'RESULT.json';j=read(P)
need(j['schema']=='RH_RAMANUJAN_ACTUAL_SOURCE_REPLAY_V1','schema');need(j['status']=='PASS_COMPLETE_BRIDGE_FREE_ACTUAL_RAMANUJAN_SOURCE_CLOSURE','incomplete proof build');need(j['source_first_PV']is False,'mislabelled whole pipeline PV');need(j['li_definition_hypotheses']==[],'li premises introduced')
need([r['module']for r in j['modules']]==EXPECTED,'exact proof closure');need(sha(j['compiler'])==j['compiler_sha256'],'compiler identity')
B=Path(j['base_replay']).resolve();bj=read(B/'RESULT.json');need(sha(B/'RESULT.json')==j['base_result_sha256'],'base receipt changed');need(bj['status']=='PASS_PORTABLE_ALL_APPLICATION_AND_LEANCERT_SOURCE_GENERIC_CACHE_ONLY','base build incomplete');need(len(j['base_objects'])==146 and len(bj['modules'])==146,'base coverage')
for key in ['application_cached_objects_used','leancert_cached_objects_used','new_proof_cached_objects_used']:need(bj[key]is False,'old object cache admitted')
need(len({x['module']for x in j['base_objects']})==146,'duplicate base modules')
for row in j['base_objects']:
 rel=Path(*row['module'].split('.'));need(sha((B/'source'/rel).with_suffix('.lean'))==row['source_sha256'],'base source changed');need(sha((B/'objects'/rel).with_suffix('.olean'))==row['object_sha256'],'base object changed')
ctx=read(Path(os.environ.get('IEANTN_GENERIC_CONTEXT',S.parent/'scripts/GENERIC_CONTEXT.json')));allowed=[(R/'objects').resolve(),(B/'objects').resolve(),Path(j['compiler']).resolve().parent.parent/'lib/lean',*[Path(x).resolve()for x in ctx['generic_libraries']]];peak=0;seconds=0
for row in j['modules']:
 m=row['module'];need(row['returncode']==0,'module failed:'+m);src=R/'source'/(m+'.lean');obj=R/'objects'/(m+'.olean');out=R/'logs'/(m+'.stdout');err=R/'logs'/(m+'.stderr')
 need(sha(src)==row['source_sha256']and sha(S/src.name)==row['source_sha256'],'proof source identity:'+m);need(sha(obj)==row['object_sha256'],'object identity:'+m);need(sha(out)==row['stdout_sha256']and sha(err)==row['stderr_sha256'],'execution logs:'+m);need('sorryAx'not in out.read_text()and 'Lean.ofReduce'not in out.read_text(),'unaccepted axioms:'+m)
 probe=row['dependency_probe'].splitlines();need(len(probe)>0,'empty dependency probe')
 for dep in probe:need(any(Path(dep.strip()).resolve().is_relative_to(root)for root in allowed),'undeclared object dependency')
 vals=row['resources'].split();need(len(vals)==2,'resource format');need(re.fullmatch(r'[0-9]+(?:\.[0-9]+)?',vals[0])is not None and vals[1].isdecimal(),'resource numbers');peak=max(peak,int(vals[1])*1024);seconds+=float(vals[0])
text=(R/'logs/ActualResult.stdout').read_text()
for name in ['actual_ramanujan_640b','actual_ramanujan_profile','actual_gap_profile']:
 line=[s for s in text.splitlines()if "RHContinuation.Ramanujan."+name+"' depends on axioms:"in s];need(len(line)==1,'missing axiom theorem');parts=re.findall(r'\[(.*?)\]',line[0]);need(len(parts)==1 and set(x.strip()for x in parts[0].split(','))=={'propext','Classical.choice','Quot.sound'},'axiom set')
record={'status':'PASS_EXACT_SOURCES_ARTIFACTS_AND_FINAL_PROOF_AUDIT','validator_sha256':sha(Path(__file__)),'run_receipt_sha256':sha(P),'python_optimization':sys.flags.optimize,'modules':len(j['modules']),'fresh_base_modules':146,'max_compiler_worker_peak_RSS_bytes':peak,'sum_module_wall_seconds':seconds,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};a.out.parent.mkdir(parents=True,exist_ok=True);tmp=a.out.with_suffix('.pending');tmp.write_text(json.dumps(record,indent=2)+'\n');os.replace(tmp,a.out);print(json.dumps(record))
