#!/usr/bin/env python3
"""Validate the seven-module selected C-linked full-profile proof closure."""
from pathlib import Path
import argparse,json,hashlib,os,re,subprocess,sys
S=Path(__file__).resolve().parent
MODS=['ActualFullPolynomial','ActualSourcePolynomial','ActualSourceFinite','ActualSourceResult','ActualDynamicMainterm','ActualDynamicTail','ActualFinalProfile']
def need(c,m):
 if not c:raise ValueError(m)
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--run-dir',type=Path,required=True);p.add_argument('--receipt',type=Path);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh output');R=a.run_dir.resolve();P=a.receipt.resolve()if a.receipt else R/'RESULT.json';j=read(P);need(j['schema']=='RH_RAMANUJAN_SOURCE_COMPONENT_STRONG_CONSUMER_V1','schema');need(j['status']=='PASS_FRESH_SOURCE_LINKED_ACTUAL_ONE_TWELFTH_CONSUMER','incomplete strong proof');need(j['whole_pipeline_source_first_PV']is False,'false PV label');need(j['li_definition_hypotheses']==[],'new li premise');need([x['module']for x in j['modules']]==MODS,'exact seven modules');need(sha(j['compiler'])==j['compiler_sha256'],'compiler identity')
B=Path(j['foundation']).resolve();C=Path(j['component']).resolve();bj=read(B/'RESULT.json');cj=read(C/'RESULT.json');need(sha(B/'RESULT.json')==j['foundation_receipt_sha256']and sha(C/'RESULT.json')==j['component_receipt_sha256'],'foundation/component receipt identity');need(cj['status']=='PASS_FRESH_SOURCE_FIRST_COMPONENT_WITH_ACTUAL_C_EXECUTION','source component incomplete');BB=Path(bj['base_replay']).resolve();banks=[BB/'objects',B/'objects',C/'objects'];need(len(j['fresh_import_objects'])==164,'full imported fresh closure');need(len({x['path']for x in j['fresh_import_objects']})==164,'duplicate imported module');ctx=read(Path(os.environ.get('IEANTN_GENERIC_CONTEXT',S.parent/'scripts/GENERIC_CONTEXT.json')));allowed=[(R/'objects').resolve(),*[x.resolve()for x in banks],Path(j['compiler']).resolve().parent.parent/'lib/lean',*[Path(x).resolve()for x in ctx['generic_libraries']]]
for row in j['fresh_import_objects']:
 q=Path(row['path']).resolve();need(any(q.is_relative_to(bank.resolve())for bank in banks),'unadmitted import bank');need(sha(q)==row['sha256'],'import object changed')
cm=read(S/'source_component/SOURCE_MANIFEST.json');need(cj['manifest_sha256']==sha(S/'source_component/SOURCE_MANIFEST.json'),'component source selection');need([x['module']for x in cj['modules']]==cm['modules'],'C source closure')
for row in cm['files']:need(sha(C/'source'/row['path'])==row['sha256']and sha(S/'source_component'/row['path'])==row['sha256'],'actual C/model source identity')
for row in cj['modules']:
 rel=Path(*row['module'].split('.'));need(row['returncode']==0,'component proof');need(sha((C/'objects'/rel).with_suffix('.olean'))==row['object_sha256'],'component artifact')
need(sha(C/'rh_coeff')==cj['binary_sha256']and sha(C/'outputs.txt')==cj['outputs_sha256'],'actual C execution association')
for row in j['modules']:
 m=row['module'];need(row['returncode']==0,'strong compiler failure');need(sha(R/'source'/(m+'.lean'))==row['source_sha256']and sha(S/(m+'.lean'))==row['source_sha256'],'proof source changed');need(sha(R/'objects'/(m+'.olean'))==row['object_sha256'],'proof object changed')
 for suffix in ['stdout','stderr']:need(sha(R/'logs'/(m+'.'+suffix))==row[suffix+'_sha256'],'execution log changed')
 text=(R/'logs'/(m+'.stdout')).read_text();need('sorryAx'not in text and 'Lean.ofReduce'not in text,'unaccepted axiom');need(len(row['dependency_probe'].splitlines())>0,'missing import probe')
 for q in row['dependency_probe'].splitlines():need(any(Path(q).resolve().is_relative_to(root)for root in allowed),'unadmitted numerical object')
for file,names in [('ActualSourceResult',['source_ramanujan_640b','source_ramanujan_profile','source_gap_profile']),('ActualFinalProfile',['final_ramanujan_profile','final_gap_profile'])]:
 text=(R/'logs'/(file+'.stdout')).read_text()
 for name in names:
  lines=[l for l in text.splitlines()if "RHContinuation.Ramanujan."+name+"' depends on axioms:"in l];need(len(lines)==1,'missing final axiom audit');vals=re.findall(r'\[(.*?)\]',lines[0]);need(len(vals)==1 and set(v.strip()for v in vals[0].split(','))=={'propext','Classical.choice','Quot.sound'},'final execution axiom')
# Validate all146+10 foundation source/artifacts through the actual independent CLI.
foundation_out=a.out.with_suffix('.foundation.json');r=subprocess.run([sys.executable,str(S/'verify.py'),'--run-dir',str(B),'--out',str(foundation_out)],capture_output=True,text=True);need(r.returncode==0,'foundation validation failed')
record={'status':'PASS_SELECTED_FULL_PROFILE_EXACT_SOURCE_AND_ARTIFACT_AUDIT','validator_sha256':sha(Path(__file__)),'run_receipt_sha256':sha(P),'foundation_validation_sha256':sha(foundation_out),'python_optimization':sys.flags.optimize,'selected_final_modules':7,'fresh_imported_modules':164,'native_execution_axioms':[],'li_definition_hypotheses':[],'whole_pipeline_source_first_PV':False};a.out.parent.mkdir(parents=True,exist_ok=True);tmp=a.out.with_suffix('.pending');tmp.write_text(json.dumps(record,indent=2)+'\n');os.replace(tmp,a.out);print(json.dumps(record))
