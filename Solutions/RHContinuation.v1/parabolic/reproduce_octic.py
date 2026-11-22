#!/usr/bin/env python3
"""Fresh normal/-O/-OO octic numerical runs and generic actual-consumer replay."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
import argparse,subprocess,sys,hashlib,json,time,os,re
B=Path(__file__).resolve().parent
def need(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 def pairs(rows):
  r={}
  for k,v in rows:need(k not in r,'duplicateJSONkey');r[k]=v
  return r
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_constant=lambda s:(_ for _ in()).throw(ValueError('nonfiniteJSON')))
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--core-library',type=Path,required=True);a=p.parse_args();O=a.out.resolve();need(not O.exists(),'fresh output');need(a.core_library.is_dir(),'explicitcorelibrary');O.mkdir(parents=True);start=time.monotonic()
def run(mode):
 flag=[]if mode==0 else['-O']if mode==1 else['-OO'];rows=[]
 for script in ['octic_quadrature.py','octic_scalars.py']:
  name=script.removesuffix('.py')+'-'+str(mode);out=O/(name+'.json');res=O/(name+'.resources');cmd=['/usr/bin/time','-v','-o',str(res),sys.executable,*flag,str(B/script),'--out',str(out)];r=subprocess.run(cmd,cwd=B,text=True,capture_output=True);(O/(name+'.stdout')).write_text(r.stdout);(O/(name+'.stderr')).write_text(r.stderr);need(r.returncode==0,'childfailed'+name);j=read(out);need(j['status']=='PASS'and j['python_optimization']==mode and j['source_sha256']==sha(B/script),'childidentity')
  if 'quadrature'in script:
   need('UPPER-BOUND EXPRESSION'in j['interval_semantics'],'expressionsemantics')
   for field,cap in [('mass_div_pi',Fraction('1.822')),('logmoment_div_pi',Fraction('1.5'))]:need(Fraction(j[field]['lower'])<=Fraction(j[field]['upper'])<cap,'momentcap')
  controls=[]
  for label,args in [('missingout',[]),('badflag',['--out',str(O/'bad-output'),'--unexpected']),('existingout',['--out',str(out)])]:
   c=subprocess.run([sys.executable,*flag,str(B/script),*args],cwd=B,text=True,capture_output=True);need(c.returncode!=0,'invalidCLIaccepted');controls.append({'label':label,'returncode':c.returncode,'stderr':c.stderr})
  (O/(name+'-controls.json')).write_text(json.dumps(controls,indent=2)+'\n');m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',res.read_text());rows.append({'script':script,'mode':mode,'receipt':str(out),'receipt_sha256':sha(out),'source_sha256':sha(B/script),'resource_sha256':sha(res),'peak_RSS_kib':int(m.group(1))if m else None,'rejected_invalid_CLIs':len(controls)})
 return rows
with ThreadPoolExecutor(max_workers=3)as pool:rows=[x for result in pool.map(run,[0,1,2])for x in result]
q=[read(x['receipt'])for x in rows if x['script']=='octic_quadrature.py']
for field in['mass_div_pi','logmoment_div_pi']:need(q[0][field]==q[1][field]==q[2][field],'mode-invariantexpression')
mods=['QuarticWindow','PsiSmoothing','EvenKernel','OcticConsumer','AuditOctic'];cmd=[sys.executable,str(B.parent/'scripts/build_modules.py'),'--source',str(B),'--out',str(O/'lean'),'--extra-library',str(a.core_library)]
for m in mods:cmd+=['--module',m]
r=subprocess.run(cmd,cwd=B,text=True,capture_output=True);(O/'LEAN.stdout').write_text(r.stdout);(O/'LEAN.stderr').write_text(r.stderr);need(r.returncode==0,'sourceLeanreplay');audit=(O/'lean/logs/AuditOctic.stdout').read_text();need(audit.count('depends on axioms:')>=3 and 'sorryAx'not in audit and 'Lean.ofReduceBool'not in audit,'actualaxiomaudit')
record={'schema':'OCTIC_ALLMODE_NUMERIC_AND_GENERIC_CONSUMER_REPLAY_V1','status':'PASS','seconds':time.monotonic()-start,'rows':rows,'actual_child_routes':len(rows),'rejected_invalid_CLI_routes':sum(x['rejected_invalid_CLIs']for x in rows),'lean_modules':mods,'core_library':str(a.core_library),'actual_quantities':'ordinaryprimeCountingdifferenceandkernelweightedMangoldtsum','trust_boundary':'NewconditionalactualLeanconsumers;writtenanalyticEF/zerodensity/cost/geometricproofsremainparameters;numericC/PythonexecutionnotPV','source_first_PV':False};tmp=O/'RESULT.json.pending';tmp.write_text(json.dumps(record,indent=2)+'\n');os.replace(tmp,O/'RESULT.json');print(json.dumps({'status':'PASS','actual_child_routes':record['actual_child_routes'],'rejected_invalid_CLI_routes':record['rejected_invalid_CLI_routes'],'seconds':record['seconds']},indent=2))
