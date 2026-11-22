#!/usr/bin/env python3
"""Fresh all-mode numerical + conditional-source Lean replay for this track."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
import argparse,json,hashlib,os,subprocess,sys,time,re
B=Path(__file__).resolve().parent
def need(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_constant=lambda s:(_ for _ in()).throw(ValueError('nonfinite JSON')))
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--core-library',type=Path,required=True);a=p.parse_args();O=a.out.resolve();need(not O.exists(),'fresh output');need(a.core_library.is_dir(),'explicit freshly built IEANTN core library required');O.mkdir(parents=True);(O/'numeric').mkdir();(O/'controls').mkdir();start=time.monotonic();jobs=[]
for script in ['quartic_quadrature.py','sextic_quadrature.py','box_quadrature.py','quartic_scalars.py','sextic_scalars.py','box_scalars.py']:
 for mode,flag in [('normal',[]),('O',['-O']),('OO',['-OO'])]:jobs.append((script,mode,flag))
def run(job):
 script,mode,flag=job;stem=script.removesuffix('.py')+'-'+mode;out=O/'numeric'/(stem+'.json');resource=O/'numeric'/(stem+'.resources');cmd=['/usr/bin/time','-v','-o',str(resource),sys.executable,*flag,str(B/script),'--out',str(out)];t=time.monotonic();r=subprocess.run(cmd,cwd=B,text=True,capture_output=True);(O/'numeric'/(stem+'.stdout')).write_text(r.stdout);(O/'numeric'/(stem+'.stderr')).write_text(r.stderr);need(r.returncode==0,'child failed:'+stem);data=read(out);need(data['status']=='PASS','numeric status');need(data['python_optimization']==len(flag)*(2 if mode=='OO'else 1),'actual mode');need(data['source_sha256']==sha(B/script),'source identity')
 if 'quadrature'in script:
  need(data['rational_sha256']==sha(B/'rational.py'),'arithmetic source');need('UPPER-BOUND EXPRESSION'in data['interval_semantics'],'upper-expression semantics missing')
  fields=[('mass_div_pi',Fraction('1.54')),('logmoment_div_pi',Fraction('.9'))]if script.startswith('quartic')else[('mass_div_pi',Fraction('1.72')),('logmoment_div_pi',Fraction('1.3'))]if script.startswith('sextic')else[('absolute_regularized_J0',Fraction('.701')),('absolute_regularized_J1',Fraction('.75'))]
  for field,cap in fields:
   interval=data[field];lo=Fraction(interval['lower']);hi=Fraction(interval['upper']);need(lo<=hi<cap,'accepted actual-moment upper gate')
 # Exercise the actual CLI rejection routes under the same optimization mode.
 for label,args in [('missing-out',[]),('unknown-flag',['--out',str(O/'controls'/stem),'--not-an-option']),('existing-output',['--out',str(out)])]:
  q=subprocess.run([sys.executable,*flag,str(B/script),*args],cwd=B,text=True,capture_output=True);need(q.returncode!=0,'invalid CLI accepted:'+stem+label);(O/'controls'/(stem+'-'+label+'.json')).write_text(json.dumps({'command':[sys.executable,*flag,str(B/script),*args],'returncode':q.returncode,'stdout':q.stdout,'stderr':q.stderr},indent=2)+'\n')
 m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',resource.read_text());return {'script':script,'mode':mode,'command':cmd,'seconds':time.monotonic()-t,'peak_RSS_kib':int(m.group(1))if m else None,'receipt':str(out),'receipt_sha256':sha(out),'source_sha256':sha(B/script),'resource_sha256':sha(resource),'accepted':True,'controls_rejected':3}
with ThreadPoolExecutor(max_workers=3)as pool:results=list(pool.map(run,jobs))
# Numerical expression identities must be mode invariant.
for script in ['quartic_quadrature.py','sextic_quadrature.py','box_quadrature.py']:
 rows=[read(Path(x['receipt']))for x in results if x['script']==script]
 fields=['absolute_regularized_J0','absolute_regularized_J1']if script.startswith('box')else['mass_div_pi','logmoment_div_pi']
 for field in fields:need(rows[0][field]==rows[1][field]==rows[2][field],'mode-dependent numerical output')
mods=['QuarticWindow','SexticWindow','PsiSmoothing','QuarticContracts','SexticContracts','Audit'];cmd=[sys.executable,str(B.parent/'scripts/build_modules.py'),'--source',str(B),'--out',str(O/'lean'),'--extra-library',str(a.core_library)]
for mod in mods:cmd+=['--module',mod]
r=subprocess.run(cmd,cwd=B,text=True,capture_output=True);(O/'LEAN.stdout').write_text(r.stdout);(O/'LEAN.stderr').write_text(r.stderr);need(r.returncode==0,'Lean source replay failed')
audit=(O/'lean/logs/Audit.stdout').read_text();need('sorryAx'not in audit and 'Lean.ofReduceBool'not in audit and 'native_decide'not in audit,'unaccepted execution axiom');need(audit.count('depends on axioms:')>=5,'missing actual audit declarations');need('standardAxiomsOnly' in audit,'missing audit sentinel')
record={'schema':'RH_PARABOLIC_TRACK_FULL_REPLAY_V1','status':'PASS_NEW_SOURCES_NUMERIC_ALL_MODES_AND_CONDITIONAL_ACTUAL_CONSUMERS','seconds':time.monotonic()-start,'numeric_runs':results,'accepted_child_routes':len(results),'invalid_CLI_rejections':sum(x['controls_rejected']for x in results),'lean_modules':mods,'core_library':str(a.core_library),'source_files':[{'path':p.name,'sha256':sha(p),'bytes':p.stat().st_size}for p in sorted(B.iterdir())if p.is_file()and p.suffix in['.py','.lean','.md']],'mathematical_status':'Written analytic full-domain bounds; Lean actual consumers retain exact EF/zero-density/cost/geometry/moment contracts, not RH-only analytic closure','PV':False};tmp=O/'RESULT.json.pending';tmp.write_text(json.dumps(record,indent=2)+'\n');os.replace(tmp,O/'RESULT.json');print(json.dumps({'status':record['status'],'numeric_runs':len(results),'invalid_CLI_rejections':record['invalid_CLI_rejections'],'seconds':record['seconds']},indent=2))
