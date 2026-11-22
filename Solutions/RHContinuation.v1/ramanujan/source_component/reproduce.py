#!/usr/bin/env python3
"""Fresh-source replay of the exact historical rh_coeff C application model."""
from pathlib import Path
import argparse,json,hashlib,os,subprocess,time,shutil,datetime
S=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
def need(c,m):
 if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,j):
 t=p.with_suffix('.pending');t.write_text(json.dumps(j,indent=2)+'\n');os.replace(t,p)
O=a.out.resolve();need(not O.exists(),'fresh output required')
for n in ['source','objects','logs']:(O/n).mkdir(parents=True,exist_ok=True)
ctx=json.loads(Path(os.environ.get('IEANTN_GENERIC_CONTEXT',S.parents[1]/'scripts/GENERIC_CONTEXT.json')).read_text());manifest=json.loads((S/'SOURCE_MANIFEST.json').read_text());need(sha(ctx['compiler'])==ctx['compiler_sha256'],'compiler pin')
for row in manifest['files']:
 src=S/row['path'];need(sha(src)==row['sha256'],'source pin');dst=O/'source'/row['path'];dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(O/'objects'),*ctx['generic_libraries']]);j={'status':'RUNNING','modules':[],'source_only':True,'native_execution_axioms':False,'compiler':ctx['compiler'],'compiler_sha256':ctx['compiler_sha256'],'manifest_sha256':sha(S/'SOURCE_MANIFEST.json')};t=time.monotonic();save(O/'RESULT.json',j)
try:
 for mod in manifest['modules']:
  rel=Path(*mod.split('.'));src=(O/'source'/rel).with_suffix('.lean');obj=(O/'objects'/rel).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);tt=time.monotonic();res=O/'logs'/(mod+'.resources');cmd=[ctx['compiler'],'--root='+str(O/'source'),'-j8','-o',str(obj),str(src)]
  r=subprocess.run(['/usr/bin/time','-f','%e %M','-o',str(res),*cmd],cwd=O/'source',env=env,capture_output=True,text=True);(O/'logs'/(mod+'.stdout')).write_text(r.stdout);(O/'logs'/(mod+'.stderr')).write_text(r.stderr);row={'module':mod,'returncode':r.returncode,'seconds':time.monotonic()-tt,'source_sha256':sha(src),'command':cmd,'resource':res.read_text()};j['modules'].append(row);save(O/'RESULT.json',j);need(r.returncode==0,'Lean:'+mod);need('sorryAx'not in r.stdout and 'Lean.ofReduce'not in r.stdout,'axiom');row['object_sha256']=sha(obj);print('PASS',mod,round(row['seconds'],2),flush=True)
 (O/'driver.c').write_text('#include <stdio.h>\n#include <inttypes.h>\n#include "source/rh_coeff.c"\nint main(void){for(uint64_t j=0;j<=20;j++)printf("%" PRIu64 " %" PRIu64 "\\n",j,rh_coeff(j));return 0;}\n')
 cmd=['cc','-std=c11','-Wall','-Wextra','-Werror','-O2',str(O/'driver.c'),'-o',str(O/'rh_coeff')];r=subprocess.run(cmd,capture_output=True,text=True);need(r.returncode==0,'C compilation');run=subprocess.run([str(O/'rh_coeff')],capture_output=True,text=True);need(run.returncode==0,'C execution');(O/'outputs.txt').write_text(run.stdout)
 import math
 expected=''.join(str(k)+' '+str(sum(math.factorial(i)*math.comb(k,i)for i in range(k+1))-sum(math.factorial(i)*math.factorial(k-i)for i in range(k+1)))+'\n'for k in range(21));need(run.stdout==expected,'actual C outputs differ from checked mathematical model');j.update(status='PASS_FRESH_SOURCE_FIRST_COMPONENT_WITH_ACTUAL_C_EXECUTION',seconds=time.monotonic()-t,C_command=cmd,C_version=subprocess.run(['cc','--version'],capture_output=True,text=True).stdout,C_source_sha256=sha(O/'source/rh_coeff.c'),driver_sha256=sha(O/'driver.c'),binary_sha256=sha(O/'rh_coeff'),outputs_sha256=sha(O/'outputs.txt'),remaining_trust='Restricted C source/AST relation and formal typed uint64 model are kernel proved; actual compiled execution assumes documented C compiler/runtime/OS/hardware contracts. Outputs are additionally compared; comparison is not the source proof. This verifies the coefficient application component, not full finite-prime-count generation or all numerical consumers.');save(O/'RESULT.json',j);print(j['status'],flush=True)
except BaseException as e:j.update(status='FAIL',error=str(e));save(O/'RESULT.json',j);raise
