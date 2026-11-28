#!/usr/bin/env python3
"""Actual CLI rejection controls in normal, -O and -OO Python.
Mutations are confined to fresh experiment-owned copies. No math acceptance.
"""
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,os,re,shutil,subprocess,sys,time
R=Path(__file__).resolve().parents[3];S=R/'Solutions/RH080Next.v1'
def need(ok,message):
 if not ok:raise RuntimeError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def replace_bytes(p,data):
 temp=p.with_name(p.name+'.mutation.tmp');temp.write_bytes(data);os.replace(temp,p)
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path,required=True);p.add_argument('--candidate',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
need(not a.out.exists(),'Fresh control output required');base=json.loads((a.candidate/'PLAN.json').read_text());need(base['stages']==13,'Use the checked small W4 diagnostic grid');a.out.mkdir();controller=S/'dual/reproduce_fft_dag_v2.py';controller_hash=sha(controller)
for row in base['modules']+base['payloads']:need(sha(a.candidate/row['file'])==row['sha256'],'Base candidate changed')
started=time.monotonic()
def one(mode,kind):
 name=mode+'-'+kind;root=a.out/name;root.mkdir();candidate=root/'candidate';shutil.copytree(a.candidate,candidate,copy_function=os.link);d=json.loads((candidate/'PLAN.json').read_text())
 if kind=='wrong_original_target':
  d.update(stages=24,n=2**24,namespace='W4DAG24',final_module='W4D24Final',norm_numerator=7813568381279801)
  expected='Wrong original program output target'
 elif kind=='changed_butterfly':
  row=next(x for x in d['payloads']if 'N01G' in x['file']);q=candidate/row['file'];lines=q.read_text().splitlines();x,y=lines[0].split(',');lines[0]=str(int(x)+1)+','+y;replace_bytes(q,('\n'.join(lines)+'\n').encode());row['sha256']=sha(q);row['bytes']=q.stat().st_size;expected='Compiler failed '
 elif kind=='weakened_final_statement':
  row=next(x for x in d['modules']if x['file']==d['final_module']+'.lean');q=candidate/row['file'];text,count=re.subn(r'^theorem complete_execution :[^\n]+$', 'theorem complete_execution : True := True.intro',q.read_text(),count=1,flags=re.M);need(count==1,'Expected exact final declaration');replace_bytes(q,text.encode());row['sha256']=sha(q);row['bytes']=q.stat().st_size;expected='Compiler failed W4D13ClaimAudit'
 elif kind=='compiler_diagnostic_exit_zero':
  row=next(x for x in d['modules']if x['file']=='W4D13Base.lean');q=candidate/row['file'];replace_bytes(q,q.read_bytes()+b'\nrun_cmd Lean.logInfo "PANIC diagnostic rejection fixture"\n');row['sha256']=sha(q);row['bytes']=q.stat().st_size;expected='Compiler diagnostic even if exit0'
 else:raise RuntimeError('Unknown control')
 replace_bytes(candidate/'PLAN.json',(json.dumps(d,indent=2)+'\n').encode());run=root/'replay';command=[sys.executable]+([]if mode=='normal'else['-'+mode])+[str(controller),'--context',str(a.context),'--candidate',str(candidate),'--run',str(run),'--workers','2'];start=time.monotonic()
 with(root/'stdout').open('x')as out,(root/'stderr').open('x')as err:r=subprocess.run(command,stdout=out,stderr=err)
 stdout=(root/'stdout').read_text();stderr=(root/'stderr').read_text();need(r.returncode!=0,'Mutation accepted: '+name);need(not(run/'RESULT.json').exists(),'False success receipt: '+name);need(expected in stdout+stderr,'Wrong rejection reason: '+name)
 if kind=='compiler_diagnostic_exit_zero':
  receipt=json.loads((run/'W4D13Base.COMPILED.json').read_text());need(receipt['returncode']==0,'Did not test actual exit-zero compiler path')
 need(sha(controller)==controller_hash,'Control driver changed');row={'mode':mode,'mutation':kind,'status':'PASS_ACTUAL_CLI_REJECTION','returncode':r.returncode,'seconds':time.monotonic()-start,'expected_rejection':expected,'command':command,'stdout_sha256':sha(root/'stdout'),'stderr_sha256':sha(root/'stderr')};(root/'CONTROL_RESULT.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps({k:row[k]for k in ['mode','mutation','status','seconds']}),flush=True);return row
jobs=[(m,k)for m in ['normal','O','OO']for k in ['wrong_original_target','changed_butterfly','weakened_final_statement','compiler_diagnostic_exit_zero']]
with concurrent.futures.ThreadPoolExecutor(max_workers=3)as pool:results=list(pool.map(lambda x:one(*x),jobs))
for row in base['modules']+base['payloads']:need(sha(a.candidate/row['file'])==row['sha256'],'Base candidate mutated')
result={'status':'PASS_ALL12_ACTUAL_CLI_REJECTION_CONTROLS','seconds':time.monotonic()-started,'controller_sha256':controller_hash,'control_driver_sha256':sha(Path(__file__)),'cases':results,'mathematical_acceptance':False};temp=a.out/'RESULT.tmp';temp.write_text(json.dumps(result,indent=2)+'\n');os.replace(temp,a.out/'RESULT.json');print('PASS_ALL12',flush=True)
