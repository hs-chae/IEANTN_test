#!/usr/bin/env python3
"""Fresh source replay of stronger full-coefficient/C-linked actual consumer.
Default rebuilds146+10+8+4 modules. Explicit --base-run and --component-run
reuse only separately completed fresh-source builds, whose exact hashes are checked.
"""
from pathlib import Path
import argparse,json,hashlib,os,subprocess,time,shutil,re,sys
S=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--base-run',type=Path);p.add_argument('--component-run',type=Path);a=p.parse_args()
def need(c,m):
 if not c:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def read(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def save(p,j):
 t=p.with_suffix('.pending');t.write_text(json.dumps(j,indent=2)+'\n');os.replace(t,p)
O=a.out.resolve();need(not O.exists(),'fresh output required')
for n in ['source','objects','logs','union']:(O/n).mkdir(parents=True,exist_ok=True)
ctx=read(Path(os.environ.get('IEANTN_GENERIC_CONTEXT',S.parent/'scripts/GENERIC_CONTEXT.json')));need(sha(ctx['compiler'])==ctx['compiler_sha256'],'compiler pin');j={'schema':'RH_RAMANUJAN_SOURCE_COMPONENT_STRONG_CONSUMER_V1','status':'RUNNING','modules':[],'compiler':ctx['compiler'],'compiler_sha256':ctx['compiler_sha256'],'controller_sha256':sha(Path(__file__)),'whole_pipeline_source_first_PV':False,'source_first_PV_component':'rh_coeff.c degree0..20 actual typed uint64 execution','actual_margin':'1/12 forx>=640000000000;4/5forx>=exp42','mathematical_inputs':['MathlibRH','ButheTable2','ButheEq1.8','ButheEq1.9','ButheEq1.10','Buthe2016Eq7.2'],'li_definition_hypotheses':[]};save(O/'RESULT.json',j);t=time.monotonic()
try:
 def child(cmd,label):
  r=subprocess.run(cmd,capture_output=True,text=True);(O/'logs'/(label+'.stdout')).write_text(r.stdout);(O/'logs'/(label+'.stderr')).write_text(r.stderr);need(r.returncode==0,label+' failed')
 if a.base_run:B=a.base_run.resolve()
 else:B=O/'foundation';child([sys.executable,str(S/'reproduce.py'),'--out',str(B)],'foundation')
 child([sys.executable,str(S/'verify.py'),'--run-dir',str(B),'--out',str(O/'foundation-validation.json')],'foundation-validation');bj=read(B/'RESULT.json');BB=Path(bj['base_replay']).resolve()
 if a.component_run:C=a.component_run.resolve()
 else:C=O/'component';child([sys.executable,str(S/'source_component/reproduce.py'),'--out',str(C)],'component')
 cj=read(C/'RESULT.json');need(cj['status']=='PASS_FRESH_SOURCE_FIRST_COMPONENT_WITH_ACTUAL_C_EXECUTION','C component incomplete');cm=read(S/'source_component/SOURCE_MANIFEST.json');need(cj['manifest_sha256']==sha(S/'source_component/SOURCE_MANIFEST.json'),'component manifest');need([x['module']for x in cj['modules']]==cm['modules'],'component closure')
 for row in cj['modules']:
  rel=Path(*row['module'].split('.'));need(row['returncode']==0,'component Lean failed');need(sha((C/'source'/rel).with_suffix('.lean'))==row['source_sha256'],'component source');need(sha((C/'objects'/rel).with_suffix('.olean'))==row['object_sha256'],'component object')
 for row in cm['files']:need(sha(C/'source'/row['path'])==row['sha256']and sha(S/'source_component'/row['path'])==row['sha256'],'actual component source identity')
 need(sha(C/'rh_coeff')==cj['binary_sha256']and sha(C/'outputs.txt')==cj['outputs_sha256'],'C binary/outputs');need(sha(C/'source/rh_coeff.c')==cj['C_source_sha256'],'actual C source pin')
 # A merged bank is necessary: Lean chooses an entire namespace directory from
 # one search-root, so separate RamanujanPV roots would shadow each other.
 banks=[BB/'objects',B/'objects',C/'objects'];bankrows=[]
 for bank in banks:
  for src in sorted(bank.rglob('*.olean')):
   dst=O/'union'/src.relative_to(bank);need(not dst.exists(),'unexpected module collision');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src.resolve());bankrows.append({'path':str(src.resolve()),'sha256':sha(src)})
 j.update(foundation=str(B),foundation_receipt_sha256=sha(B/'RESULT.json'),component=str(C),component_receipt_sha256=sha(C/'RESULT.json'),fresh_import_objects=bankrows);save(O/'RESULT.json',j)
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(O/'objects'),str(O/'union'),*ctx['generic_libraries']]);allowed=[(O/'objects').resolve(),*[x.resolve()for x in banks],Path(ctx['compiler']).resolve().parent.parent/'lib/lean',*[Path(x).resolve()for x in ctx['generic_libraries']]]
 for mod in ['ActualFullPolynomial','ActualSourcePolynomial','ActualSourceFinite','ActualSourceResult','ActualDynamicMainterm','ActualDynamicTail','ActualFinalProfile']:
  src=S/(mod+'.lean');dst=O/'source'/src.name;shutil.copyfile(src,dst);tt=time.monotonic();res=O/'logs'/(mod+'.resources');cmd=[ctx['compiler'],'--root='+str(O/'source'),'-j8','-o',str(O/'objects'/(mod+'.olean')),str(dst)];r=subprocess.run(['/usr/bin/time','-f','%e %M','-o',str(res),*cmd],cwd=O/'source',env=env,text=True,capture_output=True);(O/'logs'/(mod+'.stdout')).write_text(r.stdout);(O/'logs'/(mod+'.stderr')).write_text(r.stderr);row={'module':mod,'source_sha256':sha(dst),'returncode':r.returncode,'seconds':time.monotonic()-tt,'command':cmd,'resources':res.read_text()};j['modules'].append(row);save(O/'RESULT.json',j);need(r.returncode==0,'Lean:'+mod);need(sha(src)==row['source_sha256'],'source changed');need('sorryAx'not in r.stdout and 'Lean.ofReduce'not in r.stdout,'unaccepted axiom')
  dep=subprocess.run([ctx['compiler'],'--root='+str(O/'source'),'--deps',str(dst)],cwd=O/'source',env=env,capture_output=True,text=True);need(dep.returncode==0,'dependency probe');need(len(dep.stdout.splitlines())>0,'empty deps')
  for line in dep.stdout.splitlines():need(any(Path(line.strip()).resolve().is_relative_to(root)for root in allowed),'undeclared object import')
  row.update(dependency_probe=dep.stdout,object_sha256=sha(O/'objects'/(mod+'.olean')),stdout_sha256=sha(O/'logs'/(mod+'.stdout')),stderr_sha256=sha(O/'logs'/(mod+'.stderr')));save(O/'RESULT.json',j);print('PASS',mod,round(row['seconds'],2),flush=True)
 final=(O/'logs/ActualSourceResult.stdout').read_text()
 for name in ['source_ramanujan_640b','source_ramanujan_profile','source_gap_profile']:
  lines=[l for l in final.splitlines()if "RHContinuation.Ramanujan."+name+"' depends on axioms:"in l];need(len(lines)==1,'final audit');vals=re.findall(r'\[(.*?)\]',lines[0]);need(len(vals)==1 and set(v.strip()for v in vals[0].split(','))=={'propext','Classical.choice','Quot.sound'},'final axiom set')
 final2=(O/'logs/ActualFinalProfile.stdout').read_text()
 for name in ['final_ramanujan_profile','final_gap_profile']:
  lines=[l for l in final2.splitlines()if "RHContinuation.Ramanujan."+name+"' depends on axioms:"in l];need(len(lines)==1,'final profile audit');vals=re.findall(r'\[(.*?)\]',lines[0]);need(len(vals)==1 and set(v.strip()for v in vals[0].split(','))=={'propext','Classical.choice','Quot.sound'},'final profile axiom set')
 j.update(status='PASS_FRESH_SOURCE_LINKED_ACTUAL_ONE_TWELFTH_CONSUMER',seconds=time.monotonic()-t,remaining_trust='Kernel verification for mathematical proof and exact interval leaves; source-first restricted C/typed uint64 proof for coefficient application; compiler/runtime/OS/hardware contracts for native C execution; six explicit RH/literature analytic inputs. Full finite prime-count source-first PV remains open.');save(O/'RESULT.json',j);print(j['status'],flush=True)
except BaseException as e:j.update(status='FAIL',error=str(e));save(O/'RESULT.json',j);raise
