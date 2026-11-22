#!/usr/bin/env python3
"""Compile actual new core statements and exact typed canonical Solution adapter."""
from pathlib import Path
import argparse,json,subprocess,hashlib,os,time,re,shutil,sys
S=Path(__file__).resolve().parent;M=S.parent;N=M.parents[2]
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--strong-run',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
def need(c,m):
 if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,j):
 t=p.with_suffix('.pending');t.write_text(json.dumps(j,indent=2)+'\n');os.replace(t,p)
O=a.out.resolve();need(not O.exists(),'fresh output');
for n in ['source','objects','logs']:(O/n).mkdir(parents=True,exist_ok=True)
C=a.strong_run.resolve();r=subprocess.run([sys.executable,str(M/'verify_strong.py'),'--run-dir',str(C),'--out',str(O/'strong-validation.json')],capture_output=True,text=True);need(r.returncode==0,'strong closure validation');j0=json.loads((C/'RESULT.json').read_text());ctx=json.loads(Path(os.environ.get('IEANTN_GENERIC_CONTEXT',M.parent/'scripts/GENERIC_CONTEXT.json')).read_text());need(sha(ctx['compiler'])==ctx['compiler_sha256'],'compiler pin')
for B in [C/'objects',C/'union']:
 for src in B.rglob('*.olean'):
  dst=O/'objects'/src.relative_to(B);need(not dst.exists(),'module collision');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src.resolve())
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(O/'objects'),*ctx['generic_libraries']]);rows=[];start=time.monotonic();j={'status':'RUNNING','modules':rows,'strong_result_sha256':sha(C/'RESULT.json'),'compiler_sha256':ctx['compiler_sha256']};save(O/'RESULT.json',j)
mods=[('IEANTN.Nodes.RH.v1.Conclusions',N/'IEANTN/Nodes/RH/v1/Conclusions.lean'),('IEANTN.Nodes.RamanujanGap.v3.Conclusions',N/'IEANTN/Nodes/RamanujanGap/v3/Conclusions.lean'),('NodeSolution',N/'Solutions/RamanujanGap.v3/Solution.lean'),('ActualLiAbelModel',M/'ActualLiAbelModel.lean'),('FiniteMangoldtAbel',M.parent/'parabolic/FiniteMangoldtAbel.lean'),('ActualCompensatedJ',M/'ActualCompensatedJ.lean'),('ActualJIdentity',M/'ActualJIdentity.lean'),('ActualGMPrimitive',M/'ActualGMPrimitive.lean'),('ActualGMTransfer',M/'ActualGMTransfer.lean'),('ActualGMClosed',M/'ActualGMClosed.lean'),('IEANTN.Vocabulary.RHSmoothing',N/'IEANTN/Vocabulary/RHSmoothing.lean'),('IEANTN.Nodes.RHSmoothing.v1.Conclusions',N/'IEANTN/Nodes/RHSmoothing/v1/Conclusions.lean'),('IEANTN.Nodes.RHPrimeCounting.v1.Conclusions',N/'IEANTN/Nodes/RHPrimeCounting/v1/Conclusions.lean'),('PrimeCountingSolution',N/'Solutions/RHPrimeCounting.v1/Solution.lean')]
for mod,src in mods:
 rel=Path(*mod.split('.'));dst=(O/'source'/rel).with_suffix('.lean');obj=(O/'objects'/rel).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True);obj.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);tt=time.monotonic();res=O/'logs'/(mod+'.resources');cmd=[ctx['compiler'],'--root='+str(O/'source'),'-j8','-o',str(obj),str(dst)];r=subprocess.run(['/usr/bin/time','-f','%e %M','-o',str(res),*cmd],cwd=O/'source',env=env,capture_output=True,text=True);(O/'logs'/(mod+'.stdout')).write_text(r.stdout);(O/'logs'/(mod+'.stderr')).write_text(r.stderr);row={'module':mod,'original_source':str(src),'source_sha256':sha(dst),'returncode':r.returncode,'command':cmd,'seconds':time.monotonic()-tt,'resources':res.read_text()};rows.append(row);save(O/'RESULT.json',j);
 if r.returncode!=0:
  j.update(status='FAIL',error='compile:'+mod);save(O/'RESULT.json',j);raise ValueError('compile:'+mod)
 need(sha(src)==row['source_sha256'],'source changed');need('sorryAx'not in r.stdout and 'Lean.ofReduce'not in r.stdout,'unaccepted axiom');row['object_sha256']=sha(obj);print('PASS',mod,round(row['seconds'],2),flush=True)
text=(O/'logs/NodeSolution.stdout').read_text()
for name in ['challenge_one_twelfth_margin','challenge_tail_144_margin','challenge_full_profile','challenge_ramanujan']:
 lines=[l for l in text.splitlines()if "RamanujanGap.v3."+name+"' depends on axioms:"in l];need(len(lines)==1,'missing exact node proof audit');vals=re.findall(r'\[(.*?)\]',lines[0]);need(len(vals)==1 and set(v.strip()for v in vals[0].split(','))=={'propext','Classical.choice','Quot.sound'},'node axiom set')
text2=(O/'logs/PrimeCountingSolution.stdout').read_text()
for name in ['challenge_generic_transfer','challenge_boxed_signed','challenge_boxed_absolute','challenge_B5_absolute','challenge_boxed_strict_gain']:
 lines=[l for l in text2.splitlines()if "RHPrimeCounting.v1."+name+"' depends on axioms:"in l];need(len(lines)==1,'missing exact prime-count node audit');vals=re.findall(r'\[(.*?)\]',lines[0]);need(len(vals)==1 and set(v.strip()for v in vals[0].split(','))=={'propext','Classical.choice','Quot.sound'},'prime-count axiom set')
j.update(status='PASS_CANONICAL_NODE_TYPED_SOLUTION_AND_ACTUAL_LI_MODEL',seconds=time.monotonic()-start,official_comparator_receipt=False,metadata_justification='lean-noncompliant');save(O/'RESULT.json',j);print(j['status'],flush=True)
