#!/usr/bin/env python3
"""Replay a complete W4 integer FFT proof DAG, with exact source and output audits.
No prior application objects are imported. This is kernel verification, NOT C PV.
"""
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,os,re,shutil,subprocess,sys,time
from reproduce_dual import context,need,publish,sha
R=Path(__file__).resolve().parents[3];S=R/'Solutions/RH080Next.v1'
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path,required=True);p.add_argument('--candidate',type=Path,required=True);p.add_argument('--run',type=Path,required=True);p.add_argument('--workers',type=int,default=4);a=p.parse_args();need(1<=a.workers<=32,'Bounded worker count');need(not a.run.exists(),'Fresh run required');c=context(a.context,R);proposal=json.loads((a.candidate/'PLAN.json').read_text());need(proposal['status']=='UNTRUSTED_W4_DAG_PROPOSAL_NOT_PROOF_NOT_PV','Proposal status');stages=proposal['stages'];need(type(stages)is int and 13<=stages<=24 and proposal['n']==2**stages,'Wrong grid');need(proposal['namespace']==f'W4DAG{stages}' and proposal['final_module']==f'W4D{stages}Final','Wrong claim namespace');need(proposal['input_sha256']=='61f745f27018ea5addbb01c1d583b128b2639b0f101d764136c98c26983c5521','Wrong original input')
if stages==24:need(proposal['norm_numerator']==7813568381279800,'Wrong original program output target')
producer=S/'dual/produce_fft_dag_certificate.py';need(sha(producer)==proposal['producer_sha256'],'Producer version changed')
a.run.mkdir();frozen=a.run/'sources';bank=a.run/'objects';frozen.mkdir();bank.mkdir();shutil.copyfile(Path(__file__),a.run/'driver.executed.py');shutil.copyfile(producer,a.run/'producer.executed.py');shutil.copyfile(a.candidate/'PLAN.json',a.run/'CANDIDATE.json');generated={}
for row in proposal['modules']:
 file=row['file'];need(Path(file).name==file and file.endswith('.lean'),'Generated module name');name=file[:-5];need(name not in generated and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',name)is not None,'Duplicate or unsupported module');need(sha(a.candidate/file)==row['sha256'],'Generated source changed');generated[name]=row
need(proposal['final_module']in generated,'Missing final proof')
payloads=[]
for row in proposal['payloads']:
 file=row['file'];need(Path(file).name==file and file.endswith('.csv'),'Data name');need(sha(a.candidate/file)==row['sha256'],'Data changed');shutil.copyfile(a.candidate/file,frozen/file);payloads.append(row)
GENERIC={'Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets'};rows={};active=set()
def visit(name):
 if name in rows or name.split('.')[0]in GENERIC:return
 need(name not in active,'Import cycle '+name);active.add(name)
 if name in generated:origin=a.candidate/generated[name]['file']
 else:
  origins=[folder/(name.replace('.','/')+'.lean')for folder in [S/'dual',S/'pv/lean']];origins=[q for q in origins if q.is_file()];need(len(origins)==1,'Missing/ambiguous foundation '+name);origin=origins[0]
 raw=origin.read_text();need(re.search(r'^\s*(?:axiom|opaque|sorry|admit)\b|\bnative_decide\b',raw,re.M)is None,'Unapproved proof leaf in '+name)
 deps=[n for line in raw.splitlines()if line.startswith('import ')for n in line[7:].split('--',1)[0].split()]
 if name in generated:need(deps==generated[name]['imports'],'Generated dependency inventory differs')
 for dep in deps:visit(dep)
 target=frozen/(name.replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(origin,target);rows[name]={'module':name,'origin':str(origin),'file':str(target.relative_to(frozen)),'sha256':sha(origin),'imports':deps};active.remove(name)
# Independently specified typed consumer: names and axiom lists alone do not
# establish that the generated theorems prove the fixed original claim.
ns=f'W4DAG{stages}';audit_name=f'W4D{stages}ClaimAudit';fixed='RH080Next.FFT.IntegerModel';audit_origin=a.run/(audit_name+'.lean')
lines=[f'import {proposal["final_module"]}', 'set_option maxRecDepth 2000000', 'set_option maxHeartbeats 0', 'set_option Elab.async false', 'noncomputable section', f'namespace W4ClaimAudit{stages}']
lines += [f'theorem execution : {fixed}.ExecutionTrace {ns}.stages ({fixed}.W4.input {2**stages}) {stages} 0 1 {ns}.output := {ns}.complete_execution',f'theorem seed_exact : {ns}.seed={fixed}.root {2**stages} := by decide +kernel',f'theorem twiddle : {fixed}.TwiddleTrace ({fixed}.root {2**stages}) ({fixed}.unit,0) ({ns}.stages {stages}).tail := by\n  rw [←seed_exact]\n  exact {ns}.global_twiddle_trace',f'theorem lengths : ∀ t<{stages}, ({ns}.stages (t+1)).length=2^t := {ns}.stage_lengths',f'theorem top_shape : ∃ tail, {ns}.stages {stages}=({fixed}.unit,0)::tail := ⟨{ns}.topTail, {ns}.top_shape⟩',f'theorem numerator : {fixed}.W4.normFromOutput {2**stages} {ns}.output={proposal["norm_numerator"]} := {ns}.numerator_checked']
for s in range(1,stages):lines.append(f'theorem step{s:02} : {fixed}.EvenTrace ({ns}.stages {s+1}) ({ns}.stages {s}) := {ns}.decimation{s:02}')
claim_roots=['execution','seed_exact','twiddle','lengths','top_shape','numerator']+[f'step{s:02}'for s in range(1,stages)]
lines += [f'#print axioms {r}'for r in claim_roots]+[f'end W4ClaimAudit{stages}'];audit_origin.write_text('\n'.join(lines)+'\n')
# Every proposal module is checked, including all numerical leaves.
for name in generated:visit(name)
# Add the checker-owned consumer explicitly, without allowing a candidate to
# replace its statement or source. Its sole import was inventoried above.
target=frozen/(audit_name+'.lean');shutil.copyfile(audit_origin,target);rows[audit_name]={'module':audit_name,'origin':str(audit_origin),'file':target.name,'sha256':sha(audit_origin),'imports':[proposal['final_module']]}
plan={'status':'FROZEN_SOURCE_COLD_W4_INTEGER_FFT_DAG_NOT_C_PV','sources':list(rows.values()),'payloads':payloads,'proposal':proposal,'candidate_plan_sha256':sha(a.candidate/'PLAN.json'),'controller_sha256':sha(Path(__file__)),'context_sha256':sha(a.context),'compiler_sha256':c['compiler_sha256'],'generic_dependencies':c['generic_dependencies'],'workers':a.workers,'application_object_fallback':False};publish(a.run/'PLAN.json',plan);env=dict(os.environ,LEAN_PATH=str(bank)+':'+c['generic_lean_path']);start=time.monotonic();done={};failed=False
BAD=re.compile(r'PANIC|error(?:\([^)]*\))?:|fatal error',re.I)
def compile_one(name):
 row=rows[name];src=frozen/row['file'];obj=bank/(name.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);cmd=[c['compiler'],'-j1','-R',str(frozen),'-o',str(obj),str(src)];out=a.run/(name+'.stdout');err=a.run/(name+'.stderr');tm=a.run/(name+'.time');t=time.monotonic()
 with out.open('x')as f,err.open('x')as g:r=subprocess.run(['/usr/bin/time','-v','-o',str(tm),*cmd],env=env,stdout=f,stderr=g)
 txt=tm.read_text();match=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',txt);receipt={'module':name,'returncode':r.returncode,'seconds':time.monotonic()-t,'peak_RSS_KiB':int(match[1])if match else None,'source_sha256':sha(src),'command':cmd,'stdout_sha256':sha(out),'stderr_sha256':sha(err),'time_sha256':sha(tm)}
 if obj.exists():receipt['object_sha256']=sha(obj)
 publish(a.run/(name+'.COMPILED.json'),receipt);need(r.returncode==0,'Compiler failed '+name);need(BAD.search(out.read_text()+'\n'+err.read_text())is None,'Compiler diagnostic even if exit0: '+name);need(obj.is_file(),'Missing object '+name);need(sha(src)==row['sha256'],'Frozen source changed '+name);return receipt
try:
 pending=set(rows);running={}
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers)as pool:
  while pending or running:
   ready=sorted(n for n in pending if all(dep.split('.')[0]in GENERIC or dep in done for dep in rows[n]['imports']))
   while ready and len(running)<a.workers:
    name=ready.pop(0);pending.remove(name);running[pool.submit(compile_one,name)]=name
   need(bool(running),'No runnable dependency route')
   finished,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
   for future in finished:
    name=running.pop(future);done[name]=future.result()
    if len(done)%10==0 or name==proposal['final_module']:print(json.dumps({'compiled':len(done),'total':len(rows),'latest':name,'seconds':time.monotonic()-start}),flush=True)
 final=audit_name;text=(a.run/(final+'.stdout')).read_text();expected=claim_roots;audits=[]
 for root in expected:
  full=f'W4ClaimAudit{stages}.'+root;matches=re.findall(r"'"+re.escape(full)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text);need(len(matches)==1,'Missing final axiom audit '+full);axes={x.strip()for x in matches[0].split(',')if x.strip()};need(axes<={'propext','Classical.choice','Quot.sound'},'Unapproved axiom '+full);audits.append({'root':full,'axioms':sorted(axes)})
 for row in rows.values():need(sha(frozen/row['file'])==row['sha256'],'Final source changed')
 for row in payloads:need(sha(frozen/row['file'])==row['sha256'],'Final numerical data changed')
 need(sha(Path(__file__))==plan['controller_sha256'],'Controller changed')
 publish(a.run/'AXIOM_AUDIT.json',{'status':'PASS','roots':audits});publish(a.run/'RESULT.json',{'status':'PASS_W4_COMPLETE_INTEGER_FFT_TRACE_CHECKED_TWIDDLES_AND_NUMERATOR_NOT_SOURCE_PV','stages':stages,'N':2**stages,'norm_numerator':proposal['norm_numerator'],'modules':len(done),'audited_roots':len(audits),'seconds':time.monotonic()-start,'max_individual_RSS_KiB':max(r['peak_RSS_KiB']or 0 for r in done.values()),'disk_bytes':sum(p.stat().st_size for p in a.run.rglob('*')if p.is_file()),'SIGKILL_exits':sum(r['returncode']==-9 for r in done.values()),'OOM_measurement':'see independent supervisor memory.events receipt','plan_sha256':sha(a.run/'PLAN.json'),'full_original_C_FFT_PV':False,'independent_fixed_claim_type_audit':True});print('PASS_INTEGER_FFT_NOT_C_PV',flush=True)
except BaseException as error:
 publish(a.run/'FAILURE.json',{'status':'NO_ACCEPTANCE','error':str(error),'seconds':time.monotonic()-start,'completed':len(done)});raise
