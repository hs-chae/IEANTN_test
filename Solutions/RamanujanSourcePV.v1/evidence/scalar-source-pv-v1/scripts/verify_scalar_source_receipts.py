#!/usr/bin/env python3
"""Independent exact285-row source-execution/type/axiom acceptance audit.
The cell audit does NOT assert a generic mathematical guard converse.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys,time
S=Path(__file__).resolve().parents[1]
LOCK='054ad58fe66e6b22ef91c06e19c1492fd24c7636c0fc241cba7c3fe760b5294e'
ALLOWED={'propext','Classical.choice','Quot.sound'}
C_PINS={'verified_finite_exp.c':'27a2ea53ced1d46ff681aac7e8ce10a18622af0b93a49eee0cfa1ca5874f4022','verified_finite_log.c':'a22ee045b69b971a6fd3156ba745b3bebf7109ed98db43bf0064244e538b246c','verified_finite_cell.c':'f291fb2062a1879a7d1aaea852eee803ba470455bb3f3fe505f9e1c5136637a9'}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def reports(path):
 text=Path(path).read_text();found={}
 for name,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text):
  need(name not in found,'duplicate axiom report');found[name]={v.strip()for v in axioms.split(',')if v.strip()}
 for name in re.findall(r"'([^']+)' does not depend on any axioms",text):need(name not in found,'duplicate axiom report');found[name]=set()
 return found

def validate(v,context,context_sha,objects,audit_root,required):
 source=Path(v['source']);need(sha(source)==v['sha256'],'current exact source hash');base=audit_root/v['module'];need(base.is_dir(),'module audit absent');candidates=sorted((p for p in base.iterdir()if p.name.isdigit()),key=lambda p:int(p.name),reverse=True);chosen=None
 for folder in candidates:
  receipt=folder/'RUN.json'
  if not receipt.is_file():continue
  r=read(receipt)
  if r.get('status')=='COMPILED'and r.get('source_sha256')==v['sha256']:chosen=(folder,receipt,r);break
 need(chosen is not None,'matching COMPILED receipt absent');folder,receipt,r=chosen
 need(r.get('returncode')==0 and r.get('source_unchanged_during_compile')is True and r.get('module')==v['module'],'completed exact module')
 need(r.get('compiler_sha256')==context['compiler_sha256']and r.get('generic_dependency_context_sha256')==context_sha,'exact compiler/context')
 need(sha(folder/'source.lean')==v['sha256'],'compiler exact source snapshot')
 for filename,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]:need(sha(folder/filename)==r.get(key),'compilerlog hash')
 obj=objects/Path(*v['module'].split('.')).with_suffix('.olean');need(sha(obj)==r.get('object_sha256'),'exact accepted object')
 parsed=reports(folder/'stdout')
 for name in required:need(name in parsed and parsed[name]<=ALLOWED,'missing or forbidden required theorem axiom report: '+name)
 need('error:'not in(folder/'stdout').read_text()and not(folder/'stderr').read_text(),'compiler reported errors')
 return dict(module=v['module'],source=str(source),source_sha256=v['sha256'],receipt=str(receipt),receipt_sha256=sha(receipt),object=str(obj),object_sha256=sha(obj),elapsed_seconds=r['elapsed_seconds'],required_axiom_names=required,rusage=str(folder/'rusage.txt'))

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--kind',choices=['log','cell'],required=True);p.add_argument('--proposal',type=Path,required=True);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');p.add_argument('--out',type=Path,required=True);p.add_argument('--cpus',default='16');p.add_argument('--memory-gib',type=int,default=24);a=p.parse_args();start=time.monotonic();selfpin=sha(__file__);context=read(a.context);context_sha=sha(a.context);objects=Path(context['new_application_object_root']).resolve();out=a.out.resolve();need(out.is_relative_to(objects.parent)and not out.exists(),'fresh context-owned output');need(1<=a.memory_gib<=300,'authorized memory bound');need(sha(context['compiler'])==context['compiler_sha256'],'actual compiler identity')
 need(all(sha(S/'c'/name)==pin for name,pin in C_PINS.items()),'actual Csource byte identity');j=read(a.proposal);need(j.get('row_count')==285 and j.get('rows_sha256')==LOCK,'independent original285-row universe');rowfile=Path(j['rows_source']);need(sha(rowfile)==LOCK,'original row source unchanged');rowline=[v for v in rowfile.read_text().splitlines()if v.startswith('noncomputable def rows : ')];need(len(rowline)==1,'one original array');rows=[[int(v)for v in text.split(',')]for text in re.findall(r'\.leaf ⟨([0-9,]+)⟩',rowline[0])];need(len(rows)==285 and all(len(v)==7 for v in rows),'exact row population');need(rows[0][0]==38358837683 and rows[-1][1]==38359837684,'original endpoints')
 modules=j['modules'];need(len(modules)==9,'exact9 proof chunks');prefix='Log'if a.kind=='log'else'Cell';cursor=0;records=[];required=[];imports=[];source_root=Path(j['source_root']).resolve()
 for slot,v in enumerate(modules):
  need(v['module']==f'RamanujanPV.FiniteScalarMillion.{prefix}{slot:04d}'and v['start']==cursor and v['stop']==min(cursor+32,285),'no dropped/replaced/extra chunk');need(Path(v['source']).resolve()==source_root/Path(*v['module'].split('.')).with_suffix('.lean'),'exact source identity');names=[f'RamanujanPV.FiniteScalarMillion.{a.kind}_{part}_{i:04d}'for i in range(v['start'],v['stop'])for part in ['checked','source']];records.append(validate(v,context,context_sha,objects,source_root/'audit',names));required+=names;imports.append(v['module']);cursor=v['stop']
 need(cursor==285,'exhaustive disjoint original population')
 if a.kind=='log':
  f=read(a.proposal.parent/'LOG_FINAL_PROPOSAL.json');need(f['original_proposal_sha256']==sha(a.proposal),'exact log proposal binding');final={'module':f['module'],'source':f['source'],'sha256':f['sha256']};final_names=['all_log_runs','all_log_source','all_log_real_upper']
 else:final=j['final'];final_names=['all_cell_runs','all_cell_source']
 need(final['module']==f'RamanujanPV.FiniteScalarMillion.{prefix}Final','exact collectivefinal');need(Path(final['source']).resolve()==source_root/Path(*final['module'].split('.')).with_suffix('.lean'),'exact finalsource');fullfinal=['RamanujanPV.FiniteScalarMillion.'+name for name in final_names];records.append(validate(final,context,context_sha,objects,source_root/'audit',fullfinal));required+=fullfinal;imports.append(final['module'])
 out.mkdir(parents=True);src=out/'controller-source';token=hashlib.sha256(str(out).encode()).hexdigest()[:16];module='RamanujanPV.ScalarIndependentAudit.'+a.kind+'_'+token;path=src/Path(*module.split('.')).with_suffix('.lean');path.parent.mkdir(parents=True);text='\n'.join('import '+v for v in imports)+'\nimport RamanujanPV.FiniteExpSource\nnamespace RamanujanPV.ScalarIndependentAudit\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
 for cname,namespace in [('verified_finite_exp.c','FiniteExpSource'),('verified_finite_log.c','FiniteLogSource')]+([('verified_finite_cell.c','FiniteCellSource')]if a.kind=='cell'else[]):
  text+='example : RamanujanPV.'+namespace+'.actualSource=(include_str '+json.dumps(str(S/'c'/cname))+') := by rfl\n'
 for i,row in enumerate(rows):
  r=f'(RamanujanPV.LocalCellsMillion.rows.get {i})';text+=f'example : {r}=⟨'+','.join(str(v)for v in row)+'⟩ := by rfl\n'
  if a.kind=='log':
   text+=f'example : RamanujanPV.FiniteLogExecution.check {r}.n (2^35) 35 {r}.Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_{i:04d}\nexample : RamanujanPV.FiniteLogExecution.SourceExecution {r}.n {r}.Lu := RamanujanPV.FiniteScalarMillion.log_source_{i:04d}\n'
  else:text+=f'example : RamanujanPV.FiniteCellExecution.check {r}=true := RamanujanPV.FiniteScalarMillion.cell_checked_{i:04d}\nexample : RamanujanPV.FiniteCellExecution.SourceExecution {r} := RamanujanPV.FiniteScalarMillion.cell_source_{i:04d}\n'
 if a.kind=='log':text+='example (i : Nat) (hi : i<285) : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get i).n (RamanujanPV.LocalCellsMillion.rows.get i).Lu := RamanujanPV.FiniteScalarMillion.all_log_source i hi\nexample (i : Nat) (hi : i<285) : Real.log ((RamanujanPV.LocalCellsMillion.rows.get i).n:ℝ)≤((RamanujanPV.LocalCellsMillion.rows.get i).Lu:ℝ)/(2:ℝ)^40 := RamanujanPV.FiniteScalarMillion.all_log_real_upper i hi\n'
 else:text+='example (i : Nat) (hi : i<285) : RamanujanPV.FiniteCellExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get i) := RamanujanPV.FiniteScalarMillion.all_cell_source i hi\n'
 for name in required:text+='#print axioms '+name+'\n' 
 text+='end RamanujanPV.ScalarIndependentAudit\n';path.write_text(text);v=dict(module=module,source=str(path),sha256=sha(path));command=[sys.executable,str(S/'scripts/compile_lean_context.py'),module,'--context',str(a.context),'--source-root',str(src),'--audit-root',str(out/'controller-audit'),'--cpus',a.cpus,'--memory-gib',str(a.memory_gib)];r=subprocess.run(command,capture_output=True,text=True);(out/'launcher.stdout').write_text(r.stdout);(out/'launcher.stderr').write_text(r.stderr);need(r.returncode==0,'fresh independent Lean controller compile failed');audit=validate(v,context,context_sha,objects,out/'controller-audit',required);need(sha(__file__)==selfpin,'validatorchanged during audit')
 result=dict(schema='EXHAUSTIVE_SCALAR_SOURCE_EXECUTION_AUDIT_V1',status='VERIFIED_ALL_ORIGINAL_LOG_SOURCE_EXECUTIONS_AND_MATHEMATICAL_BOUNDS'if a.kind=='log'else'VERIFIED_ALL_ORIGINAL_POSITIVE_CELL_SOURCE_EXECUTIONS_GENERIC_MATH_CONVERSE_SEPARATE',kind=a.kind,controller_sha256=selfpin,context=str(a.context),context_sha256=context_sha,proposal=str(a.proposal.resolve()),proposal_sha256=sha(a.proposal),original_rows_sha256=LOCK,c_source_sha256=C_PINS,row_count=285,records=records,controller=audit,exact_type_examples=859,required_axiom_facts=len(required),allowed_axioms=sorted(ALLOWED),seconds=time.monotonic()-start,scope='Actual source AST execution on ALL285 original inputs; no native execution axiom. Generic all-input cell acceptance correctness and C++ generator/caller PV are not asserted by this receipt.')
 (out/'RESULT.json.pending').write_text(json.dumps(result,indent=2)+'\n');(out/'RESULT.json.pending').replace(out/'RESULT.json');print(json.dumps({'status':result['status'],'result':str(out/'RESULT.json'),'seconds':result['seconds']}))
if __name__=='__main__':main()
