#!/usr/bin/env python3
"""Exhaustive original285 NON-STRICT applicability gate, no positivity premise."""
from pathlib import Path
import argparse,json,hashlib,subprocess,sys,time
from verify_scalar_source_receipts import need,sha,read,validate,C_PINS,S,LOCK
BASE_VALIDATOR_SHA='14bfd755f30fe914a0504c35623cabf84ec23dd5628fa6864e4792ce8b7d69a5'
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--proposal',type=Path,required=True);p.add_argument('--original-log-proposal',type=Path,required=True);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');p.add_argument('--out',type=Path,required=True);p.add_argument('--cpus',default='16');a=p.parse_args();start=time.monotonic();selfpin=sha(__file__);need(sha(S/'scripts/verify_scalar_source_receipts.py')==BASE_VALIDATOR_SHA,'exact tested common validator');c=read(a.context);context_sha=sha(a.context);objects=Path(c['new_application_object_root']).resolve();out=a.out.resolve();need(out.is_relative_to(objects.parent)and not out.exists(),'fresh context-ownedout');j=read(a.proposal);base=read(a.original_log_proposal);need(j.get('row_count')==285 and j.get('rows_sha256')==base.get('rows_sha256')==LOCK,'exact285originaluniverse');need(sha(base['rows_source'])==LOCK,'originalrowsource');need(all(sha(S/'c'/k)==v for k,v in C_PINS.items()),'sourceCbytes')
 import re
 rowline=[v for v in Path(base['rows_source']).read_text().splitlines()if v.startswith('noncomputable def rows : ')];need(len(rowline)==1,'oneoriginalarray');rows=[[int(v)for v in s.split(',')]for s in re.findall(r'\.leaf ⟨([0-9,]+)⟩',rowline[0])];need(len(rows)==285 and all(len(v)==7 for v in rows),'all285sevenfields');source_root=Path(j['source_root']).resolve();modules=j['modules'];need(len(modules)==9,'nineexactchunks');cursor=0;records=[];required=[];imports=[]
 for slot,v in enumerate(modules):
  need(v['module']==f'RamanujanPV.FiniteScalarMillion.Domain{slot:04d}'and v['start']==cursor and v['stop']==min(cursor+32,285),'orderedfullpopulation');need(Path(v['source']).resolve()==source_root/Path(*v['module'].split('.')).with_suffix('.lean'),'exactsourceidentity');names=[f'RamanujanPV.FiniteScalarMillion.cell_domain_{i:04d}'for i in range(v['start'],v['stop'])];records.append(validate(v,c,context_sha,objects,source_root/'audit',names));required+=names;imports.append(v['module']);cursor=v['stop']
 need(cursor==285,'nocoveragegap');f=j['final'];need(f['module']=='RamanujanPV.FiniteScalarMillion.DomainFinal'and Path(f['source']).resolve()==source_root/Path(*f['module'].split('.')).with_suffix('.lean'),'exactcollective');names=['RamanujanPV.FiniteScalarMillion.all_cell_domain_records','RamanujanPV.FiniteScalarMillion.all_cell_domains'];records.append(validate(f,c,context_sha,objects,source_root/'audit',names));required+=names;imports.append(f['module']);out.mkdir(parents=True);src=out/'controller-source';module='RamanujanPV.DomainIndependentAudit.a'+hashlib.sha256(str(out).encode()).hexdigest()[:16];path=src/Path(*module.split('.')).with_suffix('.lean');path.parent.mkdir(parents=True)
 text='\n'.join('import '+v for v in imports)+'\nnamespace RamanujanPV.DomainIndependentAudit\nopen RamanujanPV FiniteScalarMachine WindowCells\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
 text+='''example (r : RawFactoredCell) : FiniteCellProtected.WordFits r ↔
    r.n<2^64 ∧r.next<2^64 ∧r.j<2^64 ∧r.P<2^64 ∧r.Q<2^64 ∧r.Lu<2^64 ∧r.A<2^64 := by
  constructor
  · intro h;exact ⟨h.nWord,h.nextWord,h.jWord,h.pWord,h.qWord,h.luWord,h.aWord⟩
  · rintro ⟨a,b,c,d,e,f,g⟩;exact ⟨a,b,c,d,e,f,g⟩
example (r : RawFactoredCell) : FiniteCellProtected.Domain r ↔
    FiniteCellProtected.WordFits r ∧38358837683≤r.n ∧r.n<r.next ∧r.next≤2000000000001 ∧
    r.j≤r.n ∧r.Q≤r.j ∧r.P≤r.next-1 ∧0<r.Lu ∧
    invoke FiniteCellExecution.prototypes FiniteCellExecution.service "rpc_log_upper" [word64 r.n]=some (word64 r.Lu) ∧
    r.j*eHi≤r.n*2^60 ∧r.A=(r.n*eLo)/r.Lu := by
  constructor
  · intro h;exact ⟨h.toWordFits,h.nLower,h.advance,h.upper,h.jBound,h.qBound,h.pBound,h.logPositive,h.logResponse,h.jExp,h.aFloor⟩
  · rintro ⟨a,b,c,d,e,f,g,h,i,j,k⟩;exact ⟨a,b,c,d,e,f,g,h,i,j,k⟩
'''
 for name,ns in [('verified_finite_exp.c','FiniteExpSource'),('verified_finite_log.c','FiniteLogSource'),('verified_finite_cell.c','FiniteCellSource')]:text+='example : '+ns+'.actualSource=(include_str '+json.dumps(str(S/'c'/name))+') := by rfl\n'
 for i,row in enumerate(rows):
  r=f'(LocalCellsMillion.rows.get {i})';text+=f'example : {r}=⟨'+','.join(str(v)for v in row)+'⟩ := by rfl\n';text+=f'example : FiniteCellProtected.Domain {r} := FiniteScalarMillion.cell_domain_{i:04d}\n'
 text+='example (i : Nat) (hi : i<285) : FiniteCellProtected.Domain (LocalCellsMillion.rows.get i) := FiniteScalarMillion.all_cell_domains i hi\n'
 for name in required:text+='#print axioms '+name+'\n'
 text+='end RamanujanPV.DomainIndependentAudit\n';path.write_text(text);command=[sys.executable,str(S/'scripts/compile_lean_context.py'),module,'--context',str(a.context),'--source-root',str(src),'--audit-root',str(out/'controller-audit'),'--cpus',a.cpus,'--memory-gib','24'];r=subprocess.run(command,capture_output=True,text=True);(out/'launcher.stdout').write_text(r.stdout);(out/'launcher.stderr').write_text(r.stderr);need(r.returncode==0,'fresh exactnonstrictcontroller failed');audit=validate(dict(module=module,source=str(path),sha256=sha(path)),c,context_sha,objects,out/'controller-audit',required);need(sha(__file__)==selfpin,'controllerchanged');result=dict(status='VERIFIED_ALL285_NONSTRICT_SOURCE_APPLICABILITY_NO_DESIRED_STRICT_PREMISE',controller_sha256=selfpin,common_validator_sha256=BASE_VALIDATOR_SHA,context_sha256=context_sha,proposal_sha256=sha(a.proposal),original_rows_sha256=LOCK,rows=285,records=records,controller=audit,exact_type_examples=576,axiom_reports=287,domain_has_no_desired_strict_premise='Kernel-checked IFF expands EXACTcompleteDomain intoWordFits+all10non-strictguards, includingactualtypedlogresponse andA=floor; desiredscaledP-squareinequalitydoesnotoccur.',seconds=time.monotonic()-start)
 (out/'RESULT.json.pending').write_text(json.dumps(result,indent=2)+'\n');(out/'RESULT.json.pending').replace(out/'RESULT.json');print(json.dumps({'status':result['status'],'result':str(out/'RESULT.json'),'seconds':result['seconds']}))
if __name__=='__main__':main()
