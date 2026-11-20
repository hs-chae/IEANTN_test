#!/usr/bin/env python3
"""Propose source-execution proofs for every original million-window row."""
from pathlib import Path
import argparse,json,hashlib,re
S=Path(__file__).resolve().parents[1]
def need(ok,msg):
 if not ok:raise ValueError(msg)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--rows-source',type=Path,required=True);p.add_argument('--rows-sha256',required=True);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');a=p.parse_args();root=a.out.resolve();need(root.is_relative_to(Path(json.loads(a.context.read_text())['new_application_object_root']).resolve().parent)and not root.exists(),'fresh owned output required');need(hashlib.sha256(a.rows_source.read_bytes()).hexdigest()==a.rows_sha256,'originalrow identity')
 definition=[v for v in a.rows_source.read_text().splitlines()if v.startswith('noncomputable def rows : ')];need(len(definition)==1,'one rowdefinition');rows=[[int(v)for v in m.split(',')]for m in re.findall(r'\.leaf ⟨([0-9,]+)⟩',definition[0])];need(len(rows)==285 and all(len(v)==7 for v in rows),'full original rowuniverse')
 src=root/'source/RamanujanPV/FiniteScalarMillion';src.mkdir(parents=True);modules=[]
 header='import RamanujanPV.FiniteLogExecution\nimport RamanujanPV.LocalCellsMillion.Data\nnamespace RamanujanPV.FiniteScalarMillion\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
 for start in range(0,len(rows),32):
  stop=min(start+32,len(rows));name=f'Log{start//32:04d}';text=header
  for i in range(start,stop):
   n,nxt,j,P,Q,Lu,A=rows[i]
   text+=f'theorem log_checked_{i:04d} : FiniteLogExecution.check (LocalCellsMillion.rows.get {i}).n (2^35) 35 (LocalCellsMillion.rows.get {i}).Lu=true := by decide +kernel\n'
   text+=f'theorem log_source_{i:04d} : FiniteLogExecution.SourceExecution (LocalCellsMillion.rows.get {i}).n (LocalCellsMillion.rows.get {i}).Lu := FiniteLogExecution.source_execution_of_checked log_checked_{i:04d}\n#print axioms log_checked_{i:04d}\n#print axioms log_source_{i:04d}\n'
  text+='end RamanujanPV.FiniteScalarMillion\n';path=src/(name+'.lean');path.write_text(text);modules.append(dict(module='RamanujanPV.FiniteScalarMillion.'+name,source=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),start=start,stop=stop,required_check_axioms=[f'RamanujanPV.FiniteScalarMillion.log_checked_{i:04d}'for i in range(start,stop)],required_source_axioms=[f'RamanujanPV.FiniteScalarMillion.log_source_{i:04d}'for i in range(start,stop)]))
 manifest=dict(schema='ACTUAL_SCALAR_C_EXECUTION_ROW_PROPOSAL_V1',status='UNTRUSTED_REQUIRES_ACTUAL_KERNEL_CHECKS',rows_source=str(a.rows_source.resolve()),rows_sha256=a.rows_sha256,row_count=285,source_root=str(root/'source'),modules=modules);(root/'PROPOSAL.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({'manifest':str(root/'PROPOSAL.json'),'modules':len(modules),'row_count':len(rows)}))
if __name__=='__main__':main()
