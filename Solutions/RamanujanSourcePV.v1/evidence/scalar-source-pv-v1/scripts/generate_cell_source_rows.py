#!/usr/bin/env python3
"""Propose actual positive C executions for all original285 scalar rows."""
from pathlib import Path
import argparse,json,hashlib,re

S=Path(__file__).resolve().parents[1]

def need(ok,msg):
 if not ok:raise ValueError(msg)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--original-log-proposal',type=Path,required=True);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');a=p.parse_args();root=a.out.resolve();need(root.is_relative_to(Path(json.loads(a.context.read_text())['new_application_object_root']).resolve().parent)and not root.exists(),'freshownedroot');j=json.loads(a.original_log_proposal.read_text());need(j.get('row_count')==285,'285originalrows');rows=Path(j['rows_source']);need(hashlib.sha256(rows.read_bytes()).hexdigest()==j['rows_sha256'],'lockedrowsource');src=root/'source/RamanujanPV/FiniteScalarMillion';src.mkdir(parents=True);modules=[]
 header='import RamanujanPV.FiniteCellExecution\nimport RamanujanPV.LocalCellsMillion.Data\nnamespace RamanujanPV.FiniteScalarMillion\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
 for start in range(0,285,32):
  stop=min(start+32,285);name=f'Cell{start//32:04d}';text=header
  for i in range(start,stop):
   text+=f'theorem cell_checked_{i:04d} : FiniteCellExecution.check (LocalCellsMillion.rows.get {i})=true := by decide +kernel\n'
   text+=f'theorem cell_source_{i:04d} : FiniteCellExecution.SourceExecution (LocalCellsMillion.rows.get {i}) := FiniteCellExecution.source_execution_of_checked cell_checked_{i:04d}\n#print axioms cell_checked_{i:04d}\n#print axioms cell_source_{i:04d}\n'
  text+='end RamanujanPV.FiniteScalarMillion\n';path=src/(name+'.lean');path.write_text(text);modules.append(dict(module='RamanujanPV.FiniteScalarMillion.'+name,source=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),start=start,stop=stop))
 text='\n'.join('import '+v['module']for v in modules)+'\nimport RamanujanPV.FiniteScalarRows\nnamespace RamanujanPV.FiniteScalarMillion\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
 text+='theorem all_cell_runs : FiniteScalarRows.RangeProof (fun i=>FiniteCellExecution.SourceExecution (LocalCellsMillion.rows.get i)) 0 285 :=\n'
 for i in range(285):text+='  (FiniteScalarRows.RangeProof.cons cell_source_'+f'{i:04d}'+'\n'
 text+='    (FiniteScalarRows.RangeProof.nil 285)'+')'*285+'\n'
 text+='theorem all_cell_source (i : Nat) (hi : i<285) : FiniteCellExecution.SourceExecution (LocalCellsMillion.rows.get i) := all_cell_runs.at (by omega) (by omega)\n#print axioms all_cell_runs\n#print axioms all_cell_source\nend RamanujanPV.FiniteScalarMillion\n';path=src/'CellFinal.lean';path.write_text(text)
 result=dict(schema='ACTUAL_FINITE_CELL_SOURCE_EXECUTION_PROPOSAL_V1',status='UNTRUSTED_REQUIRES_KERNEL_SOURCE_EXECUTIONS',row_count=285,rows_source=str(rows),rows_sha256=j['rows_sha256'],source_root=str(root/'source'),modules=modules,final=dict(module='RamanujanPV.FiniteScalarMillion.CellFinal',source=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest()),not_claimed='No all-input mathematical positive-output converse is asserted; selected-instance mathematical postconditions are composed separately with the original checkedrows and source e/log bounds.')
 (root/'PROPOSAL.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'proposal':str(root/'PROPOSAL.json'),'chunks':9,'rows':285}))
if __name__=='__main__':main()
