#!/usr/bin/env python3
"""Non-strict applicability ONLY; does not assume desired rowpositivity."""
from pathlib import Path
import argparse,json,hashlib

S=Path(__file__).resolve().parents[1]

def need(ok,msg):
 if not ok:raise ValueError(msg)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--original-log-proposal',type=Path,required=True);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');a=p.parse_args();root=a.out.resolve();need(root.is_relative_to(Path(json.loads(a.context.read_text())['new_application_object_root']).resolve().parent)and not root.exists(),'fresh owned proposal');j=json.loads(a.original_log_proposal.read_text());need(j.get('row_count')==285 and j.get('rows_sha256')=='054ad58fe66e6b22ef91c06e19c1492fd24c7636c0fc241cba7c3fe760b5294e','all original285records');need(hashlib.sha256(Path(j['rows_source']).read_bytes()).hexdigest()==j['rows_sha256'],'original unchangedrowdata');src=root/'source/RamanujanPV/FiniteScalarMillion';src.mkdir(parents=True);modules=[]
 header='import RamanujanPV.FiniteCellProtected\nimport RamanujanPV.LocalCellsMillion.Data\nnamespace RamanujanPV.FiniteScalarMillion\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
 for start in range(0,285,32):
  stop=min(start+32,285);name=f'Domain{start//32:04d}';text=header
  for i in range(start,stop):
   text+=f'theorem cell_domain_{i:04d} : FiniteCellProtected.Domain (LocalCellsMillion.rows.get {i}) where\n'
   text+='  toWordFits := by constructor <;>decide +kernel\n'
   for field in ['nLower','advance','upper','jBound','qBound','pBound','logPositive','logResponse','jExp','aFloor']:text+='  '+field+' := by decide +kernel\n'
   text+=f'#print axioms cell_domain_{i:04d}\n'
  text+='end RamanujanPV.FiniteScalarMillion\n';path=src/(name+'.lean');path.write_text(text);modules.append(dict(module='RamanujanPV.FiniteScalarMillion.'+name,source=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),start=start,stop=stop))
 text='\n'.join('import '+v['module']for v in modules)+'\nimport RamanujanPV.FiniteScalarRows\nnamespace RamanujanPV.FiniteScalarMillion\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
 text+='theorem all_cell_domain_records : FiniteScalarRows.RangeProof (fun i=>FiniteCellProtected.Domain (LocalCellsMillion.rows.get i)) 0 285 :=\n'
 for i in range(285):text+=f'  (FiniteScalarRows.RangeProof.cons cell_domain_{i:04d}\n'
 text+='    (FiniteScalarRows.RangeProof.nil 285)'+')'*285+'\n'
 text+='theorem all_cell_domains (i : Nat) (hi : i<285) : FiniteCellProtected.Domain (LocalCellsMillion.rows.get i) := all_cell_domain_records.at (by omega) (by omega)\n#print axioms all_cell_domain_records\n#print axioms all_cell_domains\nend RamanujanPV.FiniteScalarMillion\n';path=src/'DomainFinal.lean';path.write_text(text)
 result=dict(schema='FINITE_CELL_NONSTRICT_SOURCE_APPLICABILITY_PROPOSAL_V1',status='UNTRUSTED_ALL_KERNEL_CHECKS_REQUIRED',row_count=285,rows_sha256=j['rows_sha256'],source_root=str(root/'source'),modules=modules,final=dict(module='RamanujanPV.FiniteScalarMillion.DomainFinal',source=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest()),excluded='No final strict inequality/desiredpositivegap/desiredRamanujanconclusion premise. Allwordbounds andnon-strictsourceguardsincludingactualtypedlogresponse andA=floor arechecked.')
 (root/'PROPOSAL.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'proposal':str(root/'PROPOSAL.json'),'rows':285,'chunks':9,'desiredstrictpremise':False}))
if __name__=='__main__':main()
