#!/usr/bin/env python3
"""Collect every original285 source execution proof without a selection rule."""
from pathlib import Path
import argparse,json,hashlib

S=Path(__file__).resolve().parents[1]

def need(ok,msg):
 if not ok:raise ValueError(msg)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--proposal',type=Path,required=True);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');a=p.parse_args();j=json.loads(a.proposal.read_text());need(j.get('row_count')==285 and len(j.get('modules',[]))==9,'exact285-row proposal required');src=Path(j['source_root']);need(src.resolve().is_relative_to(Path(json.loads(a.context.read_text())['new_application_object_root']).resolve().parent),'ownedsource')
 imports=[];cursor=0
 for v in j['modules']:
  need(v['start']==cursor and v['stop']==min(cursor+32,285),'ordered fullcoverage');need(hashlib.sha256(Path(v['source']).read_bytes()).hexdigest()==v['sha256'],'chunk sourcehash');cursor=v['stop'];imports.append(v['module'])
 need(cursor==285,'complete originalcoverage')
 text='\n'.join('import '+v for v in imports)+'\nimport RamanujanPV.FiniteScalarRows\nnamespace RamanujanPV.FiniteScalarMillion\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
 text+='theorem all_log_runs : FiniteScalarRows.RangeProof (fun i=>FiniteLogExecution.SourceExecution (LocalCellsMillion.rows.get i).n (LocalCellsMillion.rows.get i).Lu) 0 285 :=\n'
 text+='  '+'(FiniteScalarRows.RangeProof.cons '+')NOTVALID' if False else ''
 for i in range(285):text+='  (FiniteScalarRows.RangeProof.cons log_source_'+f'{i:04d}'+'\n'
 text+='    (FiniteScalarRows.RangeProof.nil 285)'+')'*285+'\n'
 text+='theorem all_log_source (i : Nat) (hi : i<285) : FiniteLogExecution.SourceExecution (LocalCellsMillion.rows.get i).n (LocalCellsMillion.rows.get i).Lu := all_log_runs.at (by omega) (by omega)\n'
 text+='theorem all_log_real_upper (i : Nat) (hi : i<285) : Real.log ((LocalCellsMillion.rows.get i).n:ℝ)≤((LocalCellsMillion.rows.get i).Lu:ℝ)/(2:ℝ)^40 := FiniteLogExecution.source_log_upper_sound (all_log_source i hi)\n'
 text+='#print axioms all_log_runs\n#print axioms all_log_source\n#print axioms all_log_real_upper\nend RamanujanPV.FiniteScalarMillion\n'
 path=src/'RamanujanPV/FiniteScalarMillion/LogFinal.lean';need(not path.exists(),'preserve previous collector');path.write_text(text);result=dict(schema='SCALAR_LOG_FINAL_PROPOSAL_V1',original_proposal=str(a.proposal.resolve()),original_proposal_sha256=hashlib.sha256(a.proposal.read_bytes()).hexdigest(),module='RamanujanPV.FiniteScalarMillion.LogFinal',source=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),row_count=285);target=a.proposal.parent/'LOG_FINAL_PROPOSAL.json';need(not target.exists(),'preserve previousfinalproposal');target.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
