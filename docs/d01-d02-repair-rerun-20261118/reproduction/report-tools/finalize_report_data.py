"""Add completion labels to the frozen all24 snapshot after exact Root acceptance."""
from pathlib import Path
import argparse,copy,hashlib,json,math,os,tempfile

def need(v,m):
 if not v:raise ValueError(m)
def pairs(xs):
 d={}
 for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
 return d
def finite(s):
 v=float(s);need(math.isfinite(v),'nonfinite or overflow JSON float');return v
def load(p):return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_float=finite,parse_constant=lambda s:(_ for _ in ()).throw(ValueError(s)))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p):return {'path':str(Path(p).resolve()),'sha256':sha(p)}
def readpin(z):
 p=Path(z['path']);need(p.is_file() and sha(p)==z['sha256'],'exact accepted final-comparison evidence bytes');return p
def atomic_new(path,obj):
 p=Path(path);need(not p.exists(),'fresh output, preserve earlier snapshots');b=(json.dumps(obj,indent=2,sort_keys=True,ensure_ascii=False,allow_nan=False)+'\n').encode();fd,name=tempfile.mkstemp(prefix='.'+p.name+'.',dir=p.parent)
 try:
  with os.fdopen(fd,'wb')as f:f.write(b);f.flush();os.fsync(f.fileno())
  os.link(name,p)
 finally:Path(name).unlink(missing_ok=True)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--data',type=Path,required=True);p.add_argument('--Root-comparison-authority',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(a.out.resolve().parent==a.data.resolve().parent,'retain same complete floor/private-source manifest context');x=load(a.data);r=load(a.Root_comparison_authority);need(r.get('reviewed_by')=='/root' and r.get('status')=='ROOT_APPROVED_FINAL24_QUANTITATIVE_COMPARISON_AND_SOURCE_COVERAGE','actual exact Root comparison authority');need(r['source_snapshot']==pin(a.data),'Root authority pins this immutable snapshot');need(r['all11411_current_objects_accounted_for'] is True,'full accepted source-claim scope accounted');need(isinstance(r.get('accepted_comparison_inputs'),list) and r['accepted_comparison_inputs'],'exact final source/data/coverage inputs');need(isinstance(r.get('actual_plot_execution_receipts'),list) and len(r['actual_plot_execution_receipts'])==2,'two actual independent-environment plot receipts')
 for z in r['accepted_comparison_inputs']+r['actual_plot_execution_receipts']+[r['source_coverage_receipt']]:readpin(z)
 need(x['currently_Root_finalized_case_count']==24 and x['scoped_objects_in_finalized_floors']==11411 and x['cases_with_actual_clean_relocated_full_reproduction']==24,'all24 mathematical and actual numerical gates closed');need(len(x['stages'])==24 and len(x['all48_family_summaries'])==48,'complete canonical cases and both families');out=copy.deepcopy(x);out['status']='COMPLETE_QUALIFIED_MATHEMATICAL_AND_REPRODUCED_NUMERICAL_FOLLOWUP_WITH_RECORDED_COMPARISON';out['original_snapshot_before_completion_labels']=pin(a.data);out['final_comparison_acceptance']=pin(a.Root_comparison_authority)
 for z in out['stages']:z['functional_frontier_comparison']='Complete recorded source-clause coverage and explicit scalar/vector comparison; selected numerical grids are diagnostic, exact signs/roots retained, quantified/kernel operators retained unoptimized. No global optimality or overall arm advantage inferred.'
 restored=copy.deepcopy(out);restored['status']=x['status'];restored.pop('original_snapshot_before_completion_labels');restored.pop('final_comparison_acceptance')
 for before,after in zip(x['stages'],restored['stages']):after['functional_frontier_comparison']=before['functional_frontier_comparison']
 need(restored==x,'only allowlisted completion-label fields changed; mathematical/resource/history/floor statements unchanged');atomic_new(a.out,out);receipt={'status':'PASS_ADDITIVE_COMPLETION_LABEL_FINALIZATION_WITH_RECURSIVE_ALLOWLIST_DIFF','input':pin(a.data),'output':pin(a.out),'Root_comparison_authority':pin(a.Root_comparison_authority),'allowed_field_changes':['status','original_snapshot_before_completion_labels','final_comparison_acceptance','stages[*].functional_frontier_comparison'],'all_other_source_proof_resource_history_floor_fields_unchanged':True,'sealer_source':pin(Path(__file__)),'new_models_or_mathematical_numerics':0};rp=a.out.with_suffix('.FINALIZATION_RECEIPT.json');atomic_new(rp,receipt);print(json.dumps({'status':receipt['status'],'receipt':pin(rp)},sort_keys=True))
if __name__=='__main__':main()
