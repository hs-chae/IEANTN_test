#!/usr/bin/env python3
"""Freeze-aware, fail-closed source/math review preservation gate; no proof/PV relabeling."""
from pathlib import Path
import argparse,hashlib,json,math,os,subprocess,sys
import yaml
S=Path(__file__).resolve().parent;N=S.parents[3]
BASE='00402b9b85c1bb3b71b8bd4da0020a5f87a3a870'
ROOT_FROZEN_SHA256='dab88bcd6d52c7f085650b3378497fb36eb8951551a1582a2940bfc8b30415e9'
def need(b,m):
 if not b:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def finite(s):
  v=float(s);need(math.isfinite(v),'nonfinite JSON');return v
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_float=finite,
  parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
class UniqueLoader(yaml.SafeLoader):pass
def unique_mapping(loader,node,deep=False):
 d={}
 for k,v in node.value:
  key=loader.construct_object(k,deep=deep);need(key not in d,'duplicate YAML key');d[key]=loader.construct_object(v,deep=deep)
 return d
UniqueLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG,unique_mapping)
def metadata(node):return yaml.load((N/'IEANTN/Nodes'/node/'formalization.yaml').read_text(),Loader=UniqueLoader)
def imports(row):return [(x['node'],x['conclusion'])for x in row['imports']]
def check_imports(node,expected):
 m=metadata(node);need(m['node']['status']=='awaiting-verification','unexpected promotion:'+node)
 need(set(x['id']for x in m['conclusions'])==set(expected),'conclusion scope:'+node)
 for row in m['conclusions']:need(imports(row)==expected[row['id']],'source edge list:'+node+':'+row['id'])
 return m

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--scope',type=Path,default=S/'SCOPE_FINAL.json');p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh receipt required');scope=read(a.scope)
 need(sha(a.scope)==ROOT_FROZEN_SHA256,'Root authorized frozen handoff identity')
 need(scope['stage']=='FROZEN_ROOT_HANDOFF_FOR_FINAL_REVIEW','final source handoff not frozen')
 need(scope['declarations']==53 and len(scope['files'])==16 and len({x['path']for x in scope['files']})==16,'exact frozen53/16 scope')
 for row in scope['files']:need(sha(N/row['path'])==row['sha256'],'reviewed source changed:'+row['path'])
 common=[('RH.v1','hypothesis'),('RHPrimeCounting.v1','gm_source'),('Buthe.v1','theorem_2_psi'),('Buthe.v1','theorem_2_li_minus_riemann_pi')]
 check_imports('RHPrimeCounting/v2',{'elementary_prime_powers':[],'refined_transfer':common,'transfer_gain':[],'ch_Epi':common+[('RHSmoothing.v1','recovered_ch_psi')],'box_Epi':common+[('RHSmoothing.v1','box_psi')],'ch_classical_gain':common+[('RHSmoothing.v1','recovered_ch_psi')],'box_point_100':common+[('RHSmoothing.v1','box_psi')]})
 nine=common+[('Buthe.v1','table_1_interval_bounds'),('Buthe.v1','table_2_interval_bounds'),('Buthe.v1','theorem_2_li_minus_pi'),('Buthe.v1','theorem_2_li_gt_pi'),('Buthe2016.v1','theorem_2_li_minus_pi')]
 old=next(x for x in metadata('RamanujanGap/v3')['conclusions']if x['id']=='full_profile');old_inputs=imports(old)
 need(len(old_inputs)==6 and set(old_inputs)<=set(nine),'original six source inputs changed')
 need(set(nine)-set(old_inputs)=={('RHPrimeCounting.v1','gm_source'),('Buthe.v1','theorem_2_psi'),('Buthe.v1','table_1_interval_bounds')},'new premises not exactly disclosed')
 check_imports('RamanujanGap/v4',{'margin_620b':nine,'full_profile':[('RamanujanGap.v4','margin_620b'),('RamanujanGap.v3','full_profile')],'ramanujan':[('RamanujanGap.v4','margin_620b')],'retains_original_margin':[]})
 pk=check_imports('PrimeKernelInputs/v1',{'octic_215':[('PrimeKernelInputs.v2','octic_215_explicit_formula'),('PrimeKernelInputs.v2','octic_215_zero_estimate')],'octic_family':[('PrimeKernelInputs.v2','octic_family_explicit_formula'),('PrimeKernelInputs.v2','octic_family_zero_estimate')]})
 check_imports('PrimeKernelInputs/v2',{x:[]for x in ['octic_215_explicit_formula','octic_215_zero_estimate','octic_family_explicit_formula','octic_family_zero_estimate']})
 for row in pk['conclusions']:need(row['designated']=='four-components-proved','pack designated proof')
 for row in metadata('PrimeKernelInputs/v2')['conclusions']:
  j=next(x for x in row['justifications']if x['id']==row['designated']);need(j['kind']=='none-yet','unproved predicate promotion')
 bm=metadata('BoxMellinInputs/v1')
 for row in bm['conclusions']:
  j=next(x for x in row['justifications']if x['id']==row['designated'])
  if row['id']=='stieltjes_trapezoid':need(row['designated']=='unconditional-limit-proof'and j['kind']=='lean-noncompliant','exact Stieltjes proof status')
  else:need(j['kind']=='none-yet','unclosed Mellin promotion')
 preserved=[]
 for name in ['IEANTN/Nodes/BoxMellinInputs/v1/Conclusions.lean','IEANTN/Nodes/PrimeKernelInputs/v1/Conclusions.lean','IEANTN/Nodes/RamanujanGap/v3/Conclusions.lean']:
  raw=subprocess.check_output(['git','show',BASE+':'+name],cwd=N);need(raw==(N/name).read_bytes(),'historical mathematical contracts changed:'+name);preserved.append({'file':name,'sha256':sha(N/name),'base_commit':BASE})
 need((N/'Solutions/RHPrimeCounting.v2/Solution.lean').read_bytes()==(N/'Solutions/RHLimit.v1/integration/PiSolution.lean').read_bytes(),'publication mirror changed')
 validator=S/'vendor/validate_ledger.py';cmd=[sys.executable,str(validator),'--scope',str(S/'scope.csv'),'--ledger',str(S/'ledger.final.csv'),'--require-final'];r=subprocess.run(cmd,text=True,capture_output=True);need(r.returncode==0,'identity/evidence gate failed:'+r.stdout+r.stderr)
 receipt={'status':'PASS_FROZEN_CANONICAL_SOURCE_MATH_PRESERVATION_GATE','scope_sha256':sha(a.scope),'ledger_sha256':sha(S/'ledger.final.csv'),'validator_sha256':sha(validator),'gate_sha256':sha(__file__),'python_optimization':sys.flags.optimize,'files':len(scope['files']),'declaration_identities':scope['declarations'],'old_mathematical_contracts_preserved':preserved,'canonical_pi_props':7,'canonical_ramanujan_props':4,'new_Ram_source_union_count':9,'old_Ram_source_count':6,'new_sources_disclosed':['GM_Q_Theorem1_1','Buthe.theorem_2_psi','Buthe.table_1_interval_bounds'],'source_first_PV_claim':False,'scope':'Bounded new canonical consumers and selected metadata; no exhaustive inherited source census/official Comparator claim. Independent kernel compile receipt is separate.','identity_validator_stdout':r.stdout}
 q=a.out.with_name('.'+a.out.name+'.pending');need(not q.exists(),'stale pending receipt');q.write_text(json.dumps(receipt,indent=2)+'\n');os.replace(q,a.out);print(receipt['status'])
if __name__=='__main__':main()
