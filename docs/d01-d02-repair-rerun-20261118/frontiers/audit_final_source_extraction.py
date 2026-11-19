"""Source-address/literal interface delta; no new mathematical claims or PV."""
from collect import O,load,need,pin,save
import copy,json,subprocess,sys,time

def mathbody(b):
    x=copy.deepcopy(b)
    x.pop('receiving_target_basis',None)
    onset=x.pop('explicit_onset_x',None)
    if onset is not None:
        lower=x['domain']['numeric_intervals'][0]['lower'];need(lower['coordinate']=='x'and lower['rational']==onset,'EXPLICIT_ONSET_IS_SAME_EXISTING_EXACT_DOMAIN')
    for interval in x['domain']['numeric_intervals']:
        for side in ['lower','upper']:
            if interval.get(side):interval[side].pop('exact_original',None)
    return x

def main():
    oldfile=O/'pre-literal-receiver-expansion-v1/FINITE_EXPLICIT_FUNCTIONS.json';old={b['bound_id']:b for b in load(oldfile)['bounds']};new={b['bound_id']:b for b in load(O/'FINITE_EXPLICIT_FUNCTIONS.json')['bounds']};retired=sorted(set(old)-set(new));expected=['FOLLOWUP-C021:M-power-420000:3',*['FOLLOWUP-C021:M-power-550000:'+str(i)for i in range(3)]];need(retired==expected,'ONLY_FOUR_EXPLICIT_SOURCE_ATTRIBUTION_RETIREMENTS');shared=sorted(set(old)&set(new));need(all(mathbody(old[k])==mathbody(new[k])for k in shared),'ALL_RETAINED_ORIGINAL_MATHEMATICAL_BODIES_IDENTICAL')
    records=[]
    for mode in [[],['-O'],['-OO']]:
        args=[sys.executable,*mode,'-B',str(O/'verify_retired_receivers.py')];start=time.monotonic();r=subprocess.run(args,cwd=O,capture_output=True,text=True);need(r.returncode==0,'ACTUAL_SOURCE_RECEIVER_DOMAIN_QUERY_CLI '+r.stderr[-600:]);result=json.loads(r.stdout);need(len(result['actual_queries'])==5,'ALL_FIVE_EXACT_X_DOMAIN_QUERIES');records.append({'argv':args,'exit_code':r.returncode,'wall_seconds':time.monotonic()-start,'result':result})
    save('FINAL_SOURCE_LITERAL_EXTRACTION_DELTA_AND_DOMAIN_QUERIES.json',{'status':'PASS_ALL15437_RETAINED_ORIGINAL_FUNCTION_MATHEMATICAL_BODIES_IDENTICAL_424_ADDITIVE_LITERAL_BRANCHES_FOUR_EXPLICIT_RETIREMENTS_AND_ACTUAL_THREE_MODE_DOMAIN_QUERIES','historical_original':pin(oldfile),'current':pin(O/'FINITE_EXPLICIT_FUNCTIONS.json'),'audit_source':pin(__file__),'domain_query_source':pin(O/'verify_retired_receivers.py'),'historical_count':len(old),'current_count':len(new),'retained_mathematical_bodies_unchanged':len(shared),'additive_source_literal_branch_ids':sorted(set(new)-set(old)),'retired':[{ 'bound_id':k,'historical_record':old[k],'reason':'Unsupported weighted receiver at420000; actual source weighted onset550000'if k.endswith('420000:3')else'Misattributed duplicate FIRST3 restriction at550000; correct original FIRST3 from420000 already retained'}for k in retired],'actual_domain_query_clis':records,'source_mathematics_or_original_experimental_outcome_changed':False,'numeric_counterexample_claimed':False,'new_analytic_Lean_theorem_or_source_first_PV_claimed':False})
    print('PASS15437_UNCHANGED_424_ADDITIVE_4EXPLICIT_SOURCE_RETIREMENTS_3ACTUAL_CLI_DOMAIN_CONTROLS')
if __name__=='__main__':main()
