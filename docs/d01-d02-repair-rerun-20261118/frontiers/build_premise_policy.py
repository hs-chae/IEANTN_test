"""Regenerate the explicit coordinator-reviewed policy for this frozen24 snapshot.

Classification is a declared descriptive source review, never a language model or
fallback heuristic. New source populations require a new reviewed policy.
"""
from collect import *
import argparse

def build():
    data=load(O/'ALL24_SOURCE_BOUND_OBJECTS.json')
    need(sha(O/'ALL24_SOURCE_BOUND_OBJECTS.json')=="5725e0f04680d279cce013b0cd1e029ea3dd6e7c43e21b4527eecdb4e54e3e34",'exact reviewed24-stage source universe')
    prior=load(N/'coordinator-private/twenty-normalized-frontiers-v1/EXACT_ASSUMPTION_FORM_POLICY.json')['all91_forms']
    old={x['exact_assumptions']:x for x in prior}
    new=load(O/'NEW_EXACT_ASSUMPTION_FORMS.json')
    # Exact newly inspected source forms, in the saved source census order.
    formspecs=new if isinstance(new,list) else new['new_forms']
    classifications=['EXACT_SOURCE_BRANCH_PARAMETER','EXACT_SOURCE_BRANCH_PARAMETER','B0_CUMULATIVE_OR_WEAKER','D02_ONLY','D02_ONLY','B0_CUMULATIVE_OR_WEAKER','B0_CUMULATIVE_OR_WEAKER','D02_ONLY','B0_CUMULATIVE_OR_WEAKER']
    additions={str(x['exact_assumptions']):cl for x,cl in zip(formspecs,classifications)}
    need(len(additions)==9,'nine exact new source assumption forms')
    forms=[];lookup={};by={tuple(r['key']):r for r in data['objects']}
    for r in data['objects']:
        st=str(r['raw_M_row']['assumptions'])
        if st not in lookup:lookup[st]=len(forms);forms.append({'form_id':len(forms),'exact_assumptions':st,'object_count':0,'all_object_keys':[]})
        f=forms[lookup[st]];f['object_count']+=1;f['all_object_keys'].append(r['key'])
    need(len(forms)==100,'exact100 reviewed forms')
    out=[]
    for x in forms:
        st=x['exact_assumptions'];need(st in old or st in additions,'unknown assumption has no B0 fallback')
        cl=old[st]['classification'] if st in old else additions[st]
        refs=[{'object_key':k,'source':by[tuple(k)]['source'],'exact_statement_sha256':by[tuple(k)]['raw_M_row_sha256'],'Root_finalization':by[tuple(k)]['Root_finalization']}for k in x['all_object_keys']]
        out.append({**x,'classification':cl,'source_antecedent_object_identities':refs,'reviewed_meaning':old[st]['reviewed_meaning'] if st in old else 'Exact actual source-local antecedent. No inference from B1/D1/D2 names; separate numerical branches require their own declared case.'})
    return forms,{'schema':'EXACT_SOURCE_BOUND_ASSUMPTION_FORM_POLICY_V2_ALL24','created_by':'informed coordinator comparative normalization','unknown_form_policy':'FAIL; no default B0','all100_forms':out}

def main():
    a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args();forms,p=build()
    if args.check:
        need(forms==load(O/'ALL100_ASSUMPTION_FORMS_SOURCE_KEYS.json'),'all100 deterministic exact form census')
        need(p==load(O/'EXACT_ASSUMPTION_FORM_POLICY.json'),'deterministic exact source-bound policy reproduction')
        print('PASS_EXACT100_SOURCE_BOUND_POLICY_REPRODUCTION')
    else:save('ALL100_ASSUMPTION_FORMS_SOURCE_KEYS.json',forms);save('EXACT_ASSUMPTION_FORM_POLICY.json',p)
if __name__=='__main__':main()
