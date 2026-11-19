"""Exact source-bound premise policies for descriptive comparisons.

Unknown assumptions never default to B0. Source-local case names are not global
mathematical premises. Whole non-scalar operators retain their exact antecedents.
"""
import functools
from collect import O,load,need
@functools.lru_cache(None)
def policies():
    p=load(O/'EXACT_ASSUMPTION_FORM_POLICY.json')['all100_forms']
    need(len(p)==100,'all100 exact assumption forms')
    d={str(x['exact_assumptions']):x for x in p}
    need(len(d)==100,'unique exact assumption form policy')
    return d

def policy(assumptions):
    k=str(assumptions);need(k in policies(),'unknown assumption form: no default B0')
    return policies()[k]

def object_scope(r):
    p=policy(r['raw_M_row']['assumptions']);cl=p['classification'];q=r.get('Root_object_qualification')or{}
    if cl=='FULL_RH_ONLY':return 'EXPLICIT_FULL_RH_COMPARATOR'
    if cl=='MIXED_QUOTED_SOURCE_COMPARATOR':return 'SOURCE_COMPARATOR_WITH_SEPARATE_FULL_RH_BRANCH'
    if cl=='COUNTERFACTUAL_ONLY'or q.get('D01_premise_eligibility')=='COUNTERFACTUAL_OR_SCOPED_CONDITIONAL_ONLY':return 'EXPLICIT_COUNTERFACTUAL_NOT_CURRENT_D01_PREMISE'
    # Preserve the historical coarse descriptive field on finite records. It
    # was never a premise-admission test. Exact policy/branch_case below alone
    # decide eligibility; even a sentence saying 'neither D01 nor D02' can
    # retain the old INPUT_SCENARIO label without gaining a D02 premise.
    text=str(r['raw_M_row']['assumptions'])
    if 'without D01 or D02'in text:return 'B0_OR_WEAKER_AS_DECLARED'
    return 'INPUT_SCENARIO_EXACT_AS_DECLARED'if any(v in text for v in ['D02','B2','B1','27/32','Hprime'])else'B0_OR_WEAKER_AS_DECLARED'

def branch_case(b):
    p=policy(b['assumptions']);cl=p['classification'];scope=b['scope']
    # Conditional scope wins even over a malformed explicit branch-case field.
    if scope=='EXPLICIT_FULL_RH_COMPARATOR':return 'FULL_RH'
    if scope=='EXPLICIT_COUNTERFACTUAL_NOT_CURRENT_D01_PREMISE':return 'COUNTERFACTUAL_D02'
    if scope=='SOURCE_COMPARATOR_WITH_SEPARATE_FULL_RH_BRANCH':return 'SOURCE_COMPARATOR_SYMBOLIC_ONLY'
    if b.get('case'):
        need(b['case']in ['B0','D02'],'only exact source-local B0/D02 numerical branches')
        weaker_keys={('FOLLOWUP-C007','M-matched-inverse-'+str(i))for i in range(4)}|{('FOLLOWUP-C018','M-targets')}
        if cl=='D02_ONLY'and b['case']=='B0':need(tuple(b['object_key'])in weaker_keys and b.get('source_explicit_weaker_B0_case')is True,'D02-only source cannot acquire B0 without its exact reviewed source-explicit weaker-case proof')
        return b['case']
    if cl=='D02_ONLY':return 'D02'
    if cl=='B0_CUMULATIVE_OR_WEAKER':return 'B0'
    if tuple(b['object_key'])==('FOLLOWUP-C011','M-free-B1'):return 'D02'
    # Non-scalar objects can have several separate antecedents; no guessed
    # numerical eligibility is needed to retain their exact operator body.
    return 'PAIRED_PARAMETER_RULE_SYMBOLIC_ONLY'
