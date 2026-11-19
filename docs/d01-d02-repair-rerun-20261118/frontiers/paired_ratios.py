"""Exact elementary ratios of already accepted paired Mertens functions.

A positive rational Taylor lower sum verifies an exponential inequality. No ANT
source computation or new analytic theorem is used. Absent pairs stay absent.
"""
from collect import *
from fractions import Fraction as Q
from compare import original_case,q

def main():
    bs=load(O/'FINITE_EXPLICIT_FUNCTIONS.json')['bounds'];groups=collections.defaultdict(list)
    for b in bs:
        if b['kind']=='M_power_log':groups[(tuple(b['object_key']),b['quantity'])].append(b)
    rows=[]
    for (key,target),xs in groups.items():
        old=[x for x in xs if original_case(x)=='B0'];new=[x for x in xs if original_case(x)=='D02']
        for a in old:
          for b in new:
            if key==('FOLLOWUP-C018','M-targets')and q(a['coefficient'])!=q(b['coefficient']):continue
            for ia in a['domain']['numeric_intervals']:
              for ib in b['domain']['numeric_intervals']:
                # This exact closure is for common log-coordinate rays only.
                if ia['upper']is not None or ib['upper']is not None:continue
                if any(z['lower'].get('coordinate')!='L'or'log_of_rational'in z['lower']for z in [ia,ib]):continue
                L=max(q(ia['lower']['rational']),q(ib['lower']['rational']));da=q(b['x_decay_exponent'])-q(a['x_decay_exponent']);k=a['log_denominator_degree']-b['log_denominator_degree']
                derivative_nonpositive=(da>=0 and k<=0)or(da>0 and Q(k)<=da*L)
                c=q(b['coefficient'])/q(a['coefficient']);r=c*L**k;z=da*L;term=Q(1);s=term;terms=0
                if derivative_nonpositive and z>=0:
                    while s<=r and terms<256:terms+=1;term=term*z/terms;s+=term
                strict=derivative_nonpositive and s>r
                rows.append({'source_object_key':list(key),'target':target,'identical_functions_on_common_ray':da==0 and k==0 and c==1,'B0_function_id':a['bound_id'],'D02_function_id':b['bound_id'],'source':a['source'],'common_ray_lower_L':str(L),'source_domains':[ia,ib],'ratio_exact':{'coefficient':str(c),'decay_rate_difference':str(da),'log_power':k},'log_ratio_derivative':'-decay_rate_difference + log_power/L','derivative_nonpositive_on_common_ray':derivative_nonpositive,'strict_D02_function_below_B0_function_on_common_ray':strict,'exact_positive_Taylor_lower_check':{'z':str(z),'terms_through_degree':terms,'lower_sum':str(s),'required_ratio_at_onset':str(r),'strict_lower_sum_greater_than_ratio':s>r}if derivative_nonpositive else None,'scope':'Comparison of these submitted sufficient functions only. The complete within-method signed/operator envelope can be stronger; no proof of actual arithmetic-error lower bounds.'})
    save('EXACT_SOURCE_PAIRED_M_FUNCTION_RATIO_CHECKS.json',{'schema':'EXACT_PAIRED_SUBMITTED_M_FUNCTION_COMPARISONS_V1','rows':rows,'all_explicit_same_object_same_target_same_parameter_log_coordinate_ray_pairs_included':True,'matched_parameter_rule':'For the C018 multi-tolerance target row, compare only the same target tolerance. Other paired source rows already fix their comparison parameter. No comparison count is an experiment count.','strict_pairs':sum(r['strict_D02_function_below_B0_function_on_common_ray']for r in rows),'not_independent_trials':True})
    print('Exact paired function ratios',len(rows),'strict common-ray comparisons',sum(r['strict_D02_function_below_B0_function_on_common_ray']for r in rows))
def validate_receipt(bs,negative=False):
    data=load(O/'EXACT_SOURCE_PAIRED_M_FUNCTION_RATIO_CHECKS.json');bm={b['bound_id']:b for b in bs}
    if negative:
        victim=next(r for r in data['rows']if r['strict_D02_function_below_B0_function_on_common_ray'])
        victim['exact_positive_Taylor_lower_check']['lower_sum']='0'
    for r in data['rows']:
        a=bm[r['B0_function_id']];b=bm[r['D02_function_id']]
        need(a['kind']==b['kind']=='M_power_log'and a['quantity']==b['quantity']==r['target'],'paired functions same actual observable')
        need(a['object_key']==b['object_key']==r['source_object_key']and original_case(a)=='B0'and original_case(b)=='D02','paired exact source and premise correspondence')
        da=q(b['x_decay_exponent'])-q(a['x_decay_exponent']);k=a['log_denominator_degree']-b['log_denominator_degree'];c=q(b['coefficient'])/q(a['coefficient']);L=Q(r['common_ray_lower_L'])
        need(r['ratio_exact']=={'coefficient':str(c),'decay_rate_difference':str(da),'log_power':k},'paired exact source ratio parameters')
        ia,ib=r['source_domains'];need(ia in a['domain']['numeric_intervals']and ib in b['domain']['numeric_intervals'],'paired domains exact source intervals')
        need(ia['upper']is None and ib['upper']is None and L==max(q(ia['lower']['rational']),q(ib['lower']['rational'])),'paired whole common ray')
        dn=(da>=0 and k<=0)or(da>0 and Q(k)<=da*L);need(dn==r['derivative_nonpositive_on_common_ray'],'paired analytic ratio monotonicity')
        z=r['exact_positive_Taylor_lower_check']
        if z is not None:
            need(dn and da*L>=0 and Q(z['z'])==da*L,'positive Taylor domain')
            m=z['terms_through_degree'];need(type(m)is int and 0<=m<=256,'finite exact positive Taylor index')
            term=Q(1);s=term
            for j in range(1,m+1):term=term*da*L/j;s+=term
            need(s==Q(z['lower_sum'])and Q(z['required_ratio_at_onset'])==c*L**k,'exact rational Taylor ratio proof receipt')
            need(r['strict_D02_function_below_B0_function_on_common_ray']==(dn and s>c*L**k),'strict common-ray ratio conclusion')
    need(data['strict_pairs']==sum(r['strict_D02_function_below_B0_function_on_common_ray']for r in data['rows']),'paired ratio census')
    return {'explicit_pairs':len(data['rows']),'strict_common_ray_function_pairs':data['strict_pairs']}

if __name__=='__main__':main()
