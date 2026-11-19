"""Exact receiving-domain queries for the source-corrected C021 rows.
This checks analysis data, not a mathematical program or source-first PV.
"""
from collect import O,load,need,pin
from fractions import Fraction as Q
from premises import branch_case
import json

def q(value):return Q(int(value['numerator']),int(value['denominator']))
def source_x_eligible(b,x):
    for interval in b['domain']['numeric_intervals']:
        lo=interval['lower'];hi=interval['upper'];need(lo['coordinate']=='x'and(hi is None or hi['coordinate']=='x'),'ACTUAL_X_SOURCE_DOMAIN')
        if x<q(lo['rational'])or(x==q(lo['rational'])and not interval['left_closed']):continue
        if hi is not None and(x>q(hi['rational'])or(x==q(hi['rational'])and not interval['right_closed'])):continue
        return True
    return False

def main():
    bounds=load(O/'FINITE_EXPLICIT_FUNCTIONS.json')['bounds'];by={b['bound_id']:b for b in bounds};retired='FOLLOWUP-C021:M-power-420000:3';need(retired not in by,'UNLICENSED_WEIGHTED420000_RECORD_RETIRED');first=[by['FOLLOWUP-C021:M-power-420000:'+str(i)]for i in range(3)];need({b['quantity']for b in first}=={'ES','EP','EQ'},'ACTUAL_FIRST_THREE_SOURCE_RECEIVERS');weighted=by['FOLLOWUP-C021:M-power-550000:3'];need(weighted['quantity']=='EW'and branch_case(weighted)=='B0','ORIGINAL_WEIGHTED550000_ID_CASE_RETAINED')
    queries=[]
    for x in [420000,500000,549999,550000,550001]:
        need(all(source_x_eligible(b,x)for b in first),'FIRST_THREE_ORIGINAL_DOMAINS_PRESERVED');licensed=source_x_eligible(weighted,x);need(licensed==(x>=550000),'WEIGHTED_HAS_OWN_REAL550000_ONSET');queries.append({'exact_x':x,'former_weighted420000_bound_id':retired,'former_id_exists':False,'former_bound_eligible':False,'actual_first_three_eligible':True,'actual_weighted550000_bound_id':weighted['bound_id'],'actual_weighted550000_eligible':licensed})
    print(json.dumps({'status':'PASS_EXACT_SOURCE_RECEIVER_QUERIES_UNLICENSED_WEIGHTED420000_REJECTED_AND_WEIGHTED550000_GUARD_RETAINED','actual_queries':queries,'source':pin(O/'FINITE_EXPLICIT_FUNCTIONS.json'),'numeric_counterexample_claimed':False},sort_keys=True))
if __name__=='__main__':main()
