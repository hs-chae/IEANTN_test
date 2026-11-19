"""Exact source/receiver bindings for Root's read nonfoundation literal clauses.
No mathematical program, new numerical certificate or source-first PV is claimed.
"""
from collect import O,load,need,pin,save
from fractions import Fraction as Q
from collections import defaultdict
from premises import branch_case

def q(v):return Q(int(v['numerator']),int(v['denominator']))
def main():
    data=load(O/'FINITE_EXPLICIT_FUNCTIONS.json');bs=data['bounds'];byid={x['bound_id']:x for x in bs};groups=defaultdict(list)
    for b in bs:groups[tuple(b['object_key'])].append(b)
    source=load(O/'ALL24_SOURCE_BOUND_OBJECTS.json');by={tuple(r['key']):r for r in source['objects']};index=load(O/'ROOT_UNEXPANDED2252_EXACT_GROUP_INDEX.json')['groups'];wanted=load(O/'ROOT_NONFOUNDATION536_LITERAL_SCOPE_READBACK_PENDING_BINDINGS.json')['identified_concrete_alias_groups_requiring_exact_mapping'];keys=[]
    for g in index:
        if g['group_id']in wanted:
            for item in g['members']:
                key=tuple(item['key'])
                if by[key]['family']=='Mertens':keys.append(key)
    need(len(keys)==len(set(keys))==32,'ALL32_ROOT_READ_NONFOUNDATION_M_LITERAL_OBJECTS')
    records=[]
    for key in keys:
        row=by[key];direct=groups.get(key,[]);record={'key':list(key),'source':{k:row['source'][k]for k in ['file','sha256','physical_LF','physical_LF_end']},'exact_statement':row['raw_M_row']['exact_statement'],'exact_assumptions':row['raw_M_row']['assumptions'],'original_domain':row['raw_M_row']['full_domain']}
        if direct:
            record.update(status='DIRECT_EXACT_SOURCE_RECEIVER_FUNCTIONS',target_bound_ids=[b['bound_id']for b in direct],target_source_keys=[list(key)])
        elif key==('FOLLOWUP-C007','M-basic-mid-comparison'):
            target=groups[('FOLLOWUP-C007','M-d02_basic_mid.txt-2-11')];need({b['quantity']for b in target}=={'ES','EP','EQ','EW'},'EXACT_BASIC_TAPE_ALL_FOUR')
            for b in target:
                need(q(b['coefficient'])==Q('9.727e-10')and q(b['x_decay_exponent'])==0 and b['log_denominator_degree']==(2 if b['quantity']=='EW' else 3),'EXACT_SAME_SOURCE_RECEIVER_SHAPE');need(branch_case(b)=='D02','ACTUAL_SAME_D02_PREMISE');interval=b['domain']['numeric_intervals'];need(len(interval)==1 and interval[0]['lower']['coordinate']=='L'and q(interval[0]['lower']['rational'])<=230 and interval[0]['upper']is None,'EXACT_SOURCE_RAY_COVERS230')
            record.update(status='EXACT_SAME_SOURCE_METHOD_BASIC_VECTOR_ALIAS',target_bound_ids=[b['bound_id']for b in target],target_source_keys=[b['object_key']for b in target],rational_derivation='Same c=9727/10^13, alpha=0; degree3 for ES/EP/EQ anddegree2 forEW, identicalD02 premise, target whole ray begins230.')
        elif key[1]=='M-D02-tail-finite-analytic':
            cid=key[0];target=groups[(cid,'M-D02-table-P,Q-22')]+groups[(cid,'M-D02-table-u-22')]+groups[(cid,'M-D02-table-j-28')];need({b['quantity']for b in target}=={'ES','EP','EQ','EW'},'ALL_FOUR_NO_QRH_TABLE_TARGETS')
            for b in target:
                need(b['assumptions']==row['raw_M_row']['assumptions'],'EXACT_WEAKER_NO_QRH_PREMISE_PRESERVED');need(q(b['coefficient'])<=Q('.090')and q(b['x_decay_exponent'])==0 and b['log_denominator_degree']==(2 if b['quantity']=='EW' else 3),'EXACT_SAME_OR_STRONGER_LOG_CAP');interval=b['domain']['numeric_intervals'];need(len(interval)==1 and interval[0]['lower']['coordinate']=='x'and q(interval[0]['lower']['rational'])<=2**28 and interval[0]['upper']is None,'EXACT_RAY_CONTAINS2_POWER28')
            record.update(status='SAME_PREMISE_EXACT_CAP_WITH_EARLIER_SOURCE_ONSETS',target_bound_ids=[b['bound_id']for b in target],target_source_keys=[b['object_key']for b in target],rational_derivation='The actual no-QRH table already givesstrict.090 in degree3(firstthree)/degree2(weighted) from20million/35million, both<=268435456. No QRH-dependent stronger branch is substituted for this weaker-premise claim.')
        else:raise ValueError('UNBOUND_ROOT_READ_CONCRETE_M_CLAUSE '+str(key))
        record['actual_current_target_records']=[byid[i]for i in record['target_bound_ids']];records.append(record)
    save('ROOT_NONFOUNDATION32_M_LITERAL_BINDINGS_V1.json',{'status':'PASS_ALL32_ROOT_READ_CONCRETE_M_CLAUSES_DIRECTLY_REPRESENTED_OR_EXACT_SAME_PREMISE_ALIASED','records':records,'root_full_read':pin(O/'ROOT_NONFOUNDATION536_LITERAL_SCOPE_READBACK_PENDING_BINDINGS.json'),'functions':pin(O/'FINITE_EXPLICIT_FUNCTIONS.json'),'all32_exact_source_keys_checked':True,'new_mathematical_or_program_claims':False});print('PASS32_ROOT_READ_M_LITERAL_SOURCE_BINDINGS')
if __name__=='__main__':main()
