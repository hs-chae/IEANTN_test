"""Strict source/receiver/domain metadata gate; no mathematical program is run.

The full Root-scoped source universe is checked, not selected by this scalar gate.
Manual regression contracts independently name source coefficients and targets.
"""
import argparse,collections,copy,json,math,re,sys
from pathlib import Path
from fractions import Fraction as Q
sys.path.insert(0,str(Path(__file__).resolve().parent))
from collect import O,N,load,need,pin,sha,EXPECTED,read_bytes
from premises import branch_case
from compare import canonical_intervals,eligible

def q(x):
    need(isinstance(x,dict)and set(x)=={'numerator','denominator'},'EXACT_RATIONAL_SCHEMA')
    need(all(isinstance(x[k],str)and re.fullmatch('-?[0-9]+',x[k])for k in x),'EXACT_RATIONAL_TEXT')
    need(int(x['denominator'])>0,'POSITIVE_RATIONAL_DENOMINATOR')
    return Q(int(x['numerator']),int(x['denominator']))
def one(group,target):
    a=[b for b in group if b['quantity']==target];need(len(a)==1,'ONE_SOURCE_RECEIVING_BRANCH '+target);return a[0]
def cap(group,target,c,a,d):
    b=one(group,target);need(b['kind']=='M_power_log','EXACT_M_ERROR_LAW_KIND')
    need((q(b['coefficient']),q(b['x_decay_exponent']),b['log_denominator_degree'])==(Q(c),Q(a),d),'SOURCE_COEFFICIENT_RATE_LOG_DEGREE '+str(b['object_key'])+' '+target)
def interval(b,coordinate,lo,hi=None):
    z=b['domain']['numeric_intervals'];need(len(z)==1,'ONE_EXPLICIT_SOURCE_INTERVAL')
    i=z[0];need(i['lower']['coordinate']==coordinate and q(i['lower']['rational'])==Q(lo),'SOURCE_LOWER_COORDINATE_ONSET')
    need((i['upper']is None if hi is None else isinstance(i['upper'],dict)and i['upper']['coordinate']==coordinate and q(i['upper']['rational'])==Q(hi)),'SOURCE_UPPER_ENDPOINT_NOT_A_RAY')
    need(i['left_closed']is True,'SOURCE_INCLUSIVE_LEFT_ENDPOINT')
    if hi is not None:need(i['right_closed']is True,'SOURCE_INCLUSIVE_RIGHT_ENDPOINT')
def guards(groups,objects):
    from reviewed_literal_interfaces import entries
    for key,entry in entries().items():
        actual=groups[key];expected=entry['functions'];need(len(actual)==len(expected),'SOURCE_LITERAL_RECEIVER_BRANCH_COUNT')
        if all(b['quantity']!='G'for b in expected):need(objects[key]['scalar_M_receiving_target_eligible']is True and objects[key]['source_defined_function_interface']['literal_provider_is_not_an_arithmetic_receiving_error']is False,'REVIEWED_M_RECEIVER_NEVER_LABELLED_PROVIDER')
        for op in entry.get('native_operators',[]):
            need(op['kind']=='FIXED_SOURCE_DEFINED_DENSITY_KERNEL_COMPOSITE_RECEIVER'and op['numerical_evaluation_performed']is False,'EXACT_UNOPTIMIZED_SOURCE_DENSITY_KERNEL_OPERATOR')
            for ref in op['exact_named_definition_sources']:
                need(sha(ref['file'])==ref['sha256'],'FIXED_OPERATOR_DEFINITION_SOURCE_SHA');lines=read_bytes(ref['file']).decode().split('\n');need('\n'.join(lines[ref['physical_LF']-1:ref['physical_LF_end']])==ref['exact_readback'],'FIXED_OPERATOR_EXACT_SOURCE_DEFINITION')
        for aa,ee in zip(actual,expected):
            for field in ['kind','quantity','coefficient','x_decay_exponent','log_denominator_degree','case','coefficient_log_shift','coefficients','degree','positive_terms']:
                need(aa.get(field)==ee.get(field),'SOURCE_LITERAL_COORDINATE_EXTRACTION_CORRESPONDENCE '+str(key)+' '+field)
            if 'explicit_source_root'in ee:
                dd=aa['domain'];root=ee['explicit_source_root'];need(dd.get('numeric_intervals')==[] and len(dd.get('exact_symbolic_intervals',[]))==1,'SOURCE_LITERAL_EXACT_ROOT_DOMAIN');ii=dd['exact_symbolic_intervals'][0];need(ii['lower']=={'coordinate':'x',**root}and ii['upper']is None and ii['left_closed']is True and ii['right_closed']is False,'SOURCE_LITERAL_EXACT_ROOT_DOMAIN');projection=dd.get('plot_intervals',[]);need(len(projection)==1 and projection[0]['lower']['coordinate']=='x'and projection[0]['lower']['rational']==root['certified_open_rational_bracket'][1]and projection[0]['upper']is None and projection[0]['left_closed']is False,'SOURCE_LITERAL_CONSERVATIVE_ROOT_PROJECTION')
            if 'explicit_source_root'in ee:need(('strict_open_subray'in aa['domain'])==(ee.get('strict_above_root_proved_by_source')is True),'EXACT_SOURCE_LICENSED_ROOT_STRICTNESS_ONLY')
            if 'explicit_domain_intervals'in ee:need(aa['domain']['numeric_intervals']==ee['explicit_domain_intervals'],'EXACT_SOURCE_MIXED_X_LOG_FINITE_INTERVAL')
            for coordinate in ['x','L']:
                if 'explicit_interval_'+coordinate in ee:
                    lo,hi=ee['explicit_interval_'+coordinate];ii=aa['domain']['numeric_intervals'];need(len(ii)==1 and ii[0]['lower']['coordinate']==coordinate and ii[0]['upper']is not None and ii[0]['upper']['coordinate']==coordinate and ii[0]['lower']['rational']==lo and ii[0]['upper']['rational']==hi and ii[0]['left_closed']and ii[0]['right_closed'],'SOURCE_LITERAL_FINITE_INTERVAL_NEVER_A_RAY')
                if 'explicit_onset_'+coordinate in ee:
                    ii=aa['domain']['numeric_intervals'];need(len(ii)==1 and ii[0]['lower']['coordinate']==coordinate and ii[0]['lower']['rational']==ee['explicit_onset_'+coordinate]and ii[0]['upper']is None and ii[0]['left_closed'],'SOURCE_LITERAL_REAL_RAY_ONSET')
    for candidate in ['FOLLOWUP-C021','FOLLOWUP-C024']:
        key=(candidate,'M-power-420000');need({b['quantity']for b in groups[key]}=={'ES','EP','EQ'},'FIRST_THREE_ONLY_420000_NO_WEIGHTED_RECEIVER')
    weighted=groups[('FOLLOWUP-C021','M-power-550000')];need(weighted and all(b['quantity']=='EW'for b in weighted),'OWN_WEIGHTED550000_SOURCE_BRANCH')
    axes=load(O/'EXACT_BARE_INTERVAL_SOURCE_AXIS_POLICY.json')['all248_exact_objects']
    need(len(axes)==248,'ALL248_BARE_INTERVAL_SOURCE_CONTEXTS')
    for rule in axes:
        key=tuple(rule['key']);need(key in objects and rule['source_identity']==objects[key]['source'],'EXACT_SOURCE_AXIS_OBJECT_IDENTITY')
        context=rule['exact_same_source_context'];path=Path(context['file']);need(sha(path)==context['sha256'],'SOURCE_AXIS_PROVIDER_CONTEXT_HASH');lines=read_bytes(path).split(b'\n')
        for line in context['physical_byte_LF']:need(lines[line['physical_LF']-1].decode()==line['readback'],'EXACT_PHYSICAL_LF_AXIS_CONTEXT')
        for b in groups[key]:
            for interval0 in b['domain']['numeric_intervals']:
                need(interval0['lower']['coordinate']==rule['axis'] and (interval0['upper']is None or interval0['upper']['coordinate']==rule['axis']),'SOURCE_AXIS_X_VS_LOG_NOT_DEFAULT')
    for key in [('FOLLOWUP-C003','M-finite-pointwise'),('FOLLOWUP-C009','M-finite-pointwise'),('FOLLOWUP-C010','M-empty')]:need(not objects[key]['finite_bound_ids'],'DOMAIN_INEQUALITY_IS_NOT_ERROR_BOUND')
    for (cid,ident),gg in groups.items():
        if cid in ['FOLLOWUP-C020','FOLLOWUP-C023']and ident.startswith('M-step-'):
            for b in gg:
                if b['quantity']=='ES' and any(t in b['domain']['exact_predicate']for t in ['additionally x≥2278383 for D1','D1 only from 2278383','additionally x>=2278383 for D1']):
                    for dom in b['domain']['numeric_intervals']:
                        lo=dom['lower'];need(lo['coordinate']=='L' or q(lo['rational'])>=2278383,'COPIED_SOURCE_ES_EXTRA_ONSET_GUARD')
    for b in groups.get(('FOLLOWUP-C018','M-targets'),[]):need(q(b['x_decay_exponent'])==0 and b['log_denominator_degree']==(0 if b['quantity']=='EW'else 1),'G_M_IS_NOT_LOG_POWER_UNITS')
    for b in groups.get(('FOLLOWUP-C010','M-fallback'),[]):need(b['log_denominator_degree']==(-2 if b['quantity']=='EW'else -1),'DENSITY_FREE_SOURCE_POSITIVE_LOG_FACTOR')
    def g(c,k):
        key=(f'FOLLOWUP-C{c:03}',k);need(key in groups,'REQUIRED_LITERAL_SOURCE_FUNCTION '+str(key));return groups[key]
    for c in [19,22]:
        z=g(c,'M.power47')
        for t in ['ES','EP','EQ','EW']:
            cap(z,t,'1233/100000','1/8',0 if t=='EW'else 1);interval(one(z,t),'L',200)
    interval(g(3,'R-old-margin-16')[0],'L','36.72','39.32')
    for c,k,v in [(17,'R-loglayer-133',['1','14','145','1412','13985','145450','1610021','19063832']),(18,'R-new-200-0',['1','14','116.6']),(23,'R02-quad-49.31-80.6',['1','14','80.6'])]:
        b=g(c,k)[0];need([q(a)for a in b['coefficients']]==list(map(Q,v)),'SOURCE_R_FULL_COEFFICIENT_VECTOR')
    for c,k,d in [(16,'R-repair-69',65),(20,'R-high-rung-40',35),(24,'R-new-Q-1425-36-d36',32)]:need(all(b['degree']==d for b in g(c,k)),'SOURCE_ORDER_TO_CANONICAL_DEGREE')
    for t in ['ES','EP','EQ']:cap(g(18,'M-new-poly-1-20'),t,'.037',0,3)
    cap(g(18,'M-new-poly-0-20'),'EW','.035',0,2)
    for t in ['ES','EP','EQ','EW']:cap(g(23,'M02-log-59.99'),t,'4.27e-8',0,2 if t=='EW'else 3)
    cap(g(17,'M-power-prefix-1-2'),'ES','.22775','5/32',1)
    interval(g(17,'M-power-prefix-1-2')[0],'x',293)
    for t in ['ES','EP','EQ','EW']:cap(g(22,'D02.M.fast.168'),t,'.256418','5/32',0 if t=='EW'else 1)
    c20=g(20,'R-stronger-constant-3')[0];interval(c20,'L','30.75',191)
    c20['_intervals']=canonical_intervals(c20);need(not eligible(c20,1000),'C020_FALSE_OLD_WHOLE_RAY_MUST_NOT_REENTER')
    c23=g(23,'R02-global-scope-correction')[0];interval(c23,'L','30.714','477.005')
    c23['_intervals']=canonical_intervals(c23);need(not eligible(c23,1000),'C023_REFUTED_GLOBAL_BOUND_NOT_A_POSITIVE_FUNCTION')
    interval(g(22,'D02.R.raw')[0],'L',49)
    need(g(22,'D02.R.raw')[0]['domain'].get('source_provider_join',{}).get('tail_anchor_L')=='200','JOINED_RAY_RETAINS_TAIL_PROVIDER_GUARDS')
    for t in ['ES','EP','EQ','EW']:
        b=one(g(9,'M-small-root-.29446-'+{'ES':'D1','EP':'P','EQ':'Q','EW':'D2'}[t]),t)
        d=b['domain'];need(bool(d.get('exact_symbolic_intervals'))and bool(d.get('plot_intervals'))and d.get('unplotted_root_microband_is_not_a_claimed_failure')is True,'EXACT_ROOT_NOT_REPLACED_BY_RATIONAL_UPPER_BRACKET')
    local=g(15,'R-local-segment')[0]['domain']['numeric_intervals'][0]
    need(q(local['lower']['rational'])==38358837683 and q(local['upper']['rational'])==38358937683 and local['left_closed']is True and local['right_closed']is False,'SOURCE_LOCAL_N_SUBSTITUTION_AND_HALF_OPEN_DOMAIN')
    z=objects[('FOLLOWUP-C022','D02.M.general-kernel')]
    need('finite I_f(y)'in z['current_qualified_statement'],'FINITE_INTEGRAL_ROOT_QUALIFICATION')
    need(z['symbolic_definition']['body']==z['current_qualified_statement'],'RAW_UNRESTRICTED_KERNEL_IS_NOT_THE_ADMITTED_BODY')
    for c,k in [(20,'R-DP-RH-comparator'),(24,'R-DP-RH')]:need(objects[(f'FOLLOWUP-C{c:03}',k)]['scope']=='EXPLICIT_FULL_RH_COMPARATOR','FULL_RH_NOT_CURRENT_B0_OR_D02')
    for obj in objects.values():
        qualification=obj.get('Root_object_qualification')or{}
        if qualification.get('object_class')=='VALID_GUARD_FAILURE_DIAGNOSTIC_NO_POSITIVE_SUFFIX':need(not obj['finite_bound_ids'],'DIAGNOSTIC_NO_POSITIVE_SUFFIX')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');ap.add_argument('--branch-fixture',type=Path);ap.add_argument('--object-fixture',type=Path);args=ap.parse_args()
    source=load(O/'ALL24_SOURCE_BOUND_OBJECTS.json');normalized=load(O/'NORMALIZED_OBJECTS.json');finite=load(O/'FINITE_EXPLICIT_FUNCTIONS.json')
    need(sha(O/'NORMALIZED_OBJECTS.json')==finite['canonical_data']['sha256'],'ATOMIC_NORMALIZED_AND_EXPANDED_VERSION_CORRESPONDENCE')
    src={tuple(r['key']):r for r in source['objects']};objects={tuple(r['key']):r for r in normalized['objects']}
    need(len(src)==len(objects)==11411,'ALL11411_UNIQUE_SOURCE_IDENTITIES')
    need(set(src)==set(objects),'EXACT_FULL_ROOT_SOURCE_UNIVERSE_NO_SELECTION')
    need(collections.Counter(k[0]for k in src)==collections.Counter({f'FOLLOWUP-C{c:03}':n for c,n in EXPECTED.items()}),'EXACT_ALL24_FLOOR_COUNTS')
    sources={}
    for k,r in src.items():
        z=objects[k];need(z['source']==r['source']and z['raw_review_row_hash']==r['raw_M_row_sha256'],'WRITTEN_FILE_ID_LF_HASH_OBJECT_IDENTITY')
        need(z['statement_exact']==r['raw_M_row']['exact_statement'],'PRESERVE_EVERY_ORIGINAL_RAW_STATEMENT')
        qf=(r.get('Root_object_qualification')or{}).get('current_qualified_statement');need(z['current_qualified_statement']==qf,'ROOT_QUALIFIED_BODY_CORRESPONDENCE')
        sr=r['source'];f=Path(sr['file']);sources[str(f)]=sr['sha256']
        need(0<sr['physical_LF']<=sr.get('physical_LF_end',sr['physical_LF']),'POSITIVE_PHYSICAL_BYTE_LF_RANGE')
    for path,digest in sources.items():need(sha(path)==digest,'CURRENT_FROZEN_SOURCE_BYTES '+path)
    groups=collections.defaultdict(list);ids=set()
    for b in finite['bounds']:
        need(b['bound_id']not in ids,'UNIQUE_EXPANDED_BRANCH_ID');ids.add(b['bound_id']);k=tuple(b['object_key']);need(k in src,'BRANCH_ROOT_SOURCE_IDENTITY')
        need(b['source']==src[k]['source'],'EXACT_BRANCH_WRITTEN_SOURCE')
        need(b['quantity']in ['G','ES','EP','EQ','EW','LQ'],'EXPLICIT_RECEIVING_TARGET')
        need(b['domain'].get('numeric_intervals')or b['domain'].get('exact_symbolic_intervals'),'NO_UNEXPLAINED_EMPTY_LITERAL_FUNCTION_DOMAIN')
        if b['kind']in ['M_positive_sum','M_exp_positive_sum']:
            need(isinstance(b.get('positive_terms'),list)and 1<=len(b['positive_terms'])<=4,'SMALL_FINITE_POSITIVE_SUM_SCHEMA')
            for term in b['positive_terms']:need(q(term['coefficient'])>0 and q(term['x_decay_exponent'])>=0 and type(term['log_denominator_degree'])is int and type(term['pi_power'])is int and term['pi_power']in [-1,0,1],'EXACT_POSITIVE_SUM_TERM_UNITS')
        if 'coefficient_log_shift'in b:q(b['coefficient_log_shift'])
        if b['kind']=='R_inverse_log_polynomial':need(b['degree']==len(b['coefficients'])-1 and all(q(z).denominator>0 for z in b['coefficients']),'CANONICAL_FULL_POLYNOMIAL_VECTOR')
        else:q(b['coefficient']);q(b['x_decay_exponent']);need(type(b['log_denominator_degree'])is int,'INTEGER_RECEIVING_LOG_DEGREE')
        ca=branch_case(b);need(ca in ['B0','D02','COUNTERFACTUAL_D02','FULL_RH','SOURCE_COMPARATOR_SYMBOLIC_ONLY'],'NO_UNKNOWN_OR_FALLBACK_NUMERICAL_PREMISE')
        groups[k].append(copy.deepcopy(b))
    if args.branch_fixture:
        fx=load(args.branch_fixture);need(set(fx)in [{'object_key','quantity','replace'},{'object_key','quantity','replace','case'}],'STRICT_SEMANTIC_FIXTURE_SCHEMA')
        key=tuple(fx['object_key']);matched=[b for b in groups[key]if b['quantity']==fx['quantity']and ('case'not in fx or b.get('case')==fx['case'])];need(bool(matched),'FIXTURE_EXACT_RECEIVING_BRANCH');z=matched[0];need(isinstance(fx['replace'],dict),'FIXTURE_REPLACEMENT_OBJECT')
        z.update(fx['replace'])
    if args.object_fixture:
        fx=load(args.object_fixture);need(set(fx)=={'object_key','replace'},'STRICT_OBJECT_FIXTURE_SCHEMA');key=tuple(fx['object_key']);need(key in objects and isinstance(fx['replace'],dict),'OBJECT_FIXTURE_BOUND_SOURCE');objects[key]=copy.deepcopy(objects[key]);objects[key].update(fx['replace'])
    for key,gg in groups.items():
        for bb in gg:
            need(bb['assumptions']==src[key]['raw_M_row']['assumptions'],'EXACT_SOURCE_ASSUMPTIONS_NO_UNVERIFIED_PREMISE')
            branch_case(bb)
    guards(groups,objects)
    print(json.dumps({'status':'PASS_ALL24_SOURCE_RECEIVER_DOMAIN_AND_PREMISE_METADATA','objects':len(objects),'expanded_branches':len(ids),'actual_source_files':len(sources),'assertions_used_for_acceptance':False,'scientific_execution':False},sort_keys=True))
if __name__=='__main__':main()
