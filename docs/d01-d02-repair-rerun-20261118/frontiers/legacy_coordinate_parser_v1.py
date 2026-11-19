"""Normalize finite scalar/vector profiles; preserve every other exact source-defined rule.

This is a data conversion, not a numerical proof or a new formula interpreter.
"""
import ast, collections, functools, math, re
from fractions import Fraction as Q
from collect import N,O,load,save,need,pin

NUM=r'(?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?'
@functools.lru_cache(None)
def true_vector(degree):
    need(0<=degree<=1000,'explicit finite degree')
    out=[]
    for d in range(degree+1):
        j=d+4
        out.append(sum(math.factorial(i)*math.comb(j,i)-math.factorial(i)*math.factorial(j-i) for i in range(j+1)))
    return out

def rat(x):
    q=Q(str(x));return {'numerator':str(q.numerator),'denominator':str(q.denominator)}
def simple_number(s):
    s=s.strip().replace(' ','').replace('−','-').replace('·','*').replace('^','**')
    tree=ast.parse(s,mode='eval')
    def go(x):
        if isinstance(x,ast.Constant) and type(x.value)in [int,float]:return Q(ast.get_source_segment(s,x))
        if isinstance(x,ast.UnaryOp) and isinstance(x.op,ast.USub):return -go(x.operand)
        if isinstance(x,ast.BinOp):
            a,b=go(x.left),go(x.right)
            if isinstance(x.op,ast.Add):return a+b
            if isinstance(x.op,ast.Sub):return a-b
            if isinstance(x.op,ast.Mult):return a*b
            if isinstance(x.op,ast.Div):return a/b
            if isinstance(x.op,ast.Pow) and b.denominator==1 and abs(b)<=1000:return a**int(b)
        raise ValueError('not a rational coefficient')
    return go(tree.body)
def plain(s):
    return s.replace('−','-').replace('≥','>=').replace('≤','<=').replace('∞','infinity').replace('²','^2').replace('³','^3').replace('⁴','^4').replace('⁶','^6').replace('⁻','-').replace('·','*').replace('e^(','exp(').replace('\\(','').replace('\\)','').replace('\\ge','>=').replace('\\le','<=')

def domain(row):
    s=plain(row['raw_M_row']['full_domain']).replace('log x','L');d={'exact_predicate':row['raw_M_row']['full_domain'],
        'real_or_integer':row['raw_M_row']['real_or_integer'],'variable':None,'intervals':[],
        'no_join_or_domain_extension_inferred':True,'machine_interval_complete':False}
    # Only source-explicit numeric bounds become machine intervals; all others remain exact symbolic predicates.
    endnum=r'(?![\w^/]|\.\d)'
    m=re.search(r'\b([Ltu])\s*>=\s*('+NUM+r')'+endnum,s)
    if m:d.update(variable='L=log(x)',intervals=[{'lower':rat(m[2]),'upper':None,'lower_inclusive':True,'upper_inclusive':False}],machine_interval_complete=True)
    else:
        m=re.search(r'(?:\b[Ltu]\s*(?:in|∈)\s*)?([\[(])\s*('+NUM+r')\s*,\s*('+NUM+r'|infinity)\s*([\])])',s)
        if m and ('L' in s or 'log' in s or s.startswith('[') or 'x' in s):
            d.update(variable='x' if 'x' in s and 'L' not in s else 'L=log(x)',intervals=[{'lower':rat(m[2]),'upper':None if m[3]=='infinity' else rat(m[3]),'lower_inclusive':m[1]=='[','upper_inclusive':m[4]==']' and m[3]!='infinity'}],machine_interval_complete=True)
        else:
            m=re.search(r'\bx\s*>=\s*('+NUM+r')'+endnum,s)
            if m:d.update(variable='x',intervals=[{'lower':rat(m[1]),'upper':None,'lower_inclusive':True,'upper_inclusive':False}],machine_interval_complete=True)
    if d['intervals'] and d['intervals'][0]['upper'] is None:
        upper=re.search(r'(?:through|up to|[Ltx]\s*<=)\s*('+NUM+r')'+endnum,s)
        if upper:d['intervals'][0].update(upper=rat(upper[1]),upper_inclusive=True)
        elif any(t in s.lower() for t in ['finite','scan interval','through','bounded']):d['machine_interval_complete']=False
    return d

def degree_for(row,label,n):
    cid=row['candidate_id'];fname=row['source']['file'].rsplit('/',1)[-1]
    # These conversions come from the exact source definitions, never bare label comparison.
    if label in ['M']:return n
    if cid in ['FOLLOWUP-C001','FOLLOWUP-C006','FOLLOWUP-C007']:return n
    if cid in ['FOLLOWUP-C002','FOLLOWUP-C008']:return n-4
    if cid in ['FOLLOWUP-C005','FOLLOWUP-C014']:return n-1
    return None

def Rbound(row):
    st=plain(row['raw_M_row']['exact_statement']);cid=row['candidate_id'];ident=row['claim_id']
    def vector(v,label=None):
        v=list(map(Q,v))
        return [{'kind':'R_inverse_log_polynomial','quantity':'G(L)=L^6 R(exp(L))/exp(2L)','operator':'>',
            'coefficients_by_inverse_log_degree':[rat(x) for x in v],'highest_inverse_log_degree':len(v)-1,
            'source_label':label,'domain':domain(row),'pure_full_coefficient_vector':v==true_vector(len(v)-1)}]
    m=re.search(r'G(?:\(L\))?>T_\{(\d+),([^}]+)\}',st)
    if m:
        k=int(m[1]);v=true_vector(k-4);t=m[2].replace('C_k','C_'+str(k));cc=re.fullmatch(r'C_?(\d+)(?:/(\d+))?',t)
        if cc and int(cc[1])==k:v[-1]=Q(v[-1],int(cc[2] or 1));return vector(v,m[0])
        try:v[-1]=simple_number(t);return vector(v,m[0])
        except (SyntaxError,ValueError):pass
    m=re.search(r'sum_\{i=4\}\^\{(\d+)-1\}.*?\+\(([^)]+)\) L\^\(4-(\d+)\)',st)
    if m and m[1]==m[3]:
        k=int(m[1]);v=true_vector(k-4);cc=re.fullmatch(r'C_?(\d+)(?:/(\d+))?',m[2])
        if cc and int(cc[1])==k:v[-1]=Q(v[-1],int(cc[2] or 1));return vector(v,'source Taylor index'+str(k))
        try:v[-1]=simple_number(m[2]);return vector(v,'source Taylor index'+str(k))
        except (SyntaxError,ValueError):pass
    m=re.search(r'\bp=(\([^;]+?\))\s*;\s*z=1/L',st)
    if m:
        try:return vector(ast.literal_eval(m[1]),'explicit source coefficient tuple')
        except (SyntaxError,ValueError):pass
    m=re.search(r'G\(t\)>\(?\[(.*?)\]\)?',st)
    if m:
        try:return vector(ast.literal_eval('['+m[1]+']'),'explicit source coefficient list')
        except (SyntaxError,ValueError):pass
    m=re.search(r'(?:Y\(L\)|Y|g(?:\(L\))?|G(?:\([Lt]\))?|F_R(?:\(L\))?|r)\s*>\s*([PM])_?\{?(\d+)\}?',st)
    if m:
        degree=degree_for(row,m[1],int(m[2]))
        if degree is not None and degree>=0:
            vec=[Q(x) for x in true_vector(degree)]
            tail=st[m.end():].strip()
            has_premium=bool(re.match(r'[+\-]',tail))
            return [{'kind':'R_inverse_log_polynomial','quantity':'G(L)=L^6 R(exp(L))/exp(2L)',
                     'operator':'>','coefficients_by_inverse_log_degree':[rat(x) for x in vec],
                     'highest_inverse_log_degree':degree,'source_label':m[1]+m[2],
                     'label_conversion':'exact per-source definition; full factorial coefficients',
                     'domain':domain(row),'additional_premium_or_expression':tail if has_premium else None,
                     'pure_full_coefficient_vector':not has_premium}]
    m=re.search(r'(?:Y\(L\)|Y|g(?:\(L\))?|G(?:\([Lt]\))?|F_R(?:\(L\))?)\s*>\s*('+NUM+r')(?:[. ]|$)',st)
    if m:
        return [{'kind':'R_inverse_log_polynomial','quantity':'G(L)=L^6 R(exp(L))/exp(2L)','operator':'>',
                 'coefficients_by_inverse_log_degree':[rat(m[1])],'highest_inverse_log_degree':0,
                 'domain':domain(row),'pure_full_coefficient_vector':Q(m[1])==1}]
    return []

def Mtarget(row):
    st=plain(row['raw_M_row']['exact_statement']);ident=row['claim_id'];cid=row['candidate_id']
    m=re.match(r'([wrPQ]) absolute error',st)
    if m:return [{'w':'EW','r':'ES','P':'EP','Q':'EQ'}[m[1]]]
    for pattern,target in [(r'\|D_?1\|','ES'),(r'\|D_?2\|','EW'),(r'\|exp\(-Z\)-1\|','EP'),(r'\|exp\(Z\)-1\|','EQ')]:
        if re.match(pattern,st):return [target]
    if re.match(r'E_?1\s*[<]',st):return ['ES']
    if re.match(r'E_P\s*[<]',st):return ['EP']
    if re.match(r'E_Q\s*[<]',st):return ['EQ']
    if re.match(r'E_w\s*[<]',st):return ['EW']
    if 'weighted' in st.lower() and not any(t in st.lower() for t in ['first','other','all four','four errors','common']):return ['EW']
    if 'first3' in st or 'first three' in st:return ['ES','EP','EQ']
    if any(t in st.lower() for t in ['all power-scaled','all four','all4','common','both coefficients','g_m']):return ['ES','EW','EP','EQ']
    return []

def Mbounds(row):
    st=plain(row['raw_M_row']['exact_statement']);ident=row['claim_id'];bounds=[]
    def add(target,c,alpha=0,logdegree=None):
        if logdegree is None:logdegree=2 if target=='EW' else 3
        bounds.append({'kind':'M_power_log','quantity':target,'coefficient':rat(c),'x_decay_exponent':rat(alpha),
            'log_denominator_degree':logdegree,'operator':row['raw_M_row']['strictness'],
            'formula':'c*x^(-alpha)*(log x)^(-d)','domain':domain(row)})
    alltargets=['ES','EW','EP','EQ']
    m=re.search(r'^\(\|w\|,\|r\|,\|exp\(-z\)-1\|,\|exp\(z\)-1\|\)<=('+NUM+r')\*',st)
    if m:
        if 'exp(-a_iL)' in st:
            ci=re.search(r'Mertens density coefficients ([01])',row['source']['exact_written_readback'])
            if ci:
                for t in alltargets:add(t,m[1],Q(1,8) if ci[1]=='0' else Q(5,32),0 if t=='EW' else 1)
                return bounds
        elif '(L^-2,L^-3,L^-3,L^-3)' in st:
            for t in alltargets:add(t,m[1])
            return bounds
    m=re.search(r'Both coefficients c=d=('+NUM+r') for (?:w at L\^-2 and other three errors at L\^-3|all four scaled errors)',st)
    if m:
        for t in alltargets:add(t,m[1])
        return bounds
    m=re.search(r'\|w\|<=('+NUM+r') exp\(-L/(\d+)\)L\^(-?\d+);.*?<=('+NUM+r') exp\(-L/(\d+)\)L\^(-?\d+)',st)
    if m:
        add('EW',m[1],Q(1,int(m[2])),-int(m[3]))
        for t in ['ES','EP','EQ']:add(t,m[4],Q(1,int(m[5])),-int(m[6]))
        return bounds
    m=re.search(r'\|w\|<=('+NUM+r')/L\^2 and .*?<=('+NUM+r')/L\^3',st)
    if m:
        add('EW',m[1])
        for t in ['ES','EP','EQ']:add(t,m[2])
        return bounds
    m=re.search(r'Polynomial-scaled tuple \(P,Q,E1,Elog\) bounded by \(([^)]+)\)',st)
    if m:
        vals=m[1].split(',')
        if len(vals)==4:
            for t,c in zip(['EP','EQ','ES','EW'],vals):add(t,c)
            return bounds
    m=re.search(r'Block bounds .*?<=\[([^]]+)\]\*10\^(-?\d+)',st)
    if m:
        vals=m[1].split(',')
        if len(vals)==4:
            for t,c in zip(['ES','EP','EQ','EW'],vals):add(t,Q(c.strip())*Q(10)**int(m[2]))
            return bounds
    m=re.search(r'Rate ('+NUM+r'): first three scaled errors <('+NUM+r'); weighted scaled error <('+NUM+r')',st)
    if m:
        for t in ['ES','EP','EQ']:add(t,m[2],m[1],1)
        add('EW',m[3],m[1],0);return bounds
    m=re.search(r'(?:Polynomial-scale|Power-scaled) first three <('+NUM+r')(?:, and power-scaled Elog| and weighted) <('+NUM+r')',st)
    if m:
        a=Q(1,8) if st.startswith('Power-scaled') else Q(0)
        for t in ['ES','EP','EQ']:add(t,m[1],a,1 if a else 3)
        add('EW',m[2],a,0 if a else 2);return bounds
    # The large frontier tables expose exact per-error scalar rows directly.
    m=re.fullmatch(r'([wrPQ]) absolute error<=\(?('+NUM+r')\)?/L\^(\d+)',st)
    if m:add({'w':'EW','r':'ES','P':'EP','Q':'EQ'}[m[1]],m[2],0,int(m[3]));return bounds
    m=re.match(r'(?:\|D_?[12]\||\|exp\(-?Z\)-1\|)\s*<=?\s*\(?('+NUM+r')\)?/L\^(\d+)',st)
    if m:
        for t in Mtarget(row):add(t,m[1],0,int(m[2]))
        return bounds
    m=re.fullmatch(r'E_?(1|P|Q|w)<=('+NUM+r')\*10\^(-?\d+)/L\^(\d+)\.',st)
    if m:add({'1':'ES','P':'EP','Q':'EQ','w':'EW'}[m[1]],Q(m[2])*Q(10)**int(m[3]),0,int(m[4]));return bounds
    m=re.search(r'Column \d+ \(E_(1|P|Q|w)\) times L\^(\d+) <= ('+NUM+r')\*10\^(-?\d+)',st)
    if m:add({'1':'ES','P':'EP','Q':'EQ','w':'EW'}[m[1]],Q(m[3])*Q(10)**int(m[4]),0,int(m[2]));return bounds
    m=re.search(r'G_M<=\(?('+NUM+r')\)? exp\(-\(1-('+NUM+r')\)L\)',st)
    if m:
        for t in ['ES','EW','EP','EQ']:add(t,m[1],1-Q(m[2]),0 if t=='EW' else 1)
        return bounds
    m=re.search(r'All four errors <('+NUM+r') in common scale z=('+NUM+r')',st)
    if m:
        for t in ['ES','EW','EP','EQ']:add(t,m[1],m[2],0 if t=='EW' else 1)
        return bounds
    m=re.search(r'All power-scaled errors strictly less than ('+NUM+r')',st)
    if m:
        for t in ['ES','EW','EP','EQ']:add(t,m[1],Q(1,8),0 if t=='EW' else 1)
        return bounds
    m=re.search(r'All four polynomial-scaled errors strictly below ('+NUM+r')',st)
    if m is None and ident.startswith('D2-M-poly-tail-'):
        m=re.search(r'Common strict coefficient ('+NUM+r') in L\^3',st)
    if m:
        for t in ['ES','EW','EP','EQ']:add(t,m[1])
        return bounds
    # Generic individual exponential leaves (D1/D2 and separately P/Q).
    m=re.search(r'<\s*('+NUM+r')\s*(?:\*\s*)?exp\(-\(?('+NUM+r')\)?L\)(/L)?',st)
    if m and Mtarget(row):
        for t in Mtarget(row):add(t,m[1],m[2],1 if m[3] else 0)
        return bounds
    m=re.search(r'<\s*('+NUM+r')\s*\*?exp\(-L/('+NUM+r')\)(/L)?',st)
    if m and Mtarget(row):
        for t in Mtarget(row):add(t,m[1],1/Q(m[2]),1 if m[3] else 0)
        return bounds
    return bounds

def main():
    data=load(O/'ALL11_SOURCE_BOUND_OBJECTS.json');out=[];counts=collections.Counter()
    for row in data['objects']:
        raw=row['raw_M_row'];st=raw['exact_statement']
        bs=Rbound(row) if row['family']=='Ramanujan' else Mbounds(row)
        shape='EXPLICIT_SCALAR_OR_COEFFICIENT_VECTOR' if bs else 'EXACT_SOURCE_DEFINED_EXPRESSION_OR_RULE'
        record={'key':row['key'],'family':row['family'],'candidate_id':row['candidate_id'],'stage_id':row['stage_id'],
                'claim_id':row['claim_id'],'source':row['source'],'Root_finalization':row['Root_finalization'],
                'normalization_kind':shape,'normalized_bounds':bs,
                'exact_source_expression_or_rule':st,'exact_domain_predicate':raw['full_domain'],
                'declared_premises':raw['assumptions'],'minimal_premises_not_inferred':True,
                'strictness':raw['strictness'],'real_or_integer':raw['real_or_integer'],
                'source_defined_parameter_rule':row['source']['exact_written_readback'] if not bs else None,
                'raw_review_row_key_and_hash':[row['key'],row['raw_M_row_sha256']],
                'baseline_or_input_use_as_disclosed':raw.get('baseline_comparison'),
                'propagation_as_disclosed':raw.get('propagation'),'remaining_trust':raw.get('remaining_trust'),
                'no_weaker_replacement_or_branch_dropping':True,
                'numeric_plot_eligible':bool(bs and all(b['domain']['machine_interval_complete'] for b in bs) and
                    all(b.get('pure_full_coefficient_vector',True) for b in bs))}
        out.append(record);counts[shape]+=1
    need(len(out)==5925 and len({tuple(x['key']) for x in out})==5925,'complete unchanged universe')
    save('NORMALIZED_FRONTIER_DATA_DRAFT.json',{'schema':'FULL11_NORMALIZED_FRONTIER_DATA_DRAFT_V1',
        'status':'SOURCE_COMPLETE_FINITE_NORMALIZATION_AND_SYMBOLIC_RULE_REVIEW_IN_PROGRESS',
        'source_collection':pin(O/'ALL11_SOURCE_BOUND_OBJECTS.json'),'all5925_active_objects_retained':True,
        'coverage':'11 finalized portfolios, not all24. Every active object retained; no strongest-only replacement.',
        'canonical_R':data['canonical_R'],'canonical_M':data['canonical_M'],'objects':out,
        'representation_counts':dict(counts),'all_symbolic_rules_finite_instantiations_and_domains_need_final_normalization_review':True,
        'no_new_mathematical_acceptance_PV_or_Lean':True,'no_causal_exposure_advantage_or_score':True})
    print(dict(counts));print('normalized bounds',sum(len(x['normalized_bounds']) for x in out))

if __name__=='__main__':main()
