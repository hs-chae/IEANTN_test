"""Exact coordinates and lossless source-defined functional objects.

Scalar/vector conversion is deliberately separate from the complete source universe.
An operator/integral/infinite family is retained as that object, never counted as a
missing scalar theorem or replaced by a weaker finite list.
"""
from fractions import Fraction as Q
import ast,collections,functools,hashlib,math,re,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from collect import N,O,load,save,need,pin,sha,read_bytes
import importlib.util
_legacy_spec=importlib.util.spec_from_file_location('_ieantn_original11_normalizer',O/'legacy_coordinate_parser_v1.py')
legacy=importlib.util.module_from_spec(_legacy_spec)
_legacy_spec.loader.exec_module(legacy)
NUM=r'(?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?'
FIRST=['ES','EP','EQ'];ALL=FIRST+['EW']
def plain(s):
    s=legacy.plain(s)
    return s.replace('⁵','^5').replace('⁷','^7').replace('⁸','^8').replace('⁹','^9').replace('¹','^1').replace('⁰','0').replace('δ','delta').replace('cdot','*').replace('\\,','').replace('\\!','').replace('\\','').replace('log x','L').replace('∑','Σ').replace('/(L)','/L').replace('/(log x)','/L')
def rat(x):
    q=Q(str(x));return {'numerator':str(q.numerator),'denominator':str(q.denominator)}
def unrat(x):return Q(int(x['numerator']),int(x['denominator']))
@functools.lru_cache(None)
def _coefficients(d):
    need(0<=d<=1000,'explicit polynomial degree')
    return tuple(sum(math.factorial(i)*math.comb(j,i)-math.factorial(i)*math.factorial(j-i)for i in range(j+1))for j in range(4,d+5))
def coefficients(d):return list(_coefficients(d))
def vec(v,label='explicit written polynomial'):
    return {'kind':'R_inverse_log_polynomial','quantity':'G','operator':'>','coefficients':[rat(x)for x in v],
            'degree':len(v)-1,'source_index_label':label,'canonical_formula':'sum(c[j]*L**(-j),j=0..degree)'}
def exprpoly(s):
    """Finite rational polynomial only; an unparsed suffix is NEVER discarded."""
    s=s.strip().strip('()').replace(' ','').replace('**','^').replace('z','z').replace('t','L')
    s=re.sub(r'/L\^\((\d+)\)',r'/L^\1',s)
    terms=s.replace('-','+-').split('+');v={}
    for t in terms:
        if not t:continue
        m=re.fullmatch('('+NUM+r')(?:\*?)?(?:/L(?:\^(\d+))?|z(?:\^(\d+))?)?',t)
        if not m:raise ValueError('not a complete inverse-log polynomial '+s)
        d=int(m[2] or m[3] or (1 if '/L'in t or 'z'in t else 0));v[d]=v.get(d,Q(0))+Q(m[1])
    need(bool(v),'nonempty polynomial');return [v.get(i,Q(0))for i in range(max(v)+1)]
def degree(row,label,n):
    cid=row['candidate_id'][-3:]
    if label=='M':return n
    if cid in ['001','006','007','010','015','017','018']:return n
    if cid in ['002','008']:return n-4
    if cid in ['005','014','019']:return n-1
    return None
def r_bounds(r):
    s=plain(r['raw_M_row']['exact_statement']);cid=r['candidate_id'][-3:];ident=r['claim_id']
    s=s.replace('L^6 R(e^L)/e^(2L)','G')
    if cid=='023'and ident=='R02-global-scope-correction':
        b=vec([Q('1.03')],'positive finite replacement, separate from the refuted whole ray');b.update(case='B0',explicit_interval_L=[rat('30.714'),rat('477.005')],compound_truth_object='True refutation at L=1000; only this separate finite replacement is a positive lower profile.');return[b]
    if cid=='017'and ident.startswith('R-fixed-'):
        mm=re.search(r'order k=(\d+), m=('+NUM+r')',s)
        if mm:
            v=coefficients(int(mm[1])-4);v[-1]=Q(mm[2]);b=vec(v,'R3 kernel '+mm[1]+'; canonical degree '+str(int(mm[1])-4));b['case']='D02'if ident.endswith('-D02')else'B0';return[b]
    if cid=='016':
        dm=plain(r['raw_M_row']['full_domain'])
        pair=re.search(r'B0 onset ('+NUM+r').*?B1 onset ('+NUM+r')',s)
        if not pair:pair=re.search(r'B0 ('+NUM+r'), B1 ('+NUM+r')',dm)
        if not pair:pair=re.search(r'L>=\s*('+NUM+r') on B0 and >=\s*('+NUM+r') on B1',dm)
        hm=re.search(r'>\s*H_(\d+)',s)
        if hm:v=coefficients(int(hm[1])-4)
        else:
            mm=re.search(r'r\(x\) > (.*?); B0 onset',s)
            if not mm:mm=re.search(r'r\(x\)>(1\+14/L\+100/L\^2)',s)
            try:v=exprpoly(mm[1])if mm else None
            except ValueError:v=None
        if pair and v is not None:
            out=[]
            for case,on in [('B0',pair[1]),('D02',pair[2])]:
                b=vec(v,'source H index '+hm[1]if hm else'complete explicit source polynomial');b.update(case=case,explicit_onset_L=rat(on));out.append(b)
            return out
        if ident=='R-fixed49-refined':
            out=[]
            for case,c in [('B0','15/2'),('D02','799/10')]:
                b=vec([Q(1),Q(14),Q(c)],'full fixed-onset degree2');b.update(case=case,explicit_onset_L=rat('49.1'));out.append(b)
            return out
    if cid in ['020','023']:
        mm=re.search(r'Y > Σ_\{k=4\}\^\{(\d+)\} C_k/L\^\(k[-−]4\) \+ \(([^)]+)\)/L\^\((\d+)\)',s)
        if mm:
            last=int(mm[3]);need(int(mm[1])==last+3,'complete C020 prefix identity');v=coefficients(last);v[-1]=Q(mm[2])
            while len(v)>1 and v[-1]==0:v.pop()
            b=vec(v,'source omitted index '+str(last+4)+'; canonical degree is actual highest nonzero coefficient');b['case']='B0';return[b]
    if cid=='024'and re.match(r'R-new-[QJ]-',ident):
        km=re.search(r'k=(\d+), w=([^;]+);',s);need(km is not None,'whole current C024 row grammar');k=int(km[1]);v=coefficients(k-4);last=km[2]
        if last.startswith('d'):need(last=='d'+str(k),'same exact factorial coefficient index')
        else:v[-1]=Q(last)
        b=vec(v,'source k='+str(k)+'; canonical G degree '+str(k-4));b['case']='B0'if ident.startswith('R-new-Q-')else'D02';return[b]
    # Complete literal margin statements, independent of old heuristic role.
    mm=re.fullmatch(r'(?:Strict )?(?:normalized )?(?:margin |G>)((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)(?:[.;].*)?',s)
    if mm:return [vec([Q(mm[1])],'source explicit scalar margin')]
    if cid=='002' and ident.startswith(('R-matched-threshold-','R-matched-strength-')):
        mm=re.search(r'(?:q=|margin (?:is )?|G>)((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)',s)
        if mm:return [vec([Q(mm[1])],'matched scalar assertion')]
    if cid=='017':
        mm=re.search(r'(?:Strict R3 order |order )(\d+), (?:terminal coefficient |m=)((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)',s)
        if mm:
            v=coefficients(int(mm[1])-4);v[-1]=Q(mm[2]);return [vec(v,'R3 source kernel index '+mm[1])]
    if cid=='022':
        mm=re.search(r'(?:R\(e\^L\)/e\^\(2L\)|G(?:\(L\))?)[ ]*>[ ]*((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)',s)
        if mm:return [vec([Q(mm[1])],'source explicit scalar normalized margin')]
    if cid=='023':
        mm=re.search(r'Y>[ ]*Σ_\(k=4\)\^(\d+) C_k/L\^\(k-4\)',s)
        if mm:return [vec(coefficients(int(mm[1])-4),'C023 source last kernel '+mm[1])]
    if cid=='017':
        mm=re.search(r'sum_\{j=4\}\^\{(\d+)-1\}.*?\+ ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)/L\^\((\d+)-4\)',s)
        if mm:
            need(mm[1]==mm[3],'same source finite endpoint');v=coefficients(int(mm[1])-4);v[-1]=Q(mm[2]);return[vec(v,'R3 source final kernel '+mm[1])]
        mm=re.search(r'sum_\{j=4\}\^(\d+) d_j/L\^\(j-4\)',s)
        if mm:return [vec(coefficients(int(mm[1])-4),'R3 source full kernel '+mm[1])]
    if cid=='022':
        mm=re.search(r'sum_\(j=0\.\.(\d+)\) a_\(4\+j\)/L\^j',s)
        if mm:return [vec(coefficients(int(mm[1])),'source full degree '+mm[1])]
    # Archived false trials/refutations and numerical obstruction are not positive bounds.
    if re.search(r'diagnostic|obstruction|comparison|withdrawn|refutation|source-PT-real',ident,re.I):return []
    if (cid,ident)in [('009','R-closed-joins-dependencies'),('010','R-fallback-extra'),('010','R-fine-fixed'),('010','R-code-16')]:return []
    if cid=='009'and ident.startswith('R-rational-match-'):
        m=re.search(r'D02 a,N,j (\d+) (-|'+NUM+r') \(Fraction\((\d+), (\d+)\), \d+, \d+\) \(Fraction\((\d+), (\d+)\), \d+, \d+\)',s)
        if m:
            v=coefficients(int(m[1])-4)
            if m[2]!='-':v[-1]=Q(m[2])
            out=[]
            for case,a in [('B0',Q(int(m[3]),int(m[4]))),('D02',Q(int(m[5]),int(m[6])))]:
                b=vec(v,'T kernel index '+m[1]);b.update(case=case,explicit_onset_L=rat(a));out.append(b)
            return out
    if cid=='011':
        m=re.search(r'F_([0-9]+)',s)
        if m and ident.startswith(('R-base-F','R-upgrade-F','R-uniform-F','R-free-F','R-base-window-F','R-upgrade-early-F')):
            v=coefficients(int(m[1]));bs=[]
            on=re.search(r'B0 L>=('+NUM+r')[;,] B1 L>=('+NUM+r')',s)
            if not on:on=re.search(r'B0/B1 at ('+NUM+r')/('+NUM+r')',s)
            if on:
                for case,a in [('B0',on[1]),('D02',on[2])]:
                    b=vec(v,'F degree '+m[1]);b.update(case=case,explicit_onset_L=rat(a));bs.append(b)
                return bs
            return [vec(v,'F degree '+m[1])]
    if cid=='012':
        m=re.search(r'R/(?:h|h\(x\))\s*>\s*(.*)',s)
        # Locked C012 row menu declares degree and final coefficient explicitly.
        im=re.match(r'R-(?:main|higher|order2)-([01])-(\d+)-([\d.]+)-(-?[\d.]+)$',ident)
        if im:
            v=coefficients(int(im[2]));v[-1]=Q(im[4]);b=vec(v,'canonical degree '+im[2]);b.update(case='B0'if im[1]=='0'else'D02',explicit_onset_L=rat(im[3]));return[b]
    if cid=='019'and ident.startswith('R.m'):
        rhs=s.split('>',1)[1].rstrip('.')
        try:return[vec(exprpoly(rhs),'source explicitly normalized L^6R/x^2')]
        except (ValueError,IndexError):return[]
    if cid=='010':
        km=re.search(r'(?:order |k=)(\d+)',s)
        if km and not re.search(r'obstruction|diagnostic',ident):
            j=int(km[1]);cs=re.search(r'm=(-?(?:\d+(?:\.\d*)?|\.\d+)) in B0 and m=(-?(?:\d+(?:\.\d*)?|\.\d+)) in B1',s)
            dm=re.search(r'common log onset ('+NUM+r')',s)
            if cs and dm:
                out=[]
                for case,c in [('B0',cs[1]),('D02',cs[2])]:
                    v=coefficients(j);v[-1]=Q(c);b=vec(v,'R1 degree '+str(j));b.update(case=case,explicit_onset_L=rat(dm[1]));out.append(b)
                return out
            mm=re.search(r'm=(-?(?:\d+(?:\.\d*)?|\.\d+))',s)
            onset=re.search(r'(?:log onsets |onsets )('+NUM+r') B0 and ('+NUM+r') B1',s)
            if not onset:onset=re.search(r'(?:onsets |from log )('+NUM+r')/('+NUM+r')',s)
            if mm and onset:
                out=[]
                for case,a in [('B0',onset[1]),('D02',onset[2])]:
                    v=coefficients(j);v[-1]=Q(mm[1]);b=vec(v,'R1 degree '+str(j));b.update(case=case,explicit_onset_L=rat(a));out.append(b)
                return out
    # Exact coefficient tuples and source-printed lists (including zeros).
    m=re.search(r'\bp=(\([^;]+?\)|\[[^;]+?\])\s*[;.]',s)
    if not m:m=re.search(r'PASS\s+[^\[]+(\[[^]]+\])',s)
    if m:
        try:return [vec([Q(str(x))for x in ast.literal_eval(m[1])])]
        except (ValueError,SyntaxError):pass
    m=re.search(r'(?:G\([Lt]\)>\(?|G\([Lt]\) exceeds )(\[[^]]+\])',s)
    if m:return [vec([Q(str(x))for x in ast.literal_eval(m[1])])]
    # The C021 kernel index starts at4; its current table carries the exact last coefficient.
    m=re.search(r'sum_\(j=4\)\^(\d+) d_j/t\^\(j-4\)\+\(([^)]+)\)/t\^(\d+)',s)
    if m:
        d=int(m[3]);need(int(m[1])==d+3,'C021 exact prefix endpoint');v=coefficients(d);v[-1]=Q(m[2]);return [vec(v,'kernel index '+str(d+4))]
    # Taylor T_{k,c}, including c=C_k/2 and the independent192-truncation convention.
    m=re.search(r'(?:G(?:\(L\))?>|G>)(?:T_\{(\d+),([^}]+)\})',s)
    if m:
        k=int(m[1]);v=coefficients(k-4);c=m[2];cm=re.fullmatch(r'C_?(?:\d+|k)(?:/(\d+))?',c)
        v[-1]=Q(v[-1],int(cm[1]or 1))if cm else legacy.simple_number(c)
        paired=re.search(r'B0 real L>=('+NUM+r'); B2 real L>=('+NUM+r')',plain(r['raw_M_row']['full_domain']))
        if paired:
            out=[]
            for case,a in [('B0',paired[1]),('D02',paired[2])]:
                b=vec(v,'T kernel index '+str(k));b.update(case=case,explicit_onset_L=rat(a));out.append(b)
            return out
        return [vec(v,'T kernel index '+str(k))]
    # Legacy exact Taylor sums remain supported by their original strict parser.
    if 'sum_{i=4}'in s:
        mt=re.search(r'sum_\{i=4\}\^\{(\d+)-1\}.*?\+\(([^)]+)\) L\^\(4-(\d+)\)',s)
        if mt and mt[1]==mt[3]:
            k=int(mt[1]);v=coefficients(k-4);cm=re.fullmatch(r'C_?(\d+)(?:/(\d+))?',mt[2])
            if cm:v[-1]=Q(v[-1],int(cm[2]or 1))
            else:v[-1]=legacy.simple_number(mt[2])
            return [vec(v,'exact Taylor index '+str(k))]
    # Paired controlR1 rows have degree=k and replace the final factorial coefficient by m.
    if cid=='010':
        k=re.search(r'(?:order |k=)(\d+)',s);m=re.search(r'\bm=((?:\d+(?:\.\d*)?|\.\d+))',s)
        if k and m and not re.search(r'common log onset',s):
            v=coefficients(int(k[1]));v[-1]=Q(m[1]);b=vec(v,'R1 degree '+k[1]);b['paired_case_domains_source_defined']=True;return [b]
        if k and m:
            ms=re.search(r'm=('+NUM+r') in B0 and m=('+NUM+r') in B1',s)
            if ms:
                out=[]
                for case,c in [('B0',ms[1]),('D02',ms[2])]:
                    v=coefficients(int(k[1]));v[-1]=Q(c);b=vec(v,'R1 degree '+k[1]);b['case']=case;out.append(b)
                return out
    # P/M source labels: source-specific degree, plus premium coefficients without truncation.
    m=re.search(r'(?:Y(?:\(L\))?|g(?:\(L\))?|G(?:\([Lt]\))?|F_R(?:\(L\))?|r)\s*>\s*\(?([PM])_?\{?(\d+)\}?(?:\([^)]*\))?',s)
    if m:
        d=degree(r,m[1],int(m[2]));tail=s[m.end():].lstrip()
        if d is not None and d>=0:
            v=[Q(x)for x in coefficients(d)]
            if tail.startswith('+'):
                pm=re.match(r'\+\(?('+NUM+r')\)?(?:C_?(\d+))?[Lt]\^\{?(-?\d+)\}?',tail)
                if pm:
                    c=Q(pm[1]);c*=coefficients(int(pm[2])-4)[-1]if pm[2]else 1;e=-int(pm[3]);v += [Q(0)]*max(0,e+1-len(v));v[e]+=c
                else:
                    pm=re.match(r'\+('+NUM+r')/[Lt]\^(\d+)',tail)
                    if pm:
                        e=int(pm[2]);v += [Q(0)]*max(0,e+1-len(v));v[e]+=Q(pm[1])
                    else:return [] # symbolic premium retained in full; no weaker numeric substitute
            return [vec(v,m[1]+m[2])]
    # Source first-m and C019 explicit factorial prefix.
    m=re.search(r'times first (\d+)',s)
    if m:return [vec(coefficients(int(m[1])-1),'first '+m[1]+' coefficients')]
    m=re.search(r'Σ_\(j=0\.\.(\d+)\) a_\(4\+j\)',s)
    if m:return [vec(coefficients(int(m[1])),'factorial prefix degree '+m[1])]
    # Complete explicit lower polynomial on G, normalized gap, or source x²/L6 units.
    start=re.search(r'(?:G(?:\([Lt]\))?|g(?:\(L\))?|Y(?:\(L\))?|F_R(?:\(L\))?|R/h|Normalized gap|normalized gap)\s*(?:>|strictly above|exceeds|margin)\s*',s)
    expression=None
    if start:expression=s[start.end():]
    if 'times 'in s and 'x^2/L^6'in s:expression=s.split('times ',1)[1]
    if s.startswith('Strict normalized margin '):expression=s[len('Strict normalized margin '):]
    if expression:
        expression=re.split(r'[,;.]\s+(?!\d)|\.(?:$)|\s+(?:on |from |with |\(equivalently|using |for )',expression,1)[0].strip().strip('()')
        try:return [vec(exprpoly(expression))]
        except (ValueError,SyntaxError):pass
    return []
def is_m_receiver_row(r):
    """Coordinator scalar-plot predicate, NOT an audit-population predicate.

    Shared psi/Lambda/zero providers are never arithmetic output leaves. The
    complete source statements remain in the lossless symbolic universe.
    """
    ident=r['claim_id'];s=plain(r['raw_M_row']['exact_statement'])
    if not ident.startswith(('M-','M.','M1-','M2-','MA-','D2-M-','D02.M.','M02-')):return False
    if re.search(r'(?i)(?:^M-(?:psi|param|src|source-psi|source-theta|mass|zero)|spectrum|polynomial-dominance)',ident):return False
    if 'centered weighted Λ'in s or 'weighted Lambda'in s:return False
    return True

def m_targets(s,ident=''):
    """Explicit arithmetic recipients; bare weighted/Lambda is not a target."""
    s=plain(s);ts=set()
    if any(x in s for x in ['all four','all4','All four','all power-scaled','all polynomial-scaled','Common','common scaled','Both coefficients','both coefficients']):return ALL
    if any(x in s for x in ['first three','first3','other three','products and recips','products and |S|','products and u','P*,Q*','P,Q,S','E123','E_P,E_Q,E_1','E1,E2,E3','P/Q/E1','products and D1','products/D1','both products and D1','first-group','first group','unweighted absolute error','both product errors and reciprocal','both relative product errors and |E1|','Both relative product errors and |E1|']):ts.update(FIRST)
    if any(x in s for x in ['Both relative product errors','both relative product errors','Each product relative error','both absolute relative product errors','both raw relative errors','P/Q','both products','Both products','both relative product','both normalized product','both relative errors','P,Q','relative P|','relative Q|']):ts.update(['EP','EQ'])
    if re.search(r'E_?P|C_P|P relative|absolute P|for P |P absolute|\|exp\(-[zZ]\)-1\|',s):ts.add('EP')
    if re.search(r'E_?Q|C_Q|Q relative|absolute Q|for Q |Q absolute|\|exp\([zZ]\)-1\|',s):ts.add('EQ')
    if re.search(r'E_?(?:w|W|log)|\|[wWj]\||\|D_?2\||W2 error|E_2=|Column 3|δV|deltaV|weighted (?:scaled |absolute |normalized )*error|^weighted\b|^Weighted\b|^w absolute',s):ts.add('EW')
    if re.search(r'E_?(?:1|S)|reciprocal|recips|\|[rSu]\||\|D_?1\||W1 error|deltaS|δS|^r absolute|\bS (?:normalized |absolute )*error|error for W1',s):ts.add('ES')
    if re.search(r'Column [12] normalized error',s):ts.add('ES')
    if 'Column 0 normalized error'in s:ts.update(['EP','EQ'])
    if 'E4'in s:ts.add('EW')
    if 'E_S'in s:ts.add('ES')
    if re.search(r'delta_?V|delta_V|δV|delta_V|D2|delta_W',s):ts.add('EW')
    if re.search(r'delta_?S|δS|D1|E1',s):ts.add('ES')
    if re.search(r'\bP (?:relative|error|normalized)|normalized P error',s):ts.add('EP')
    if re.search(r'\bQ (?:relative|error|normalized)|normalized Q error',s):ts.add('EQ')
    if re.search(r'weighted (?:sum|prime-sum|prime sum|error)|sum log\(p\)/p',s):ts.add('EW')
    if 'First three errors'in s or 'first three errors'in s:ts.update(FIRST)
    if 'two relative product errors'in s or 'Original products'in s or re.search(r'\bproducts\b',s,re.I):ts.update(['EP','EQ'])
    if re.search(r'Absolute u|\|u\|',s):ts.add('ES')
    if re.search(r'Absolute j|\|j\|',s):ts.add('EW')
    return [t for t in ALL if t in ts]
def m_bounds(r):
    s=plain(r['raw_M_row']['exact_statement']);ident=r['claim_id'];cid=r['candidate_id'][-3:];out=[]
    if not is_m_receiver_row(r):return []
    if re.search(r'diagnostic|obstruction|withdrawn|witness|comparison|crossover|necessity|limit|counterexample|dominance',ident,re.I):return []
    def add(t,c,a=0,d=None,kind='M_power_log'):
        if d is None:d=2 if t=='EW'else 3
        out.append({'kind':kind,'quantity':t,'coefficient':rat(c),'x_decay_exponent':rat(a),'log_denominator_degree':d,
                    'operator':r['raw_M_row']['strictness'],'canonical_formula':'c*exp(-alpha*L)/L**d','receiving_target_basis':'source-declared arithmetic Mertens error; shared psi/Lambda providers excluded'})
    def many(ts,c,a=0,d=None):
        for t in ts:add(t,c,a,d)
    # Actual arithmetic receivers only; source Lambda/psi bounds are not these errors.
    if ident in ['M-empty','M-finite-pointwise']:return []
    if cid=='008'and ident=='D2-M-tail-30000-converted':
        for t in ALL:add(t,'.146743',Q(1,8),0 if t=='EW'else 1);out[-1].update(coefficient_log_shift=rat(-Q(30000,32)),canonical_formula='c*exp(coefficient_log_shift-alpha*L)/L**d')
        return out
    if cid=='023'and ident.startswith('M-new-log-'):
        mm=re.search(r'coefficient <=('+NUM+r') in log-power units',s)
        if mm:many(FIRST if'products-D1'in s else['EW'],mm[1]);return out
    if cid=='014'and ident.startswith('M2-finite-ray-example-'):
        mm=re.search(r'L\^3E_i<=('+NUM+r').*?L\^2E_w<=('+NUM+r')',s)
        if mm:
            onset=re.findall(r'from x=('+NUM+r')',s);need(len(onset)==2,'distinct explicit first-three and weighted source onsets')
            for t in FIRST:add(t,mm[1]);out[-1]['explicit_onset_x']=rat(onset[0])
            add('EW',mm[2]);out[-1]['explicit_onset_x']=rat(onset[1]);return out
    if ident=='M-plateau':
        mm=re.search(r'<('+NUM+r')/L;.*?<('+NUM+r')',s)
        if mm:many(FIRST,mm[1],0,1);add('EW',mm[2],0,0);return out
    if cid in ['020','023']and ident.startswith('M-old-sqrt-'):
        mm=re.search(r'products and D1 <=('+NUM+r')/\(sqrt\(x\)L\), D2 <=('+NUM+r')/sqrt\(x\)',s);need(mm is not None,'actual separate source sqrt coefficients')
        many(FIRST,mm[1],Q(1,2),1);add('EW',mm[2],Q(1,2),0);return out
    if cid in ['017','018','022','023']:
        st=re.sub(r'\bu\b','L',s) if cid=='017' else s
        mm=re.search(r'Both products <= ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)/L\^3, reciprocal sum <= ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)/L\^3, weighted sum <= ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)/L\^2',st)
        if mm:
            many(['EP','EQ'],mm[1]);add('ES',mm[2]);add('EW',mm[3]);return out
        mm=re.search(r'Absolute both relative products error\(s\) <= ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)/10\^6/L\^3',st)
        if mm:many(['EP','EQ'],Q(mm[1])/10**6);return out
        mm=re.search(r'(?:E=max|each <=|<=)[^;]*?((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)\s*(?:x\^\((-?(?:1/8|5/32))\)|exp\((-?L/8|-?5L/32)\))',st)
        if mm and (st.startswith('E=max(') or 'maximal unweighted absolute error'in st):
            a=Q(5,32) if '5/32'in (mm[2]or'') or'5L/32'in(mm[3]or'') else Q(1,8)
            for t in ALL:add(t,mm[1],a,0 if t=='EW'else 1)
            return out
        mm=re.search(r'(?:Both relative product errors and \|E1\||Each product relative error and \|E1\|) <= ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)(.*)',st)
        if mm:
            tail=mm[2];a=Q(1,8)if'x^(-1/8)'in tail else Q(5,32)if'x^(-5/32)'in tail else Q(0)
            dm=re.match(r'/L\^(\d+)',tail);power=1 if a else int(dm[1])if dm else 0
            many(FIRST,mm[1],a,power)
            wm=re.search(r'\|Ew\| <= ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)(.*)',tail)
            if wm:
                d2=re.match(r'/L\^(\d+)',wm[2]);add('EW',wm[1],a,int(d2[1])if d2 else 0)
            return out
        mm=re.search(r'^([PQ])(?: relative absolute| relative)? error < ?((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)(?:[ ]*(x\^\((-?(?:1/8|5/32))\)))?(?:/[uL](?:\^(\d+))?)?',st)
        if mm:
            a=-Q(mm[4])if mm[4]else Q(0);den=int(mm[5])if mm[5]else(1 if '/L'in mm[0]or'/u'in mm[0]else 0)
            add('EP'if mm[1]=='P'else'EQ',mm[2],a,den);return out
        mm=re.search(r'Errors of P,Q,sum 1/p <((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)/L\^3 and weighted sum <((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)/L\^2',st)
        if mm:many(FIRST,mm[1]);add('EW',mm[2]);return out
    if cid in ['003','009']and ident in ['M-root-D1','M-root-D2','M-root-P','M-root-Q']:
        t={'D1':'ES','D2':'EW','P':'EP','Q':'EQ'}[ident.rsplit('-',1)[1]];add(t,'.3'if t=='EW'else'.2');return out
    if cid=='023':
        mm=re.search(r'all[- ]four(?: strict)? coefficient ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)|all four coefficient ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)',s)
        if mm:many(ALL,mm[1]or mm[2]);return out
        mm=re.search(r'all four errors <=([^ ]+) in power units',s)
        if mm:
            for t in ALL:add(t,mm[1],Q(1,8),0 if t=='EW'else 1)
            return out
        if ident.startswith('M-old-sqrt-'):
            for t in ALL:add(t,'2.4',Q(1,2),0 if t=='EW'else 1)
            return out
    if cid=='018'and ident.startswith('M-connected-'):
        mm=re.search(r'<= ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?) exp\(-([0-9]*)L/([0-9]+)\)',s)
        if mm:
            for t in ALL:add(t,mm[1],Q(int(mm[2]or 1),int(mm[3])),0 if t=='EW'else 1)
            return out
    if cid in ['017','018','022','023']:
        # Parse each receiving-error clause separately. A later weighted clause must
        # never inherit the first-three log denominator (nor the other way around).
        st=re.sub(r'\bu\b','L',s) if cid=='017' else s
        st=st.replace('sum 1/p','reciprocal sum').replace('scaled all-output error','G_M')
        if cid=='022'and ident.startswith('D02.M.level'):
            mm=re.search(r'< ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)/10\^6 x\^\(-1/8\)',st)
            if mm:
                ts=['EP','EQ']if '.P,Q'in ident else ['ES']if ident.endswith('.S')else['EW']
                for t in ts:add(t,Q(mm[1])/10**6,Q(1,8),0 if t=='EW'else 1)
                return out
        if st.startswith('E=max('):
            mm=re.search(r'(?:<|<=)((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)\s*x\^\(-((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)\)',st)
            if mm:
                for t in ALL:add(t,mm[1],Q(mm[2]),0 if t=='EW'else 1)
                return out
        if 'Each G_M' in st or st.startswith('G_M') or st.startswith('Each scaled all-output'):
            mm=re.search(r'(?:<=|<)\s*((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)\s*exp\(-L/8\)',st)
            if mm:
                for t in ALL:add(t,mm[1],Q(1,8),0 if t=='EW'else 1)
                return out
        clauses=re.split(r';|,\s*(?=\|(?:D_?2|Ew|[wWj])\||(?:weighted|reciprocal) (?:sum|error)|E_?w)| and (?=weighted |\|Ew\|)',st)
        generics=[]
        for clause in clauses:
            mm=re.search(r'(?:<=|<)\s*((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)(?:[ ]*x\^\(-((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)\))?(?:[ ]*exp\(-([0-9]*L/[0-9]+)\))?(?:/[L](?:\^(\d+))?)?',clause)
            if not mm:continue
            prefix=clause[:mm.start()]
            if re.search(r'L\^\d+',prefix):continue
            ts=m_targets(prefix,ident)
            if not ts:continue
            rhs=clause[mm.end():]
            # Avoid parsing only a numeric prefix of an unparsed nonconstant RHS.
            if re.match(r'[A-Za-z_*^/(]',rhs.lstrip()) and not re.match(r'(?:on|from|for|at|in|using|with|inclusive|strict)(?:\b|[ .,])',rhs.lstrip()):continue
            a=Q(mm[2])if mm[2]else (Q((mm[3].split('L/')[0] or '1'))/Q(mm[3].split('L/')[1])if mm[3]else Q(0))
            d=int(mm[4])if mm[4]else(1 if re.search(r'/L(?:$|[ ,.;])',mm[0])else 0)
            for t in ts:generics.append((t,mm[1],a,d))
        if generics:
            for t,c,a,d in generics:add(t,c,a,d)
            return out
    if cid=='017'and ident.startswith('M-zoom-'):
        i=int(ident.rsplit('-',1)[1]);t=['EP','EQ','ES','EW'][i];add(t,'.3'if t=='EW'else'.2');out[-1]['source_parameter_import']={'own_source_object':['FOLLOWUP-C017','M-original-'+str(i)],'meaning':'the explicitly named original receiver coefficient, at its own newly certified crossing'};return out
    if cid=='017'and ident=='M-refined-early-bridge':
        for c,on in [('.235','166.4'),('.234','184')]:
            for t in ALL:add(t,c,Q(5,32),0 if t=='EW'else 1);out[-1].update(case='D02',explicit_onset_L=rat(on))
        return out
    if cid=='018'and ident.startswith('M-witness-'):
        mm=re.match(r'M-witness-([0-3])-(\d+)',ident);need(mm is not None,'complete source witness/finite-success key')
        t=['ES','EQ','EW','EP'][int(mm[1])];on='912581'if t=='EW'else'2278421'
        add(t,Q(int(mm[2]),1000));out[-1].update(explicit_interval_x=[rat(on),rat(20000000)],branch_strictness='non-strict <= on the finite certificate segment',compound_truth_object='Separate failed witness at earlier point and this accepted finite success segment.');return out
    if cid=='022'and ident.startswith('M.Python-row.'):
        mm=re.search(r'<= ('+NUM+r')/10\^6/L\^(2|3)',s)
        if mm:
            ts=['EP','EQ']if'both relative products'in s else['ES']if'reciprocal'in s else['EW'];many(ts,Q(mm[1])/10**6,0,int(mm[2]));return out
    if cid=='016':
        mm=re.search(r'first-group errors <= ('+NUM+r') x\^\([-−](1/8|5/32)\)/L and weighted error <=',s)
        if not mm:mm=re.search(r'both product errors and reciprocal prime-sum error <= ('+NUM+r')(?:\.|$)',s)
        if mm:
            if len(mm.groups())==2:
                for t in ALL:add(t,mm[1],Q(mm[2]),0 if t=='EW' else 1)
            else:many(FIRST,mm[1],0,0)
            for b in out:b['case']='D02'if'On B1'in s else'B0'
            return out
        mm=re.search(r'weighted prime-sum error <= ('+NUM+r')(?:\.|$)',s)
        if mm:add('EW',mm[1],0,0);out[-1]['case']='D02'if'On B1'in s else'B0';return out
        mm=re.search(r'(?:Both normalized relative product errors|Absolute reciprocal prime-sum error|Absolute weighted prime-sum error|\|reciprocal prime-sum error\|) <= \(?('+NUM+r')\)?/L\^(2|3)',s)
        if mm:
            ts=['EP','EQ']if'product'in s else['EW']if'weighted'in s else['ES'];many(ts,mm[1],0,int(mm[2]));return out
    if cid in ['020','023']and ident.startswith('M-new-log-'):
        mm=re.search(r'coefficient (?:<=|≤)('+NUM+r') in log-power units',s)
        if mm:
            ts=FIRST if'products-D1'in s else['EW'];many(ts,mm[1]);return out
    if cid=='024':
        if re.match(r'M-new-power-[QJ]-',ident):
            p=ident.split('-',5);a=Q(1,8)if p[3]=='Q'else Q(5,32)
            for t in ALL:add(t,p[5],a,0 if t=='EW' else 1)
            for b in out:b['case']='B0'if p[3]=='Q'else'D02'
            return out
        if re.match(r'M-new-log-[QJ]-',ident):
            p=ident.split('-',5);many(ALL,p[5]);
            for b in out:b['case']='B0'if p[3]=='Q'else'D02'
            return out
        if ident=='M-new-power-119':
            for t in FIRST:add(t,'.25665',Q(5,32),1)
            for b in out:b['case']='D02'
            return out
        if re.match(r'M-new-shapes-(98|117|200)$',ident):
            c={'98':'.012400','117':'.006665','200':'.000421'}[ident.rsplit('-',1)[1]]
            for t in ALL:add(t,c,Q(1,8),0 if t=='EW' else 1)
            for b in out:b['case']='D02'
            return out
    if cid=='011'and ident.startswith('M-new-early-'):
        m=re.search(r'10\^\(-([0-9]+)\)',s)
        if m:many(ALL,Q(1,10**int(m[1])));return out
    m=re.fullmatch(r'\|w\|<=('+NUM+r') exp\(-L/(\d+)\)L\^(-?\d+);.*?<=('+NUM+r') exp\(-L/(\d+)\)L\^(-?\d+)',s)
    if m:
        add('EW',m[1],Q(1,int(m[2])),-int(m[3]))
        for t in FIRST:add(t,m[4],Q(1,int(m[5])),-int(m[6]))
        return out
    if cid=='011'and ident in ['M-free-B0','M-free-B1']:
        m=re.search(r'\|W\|<('+NUM+r') L\^2exp\(-('+NUM+r')L\);.*?<('+NUM+r') L exp\(-('+NUM+r')L\)',s)
        need(m is not None,'complete density-free source log-loss function')
        add('EW',m[1],m[2],-2)
        for t in FIRST:add(t,m[3],m[4],-1)
        return out
    # Explicit sqrt-x finite strips, retaining the original finite interval.
    m=re.search(r'^\|w\|<=('+NUM+r')/√x,',s)
    if m:
        for t in ALL:add(t,m[1],Q(1,2),0 if t=='EW'else 1)
        return out
    m=re.search(r'(?:All four polynomial-scaled errors (?:are )?strictly (?:below|less than)|All power-scaled errors strictly (?:below|less than)) ('+NUM+r')',s)
    if m:
        if 'power-scaled'in s:
            for t in ALL:add(t,m[1],Q(1,8),0 if t=='EW'else 1)
        else:many(ALL,m[1])
        return out
    m=re.search(r'^('+NUM+r') for the power-scaled (first3|weighted)',s)
    if m:
        for t in FIRST if m[2]=='first3'else['EW']:add(t,m[1],Q(1,8),0 if t=='EW'else 1)
        return out
    m=re.search(r'(?:Polynomial-scaled|strict|Strict) (P/Q/E1|P/Q|Elog|Both products|First three|Weighted).*?(?:below |coefficient )('+NUM+r')',s)
    if m:
        many({'P/Q/E1':FIRST,'P/Q':['EP','EQ'],'Elog':['EW'],'Both products':['EP','EQ'],'First three':FIRST,'Weighted':['EW']}[m[1]],m[2]);return out
    # Original four Dusart leaves: these values are exact in each named original
    # and still use each row's own x-domain, not a shared arbitrary onset.
    if ident in ['M-source-products','M-Dusart-5.9']:many(['EP','EQ'],Q(1,5));return out
    if ident in ['M-Dusart-5.6']:many(['ES'],Q(1,5));return out
    if cid in ['019','022']and ident.startswith('M.onsetExample'):
        m=re.match('('+NUM+r') coefficient',s)
        if m:many(ALL if 'all four'in s else(['EW']if 'for V'in s else FIRST),m[1]);return out
    if cid=='011':
        m=re.search(r'B0 \(d,C\)=\(1/8,('+NUM+r')\), B1 \(5/32,('+NUM+r')\)',s)
        if m:
            for case,c,a in [('B0',m[1],Q(1,8)),('D02',m[2],Q(5,32))]:
                on=re.search(r'For real L>=('+NUM+r')',s)
                for t in ALL:
                    add(t,c,a,0 if t=='EW'else 1);out[-1]['case']=case
                    if on:out[-1]['explicit_onset_L']=rat(on[1])
            return out
        im=re.match(r'M-(uniform|base|upgrade|free)-log-(\d+)$',ident)
        if im:
            am=re.search(r'B0 L>=('+NUM+r'), B1 L>=('+NUM+r')',s)
            if am:
                for case,a in [('B0',am[1]),('D02',am[2])]:
                    for t in ALL:add(t,Q(1,10**int(im[2])));out[-1].update(case=case,explicit_onset_L=rat(a))
                return out
    # These paired portfolios use a common power law for all four outputs.
    # Handle the complete group before a generic clause parser can lose E4.
    if cid in ['006','015'] and ('M-old-power-'in ident or 'M-power-'in ident):
        m=re.search(r'(?:<|below )\s*('+NUM+r')\s*(?:e\^\(-L/8\)|x\^\(-5/32\))',s)
        if m:
            a=Q(5,32)if '5/32'in s else Q(1,8)
            for t in ALL:add(t,m[1],a,0 if t=='EW'else 1)
            return out
    if cid=='012':
        m=re.search(r'(?<!\w)([0-9.]+)\s*(?:x\^|exp\()',s)
        im=re.match(r'M-power-(?:old|enhanced|early-old|early-new|continuous)-([01])-([\d.]+)-([\d.]+)$',ident)
        if im:
            a=Q(1,8)if im[1]=='0'else Q(5,32)
            for t in ALL:
                add(t,im[3],a,0 if t=='EW'else 1);out[-1].update(case='B0'if im[1]=='0'else'D02',explicit_onset_L=rat(im[2]))
            return out
    # A max of the four polynomial-scaled absolute errors means four caps.
    m=re.search(r'max\(L\^3E_1,L\^3E_P,L\^3E_Q,L\^2E_w\)<=('+NUM+r')',s)
    if m:many(ALL,m[1]);return out
    # Exact large C019 tapes; diagnostic last-failed rows do not become rays.
    m=re.search(r'Scaled ceilings \[([^]]+)\] in units 10\^-9',s)
    if m:
        vals=ast.literal_eval('['+m[1]+']')
        for ts,c in zip([['EP','EQ'],['ES'],['EW']],vals):many(ts,Q(c,10**9))
        return out
    m=re.search(r'^(P,Q|S|V): last failed cell end .*?threshold ('+NUM+r')',s)
    if m and 'yields an inclusive full-ray bound'in s:many({'P,Q':['EP','EQ'],'S':['ES'],'V':['EW']}[m[1]],m[2]);return out
    m=re.search(r'Column (\d+) normalized error <=('+NUM+r')/10\^6',s)
    if m:many([['EP','EQ'],['ES'],['EW']][int(m[1])],Q(m[2])/10**6);return out
    # C007 coefficients declare their edge a_i in the exact scientific tape LF.
    m=re.search(r'^\(\|w\|,\|r\|,\|exp\(-z\)-1\|,\|exp\(z\)-1\|\)<=('+NUM+r')\*',s)
    if m:
        if 'exp(-a_iL)'in s:
            edge=re.search(r'Mertens density coefficients ([01])',r['source']['exact_written_readback'])
            if edge:
                a=Q(1,8)if edge[1]=='0'else Q(5,32)
                for t in ALL:add(t,m[1],a,(-2 if t=='EW'else -1)if '(L^2,L,L,L)'in s else (0 if t=='EW'else 1))
                return out
        elif '(L^-2,L^-3,L^-3,L^-3)'in s:many(ALL,m[1]);return out
    # Explicit common scaled caps.
    m=re.search(r'(?:Common strict cap coefficient|Common cap coefficient)\s*\(?([^;]+?)\)? in [tL]\^\(-2\)',s)
    if m:
        c=m[1].replace('{','').replace('}','').replace('10^','10**')
        try:many(ALL,legacy.simple_number(c));return out
        except (ValueError,SyntaxError):pass
    m=re.search(r'(?:Common strict coefficient|Strict common coefficient) ('+NUM+r') in (?:e\^\(|exp\()(-?[^)]*)\)',s)
    if m:
        ex=m[2].replace('t','L');a=Q(5,32)if '5'in ex and '32'in ex else Q(1,8)
        for t in ALL:add(t,m[1],a,0 if t=='EW'else 1)
        return out
    m=re.search(r'G_M<=\(?('+NUM+r')\)?(?: exp\(-(?:\(1-('+NUM+r')\)|('+NUM+r'))L\))?',s)
    if m:
        a=1-Q(m[2])if m[2]else(Q(m[3])if m[3]else 0)
        for t in ALL:add(t,m[1],a,0 if t=='EW'else 1)
        return out
    # C010 paired source laws, degree-specific source decay exponents.
    m=re.search(r'(?:constants |C=)('+NUM+r')/('+NUM+r')',s)
    if cid=='010' and m and any(k in ident for k in ['M1-','MA-','M-light','M-split']):
        for case,c,a in [('B0',m[1],Q(1,8)),('D02',m[2],Q(5,32))]:
            for t in ALL:
                d=(-2 if t=='EW'else -1)if 'multiply L'in s else (0 if t=='EW'else 1)
                add(t,c,a,d);out[-1]['case']=case
        return out
    # Componentwise finite vectors, canonical order supplied explicitly in the statement.
    m=re.search(r'Whole-ray normalized error caps in stated order: (\[[^]]+\])',s)
    if m:
        for t,c in zip(['ES','EP','EQ','EW'],ast.literal_eval(m[1])):
            if c is not None:add(t,str(c))
        return out
    m=re.search(r'\(L\^3E_1,L\^3E_P,L\^3E_Q,L\^2E_w\)<=10\^-4 times (\[[^]]+\])',s)
    if m:
        for t,c in zip(['ES','EP','EQ','EW'],ast.literal_eval(m[1])):add(t,Q(c)/10000)
        return out
    m=re.search(r'Coefficients /10000 S:(\d+) W:(\d+) EP:(\d+) EQ:(\d+)',s)
    if m:
        for t,c in zip(['ES','EW','EP','EQ'],m.groups()):add(t,Q(c)/10000)
        return out
    # Signed-log finite bins: preserve exp(z)-1, never replace relative products by z.
    m=re.search(r'[Lt]\^3\|S\|\s*<=\s*('+NUM+r').*?[Lt]\^2\|W\|\s*<=\s*('+NUM+r').*?[Lt]\^3\|Z\|\s*<=\s*('+NUM+r')',s)
    if m:
        add('ES',m[1]);add('EW',m[2])
        for t in ['EP','EQ']:add(t,m[3],0,3,'M_exp_log_enclosure')
        return out
    # General direct inverse-log endpoints, including separate target clauses.
    clauses=re.split(r';| and for |;? weighted (?:<=|<)|;? \|W\|',s)
    matched=False
    for clause in clauses:
        m=re.search(r'(?:<=|<|below |strictly by |bounded by |bounded strictly by |coefficient )\s*\(?('+NUM+r')\)?\s*(?:\*10\^\(?(-?\d+)\)?)?\s*/[Lt]\^(\d+)',clause)
        if m:
            ts=m_targets(clause,ident)
            if not ts:continue
            c=Q(m[1])*Q(10)**int(m[2]or 0)
            for t in ts:add(t,c,0,int(m[3]))
            matched=True
    if matched:return out
    # Exponential endpoints with complete alpha (5L/32 must not be read as L/32).
    clauses=re.split(r';| and for ',s)
    for clause in clauses:
        m=re.search(r'(?:<=|<|below |strictly by |bounded by |bounded strictly by )\s*('+NUM+r')\s*\*?\s*(?:exp\(-\(?([^)]*?)\)?\)|[ex]\^\(?(-[^)]*)\)?)',clause)
        if not m:continue
        ts=m_targets(clause,ident)
        if not ts:continue
        exponent=(m[2]or m[3].lstrip('-')).replace(' ','').replace('t','L').replace('x','L')
        exponent=exponent.replace('(1/8)','1/8')
        am=re.fullmatch(r'(?:('+NUM+r')\*?)?L/('+NUM+r')',exponent)
        if am:a=Q(am[1]or 1)/Q(am[2])
        else:
            am=re.fullmatch(r'('+NUM+r')\*?L',exponent)
            if not am:continue
            a=Q(am[1])
        tail=clause[m.end():];dm=re.match(r'/[Lt](?:\^(-?\d+))?',tail);pm=re.match(r'[Lt]\^(-?\d+)',tail)
        d=int(dm[1]or 1)if dm else(-int(pm[1])if pm else 0)
        for t in ts:add(t,m[1],a,d)
    if out:return out
    # Grouped current C006/C015 power laws and common C019/C021 bounds.
    if cid in ['006','015'] and ('M-old-power-'in ident or 'M-power-'in ident):
        m=re.search(r'(?:<|below )\s*('+NUM+r')\s*(?:e\^\(-L/8\)|x\^\(-5/32\))',s)
        if m:
            a=Q(5,32)if '5/32'in s else Q(1,8)
            for t in ALL:add(t,m[1],a,0 if t=='EW'else 1)
            return out
    if cid in ['019','022']:
        m=re.search(r'Power envelope coefficient ('+NUM+r')',s)
        if m:
            for t in ALL:add(t,m[1],Q(1,8),0 if t=='EW'else 1)
            return out
        m=re.search(r'(?:P,Q|S|V) coefficient ('+NUM+r')',s)
        if m:many(['EP','EQ']if s.startswith('P,Q')else(['ES']if s.startswith('S ')else['EW']),m[1]);return out
    if cid in ['021','023']:
        m=re.search(r'Absolute (both relative products|q log|u|j) scaled by t\^(\d+) is <('+NUM+r')',s)
        if m:
            ts={'both relative products':['EP','EQ'],'q log':['LQ'],'u':['ES'],'j':['EW']}[m[1]];many(ts,m[3],0,int(m[2]));return out
        m=re.search(r'(?:below |below\.)(?:strictly )?('+NUM+r')',s)
        if m and ident.startswith(('M-power-','M-sensitivity-')):
            for t in ALL:add(t,m[1],Q(5,32)if '5/32'in s else Q(1,8),0 if t=='EW'else 1)
            return out
        m=re.search(r'(?:below|is <)\s*('+NUM+r')/[tL]\^(\d+)',s)
        if m:
            ts=['EP','EQ']if 'both relative products'in s else (['ES']if 'Absolute u'in s else(['EW']if 'Absolute j'in s else m_targets(s)))
            many(ts,m[1],0,int(m[2]));return out
        m=re.search(r'Absolute (P,Q|u|j) error.*?below ('+NUM+r')/[tL]\^(\d+)',s)
        if m:many({'P,Q':['EP','EQ'],'u':['ES'],'j':['EW']}[m[1]],m[2],0,int(m[3]));return out
    if cid=='022' and ident.startswith('M.matched'):
        mm=re.search(r'coefficient ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)',s)
        if mm:many(['EP','EQ']if'P,Q'in s else['ES']if'S coefficient'in s else['EW'],mm[1]);return out
    # Previously checked simple rows; retain all components exactly as represented.
    b=legacy.Mbounds(r)
    for x in b:
        x={**x};x['coefficient']=x['coefficient'];x.pop('domain',None);out.append(x)
    if cid in ['019','022']and ident in ['M.old-sharper','M.old-analytic','M.old-refined','M.finite26-examples','M.finite24-examples']:
        def source_cap(ts,c,on,var='x',a=0,power=False):
            for t in ts:
                add(t,c,a,(0 if t=='EW'else 1)if power else(2 if t=='EW'else 3))
                out[-1]['explicit_onset_'+var]=rat(on);out[-1]['source_clause_label']=ident+' exact source-declared coefficient/receiver/onset clause'
        if ident=='M.old-sharper':
            source_cap(['EP','EQ'],'.199999',2278382);source_cap(['ES'],'.199999',2278383);source_cap(['EW'],'.2999995',912560)
        elif ident=='M.old-analytic':source_cap(FIRST,'.125',10**8);source_cap(['EW'],'.135',10**8)
        elif ident=='M.old-refined':
            source_cap(ALL,'.044',26,'L');source_cap(['EP','EQ'],'.0211','189.5','L',Q(1,8),True);source_cap(['ES'],'.02101','189.5','L',Q(1,8),True)
        elif ident=='M.finite26-examples':
            source_cap(['EP','EQ'],'.199972897',2278382);source_cap(['ES'],'.199928568',2278383);source_cap(['EW'],'.299999705',912560)
            source_cap(ALL,'.1',30000000);source_cap(ALL,'.044',500000000);source_cap(FIRST,'.453',300000);source_cap(['EW'],'.488',300000);source_cap(FIRST,'.19',3451809)
        else:
            source_cap(ALL,'.088',24,'L');source_cap(['EP','EQ'],'.199980',2278382);source_cap(['ES'],'.199929',2278383)
            source_cap(FIRST,'.145',6000000);source_cap(['EW'],'.155',6000000);source_cap(FIRST,'.453',300000);source_cap(['EW'],'.488',300000)
        return out
    if cid=='010'and ident=='M-fallback':
        for case,a in [('B0',Q(1,8)),('D02',Q(5,32))]:
            for t in ALL:add(t,'.0626',a,-2 if t=='EW'else -1);out[-1].update(case=case,explicit_onset_L=rat(300))
        return out
    if cid=='010'and ident=='M-.002':
        for t in ALL:add(t,'.002',Q(1,8),0 if t=='EW'else 1);out[-1].update(case='D02',explicit_onset_L=rat(170))
        return out
    if cid=='018'and ident=='M-targets':
        for c,old,new in [('1e-14',224,198),('1e-18',296,255)]:
            for case,on in [('B0',old),('D02',new)]:
                for t in ALL:add(t,c,0,0 if t=='EW'else 1);out[-1].update(case=case,explicit_onset_L=rat(on),source_explicit_weaker_B0_case=True)
        return out
    if out:return out
    if ident.startswith('M-matched-inverse-'):
        mm=re.search(r'Common scaled strength ('+NUM+r')',s)
        if mm:
            pair=re.search(r'B0 L>=('+NUM+r'), D02 L>=('+NUM+r')',plain(r['raw_M_row']['full_domain']));need(pair is not None,'complete paired source inverse-log onsets')
            for case,on in [('B0',pair[1]),('D02',pair[2])]:
                for t in ALL:add(t,mm[1]);out[-1].update(case=case,explicit_onset_L=rat(on),source_explicit_weaker_B0_case=True)
            return out
    if cid=='016'and ident=='M-bridge-strong':many(ALL,'.0223');return out
    if cid=='017'and ident=='M-extension-join':
        many(FIRST,'.077911');add('EW','.081342');return out
    if cid=='024'and re.search(r'Absolute q log scaled by t\^3 is <('+NUM+r')',s):
        mm=re.search(r'is <('+NUM+r')',s);add('LQ',mm[1],0,3);return out
    if cid=='008'and ident.startswith('D2-M-fixed-'):
        if 'First three strict coefficient .2'in s:many(FIRST,'.2');return out
        if 'Both products .199879 and reciprocal sum .199917'in s:many(['EP','EQ'],'.199879');add('ES','.199917');return out
        if 'Weighted strict coefficient .3'in s:add('EW','.3');return out
    if cid=='008'and ident=='D2-M-free-square':
        for t in ALL:add(t,'.01421',Q(5,32),-2 if t=='EW'else -1)
        return out
    if cid=='008'and ident=='D2-M-raw':
        for t in ALL:add(t,'.123'if t=='EW'else'.120',Q(5,32),-2 if t=='EW'else -1)
        return out
    mm=re.search(r'Polynomial-scaled (all4|first3|weighted)(?: bound)? <('+NUM+r')',s)
    if mm:many(ALL if mm[1]=='all4'else FIRST if mm[1]=='first3'else['EW'],mm[2]);return out
    st=re.sub(r'\bt\b','L',s)
    if cid=='017':st=re.sub(r'\bu\b','L',st)
    mm=re.search(r'Scaled ceilings \[([^]]+)\] in units 10\^-([0-9]+)',st)
    if mm:
        vals=ast.literal_eval('['+mm[1]+']');need(len(vals)==3,'all three finite source columns')
        for ts,c in zip([['EP','EQ'],['ES'],['EW']],vals):many(ts,Q(c)/10**int(mm[2]))
        return out
    if cid in ['020','023']:
        if ident.startswith('M-old-sqrt-'):
            for t in ALL:add(t,'2.4',Q(1,2),0 if t=='EW'else 1)
            return out
        mm=re.search(r'all[- ]four(?: strict)? coefficient ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)|all four coefficient ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)',st)
        if mm:many(ALL,mm[1]or mm[2]);return out
        mm=re.search(r'all four errors <=([^ ]+) in power units',st)
        if mm:
            for t in ALL:add(t,mm[1],Q(1,8),0 if t=='EW'else 1)
            return out
    mm=re.search(r'(?:Common scaled cap|Scaled log/product and sum caps) < ?((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)',st)
    if mm:many(ALL,mm[1]);return out
    mm=re.search(r'Both products strict coefficient ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?) in polynomial scales',st)
    if mm:many(['EP','EQ'],mm[1]);return out
    mm=re.search(r'Finite-to-ray log coefficient c=((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?), product onset ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?), recips ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?), weighted ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)',st)
    if mm:
        for t,on in [('EP',mm[2]),('EQ',mm[2]),('ES',mm[3]),('EW',mm[4])]:add(t,mm[1]);out[-1]['explicit_onset_x']=rat(on)
        return out
    mm=re.search(r'below ((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?) x\^\(-((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)\) /L for products and u, without /L for j',st)
    if mm:
        for t in ALL:add(t,mm[1],Q(mm[2]),0 if t=='EW'else 1)
        return out
    clauses=re.split(r';|,\s*(?=\|(?:D_?2|Ew|[wWj])\||(?:weighted|reciprocal) (?:sum|error)|E_?w)| and (?=weighted |\|Ew\|)',st)
    for clause in clauses:
        mm=re.search(r'(?:<=|<|below )\s*((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)(?:[ ]*x\^\(-((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)\))?(?:[ ]*exp\(-([0-9]*L/[0-9]+)\))?(?:/[L](?:\^(\d+))?)?',clause)
        if not mm:continue
        prefix=clause[:mm.start()]
        if re.search(r'\b[xLtv]\s*$',prefix):continue
        if re.search(r'L\^\d+',prefix)and not re.search(r'scaled by L\^\d+',prefix):continue
        ts=m_targets(prefix,ident)
        if not ts:continue
        rhs=clause[mm.end():]
        if re.match(r'[A-Za-z_*^/(]',rhs.lstrip())and not re.match(r'(?:on|from|for|at|in|using|with|inclusive|strict)(?:\b|[ .,])',rhs.lstrip()):continue
        a=Q(mm[2])if mm[2]else(Q(mm[3].split('L/')[0]or'1')/Q(mm[3].split('L/')[1])if mm[3]else Q(0))
        dm=re.search(r'scaled by L\^(\d+)',prefix)
        d=int(mm[4])if mm[4]else(1 if re.search(r'/L(?:$|[ ,.;])',mm[0])else int(dm[1])if dm else 0)
        # A normalized log-product radius is not a relative error without its
        # explicit exponential conversion. Leave such source operators exact.
        if 'log/product'in prefix and 'relative conversion included'not in st:continue
        for t in ts:add(t,mm[1],a,d)
    return out
def domain(r):
    original=r['raw_M_row']['full_domain'];effective=original;qualified=False
    if r['key']==['FOLLOWUP-C020','R-stronger-constant-3']:
        q=r.get('Root_object_qualification')or{}
        need(original=='L≥30.75'and q.get('original_raw_domain_is_false_as_a_whole_ray')is True,'preserve the original false unqualified ray')
        need(q.get('full_domain')=='30.75≤L≤191'and q.get('current_assessment')=='supported_at_corrected_finite_scope_only','exact Root-qualified originally certified finite scope')
        effective=q['full_domain'];qualified=True
    s=plain(effective).strip();s=re.sub(r'log\(10\^(\d+)\)',lambda m:'log('+str(10**int(m[1]))+')',s);d={'exact_predicate':effective,'integer_or_real':r['raw_M_row']['real_or_integer'],
        'canonical_variable':'L=log(x)','symbolic_eligibility_preserved':True,'numeric_intervals':[]}
    if qualified:d.update(original_raw_predicate=original,original_raw_unqualified_ray_is_false=True,effective_Root_qualified_scope=r['Root_floor'],scope_note='Only the original certified finite closed interval is admitted. Raw M review body/domain are preserved; no later C023 interval imported.')
    # Exact root boundary and a SEPARATE conservative plotting projection.
    if 'root'in s.lower() and re.search(r'[xX]\s*(?:>=|>)\s*root',s):
        mm=re.search(r'root(?: in)? \(((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?),((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)\)',plain(r['raw_M_row']['exact_statement'])+' '+s)
        if mm:
            br=[rat(mm[1]),rat(mm[2])];closed='>='in s
            d['exact_symbolic_intervals']=[{'lower':{'coordinate':'x','root_defined_by_source_object':r['key'],'certified_open_rational_bracket':br},'upper':None,'left_closed':closed,'right_closed':False}]
            d['plot_intervals']=[{'lower':{'coordinate':'x','rational':br[1],'exact_original':'conservative upper endpoint of the certified root bracket; NOT the exact ray boundary'},'upper':None,'left_closed':False,'right_closed':False}]
            d['unplotted_root_microband_is_not_a_claimed_failure']=True
            return d
    # The C015 integer n is explicitly fixed in its own local-root assertion.
    if r['key']==['FOLLOWUP-C015','R-local-segment']:
        d.update(source_parameter_substitution={'n':'38358837682','defining_source_object':['FOLLOWUP-C015','R-local']},numeric_intervals=[{'lower':{'coordinate':'x','rational':rat(38358837683),'exact_original':'n+1'},'upper':{'coordinate':'x','rational':rat(38358937683),'exact_original':'n+100001'},'left_closed':True,'right_closed':False}]);return d
    # Source-local English ray grammar, as literal as an inequality.
    sm=re.search(r'(?:starting|beginning|from|onset(?: at)?) (?:at )?([xLtu])=((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)',s)
    if sm:s+='; '+sm[1]+'>='+sm[2]
    # Two separately written inequalities on the SAME variable form an interval.
    lm=re.search(r'\b([xLtuv])\s*(>=|>)\s*((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)(?![\w^/])',s)
    um=re.search(r'\b([xLtuv])\s*(<=|<)\s*((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)(?![\w^/])',s)
    if lm and um and lm[1]==um[1] and all(re.fullmatch(NUM,m[3])for m in [lm,um]):
        v='x'if lm[1]=='x'else'L'
        d['numeric_intervals']=[{'lower':{'coordinate':v,'rational':rat(lm[3]),'exact_original':lm[3]},'upper':{'coordinate':v,'rational':rat(um[3]),'exact_original':um[3]},'left_closed':lm[2]=='>=','right_closed':um[2]=='<='}];return d
    if r['candidate_id']=='FOLLOWUP-C011'and r['claim_id'].startswith('M-old-early-'):
        mm=re.search(r'on L>=((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)',plain(r['raw_M_row']['exact_statement']));need(mm is not None,'own full scalar statement onset')
        d['numeric_intervals']=[{'lower':{'coordinate':'L','rational':rat(mm[1]),'exact_original':'same exact written claim onset'},'upper':None,'left_closed':True,'right_closed':False}];return d
    if r['candidate_id']in ['FOLLOWUP-C019','FOLLOWUP-C022'] and r['claim_id']=='R.U-mid':
        mm=re.search(r'((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)<=L<=((?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?(?:/\d+)?)',plain(r['raw_M_row']['exact_statement']));need(mm is not None,'own full finite source statement endpoints')
        d['numeric_intervals']=[{'lower':{'coordinate':'L','rational':rat(mm[1]),'exact_original':mm[1]},'upper':{'coordinate':'L','rational':rat(mm[2]),'exact_original':mm[2]},'left_closed':True,'right_closed':True}];return d
    if r['key']==['FOLLOWUP-C022','D02.R.raw']:
        d['numeric_intervals']=[{'lower':{'coordinate':'L','rational':rat(49),'exact_original':'joined receiving theorem at L49'},'upper':None,'left_closed':True,'right_closed':False}]
        d['source_provider_join']={'finite_second_coefficient_checks_through_L':'58','CH2_through_L':'222','direct_A_tail_after_L':'222','tail_anchor_L':'200','both_shifted_arguments_must_lie_in_direct_A_domain':True,'proof_source_LF':[204,212,338,345],'fresh_review_LF':[22,24,26]};return d
    # These are literal intervals only. No root, per-argument height guard, parameter,
    # conditional quantifier or finite tape diagnostic is silently promoted to a ray.
    if any(t in s.lower()for t in ['root','each argument','individ','option','guard','counterfactual','finite scan','only through','diagnostic','satisf','both arg','parameter','source domain']):return d
    s=s.replace('infinity','inf').replace('∞','inf').replace('L∈','L in ')
    atom=NUM+r'(?:\*10\^\d+)?|10\^\d+|e\^\(?'+NUM+r'\)?|exp\('+NUM+r'\)|log\('+NUM+r'\)'
    def val(a,var):
        a=a.strip()
        if a=='inf':return None
        if a.startswith(('exp(','e^')):
            n=re.search(NUM,a).group();return {'coordinate':'L','rational':rat(n),'exact_original':a}
        if a.startswith('log('):return {'coordinate':'L','log_of_rational':rat(a[4:-1]),'exact_original':a}
        if '*10^'in a:v,c=a.split('*10^');q=Q(v)*10**int(c)
        elif a.startswith('10^'):q=Q(10)**int(a[3:])
        else:q=Q(a)
        return {'coordinate':var,'rational':rat(q),'exact_original':a}
    # Explicit lower and upper inequalities; upper endpoint parsed independently.
    m=re.search(r'('+atom+r')\s*<=\s*([xLtuv])\s*<=\s*('+atom+r')',s)
    if m:
        var='x'if m[2]=='x'else'L';d['numeric_intervals']=[{'lower':val(m[1],var),'upper':val(m[3],var),'left_closed':True,'right_closed':True}];return d
    ints=list(re.finditer(r'([\[(])\s*('+atom+r')\s*,\s*('+atom+r'|inf)\s*([\])])',s))
    if len(ints)==1 and not any(t in s for t in [' then ',' and [',' plus ']):
        m=ints[0];before=s[:m.start()];after=s[m.end():]
        if re.search(r'\bx\s*(?:∈|in|=|:)?\s*$',before)or re.search(r'^\s*(?:in |for )x\b',after):var='x';basis='Explicit x immediately binding the written interval.'
        elif re.search(r'\b[Ltuv]\s*(?:∈|in|=|:)?\s*$',before)or re.search(r'^\s*(?:in |for )[Ltuv]\b',after)or'log interval'in s.lower():var='L';basis='Explicit logarithmic variable binding the interval.'
        elif re.search(r'\bx\b',s)and not re.search(r'\b[Ltuv]\b|log',s):var='x';basis='Explicit x-only written domain context.'
        elif re.search(r'\b[Ltuv]\b|log',s)and not re.search(r'\bx\b',s):var='L';basis='Explicit log-only written domain context.'
        else:
            policy=load(O/'EXACT_BARE_INTERVAL_SOURCE_AXIS_POLICY.json')['all248_exact_objects'];matched=[a for a in policy if a['key']==r['key']]
            if not matched:d['unresolved_axis']='Bare finite interval has no explicit source/provider axis policy; no default L.';return d
            need(len(matched)==1 and matched[0]['source_identity']==r['source'],'exact written-source axis context binding');axis=matched[0];var=axis['axis'];basis=axis['provider_context_rule'];d['source_axis_context']=axis['exact_same_source_context']
        d['source_interval_axis']=var;d['source_axis_basis']=basis
        d['numeric_intervals']=[{'lower':val(m[2],var),'upper':val(m[3],var),'left_closed':m[1]=='[','right_closed':m[4]==']'and m[3]!='inf'}];return d
    m=re.search(r'\b([xLtuv])\s*(>=|>)\s*('+atom+r')(?![\w^/])',s)
    if m:
        # Semicolon with a second unrelated domain remains symbolic unless it merely
        # explains an analytic join establishing this very whole ray.
        rest=s[m.end():]
        if re.search(r'\b(?:[xLtuv])\s*<=',rest):return d
        var='x'if m[1]=='x'else'L';d['numeric_intervals']=[{'lower':val(m[3],var),'upper':None,'left_closed':m[2]=='>=','right_closed':False}]
    return d
def recipient_domain(r,b,d):
    """Source-explicit extra receiving-error guards and literal joined pieces."""
    if r['candidate_id']not in ['FOLLOWUP-C020','FOLLOWUP-C023']:return d
    s=plain(r['raw_M_row']['full_domain'])
    # D1 is the reciprocal-prime-sum error here, not an input stage. Products
    # keep their own earlier onset; only ES acquires the additional guard.
    if b['quantity']=='ES'and ('additionally x>=2278383 for D1'in s or'D1 only from 2278383'in s):
        need(len(d['numeric_intervals'])==1,'one base C020 source ray')
        interval=d['numeric_intervals'][0];lo=interval['lower']
        if lo['coordinate']=='x':
            low=max(unrat(lo['rational']),Q(2278383));newlo={'coordinate':'x','rational':rat(low),'exact_original':'source D1/ES maximum of its two required x-onsets'}
            return {**d,'numeric_intervals':[{**interval,'lower':newlo}],'recipient_specific_guard':'D1/ES additionally x>=2278383; products retain their earlier own onsets.'}
        need(lo['coordinate']=='L'and unrat(lo['rational'])in[Q(27),Q(32)],'exact C020 exponential onset cases')
        # e^27>2278383 is already elementary (e>2 implies e^27>2^27).
        need(2**int(unrat(lo['rational']))>2278383,'log onset implies the extra x guard')
        return {**d,'recipient_specific_guard':'Source L>=27 or32 implies x>=2278383; both ES guards retained.'}
    m=re.fullmatch('('+NUM+r')<=x<=2278383; same coefficient continues on x>=2278383',s)
    if m:
        need(b['quantity']=='EW','literal C020 joined weighted-source error')
        low={'coordinate':'x','rational':rat(m[1]),'exact_original':m[1]}
        edge={'coordinate':'x','rational':rat(2278383),'exact_original':'2278383'}
        return {**d,'numeric_intervals':[{'lower':low,'upper':edge,'left_closed':True,'right_closed':True},{'lower':edge,'upper':None,'left_closed':True,'right_closed':False}],'literal_source_join':'Finite interval followed by the explicitly source-proved continuing ray. Kept as two pieces.'}
    return d

def role(r,bounds):
    ident=r['claim_id'];s=plain(r['raw_M_row']['exact_statement']).lower();sd=s+' '+plain(r['raw_M_row']['full_domain']).lower();q=r.get('Root_object_qualification')or{}
    if q.get('object_class')=='VALID_GUARD_FAILURE_DIAGNOSTIC_NO_POSITIVE_SUFFIX':return 'COMPARISON_OR_EXPERIMENT_DIAGNOSTIC'
    if r['candidate_id']=='FOLLOWUP-C018'and ident.startswith('M-witness-'):return 'COMPOUND_VALID_BOUND_AND_DIAGNOSTIC'
    if r['candidate_id']=='FOLLOWUP-C020'and ident=='R-PT-literal':return 'TRUE_REFUTATION_NOT_THE_REFUTED_BOUND'
    if 'TRUE_REFUTATION'in r.get('object_role','')or ident=='R2-withdrawn-15000':return 'TRUE_REFUTATION_NOT_THE_REFUTED_BOUND'
    if 'false'in s and any(t in ident.lower()for t in ['withdrawn','refut','source','counterexample']):return 'TRUE_REFUTATION_NOT_THE_REFUTED_BOUND'
    if not bounds and ('diagnostic only'in s or 'last failed cell'in s):return 'COMPARISON_OR_EXPERIMENT_DIAGNOSTIC'
    if 'bounding functions'in s or 'paired margin coefficient brackets'in s:return 'COMPARISON_OR_EXPERIMENT_DIAGNOSTIC'
    if any(t in ident.lower()for t in ['trial','failed','obstruction','diagnostic','compare','comparison','crossover','witness']):return 'COMPARISON_OR_EXPERIMENT_DIAGNOSTIC'
    if any(t in s for t in ['limit','limsup','little-o','tends to','no constant','no eventual constant']):return 'ASYMPTOTIC_LIMIT_OR_OBSTRUCTION'
    if bounds:return 'FINITE_EXPLICIT_BOUND_FUNCTION'
    if any(t in sd for t in ['every fixed','every integer','for each fixed','arbitrary','any nonnegative','every admissible','parametric','floor(l/']) or re.search(r'Σ.*(?:n-1|\(n|\^n|\^\{n)',sd):return 'PARAMETRIC_OR_OPERATOR_FAMILY'
    if any(t in s for t in ['pointwise','intersect','envelope','signed interval','minim','maximum','lower profile','shaped gap','signed transfer']):return 'SIGNED_OR_POINTWISE_OPERATOR'
    if any(t in s for t in ['root','last real','least integer','sign holds','strict sign','positive whole','connected','finite bridge']):return 'FINITE_ONSET_SIGN_OR_ROOT_FUNCTION'
    if ident.startswith(('M.secondary','M.prior-short','M.prior-A4','A-D02')):return 'AUXILIARY_COROLLARY_OUTSIDE_FOUR_M_ERRORS'
    return 'FOUNDATION_IDENTITY_OR_PROOF_PROVIDER'
def scope(r):
    from premises import object_scope
    return object_scope(r)
def main():
    data=load(O/'ALL24_SOURCE_BOUND_OBJECTS.json');collection_pin=pin(O/'ALL24_SOURCE_BOUND_OBJECTS.json');out=[];counts=collections.Counter();bounds=[];files={}
    environments={p['candidate_id']:{'primary_source_LOCK':p['complete_source'],'additional_own_history_view_LOCKs':p['review_source_views']}for p in data['portfolios']}
    for r in data['objects']:
        b=r_bounds(r)if r['family']=='Ramanujan'else m_bounds(r);d=domain(r);kind=role(r,b);sc=scope(r)
        if kind in ['COMPARISON_OR_EXPERIMENT_DIAGNOSTIC','TRUE_REFUTATION_NOT_THE_REFUTED_BOUND','ASYMPTOTIC_LIMIT_OR_OBSTRUCTION']:b=[]
        for i,x in enumerate(b):
            if 'coefficients_by_inverse_log_degree'in x:x['coefficients']=x.pop('coefficients_by_inverse_log_degree');x['degree']=x.pop('highest_inverse_log_degree')
            x.update(bound_id=r['candidate_id']+':'+r['claim_id']+':'+str(i),object_key=r['key'],candidate_id=r['candidate_id'],source=r['source'],domain=d,scope=sc,
                     assumptions=r['raw_M_row']['assumptions'],strictness=x.pop('branch_strictness',r['raw_M_row']['strictness']),plot_semantics='diagnostic evaluation of already accepted source-bound function, not a new proof')
            if 'explicit_onset_L'in x:x['domain']={**d,'numeric_intervals':[{'lower':{'coordinate':'L','rational':x['explicit_onset_L'],'exact_original':'source-explicit per-case onset'},'upper':None,'left_closed':True,'right_closed':False}]}
            if 'explicit_onset_x'in x:
                x['domain']={**d,'numeric_intervals':[{'lower':{'coordinate':'x','rational':x['explicit_onset_x'],'exact_original':'exact source receiving-error onset'},'upper':None,'left_closed':True,'right_closed':False}]}
            if 'explicit_interval_L'in x:
                x['domain']={**d,'numeric_intervals':[{'lower':{'coordinate':'L','rational':x['explicit_interval_L'][0],'exact_original':'exact source replacement left endpoint'},'upper':{'coordinate':'L','rational':x['explicit_interval_L'][1],'exact_original':'exact source replacement right endpoint'},'left_closed':True,'right_closed':True}]}
            if 'explicit_interval_x'in x:
                x['domain']={**d,'numeric_intervals':[{'lower':{'coordinate':'x','rational':x['explicit_interval_x'][0],'exact_original':'exact finite certificate start'},'upper':{'coordinate':'x','rational':x['explicit_interval_x'][1],'exact_original':'exact finite certificate end'},'left_closed':True,'right_closed':True}]}
            x['domain']=recipient_domain(r,x,x['domain'])
            bounds.append(x)
        f=r['source']['file'];files.setdefault(f,{'pin':pin(f),'literal_LF_count':len(read_bytes(f).split(b'\n'))})
        rec={'key':r['key'],'family':r['family'],'claim_id':r['claim_id'],'candidate_id':r['candidate_id'],'stage_id':r['stage_id'],
             'object_role':kind,'scope':sc,'source':r['source'],'Root_finalization':r['Root_finalization'],'raw_review_row_hash':r['raw_M_row_sha256'],
             'statement_exact':r['raw_M_row']['exact_statement'],'current_qualified_statement':(r.get('Root_object_qualification')or{}).get('current_qualified_statement'),'Root_object_qualification':r.get('Root_object_qualification'),'domain':d,'assumptions_exact':r['raw_M_row']['assumptions'],
             'strictness_exact':r['raw_M_row']['strictness'],'remaining_trust_exact':r['raw_M_row'].get('remaining_trust'),'original_object_role':r.get('object_role'),'source_defined_function_interface':{'exact_body':(r.get('Root_object_qualification')or{}).get('current_qualified_statement',r['raw_M_row']['exact_statement']),'all_domain_and_parameter_guards':d,'complete_source_closure':environments[r['candidate_id']],'literal_provider_is_not_an_arithmetic_receiving_error':r['family']=='Mertens'and not is_m_receiver_row(r)},
             'finite_bound_ids':[x['bound_id']for x in b],
             'scalar_M_receiving_target_eligible':is_m_receiver_row(r)if r['family']=='Mertens'else None,
             'symbolic_definition':{'representation':'SOURCE_EXACT_DEFINITION_CLOSURE','body':(r.get('Root_object_qualification')or{}).get('current_qualified_statement',r['raw_M_row']['exact_statement']),'raw_unqualified_body_preserved':r['raw_M_row']['exact_statement'],
                  'anchor':r['source'],'definition_environment_source_file':f,'definition_environment_sha256':r['source']['sha256'],
                  'complete_pinned_definition_environment':environments[r['candidate_id']],
                  'canonical_change_of_variable':'L=log(x); x=exp(L)',
                  'canonical_receiving_targets':['G']if r['family']=='Ramanujan'else ALL,
                  'guard_semantics':'Every original domain/premise/parameter and shifted-argument guard is retained verbatim. Source-defined integrals, sums, intersections, exponentiation and max/min are unevaluated exact operators, not scalar approximations.',
                  'not_a_separately_counted_quantitative_theorem':kind=='FOUNDATION_IDENTITY_OR_PROOF_PROVIDER'},
             'all_parameters_and_raw_M_evidence_ref':{'collection':collection_pin,'key':r['key']}}
        if r['candidate_id']=='FOLLOWUP-C008':
            rec['additive_current_source_center_correction']=pin(N/'coordinator-private/C008-PT-Cor2-center-addendum-v1/ROOT_SOURCE_CENTER_CORRIGENDUM.json')
            rec['Root_final_presentation_V2']=pin(N/'protocol/finalized-D02-portfolios-v1/FRESH-R1-D02-IEANTN/FINAL_D02_PORTFOLIO_ROOT_V2.json')
            rec['current_operator_normalization_note']='PT Corollary2 already uses Li2; its interval is unshifted in current coordinates. Shift the distinct principal-value FiniteRH interval by li0(2). Root-approved whole-domain containment proves the actual declared pool and all401 bound functions unchanged; raw historical source body retained above.'
        out.append(rec);counts[kind]+=1
    need(len(out)==11411==len({tuple(x['key'])for x in out}),'complete twentyfour-stage normalization identity')
    save('NORMALIZED_OBJECTS.json',{'schema':'ALL24_CANONICAL_FUNCTIONAL_OBJECTS_V1','all_active_scoped_objects':len(out),
        'coverage_criterion':'All exact Root-sealed active IDs; no parser-dependent inclusion. Explicit scalar/vector functions additionally expanded. Non-scalar mathematical operators and all their source definitions remain symbolic, never counted as absent scalar theorems.',
        'objects':out,'object_role_counts':dict(counts),'definition_environment_files':list(files.values()),
        'canonical_R':'G(L)=L^6*(e*x*pi(x/e)/log(x)-pi(x)^2)/x^2, x=exp(L)',
        'canonical_M':{'ES':'abs(sum(p<=x,1/p)-log(log(x))-M)','EW':'abs(sum(p<=x,log(p)/p)-log(x)+B3)',
             'EP':'abs(exp(gamma)*log(x)*prod(p<=x,1-1/p)-1)','EQ':'abs(exp(-gamma)*prod(p<=x,(1-1/p)^(-1))/log(x)-1)'},
        'no_claim_of_machine_evaluation_of_all_integral_operator_frontiers':True})
    save('FINITE_EXPLICIT_FUNCTIONS.json',{'schema':'EXACT_EXPANDED_SCALAR_AND_VECTOR_BRANCHES_V1','bounds':bounds,'count':len(bounds),
        'does_not_replace_whole_symbolic_operator_frontier':True,'canonical_data':pin(O/'NORMALIZED_OBJECTS.json')})
    print(dict(counts));print('expanded finite bounds',len(bounds))
if __name__=='__main__':main()
