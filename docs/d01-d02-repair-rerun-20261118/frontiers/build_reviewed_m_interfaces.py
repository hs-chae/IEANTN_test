"""Explicitly read literal Mertens clauses, in the existing canonical schema.

This supplements descriptive parser coverage. These are parameters/statements
already present in the accepted written sources, not new mathematical outputs.
"""
from collect import O,load,need,save,pin,sha,read_bytes,Path
from fractions import Fraction as Q
import re

def rational(x):
    x=Q(x);return {'numerator':str(x.numerator),'denominator':str(x.denominator)}
ALL=['ES','EP','EQ','EW'];FIRST=ALL[:3]
def main():
    source=load(O/'ALL24_SOURCE_BOUND_OBJECTS.json');by={tuple(x['key']):x for x in source['objects']};work=load(O/'CONCRETE_FOUNDATION_M_BINDING_WORKLIST.json')['groups'];entries=[];dispositions=[]
    # Independent source rereading found the old normalizer had fabricated a
    # weighted receiver at420000 for this first-three-only source claim.
    work=work+[{'exact_keys':[['FOLLOWUP-C021','M-power-420000']],'group':None},{'exact_keys':[['FOLLOWUP-C021','M-power-550000']],'group':None}]
    work+= [{'exact_keys':[[f'FOLLOWUP-C{c:03}',k]],'group':None}for c in [21,24]for k in ['M-old-power-.019851','M-old-power-.01985']]
    work+= [{'exact_keys':[['FOLLOWUP-C022','OwnD02.old.M24']],'group':None}]
    def add_entry(key,bounds,basis):
        row=by[tuple(key)];raw=row['raw_M_row'];entries.append({'key':list(key),'exact_written_source':{k:row['source'][k]for k in ['file','sha256','physical_LF','physical_LF_end']},'exact_statement':raw['exact_statement'],'exact_domain':raw['full_domain'],'exact_assumptions':raw['assumptions'],'functions':bounds,'basis':basis,'reviewed_clause_role':'COMPOUND_VALID_BOUND_AND_DIAGNOSTIC'if key[1].startswith('M-witness-')else'FINITE_EXPLICIT_BOUND_FUNCTION'})
    for group in work:
        for key in group['exact_keys']:
            cid,ident=key;c=int(cid[-3:]);row=by[tuple(key)];raw=row['raw_M_row'];text=raw['exact_statement'];bounds=[];basis=None;native=None
            def add(target,coefficient,rate=0,degree=None,**fields):
                if degree is None:degree=2 if target=='EW'else 3
                bounds.append({'kind':'M_power_log','quantity':target,'coefficient':rational(coefficient),'x_decay_exponent':rational(rate),'log_denominator_degree':degree,'operator':raw['strictness'],'canonical_formula':'c*exp(-alpha*L)/L**d','receiving_target_basis':'independently read exact accepted literal receiver clause, not a provider-to-receiver cast',**fields})
            def many(targets,coefficient,rate=0,first_degree=3,weighted_degree=2,**fields):
                for target in targets:add(target,coefficient,rate,weighted_degree if target=='EW'else first_degree,**fields)
            def positive_sum(target,terms,interval=None,interval_x=None,case=None,converted=False):
                add(target,1,0,0,kind_unused_for_constructor=True)
                out=bounds[-1];out.pop('kind_unused_for_constructor');out['kind']='M_exp_positive_sum'if converted else'M_positive_sum';out['positive_terms']=[{'coefficient':rational(co),'x_decay_exponent':rational(rate),'log_denominator_degree':degree,'pi_power':power}for co,rate,degree,power in terms];out['canonical_formula']=('exp('if converted else'')+'sum_j(c_j*pi^p_j*exp(-alpha_j*L)/L^d_j)'+(')-1'if converted else'')
                if interval is not None:out['explicit_interval_L']=[rational(z)for z in interval]
                if interval_x is not None:out['explicit_interval_x']=[rational(z)for z in interval_x]
                if case is not None:out['case']=case
            if c in [2,8]and ident=='M-W':
                pieces=[((17,29),[('3.25',Q(1,2),0,0)]),((29,58),[(Q(1,8),Q(1,2),-2,-1),(3,Q(1,2),0,0)]),((58,189),[('1.048e-12',0,0,0),(117,Q(1,2),0,0),('5e-11',Q(1,8),0,0)])]
                for interval,terms in pieces:
                    for target in ALL:
                        factor=Q('1.0001')if target in ['EP','EQ']else Q(1);positive_sum(target,[(Q(co)*factor,a,d+(0 if target=='EW'else 1),power)for co,a,d,power in terms],interval=interval)
                basis='Exact fixed source W pieces and the explicit1.0001 conversion for product relative errors; inverse-pi coefficient is exact1/(8pi), not a decimal. Last density/kernel W branch is separately retained as a named composite operator.'
            elif c==12 and ident=='M-old-directional':
                for target in ['EP','EQ']:add(target,'.1973',0,3,explicit_onset_x=rational(767135587));bounds[-1]['kind']='M_exp_log_enclosure'
                basis='Dusart proof of Theorem5.9, original PDFp20, already includes its -S<1.02/((x-1)logx) allowance inside.1973. Both normalized products lie between exp(-.1973/L^3) and exp(.1973/L^3); expm1(.1973/L^3) is a valid conservative relative radius. Full signed intersections remain retained.'
            elif c==17 and ident=='M-three-pieces':
                for target in ALL:
                    add(target,'.165'if target=='EW'else'.166',explicit_interval_x=[rational(10000000),rational(10000000000000)])
                    add(target,'.002',explicit_interval_x=[rational(10000000000000),rational(10000000000000000000)])
                    add(target,'.00008',explicit_domain_intervals=[{'lower':{'coordinate':'x','rational':rational(10000000000000000000),'exact_original':'x=10^19'},'upper':{'coordinate':'L','rational':rational(190),'exact_original':'L=190'},'left_closed':True,'right_closed':True}])
                basis='Actual three fixed whole intervals from mertens.mdLF335-358: first-three.166/weighted.165, then all.002, then all.00008; the B0power tail after190 is a separate existing branch.'
            elif c==17 and ident=='M-new-power-joins':
                many(ALL,'.117',case='B0',explicit_interval_L=[rational(17),rational(32)])
                for case,a,top in [('B0',Q(1,8),185),('D02',Q(5,32),166)]:
                    for target in ALL:
                        terms=[(Q(1,3000000000000),0,0,1),(115,Q(1,2),0,0),(Q(21,3000000000000),a,0,0),(3,1,0,0)];positive_sum(target,[(co,rate,d+(0 if target=='EW'else 1),power)for co,rate,d,power in terms],interval=(32,top),case=case,converted=target in ['EP','EQ'])
                basis='The actual.125 is a log slab width, not an error coefficient. The.117 inverse-log bridge and fixed CH2 middle majorant are receiving bounds; H=3*10^12 is fixed in spectral.mdLF3/profiles.pyLF4. Products use the conservative exact exponential conversion. Height menu/slab optimization remains source-defined.'
            elif c in [20,23]and ident=='M-signed-early-weighted':
                positive_sum('EW',[('1.837401',Q(1,2),0,0),('2.67',Q(2,3),0,0),('3.2e-12',Q(1,8),0,0),(2,1,0,0)],interval=(18,'29.9'));basis='Actual fixed four-term absolute weighted-prime-error upper bound; s,t,r,X definitions are literal source exponentials on the closed slab, not free parameters.'
            elif c in [21,24]and ident in ['M-old-power-.019851','M-old-power-.01985']:
                many(FIRST if ident.endswith('.019851')else['EW'],'.019851'if ident.endswith('.019851')else'.01985',Q(1,8),1,0,explicit_onset_L=rational(200));basis='Actual inherited slow-power receiver clause with its own zero-strip premise and method trust preserved; no stronger-premise function is used as a reproof of this source clause.'
            elif c==22 and ident=='OwnD02.old.M24':
                many(ALL,'.24',Q(5,32),1,0,explicit_onset_L=rational(200));basis='Actual earlier lawful Dusart-density proof gives all four receiver shapes with common.24. Its own source/method trust is preserved rather than silently replacing it by a later Table8 branch.'
            elif (c in [2,8]and ident=='M-old-polynomial-dominance'):

                many(ALL,'.2',explicit_onset_L=rational(17));basis='The actual source states strict .2/L^3 for first three and .2/L^2 for weighted throughout L>=17; W itself remains a separate exact operator.'
            elif c in [2,8]and ident in ['M-direct-first3','M-direct-weighted']:
                many(FIRST if ident.endswith('first3')else['EW'],'.147'if ident.endswith('first3')else'.152',Q(1,8),first_degree=-1,weighted_degree=-2,explicit_onset_L=rational(200));basis='Exact direct-D01 upper bounds with positive log losses; D01 is already implied by cumulative B0.'
            elif c==4 and ident.startswith('M-original-'):
                target={'M-original-P':'EP','M-original-Q':'EQ','M-original-S':'ES','M-original-W':'EW'}[ident];add(target,'.3'if target=='EW'else'.2');basis='Original displayed absolute or normalized relative error and its original inclusive real x onset.'
            elif ident in ['M-original-W2','M-Dusart-5.7','M-original-W']:
                add('EW','.3');basis='The exact weighted prime-error bound .3/L^2, retaining its own source real x onset.'
            elif c in [5,14]and ident=='M-CH80':
                add('EW','1.049e-12',0,0,explicit_onset_L=rational(80))
                for t in FIRST:add(t,'2.097e-12',0,1,explicit_onset_L=rational(80))
                basis='Exact source CH80 corollary has distinct weighted and first-three units, all real L>=80.'
            elif c in [5,14]and ident in ['M-bridge','M-coarse']:
                for t in ALL:add(t,('.0726'if t=='EW'else'.0667')if ident=='M-bridge'else'.08',explicit_onset_L=rational(20))
                basis='Source whole-ray analytic bridge/coarse caps in cubic first-three and quadratic weighted units; not a point or a finite cell extrapolation.'
            elif c==7 and (ident.startswith('M-d02_coeff.txt-18-')or ident.startswith('M-density-power-')or ident.startswith('M-basic-uniform-')or ident.startswith('M-basic-late-')):
                mm=re.search(r'≤\s*([.0-9]+)·exp',text);need(mm is not None,'EXACT_SOURCE_VECTOR_COEFFICIENT '+ident);a=Q(1,8)if ident=='M-basic-uniform-0'else Q(5,32);positive='(L²,L,L,L)'in text
                many(ALL,mm[1],a,first_degree=-1 if positive else 1,weighted_degree=-2 if positive else 0)
                basis='Actual vector order (weighted, reciprocal, exp(-z)-1, exp(z)-1); a_i=1/8 for the explicitly B0 basic row and5/32 for the explicitly D02 rows, confirmed by enclosing source.'
            elif c==8 and ident=='D2-M-tail-1000000-converted':
                many(ALL,'.146320',Q(1,8),1,0,coefficient_log_shift=rational(-Q(1000000,32)),explicit_onset_L=rational(1000000));basis='Exact source common slower power scale, including the source exp(-1000000/32) coefficient factor rather than replacing it by an unscaled number.'
            elif c==8 and ident=='D2-M-fixed-912560':
                add('EW','.29999946',explicit_onset_x=rational(912560));basis='Exact strict quadratic weighted coefficient at its original real closed x onset.'
            elif c==11 and ident=='M-old-direct':
                many(ALL,'.015626',Q(5,32),-1,-2,case='D02',explicit_onset_L=rational(200));basis='Exact source direct-D02 bound with positive logarithmic losses, preserving all four receiver units on its actual L>=200 ray.'
            elif c==13 and ident=='M-new-fallback-rounded':
                many(ALL,'.123',Q(5,32),-1,-2,explicit_onset_L=rational(200));basis='Exact fallback with positive logarithmic losses, not inverse-log gains.'
            elif c==13 and ident=='M-logbin-join':
                many(ALL,'.0503',explicit_onset_x=rational(9750000000));basis='Exact same common log-power cap at its inclusive real x onset.'
            elif c==16 and ident in ['M-old-product','M-old-reciprocal','M-old-weighted']:
                many(['EP','EQ']if ident=='M-old-product'else['ES']if ident=='M-old-reciprocal'else['EW'],'.3'if ident=='M-old-weighted'else'.2');basis='Original explicit receiver and its own source real x domain.'
            elif c==16 and re.fullmatch(r'M-power-5[1-9]',ident):
                m=re.fullmatch(r'M0 first-group bound C exp\(−aL\)/L and weighted bound C exp\(−aL\)\. B0 \(a=1/8,L0=([.0-9]+),C=([.0-9]+)\); B1 \(a=5/32,L0=([.0-9]+),C=([.0-9]+)\)\.',text);need(m is not None,'EXACT_SOURCE_TWO_CASE_POWER_TABLE '+ident)
                for case,a,on,co in [('B0',Q(1,8),m[1],m[2]),('D02',Q(5,32),m[3],m[4])]:many(ALL,co,a,1,0,case=case,explicit_onset_L=rational(on))
                basis='Both exact source-local B0/D02 cases, each with its distinct coefficient and inclusive whole-ray log onset.'
            elif c==16 and ident=='M-at200':
                for case,cfirst,cweighted in [('B0','1.305e-15','2.610e-13'),('D02','3.482e-17','6.964e-15')]:
                    for t in ALL:add(t,cweighted if t=='EW'else cfirst,0,0,case=case,explicit_interval_L=[rational(200),rational(200)])
                basis='Actual fixed-L=200 numerical enclosures remain singleton closed intervals, never promoted to rays.'
            elif c==16 and ident in ['M-fixed-prodR','M-fixed-G']:
                for case,on in [('B0',186 if ident=='M-fixed-prodR' else 190),('D02',167 if ident=='M-fixed-prodR' else 170)]:
                    for t in FIRST if ident=='M-fixed-prodR'else['EW']:add(t,'1e-14'if ident=='M-fixed-prodR'else'1e-12',0,0,case=case,explicit_onset_L=rational(on))
                basis='The actual source explicitly proves whole rays for these fixed absolute tolerances; each local case is separate.'
            elif c==16 and ident=='M-bridge-basic':
                many(ALL,'.05',explicit_onset_L=rational('21.41'));basis='Closed source bridge through200 and the separately proved monotone analytic tail, hence the joined whole ray from21.41.'
            elif c==17 and ident=='M-power-167-join':
                many(ALL,'.277',Q(5,32),1,0,explicit_interval_L=[rational(167),rational(170)]);basis='Only the actual source closed finite power-join segment [167,170]; no invented extension.'
            elif c==17 and ident=='M-cheap-join':
                many(FIRST,'.10994',explicit_onset_x=rational(25000000));basis='Actual first-three-only cubic ray at25million; no weighted receiver is inferred.'
            elif c==18 and ident in ['M-Dusart-products','M-Dusart-reciprocal','M-Dusart-weighted']:
                many(['EP','EQ']if ident.endswith('products')else['ES']if ident.endswith('reciprocal')else['EW'],'.3'if ident.endswith('weighted')else'.2');basis='Original Dusart error types and inclusive real x onsets, with no conversion of psi or Lambda providers.'
            elif c in [19,22]and ident=='M.old-PS':
                many(FIRST,'.170',explicit_onset_L=rational(22));add('EW','.235',explicit_onset_L=rational(21));basis='Actual earlier asymmetric-smoothing receiver corollaries, with distinct first-three and weighted log onsets.'
            elif c in [20,23]and ident in ['M-old-011-link','M-old-weighted-0165']:
                many(FIRST if ident=='M-old-011-link'else['EW'],'.011'if ident=='M-old-011-link'else'.0165',explicit_onset_x=rational(4760000000));basis='Original repaired source branch retains its actual stated real domain; its proof closure includes the finite bridge, not the invalid old argument.'
            elif c in [21,24]and ident=='M-Dusart-products':
                many(['EP','EQ'],'.2',explicit_onset_x=rational(2278382));basis='Original two normalized relative product bounds, not an inferred prime-sum clause.'
            elif c in [20,23]and ident=='M-signed-PI-slab':
                for t in ALL:
                    add(t,'2.25',Q(1,2),0 if t=='EW'else 1,explicit_interval_L=[rational('29.9'),rational('43.7')])
                    if t in ['EP','EQ']:bounds[-1]['kind']='M_exp_log_enclosure'
                basis='Actual source absolute max(|L D1|,|D2|,|L ZQ|)<=2.25 exp(-L/2). Products use exp(radius)-1; the correlated signed slab remains separately retained, and no logarithm is confused with relative error.'
            elif c in [21,24]and ident in ['M-aux-repaired','M-analytic-1.94']:
                first,weighted,lo,hi=('1.70','1.88',10000,100000000)if ident=='M-aux-repaired'else('1.94','1.94',100000000,10000000000000)
                for t in ALL:
                    add(t,weighted if t=='EW'else first,Q(1,2),0 if t=='EW'else 1,explicit_interval_x=[rational(lo),rational(hi)])
                    if t in ['EP','EQ']:bounds[-1]['kind']='M_exp_log_enclosure'
                basis='Actual source q=log normalized reciprocal product, u=centered reciprocal sum, j=weighted sum: distinct first-three/weighted units retained. Both products are bounded through exp(abs(log radius))-1, never identified with the log itself.'
            elif c==21 and ident=='M-power-550000':
                add('EW','.01325',Q(1,8),0,explicit_onset_x=rational(550000),preserve_bound_id_suffix=3);basis='Exact weighted-only source branch at550000. Earlier first-three source420000 already covers their restrictions beyond550000; no extra receiver is attributed to this weighted row.'
            elif c in [21,24]and ident=='M-power-420000':
                many(FIRST,'.01325',Q(1,8),1,0,explicit_onset_x=rational(420000));basis='Exact source first-three-only slow-power corollary, on its inclusive real x ray; no weighted or stronger-premise claim inferred.'
            elif c in [10,11,21,24]and any(t in ident for t in ['M-local-','M-exact-onset-','M-root-']):
                rawtext=raw['exact_statement']
                if c==10:
                    mm=re.search(r'at (\d+)\+t, t in \(([.0-9]+),([.0-9]+)\)',rawtext);need(mm is not None,'EXACT_LOCAL_ROOT_OFFSET_BRACKET');br=[Q(mm[1])+Q(mm[2]),Q(mm[1])+Q(mm[3])];target={'75':'EQ','76':'EP','77':'ES','78':'EW'}[ident.rsplit('-',1)[1]];targets=[target]
                else:
                    mm=re.search(r'(?:∈|in)\s*\(([.0-9]+),([.0-9]+)\)',rawtext);need(mm is not None,'EXACT_SOURCE_REAL_ROOT_BRACKET '+str(key));br=[Q(mm[1]),Q(mm[2])]
                    targets=['ES']if ident in ['M-exact-onset-S','M-root-u']else['EW']if ident in ['M-exact-onset-W','M-root-j']else['EP']if ident in ['M-exact-onset-P','M-root-P']else['EQ']if ident=='M-exact-onset-Q'else['EP','EQ']
                need(1<br[0]<br[1],'ORDERED_EXACT_RATIONAL_ROOT_BRACKET')
                for t in targets:add(t,'.3'if t=='EW'else'.2',explicit_source_root={'certified_open_rational_bracket':[rational(z)for z in br],'root_defined_by_source_object':list(key)},strict_above_root_proved_by_source=c in [21,24],branch_strictness='non-strict <= on the closed source root ray; strict < above it'if c in [21,24]else'non-strict <= on the closed source root ray; equality at the least onset; global strictness not claimed')
                basis='Source-fixed original tolerance with its actual receiver and exact real root; C010/C011 license only the non-strict closed ray, whereas C021/C024 explicitly license a further strict open ray. Only a separately labeled conservative upper-bracket projection is used by numerical plots.'
            elif ident.startswith(('M-signed-','MA-signed-','M-sign-')):
                native='EXACT_SOURCE_DEFINED_SIGNED_OR_CORRELATED_INTERVAL: literal signed lower/upper inequalities retained in the complete interface. A sign, log-product or correlated linear form is not silently cast to an absolute normalized product-error cap.'
            elif ident=='M-finite-only':
                native='HISTORICAL_FINITE_CERTIFICATE_SCOPE_RESTRICTION: this saved earlier review restricts the old sweep at its recorded finite onsets; it does not revoke the later independently repaired M-extended-.10/.11 whole-ray proofs. Original finite outputs and old review are preserved, with later branches separately source-linked.'
            elif ident in ['M-aux-repaired','M-analytic-1.94','M-power-420000']:
                native='EXACT_SOURCE_DEFINED_COMPOUND_OPERATOR_OR_BRANCH_TABLE: source gives a piecewise/signed or multi-observable function with its complete definitions and domains; this comparison retains the native function rather than replacing it by an unproved scalar radius. Exact literal receiving subclauses require the accompanying explicit source-interface mapping.'
            else:native='PENDING_LITERAL_SCOPE_BINDING_NO_COMPLETENESS_CLAIM'
            if bounds:add_entry(key,bounds,basis);status='ADDITIVE_EXACT_SOURCE_LITERAL_CANONICAL_RECEIVER_FUNCTIONS'
            else:status=native
            dispositions.append({'key':key,'group':group['group'],'exact_literal_statement':text,'source':{k:row['source'][k]for k in ['file','sha256','physical_LF','physical_LF_end']},'status':status,'functions_added':len(bounds),'basis':basis})
    # Compound20 finite witnesses retain both the failed witness and its own
    # positive finite suffix; a generic 'witness' name is not an exclusion rule.
    for row in source['objects']:
        if row['candidate_id']!='FOLLOWUP-C018'or not row['claim_id'].startswith('M-witness-'):continue
        key=row['key'];raw=row['raw_M_row'];m=re.fullmatch(r'M-witness-([0-3])-(\d+)',key[1]);d=re.fullmatch(r'x=\d+ and finite ray segment \[(\d+),(\d+)\]',raw['full_domain']);need(m is not None and d is not None,'EXACT_FINITE_WITNESS_SOURCE_DOMAIN')
        target=['ES','EQ','EW','EP'][int(m[1])];bounds=[{'kind':'M_power_log','quantity':target,'coefficient':rational(Q(int(m[2]),1000)),'x_decay_exponent':rational(0),'log_denominator_degree':2 if target=='EW' else 3,'operator':'<=','canonical_formula':'c/L**d','receiving_target_basis':'only the accepted positive finite certificate part of the compound source truth','explicit_interval_x':[rational(d[1]),rational(d[2])],'branch_strictness':'non-strict <= on the source finite certificate segment','compound_truth_object':'The separate earlier violation witness remains true; this bound starts only at this own source certificate onset.'}];add_entry(key,bounds,'Exact finite source suffix, each coefficient/observable has its own stated onset; the failed point is not included in this upper-bound domain.');dispositions.append({'key':key,'status':'ADDITIVE_POSITIVE_FINITE_PART_WITH_SEPARATE_TRUE_WITNESS','functions_added':1,'source':{k:row['source'][k]for k in ['file','sha256','physical_LF','physical_LF_end']}})
    for entry in entries:
        for fn in entry['functions']:
            if fn['kind']in ['M_positive_sum','M_exp_positive_sum']:continue
            inner='c*exp(coefficient_log_shift-alpha*L)/L**d'if'coefficient_log_shift'in fn else'c*exp(-alpha*L)/L**d'
            fn['canonical_formula']='exp('+inner+')-1'if fn['kind']=='M_exp_log_enclosure'else inner
    for row in source['objects']:
        if row['candidate_id']!='FOLLOWUP-C024'or row['claim_id']not in ['M-new-root-16','M-new-root-17','M-new-root-18','M-new-root-19']:continue
        key=row['key'];raw=row['raw_M_row'];m=re.search(r'root in \(([0-9/]+),([0-9/]+)\)',raw['exact_statement']);need(m is not None,'EXACT_NEW_POWER_ROOT_FRACTION_BRACKET');br=[rational(m[1]),rational(m[2])];suffix=key[1].rsplit('-',1)[1];targets=['EP','EQ']if suffix=='16'else['EP']if suffix=='17'else['ES']if suffix=='18'else ALL
        funcs=[]
        for t in targets:funcs.append({'kind':'M_power_log','quantity':t,'coefficient':rational('.25665'),'x_decay_exponent':rational(Q(5,32)),'log_denominator_degree':0 if t=='EW' else 1,'operator':'<=','canonical_formula':'c*exp(-alpha*L)/L**d','receiving_target_basis':'actual m_d02.md powerrow c=.25665,b=27/32; exact native observable/root case','explicit_source_root':{'certified_open_rational_bracket':br,'root_defined_by_source_object':list(key)},'strict_above_root_proved_by_source':True,'branch_strictness':'non-strict <= at and above the exact source-defined root; strict < above that root'})
        add_entry(key,funcs,'Actual source m_d02.md LF3-21 binds this root to narrower-power row c=.25665 and b=27/32, x not log x; joint products/four-error clauses preserve their actual receivers.');dispositions.append({'key':key,'status':'ADDITIVE_EXACT_POWER_TOLERANCE_WITH_SOURCE_DEFINED_REAL_ROOT','functions_added':len(funcs),'source':{k:row['source'][k]for k in ['file','sha256','physical_LF','physical_LF_end']}})
    need(len({tuple(e['key'])for e in entries})==len(entries),'UNIQUE_EXACT_SOURCE_INTERFACE_OVERRIDES')
    for entry in entries:
        if entry['key'][1]!='M-W':continue
        parent=Path(entry['exact_written_source']['file']).parent
        refs=[]
        for file,lo,hi,symbol in [(parent/'common.md',14,36,'D'),(parent/'mertens.md',84,99,'J2'),(parent/'mertens.md',67,82,'V_b')]:
            lines=read_bytes(file).decode().split('\n');refs.append({'symbol':symbol,'file':str(file),'sha256':sha(file),'physical_LF':lo,'physical_LF_end':hi,'exact_readback':'\n'.join(lines[lo-1:hi])})
        late={'op':'add','args':[{'op':'source_function_call','symbol':'D','argument':'L'},{'op':'multiply','args':[{'op':'add','args':[{'rational':rational(1)},{'op':'inverse','argument':'L'}]},{'op':'source_function_call','symbol':'J2','argument':'L'}]},{'op':'source_function_call','symbol':'V_b','argument':'L'}]}
        entry['native_operators']=[{'kind':'FIXED_SOURCE_DEFINED_DENSITY_KERNEL_COMPOSITE_RECEIVER','quantity':target,'expression':{'op':'multiply','args':[{'rational':rational('1.0001'if target in ['EP','EQ']else 1)},late,{'op':'power','base':'L','integer_exponent':0 if target=='EW' else -1}]},'domain':{'lower_L':rational(189),'left_closed':True,'upper':None},'exact_named_definition_sources':refs,'provider_domain_applicability':'L>=189 satisfies D(L) domainL>=100, integrated J2 domainL>=1 and prime-power V_b domainx>=8.','numerical_evaluation_performed':False,'classification':'Fixed density/kernel composite, not a free parameter family; retained with its exact definitions, explicitly unoptimized.'}for target in ALL]
    save('REVIEWED_M_LITERAL_RECEIVER_INTERFACES_V1.json',{'schema':'SOURCE_REVIEWED_LITERAL_RECEIVER_INTERFACE_SUPPLEMENT_V1','source_universe':pin(O/'ALL24_SOURCE_BOUND_OBJECTS.json'),'source_scope':'Explicit clauses independently read in current accepted source universe; source addresses and mathematical assumptions unchanged.','entries':entries,'new_mathematical_claims':False,'new_program_evaluation_or_certificates':False})
    save('M_LITERAL_RECEIVER_SCOPE_DISPOSITIONS_V1.json',{'status':'EXPLICIT_M_LITERAL_SCOPE_REVIEW_WITH_ALL_UNRESOLVED_ITEMS_VISIBLE','source_flags':pin(O/'CONCRETE_FOUNDATION_M_BINDING_WORKLIST.json'),'rows':dispositions,'pending_count':sum('PENDING'in x['status']for x in dispositions),'interface_count':len(entries),'canonical_function_count':sum(len(x['functions'])for x in entries)})
    print('SOURCE_BOUND_M_ENTRIES',len(entries),'FUNCTIONS',sum(len(x['functions'])for x in entries),'PENDING',sum('PENDING'in x['status']for x in dispositions))
if __name__=='__main__':main()
