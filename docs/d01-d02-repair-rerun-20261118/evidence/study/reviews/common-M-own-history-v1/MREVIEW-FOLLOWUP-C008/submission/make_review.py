"""Build this review's exact-file claim and evidence ledger after a completed replay."""
import hashlib, json, re
from pathlib import Path
from collections import Counter
from decimal import Decimal

A=Path('/work/c008'); T=Path('/task'); Q=Path('/work/submission')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def dump(n,obj):(Q/n).write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n')
def lines(n):return (A/n).read_bytes().decode().split('\n')
ix=load(T/'CANDIDATE_INDEX.json')
sources=load(T/'SOURCE_INDEX.json')['sources']
by={r['original_name']:r for r in ix['candidate_files']}
for r in by.values():assert sha(A/r['original_name'])==sha(T/r['packet_name'])==r['sha256']
for r in sources:
    for k in ('pdf','text'):assert sha(Path('/corpus/originals')/r[k])==r[k+'_sha256']

def ref(n,i,j=None,read=False):
    j=i if j is None else j
    assert 0<i<=j<=len(lines(n)),(n,i,j)
    r=by[n]
    d=dict(file=r['packet_name'],physical_LF=i,physical_LF_end_inclusive=j,
           original_name=n,sha256=r['sha256'])
    if read:d['locked_readback']='\n'.join(lines(n)[i-1:j])
    return d

jobs={
'verify.py--endpoint':('verify.log','Quotient-compressed exact local counts; root bracket, Li anchor, old fixed closed meshes, nine tails, density constants',
                       ['verify.py','count.py'],[]),
'bridge.py':('bridge.log','38358837683 through 100000000000, 61642 blocks, both odd streams, 2473381581 prime jumps',
             ['bridge.py','bridge.c','verify.py'],[]),
'general.py':('general.log','Default P_n orders 20,24,32,48,64 with certified cutoffs',
              ['general.py','verify.py'],[]),
'early.py':('early.log','From 2 (plus clipped onsets) through 2278383; both product-relative errors and both sums',
            ['early.py','verify.py'],[]),
'weighted.py':('weighted.log','Weighted cells through 66000000, normalizer cutoff 25000000',
                ['weighted.py','early.py','verify.py'],[]),
'smallprod.py':('smallprod.log','Both products and reciprocal sum through 66000000, M normalizer through 2278383',
                 ['smallprod.py','weighted.py','early.py','verify.py'],[]),
'mverify.py':('mverify.log','Old signed spectral envelope W, [14,17]/[17,29]/[29,58]/[58,189]/tail and crossings',
               ['mverify.py','verify.py'],[]),
'tradeoff.py':('tradeoff.log','EC-only unit bridge [60,269], six direct-D01 factorial tails and two direct Mertens constants',
                ['tradeoff.py','verify.py'],[]),
'receipts.py':(None,'Selected older matching finite threshold comparisons',
                ['receipts.py'],['smallprod.log','early.log','weighted.log','bridge.log']),
'spectral_repair.py':('spectral_repair.log','Sharper weights, Wstar bands and comparisons, density-free polynomial fallback from 230',
                       ['spectral_repair.py','verify.py'],['smallprod.log','weighted.log']),
'power_bridge.py':('power_bridge.log','Finite power cells through composite 1202606 and normalization through 5000000',
                    ['power_bridge.py','smallprod.py','weighted.py','early.py','verify.py'],[]),
'gap_repair.py':('gap_repair.log','19 older adaptive joins and 14 deeper factorial thresholds',
                  ['gap_repair.py','spectral_repair.py','verify.py'],['smallprod.log','weighted.log']),
'optimize_d02.py':('optimized.log','38 reported directed factorial endpoints, two caps, selected m and k only',
                    ['optimize_d02.py','d02_cert.py','verify.py'],[]),
'finite_d02.py':('finite_d02.log','New polynomial/fractional joins through 66000000, N=66000000',
                  ['finite_d02.py','d02_cert.py','verify.py','early.py','weighted.py','smallprod.py'],[]),
'finite_d02.py--extended':('finite_extended.log','New polynomial joins through 300000000, N=66000000',
                            ['finite_d02.py','d02_cert.py','verify.py','early.py','weighted.py','smallprod.py'],[]),
'power_new.py':('power_new.log','New power joins through 24154954; N=5000000; rightward fixed-point scaling',
                 ['power_new.py','d02_cert.py','verify.py','early.py','weighted.py','smallprod.py'],[]),
'run_d02.py':('d02_checks.log','All new analytic cells and ray checks from submitted proof, and exact finite receipt joins',
               ['run_d02.py','d02_cert.py','verify.py','early.py'],['optimized.log','finite_d02.log','finite_extended.log','power_new.log']),
'ancillary.py':(None,'Independent exact hash checks, endpoint and monotone-tail constants and joins; local comparison diagnostics',
                ['verify.py','d02_cert.py'],[])}
evidence={}
for n,(log,covered,scripts,inputs) in jobs.items():
    st=int((Q/(n+'.status')).read_text()); assert st==0
    a=sha(Q/(n+'.stdout')); b=sha(Q/(n+'.stderr'))
    assert (Q/(n+'.stderr')).stat().st_size==0
    eq=sha(A/log)==a if log else None
    if eq is False:
        assert n=='bridge.py' and sorted((Q/(n+'.stdout')).read_bytes().splitlines())==sorted((A/log).read_bytes().splitlines()),(n,log)
    cmd=['/usr/bin/python3.10',*n.replace('.py--','.py --').split()]
    if n=='ancillary.py':cmd=['/usr/bin/python3.10','/work/submission/ancillary.py']
    evidence[n]=dict(command=cmd,cwd=str(A),shell='/bin/bash (non-login)',env={'LC_ALL':'C','PYTHONDONTWRITEBYTECODE':'1',**({'PYTHONPATH':str(A)} if n=='ancillary.py' else {})},
        status=st,covered=covered,source_dependencies={p:by[p]['sha256'] for p in scripts},
        receipt_inputs={p:by[p]['sha256'] for p in inputs},
        stdout={'file':n+'.stdout','sha256':a},stderr={'file':n+'.stderr','sha256':b},
        candidate_log=log,byte_equal_to_candidate_log=eq)
evidence['bridge.py']['additional']={
  'build':['/usr/bin/gcc','-std=c11','-O3','/work/c008/bridge.c','-o','/work/bridge'],
  'run':['/work/bridge'],
  'stdout_note':'Same exact lines in different order due to redirected Python stdout buffering; C result line and counts identical.',
  'generated_stdin':{'path':'/work/bridge.logs','records':61642,'sha256':sha('/work/bridge.logs')},
  'binary_sha256':sha('/work/bridge')}
evidence['ancillary.py']['source_dependencies']['ancillary.py']=sha(Q/'ancillary.py')
dump('evidence.json',dict(replays=evidence, restore_command=['/usr/bin/python3.10','/task/RESTORE_CANDIDATE.py','--out',str(A)],
   build_runtime='Python 3.10.12 / libmpdec 2.5.1; GCC 11.4.0; x86_64 glibc 2.35; ordinary assertions and interval arithmetic',
   failures_and_limits=['Initial cwd command: ls absent, exit 127; readability confirmed with Bash tests.',
         'No PDF renderer executable; used source text of the pinned originals at physical LF and PDF page locators.',
         'Did not replay inherited published long prime and zeta computations; retain literature trust.',
         'No formal project supplied. Published finite computations are not certified C execution.',
         'Author failed stronger P6 join and two bounded gap targets, weighted .057 at 60m, and .3 at 912559.997; not counterexamples.']))

SUP='supported_at_stated_trust_tier'; BASE='baseline_retained'; EQ='equivalent_or_weaker'; FALSE='false_with_specific_counterexample'
V='Ordinary source/formula readback; any numerical obligations replayed as identified. Lean/Blueprint/kernel/PV not checked or claimed.'
trust='Original named result and published computation trust where used; standard arithmetic/analysis and ordinary source replay, not formal verification.'
c0=['OpenAIQRH Thm.1.1 p.4 LF255–262; Part II (15.9) p.107 LF8102–8108 and p.197 LF14658–14668',
    'PlattTrudgian2021 Lemma 2 p.4 LF236–246',
    'FKS Thm.3.2 p.8 LF631–642']
density=c0+['PlattTrudgianFiniteRH Thm.1 p.2 LF48–49',
            'FKS Cor.2.9 pp.7–8 LF586–608 and Table 8 p.26 LF3138–3258; Thm.2.7 p.7 LF520–527 (not used with table delta)']
primitive=['Dusart (2.1) pp.3–4 LF171–189; Thm.5.7 p.18 LF1552–1583',
           'FKS Lemma 2.1/Remark 2.2 pp.4–5 LF272–313 and Table 1 p.5 LF327–345',
           'CH2 Appendix B.1 p.43 LF6133–6143',
           'PlattTrudgianFiniteRH Thm.1 p.2 LF48–49']
local=['CH2 Cor.1.2–1.3 p.3 LF193–239; Lemma 4.2 pp.13–14 LF1666–1668; Lemma 9.2 p.35 LF5216–5223; Cor.9.3 p.36 LF5336–5363',
       'Dusart Thm.4.2 p.11 LF959–1010, Prop.4.3 p.12 LF1049–1056, Cor.4.5 p.13 LF1129–1130',
       'PlattTrudgianFiniteRH Cor.1 p.4 LF138–150']
pv=['DudekPlatt2015 p.8 LF561–562 (computed pi<li only); PlattTrudgian2021 Lemma 6 p.9 LF801–805 and Cor.2 p.3 LF126–135']
norm=['Dusart Theorems 5.6–5.9 pp.17–20 LF1476–1502,1552–1583,1630–1661']
old=load(A/'D01_M_REVIEW_review.json')
fl=load(A/'OWN_D01_VALIDATED_FLOOR.json')
floor={k for v in fl['validated_claim_ids_by_family'].values() for k in v}
excluded={r['claim_id']:r['scope'] for r in fl['excluded_history_or_source_objects']}
assert len(floor)==199 and len(excluded)==2
claims=[]
rewritten_locators=set()
for r in old['claims']:
    k=r['claim_id']; name=r['written_source']['original_name']
    def convert(s,read=False):
        a=s['physical_LF']; b=s.get('physical_LF_end_inclusive',a); n=s['original_name']
        new=ref(n,a,b,read=read); assert new['sha256']==s['sha256']
        if 'locked_readback' in s: assert '\n'.join(lines(n)[a-1:b])==s['locked_readback'], (n,a,b)
        return new
    written=convert(r['written_source'],True)
    impl=[convert(s) for s in r['implemented_formula_sources']]
    baselines={'R-bridge-original','R-original-integer','R-original-3915','R-original-9658','M-Dusart-P','M-Dusart-Q','M-Dusart-E1','M-Dusart-weighted'}
    weaker=k.startswith(('C-equivalent','C-B6','R-D01-','M-direct-'))
    stat=FALSE if k in excluded else BASE if k in baselines else EQ if weaker else SUP
    floor_note='Retained B0 proof; D01 is entailed by B0; D02 not needed for this branch.'
    u=False; where=None
    if k.startswith(('R-D01-','M-direct-')):
        u='D01 (historical, redundant)'; where='Raw direct psi error in local and absolute integrals, not the cap-based density optimum.'
    elif k.startswith('C-B6'):
        u='D01 in the B6 premise-substitution direction'; where='Mellin continuation; conversely the capped spectrum gives the exact D01 inequality.'
    elif k.startswith('C-equivalent'):
        where='B0 already proves exact D01; replacing it everywhere leaves the entire lawful envelope unchanged.'
    file_receipts=['ancillary.py' if q=='audit_aux.replay' else 'verify.py--endpoint' if q=='verify.replay' else q.replace('.replay','.py') for q in r['actual_verification_receipts']]
    assert all(q in evidence for q in file_receipts)
    loc=[s.replace('LF1132–1133','LF1129–1130').replace('LF1479–1505,1555–1586,1633–1664','LF1476–1502,1552–1583,1637–1661') for s in r['source_locators']]
    gap=None
    if k=='R-real-original-boundary':
        gap='Quoted, not adopted: real x=38358837682.1 has R in (-7974585.083,-7974585.082).'
    if k=='M-old-theta-scope-false':
        gap='Withdrawn: at L=17, integral of u_theta is at most -0.00036611 < -J1(17), where J1(17)<0.000040777.'
    notes=r['derivation_check'] # identity aid checked against the present proof; review.md gives independent derivation.
    if k.startswith('R-old-tail-'):
        written=ref(name,86,90,True)
    if k.startswith('R-deep-tail-'):
        written=ref(name,50,57,True)
    numerical=list(r['numerical_obligations'])
    if k=='R-original-integer':
        notes='Use the computed exact new real ray, which implies the integer restriction, independently of the literal displayed false real lower boundary.'
    if k=='M-old-polynomial-dominance':
        notes='Separate floor and decreasing terms on capped intervals and use the full tail scaling derivative; 1.0001 conversion is uniform.'
    if k=='M-early-row-1000000':
        notes='Early run establishes the first-three maxima; for weighted .296 use weighted.py to 66m and .130 from exp(18), not the old .298 receipt criterion.'
    if k=='R-B0-join':
        raise AssertionError(k)
    claims.append(dict(claim_id=k,family=r['family'],written_source=written,exact_statement=r['exact_statement'],
         assumptions=r['assumptions'],full_domain=r['full_domain'],strictness=r['strictness'],real_or_integer=r['real_or_integer'],
         baseline_comparison=floor_note,source_locators=loc,
         derivation_check=notes+' Independent assessment in review.md §§1–3.',
         numerical_obligations=numerical,implemented_formula_sources=impl,
         actual_verification_receipts=file_receipts,retained_valid_branches=r['retained_valid_branches'],
         M_status=stat,precise_gap_or_counterexample=gap,propagation={'input_used':u,'where_it_changes_proof':where,'matched_comparison':floor_note},
         V_status=V,remaining_trust=trust,current_affirmative_branch=k in floor,history_scope=excluded.get(k)))
assert set(r['claim_id'] for r in claims)==floor|set(excluded)
def add(k,f,n,i,j,stmt,dom,check, *, l=None, code=(), receipts=(), use=False, direct=False,
        cmp=None, status=SUP, strict='As stated; strict numeric inequalities on closed domains otherwise as in formula.', refs=()):
    written=ref(n,i,j,read=True)
    impl=[ref(*q) for q in code]
    if l is None:l=[]
    assert all(q in evidence for q in receipts)
    base=cmp or ('Retained improved B0-only consequence (and hence B0+D01 and B0+D02).' if not use
                 else 'D01 adds nothing to B0. D02 comparison to the stated B0 within-method certificate, not a blind search or strict deductive separation.')
    where=None if not use else ('Direct t≥200 use (and checked shifted argument where applicable)' if direct
                               else 'D02→cap 27/32; continuous density endpoint and/or signed high-zero primitive use exp(−5t/32) rather than exp(−t/8).')
    claims.append(dict(claim_id=k,family=f,written_source=written,exact_statement=stmt,
        assumptions=('B0 (cumulative original results, no full RH)' + (' + exact D02' if use else '')),
        full_domain=dom,strictness=strict,real_or_integer='Real analytic variables including noninteger x and boundary points unless excluded; integer prime/order indices.',
        baseline_comparison=base,source_locators=l,derivation_check=check,
        numerical_obligations=[evidence[q]['covered'] for q in receipts],
        implemented_formula_sources=impl,actual_verification_receipts=list(receipts),
        retained_valid_branches=list(refs),M_status=status,precise_gap_or_counterexample=None,
        propagation={'input_used':('D02' if use else False),'where_it_changes_proof':where,'matched_comparison':base},
        V_status=V,remaining_trust=trust,current_affirmative_branch=True))

AN='d02_analysis.md'; RG='d02_gap.md'; MG='d02_mertens.md'; DC='d02_cert.py'; RUN='run_d02.py'
RR='Ramanujan'; MM='Mertens'
a_code=((DC,6,64),(DC,88,107))
for fam in (RR,MM):
    add('D2-zeta-'+fam,fam,AN,3,15,'Exact D02 implies beta≤27/32 (and D01).',
        'All nontrivial zeros; raw psi assumption for real x≥exp(200).',
        'Euler-product Mellin identity and holomorphy; strict open-half-plane exclusion. D01 follows by comparing powers for x>1 and already follows from B0.',
        l=c0,use=True,cmp='Stronger available spectral cap than the B0 theorem states; no assertion of nonderivability from B0.',
        strict='Non-strict cap; equality permitted.')
    claims[-1]['propagation']['where_it_changes_proof']='Direct-supplied real-ray psi bound yields holomorphy to the right of 27/32.'
    add('D2-density-free-'+fam,fam,AN,17,21,'Density-free majorant .0142 t²e^{−(1−b)t}+2.091 t e^{−t/4}; cap b2 implies exact D02 over B6.',
        'Real t≥100 for majorant, t≥200 for the contractual estimate; b=b0 or b2.',
        'T=exp(t/4), count both ordinate signs and compare the residual scaled decreasing ratio at 200.',
        code=((DC,48,60),(DC,88,96)),l=c0,receipts=(RUN,'ancillary.py'),
        cmp='Uses the chosen zeta cap as premise; does not use FKS density or assume D02 in the reverse direction. B6 excludes OpenAIQRH.',
        strict='Non-strict local envelope; strict improvement on 1/64 coefficient at t≥200.')
    claims[-1]['assumptions']='B6 plus chosen zeta cap, or B0/B0+D02 respectively to obtain b0/b2.'
    add('D2-density-mixture-'+fam,fam,AN,23,45,'Continuous log-linear w majorizes the inverse-ordinate tail; D_b(t;s0,k) of (A) bounds |u(t)|.',
        's in [.75,b], b=7/8 or 27/32, exact knots and listed k,s0; real t≥100.',
        'Taylor upper at exact knots, Hölder within bins; nonnegative cumulative multipliers, factor 2 and boundary term. Derivative test and strictly improved matched difference are in review.md §1.',
        l=density,code=a_code,receipts=(RUN,),use=True,refs=('C-density-weights-'+fam,))
    claims[-1]['assumptions']='B0 (b0) or B0+D02 (b2). FKS Cor.2.9 as stated.'
    add('D2-signed-primitives-'+fam,fam,AN,50,61,'Signed ψ kernel interval k(t)[−Z_b−2e^{−t},Z_b], Z_b=.0462e^{−t/2}+4e−12 e^{−(1−b)t}; |B2|≤Z_b/14+2e^{−t}.',
        'Real t≥1, k=1,K; both cap choices; zero-weight identity at t→0+.',
        'L² on compact intervals; Laplace divisor and summable reciprocal-square weights. The original weighted prime-sum limit fixes primitive at zero and hence low weight.',
        code=((DC,67,75),(DC,255,260),('spectral_repair.py',6,15)),l=primitive+c0,
        receipts=('spectral_repair.py',RUN),use=True,
        cmp='Low .0462 constant is B0; D02 only affects high-scale term. B0+D01=B0.')
    claims[-1]['assumptions']='B0 (b0) or B0+D02 (b2); does not use FKS Cor.2.9.'

r_fin=((DC,142,194),(RUN,17,30),('verify.py',55,65),('verify.py',124,130))
r_fin_src=local+primitive+density+pv
r_tail=((DC,108,139),('optimize_d02.py',3,22),(RUN,31,38))
r_tail_src=local+primitive+density
r_cell='Real closed cells; see review.md §2: main term or reserve at right endpoint, both shifted and unshifted interval errors bounded over each entire cell.'
for i,a,b,q in [(15,'36.528','∞','.001'),(16,'36.531','∞','.002'),
                (17,'36.737','∞','.1'),(18,'36.890','∞','.168'),
                (19,'36.98','37.5','.207'),(20,'39.912','∞','.4'),
                (21,'40','∞','.431'),(22,'42.471','∞','1'),
                (23,'45','76','1.212'),(24,'46','68','1.241'),
                (25,'47','63','1.264'),(26,'48','55','1.308'),
                (27,'49','52','1.321'),(28,'59','73','1.220'),(29,'75','100','1.152')]:
    cmp={18:'B0 improves old .164 at 36.98 to .168, and extends the new .168 ray back to 36.890.',
         20:'B0-only .4 threshold 39.912 replaces 39.94 as sufficient threshold.',
         21:'B0 .431 vs .425, same onset 40.',
         22:'B0 unit ray log-onset 42.471 vs old 42.482 (older 42.8); no D02 gain.'}.get(i)
    add('D2-R-fixed-'+str(i),RR,RG,i,i,'Y(L)>'+q,f'L∈[{a},{b}'+(')' if b=='∞' else ']'),
        r_cell+(' Join later fixed-margin pieces then the old unit ray.' if b=='∞' else ''),
        l=r_fin_src,code=r_fin,receipts=(RUN,'verify.py--endpoint') if b=='∞' else (RUN,),cmp=cmp,
        refs=('R-open-ray','R-old-margin-13'))
for id,a,b,q,use,cmp in [
    ('old-175','100','175','1.0820',False,'Matched D02 strengthens to 1.0838.'),
    ('new-175','100','175','1.0838',True,'B0 same interval has 1.0820.'),
    ('old-1721','100','172.1','1.0837',False,'B0 sufficient right endpoint; D02 175.3.'),
    ('new-1753','100','175.3','1.0837',True,'D02 extends matched 1.0837 target versus B0 endpoint 172.1.'),
    ('new-190','175','190','1.0777',True,'New D02 closed interval, use maxima with applicable old branches.')]:
    add('D2-R-bounded-'+id,RR,RG,33,33,'Y(L)>'+q,f'L∈[{a},{b}]',
        r_cell+' Local D02 power can beat CH2 near 169, through the new cap; raw local bound not used.',
        l=r_fin_src,code=r_fin,receipts=(RUN,),use=use,cmp=cmp)
for n,a,b in [(5,'47.02','∞'),(6,'52.1','125'),(7,'57.5','91'),(8,'64','66')]:
    add('D2-R-island-'+str(n),RR,RG,39,42,f'Y>P_{n}(L)',f'L∈[{a},{b}'+(')' if b=='∞' else ']'),
        r_cell+(' Closed [47.02,58],[58,100],[100,190] then B0 P5 tail from 188.83.' if n==5 else ''),
        l=r_fin_src,code=r_fin+r_tail if n==5 else r_fin,receipts=(RUN,),cmp=
        ('The B0 connected P5 ray precedes both P5 spectral-only onsets.' if n==5 else 'Finite B0 strengthening; no extrapolation into remaining uncovered P6 region.'))
for i,n,eta,a0,a2 in [(46,4,'0','160.19','142.34'),(47,5,'0','188.83','163.33'),
    (48,5,'.5','195.43','168.37'),(49,5,'.9','208.68','178.34'),(50,5,'.99','218.34','185.19'),
    (51,6,'0','220.37','186.54'),(52,7,'0','253.57','211.07'),(53,8,'0','287.78','236.44'),
    (54,10,'0','357.97','288.63'),(55,12,'0','429.41','341.9'),(56,14,'0','501.51','395.74'),
    (57,16,'0','573.97','449.92'),(58,17,'0','610.3','477.09'),(59,20,'0','719.55','558.84'),
    (60,24,'0','865.62','668.21'),(61,32,'0','1158.51','887.63'),(62,48,'0','1745.69','1327.75'),
    (63,64,'0','2333.71','1768.62'),(64,100,'0','3658.04','2761.7')]:
    for use,a in ((False,a0),(True,a2)):
        add(f'D2-R-tail-{i}-B{2 if use else 0}',RR,RG,i,i,f'Y>P_{n}'+(f'+({eta})C_{n+1}L^{{{3-n}}}' if eta!='0' else ''),
            f'Real L≥{a}, closed.',
            'Polynomial reserve through m−1 dominates signed-tail-absorbed loss. Positive exponential mixtures and both shifted monomial derivatives preserved on the ray.',
            l=r_tail_src,code=r_tail,receipts=(RUN,'optimize_d02.py'),use=use,
            cmp=f'Matched spectral-tail thresholds {a0} (B0) vs {a2} (B0+D02); B0+D01 ties B0. This is not the best connected threshold for P4/P5.',
            refs=('D2-R-island-5','R-arbitrary-order','R-open-ray'))
for typ,i,j,table in [
    ('free',66,66,[(12,420),(17,561),(32,982),(64,1874),(100,2875)]),
    ('raw',117,123,[(6,253),(12,421),(17,562),(32,983),(64,1875),(100,2876)])]:
    for n,a in table:
        add(f'D2-R-{typ}-{n}',RR,RG,i,j,f'Y>P_{n} with no FKS Cor.2.9 in this proof.',f'Every real L≥{a}.',
            'Same factorial reserves and shifted tests. Density-free truncation with the new cap, or absolute raw D02 from 200 with EC integral prefix and no old primitive.',
            l=local+primitive+c0,code=r_tail+((RUN,9,12),),receipts=(RUN,),use=True,direct=typ=='raw',
            cmp='Weaker/later than the D02 density-dependent row, but avoids the FKS density estimate; does not annul old domains.')
add('D2-R-prefix',RR,RG,70,95,'Second-primitive forward integral prefix W_pi and signed corrections U_pi and V_pi for Li2.',
    'Real L≥7 for prefix; each local error on its stated ray/finite-height hypothesis.',
    'Integrate by parts twice with both lower boundary contributions, compare logarithmic derivatives and residual; subtract lower costs on the upper side only.',
    l=r_fin_src,code=((DC,67,75),(DC,88,95),(DC,142,167)),receipts=(RUN,))
claims[-1]['assumptions']='B0 (b0) or B0+D02 (b2); same formula with respective cap.'
claims[-1]['propagation']['where_it_changes_proof']='If specialized to b2, the high-zero term in the integral is faster; lowering low weight and using second primitive are already B0.'
add('D2-R-G18-Signed',RR,RG,97,102,'General shifted lower bound (G), improved signed errors and reserves through coefficient 26.',
    'Real L≥36 with applicable upper/lower estimates at L and L−1; 4≤n≤17 for reserve.',
    'Square upper error of the unshifted nonnegative count; lower the shifted count with L/(L−1); exact coefficient absorption.',
    l=r_fin_src,code=r_fin,receipts=(RUN,'verify.py--endpoint'),refs=('R-G18','R-old-profile'))
add('D2-R-arbitrary-premium',RR,RG,106,115,'For each fixed integer n≥4 and 0≤η<1, eventually Y>P_n+η C_{n+1}L^{3−n}, with finite tests for sufficient onset.',
    'Real closed ray after some a fixed per n,η; shifted argument at least max(100,b_m).',
    'm=n+4 works eventually; reserve polynomial stays positive and scaled loss tends to zero. This is mathematical eventuality, not unlimited software performance.',
    l=r_tail_src,code=r_tail,receipts=('optimize_d02.py',RUN),cmp='Arbitrary fixed n already B0; D02 moves certified endpoints rather than the quantifier.')
add('D2-R-pointwise-Li',RR,RG,125,127,'Exact-Li branch for Y using (G) with B and signed Li2 errors, including optional shifted literal pi−li interval.',
    'L≥36; original finite or late domain restrictions checked separately at both x and x/e.',
    'Exact normalized Li2, add constant li(2) before normalizing original error intervals; take maxima of applicable profiles.',
    l=r_fin_src,code=((DC,70,75),(DC,142,180)),cmp='Pointwise refinement; do not replace other valid lower branches. No separate executable exact-Li evaluation needed for bound.')
for id,b,z,coeff in [('B0',0,'1/8','.060'),('D02-same',2,'1/8','.00161'),('D02-fast',2,'5/32','.831')]:
    add('D2-R-Li-loss-'+id,RR,RG,127,131,f'|Y−Y_Li|<{coeff}L^4 exp(−{z}L).','Real L≥201.',
        '3.24 C_a bound using A_pi+B<2.05 and scaled shift penalty; isolate caps and both monotone exponent branches.',
        l=r_tail_src,code=((DC,47,75),(RUN,14,16),(RUN,39,42)),receipts=(RUN,),use=b==2,
        cmp='Fixed onset 201; compare .060 vs .00161 at rate 1/8; .831 at 5/32 is an additional faster-rate tradeoff.')
add('D2-R-Li-parametric',RR,RG,127,131,'|Y−Y_Li|<3.24 C_a L^4e^{-zL} with C_a=e^{z(a−1)}E_pi(a−1).',
    'a≥101, L≥a, 0≤z≤1−b and specified monomial tests, applicable spectral parameters.',
    'Termwise scaling and two-sided exact-Li algebra with shifted factor; 3.24 strict.',
    l=r_tail_src,code=((DC,47,75),(RUN,14,16),(RUN,39,42)),receipts=(RUN,))
claims[-1]['assumptions']='B0 (b0) or B0+D02 (b2), density trust.'
add('D2-R-rate-converse',RR,RG,133,141,'Either input context: eventual one-sided Y≥Y_Li−C L^j e^{−rL} implies beta≤1−r.',
    'r∈[1/8,5/32], all sufficiently large real L; cap for all nontrivial zeta zeros.',
    'Positive-part contraction, Mellin differentiated identity, nonnegative-transform Taylor argument, pole cancellation at 1, identity theorem.',
    l=c0,cmp='A hypothetical matching B0 new rate would prove the exclusion. No assertion that it cannot.')
m_code=((DC,67,87),(DC,195,268),(RUN,44,69))
m_l=norm+local+primitive+density
m_chk='Same-signed magnitude enclosure for weighted and L times log/reciprocal errors; e^d−1≤d exp(d) for products. Both scaled W and unscaled exponentiation factor verified by analytic derivative or directed finite-band tests.'
m_power_fin=(('power_new.py',8,65),(RUN,99,131))
m_poly_fin=(('finite_d02.py',8,77),(RUN,99,119))
def mscale(z,p=None,w=None,extra=''):
    if p is None:return f'All four errors <{w or extra} in common scale z={z} (weighted exp(zL); first three L exp(zL)).'
    if w is None:w=p
    return f'Rate {z}: first three scaled errors <{p}; weighted scaled error <{w}.'
def mcommon(k,i,j,a,z,K,use,cmp=None):
    add('D2-M-'+k,MM,MG,i,j,mscale(z,w=K),f'Real L≥{a}.',m_chk,
        l=m_l,code=m_code,receipts=(RUN,),use=use,cmp=cmp,
        refs=('M-new-min','M-new-power-14','M-new-poly-fallback'))
mcommon('base-power-14',14,14,'14','1/8','.01908',False)
for z,K in [('1/8','.01111'),('.130','.01191'),('.135','.01278'),('.140','.01920'),
            ('.145','.04461'),('.150','.10363'),('5/32','.2973')]:
    mcommon('power-14-'+z,16,20,'14',z,K,True,cmp='Same L≥14: compare with B0 .01908 at rate 1/8; preserve tradeoffs and crossover branches.')
for a,K in [('13','.01677'),('13.5','.01363'),('15','.00741'),('16','.00498'),('17','.003358'),('18','.002275'),('19.03','.001537')]:
    mcommon('onset-'+a,22,22,a,'1/8',K,True)
for i,a,K0,K2,Ks in [
 (26,170,None,'.29473','.001453'),(27,180,None,'.27903','.001007'),(28,200,'.018221','.25594','.000495'),
 (29,250,'.015899','.22294','.00009021'),(30,300,'.014652','.20535','.00001742'),
 (31,500,'.012654','.17733','2.904e-8'),(32,1000,'.011454','.16057','4.305e-15'),
 (33,3000,'.010761','.15079','2.906e-42'),(34,30000,'.010476','.146743',None),
 (35,1000000,'.010446','.146320',None)]:
    for label,K,use,z in [('old',K0,False,'1/8'),('same',Ks,True,'1/8'),('fast',K2,True,'5/32')]:
        if K is not None:
            mcommon(f'tail-{a}-{label}',i,i,a,z,K,use,
                    cmp=f'Matched closed onset {a}; B0 {K0 or "no separately optimized table entry"} at rate 1/8; D02 {Ks or "exponential conversion of fast-rate coefficient"} at rate 1/8 and {K2} at 5/32.')
    if Ks is None:
        mcommon(f'tail-{a}-converted',i,i,a,'1/8',f'{K2} exp(−{a}/32)',True,
                cmp='Convert rate by decreasing ratio exp(−L/32); also keep faster pointwise branch.')
for a,p,w in [(70000,'.01946','.02138'),(100000,'.01908','.02080'),(104000,'.01908','.01908')]:
    add(f'D2-M-base-bridge-{a}',MM,MG,14,14,mscale('1/8',p,w),f'Real x≥{a}.',
        'Outward finite power cells with strict maxima, joined to B0 L≥14 .01908 tail through overlapping T.',
        l=m_l,code=m_code+m_power_fin,receipts=(RUN,'power_new.py'))
for i,a,p,w in [
 (43,100000,'.01895','.02080'),(44,104000,'.01724','.01876'),(45,180000,'.01469','.01598'),
 (46,250000,'.01363','.01469'),(47,400000,'.01104','.012001'),(48,500000,'.01020','.01103'),
 (49,700000,'.00849','.00919'),(50,1000000,'.00807','.00870'),(51,1200000,'.00753','.00816'),
 (52,1500000,'.00737','.00793'),(53,2000000,'.00608','.00654'),(54,2500000,'.005752','.006141'),
 (55,4000000,'.004622','.004957'),(56,5000000,'.004340','.004675'),(57,6000000,'.004047','.004335'),
 (58,8000000,'.003549','.003809'),(59,10000000,'.003456','.003676'),(60,15000000,'.003358','.003358'),
 (61,40000000,'.002275','.002275'),(62,150000000,'.001537','.001537')]:
    late=i>=61
    add(f'D2-M-power-bridge-{a}',MM,MG,i,i,mscale('1/8',p,w),f'Real x≥{a}.',
        ('Use overlapping finite power cells through composite 24154954 and D02 L≥17 analytic ray.' if not late else
         'Finite polynomial cells through exp(18) or exp(19.03) rescaled at the right endpoint by increasing exp(L/8)/L², then closed D02 power ray.'),
        l=m_l,code=m_code+(m_poly_fin+((RUN,132,136),) if late else m_power_fin),
        receipts=(RUN,'finite_d02.py' if i==61 else 'finite_d02.py--extended' if i==62 else 'power_new.py'),use=True,
        cmp={43:'At 100000 compare B0 .01908/.02080: only first three improve in these rows.',
             44:'At 104000 compare B0 .01908 for both groups against D02 .01724 and .01876.',
             47:'First three <.01111 from 400000 instead of sufficient exp(14) within the D02 envelope.',
             48:'Weighted <.01111 from 500000 instead of sufficient exp(14) within the D02 envelope.'}.get(i))
add('D2-M-fast-dominance',MM,MG,37,37,'New .29473 at 5/32 beats old uniform rate-1/8 power entries on all their matched rays after L=170; weighted below c; polynomial-scale below .043.',
    'L≥170 intersected with each compared domain.', 'Ratio .29473e^{−L/32}/K decreases from value <1; .29473e^{−5L/32} and its polynomial rescaling also decrease.',
    l=m_l,code=((RUN,70,73),),receipts=(RUN,),use=True,
    cmp='Comparison of explicit uniform branches and indicated fixed targets, not dominance of an unknown best B0 theorem.')
for id,stmt,dom,use in [
 ('fast-v-base','Rate .15625, .2973 crosses rate .125, .01908 at 87<L<88.','Matched domain L≥14.',True),
 ('fast-v-new','Rate .15625, .2973 crosses rate .125, .001537 at 168.47<L<168.48.','Matched earlier finite onset 150000000 or the log 19.03 onset.',True),
 ('fast-v-Dusart-first','Rate .15625, .2973 crosses .2 polynomial at 53<L<54.','Actual original matched ray for each of products and E1.',True),
 ('fast-v-Dusart-weighted','Rate .15625, .2973 crosses .3 polynomial at 50<L<51.','Actual original weighted ray.',True),
 ('base-v-Dusart-first','Rate .125, .01908 crosses .2 polynomial at 40<L<41.','Actual original matched ray for the products and E1.',False),
 ('base-v-Dusart-weighted','Rate .125, .01908 crosses .3 polynomial at 34<L<35.','Actual original weighted ray.',False)]:
    add('D2-M-cross-'+id,MM,MG,66,66,stmt,dom,'Uniqueness from monotone ratio, or L²exp(−zL) increasing to 2/z then decreasing and above target at the matched onset. Keep both curves, not the worse one.',
        l=norm,code=((RUN,74,82),),receipts=(RUN,),use=use,
        cmp='Matched branch strength changes at the unique crossing; not a global minimum claim.')

for a,stmt in [('2278381.72','Both products strict coefficient .2'),('2278381.75','Both products strict coefficient .199997'),
               ('2278382','Both products strict coefficient .199973'),('2278382.12','First three strict coefficient .2'),
               ('2278383','Both products .199879 and reciprocal sum .199917'),
               ('912559.9975','Weighted strict coefficient .3'),('912560','Weighted strict coefficient .29999946')]:
    add(f'D2-M-fixed-{a}',MM,MG,70,70,stmt+' in polynomial scales.',
        f'Real x≥{a}, closed.', 'Directed finite onset-clipped cells to 66m, then analytic .079 from exp(18); signs and exponentiation verified.',
        l=local+norm,code=m_poly_fin+((DC,261,268),),receipts=('finite_d02.py',RUN,),
        cmp='B0-only earlier onset/stronger fixed coefficient alongside original Dusart and old certified branches.')
for a,K in [('17','.117'),('17.3','.104'),('18','.079'),('18.8','.057'),('19.25','.047'),('19.5','.043')]:
    add(f'D2-M-poly-tail-{a}',MM,MG,72,72,f'Common strict coefficient {K} in L³,L³,L³,L² scales.',
        f'Real L≥{a}.',m_chk+' Use B=230 split and density-free tail, with fourth power as largest scaled log-degree.',
        l=norm+local+primitive+c0,code=m_code,receipts=(RUN,),cmp='New B0-only profile; holds even without FKS Cor.2.9.')

for i,a,p,w in [(76,15000000,'.09574','.10246'),(77,18000000,'.09394','.10059'),
                (78,20000000,'.08875','.09479'),(79,25000000,'.08810','.09334'),
                (80,40000000,'.07019','.07483'),(81,50000000,'.05620','.06036'),
                (82,60000000,'.05609','.05910'),(83,150000000,'.04467','.04709'),
                (84,200000000,'.043','.043')]:
    add(f'D2-M-poly-bridge-{a}',MM,MG,i,i,f'Polynomial-scale first three <{p} and weighted <{w}.',f'Real x≥{a}.',
        'Directed finite clipped cells to '+('300m, join .043 from exp(19.5).' if i>=80 else '66m, join .079 from exp(18).'),
        l=norm+local+primitive+c0,code=m_poly_fin+m_code,receipts=(RUN,'finite_d02.py--extended' if i>=80 else 'finite_d02.py'))
add('D2-M-exact-transforms',MM,MG,90,101,'Exact D_Q=u/L−∫uK+U, E_1=D_Q+T_0, Elog=u−∫u+V and joint tails inequalities.',
    'Real L>0; spectral refinement at L≥1; all tail sums p^m>x.', 'Stieltjes partial summation and correct normalizations; no θ-tail double counting.',
    l=norm+primitive,refs=('M-psi-logQ','M-theta-transform','M-A-bridge'))
add('D2-M-early-prime-powers',MM,MG,103,115,'θ≤x up to exp(29), θ≤1.000058x globally; Vplus with separate square/cube budgets and 3.46 e^{−3L/4}.',
    'θ from real x≥1; Vplus for 10≤L≤58; early W for 10≤L≤29.',
    'Prime-by-prime ≤121, signed CH2 and Dusart beyond; boundary term and both integral portions in V_j. Use θ upper for higher powers and Jensen-free direct tail.',
    l=norm+local,code=((DC,195,218),(DC,244,260)),receipts=(RUN,))
add('D2-M-parametric',MM,MG,117,123,'Cut-and-join uniform sufficient constant from early signed, middle finite RH/CH2 floor, late spectral branch.',
    'a≥10, split ≥max(a,100), 0≤z≤1−b, and derivative tests hold at late split.',
    'Scale decreasing monomials at the left and increasing finite constants at the right, with common product exponentiation factor. Bounds valid separately at shared endpoints.',
    l=m_l,code=m_code,receipts=(RUN,),cmp='Retain old W and Wstar as competing branches, not a mandatory piecewise switch.')
claims[-1]['assumptions']='B0 (old cap) or B0+D02 (new cap).'
for b,lo,hi,z in [(0,'.01044','.01045','1/8'),(2,'.14630','.14631','5/32')]:
    add(f'D2-M-limit-B{b}',MM,MG,125,125,f'Uniform scaled certificate limit at rate {z} is 2w(b)+4e−12, in ({lo},{hi}).',
        'L→∞ with fixed applicable spectral parameters.', 'Dominated convergence on the positive continuous mixture and lower-rate rapid terms; surviving endpoint and primitive only.',
        l=m_l,code=((DC,33,64),(DC,80,87),(RUN,68,69)),receipts=(RUN,),use=b==2,
        cmp='Limiting coefficient of this majorant, not an optimal or sharp error lower bound.')
for i,z,a,K,raw in [('free-square','5/32',200,'.01421 L²',False),('free-eighth','1/8',600,'.000037',False),
                    ('free-point14','.14',1000,'.00125',False),('raw','5/32',200,None,True)]:
    text=mscale(z,w=K) if K else mscale(z,'.120 L²','.123 L²')
    add('D2-M-'+i,MM,MG,127,131,text,f'Real L≥{a}.',
        'Use explicit absolute local and tail integrals for raw D02, or density-free truncation plus signed primitive, then decreasing ratios after L² scaling and actual product exponentiation.',
        l=local+primitive+c0+norm,code=((DC,48,60),(DC,67,87),(RUN,83,98)),receipts=(RUN,),
        use=True,direct=raw,cmp='Still improves eventual B0 pure rate in indicated domains; log-square loss at rate 5/32. Does not use FKS Cor.2.9.')
add('D2-M-direct-dominance',MM,MG,131,131,'Raw direct .120L²/.123L² at 5/32 beats all retained old uniform pure powers after L=500; raw local D02 worse than old density local bound at 200.',
    'L≥500 for first comparison, L=200 for second.', 'Use .123 L² e^(−L/32) decreasing there, strict endpoint comparison; both are comparisons of certificates only.',
    l=norm+c0,code=((RUN,91,98),),receipts=(RUN,),use=True,direct=True)
add('D2-M-finite-normalizers',MM,MG,135,141,'Tighter gamma, M and B3 outward brackets; whole polynomial finite cells with separate product signed extrema.',
    'N of 66m; through 66m or 300m closed; finite active queries and end-inclusive prefix.',
    'Trapezoid error, Dusart theta-deviation Stieltjes costs, alternating geometric integration, monotone cell derivatives and directed clipping.',
    l=norm+local,code=m_poly_fin+(('smallprod.py',7,29),('weighted.py',5,21),(DC,205,207)),
    receipts=('finite_d02.py','finite_d02.py--extended',RUN))
add('D2-M-power-finite',MM,MG,135,143,'Outward finite power cells and nonoverlapping slab scale upper bounds; independent of D02.',
    'Listed query onsets through 24154954 including final composite point.', 'Separate finite arithmetic from input-dependent large L tail, with conservative right-end scale.',
    l=norm+local,code=m_power_fin+(('smallprod.py',7,29),('weighted.py',5,21)),receipts=('power_new.py',RUN))
for i,j,id,stmt,check in [
    (147,147,'local','Intersect local signed ψ and θ intervals, including shifted outputs of finite Möbius inversion.',
     'Test each shifted scale separately; subtract full prime-power range; correct CH2 shifted center and FKS row domains.'),
    (148,148,'kernels','ψ tail and θ shifted tail intersections, and weighted-ψ A identity and CH2 branch.',
     'Correct signed subtraction by full ∫qk; θ-only formulas have no power corrections; exact A Stieltjes bridge.'),
    (149,158,'powers','Signed Stieltjes prime-power tail refinement with two explicit convergent residual ceilings.',
     'Deviation boundary minus f(y)(theta(y)−y), decreasing weights, geometric split or convergent integer integral.'),
    (159,159,'relative','Separate product relative envelopes and signed-sum maximum, pointwise minimum keeping all finite/empty/original branches.',
     'Exponential monotonicity on interval, first/last jumps handled exactly, no unsupported extrapolation.')]:
    add('D2-M-envelope-'+id,MM,MG,i,j,stmt,'Real x>1 with each branch restricted to its own premise and domain.',
        check,l=m_l+['FKS Cor.1.4 p.2 LF140–143, 1.1–1.2 LF113–135, Tables 5–6 p.21ff LF2307,2581'],
        refs=('M-new-min','M-local-psi-min','M-J-shift-theta','M-relative'))
    claims[-1]['assumptions']='B0; intersect with additional D02 estimates only in B0+D02.'
add('D2-M-rate-converse',MM,MG,163,165,'A matching eventual O(e^{−rL}L^j) for ANY of P,Q,E1,Elog implies zeta cap 1−r.',
    'r∈[1/8,5/32], sufficiently large real L; cap for all nontrivial zeros.',
    'For products take log after relative convergence; remove smaller tails. Invert A/L−∫A/t², then solve B1′=−A−B1, preserving exponent, and use Mellin exclusion.',
    l=norm+primitive+c0,
    cmp='Matching rate from B0 would prove stronger zeta exclusion; no false deductive separation claimed.')

assert len(set(r['claim_id'] for r in claims))==len(claims)
assert all(r['M_status'] in {SUP,BASE,EQ,FALSE} for r in claims)
assess={}
for family,summary in [
    (RR,'Exact open sign ray and least strict integer onset preserved; strengthened B0 finite margins, P5 connected ray, P6–P8 finite islands, full retained larger-margin tradeoffs, D02 earlier spectral rays and matched exact-Li gains. No closed P6 bridge in the unsupplied middle interval.'),
    (MM,'Both product-relative errors and both sums supported with pointwise signed minima, B0 tighter finite/polynomial joins, and earlier and stronger D02 power envelopes, plus valid direct/density-free alternatives and crossed comparisons.')]:
    rows=[r for r in claims if r['family']==family]
    keep=[r['claim_id'] for r in rows if r['current_affirmative_branch']]
    assess[family]={'strongest_supported_portfolio':keep,'rejected_or_incomplete_claims':[r['claim_id'] for r in rows if r['M_status']==FALSE],
        'rejections_scope':'Quoted source or withdrawn history only; no active candidate branch rejected at the stated trust tier.',
        'remaining_assessment_work':[],'summary':summary}
# Separate locked text and executable readbacks (deduplicated by exact byte-LF span).
code_readbacks={}
for r in claims:
    for c in r['implemented_formula_sources']:
        name=c['original_name']; a=c['physical_LF']; b=c['physical_LF_end_inclusive']
        key=f'{name}:{a}-{b}'
        if key not in code_readbacks:
            code_readbacks[key]=ref(name,a,b,read=True)
        c['implementation_readback_key']=key
dump('implementation_readbacks.json',dict(origin='Immutable actual implemented formula/source; no Lean project',readbacks=code_readbacks))
# Publication checks: immutable receipts, all 201 restored history maps, separate new algorithm references.
dump('review.json',dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=ix['candidate_id'],input_stage='D02',
    assessment_complete=True,all_claims_inventoried=True,source_bibliography=sources,
    reviewed_source_hashes={**{r['packet_name']:r['sha256'] for r in by.values()},
      **{r[k]:r[k+'_sha256'] for r in sources for k in ('pdf','text')},
      **{p:sha(T/p) for p in ('INPUT_CONTRACT.json','SOURCE_INDEX.json','CANDIDATE_INDEX.json','OWN_HISTORY_DISCLOSURE.json')}},
    actual_verification_commands={p:e['command'] for p,e in evidence.items()},
    effort_description='Independent re-derivation/check of both proof chains and cells/rays; packet original source and code readback; 18 ordinary replay/ancillary commands with captured output. No controller token estimate.',
    evidence='evidence.json',source_checkpoint='checkpoint.md',implemented_formula_readback_artifact='implementation_readbacks.json',
    overview_declarations=[ref('candidate.md',3,9,True),ref('D01_README.md',3,19,True)],
    family_assessments=assess,claims=claims,
    no_other_arm_or_ranking_seen=True,new_core_math_salvage_performed=False,original_candidate_bytes_changed=False,
    own_history_used_as_premise=False,optional_formal_evidence='No paper-only paper-runtime Lean project; not checked / not claimed.'))
dump('STAGE_STATUS.json',dict(ready_for_review=True,
    families={f:{'status':SUP,'claim_files':['review.md','review.json']} for f in (RR,MM)},
    serious_attempts_documented=True))
print('claim ledger:',len(claims), Counter(r['M_status'] for r in claims))
