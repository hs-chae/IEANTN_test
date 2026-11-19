"""Build machine review inventory and evidence metadata from the immutable packet and replay receipts."""
import re,json,hashlib,sys
from pathlib import Path
D=Path(__file__).resolve().parent
T=Path('/task')
C=Path('/work/reviewcand')
def write(n,ob): (D/n).write_text(json.dumps(ob,indent=2,ensure_ascii=False)+'\n')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
index=json.loads((T/'CANDIDATE_INDEX.json').read_text())
refs={r['original_name']:r for r in index['candidate_files']}
src=json.loads((T/'SOURCE_INDEX.json').read_text())['sources']
rs=json.loads((D/'replay_status.json').read_text())
assert all(s==0 for a,s in rs)
details={
'verify':('count.py (endpoint); stdlib decimal/fractions/math','root and two counts at N/floor(N/e); G18 and Li anchor; old closed cells L=36.98–60 and bands through 77; old unit [60,163]; 9 monotone tails; density constants'),
'bridge':('verify.py for interval e/logs; bridge.c; GCC -std=c11 -O3; /work/bridge.logs','[38358837683,100000000000]; 2473381581 prime tests; left and truncated shifted counts'),
'general':('verify.py for ED and factorial arithmetic','orders 20,24,32,48,64 at 722,868,1161,1748,2336'),
'early':('verify.py interval primitives','[2,2278383]; gamma/M/B3 normalizers; all active clipped constant-prefix cells'),
'weighted':('early.py sieve, verify.py intervals; fixed-point logs; Dusart 4.2 .2/L² at 25000000','listed real onsets through 66000000, exact weighted scale on each cell'),
'smallprod':('early.py sieve, weighted.py fixed-point helpers, verify.py; Dusart 4.2 10/L³ from N=2278383','listed real onsets through 66000000, separate P/Q/E1'),
'mverify':('verify.py density and intervals; original constants','W band inequalities, .01970 + seven endpoints, .130/.2 whole-ray tests, crossings, early power joins'),
'tradeoff':('verify.py EC/closed cells/coefficient arithmetic','EC-only [60,269]; 6 D01 tails; two Mertens direct-use coefficients at L=200'),
'receipts':('early.log, smallprod.log, weighted.log, bridge.log (locked); also independently reran underlying scripts','Decimal comparisons of selected table rows, not standalone certificates'),
'spectral_repair':('verify.py; smallprod.log, weighted.log locked finite rows, matched independent replays','J weights, prime-power constants, W* bands, 7 late endpoints, density-free 230 test, crossings and theta-scope diagnostic'),
'power_bridge':('weighted.py, early.py, smallprod.py, verify.py; Dusart 4.2 .2/L² at N=5000000','listed onsets 50000–120000 through T=1202606, finite power scaling and four asserted tradeoffs'),
'gap_repair':('verify.py, spectral_repair.py (and its dependencies)','19 closed adaptive joins with prescribed PV flag and separate shifted arguments; 14 decimal tail onsets')}
times=[44.571705870330334,123.31399993784726,47.977249873802066,85.79244202375412,54.70528034679592,129.23044981248677,0.121518949046731,3.7881570365279913,0.017106249928474426,0.12476917542517185,6.0944221932441,1.3393723294138908]
receipts={}
for (a,s),t in zip(rs,times):
    k=Path(a[3]).stem
    log=C/(k+'.log'); o=D/(k+'.replay'); e=D/(k+'.stderr')
    same=(sha(o)==sha(log)) if log.exists() else None
    assert same is not False and e.stat().st_size==0
    receipts[k]=dict(argv=a,cwd=str(C),env={'LC_ALL':'C'},exit_status=s,elapsed_seconds=t,
        dependencies=details[k][0],covered_obligations=details[k][1],stdout=o.name,stdout_sha256=sha(o),
        stderr=e.name,stderr_sha256=sha(e),locked_log_match=same)
receipts['audit_aux']=dict(argv=['/usr/bin/python3.10','-B','audit_aux.py'],cwd=str(D),exit_status=int((D/'audit_aux.status').read_text()),
    dependencies='locked verify.py, count.py; /task indices; original PDFs and extracts; stdlib zlib',
    covered_obligations='all immutable file digests; explicit real-endpoint witness; floor of 10^11/e; extra .019 endpoint; fixed meshes and PDF stream checkpoints',
    stdout='audit_aux.replay',stdout_sha256=sha(D/'audit_aux.replay'),
    stderr='audit_aux.stderr',stderr_sha256=sha(D/'audit_aux.stderr'))
write('evidence.json',dict(restoration=['/usr/bin/python3.10','/task/RESTORE_CANDIDATE.py','--out','/work/reviewcand'],
    executor='non-login /bin/bash; Python 3.10.12, GCC 11.4.0; stdlib only for Python',
    bridge_compile=['/usr/bin/gcc','-std=c11','-O3','/work/reviewcand/bridge.c','-o','/work/bridge'],
    bridge_exec=['/work/bridge'],bridge_regenerable_files=[
        dict(path=str(p),size=p.stat().st_size,sha256=sha(p)) for p in map(Path,['/work/bridge.logs','/work/bridge'])],
    receipts=receipts))
L={
 'qr':'OpenAIQRH Theorem 1.1, PDF p.4 LF255–262',
 'rh':'PlattTrudgianFiniteRH Theorem 1, PDF p.2 LF48–49 and Cor.1 p.4 LF138–150',
 'fks':'FKS Theorem 3.2 PDF p.8 LF631–642; Cor.2.9 pp.7–8 LF586–608; Table 8 p.26 LF3178–3258',
 'recip':'PlattTrudgian2021 Lemma 2, PDF p.4 LF236–246',
 'zcount':'FKS Lemma 2.1/Remark 2.2 pp.4–5 LF272–313 and Table 1 p.5 LF330–345; CH2 p.43 Appendix B.1 LF6133–6143',
 'sieve':'DudekPlatt2015 Lemma 3.4, PDF p.10 LF698–715; PlattTrudgian2021 Thm 2 p.3 LF205–212',
 'pv':'DudekPlatt2015 proof of Lemma 3.2, PDF p.8 LF561–562 only for the computed sign',
 'pt':'PlattTrudgian2021 Theorem 2, PDF p.3 LF205–212; DudekPlatt2015 Theorem 1.2 p.2 LF53',
 'ch':'CH2 Cor.1.3 PDF p.3 LF226–240; Cor.9.3 p.36 LF5336–5363, including (9.4)',
 'clocal':'CH2 Cor.1.2–1.3 PDF p.3 LF190–240; Lemma 9.2 p.35 LF5216–5223',
 'ef':'PlattTrudgian2021 Lemma 6, PDF pp.9–10 LF801–812; PlattTrudgianFiniteRH Cor.1 p.4 LF138–150',
 'dis':'Dusart Theorem 4.2 PDF p.11 LF959–1027; Prop.4.3 p.12 LF1049–1056 and Cor.4.5 p.13 LF1132–1133',
 'dus':'Dusart Thms 5.6–5.9 PDF pp.17–20 LF1479–1505,1555–1586,1633–1664',
 'expl':'Dusart (2.1) pp.3–4 LF171–189',
 'fb':'FKS Cor.1.4 p.2 LF140–143; Theorems 1.1–1.2 LF113–135, Tables 5–6 at admissible rows'}
S='supported_at_stated_trust_tier'; B='baseline_retained'; X='false_with_specific_counterexample'; W='equivalent_or_weaker'
claims=[]
def loc(f,r,quote=True):
    lines=(C/f).read_text().split('\n')
    seg=r if isinstance(r,str) else str(r)
    assert refs[f]['sha256']==sha(C/f)
    nums=tuple(map(int,seg.split('-')))
    d={'file':refs[f]['packet_name'],'physical_LF':nums[0],'sha256':refs[f]['sha256'],
       'original_name':f,'physical_LF_end_inclusive':nums[-1]}
    if quote: d['locked_readback']='\n'.join(lines[nums[0]-1:nums[-1]])
    return d
def add(i,fam,f,r,stmt,dom,check,cites='',code='',rec='',strict='As written',status=S,
        base='Input-independent B0 branch; pointwise keep the best applicable envelope.',
        assume='B0 (cumulative seven originals at stated trust, no full RH or D01).',
        gap=None,keep=(),prop=False,where=None,current=True,trust=None):
    family={'C':'Both','R':'Ramanujan','M':'Mertens'}[fam]
    rcs=rec.split()
    claims.append(dict(claim_id=i,family=family,written_source=loc(f,r),
        exact_statement=stmt,assumptions=assume,full_domain=dom,strictness=strict,
        real_or_integer=('Integer onset interpretation additionally specified; primary variable real.' if i=='R-integer' else
          'Integer only.' if i=='R-original-integer' else 'Real analytic variable; cutoffs include equality unless specified; integer indices where stated.'),
        baseline_comparison=base,source_locators=[L[c] for c in cites.split()],
        derivation_check=check,numerical_obligations=[details[k][1] if k in details else receipts[k]['covered_obligations'] for k in rcs],
        implemented_formula_sources=[loc(*pair.split(':')) for pair in code.split()],
        actual_verification_receipts=[receipts[k]['stdout'] for k in rcs],
        retained_valid_branches=list(keep),M_status=status,precise_gap_or_counterexample=gap,
        propagation={'input_used':prop,'where_it_changes_proof':where,
                     'matched_comparison':'B0 and B0+D01 have identical lawful consequences; no D02 supplied.'},
        V_status='Ordinary executable replay; no Lean/Blueprint/kernel or source-first PV.' if rcs else
            'Written mathematics or inherited original; no Lean/Blueprint/kernel or source-first PV.',
        remaining_trust=trust or ('Original-source trust and ordinary directed arithmetic/sieve/toolchain where relevant.' if rcs else 'Written mathematics and stated original-source trust.'),
        current_affirmative_branch=current))
def common(i,r,s,d,check,**kw):add(i,'C','common.md',r,s,d,check,**kw)
def rg(i,r,s,d,check,**kw):add(i,'R','ramanujan.md',r,s,d,check,**kw)
def gr(i,r,s,d,check,**kw):add(i,'R','gap_repair.md',r,s,d,check,**kw)
def mt(i,r,s,d,check,**kw):add(i,'M','mertens.md',r,s,d,check,**kw)
def sp(i,r,s,d,check,**kw):add(i,'M','spectral_repair.md',r,s,d,check,**kw)
common('C-density-weights','15-36','Explicit density weight W_i and telescoped D(t) with the nine rounded FKS bins and the stated finer right endpoint cuts; |u(t)|≤D(t).',
       't≥100; density integrals in v≥H','No end count before H; integrate N(s,v)/v², fourth Taylor majorant and nonnegative cumulative differences. Check conjugates and boundary beta=7/8.',
       cites='qr rh fks recip',code='verify.py:67-84 verify.py:101-111',rec='verify',strict='Non-strict majorant.')
common('C-power','3-7','|psi(x)−x|<.02 x^(7/8).','x≥e^200','All terms in scaled D decrease, and directed upper at 200 is <.019.',cites='qr rh fks recip',code='verify.py:109-111 verify.py:214-217',rec='verify audit_aux',strict='Strict.')
common('C-density-free','45-66','|u(L)|≤.0142L²exp(−L/8)+2.091L exp(−L/4), strictly less than D01 at L≥200.',
       'Truncation bound L≥100; comparison L≥200.','Use the same sum with all exponents ≤7/8; scaled remainder decreases. No far-right density or finite RH needed.',
       cites='qr fks recip',code='spectral_repair.py:85-86',rec='spectral_repair',
       assume='Zeta part of QRH, FKS Theorem 3.2 and Platt–Trudgian Lemma 2.')
common('C-equivalent','40-42','B0 and B0+D01 entail exactly the same mathematical conclusions in both families.','Every matched strength, onset and domain.',
       'Direct entailment of exact D01 proves equivalence of the premise sets.',status=W,cites='qr fks recip',base='No D01-specific propagation possible.')
add('C-B6','C','tradeoff.md','3-9','Over B6, D01 is equivalent to the zeta half-plane beta≤7/8; no non-zeta replacement asserted.',
    'Every nontrivial zeta zero; D01 x≥exp(200).','Uniform integral convergence in Re s>7/8 and meromorphic log-derivative identity; nonzero residues at zeros.',
    cites='qr fks recip',status=W,assume='B6 + either D01 or just the zeta conclusion of QRH, as appropriate.',prop=True,
    where='D01 supplies analytic continuation of the residual integral, replacing the zeta conclusion only in this alternative premise accounting.')
rg('R-count','28','Two exact prime counts via quotient-compressed Eratosthenes.','Integer queries n=N and n=floor(N/e); generic routine for integer n.',
   'Descending updates preserve smaller cells; composites removed according to least prime factor.',
   code='count.py:3-15 verify.py:173-182',rec='verify audit_aux')
rg('R-root','20-24','Unique z in (N,N+1) with ezB/log z=A², strictly between 38358837682.21792636514419 and 38358837682.21792636514511; R(z)=0 and R<0 on [N,z).',
   '[N,z] and the bracket.','Counts and both shifted floors checked; derivative positive and bisection signs directed.',
   code='count.py:3-15 verify.py:173-194',rec='verify audit_aux')
rg('R-local-margin','24-26','R(x)≥67000000(x−z).','[z,N+1] closed.','Both counts remain constant including composite N+1; directed lower bound on derivative.',
   code='verify.py:173-194',rec='verify audit_aux',strict='Non-strict lower bound.')
rg('R-bridge-new','30-35','R>0 over the new re-sieved near-endpoint block.','[38358837683,10^11] real closed.',
   'Exact lower floor for p/e, correct two segmented sieve streams, outward logarithmic tangent, proved integer widths and monotonic on prime-free intervals.',
   code='bridge.py:6-19 bridge.c:18-62 verify.py:173-194',rec='bridge verify audit_aux',strict='Strict.')
rg('R-bridge-original','26','R>0 on the published middle interval (even integer restriction suffices via monotonicity).','[10^11,1.15e16] closed.',
   'Published computation applies without full RH; integer-to-real via constant pi(x) on unit cells.',cites='sieve',status=B,strict='Strict.')
rg('R-open-ray','24-26','Strict sign holds on the whole open ray x>z and it fails at z.','(z,∞) with endpoint excluded.',
   'Join local interval, C sieve, original middle and overlapping analytic ray.',cites='sieve',code='bridge.c:36-62 verify.py:173-207 gap_repair.py:82-106',
   rec='bridge verify gap_repair audit_aux',strict='Strict for x>z; equality at z.',keep=('R-root','R-bridge-new','R-bridge-original'))
rg('R-integer','24','38358837683 is the least strict integer-ray onset.','All integers ≥38358837683 (N fails).',
   'Follows from the exact real root and connected ray.',cites='sieve',rec='bridge verify gap_repair',strict='Strict.')
rg('R-real-original-boundary','26','Rejected diagnostic: original literal R>0 for N<x≤exp(58).','N<x≤exp(58), interpreted real.',
   'Both counts constant up to N+1; the literal lower real endpoint is wrong. Not a candidate theorem.',status=X,
   cites='pt',code='verify.py:173-194',rec='audit_aux verify',current=False,
   gap='x=38358837682.1: R lies between −7974585.083 and −7974585.082.',keep=('R-root','R-open-ray','R-original-integer','R-original-3915'))
for i,dom,c in [('integer','Integers N<x≤e^58.','Integer restriction of Platt–Trudgian PNT Thm 2.'),('3915','Real L≥3915.','Platt–Trudgian high-ray branch.'),('9658','Real L≥9658.','Dudek–Platt unconditional Thm 1.2.')]:
    rg('R-original-'+i,'96','R(x)>0. '+c,dom,'Inherited as stated, not full RH; included independently in the finite/tail union.',cites='pt',status=B,strict='Strict.')
rg('R-pi-transform','39-45','Exact Li_2-normalized pi identity with u_theta(L) and the prefix integral from log 2.','x≥2.',
   'Partial summation from the end-inclusive theta count; base term is +2/log 2.')
for tag,r,dom,c,alg,code in [
 ('EC','48-51','L≥12','ch dis','Use c+117e^(−L/2), log derivatives 5/6 and 1/3 and prefix through 12.','verify.py:112-113'),
 ('EF','52','7≤L≤58','ef dis','Integrand t² cancels the t^−2 weight; prefix through 7.','verify.py:114-115'),
 ('EF2','53-57','34≤L≤58','ch dis rh ef','CH2 (9.4), verified T endpoints and algebra reserve; weighted squared factor increases past 34.','verify.py:94-98 verify.py:116-119'),
 ('EF2-upper','58','34≤L≤58','ch dis rh ef','Subtract 2e^(−L/2)[1+2(1−e^((34−L)/2))/L]; .9999+1.007>2 and use t^−2≥L^−2.','verify.py:124-129'),
 ('ED','59-63','L≥100','qr rh fks recip dis','Only integral anchor at 100; apply log derivative ≥.98−r to each actual exponential.','verify.py:99-111 verify.py:120-123')]:
    rg('R-'+tag,r,tag+' approximation envelope to the normalized Li_2 pi error.',dom,alg,cites=c,code=code,rec='verify')
rg('R-Li-anchor','65','12<Li_2(e^30)−F18(e^30)<13 and its positive normalized remainder ≤13Le^(−L)+3·19!/L^19.',
   'L≥30 (anchor L=30).','Derivative identity and exp-series/geometric remainder, then derivative ≥1/3.',code='verify.py:87-93',rec='verify')
rg('R-PV','67-69','Apply pi<li on admissible unshifted cells and use li(2)<3, yielding upper error 16Le^(−L)+3·19!/L^19.',
   'Applicable displayed cells under e^L≤1.2e17.','PV change of variable checked; the numerator shift uses separately certified error.',
   cites='pv',code='verify.py:152-162 gap_repair.py:24-31',rec='verify gap_repair')
rg('R-old-profile','67-77','Pointwise bound G18−L⁴[(L/(L−1))V(L−1)+2S18(L)U(L)+U(L)²].',
   'L≥36.98.','Take minimum only of eligible pi error bounds, apply lower shifted and upper unshifted, then square. Min of signed upper budgets checked nonnegative on replayed cells.',
   cites='ch dis ef qr rh fks recip pv',code='verify.py:124-162',rec='verify')
rg('R-G18','79-86','G18 monotone from L≥36.98 (indeed ≥36); explicit C_j and reserve through n+1, 4≤n≤17.',
   'Series for L>1; derivative/reserve assertions from L≥36.',
   'Exact binomial and polynomial coefficients; weighted negative derivatives and values absorbed by C27.',
   code='verify.py:55-65',rec='verify')
oldrows=[('36.98','37.5','.10'),('37.5','39.32','.32'),('39.1','39.32','.8'),('39.32','39.5','.065'),
    ('39.5','40','.145'),('40','42.8','.35'),('42.8','∞','1'),('43','60','1.038'),('46','77','1.209'),('47','67','1.246')]
for lf,(a,b,v) in enumerate(oldrows,7):
    rg('R-old-margin-'+str(lf),lf,'Y(L)>'+v+'.',f'Closed log domain [{a},{b}] (∞ means unbounded).',
       'Directed closed-cell lower loss; in the unit ray use overlap [60,163] and P4 from 163.',
       cites='ch dis ef pv qr rh fks recip',code='verify.py:124-171 verify.py:197-213',rec='verify',strict='Strict.')
for a,v in [('36.98','.065'),('39.5','.145'),('40','.35')]:
    rg('R-old-ray-'+a,18,'Y(L)>'+v+'.','L≥'+a+'.','Use the minimum of covered successive margins and the unit ray.',
       cites='ch dis ef pv qr rh fks recip',code='verify.py:197-213',rec='verify',strict='Strict.')
gr('R-forward','63-83','W_pi bounds the forward prefix with psi on [7,L] and old theta before 7.','L≥7.',
   'Integrate B by parts with exact signs; 3/14,33/56 log derivatives, residual 2/7, and w(7)J(7)+2/7<1.',
   cites='dis expl zcount qr rh',code='gap_repair.py:4-8 gap_repair.py:30-31',rec='gap_repair')
gr('R-prime-power-forward','84-99','U_pi≤q correction≤V_pi with the displayed weighted forward-integral factors.',
   'L≥7.','Upper square/cube log derivatives 3/14 and 1/21, lower correction integrate nonnegative square with t^−2≥L^−2.',
   cites='dis',code='gap_repair.py:9-13',rec='gap_repair')
gr('R-new-profile','101-125','New G18 profile from M_psi+W_pi± prime-power errors, with old envelopes and PV-li branch.',
   'Finite calculations L≥36.54; each option only when L and separately L−1 are in its source domain.',
   'Include truncation only on the upper signed side; shifted lower has no positive remainder cost. Only use PV through verified range.',
   cites='ch dis ef pv qr rh fks recip expl zcount',code='gap_repair.py:14-48',rec='gap_repair')
newrows=[('36.54','∞','.002'),('36.745','∞','.1'),('36.91','∞','.164'),('36.98','37.5','.2'),('37.5','39.326','.4'),
    ('39.1','39.326','.84'),('39.3','39.326','.88'),('39.94','∞','.4'),('40','∞','.425'),('42.482','∞','1'),
    ('43','60','1.06'),('45','77','1.209'),('46','67','1.246'),('47','61','1.27'),('48','55','1.30'),('49','52','1.32'),('59','80','1.20'),('80','100','1.15')]
for lf,(a,b,v) in enumerate(newrows,18):
    gr('R-new-margin-'+str(lf),lf,'Y(L)>'+v+'.',f'Closed log domain [{a},{b}] (∞ means unbounded).',
       'Replay adaptive cells with interval excess; for rays use unit overlapping finite [60,163] and P4 tail from 160.54.',
       cites='ch dis ef pv qr rh fks recip expl zcount',code='gap_repair.py:14-48 gap_repair.py:82-106 verify.py:203-207',
       rec='gap_repair verify',strict='Strict.')
for i,(tol,a0,a1) in enumerate([('.065','36.98','36.745'),('.145','39.5','36.91'),('.35','40','39.94'),('1','42.8','42.482')]):
    gr('R-matched-threshold-'+str(i),'42-45','For fixed q='+tol+', improve sufficient L-onset '+a0+' to '+a1+'.','L≥'+a1+'.',
       'Use the stronger connected new margins then unit tail.',cites='ch dis ef pv qr rh fks recip expl zcount',rec='gap_repair verify')
for i,(a,v) in enumerate([('36.98','.164'),('39.5','.164'),('40','.425')]):
    gr('R-matched-strength-'+str(i),'44-45','At fixed log onset '+a+' the improved guaranteed margin is '+v+'.','L≥'+a+'.',
       'Use the stronger connected new margins and unit tail.',cites='ch dis ef pv qr rh fks recip expl zcount',rec='gap_repair verify',strict='Strict.')
for n,a in [(4,163),(5,191),(6,223),(8,290),(10,360),(12,432),(14,504),(16,577),(17,620)]:
    rg('R-old-tail-'+str(n),'86-90',f'Y>P_{n}, old m=18 fixed loss certificate.',f'L≥{a}.',
       'Take E_− at L−1 including truncation. Scale by L^(n+1) and use derivative and inverse-power tests; absorb into C_(n+1).',
       cites='qr rh fks recip dis',code='verify.py:164-171 verify.py:208-213',rec='verify',strict='Strict.')
rg('R-arbitrary-order','92','For every fixed integer n≥4 there exists an eventual strict normalized ray Y>P_n, by m=n+2.',
   'Every fixed n≥4, L≥a(n) as certified, with no unconditional arbitrary-resource execution guarantee.',
   'Full positive coefficients through m; negative finite tail absorbed by C_m; scaled error tends to zero.',
   cites='qr rh fks recip dis',code='general.py:5-23',rec='general',strict='Strict.')
for n,a in [(20,722),(24,868),(32,1161),(48,1748),(64,2336)]:
    rg('R-general-example-'+str(n),92,f'Y>P_{n}, old arbitrary-order m=n+2 example.',f'L≥{a}.',
       'Exact coefficient and monotone loss reserve check at stated onset.',cites='qr rh fks recip dis',
       code='general.py:5-23',rec='general',strict='Strict.')
for n,a in zip([4,5,6,8,10,12,14,16,17,20,24,32,48,64],
    ['160.54','189.18','220.73','288.15','358.34','429.78','501.87','574.34','610.67','719.91','865.96','1158.82','1745.95','2333.94']):
    gr('R-deep-tail-'+str(n),'50-59',f'Y>P_{n}, repaired multi-reserve m=n+8 proof.',f'L≥{a}.',
       'Scaled G reserve through m−1; exact negative tail test and derivative-justified monotone separate L/L−1 losses, checked at exact decimal.',
       cites='qr rh fks recip dis expl zcount',code='gap_repair.py:50-71 gap_repair.py:105-106',rec='gap_repair',strict='Strict.')
rg('R-limit',96,'Y=1+14/L+O(L^−2); no fixed eventual q>1.','L→∞; assertion about every eventual ray.',
   'Two-sided factorial truncation m=5 and exponential prime error give the asserted expansion.',cites='qr rh fks recip dis')
gr('R-robust-fixed','173-180','New finite/connected fixed margins remain without the FKS Cor. 2.9 coefficients.',
   'New finite and connected rows; EC-only [60,269], D01-derived unit tail after 269.',
   'No finite adaptive cell uses density, and weaker D01 follows density-free from B0; replace only the middle/tail proof route.',
   cites='qr fks recip ch dis expl zcount rh',code='gap_repair.py:14-29 tradeoff.py:3-20',rec='gap_repair tradeoff',
   assume='B0 with FKS Cor. 2.9/Table 8 withheld (direct D01 via density-free implication).')
for n,a in [(4,269),(5,303),(6,338),(8,412),(12,562),(17,755)]:
    add('R-D01-direct-'+str(n),'R','tradeoff.md',13,f'Y>P_{n} via direct D01 tail with weaker onset {a}.',f'L≥{a}.',
        'Replace psi term in ED from 200, prefix <4e−17, then scaled monotone m=18 bound with separate L−1.',
        cites='ch dis',code='tradeoff.py:3-20',rec='tradeoff',status=W,prop=True,strict='Strict.',
        where='Substitute D01 for the theta budget after adding prime powers in ED. Later onsets than density B0 at the same target.',
        assume='B6+D01, using D01 directly rather than recovering QRH.')
add('R-D01-join','R','tradeoff.md',13,'EC-only unit closed bridge to the direct-D01 P4 ray.','60≤L≤269; tail L≥269.',
    'Code uses only EC on both t=L,L−1 in the [60,269] join; old earlier fixed margins need no QRH.',cites='ch dis ef pv',
    code='tradeoff.py:16-19 verify.py:124-150',rec='tradeoff',status=W,
    assume='B6 in the finite part; direct D01 in the adjoining unit tail.')

for k,expr,start,lf in [('P','|C_P−1|≤.2/L³',2278382,50),('Q','|C_Q−1|≤.2/L³',2278382,50),
                        ('E1','|E1|≤.2/L³',2278383,50),('weighted','|Elog|≤.3/L²',912560,50)]:
    mt('M-Dusart-'+k,lf,expr+'.',f'x≥{start}, real closed.','Original O* gives a nonstrict absolute error; product original normalizations retain relative form.',
       cites='dus',status=B,strict='Non-strict.')
mt('M-normalizations','3-11','C_P=e^gamma L P_raw, C_Q=e^(−gamma)Q_raw/L; E1=∑1/p−log L−M; Elog=∑log(p)/p−L+B3; exact constants M and B3.',
   'x>1; p≤x right inclusive.','Compare weighted sign (plus B3 in error) and product reciprocal normalizations to named original.',cites='dus',
   code='early.py:15-25 weighted.py:22-36 smallprod.py:31-47 power_bridge.py:11-24')
mt('M-empty',50,'Empty raw products equal 1 and prime sums equal 0; insert into the normalizations, not normalized product=1.',
   '1<x<2.','No primes; the logarithms of L are defined at these points.')
for i,line,stmt in [
 ('logQ',66,'D_Q=u(L)/L−∫uK+U.'),('recip',67,'E1=u(L)/L−∫uK+U+T_0.'),
 ('weighted',68,'Elog=u(L)−∫u+V.')]:
    mt('M-psi-'+i,line,stmt,'L>0, strict prime-power tails and inclusive local p^m≤x.',
       'Partial summation with p^m cutoff, exact complementary tail and limit constant from original.',
       cites='dus qr fks recip')
mt('M-pp-old','71-82','0≤U≤U+T_0≤V/L; V_b=(1+7.3938/L)e^(−L/2)+10e^(−2L/3); global alternative 4e^(−L/2)+10e^(−2L/3); T_0≤1/(2floor(x)).',
   'V_b x≥4; global alternative x>1; T_0 bound x≥1.',
   'Separate square term with partial summation and the two geometric-prime regimes; T_0 follows telescoping.',
   cites='dis',code='mverify.py:14-20 tradeoff.py:21-26',rec='mverify')
mt('M-J1','84-99','|∫_L^∞u|≤J_1=.2e^(−L/2)+2e−11e^(−L/8)+2e^(−L).','L≥1.',
   'Binwise L² justification, zero-integral divisor, bound normalized residual and dyadic zero weights, then dominate upper endpoint limit.',
   cites='expl zcount qr rh',code='mverify.py:7-13',rec='mverify')
mt('M-J2','90-99','|∫u k|≤k(L)J_2 for bounded nonnegative decreasing C¹ kernel k, in particular K.',
   'L≥1; k on [L,∞).','Integration by parts in each zero term yields factor two; the actual normalized residual is still bounded by 2e^(−L).',
   cites='expl zcount qr rh',code='mverify.py:7-20',rec='mverify')
mt('M-W','101-115','Piecewise W for unsigned weighted and scaled log/reciprocal errors, converted with 1.0001 on L≥17.',
   'Closed analytic bands [17,29], [29,58], [58,189], [189,∞).',
   'Both signed sides checked in early CH2 band; coefficient comparisons at each correct endpoint, then termwise bounds, and exponentiation.',
   cites='clocal rh fks qr recip expl zcount dis',code='mverify.py:14-46',rec='mverify')
mt('M-old-polynomial-dominance',21,'1.0001 W is strictly below .2/L² for weighted and gives stronger than .2/L³ for first three; thus also improves weighted .3.',
   'L≥17, matched original domains there.','Band-scaled reserves decrease except floor right-end maximum; split tail with decreasing L²e^(−L/8).',
   cites='dus clocal rh fks qr recip expl zcount dis',code='mverify.py:42-47',rec='mverify',strict='Strict.')
mt('M-old-polynomial-130','117','All four polynomial-scaled errors are strictly below .130.','L≥18.',
   'Start narrower first band at 18, keeping the same other reserves.',
   cites='dus clocal rh fks qr recip expl zcount dis',code='mverify.py:60-64',rec='mverify',strict='Strict.')
for k,domain,orig,a,b in [('first3','L≥log(2278382) for products / log(2278383) for reciprocal sum','.2',40,41),
                            ('weighted','L≥log(912560)','.3',35,36)]:
    mt('M-old-cross-'+k,21,f'.01970 power curve is weaker on earlier matched part, then has unique crossover with {orig} in ({a},{b}) and is stronger thereafter.',
       domain,'Ratio proportional to L² exp(−L/8), increasing to 16 and decreasing thereafter; original left endpoints above ratio 1.',
       cites='dus',code='mverify.py:66-72',rec='mverify')
for tag,ff,rows,lf in [
    ('old','mertens.md',[(200,'.01886'),(300,'.01517'),(500,'.01311'),(1000,'.01183'),(3000,'.01099'),(30000,'.01052'),(1000000,'.01046')],'17-19'),
    ('new','spectral_repair.md',[(200,'.018857'),(300,'.015169'),(500,'.013103'),(1000,'.011821'),(3000,'.010979'),(30000,'.010514'),(1000000,'.010453')],'226-228')]:
    for a,k in rows:
        add(f'M-{tag}-power-{a}','M',ff,lf,f'All power-scaled errors strictly less than {k} (L exp(L/8) for P,Q,E1, exp(L/8) for Elog).',
            f'L≥{a}.','Scaled positive envelope and unscaled log magnitude decrease; directed endpoint including relative conversion.',
            cites='fks recip qr rh zcount expl dis',code='mverify.py:37-41' if tag=='old' else 'spectral_repair.py:41-45 spectral_repair.py:63-66',
            rec='mverify' if tag=='old' else 'spectral_repair',strict='Strict.')
for k,a in [('first3',100000),('weighted',500000)]:
    mt('M-early-old-power-'+k,15,f'.01970 for the power-scaled {k} error(s).',f'x≥{a}.',
       'Join from early polynomial maxima via exp(L/8)/L² decreasing through L=14, then old spectral/density bands with separate exponentiation.',
       cites='clocal rh qr fks recip expl zcount dis',code='mverify.py:14-58 early.py:24-54',rec='mverify early',strict='Strict.')
mt('M-local-psi-min',122,'Intersect all explicitly stated applicable signed psi intervals, incl. shifted CH2 and literal FKS rows.',
   'Every x>1 within each branch domain; CH2 varying T in [10^7,H], x>max(T,10^9); FKS Cor.1.4 x>2; density L≥100.',
   'Respect shifted CH2 center and use finite RH only through T; optional original table rows only within their hypotheses.',
   cites='clocal ch rh fks fb qr recip')
mt('M-tail-psi-min',123,'Intersect segmented signed local-endpoint integrals with the ψ spectral envelopes in each ψ transform.',
   'L>0; spectral options when L≥1.',
   'Positive kernels preserve inequality; local intervals at all t combined integrably using exponential tail. No θ used in this ψ bound.',
   cites='expl fks recip qr rh zcount')
mt('M-theta-transform',123,'Both prime-sum transforms with theta and no prime-power correction; signed theta intervals and integrals.',
   'L>0; original theta local interval rows only at actual onsets; lower discrepancy zero before x=121.',
   'Direct summation by parts; signed subtraction from ψ interval or direct original theta bound. Use non-strict elementary |theta−x|≤x here; small-x branch exact.',
   cites='dus dis ef rh')
mt('M-log-via-recip',123,'D_Q=E1−T_0, so subtract [0,1/(2floor(x))] from the E1 interval.',
   'x>1.','Exact difference of tail sums.',cites='dus')
mt('M-A-bridge',124,'D_Q−U=A(L)/L−∫_L^∞A/t², A(t)=∑_{n≤e^t}Λ(n)/n−t+γ, intersect with the separate CH2 A intervals.',
   'L>0; CH2 Cor.1.2 valid T and x cutoff; Cor.1.3 all x≥1; spectral intersections L≥1.',
   'Stieltjes integration against t^−1; correct constants and local inclusion. Endpoint integrals converge.',
   cites='clocal dus fks qr recip')
mt('M-relative',125,'Separate P and Q conversions from signed log interval [l,h], then min with other valid envelopes; simultaneous relative d gives |D_Q|≤log(1+d).',
   'All admissible x>1.','Use monotonicity of exp in both signs and positivity of the raw products.',cites='dus',
   code='early.py:37-43 smallprod.py:55-68 power_bridge.py:39-45',rec='early smallprod power_bridge')
mt('M-early-sieve','129-131','All early real constant-prefix intervals, outward normalizers and a finite exact-prefix pointwise branch.',
   '2≤x≤2278383, including post-jump final cell.',
   'Trapezoid error gamma enclosure and positive prime tails; check logs at upper and lower endpoints, p exactly counted via sieve.',
   cites='dus',code='early.py:4-54',rec='early')
mt('M-extended-weight',133,'Weighted prime-sum finite bridge with fixed-point logs and tighter B3 normalizer through 25m.',
   'From the stated active real onsets through 66000000; analytic join later.',
   'Use eta=.2/log²(25m) in weighted theta tail; scaled signed positive decreases when 2d<L, negative magnitude increases; endpoint limits outward.',
   cites='dis dus',code='weighted.py:5-62',rec='weighted')
mt('M-extended-products','135-137','Extended ordinary exact integer interval products and reciprocal-sum bounds; matched fractional onsets.',
   'Listed real onsets from 2000000 through 66000000.',
   'Fixed-point log and loglog, theta tail for M after 2278383, checked |delta|<.1 controls signed derivative; separate exponential conversions.',
   cites='dis dus',code='smallprod.py:7-79',rec='smallprod')
earlyrows=[(2,'3.826','3.960','3.971','4.551'),(1000,'2.247','2.261','2.271','2.570'),
 (10000,'1.266','1.268','1.271','1.414'),(100000,'.596','.596','.597','.656'),(500000,'.343','.343','.343','.372'),
 (900000,'.288','.288','.288','.313'),(1000000,'.275','.275','.276','.296'),(2000000,'.209','.209','.209','.2248')]
for lf,(a,p,q,r,w) in enumerate(earlyrows,27):
    code='early.py:24-54' if a<1000000 else 'early.py:24-54 weighted.py:37-62' if a==1000000 else 'smallprod.py:48-79 weighted.py:37-62'
    rec='early' if a<1000000 else 'early weighted mverify' if a==1000000 else 'smallprod weighted mverify'
    mt('M-early-row-'+str(a),lf,f'Polynomial-scaled tuple (P,Q,E1,Elog) bounded by ({p},{q},{r},{w}).',f'x≥{a} real closed.',
       'Use early outward sieve then original bounds, or extended sieve then .130 analytic join for refined entries.',
       cites='dus dis clocal rh fks qr recip zcount expl',code=code,rec=rec,strict='Strict (finite and tail bounds below targets).')
for tag,a,c in [('weighted',912000,'.30151'),('weighted',3000000,'.212'),('weighted',5000000,'.162'),('all4',10000000,'.130'),
                ('first3',3000000,'.19844'),('first3',5000000,'.15013'),('first3',10000000,'.120')]:
    finite=tag=='first3' and a==10000000
    rc='weighted' if tag=='weighted' else 'smallprod' if tag=='first3' else 'weighted smallprod'
    mt(f'M-old-extra-{tag}-{a}',36,f'Polynomial-scaled {tag} bound <{c}.',f'x≥{a}'+(' through 66000000 (finite).' if finite else ' real closed ray.'),
       'Use printed strict outward finite maxima; analytic old .130 tail for full rays (or equality of the coefficient as a strict bound).',
       cites='dus dis clocal rh fks qr recip expl zcount',code='receipts.py:27-35 mverify.py:60-64',
       rec=rc if finite else rc+' mverify receipts',strict='Strict.')
fix=[('P/Q','.2','2278381.8'),('P/Q','.19999','2278381.9'),('P/Q','.19998','2278382'),
     ('P/Q/E1','.2','2278382.2'),('P/Q/E1','.19992','2278383'),('Elog','.3','912559.998'),('Elog','.2999995','912560')]
for lf,(tag,c,a) in enumerate(fix,42):
    weighted=tag=='Elog'
    mt('M-matched-'+a+'-'+tag.replace('/',''),lf,f'Polynomial-scaled {tag} strictly below {c}.',f'x≥{a} real closed.',
       'Clip exact real onset and use extended test through 66m, then .130 from e^18. Original constants/domains retained where applicable.',
       cites='dus dis clocal rh fks qr recip expl zcount',
       code=('weighted.py:37-62' if weighted else 'smallprod.py:48-79')+' receipts.py:27-35 mverify.py:60-64',
       rec=('weighted' if weighted else 'smallprod')+' mverify receipts',strict='Strict.',
       base='Same or improved Dusart tolerance at earlier closed real onset, or stronger tolerance at matched onset, as stated; B0 only.')
sp('M-old-theta-scope-false','13-22','Withdrawn: apply the unshifted ψ-only J1 directly to the θ integral.',
   'Counterexample at L=17, k=1.','∫q≥1.9998exp(−17/2)>2J1, hence ∫u_theta<−J1; actual transform and final replacement retained.',
   cites='dis expl zcount qr rh',code='spectral_repair.py:81-84',rec='spectral_repair',status=X,current=False,
   gap='L=17 gives strict violation by the displayed lower bound on ∫q and upper ψ J1 bound.',
   keep=('M-J1','M-theta-transform','M-J-shift-theta'))
sp('M-zero-weights','52-84','Gamma^−2 total below .1, high |gamma|≥H below 4e−12; general y≥100 bound (3).',
   'y≥100, H=3e12.','Use pre-jump lower N(y−) and continuous count bounds; integrate r0 majorant and add low weights; both signs.',
   cites='zcount rh',code='spectral_repair.py:6-13',rec='spectral_repair')
sp('M-J-sharp','28-39','For k=1 or K, ψ integral ∈ k(L)[−Z−2exp(−L), Z].','L≥1.',
   'Laplace factor-one expansion for full ray; dominated limit from compact L²; residual has strictly negative sign.',
   cites='expl zcount qr rh',code='spectral_repair.py:6-17',rec='spectral_repair')
sp('M-J-shift-theta','40-50','θ integral belongs to ψ interval minus [∫q_- k, ∫q_+ k].','L≥1, k=1 or K.',
   'Exact u_theta=u−q, correct interval subtraction, q_- switches at log121.',
   cites='expl zcount qr rh dis',rec='spectral_repair')
sp('M-kernel','86-112','Factor-one bound for any nonnegative-measure Laplace kernel finite at L.',
   'L≥1, both cited kernels satisfy representation; statement applies to the stated Laplace class.',
   'For each zero factor integrate e^(rho−1−v)t and compare divisor norms monotonically in v. Finite-interval bound twice as large dominates.',
   cites='expl zcount qr rh')
sp('M-prime-theta','116-126','|u_theta(t)|≤3e^(−t/2)+d; theta(z)≤1.08z.',
   't≥7 and z≥e^(14/3); d=c+114e^(−14.5).',
   'Use signed CH2 small-range branch and positive side from earliest cutoff, then CH2 floor and Dusart discrepancies.',
   cites='clocal dis',code='spectral_repair.py:18-25',rec='spectral_repair')
sp('M-V2','128-134','|V2−e^(−L/2)|≤(7e^(−L/4)+3d)e^(−L/2).','L≥14.',
   'Stieltjes tail from y=sqrt(x), correct left exclusion; constants from boundary and double integral.',cites='clocal dis',code='spectral_repair.py:18-25',rec='spectral_repair')
sp('M-V-sharp','135-147','V between exp(−L/2)max(0,1−7exp(−L/4)−3d) and widehat V including +3.8 exp(−2L/3).',
   'L≥14, p^m=x on non-tail side.',
   'Sum cubic cutoff bins with theta≤1.08z and endpoint-verified geometric factor.',
   cites='clocal dis',code='spectral_repair.py:18-25',rec='spectral_repair')
sp('M-U-lower','149-165','U+T0≥max(0,1−2/L−3eta_y)e^(−L/2)/L; U separately by subtracting T_0 upper and clipping; new common upper from min(V_b,widehat V)/L.',
   'L≥14.',
   'Reweight square tail; elementary main integral lower and Stieltjes error budget as written; retain old signed alternatives.',
   cites='dis clocal',code='spectral_repair.py:18-25',rec='spectral_repair')
sp('M-new-min','167-181','New pointwise signed intersection, integrating sharpened ψ and shifted θ intervals, and optional CH2 local refinements.',
   'Whole x>1 with per-option domains, including CH2 [10^4,10^13] small interval and [34,58] log interval for (9.4).',
   'Only ψ receives prime-power corrections. Keep all valid branches, normalizations and empty cutoff.',
   cites='expl zcount qr rh dis clocal ch dus')
sp('M-Wstar','183-210','Explicit W_* piecewise shared envelope for weighted and L times three scaled log/sum errors, with e^(W_*/L)<1.0002 first band and <1.0001 thereafter for relative errors.',
   'L≥14, all band endpoints covered. Internal last split L=189.24.',
   'Valid signed CH2 checks using opposite endpoints, controlled high terms, floor and dominated last band; directed conversion.',
   cites='clocal rh qr fks recip expl zcount dis',code='spectral_repair.py:14-61',rec='spectral_repair')
for a,k in [(17,'.133'),('17.3','.120'),(18,'.091')]:
    sp('M-new-poly-'+str(a),'212-215',f'All four polynomial-scaled errors strictly below {k}.',f'L≥{a}.',
       'Scaled powers decrease within each band except the separate floor modeled at right endpoint; rigorous last ray.',
       cites='dus clocal rh qr fks recip expl zcount dis',code='spectral_repair.py:50-57',rec='spectral_repair',strict='Strict.')
for tag,coef,a in [('first3','.120','17.3'),('weighted','.12722','17.16')]:
    sp('M-new-10m-'+tag,'215-220',f'Polynomial-scaled {tag} <{coef} from 10^7.',
       'x≥10000000 real closed.',
       f'Replay old respective exact real-cell bound through 66m and overlap with analytic L≥{a}.',
       cites='dus dis clocal rh qr fks recip expl zcount',code='spectral_repair.py:50-58 spectral_repair.py:73-80',
       rec=('smallprod' if tag=='first3' else 'weighted')+' spectral_repair',strict='Strict.')
sp('M-new-poly-fallback','299-315','Tightened polynomial rays and early joins without Cor. 2.9/Table 8.',
   'Same .133/.120/.091 and finite-join rays; switch CH2 floor to density-free formula at L=230.',
   'Exponentiated/scaled endpoint reserve fits .091 at 230 and every expanded term decreases thereafter.',
   cites='dus clocal rh qr fks recip expl zcount dis',code='spectral_repair.py:95-100',rec='spectral_repair',
   assume='B0 with Cor. 2.9/Table 8 withheld.')
sp('M-new-power-14','222-228','All power-scaled errors strictly below .019675.',
   'L≥14.','Proof via directed bounds on each W_* band and its exponential conversion; no sampling.',
   cites='clocal rh qr fks recip expl zcount dis',code='spectral_repair.py:14-61',rec='spectral_repair',strict='Strict.')
for k,domain,orig,a,b in [('first3','L≥log(2278382) for products / log(2278383) for reciprocal sum','.2',40,41),
                            ('weighted','L≥log(912560)','.3',35,36)]:
    sp('M-new-cross-'+k,'234-248',f'.019675 power curve is incomparable on full matched {k} domain with {orig} polynomial curve; unique crossover ({a},{b}).',
       domain,'Scale the ratio; monotonicity on either side of 16, correct original left endpoints, exact bracket comparisons.',
       cites='dus',code='spectral_repair.py:88-93',rec='spectral_repair')
sp('M-power-finite','267-297','Closed real finite power bridges with clipped cells and rightward slab scaling; fixed-point gamma/M/B3 arithmetic.',
   'Each listed onset through composite T=1202606>e^14.',
   'Stieltjes B3 normalizer after 5m; b/(1−b) controls both relative errors; local bound each cell by endpoints then power scale at ≥ upper endpoint.',
   cites='dis dus',code='power_bridge.py:8-63 weighted.py:7-21 smallprod.py:7-29',rec='power_bridge')
for lf,(a,p,w) in enumerate([(50000,'.0268','.0292'),(60000,'.0248','.0272'),(70000,'.019675','.0214'),(104000,'.019675','.019675')],258):
    sp('M-new-power-'+str(a),lf,f'Power-scaled first three <{p}, and power-scaled Elog <{w}.',f'x≥{a}, real closed.',
       'Verified clipped finite cells to T and strict .019675 analytic branch for L≥14.',
       cites='dis dus clocal rh qr fks recip expl zcount',code='power_bridge.py:33-63 spectral_repair.py:59-61',
       rec='power_bridge spectral_repair',strict='Strict.')
for tag,coef,expr in [('first3','.147','L exp(−L/8)'),('weighted','.152','L² exp(−L/8)')]:
    add('M-direct-'+tag,'M','tradeoff.md',11,f'Direct D01 gives {tag} bound <{coef} {expr}, weaker than B0.',
        'L≥200.','Explicit integration of D01 with K or constant kernel; fully matched decreasing extraction and proper exponentiation.',
        cites='dus dis',code='tradeoff.py:21-27',rec='tradeoff',strict='Strict.',status=W,prop=True,
        assume='B6+D01 used directly.',
        where='D01 replaces u in both local and absolute tail in the ψ transform. No gain over the B0 density envelope.')
# Common analytic premises apply independently to both portfolio assessments.
# Serialize separate family-scoped references with distinct identifiers.
expanded=[]
for q in claims:
    if q['family'] != 'Both':
        expanded.append(q)
        continue
    for family in ('Ramanujan','Mertens'):
        expanded.append(dict(q, family=family, claim_id=q['claim_id']+'-'+family,
                             shared_analytic_claim_id=q['claim_id']))
claims=expanded
# Readiness summarizes only current claims; diagnostics are identified separately.
affirmative=lambda fam:[q['claim_id'] for q in claims if q['family']==fam and q['current_affirmative_branch'] and q['M_status'] in (S,B)]
review=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=index['candidate_id'],input_stage='D01',
    assessment_complete=True,all_claims_inventoried=True,reviewed_source_hashes=list(refs.values()),
    source_bibliography=src,actual_verification_commands=rs+[ [receipts['audit_aux']['argv'],receipts['audit_aux']['exit_status']] ],
    effort_description='Full written derivation and source audit of both families; all twelve locked certificate commands rerun and all available immutable stdout claims matched; ancillary checks described in evidence.json. No authoritative review token count available.',
    source_checkpoint='Page-numbered original source extractions with independently checked PDF/extraction hashes and selected original Flate content-stream checkpoints.',
    family_assessments={
      'Ramanujan':dict(strongest_supported_portfolio=affirmative('Ramanujan'),rejected_or_incomplete_claims=['R-real-original-boundary'],
        remaining_assessment_work=[],summary='Exact corrected real endpoint, near and inherited middle bridges, strongest new fixed/finite profiles and all repaired factorial onsets supported. No D01 increment. Rejected diagnostic is the original literal real boundary, not a current candidate theorem.'),
      'Mertens':dict(strongest_supported_portfolio=affirmative('Mertens'),rejected_or_incomplete_claims=['M-old-theta-scope-false'],
        remaining_assessment_work=[],summary='Raw reciprocal products and both normalized sums: finite, analytic, shifted, late and polynomial fallback branches supported at stated trust, with pointwise minima. No D01 increment. Rejected θ scope is withdrawn.')},
    claims=claims,no_other_arm_or_ranking_seen=True,new_core_math_salvage_performed=False,original_candidate_bytes_changed=False)
write('review.json',review)
write('STAGE_STATUS.json',dict(ready_for_review=True,families={x:dict(status=S,claim_files=['review.md','review.json']) for x in review['family_assessments']},serious_attempts_documented=True))
print(len(claims),'claim rows')
