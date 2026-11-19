from pathlib import Path
import json, re, ast, hashlib, copy
here=Path(__file__).resolve().parent
t=Path('/task')
idx=json.loads((t/'CANDIDATE_INDEX.json').read_text())
orig=json.loads((t/'SOURCE_INDEX.json').read_text())
files={r['original_name']:r for r in idx['candidate_files']}
lines={}
for f,r in files.items():
    b=(t/r['packet_name']).read_bytes()
    assert hashlib.sha256(b).hexdigest()==r['sha256']
    lines[f]=b.decode().split('\n')
def loc(f,n):
    ns=[n] if isinstance(n,int) else list(range(n[0],n[1]+1))
    assert all(1<=j<=len(lines[f]) for j in ns),(f,n)
    # Index identity is the packet filename and a single one-based LF anchor.
    # Preserve the exact original name and the full span separately.
    a=ns[0]
    result=dict(file=files[f]['packet_name'],physical_LF=a,sha256=files[f]['sha256'],original_name=f)
    if len(ns)>1:result['physical_LF_end']=ns[-1]
    return result
def txt(f,n):return lines[f][n-1]
def parsed(f,n):
    s=txt(f,n)
    return ast.literal_eval(s[s.index('['):])
received={}
for l in (here/'evidence.txt').read_text().splitlines():
    if l.startswith('{"'):
        r=json.loads(l)
        assert all(c['status']==0 for c in r['commands'])
        if r['receipt']:
            assert r['byte_match']
            received[r['receipt']]=r
assert len(received)==12
R='Ramanujan'; M='Mertens'
sup='supported_at_stated_trust_tier'
base='baseline_retained'
inc='incomplete_with_specific_missing_step'
false='false_with_specific_counterexample'
cands=[]; portfolios={R:[],M:[]}; rejected={R:[],M:[]}
tier='Pinned originals at written hypotheses; numerical checks where specified at ordinary directed/integer execution trust.'
qrh='OpenAIQRH p.4 Thm. 1.1; FiniteRH p.2 Thm. 1; FKS p.8 Thm. 3.2; PT PNT p.4 Lemma 2.'
density=' FKS pp.7–8 Cor. 2.9 (2.17), p.26 Table 8, a1=.77, at asserted corollary/table trust; no instantiation of Theorem 2.7 at δ<1.'
ch='CH2 p.3 Cor. 1.2–1.3, p.35 Lemma 9.2 ψ only; FiniteRH p.2 Thm. 1, p.4 Cor. 1, p.5 §3.3 as eligible.'
d='CH2 p.41 (A.2)–(A.4), p.43 Cor. B.3 and first ordinate, p.44 B.5, Prop. B.8; QRH edge and FiniteRH height as in S-D01.'
dus='Dusart2018 p.11 Thm. 4.2, p.13 Cor. 4.5, pp.17–20 Thms. 5.6–5.9 at exact endpoints.'
gap='Dusart2018 pp.13,15 §5.1, Thm. 5.1 proof, Cor. 5.2; FiniteRH p.5 §3.3 for repair; S-D, S-CH, S-D01 as eligible.'
finite='DudekPlatt1407.1901v1 p.2 Galway report, §3.1 pp.8–10 Lemma 3.4 integer cases; PT PNT p.3 Thm. 2 for comparison only.'
def add(id,family,f,n,statement,domain,*,s=None,der=None,impl=(),receipts=(),mode=None,strict='non-strict bounds unless separately specified',units='real',compare=None,status=sup,gaptext=None,keep=(),trust=None,port=True):
    ids=(R,M) if family=='Both' else (family,)
    if mode=='density':
        s=(s or '')+density
    assumption=('B0; neither D01 nor D02 is needed.' if mode!='density' else 'B0 including FKS Corollary 2.9/Table 8 at published tabulated-assertion trust; neither D01 nor D02.')
    defaultcomp={'Both':'Same B0 versus B0+D01 under S-D01.',R:'B0 profile on its exact domain; compare original sign statements and preserve compact/ray tradeoffs by maximum.',M:'B0; compare same-error coefficients only on common domains and retain earlier onsets and differing shapes by minimum.'}[family]
    row=dict(claim_id=id,family=family,written_source=loc(f,n),exact_statement=statement,assumptions=assumption,full_domain=domain,strictness=strict,real_or_integer=units,baseline_comparison=compare or defaultcomp,source_locators=s or 'Self-contained from supporting claim rows and elementary analysis.',derivation_check=der or 'See review.md for the checked analytic derivation and joins.',implemented_readbacks=[loc(*i) for i in impl],numerical_obligations=('Check all directed intervals/eligible endpoints, plus stated analytic monotonicity or complete gap coverage.' if receipts else 'No new empirical test is a premise; analytic/source derivation or cited dependency receipts.'),actual_verification_receipts=[dict(file='evidence.txt',receipt=x,stdout_sha256=received[x]['expected_sha256']) if x in received else dict(file=x) for x in receipts],retained_valid_branches=list(keep),M_status=status,precise_gap_or_counterexample=gaptext,propagation=dict(input_used=False,where_it_changes_proof='No change: S-D01 dominates D01 everywhere eligible.',matched_comparison='B0 and B0+D01 tie as premise sets; no D02 comparison available.'),V_status='Lean/Blueprint/kernel and source-first PV not checked or claimed here; ordinary executed certificates are separate.',remaining_trust=trust or tier)
    cands.append(row)
    for ff in ids:
        if status in [inc,false]:rejected[ff].append(id)
        elif port:portfolios[ff].append(id)
def literal(id,family,f,n,domain,**kw):
    nums=[n] if isinstance(n,int) else range(n[0],n[1]+1)
    add(id,family,f,n,'\n'.join(txt(f,j) for j in nums),domain,**kw)
add('S-D01','Both','foundation.md',(7,11),'For every real x≥exp(200), |ψ(x)−x|<.005 x^(7/8)(log x)^2; thus B0 implies D01.', 'x≥exp(200), inclusive',s=qrh,strict='strict .005 estimate; implies weak 1/64',impl=[('check.py',(95,119)),('check.py',(130,133))],receipts=['gap_basic_evidence.txt'],der='Truncation eligibility persists; normalize each positive term by L² and apply monotonicity.',compare='Exact 0.32 coefficient ratio on whole input ray; equality of premise consequences, not blind baseline.')
literal('S-QB','Both','repair.md',(23,28),'L≥40 for bound, L≥240 derivative, L≥241 normalized bound and L≥1200 normalized decrease',s=qrh,impl=[('repair_check.py',(9,15)),('repair_check.py',(41,62))],receipts=['repair_gap_basic_evidence.txt'],der='Both-sign counting split by symmetry; normalized polynomial maximum plus exponential.')
literal('S-q','Both','foundation.md',(15,37),'s∈[.8,.875], t≥H; ψ bound at L≥110',s=qrh,mode='density',impl=[('check.py',(50,53)),('check.py',(97,110)),('check.py',133)],receipts=['gap_evidence.txt'],der='Count integral, F slope and endpoint, left edge limit, layer cake, decreasing ray.')
literal('S-QD','Both','repair.md',(32,42),'s∈[.8,.875], t≥H; ψ bound at L≥110',s=qrh,mode='density',impl=[('repair_check.py',(17,40))],receipts=['repair_gap_basic_evidence.txt'],der='Taylor degree four integrated exactly, continuous derivative enclosures and full layer cake. QB proof does not require this table.')
literal('S-D','Both','foundation.md',(41,60),'D formula x>1; d bounds x≥2 with a≥0',s=d,impl=[('check.py',(60,61)),('check.py',(118,119))],receipts=['gap_basic_evidence.txt'],der='Perron residues, boundary control, γ⁻² and Fubini.')
literal('S-Dstar','Both','repair.md',(46,53),'Same integrated bounds and domains as S-D; R1 used from L≥34',s=d,impl=[('repair_check.py',(47,50)),('repair_check.py',(65,66)),('repair_check.py',83)],receipts=['repair_gap_basic_evidence.txt'],der='ξ log derivative quotient contour gives both-sign positive real weight bound with finite-height restriction.')
literal('S-CH','Both','foundation.md',(64,68),'Cor.1.3 x≥1; Cor.1.2 x>max(T,10^9), 10^7≤T≤H*; further bounds in their separate domains',s=ch+' FKS p.2 Cor.1.4 and pp.2,24–25 Thms.1.1–1.2 and Tables 5–6, at stipulated x0 and R.',impl=[('check.py',(54,59))],receipts=['pdf_evidence.txt'],der='Coth centering and exact weighted normalization. Exclude Lemma 9.2 weighted line; retain signed ψ and distinct θ sources.')
literal('S-CHtrial','Both','repair.md',(68,72),'Eligible repair trials at x≥10^13; shifted argument separately',s=ch,impl=[('repair_check.py',(68,83))],receipts=['repair_gap_basic_evidence.txt','repair_mertens_evidence.txt'],der='Capped T≤H*; first be eligible then minimize.')
add('R-old-source-real',R,'ramanujan.md',13,'Source literal positivity on N<x≤exp(58) (quoted and rejected, not asserted by the candidate).','N<x≤exp(58)',strict='strict positivity',s='PT PNT p.3 Thm. 2',status=false,gaptext='At x=38358837682.1, R ∈ (−7974585.083,−7974585.082). Exact prime counts and directed interval in evidence.txt.',keep=['R-cell','R-connected','R-source-tails'],impl=[('check.py',(206,220)),('small_end.cpp',(8,26))],receipts=['gap_basic_evidence.txt','evidence.txt'])
add('R-retired-pi',R,'prior_ramanujan.md',77,'Historical cited π-error minimum |π−li|/x≤L exp(−L/2)/(8π) under finiteRH source; retired.', 'Historical uses individually at L from 34 through 58; not an active claim.',s='FiniteRH p.4 Cor. 1, PDF object 112 stream 114 lines 417–424.',status=inc,gaptext='Original prints log², not log¹. No need to assume the historical term; corrected checks and closed-cell redundancy audit.',keep=['R-R3','R-pointwise-repair','R-fixed-old-0','R-fixed-new-0'],impl=[('prior_check.py',69),('explore_gap.py',12),('check.py',(62,69)),('source_audit.py',(14,27))],receipts=['source_audit_evidence.txt','pdf_evidence.txt','historical_replay_evidence.txt'])
add('R-source-tails',R,'ramanujan.md',54,'Retain PT PNT reported eventual sign from exp(3915) and DP unconditional sign from exp(9658); candidate also gives an independent proof on both rays.', 'inclusive stated tails',status=base,s=finite+' DP p.2 Theorem 1.2; PT PNT p.3 Thm.2.',strict='R>0',keep=['R-connected'])
literal('R-cell',R,'ramanujan.md',(56,57),'[N,N+1], including both ends; local zero bracket and derivative; quantitative lower bound for r<x≤N+1',strict='R(r)=0; strict R(x)>66000000(x−r) for r<x≤N+1',s='Real-domain definitions and elementary prime arithmetic; no historical sieve for the cell.',impl=[('small_end.cpp',(8,26)),('check.py',(206,220))],receipts=['gap_basic_evidence.txt','evidence.txt'],der='Floor quotient sieve, monotonicity and directed decimal endpoint checks.')
add('R-connected',R,'ramanujan.md',(9,13),'Unique root in last unit cell N+.217926<r<N+.217927; R(r)=0, R(x)>0 for x>r; N fails, least inclusive integer onset N+1.', 'x>r (strict sign), separately x=r; integer n≥N+1',strict='strict except R(r)=0',units='real and separately integer',s=finite,impl=[('check.py',(206,220))],receipts=['gap_basic_evidence.txt','repair_gap_basic_evidence.txt'],der='Local analytic cell; inherit prime cases below 10¹¹ and integer cases to 1.15·10^16, lift integers by monotonicity on [n,n+1), overlap analytic ray.',trust='Published finite prime/integer sign output inherited; no full RH. Without that trust retain R-cell and analytic rays.',keep=['R-cell','R-fixed-new-0'])
literal('R-sawtooth',R,'ramanujan.md',50,'real x≥n=floor x≥N+1',s=finite,strict='strict lower bound',der='At n inherit or prove R(n)>0; π(x)=π(n), π(x/e)≥b_n.')
literal('R-sawtooth-int',R,'repair.md',(9,13),'real n≤x<n+1, integer n≥N+1',s=finite,strict='non-strict bound by strictly positive RHS',der='π(n) integer strictly below sqrt(a_n b_n), so ≤ceil(sqrt(a_n b_n))−1.')
literal('R-R1',R,'ramanujan.md',(63,68),'L≥34 in the proof-bearing uses',s=d,impl=[('check.py',68),('source_audit.py',(28,30))],receipts=['source_audit_evidence.txt'],der='Integration by parts splitting at e^16; factors 4 and 2.5 on exponential terms.')
literal('R-R2',R,'ramanujan.md',(70,75),'L≥34 per π argument, choose each b/sign branch on its real eligibility',s=gap,impl=[('check.py',(62,69))],receipts=['gap_evidence.txt','gap_basic_evidence.txt'],der='J−π between the stated two prime-power expressions.')
literal('R-R3',R,'ramanujan.md',(77,87),'Both argument restrictions; conservative active starts L≥36.56 (n=20), L≥81 (n=30)',strict='strict pointwise lower bound',s=gap,impl=[('check.py',(70,85)),('check.py',(120,126)),('check.py',(162,173))],receipts=['gap_evidence.txt','gap_basic_evidence.txt'],der='Calibrated PV li bracket, positive shifted-binomial remainder; upper π bracket nonnegative.')
literal('R-pointwise-repair',R,'repair.md',(68,76),'L≥36.4 for (20,4), L≥96 for (50,3), at separate pointwise source cutoffs',strict='strict R3 lower bound',s=gap,impl=[('repair_check.py',(65,100)),('repair_check.py',(117,122))],receipts=['repair_gap_basic_evidence.txt','repair_gap_evidence.txt'],der='Smaller I*, three cutoffs and eligible Q; take maximum with old valid R3.')
add('R-asymptotic',R,'repair.md',64,'g(L)=1+14/L+O(L^(-2)); no constant >1 bounds g from below on an entire ray.', 'L→∞',s=gap,strict='asymptotic with upper and lower remainders',der='Fixed-order asymptotic PV li and exponentially decreasing π remainder at both arguments.')
for i,(new,c,old) in enumerate(zip('36.554 36.786 36.988 37.554 37.790 38.520 38.682 39.394 39.504 39.996'.split(),'0 .11 .20 .42 .50 .71 .75 .90 .92 1'.split(),'36.56 36.8 37 40 40.23 41 41.15 41.9 42 42.5'.split())):
    add('R-fixed-old-'+str(i),R,'ramanujan.md',19+i,f'g(L)>{c}',f'L≥{old}',strict='strict',s=gap,impl=[('check.py',(151,152)),('check.py',(174,205))],receipts=['gap_basic_evidence.txt','gap_evidence.txt'])
    add('R-fixed-new-'+str(i),R,'repair.md',(59,62),f'g(L)>{c}',f'L≥{new}',strict='strict',s=gap,impl=[('repair_check.py',(123,135)),('repair_gap_basic_evidence.txt',3)],receipts=['repair_gap_basic_evidence.txt','gap_basic_evidence.txt'],compare=f'Strictly earlier B0 sufficient onset than {old} at same c; identical with D01.')
for id,mode,f,n,m,domain,rc in [
 ('old-1d','density','ramanujan.md',36,1,'L≥47.05','gap_evidence.txt'),
 ('old-1b','basic','ramanujan.md',36,1,'L∈[47.05,60] or L≥400','gap_basic_evidence.txt'),
 ('old-2','basic','ramanujan.md',38,2,'52.075≤L≤125','gap_basic_evidence.txt'),
 ('old-3','basic','ramanujan.md',38,3,'57.375≤L≤91.50','gap_basic_evidence.txt'),
 ('old-4','basic','ramanujan.md',38,4,'63.50≤L≤71.75','gap_basic_evidence.txt'),
 ('new-1d','density','repair.md',66,1,'L≥47.040','repair_gap_evidence.txt'),
 ('new-1b','basic','repair.md',66,1,'L∈[47.040,190.8] or L≥271.2','repair_gap_basic_evidence.txt'),
 ('new-2','basic','repair.md',66,2,'52.075≤L≤125.2','repair_gap_basic_evidence.txt'),
 ('new-2d','density','repair.md',66,2,'L≥220.8','repair_gap_evidence.txt'),
 ('new-3d','density','repair.md',66,3,'L≥254','repair_gap_evidence.txt'),
 ('new-4','basic','repair.md',66,4,'63.300≤L≤72.050','repair_gap_basic_evidence.txt')]:
    add('R-window-'+id,R,f,n,f'g(L)>P_{m}(L), P_m=Σ_{{j=4}}^{{4+m}} c_j L^(4−j) with c_j as in ramanujan.md 34.',domain,strict='strict on closed interval/ray',s=gap,mode=mode,impl=[('check.py',(174,205))] if f=='ramanujan.md' else [('repair_check.py',(109,163))],receipts=[rc],keep=['R-window-old-3'] if id=='new-4' else [])
old=[200,225,258,292,327,362,398,434,470,506,542,578,615,652,695,730,770,810,850,890,930,970,1010,1050,1100]
for mode,rc,ln in [('basic','repair_gap_basic_evidence.txt',4),('density','repair_gap_evidence.txt',3)]:
    for m,v in enumerate(parsed(rc,ln)):
        add(f'R-tail-new-{mode}-{m}',R,rc,ln,f'g(L)>P_{m}(L)',f'L≥{v}',strict='strict inclusive onset',s=gap+' '+qrh,mode=mode,impl=[('repair.md',(66,76)),('repair_check.py',(102,115)),('repair_check.py',(136,148))],receipts=[rc],der='Verified endpoint with monotone scaled loss using both L and L−1; surplus not weakened when dropping positives only.')
    for m,v in enumerate(old,1):
        v+=200 if mode=='basic' else 0
        add(f'R-tail-old-{mode}-{m}',R,'ramanujan.md',50 if mode=='basic' else 44 if m<14 else 48,f'g(L)>P_{m}(L)',f'L≥{v}',strict='strict inclusive onset',s=gap+' '+qrh,mode=mode,impl=[('check.py',(151,173)),('check.py',(200,205))],receipts=['gap_basic_evidence.txt' if mode=='basic' else 'gap_evidence.txt'],der='Old decreasing scoped loss via 1.14 and 2.081, shifted q eligible, monotone surplus.')
add('R-tail-basic-old-0',R,'ramanujan.md',89,'g(L)>1 after the old basic compact join.', 'L≥340',strict='strict',s=gap,impl=[('check.py',(190,205))],receipts=['gap_basic_evidence.txt'])
literal('R-failed-tests',R,'repair.md',107,'anchor 32; L=160 (density order 2), L=210 (basic order 1)',strict='no inequality counterexample claimed',impl=[('source_audit.py',(34,44))],receipts=['source_audit_evidence.txt'],port=False,der='Recorded failures of chosen sufficient tests only.')
literal('M-normalization',M,'mertens.md',(3,14),'real x≥2',s=dus,der='Prime tails and γ normalization agree exactly with source; P and Q reciprocal.')
for nm,error,v,Lpow,c in [('weighted','|w|',912560,2,'.300'),('reciprocal','|r|',2278383,3,'.2'),('products','both raw relative errors',2278382,3,'.2')]:
    add('M-source-'+nm,M,'mertens.md',110,f'{error}≤{c}/L^{Lpow}',f'x≥{v}',status=base,s=dus)
literal('M-M1',M,'mertens.md',(74,88),'real x≥2 where eligible b and finite/integrable analytic estimates chosen',s=dus+' '+d,der='Stieltjes sum, W,U,V strictly above x at powers, and log-weighted integrated error.',impl=[('mertens_check.py',(12,15)),('repair_mertens.py',(19,23))])
literal('M-M2',M,'mertens.md',(90,94),'x≥8 generic η; special uniform finite-RH eta_v for 8000≤√x≤exp(58)',s=ch+' '+dus,impl=[('mertens_check.py',(6,11))],receipts=['mertens_evidence.txt'],der='Exact squares, split k≥3; bound and lower square term with correct Stieltjes endpoints.')
literal('M-log-tail',M,'mertens.md',(96,101),'same eligible eta_j domains as M-M2',s=dus+' '+ch,der='Integrate log-weighted squares directly, divide remainder by L and shift lower V by telescoping integer bound.')
literal('M-theta-option',M,'mertens.md',(103,108),'eligible integrable θ error majorant for all t≥x; k>1 for single power row',s=dus+' '+ch,der='θ source identities, analytic integrals and eligibility intersections.')
add('M-Z1-option',M,'mertens.md',108,'Centered Z1=ΣΛ(n)/n−L+γ alternative shared bound B1(x)/L+∫_x^∞B1(t)/(t log²t)dt.', 'x≥2, B1 from eligible branches on full forward domain',s='CH2 p.3 Cor.1.2–1.3 centered weighted branch; M-M1.',der='Integrate dZ1/log t by parts; signed log tails then added.')
literal('M-envelope',M,'mertens.md',110,'x≥2; only eligible branches',s=dus+' '+ch,der='Intersection, exact exponential endpoints, and min with every eligible table/direct branch.')
literal('M-W3',M,'repair.md',(86,91),'generic x≥16 with eligible uniform eta; signed strip 64000000≤x≤10^13',s=ch+' '+dus,impl=[('repair_mertens.py',(6,17)),('repair_mertens.py',(30,31))],receipts=['repair_mertens_evidence.txt'],der='Split squares/cubes/fourth powers and signed integral to 10^19, with tiny remaining Gas tail.')
literal('M-envelope-repair',M,'repair.md',93,'x≥2, applicable signed pointwise/finite/table branches only',s=ch+' '+dus,der='Improved shared errors; signed conversions after intersection, no incorrect extrapolation.')
literal('M-constants',M,'mertens.md',(114,116),'J=64000000, eta uniform on t≥J, n=10^6 for γ',s=ch+' '+dus,impl=[('finite.cpp',(78,84)),('check.py',(113,116)),('mertens_check.py',(16,23))],receipts=['finite_evidence.txt','mertens_evidence.txt'],der='Trapezoid harmonic interval and Stieltjes prime-series tail outward bounds.')
literal('M-constants-repair',M,'repair.md',97,'J₂=256000000, eta uniform on t≥J₂',s=ch+' '+dus,impl=[('finite_frontier.cpp',(82,88)),('repair_mertens.py',(24,31))],receipts=['frontier_evidence.txt','repair_mertens_evidence.txt'])
literal('M-finite-pointwise-old',M,'mertens.md',118,'2≤x≤64000000 by exact prime sums/logs',s='M-constants',impl=[('finite.cpp',(10,38))],receipts=['finite_evidence.txt'],der='Pointwise prescription, not run of log-log executable at x=2.')
add('M-finite-pointwise-new',M,'repair.md',97,'Same exact finite prescription, extended to J₂.', '2≤x≤256000000',s='M-constants-repair',impl=[('finite_frontier.cpp',(14,41))],receipts=['frontier_evidence.txt'],der='Exact pointwise prescription uses constant intervals; table scanner starts at 900000.')
for n in range(24,48):
    x,c,e=[a.strip() for a in txt('mertens.md',n).strip().strip('|').split('|')]
    for coeff,labels in [(c,('P','Q') if 'products' in c else ('r','P','Q')),(e,('w',))]:
        if not coeff:continue
        val=coeff.split()[0]
        for field in labels:
            add(f'M-old-{n}-{field}',M,'mertens.md',n,f'{field} absolute error≤{val}/L^{2 if field=="w" else 3}',f'real x≥{x}',s=ch+' '+dus,impl=[('finite.cpp',(42,67)),('finite.cpp',(69,106)),('finite_evidence.txt',n-23),('mertens_check.py',(16,43))],receipts=['finite_evidence.txt','finite_ubsan_evidence.txt','mertens_evidence.txt'],der='Entire closed analytic join plus signed monotone prime gaps, including onset inside gap and composite endpoint.')
for n in range(2,94):
    c,*xs=map(int,txt('frontier_evidence.txt',n).split())
    for j,(field,x) in enumerate(zip(('w','r','P','Q'),xs)):
        add(f'M-frontier-{c}-{field}',M,'frontier_evidence.txt',n,f'{field} absolute error≤({c}/1000)/L^{2 if j==0 else 3}',f'x≥{x} inclusive real',s=ch+' '+dus,impl=[('repair.md',(80,82)),('finite_frontier.cpp',(44,72)),('finite_frontier.cpp',(74,111)),('repair_mertens.py',(24,73))],receipts=['frontier_evidence.txt','frontier_ubsan_evidence.txt','repair_mertens_evidence.txt'],der='Separate directional gap bins; 256m join <.045 and remaining bridges cover all x.')
for n,(x,c) in enumerate(zip([64000000,82000000,115000000,180000000,300000000,600000000],['.0868','.079','.070','.060','.050','.040'])):
    add(f'M-old-analytic-{n}',M,'mertens.md',(49,53),f'|w|≤{c}/L² and |r|,|relative P|,|relative Q|≤{c}/L³',f'real x≥{x}',s=ch+' '+dus,impl=[('mertens_check.py',(24,43))],receipts=['mertens_evidence.txt'])
for id,f,n,c,code,rc in [('old','mertens.md',55,'2.151',('mertens_check.py',(31,34)),'mertens_evidence.txt'),('repair','repair.md',83,'1.939',('repair_mertens.py',(24,36)),'repair_mertens_evidence.txt')]:
    add('M-strip-'+id,M,f,n,f'|w|≤{c}/√x, r and both relative product absolute errors≤{c}/(√x L).','64000000≤x≤10^13',s=ch+' '+dus,impl=[code],receipts=[rc],der='High-zero weighted factor bounded at right endpoint, rest at left.')
for j,(x,c) in enumerate(parsed('repair_mertens_evidence.txt',2)):
    add(f'M-post-{j}',M,'repair_mertens_evidence.txt',2,f'Both coefficients c=d={c} for all four scaled errors.',f'x≥{x}',s=ch+' '+dus,impl=[('repair.md',83),('repair_mertens.py',(37,73))],receipts=['repair_mertens_evidence.txt'],der='At most .0097 after strip, below every row; strict numerical slack before inclusive onset bound.')
for mode,n in [('basic',3),('density',5)]:
    for L,c in parsed('repair_mertens_evidence.txt',n):
        add(f'M-mid-{mode}-{L}',M,'repair_mertens_evidence.txt',n,f'Both coefficients c=d={c} for w at L^-2 and other three errors at L^-3.',f'log x≥{L}',s=qrh+' '+ch+' '+dus,mode=mode,impl=[('repair.md',(83,95)),('repair_mertens.py',(47,73))],receipts=['repair_mertens_evidence.txt'],der='Backward maxima of closed evaluated cells through 420; monotone bound onward.')
for id,mode,v,c,p,f,n,code in [('old400','density',400,'.014',0,'mertens.md',58,('mertens_check.py',(44,56))),('old500','basic',500,'.005001',2,'mertens.md',59,('mertens_check.py',(44,56))),('repair241','basic',241,'.001285',2,'repair.md',84,('repair_mertens.py',(84,89)))]+[
    (f'oldD{L}','density',L,c,0,'mertens.md',(64,66),('mertens_check.py',(44,56))) for L,c in zip([200,224,272,312,376,493,773,2354,4321,32507],['.020','.018','.016','.015','.014','.013','.012','.011','.0108','.0106'])]+[
    (f'newD{L}','density',L,c,0,'repair_mertens_evidence.txt',6,('repair_mertens.py',(75,83))) for L,c in parsed('repair_mertens_evidence.txt',6)]+[
    (f'newB{L}','basic',L,c,2,'repair_mertens_evidence.txt',8,('repair_mertens.py',(90,96))) for L,c in parsed('repair_mertens_evidence.txt',8)]:
    add('M-power-'+id,M,f,n,f'|w|≤{c} exp(−L/8)L^{p}; |r| and both relative product errors≤{c} exp(−L/8)L^{p-1}',f'L≥{v}',s=qrh+' '+dus,mode=mode,impl=[code],receipts=['mertens_evidence.txt' if id.startswith('old') else 'repair_mertens_evidence.txt'],der='Normalized supplementary terms decrease on entire ray; positive denominator and uniform basic maximum/monotonicity as appropriate. Compare shapes on overlap, not coefficients alone.')
add('M-limit-old',M,'mertens.md',68,'Density majorant for w and L times other errors, after multiplying by x^(1/8), tends to .010570000003.', 'L→∞, named density branch only',mode='density',s=qrh,der='Only q limiting coefficient and high-zero term of d survive; exponential denominator tends to 1.')
add('M-limit-repair',M,'repair.md',84,'Improved analogous density normalized majorant tends to .010445+3·10^−12.', 'L→∞, named density branch only',mode='density',s=qrh,der='Same argument with Q_D and d_*.')
literal('M-trials',M,'mertens.md',130,'finite trial inputs to 64m; tested inequality failures are not counterexamples',impl=[('finite_trials.cpp',(42,45)),('finite_trials.cpp',(66,104))],receipts=['finite_trials_evidence.txt','ancillary_trial_evidence.txt'],port=False,der='Original failed tests replay; assessor parameter-only single case reproduces 827 and 18002111.')
# Shared mathematical statements are assessed separately in each family.
# Keep the identical physical locator and evidence, but assign unique row IDs.
shared={row['claim_id'] for row in cands if row['family']=='Both'}
suffix={R:'-R',M:'-M'}
expanded=[]
for row in cands:
    for f in (R,M) if row['family']=='Both' else (row['family'],):
        rr=copy.deepcopy(row)
        rr['family']=f
        if rr['claim_id'] in shared:
            rr['claim_id']+=suffix[f]
        for key,val in list(rr.items()):
            if isinstance(val,str) and key not in {'claim_id','exact_statement'}:
                rr[key]=re.sub(r'(?<![\w-])S-[\w]+(?![\w-])',lambda m:m[0]+suffix[f] if m[0] in shared else m[0],val)
        rr['retained_valid_branches']=[i+suffix[f] if i in shared else i for i in rr['retained_valid_branches']]
        for key,val in list(rr['propagation'].items()):
            if isinstance(val,str):rr['propagation'][key]=val.replace('S-D01','S-D01'+suffix[f])
        expanded.append(rr)
cands=expanded
for f in (R,M):
    portfolios[f]=[i+suffix[f] if i in shared else i for i in portfolios[f]]
    rejected[f]=[i+suffix[f] if i in shared else i for i in rejected[f]]
assert all(row['family'] in (R,M) for row in cands)
assert len({row['claim_id'] for row in cands})==len(cands)
fam={}
for f in (R,M):
    fam[f]=dict(strongest_supported_portfolio=portfolios[f],rejected_or_incomplete_claims=rejected[f],remaining_assessment_work=[],summary=('Open last-root sign ray at inherited integer computation trust; strict real fixed and compact/tail profiles to order 45 with distinct basic/density modes. Retired citation and false literal source endpoint listed separately.' if f==R else 'Directional finite frontier through 256m joined to all real tails, both products and both prime sums, signed pointwise intersections and retained original rows. Basic and literature-density refinements.'),input_effect='no_additional_improvement')
out=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=idx['candidate_id'],assessment_complete=True,all_claims_inventoried=True,reviewed_source_hashes=files,source_bibliography=orig['sources'],effort_verification_commands=[
    'Non-login /bin/bash: pwd; ls -l /task/{INPUT_CONTRACT,RUNTIME_PATHS,CANDIDATE_INDEX}.json (ls unavailable, status 127); /usr/bin/python3.10 readers confirmed cwd and readability.',
    '/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out /work/c',
    'Offline indexed PDF/text inspection, LF physical line reads, diffs on every prior_* version with an active counterpart.',
    'cd /work/submission; /usr/bin/python3.10 reproduce.py > evidence.txt 2> replay_stderr.txt (actual subprocess commands and times in evidence.txt).',
    'cd /work/submission; /usr/bin/python3.10 pdf_readback.py > pdf_evidence.txt',
    'cd /work/submission; /usr/bin/python3.10 ancillary_trial.py > ancillary_trial_evidence.txt',
    'cd /work/submission; /usr/bin/python3.10 historical_replay.py > historical_replay_evidence.txt',
    'cd /work/submission; /usr/bin/python3.10 make_inventory.py'
],family_assessments=fam,claims=cands,no_other_arm_or_ranking_seen=True,new_core_math_salvage_performed=False,original_candidate_bytes_changed=False)
(here/'review.json').write_text(json.dumps(out,ensure_ascii=False,separators=(',',':'))+'\n')
print(len(cands),'claims;',len(portfolios[R]),len(portfolios[M]),'portfolio/dependency IDs')
