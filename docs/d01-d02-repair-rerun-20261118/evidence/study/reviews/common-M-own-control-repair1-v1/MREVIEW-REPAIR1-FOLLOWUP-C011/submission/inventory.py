
from pathlib import Path
from fractions import Fraction
import json,hashlib,re,ast
p=Path('/work/submission'); t=Path('/task')
ix=json.loads((t/'CANDIDATE_INDEX.json').read_text())
rows={r['original_name']:r for r in ix['candidate_files']}
src=json.loads((t/'SOURCE_INDEX.json').read_text())['sources']
def digest(f): return hashlib.sha256(f.read_bytes()).hexdigest()
for r in rows.values(): assert digest(t/r['packet_name'])==r['sha256']
for s in src:
    for k in ['pdf','text']:assert digest(Path('/corpus/originals')/s[k])==s[k+'_sha256']
def find(f,L):
    u=rows[f]
    lines=(t/u['packet_name']).read_bytes().split(b'\n')
    i=int(str(L).split('-')[0])
    assert 1<=i<=len(lines) and lines[i-1].strip(),(f,L)
    return dict(file=u['packet_name'],physical_LF=i,sha256=u['sha256'])
def receipt(*files):
    return [dict(file=f,sha256=digest(p/f)) for f in files]
R='Ramanujan'; M='Mertens'
OK='supported_at_stated_trust_tier'; EQ='equivalent_or_weaker'; BASE='baseline_retained'
BAD='false_with_specific_counterexample'
B='B0: seven original papers at exact stated domains and literature/computation trust; no full RH.'
D='B1: B0 + exact D02 |ψ(x)−x|≤x^(27/32)(log x)^2/64, all real x≥exp(200).'
AB='B0 within-method ablation; exact D01 not supplied.'
FD='FKS Cor.2.9/(2.17), PDF pp.7–8 LF586–609, Table 8 p.26 LF3139–3258'
FX='FKS Thm.3.2/(3.2), p.8 LF631–642; FKS Remark 3.3 LF643–653'
Q='OpenAIQRH Thm.1.1, PDF p.4 LF255–262; FiniteRH Thm.1 PDF p.2 LF47–49'
H='CH2 Cor.1.2/1.3 p.3 LF193–240, Prop.9.1 pp.34–35 LF4982–5012, eq.(9.2), Cor.9.3 p.36 LF5273–5355'
PT='PT PNT Thm.1/Cor.1 pp.2–3 LF77–117; Table 1 p.3 LF135–201'
A='PT PNT p.8 LF695–705 Büthe absolute; FiniteRH Cor.1 p.4 LF138–150; Dusart p.13 LF1141–1155 PV'
Z='PT PNT Lem.2 p.4 LF235–246; Dusart Cor.4.5 p.13 LF1132–1136'
C='CH2 Prop.B.8/(B.8),(B.9) pp.46–47 LF6744–6820; FKS Lem.2.1/Remark 2.2 LF276–313; FKS Table 1 LF340–346'
DS='Dusart Thms.5.6–5.7 pp.17–19 LF1479–1585; Thm.5.9 p.19 LF1640–1664'
DT='Dusart Thm.4.2 p.11 LF959–1010'
DP='Dudek–Platt §3.1 p.8 LF589–594; Table 1 p.9 LF647–675; Lem.3.4 p.10 LF698–715'
pv='Not checked in paper-only runtime. No Lean/Blueprint correspondence or source-first PV claimed.'
density='Inherits the stated FKS density corollary; printed δ discrepancy is not independently repaired.'
inherit='Large integer bridge inherited at publication computation trust; no step-by-step execution verification.'
std='Written proof with original literature conclusions and ordinary exact-integer interval replay where shown.'
RE='replay_receipts.json'; AX='ancillary.stdout'; PX='pdf_readback.log'
cs=[]
def add(cid,fam,f,L,s,domain,check,*,impl=(),source=(),trust='',status=OK,dep=None,use=None,comp=None,related=(),gap=None,numerical=None,e=(),kind='real',strict='As displayed',best=True):
    spec=[dict(**find(g,l),physical_LF_range=str(l),restored_basename=g) for g,l in impl]
    cs.append(dict(claim_id=cid,family=fam,written_source=find(f,L),written_source_passage=str(L),
        written_source_restored_basename=f,implemented_formula_readbacks=spec,exact_statement=s,
        assumptions=dep or B,full_domain=domain,strictness=strict,real_or_integer=kind,
        baseline_comparison=(AB+' '+comp if comp else AB),
        source_locators=list(source),derivation_check=check,
        numerical_obligations=numerical or ('Exact script replay and real cell/monotone-tail justification in review.md.' if impl else 'Analytic or inherited source statement; no separate numerical certificate invoked.'),
        actual_verification_receipts=receipt(*e),retained_valid_branches=list(related),
        M_status=status,precise_gap_or_counterexample=gap,
        propagation=dict(input_used=('D02' if use else 'none for this branch'),
            where_it_changes_proof=use or 'Unchanged from B0.',
            matched_comparison=comp or 'Available at B0; not a D02 gain.'),
        V_status=pv,remaining_trust=std+(' '+trust if trust else ''),include_in_best_portfolio=best))
for fam,k in [(R,'R'),(M,'M')]:
    add(k+'-strip',fam,'common.md','3-11','B0 1/8≤β≤7/8; B1 5/32≤β≤27/32.', 'All nontrivial zeros including strip edges',
        'Euler log derivative, meromorphic identity, local uniform Mellin convergence and reflection; eta excludes real zeros.',source=(Q,),dep=B+' '+D,use='Tail exponent in the assumed D02 bound shows no log-derivative pole in Re s>27/32.',comp='Open zero-free half-plane improves before any x evaluation.',kind='complex')
    add(k+'-explicit',fam,'common.md','15-20','T=e^(v/2)/6; FKS signed explicit formula with |r|≤12.546 v e^(−v/2)<3v²e^(−v/2); two-sided reciprocal mass ≤.04v²+2 and <117 through H.', 'Real v≥61', 'Original strict parameter tests, reciprocal mass and conjugation.',impl=(('certificate.py','125-137'),('upgrade.py','17-24')),source=(FX,Q,Z),e=(RE,AX))
    for suffix,file,lf,imp,desc in [
        ('uniform','common.md','24-40',(('certificate.py','30-41'),),'Uniform Z(s) with 12,5 and 1/2000 grid'),
        ('local','common.md',42,(('refine.py','3-33'),),'Prefix-minimum Z_loc(s) with upward row bounds and 1/4000 grid'),
        ('taylor','upgrade.md','143-149',(('upgrade.py','6-33'),),'Degree-four integrated Taylor Z_4(s) on same local grid')]:
        add(k+'-density-'+suffix,fam,file,lf,desc+'; positive endpoint form plus low-zero term and prime-power cap for θ; scaled e^(dv) endpoint nonincreasing on v≥160.', 'v≥61, s-grid from .75 through inclusive strip edge; scaled v≥160',
            'Stieltjes tail, endpoint differences, nonincreasing cumulative weights, negative fifth derivative for new Taylor upper polynomial.',impl=imp,source=(FD,FX,Z,Q),e=(RE,PX),trust=density,dep=B+' '+D,use='D02 changes the common grid upper edge, truncating positive layers.',comp='Strict raw bound-value gain on the same v-ray; Taylor gain by itself improves both sides.')
    add(k+'-strip-free',fam,'common.md','46-49','No-density (3): |eψ(v)|≤(.04v²+2)e^(−dv)+(3v²+117)e^(−v/2).','v≥61','Apply the strip to all high zeros and finite RH to low zeros in (1).',impl=(('certificate.py','151-155'),),source=(FX,Q,Z),dep=B+' '+D,use='Changes d from 1/8 to 5/32.',comp='Strictly decreases the high-zero allowance everywhere on common v≥61.',e=(RE,))
    add(k+'-literal-d02',fam,'common.md',50,'Exact v² e^(−5v/32)/64 bound for |eψ(v)|; +2e^(−v/2) for θ where used.', 'v≥200','Input normalization; no extrapolation.',impl=(('certificate.py','156-159'),('upgrade.py','232-239')),source=(Z,'INPUT_CONTRACT.json'),dep=D,use='Uses both exact D02 coefficient and threshold.',comp='Available in addition to B0; direct matched outputs below.',e=(RE,))
    add(k+'-prime-power',fam,'common.md',40,'0≤ψ(e^v)−θ(e^v)<2e^(v/2) on v≥24.', 'v≥24','Apply Dusart .333 and .5 powers; check division after normalization at the left.',source=(Z,))
    add(k+'-moment',fam,'common.md','52-75','For k(v)=1 or 1/v+1/v², |∫_L^∞ k eψ|≤k(L)[6e^(−L/2)+(400/H)e^(−dL)]≤k(L)B_d(L), with B_d as (4).','L≥39 (prior 61 retained)',
        'Absolute Perron smoothing; contour at .1; residues and square-sum bound; integrate by parts against the signed primitive.',impl=(('checks.py','16-21'),('certificate.py','194-200'),('upgrade.py','34-39'),('upgrade.py','154-175')),source=(C,Q,Z),dep=B+' '+D,use='Strip changes high-zero tail rate d; low zeros and vertical contour unchanged.',comp='Sharper signed moment on the same domain, density-free.',e=(RE,AX))
    add(k+'-CH',fam,'common.md','79-84','CH2 adjusted heights for ψ and weighted u, plus A+114e^(−v/2) all-domain; use finite-RH and Cor.9.3 only on eligible domains.','x≥1 for Cor.1.3; e^v>max(T,10^9), 10^7≤T≤H* for Cor.1.2; other original controls on their supplied domains and portfolio x≥2 as applicable.',
        'Coth shift only in ψ; weighted center v−γ. θ cost takes coefficient 116 on used domain.',impl=(('certificate.py','52-69'),('certificate.py','181-193')),source=(H,Q,A),e=(RE,AX),status=BASE,best=False)
rp='ramanujan.md'; up='upgrade.md'; mm='mertens.md'; cp='certificate.py'; rf='refine.py'; ug='upgrade.py'
add('R-polynomial',R,rp,'5-10','R=exπ(x/e)/L−π(x)^2; F_j=Σ_(n=6)^(j+6)c_n L^(6−n) with written factorial convolution; c_6=1 and later included terms positive.','L>0 for profile; j=0..43 used',
    'Binomial expansion at L−1, convolution at L; cancellation through exponent 5 and positive exact coefficients.',impl=((cp,'16-29'),(ug,'125-135')),e=(RE,AX))
for i,(file,lf,m,a,impl) in enumerate([(rp,'55-60',24,31,((cp,'8-15'),(cp,'138-149'))),(up,78,24,28,((ug,'49-59'),)),(up,'84-89',48,61,((ug,'116-135'),))]):
    add('R-Li-'+str(a),R,file,lf,f'P_{m}(v)≤f(v)≤P_{m}(v)+K/v^{m+2} anchored at {a}, K as declared.',f'v≥{a}',
        'PV Ei Taylor brackets at anchor and ODE sub/supersolution; high order uses the 9/8 inflation.',impl=impl,source=(A,),e=(RE,AX))
add('R-transfer',R,rp,'62-69','Formula (6) with the guard used in its proof: 1−d_i−2/a>0 for all terms.','v≥a; all selected anchors with their source conditions',
    'Anchored partial summation and lower log-derivative bound for the integral kernel.',impl=((cp,'43-44'),(ug,'88-98')),source=(A,H),e=(RE,AX),related=('R-transfer-unguarded',))
add('R-transfer-unguarded',R,rp,'62-67','Unrestricted literal hypotheses of displayed transfer (6) if LF69 guard is not imposed.','In particular a=v=3.9, allowed by literal LF62',
    'The primitive estimate divides by a decay constant that need not be positive.',impl=((cp,'43-44'),),source=(H,Z),status=BAD,
    gap='Use P_a=1 and D=A+116e^(−v/2), valid on v≥3.9. The d_i=1/2 term has 1−d_i−2/a=−1/78 and RHS is <−75 at v=a; LHS nonnegative. All actual anchors ≥24 so this does not reject any profile.',related=('R-transfer',),e=(AX,),best=False)
add('R-repaired-fRH',R,rp,'71-79','Normalized π majorant v e^(−v/2)/(8π) for 24≤v<43 and v²e^(−v/2)/(8π) for 43≤v≤58, including 50 anchor.', 'Exact piecewise ranges; shifts separately',
    'Büthe with PV shift plus comparison at 24 for one log, literal Cor.1 for two logs; source cutoff handled in actual code.',impl=((cp,'46-69'),(cp,'97-106'),(cp,'125-132')),source=(A,),e=(RE,PX,AX))
add('R-signed-base',R,rp,79,'Use U=0 on applicable v≤39.3 in old cells.','Used early cells, not a general all-x claim','Original signed report is applicable and the code tests the complete cell.',impl=((cp,'84-106'),),source=('Dudek–Platt proof of Lem.3.2 p.8 LF561–562',),e=(RE,),status=BASE,best=False)
add('R-full-Buthe',R,up,76,'Full normalized Büthe absolute allowance with +2e^(−v), signed upper allowance 2e^(−v).','Both used arguments through v=43.74 inclusive','PT PNT and FiniteRH give the respective absolute and signed results up to 10^19; normalization checked.',impl=((ug,'47-48'),(ug,'61-87')),source=(A,'FiniteRH p.5 LF182–185'),e=(RE,AX))
add('R-loss',R,rp,'81-91','Scaled loss ≤L^5[V(L−1)+2.07U(L)], plus the stated polynomial slack; upgraded early factor 2.09.', 'Complete finite/late cells of base and upgrade',
    'Linearized square via cap LU<.01; correct endpoint orientations for signs of slack terms and both shifted arguments.',impl=((cp,'18-29'),(cp,'92-119'),(ug,'61-98')),e=(RE,))
add('R-counts',R,rp,'45-51','π(n)=1644673232, π(p*)=632207037, n=38358837682, p*=14111427770; both buckets fixed on [n,n+1).','Two integer counts and local real interval','Descending clustered quotient sieve and directed exact floors.',impl=(('endpoint.py','2-25'),),e=(RE,),kind='integer and real')
add('R-local-root',R,rp,'45-49','Unique r∈(38358837682.2179263651,38358837682.2179263652); R<0 on [n,r), R(r)=0 and R>0 on (r,n+1).','Real [n,n+1)','Constant floor pair, e x/log x strictly increases there; exact bracket signs.',impl=(('endpoint.py','15-25'),),e=(RE,))
add('R-literal-source-counterexample',R,rp,49,'Original PT PNT Thm.2 early real wording cannot be retained literally.','Claimed original n<x≤exp(58)','x=38358837682.1 belongs to its interval but lies below the certified lower bracket for r.',
    source=('PT PNT Thm.2 p.3 LF205–212',),impl=(('endpoint.py','16-25'),),e=(RE,),
    gap='Specific counterexample to the original wording, not the repaired candidate claim; far PT ray unaffected.',related=('R-local-root','R-old-PT','R-exact-sign'),best=False)
add('R-integer-bridge',R,rp,49,'Lift published integer signs to all real [n+1,1.15·10^16].', 'Reported integer segments [n+1,10^11] and [10^11,1.15·10^16], then real lift', 'No full RH; π(x) constant on [k,k+1), and shifted π and scale nondecreasing.',source=(DP,),trust=inherit,kind='integer source, real lift')
add('R-finite-join',R,rp,49,'R>0 on 36.95≤L≤37.2, with 36.95<log(1.15·10^16).','Closed real L cell coverage','Both π arguments covered; analytic interval overlaps reported finite bridge and subsequent margin rays.',impl=(('checks.py','22-23'),(cp,'92-115')),source=(A,H),e=(RE,),strict='Strict.')
add('R-exact-sign',R,rp,49,'Largest real failure r; largest integer failure n; R>0 on (r,∞), e.g. on closed ray from 38358837682.2179263652.', 'Real x>1 and integer restriction',
    'Exact local sign joins published integer lift, then finite analytic interval and F0 tails.',impl=(('endpoint.py','16-25'),('checks.py','22-23'),(cp,'172-180')),source=(DP,A,FX,Q),e=(RE,),trust=inherit,kind='real and integer',strict='Strict after r, equality at r.')
add('R-no-onset-gain',R,rp,41,'No B1 improvement of true connected strict-sign endpoint; no positive normalized constant uniformly just above r.','Right-hand neighborhood and all final strict-sign rays','Actual equality at r; local continuity and exact sign proof.',trust=inherit,related=('R-exact-sign',),best=False)
add('R-normalized-limit',R,rp,39,'L^6 R/x²→1. No fixed constant >1 on a final ray.','Real x→∞','No-density ψ transfer and two-sided shifted/unshifted factorial asymptotics.',source=(FX,Q,Z),best=False)
for k,a,src1 in [('PT',3915,'PT PNT Thm.2 p.3 LF205–212 (far ray only)'),('DP',9658,'Dudek–Platt Thm.1.2 p.2 LF53')]:
    add('R-old-'+k,R,rp,99,f'R>0 on L≥{a}.',f'Closed L≥{a}','Retained original unshifted claim, not the too-broad early wording.',source=(src1,),status=BASE,best=False)
add('R-analytic-glue-F0',R,rp,91,'CH2 finite F0 on [60,280], no-density F0 on [280,∞); attach [42.8,60].','Closed real intervals','Quarter-unit exact cell tests and endpoint decreasing no-density tail.',impl=((cp,'172-180'),(cp,'246-257')),source=(H,Q,FX,Z),e=(RE,),status=EQ,best=False)
add('R-analytic-glue-F1',R,rp,91,'Base F1 join [47.5,48], [48,170], [170,190], then B0 refined tail; B1 retains it. Uniform B0 only [47.5,170] and [192,∞), uniform B1 [47.5,180] and [180,∞).','Closed real segments as stated',
    'Eighth-unit CH/refined cell minima on the missing segment, tested tail; no net final F1 propagation credit.',impl=((cp,'246-257'),(rf,'56-73')),source=(H,A,FD),trust=density,e=(RE,))
for a,c in [('37.2','.005'),('39.4','.05'),('39.9','.25'),('40.9','.60'),('41.9','.84'),('42.8','1'),('37.2','.06')]:
    domain=f'{a}≤L≤39.3' if c=='.06' else f'L≥{a}'
    add('R-margin-'+c,R,rp,39,f'R>{c}x²/L^6 on {domain}.',domain,'Finite closed-cell signs join the larger F0 ray if needed.',impl=((cp,'234-249'),),source=(A,H),e=(RE,),status=EQ,best=False)
for j,a,b in [(2,53,120),(3,58,91),(4,64,71.5)]:
    add(f'R-base-window-F{j}',R,rp,37,f'R>(x²/L^6)F_{j} for {a}≤L≤{b}.',f'Closed [{a},{b}]','Real finite cells, not an assertion about gaps.',impl=((cp,'92-115'),(cp,'246-248')),source=(A,H),e=(RE,))
for j,a in [(0,'30.75'),(1,'34.4'),(2,'38.52')]:
    dom=f'L≥{a}' if j==0 else f'{a}≤L≤43.74'
    add(f'R-upgrade-early-F{j}',R,up,8+j,f'R>(x²/L^6)F_{j} for {dom}.',dom,
        'Full signed and absolute Büthe, guarded shifted providers, Li anchor 28; F0 bridge [43.74,47.5] meets valid density-free ray.' if j==0 else 'Finite whole cells with the full Büthe and signed allowances at both arguments.',
        impl=((ug,'47-87'),(ug,'203-213')),source=(A,H,'FiniteRH p.5 LF182–185'),e=(RE,),strict='Strict, closed onset/window.')
def table(file,i,j):
    lines=(t/rows[file]['packet_name']).read_text().split('\n')
    for ln in range(i,j+1):
        yield ln,[c.strip() for c in lines[ln-1].strip().strip('|').split('|')]
baseR=list(table(rp,19,35)); newR=list(table(up,18,59))
for typ, tb in [('base',baseR),('upgrade',newR)]:
    for l,(j,x,y) in tb:
        j=int(j); f=rp if typ=='base' else up
        imp=((rf,'56-73'),) if typ=='base' else (((ug,'227-231'),) if j<=16 else ((ug,'116-141'),))
        srcs=(A,H,FD,Q,FX,Z) if j else (A,H,Q,FX,Z)
        add(f'R-{typ}-F{j}',R,f,l,f'R>(x²/L^6)F_{j}: B0 L≥{x}; B1 L≥{y}.',f'Two closed real rays with B0/B1 onsets {x}/{y}.',
            'Degree-24 or degree-48 polynomial slack and decreasing scaled error; base F0/F1 joins separately assessed.',impl=imp if j>=2 else ((cp,'246-257'),(rf,'56-73')),
            source=srcs,trust=density if j else '',dep=B+' '+(D if j>=2 else 'B1 retains by inclusion.'),use='Smaller strip b gives smaller late Li-proxy error at both arguments.' if j>=2 else None,
            comp=f'Matched F_{j} onset {x}→{y}.' if j>=2 else 'No change in matched final onset.',
            e=(RE,),strict='Strict, including left endpoint.', status=(OK if typ=='upgrade' or j==1 else EQ), best=typ=='upgrade' or j==1)
U0=[280,192,223,256,290,325,360,396,432,468,504,540,576,613,649,685,722]
U1=[280,180,190,214,240,266,292,318,345,372,399,426,453,480,507,535,562]
for j,(x,y) in enumerate(zip(U0,U1)):
    add(f'R-uniform-F{j}',R,cp,253+(j>0),f'Uniform-grid F_{j} strict tails B0/B1 at {x}/{y}.','Closed real log-rays',
        'Retained plain uniform density acceptance tests; dominated by corresponding better profile.',impl=((cp,'116-120'),(cp,'253-257')),source=(FD,FX,Q,Z),trust=density,
        dep=B+' '+D,use='Boundary change in same former weight grid.',comp=f'Matched uniform tails {x}→{y}; retained but no extra final F0/F1 gain.',e=(RE,),status=EQ,best=False)
for l,(j,x,y) in list(table(up,67,70))+[(93,(1,312,227)),(93,(2,347,254)),(93,(4,421,309)),(93,(8,570,421))]:
    f=rp if l==93 else up
    add(f'R-free-F{j}',R,f,l,f'Density-free R>(x²/L^6)F_{j}: B0 L≥{x}, B1 L≥{y}.',f'Two real closed L rays; y−1≥200',
        'QRH no-density transfer versus literal D02 θ transfer at both arguments, plus polynomial slack and monotone loss.',
        impl=(((cp,'151-171'),) if l==93 else ((ug,'142-152'),)),source=(Q,FX,Z,H),dep=B+' '+D,use='Direct θ majorant uses exact D02 coefficient/threshold after adding prime-power cost.',comp=f'Matched F_{j} onsets {x}→{y}.',e=(RE,))
for l,f,a,j,k in [(37,rp,200,1,2),(37,rp,290,4,6),(37,rp,400,7,10),(61,up,800,18,24),(61,up,1000,23,32)]:
    add(f'R-matched-{a}',R,f,l,f'At L={a} named profile order improves F_{j}→F_{k}.',f'L={a} and comparisons of applicable profiles, not persistence of those two exact maximum orders.',
        'Read onset rows and strict positivity of intervening coefficients; no universal B0 optimality assertion.',source=(FD,),dep=B+' '+D,use='Same as the applicable density table.',comp=f'Fixed L={a}, F_{k}(L)>F_{j}(L).',e=(RE,AX),trust=density,best=False)
add('R-envelope',R,rp,93,'Pointwise supremum of valid profile/π-interval lower bounds, sign and exact local values when applicable; B1 nonworsening.', 'All applicable real x>1; domain guards remain',
    'Intersect valid π intervals at each shifted argument (both true counts nonnegative), use θ endpoint and optionally minimum integrand at a common valid anchor.',source=(A,H,PT,'Dusart Thm.5.1, Cors.5.2–5.3 pp.14–16'),dep=B+' '+D,use='Keep all B0 branches, add applicable B1 ones.',comp='Whole-domain weak order, not general strictness.')
for k,f,l,a,imp,mode in [('refined',rp,95,171,('checks.py','12-15'),'refined density'),('direct',up,72,436,(ug,'195-198'),'direct D02')]:
    add('R-proxy-'+k,R,f,l,f'{mode} allowance beats named B0 at both arguments throughout L≥{a}, via .99q(v)/v.',f'L≥{a} including shifted v=L−1',
        'Use calibrated left checks on both q components; each scaled term decreases; ancillary direct original upper/lower comparison.',impl=(imp,),source=(H,PT,A,'PT PNT Cor.2 p.3 LF127–131 and PV normalization p.8 LF710–712'),
        trust=density+' The stated B0 comparator includes density.' if k=='refined' else 'B1 upper allowance is density-free; reference B0 envelope includes density branches.',
        dep=B+' '+D,use='Refined strip majorant' if k=='refined' else 'Literal D02 at ≥200 anchor and on whole transfer integral.',
        comp=f'Strict improvement of proxy radii at both arguments for L≥{a}.',e=(RE,AX))

add('M-normalizations',M,mm,'5-15','S=Σ1/p−log L−M; W=Σ(log p)/p−L+B3; Δ=log Qraw−γ−log L. M=γ+Σ[log(1−1/p)+1/p], B3=γ+Σ_{p,m≥2}(log p)/p^m; raw relative errors |exp(−Δ)−1| and |exp(Δ)−1|.', 'Real x≥2, sums with p≤x',
    'Matches Dusart exact normalization; product directions reversed for inverse as required.',impl=(('small.py','24-55'),),source=(DS,),e=(RE,))
add('M-power-tails',M,mm,'49-55','W=u+C_w, S=z+C_s, Δ=z+C_Q; 0≤C_w≤G=4e^(−L/2)+10e^(−2L/3), 0≤C_Q≤C_s≤G/L; optional exact square-tail integral.',
    'Real x≥2; exact powers p^m=x counted in main sum','Geometric expansion, split m≥3 by prime against x^(1/3), θ≤2t to bound square Stieltjes tail; divide by log(p^m)>L.',impl=((cp,'196-200'),(ug,'34-39')),source=(DT,DS),e=(RE,))
add('M-partial-summation',M,mm,'57-65','(7): u=eψ−∫eψ; z=eψ/L−∫(v^−1+v^−2)eψ=u/L−∫u(v)/v². θ equivalents for W,S; Δ=S−Σ_{p>x,m≥2}1/(mp^m), subtracted tail ≤4e^(−L)/L.',
    'All real x≥2','Fix the limit via Dusart and prime-power correction; jump convention from partial summation.',source=(DS,DT,Q,FX))
add('M-product-conversion',M,mm,'67-78','(8) with J=N/L and numerator N=E_b^θ+(1+1/L)B_d+G; |W|≤N; S,Δ≤J in magnitude; both product errors ≤J/(1−J) for J<1, or use exact interval endpoints.',
    'Signed moment and chosen ψ bound active; denominator positive at all rate anchors and certified cells','Taylor series comparison; adequate absolute conversion for either sign. Can replace E_b^θ by better valid ψ endpoint.',impl=((cp,'194-200'),(rf,'31-39'),(ug,'25-39')),source=(C,Z,DS),e=(RE,))
add('M-CH-weighted',M,mm,'80-85','For weighted CH2 a+ce^(−L/2), |W|≤a+(c+4)e^(−L/2)+10e^(−2L/3) and |S|,|Δ|≤J=(2a+(c+4+2c/L)e^(−L/2)+10e^(−2L/3))/L.',
    'L≥log 2 where chosen source is active for the whole tail L..∞','Last identity of (7), constant integral and exponential derivative bound; keep full fixed-height family.',impl=((cp,'181-193'),),source=(H,DT),e=(RE,))
for name,file,l0,pars,imp in [
    ('uniform',cp,201,[('160','.0263','.427'),('250','.0182','.292'),('400','.0151','.241')],((cp,'194-203'),)),
    ('base',mm,28,[z for _,z in table(mm,28,30)],((rf,'34-47'),)),
    ('upgrade',up,101,[z for _,z in table(up,101,103)],((ug,'25-39'),(ug,'220-224')))]:
    for i,(a,c0,c1) in enumerate(pars):
        add(f'M-{name}-power-{a}',M,file,l0+(i if name!='uniform' else 0),
            f'For real L≥{a}, |W|<C exp(−dL), |S| and both relative product errors <C exp(−dL)/L; B0 (d,C)=(1/8,{c0}), B1 (5/32,{c1}).',
            f'Closed common real onset {a}', 'Scaled common numerator and relative conversion decreasing on the ray; checked at its left edge.',
            impl=imp,source=(FD,C,DS,FX),trust=density,dep=B+' '+D,use='D02 strip compression and changed d in signed tail.',
            comp=f'B1/B0 radius ratio ({c1}/{c0})exp(−L/32)<1 throughout the common ray.',e=(RE,AX),strict='All four strict, including onset.',
            status=OK if name=='upgrade' else EQ,best=name=='upgrade')
def logcase(cid,file,ln,k,a,b,imp,tf=True,status=OK):
    add(cid,M,file,ln,f'|W|<10^(−{k})/L² and |S| and both relative product errors <10^(−{k})/L³ on B0 L≥{a}, B1 L≥{b}.',
        f'Closed real rays {a}/{b}.','Scaled converted denominator plus L²exp(−dL) for density or L⁴exp(−dL) for log-loss; strict left tests.',
        impl=imp,source=(C,DS,FX)+( (FD,) if tf else () ),trust=density if tf else '',dep=B+' '+D,
        use='Strip boundary gives shorter matched log-format ray.' if tf else 'B1 exact D02 endpoint, signed moment and associated log-loss rate.',
        comp=f'Same η=10^(−{k}), onset {a}→{b}.',e=(RE,),strict='All strict, including onset.',
        status=status,best=status==OK)
ks=(8,10,12,16,20,24)
for k,(a,b) in zip(ks,[(202,178),(240,209),(279,240),(356,301),(432,362),(508,422)]):
    logcase(f'M-uniform-log-{k}',cp,211,k,a,b,((cp,'211-220'),),status=EQ)
for name,file,start,end in [('base',mm,38,43),('upgrade',up,111,116),('free',up,124,129)]:
    for k,(ln,(_,a,b)) in zip(ks,table(file,start,end)):
        logcase(f'M-{name}-log-{k}',file,ln,k,a,b,
                ((rf,'48-55'),) if name=='base' else (((ug,'225-226'),) if name=='upgrade' else ((ug,'240-244'),)),
                tf=name!='free',status=EQ if name=='base' else OK)
for a,c,b in [('23.25','.2',160),('26.5','.05',160),('30.25','.01',160),('36.25','.001',160),('53','1e-6',170),('62','1e-7',215)]:
    add(f'M-old-early-{a}',M,mm,45,f'B0 |W|<{c}/L²; |S| and both relative product errors <{c}/L³ on L≥{a}.',
        f'Real closed ray; join at {b}', 'Fixed-height CH2 weighted-cell proof over closed prefix, then density-based tail.',
        impl=((cp,'181-210'),),source=(H,FD,C,DS),trust=density+' Tail only; finite prefix independent of density.',
        e=(RE,),status=EQ if a in ['53','62'] else OK,best=a not in ['53','62'])
for a,b,k in [('52.9','170',6),('58.3','215',7),('64.4','97.6',8)]:
    dom=f'{a}≤L≤{b}' if k==8 else f'L≥{a} (join at {b})'
    add(f'M-new-early-{a}',M,up,118,f'B0 |W|<10^(−{k})/L²; |S| and both relative product errors <10^(−{k})/L³ for {dom}.',
        dom,'ψ CH2 and finite RH endpoint cells with shorter signed moment, plus B0 tail where asserted.',
        impl=((ug,'154-177'),(ug,'214-219')),source=(H,A,C,DS)+( (FD,) if k!=8 else () ),e=(RE,),
        trust=density+' Tail only.' if k!=8 else 'Finite window only; density-free.')
for name,f,l,c,a,d,s,use in [
    ('old-direct',mm,32,'.015626',200,'5/32',EQ,True),
    ('free-B0',up,120,'.040079',160,'1/8',OK,False),
    ('free-B1',up,120,'.015625000000005',200,'5/32',OK,True)]:
    add('M-'+name,M,f,l,f'|W|<{c} L²exp(−{d}L); for |S| and both relative product errors <{c} L exp(−{d}L).',
        f'Real closed ray L≥{a}','Scale signed tail and prime-power terms before conversion; all corrections decreasing on this ray.',impl=(((cp,'221-226'),) if f==mm else ((ug,'232-239'),(ug,'34-39'))),
        source=(FX,Q,C,DS),dep=(B+' '+D if use else B),status=s,best=s==OK,e=(RE,),
        use='Direct literal ψ endpoint plus signed tail at D02 exponent.' if use else None,
        comp='B1 beats named B0 density-free rate from L=200 in both coefficient and exponent.' if use else 'Density-free B0 comparison bound.')
origM={'S':('.2/L³',2278383,112,'2278382.112','2278382.114','Thm.5.6 p.17 LF1479–1493'),
       'W':('.3/L²',912560,113,'912559.997','912559.998','Thm.5.7 p.18 LF1555–1573'),
       'Q':('.2/L³',2278382,114,'2278381.711','2278381.712','Thm.5.9 p.19 LF1640–1664'),
       'P':('.2/L³',2278382,115,'2278381.575','2278381.576','Thm.5.9 p.19 LF1640–1664')}
for k,(c,a,ln,lo,hi,ori) in origM.items():
    add('M-original-'+k,M,mm,94,f'{k} error ≤{c} for x≥{a}.',f'Real closed ray x≥{a}','Matches original prime-sum or relative-product form as appropriate.',
         source=('Dusart2018 '+ori,),status=BASE,best=False,strict='Non-strict.')
    add('M-exact-onset-'+k,M,mm,ln,f'Least real closed x onset r_{k}∈({lo},{hi}) for error ≤{c}; integer onset remains {a}.',
        f'x≥r_{k} and failure immediately below r_{k}', 'Sieve certifies fixed prime gap, directed values of normalized positive error, strict derivative and sign change; original bound past join.',
        impl=(('small.py','19-74'),),source=('Dusart2018 '+ori,DT),e=(RE,),
        strict='Equality at r, non-strict bound on final closed ray; strict failure immediately before.',kind='real onset and integer restriction')
add('M-constant-enclosures',M,mm,'119-120','g=10^5 γ enclosure from trapezoid; N=8·10^6 sieve and exact M,B3 tail enclosures as displayed.',
    'Finite sieve and full real t≥N tail', 'Recomputed signs using directed arithmetic; θ .2/log²N coefficient eligible; alternating factorial tail and geometric remainder bounds.',
    impl=(('small.py','19-48'),),source=(DT,DS),e=(RE,))
add('M-source-psi',M,mm,91,'Minimum of named valid ψ controls (FKS formulas/rows, PT, Dusart, finite RH, CH2, new analytic variants).',
    'Real x≥2; individual original hypotheses retained, FKS Cor.1.4 only x>2.',
    'Named originals and table re-read; exercised LF-dependent parse and domain/normalization check. See review.md.',
    impl=(('source_rows.py','9-35'),('source_rows.py','70-76')),source=(PT,FD,H,A,'FKS Thms.1.1–1.2 & Cor.1.4 p.2; Tables 5–6 pp.22–23; Dusart Prop.3.2 and Thm.3.3 pp.7–9'),
    dep=B+' '+D,use='Adds analytic D02 strip and exact literal ray to preserved B0 controls.',comp='Nonworsening on full real domain.',e=(RE,AX))
add('M-source-theta',M,mm,92,'θ intervals by subtracting prime-power interval from ψ, intersecting with original Dusart, FiniteRH, PT sources.',
    'Real x≥2 and exact leaf domains','Dusart all rows in Thm.4.2; PT uses A+.1; FiniteRH x>599 and x≤2.169·10^25.',source=(DT,PT,A,Z),
    dep=B+' '+D,use='Any new tighter ψ endpoint is usable with same θ offset.',comp='Weak comparison across all branches.')
add('M-corrected-PT-4000',M,'REPAIR.md',10,'PT Table 1 X=4000 row A=356.3, σ=.98,B=1.52,C=1.89,ε0=7.33e−16; actual providers updated.',
    'L≥4000', 'Compared typed transcription/serialization and original PDF placements.',impl=(('source_rows.py',31),('source_rows.json',511)),source=(PT,),e=(RE,AX),status=BASE,best=False)
add('M-envelope',M,mm,'87-94','Whole-domain intersected u,z,θ transforms, tail intervals and direct outputs on correct scales; B1 keeps entire B0 envelope and adds new valid branches.',
    'Every real x≥2; source arms may be inactive','Add signed and/or unsigned radius intervals, use exp endpoint maxima, intersect direct relative estimates; no bound-valued q used as a lower bound for actual errors.',
    source=(H,PT,DS,DT,FD,Q,C),dep=B+' '+D,use='B1 transfer may reduce endpoint and integration radii.',comp='Nonworsening across all preserved branches.')
for tag,f,l,a in [('base',mm,'96-104','170'),('upgrade',up,155,'168.9'),('literal',up,155,'435')]:
    add('M-comparison-'+tag,M,f,l,f'Named B1 envelope strictly beats named B0 on L≥{a}; '+('B1 numerator from literal D02 log-loss bound.' if tag=='literal' else 'Compare .99q to B0 radius floor from centered inner intervals.'),
         f'All real L≥{a}', 'Finite lower tests for all active B0 rows and source formula families, verified rate derivatives, small shifts and relative transform. B1 finer numerator or direct rate lies below both components; selected smaller component suffices on L≥435.',
         impl=(('source_rows.py','39-69'),('checks.py','4-15'),(ug,'179-200'),(ug,'232-236')),source=(PT,H,C,FD,DS,'FKS (4.1),(5.2); CH2 Lem.B.7 proof p.46 LF6662–6673'),
         trust=density+' Reference named B0 envelope includes density results even when B1 upper bound is literal.',dep=B+' '+D,
         use='Mellin strip and finer envelope' if tag!='literal' else 'Exact D02 coefficient/threshold drives the direct rate.',comp=f'Strict all-ray dominance after {a} vs named B0, not universally over every possible B0 proof.',
         e=(RE,AX),status=EQ if tag=='base' else OK,best=tag!='base')
add('M-power-obstruction',M,mm,'124-129','If W=O(x^(−d′)L^k) for d′>5/32, then no zeros in Re s>max(1−d′,1/2); analogous implications from S or either relative product.',
    'Asymptotic error hypotheses, holomorphic half-plane open at edges',
    'Partial summation in log derivative and holomorphic prime-power series; S→W, log product→S with O(1/(xL)). No actual zero on boundary asserted.',source=(Q,DS),best=False)

assert len({z['claim_id'] for z in cs})==len(cs)
# Verify exact table readback against independently replayed stdout.
obs={r['argv'][-1]:r['stdout'] for r in json.loads((p/RE).read_text())['runs']}
for lo,hi,label in [(18,32,'R new decimal onsets 2..16'),(33,59,'R new higher profiles 17..43')]:
    for j,b in enumerate(('7/8','27/32'),1):
        s=next(x for x in obs['upgrade.py'].splitlines() if x.startswith(label+' '+b+' '))
        x=ast.literal_eval(s[s.index('['):]); got=[Fraction(w) for w in x]
        assert got==[Fraction(z[j]) for _,z in table(up,lo,hi)]
for start,end,label in [(111,116,'M new log onsets'),(124,129,'M density-free matched log onsets')]:
    for j,b in enumerate(('7/8','27/32'),1):
        s=next(x for x in obs['upgrade.py'].splitlines() if x.startswith(label+' '+b+' '))
        assert list(map(Fraction,ast.literal_eval(s[s.index('['):])))==[Fraction(z[j]) for _,z in table(up,start,end)]
for j,b in enumerate(('7/8','27/32'),1):
    s=next(x for x in obs['upgrade.py'].splitlines() if x.startswith('R higher density-free '+b))
    assert list(map(Fraction,ast.literal_eval(s[s.rindex('['):])))==[Fraction(z[j]) for _,z in table(up,67,70)]
    x=next(x for x in obs['refine.py'].splitlines() if x.startswith('refined Ramanujan onsets '+b))
    assert ast.literal_eval(x[x.index('['):])[1:]==[int(z[j]) for _,z in table(rp,21,35)]
    x=next(x for x in obs['refine.py'].splitlines() if x.startswith('refined Mertens onsets '+b))
    assert ast.literal_eval(x[x.index('['):])==[int(z[j]) for _,z in table(mm,38,43)]

summ={R:'All main real profiles, shifts, finite joins and matched rays supported. The exact largest real failure uses the inherited reported integer bridge. Generic unguarded (6) is literally false; every actual use is guarded. Earliest stated connected F0 from L=30.75, no early F1 join, and matched F43 onset 1717.38→1310.73 (density-free 1882.82→1410.23).',
      M:'All old/new density and density-free product/prime-sum tables and their stated joins supported. Finite 10^-8 window not a connected ray. Four least local closed real onsets, normalized relative product conversions, and all-ray named comparison at 168.9 supported at stated trust.'}
fams={}
for fam in [R,M]:
    rs=[c for c in cs if c['family']==fam]
    fams[fam]=dict(strongest_supported_portfolio=[c['claim_id'] for c in rs if c['include_in_best_portfolio'] and c['M_status']==OK],
        rejected_or_incomplete_claims=[c['claim_id'] for c in rs if c['M_status'] in [BAD,'incomplete_with_specific_missing_step']],
        remaining_assessment_work=[],summary=summ[fam])
doc=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=ix['candidate_id'],input_stage='D02',
    assessment_complete=True,all_claims_inventoried=True,
    reviewed_source_hashes={r['packet_name']:r['sha256'] for r in rows.values()},
    reviewed_source_identity=ix['candidate_files'],source_bibliography=src,
    verification_commands=[dict(cmd="pwd; ls -l /task/{INPUT_CONTRACT,RUNTIME_PATHS,CANDIDATE_INDEX}.json",exit=127,note='ls absent, cwd printed'),
        dict(cmd="pwd; Bash [[ -r ... ]] tests then /usr/bin/python3.10 file reads",exit=0),
        dict(cmd="/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out /work/subject",exit=0),
        dict(cmd="cd /work/subject; PYTHONDONTWRITEBYTECODE=1 /usr/bin/python3.10 /dev/stdin (sys.path.insert(0,'.'); runpy.run_path('replay_portfolio.py',run_name='__main__'))",exit=0,evidence=RE),
        dict(cmd="cd /work/subject; /usr/bin/python3.10 OWN_PRIOR_M_014.py",exit=0,evidence=PX),
        dict(cmd="cd /work/submission; PYTHONDONTWRITEBYTECODE=1 /usr/bin/python3.10 ancillary.py /work/subject",exit=0,evidence=AX)],
    family_assessments=fams,claims=cs,
    source_and_trust_limitations=['D01 unavailable.',density,inherit,'Unchanged historical files not new claims. Original statements, withdrawn earlier providers and failed tests are distinguished from active claims.',
        'No independent rerun of published finite-RH/CH2/Dudek–Platt large computations; no unsupported PV/Lean assessment.',
        'All exact candidate bytes unchanged, all seven active outputs match locked stdout.', 'No review generator counters exposed; numerical-run durations recorded separately.'],
    no_other_arm_or_ranking_seen=True,own_history_read=True,new_core_math_salvage_performed=False,original_candidate_bytes_changed=False)
p.joinpath('review.json').write_text(json.dumps(doc,indent=2,ensure_ascii=False)+'\n')
p.joinpath('STAGE_STATUS.json').write_text(json.dumps(dict(ready_for_review=True,families={k:dict(status=OK,claim_files=['review.md','review.json']) for k in (R,M)},serious_attempts_documented=True),indent=2)+'\n')
md=p/'review.md'
s=md.read_text().split('\n## Exact candidate locator manifest')[0]
used=sorted({c['written_source_restored_basename'] for c in cs}|{q['restored_basename'] for c in cs for q in c['implemented_formula_readbacks']})
s+='\n## Exact candidate locator manifest\n\nThe per-statement locators are in review.json; these are the corresponding immutable file digests. Program readbacks are separate from prose declarations. The evidence receipts record actual execution.\n\n| Restored name | Packet file | SHA-256 |\n|---|---|---|\n'
for n in used:s+=f"| \`{n}\` | \`{rows[n]['packet_name']}\` | \`{rows[n]['sha256']}\` |\n"
md.write_text(s.replace('\\\`','\`'))
print('Completed',len(cs),'claims;',len([z for z in cs if z['family']==R]),'Ramanujan and',len([z for z in cs if z['family']==M]),'Mertens. Exact replay/table correspondence validated.')
