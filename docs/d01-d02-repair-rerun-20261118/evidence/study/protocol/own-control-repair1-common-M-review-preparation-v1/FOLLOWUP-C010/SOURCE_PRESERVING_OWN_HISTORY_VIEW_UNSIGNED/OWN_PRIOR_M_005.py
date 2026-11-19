#!/usr/bin/python3.10
"""Build structured assessment and final exact lock; run from any cwd."""
from pathlib import Path
import hashlib, json
P=Path(__file__).resolve().parent
T=Path('/task')
def rd(name): return json.loads((T/name).read_text())
def put(name,obj): (P/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
index=rd('CANDIDATE_INDEX.json')
files={row['original_name']:row for row in index['candidate_files']}
orig=rd('SOURCE_INDEX.json')['sources']
def loc(f,line):
    assert 1<=line<=len((T/files[f]['packet_name']).read_bytes().split(b'\n'))
    return dict(file=f,physical_LF=line,sha256=files[f]['sha256'],packet_file=files[f]['packet_name'])
s='spectral.md'; r='ramanujan.md'; m='mertens.md'; b='bounds.py'; fm='finite_m.py'; ov='candidate.md'
S='supported_at_stated_trust_tier'; B='baseline_retained'; E='equivalent_or_weaker'
F='false_with_specific_counterexample'; I='incomplete_with_specific_missing_step'
claims=[]
TIER='Written proof with stipulated original literature trust and ordinary directed/exact arithmetic where used; no Lean/Blueprint, PV or kernel certification.'
DENS='FKS Cor. 2.9/Table 8, a1=.77 (pp.7–8,26, text 586–608,3139–3258) as published conclusion; no independent recovery from the conflicting Theorem 2.7 δ premise.'
FINITE='PT2021 Theorem 2 PDF p.3 text 205–212 finite integer restriction at literature trust, not independent large finite re-sieve.'
CH='CH2 Corollaries 1.2/1.3 PDF p.3 text 190–240.'
ZERO='OpenAIQRH Thm 1.1 PDF p.4 text 255–262; FiniteRH Thm 1 PDF p.2 text 48–49.'
PERT='FKS Lemma 2.1/Cor. 2.3/Table 1 pp.4–5 text 275–347 and Thm 3.2 p.8 text 631–642.'
APP='CH2 A.1/A.4/B.8/(B.9), PDF pp.40,41,46–47, text 5678–5693,5892–5903,6744–6819.'
DTH='Dusart Thm 4.2 and Prop. 4.3–4.4/Cor. 4.5 PDF pp.11–13 text 959–1010,1049–1137.'
DME='Dusart Thms 5.6/5.7/5.9 PDF pp.17–20 text 1479–1505,1555–1586,1640–1664.'
M9='CH2 Lemma 9.2 PDF p.35 text 5216–5232.'
D02='B0 + PsiMajorant (coefficient 1/64, exponent 27/32, log power 2, on every real x>=exp(200))'
def add(cid,f,line,family,statement,domain,strict,ass='B0',status=S,source=(),derive='',code=(),receipt=(),num='',retained=(),gap='',gain='',base='',trust=TIER):
    assert all(c['claim_id']!=cid for c in claims)
    if isinstance(code,tuple) and code and isinstance(code[0],int):code=[(b,i) for i in code]
    claims.append(dict(claim_id=cid,written_source=loc(f,line),family=family,
        exact_statement=statement,assumptions=ass,full_domain=domain,strictness=strict,
        real_or_integer='Integers and reals separately as stated' if cid in ('R-root','R-PT-finite','R-count-code') else 'Real variable (integer prime-count computation only where indicated)',
        baseline_comparison=base or ('Input-independent; also retained under D02.' if not gain else 'Matched within-method B0 and B0+D02 only; no D01 at this stage.'),
        source_locators=list(source),derivation_check=derive,implemented_source_readback=[loc(ff,ll) for ff,ll in code],
        numerical_obligations=num,actual_verification_receipts=list(receipt),retained_valid_branches=list(retained),M_status=status,
        precise_gap_or_counterexample=gap,propagation=dict(input_used=D02 if gain else 'none (B0)',where_it_changes_proof=gain or 'No D02 use.',
        matched_comparison=base or ('See paired parameters and comparison in review.md.' if gain else 'Preserved under D02.')),
        V_status='not_claimed_not_checked (paper-only runtime; ordinary replay is not PV)',
        remaining_trust=trust))
both='Both'; R='Ramanujan'; M='Mertens'
mixed='B0 and '+D02+', respectively'
def shared(cid,line,statement,dom,strict,**kw): add(cid,s,line,both,statement,dom,strict,**kw)
shared('S-B0',14,'All nontrivial zeros have real part <=7/8; positive heights <=H have real part 1/2.', 'Whole strip; finite branch gamma<=H.','Closed boundaries',status=B,source=(ZERO,),derive='Read exact original theorem statements; conjugation and eta handle negative and zero height.')
shared('S-cut',21,'D02 implies no zero in Re(s)>27/32 by the holomorphic remainder of the Euler-integral.', 'All heights, including boundary allowance at 27/32; usable at any later admissible real x.','Open zero-free half-plane',ass=D02,source=(ZERO,'INPUT_CONTRACT.json'),derive='Integral over [1,e^200] entire; dominated on compact right half-planes beyond beta; poles of logarithmic derivative forbid zeros.',gain='Replaces b0 by b1 in every endpoint and K bound, also below exp(200).')
shared('S1',58,'|e(L)| <= 2.091 L exp(-L/3)+(L^2/16)exp(-a_j L).','L>=40.','Non-strict bound',ass=mixed,source=(PERT,ZERO),derive='T=exp(L/3), admissible at 40 and all larger; T* depends on x. Reciprocal total <L²/16 via table and log products.',code=(95,105,164,175),receipt=('bounds.stdout.txt: main constants and fallback',),gain='Use b1 in all zeros instead of b0; density free.')
shared('S-density-source',61,'N(s,t)<=c t^((8/3)(1-s)) (log t)^(5-2s)+d(log t)^2 for nine specified rows.','t>=3e12, .75<=s<=.88, row endpoints inclusive.','Non-strict',status=B,source=(DENS,),derive='All 9 upward rounded pairs checked against Table 8. Accept the corollary as a stated original result, not the printed Theorem 2.7 instance.',gap='Independent derivation from Thm 2.7 missing: printed δ>=1 while used rows list δ around .309. Density-free branches do not need it.',code=(66,),trust=DENS)
shared('S2-S3',89,'Weighted zero tail is <= B_int(s) <= B(s) (S2/S3); order 3 is a lower bound on B_int only.','s in used rows, zeros gamma>H, log cutoff h.','Non-strict',source=(DENS,ZERO),derive='Tonelli, gamma^-1 kernel, signed Taylor remainder of order 4 (order 3 lower), exact gamma moments.',code=(67,74,404),receipt=('bounds.exit.txt',))
shared('S4',111,'|e(L)|<=D_j(L) = 2.091Le^(-L/3)+(L²/16)e^(-L/4)+S_j(L), S_j positive sum of right-bin exponential masses; D1<D0 as functions for L>0.','Bound L>=40; mixture comparison L>0.','Non-strict bound; strict functional comparison',ass=mixed,source=(DENS,PERT,ZERO),derive='Monotone tail coefficients; endpoint atom in last closed bin; no subtraction of actual unknown tails.',code=(75,80,86,93,96),receipt=('bounds.stdout.txt: crossover and power limits',),gain='Shorten mesh from 2800 to 2700 and collapse final tail at the new boundary.',trust=TIER+' '+DENS)
shared('S5',126,'Continuous derivative-transfer upper bound S_hat<=S_j, with scaled limsup of |e| bounded by B_int(b_j) (upper rounded .010444096,.146302424).','L>=40; limsup L→infty.','Non-strict',ass=mixed,source=(DENS,PERT),derive='Integrate nonnegative derivative over each zero, use running infimum, and bound on each mesh bin by B_i. Endpoint exponential concentrates at b_j.',code=(404,413),receipt=('bounds.exit.txt; nonnumerical profile is prose, code checks anchors only',),gain='Truncate continuous integration at b1, preserving stronger exponent.')
shared('S-CH2',143,'C(L)=pi/(H-1-pi/3)+113.67e^(-L/2) plus all originally admissible signed and symmetric finite-height branches.','C on x>H; all CH2 1.2 branches x>max(T,1e9), 1e7<=T<=H; 1.3 x>=1.','Non-strict bounds, strict domains',source=(CH,),derive='coth enclosure and rational inequality; preserve original weighted A normalization (no shifted center).',code=(98,164,350),receipt=('bounds.stdout.txt: main constants',))
shared('S6',155,'F_psi=( (L-2log(L/(pi e)))²-4 ) exp(-L/2)/(8pi), bounds |e|.','34<=L<=58, both included.','Non-strict',source=('CH2 Cor. 9.3 eq. (9.4), PDF p.36 text 5336–5355',ZERO),derive='Chosen T is increasing and both thresholds strict on checked range.',code=(114,128,170),receipt=('bounds.stdout.txt: main constants',))
shared('S-finite',160,'FiniteRH square root-log² estimates for psi and theta and signed CH2 bounds -.751 and +.791 in square-root units.', '59<x<=2.169e25 psi, 599<x<=2.169e25 theta; PT lemma through e^58; signed psi 1e4<=x<=1e13.','Closed upper endpoints; stated strict lower endpoints',status=B,source=('FiniteRH Cor. 1 PDF 4 text 138–150; PT2021 Lemma 6 PDF 9–10 text 802–812',M9),derive='Preserve finite heights and signed asymmetric constants.')
shared('S-slope',169,'Absolute log derivative of C is <1e-8 on L>=100.','L>=100.','Strict',status=F,source=(CH,),derive='Exact derivative magnitude 113.67e^(-L/2)/(2C).',receipt=('verify.stdout.txt: Spectral C absolute log derivative',),gap='At L=100 magnitude is 1.04685980098...e-8. A 1e-7 bound on whole ray suffices.',retained=('S-cross','S-CH2'))
shared('S-cross',167,'D_j/C decreases strictly; unique crossover brackets (189.023,189.024), (168.795,168.798).','L>=100.','Strict monotonicity and open brackets',ass=mixed,source=(CH,DENS),derive='Repair overly tight C slope assertion by using <1e-7, still <1/8; D_j slope <=-1/8.',code=(383,384,385),receipt=('bounds.stdout.txt: lines 56–58', 'verify.stdout.txt: C slope'),gain='B1 spectral branch overtakes common finite-height floor earlier.')
shared('S-direct-redundant',172,'D1 is stronger than direct D02 |e| <=L² exp(-5L/32)/64.','L>=200.','Strict comparison',ass=D02,status=E,source=(DENS,'INPUT_CONTRACT.json'),derive='After common rescaling, D1 decreases and is <.3 at 200, while direct bound >=625 grows.',code=(387,),receipt=('bounds.exit.txt',),gain='Use D02 via cutoff; the direct endpoint branch is redundant.')
shared('S7',181,'K=integral of e equals absolutely convergent two-pole zero, elementary and trivial-zero series displayed in S7.','L>0.','Identity',source=(APP,PERT,DME),derive='Residues of A(s)x^(s-1)/(s(s-1)), absolutely convergent kernel and horizontal/vertical limits; endpoint equality harmless. Full written proof, no executable contour.',trust=TIER)
shared('S8',218,'|K(L)|<=.047e^(-L/2)+8e-12e^(-a_j L)+1.838e^(-L)+e^(-3L).','L>=log 2.','Non-strict',ass=mixed,source=(APP,PERT,ZERO),derive='CH2 difference identity gives positive low-line budget; Rosser tail and trivial zeros give remaining terms.',code=(318,321,360,369),receipt=('bounds.exit.txt',),gain='High zero term exponent tightens; nothing else in S7 changes.')
shared('S8-signed',238,'May center elementary terms in S7 exactly and minimize high K with 4(h+1)e^(-L/4)/(5H)+S_j/H or S_hat_j/H.','L>=log 2.','Non-strict',ass=mixed,source=(APP,PERT,DENS),derive='Both parts follow by triangle inequality and gamma^-2<=1/(H gamma) for high zeros.',gain='Continuous and discrete high-zero contribution inherits the thinner cut.')
add('R-PT-real',r,42,R,'Literal real reading of PT Theorem 2 first ray: R>0 from all real x>38358837682 to e^58 (candidate identifies this as false).','38358837682<x<=e^58.','Strict',status=F,source=(FINITE,),derive='Counts fixed on first real unit; quotient count and directed endpoint.',code=(296,305),receipt=('bounds.stdout.txt 54','verify.stdout.txt: PT literal endpoint gap'),gap='R(38358837682.217926) < -24.692 by verified counts and Decimal interval.',retained=('R-PT-finite','R-root'))
add('R-PT-finite',r,39,R,'Inherited integer portion R(m)>0 and real extension by floor once x>=n+1.','Integers n+1<=m<=floor(e^58); real transfer [n+1,e^58].','Strict',status=B,source=(FINITE,'Dudek–Platt §3.1 pp.8–10 text 591–707 complementary finite range'),derive='Same pi at x and floor x, increasing shifted count and coefficient. Accept the finite integer assertion at original trust only; literal real version false in first unit.',trust=FINITE)
add('R-root',r,10,R,'r uniquely solves e r B/log r=A² in (38358837682.217926,38358837682.217927). R(r)=0, R>0 for x>r, last failing integer n and ray n+1.','Real x>r; n and r exact last failures with specified integer/real notions.','Strict beyond r, equality at r',source=(FINITE,'PT2021 Lemma 6 PDF 9 text 802–805',PERT),derive='Exact counts, strict continuous monotonicity on final unit, floor extension and B0 density-free analytic upper join.',code=(283,296,305,258),receipt=('bounds.stdout.txt 44–54','verify.stdout.txt: PT literal endpoint gap'),trust=TIER+' '+FINITE)
add('R-tail-old-PT',r,53,R,'Source tail R>0 from e^3915.','Real x>=e^3915.','Strict',status=B,source=('PT2021 Thm 2 PDF 3 text 205–212',),derive='Valid also from candidate elementary branch; no need for older defective finite interpretation.')
add('R-tail-old-DP',r,54,R,'Source tail R>0 from e^9658, not the full-RH integer theorem as an unconditional premise.','Real x>=e^9658.','Strict',status=B,source=('Dudek–Platt Thms 1.2/1.3 PDF 2 text 52–55',),derive='Retain the unconditional tail; new argument covers it already.')
add('R2',r,147,R,'P<= L exp(-L) F(exp L) <=P+10Lexp(-L)+(15/4)21! L^-21 with degree-20 P.','L>=30.','Closed inequalities (strict lower actually)',derive='Exact convergent-series anchor and derivative term; no imported li normalization.',code=(153,154,156,182,192),receipt=('bounds.stdout.txt 1',))
add('R3',r,162,R,'Normalized pi transfer via endpoint f plus Le^-L integral of e^u f/u², including atom 2.','x>=2.','Identity',source=('PT2021 (11), PDF 7 text 544–558',),derive='Stieltjes partial summation and F=2/log2+integral from 2.')
for cid,line,stmt,dom,src,cc,d in [
('R-bF',171,'b_F including S6 endpoint alternative upper bounds absolute normalized pi error.','20<=L<=58 (alternative 34<=L<=58).',('PT2021 Lemma 6 PDF 9–10 text 802–812',DTH),111,'Integrate intrinsic log² endpoint error from 599; initial integral <1250.'),
('R-bC',179,'b_C using CH2 constant and prime-power drift.','L>=20.', (CH,DTH),102,'Finite theta to H; Cor. 1.2 strictly above H. Integral at 20 plus exponential tails.'),
('R-bD',188,'b_D with D_j, D_j* or continuous S5, and power drift.','L>=40.',(PERT,DTH,DENS),108,'Initial integral budget at 40; remaining terms lower log derivative and positive mixture.')]:
    add(cid,r,line,R,stmt,dom,'Non-strict',ass=mixed if cid=='R-bD' else 'B0',source=src,derive=d,code=(cc,164),receipt=('bounds.stdout.txt 1',),gain=('Switch D0 to D1 or D0* to D1*.' if cid=='R-bD' else ''))
add('R4',r,209,R,'Signed pi errors u_j,w_j as displayed in R4 with J_j integrated error and negative prime-power drift.','L>=34; all min branches only on stated domains.','Non-strict',ass=mixed,source=(CH,DTH,APP,PERT),derive='Use -K\' and positive kernel from 20, absolute earlier theta, correct signed drift. Optional finite unshifted upper pi< li only on source range.',code=(125,134,145,388),receipt=('bounds.stdout.txt 36–43','bounds.exit.txt'),gain='D_j and high k_j used in both errors shrink when b_j falls.')
add('R5',r,256,R,'G strictly exceeds the degree-40 difference profile R5; symmetric and exact rational main-term variants retained.','L>=35, with L-1 arguments checked.','Strict',ass=mixed,source=(ZERO,PERT,DTH),derive='Normalize both counts, preserve shift, binomial expansion and cancellation through degree 3; omitted positive remainder or strict R2 anchor yields strictness.',code=(153,154,158,160),receipt=('bounds.stdout.txt 1–47',),gain='After obtaining nested D and K, the loss from both error sides shrinks; no change to the polynomial.')
# Parse the literal quantitative tables, with one row per written statement.
pages=lambda f: (T/files[f]['packet_name']).read_bytes().decode().split('\n')
rp,mp=pages(r),pages(m)
fields=lambda line: [x.strip() for x in line.strip('|').split('|')]
for lf in range(72,101):
    k,h,a,z=fields(rp[lf-1])
    refined=lf in [72,77,82,85,92,95,98]
    add('R-onset-'+str(lf),r,lf,R,f'R1: G> sum(c_i/L^i for 0<=i<{k}) + ({h}) L^(-{k}); c_0..c_7=1,14,145,1412,13985,145450,1610021,19063832; log-onsets {a} B0 and {z} B0+D02.',
        f'Real closed rays L>={a} (B0), L>={z} (D02).','Strict',ass=mixed,source=(ZERO,PERT,CH,DTH,DENS),
        derive='Signed IMPROVED certificate where needed, otherwise symmetric ROWS; check both shifted and unshifted domains, finite cells and monotone tail.',
        code=(248 if refined else 196,214,221,225,238),
        receipt=(('bounds.stdout.txt 36–43 (refined)' if refined else 'bounds.stdout.txt 2–28 (onset)'),),
        num='Cover [onset,450], then upper bound monotone losses and discarded negative coefficients at 450; rescale by extra L if m=c_k.',
        gain='Use thinner zero cut in R4/R5, causing earlier certified onset.' if a!=z else '',
        base=f'Matched R1 strength at B0 {a} and D02 {z}; '+('tie in stated onsets.' if a==z else 'earlier sufficient onset, no B0 optimality claim.'))
for lf in range(108,115):
    k,u,h,z=fields(rp[lf-1])
    add('R-fixed-'+str(lf),r,lf,R,f'R1 k={k}, log onset {u}, strict last coefficient {h} B0 and {z} D02.','Real closed L>='+u+'.','Strict',ass=mixed,source=(PERT,DENS,DTH,CH),derive='Matched-domain fixed-row cells, using stronger prior proved rays for 8.6/80.7 at 50. Preserve 8.6 B0 at 170 and 180.' if lf in (108,109,110) else 'Same R1 cells and tail, lower target allowed even when coefficient is negative.',code=(210,218,225,244,248),receipt=('bounds.stdout.txt 29–43',),gain='D02 improves bound on the same domain; compared to the same R1 prefix.')
for lf,u,c,dom in [(131,'36.55','0','ray'),(131,'36.64','.05','ray'),(132,'36.75','.1','ray'),(132,'36.88','.16','ray'),(134,'36.98','.2','compact'),(135,'39','.8','compact')]:
    add('R-bridge-'+u,r,lf,R,'G>'+c,'L>='+u+(' with upper bound log(1.2e17)' if dom=='compact' else ', all reals on ray; joins analytic .16 from 39.32')+'.','Strict',source=('Dudek–Platt proof of Lemma 3.2 PDF 8 text 561–562 (finite pi<li only)',CH,DTH,PERT,DENS),derive='Use only unshifted upper normalization bound; shifted lower checked with R4, no analytic full RH premise.',code=(262,268,276,280),receipt=('bounds.stdout.txt 37,48–53',),num='Finite signed cells only used through exact source endpoint.')
for lf,k,c,u,v in [(141,0,'0','39.25','39.25'),(142,2,'145','360','275'),(143,3,'1412','405','326')]:
    add('R-fallback-'+str(k),r,lf,R,f'Density-free R1 k={k}, m={c}, onsets {u}/{v}.',f'Closed real rays L>={u}/{v} under B0/D02 respectively.','Strict',ass=mixed,source=(PERT,CH,DTH,ZERO),derive='Symmetric certificates replace D with D*; no numerical use of Table 8. Tail at 450 verified.',code=(105,108,214,258),receipt=('bounds.stdout.txt 44–47',),gain=('Thinner cut changes D* and sufficient onset.' if u!=v else ''))
add('R-fallback-replay',b,258,R,'Replay-only density-free k=1,m=7 margin from L=46.6 under both treatments.','L>=46.6.','Strict',source=(PERT,CH,DTH,ZERO),derive='Same cell and tail tests with fallback flag.',receipt=('bounds.stdout.txt 45',))
add('R-limit',r,119,R,'G→1, so no constant G>m>1 all-ray guarantee.','L→infty.','Limit',derive='Use two-sided normalized pi enclosure with factorial main term and vanishing higher remainder.',source=(PERT,ZERO))
add('R-max',r,102,R,'Pointwise max of applicable strict R1/R5 lower bounds; fixed-onset ties do not discard better earlier certified rows.','Each branch on stated domain.','Strict',ass=mixed,derive='Finite maxima preserve strictness; no bound used at unavailable arguments.',gain='New R1 rows and R5 profile available in B1.')
add('R-original-Dusart',r,319,R,'Intersect original Dusart π bounds before substituting both x,x/e.','Dusart separate real thresholds at each argument.','Original strictness as printed',status=B,source=('Dusart Thm 5.1/Cor. 5.2–5.3 pp.14–16 text 1188–1214,1309–1355,1388–1402',),derive='Use nonnegative upper for squaring, separate x/e domain; constants read back in review.md.')
add('R-original-PT-cor2',r,320,R,'Retain PT |π-li|<=235x L^.52 exp(-.8 sqrt L) with li=integral from 2.','L>=2000 for each argument, common L>=2001.','Non-strict',status=B,source=('PT2021 Cor 2 PDF 3 text 127–131; (11) p.7 text 544–558',),derive='Translate centers by 2/log2 when comparing with F.')
add('R-original-PT-sec5',r,321,R,'Optional π intersections with (19),(20) at the published anchor e^3914.','Each L>=3914; both arguments if L>=3915.','Non-strict enclosures; ancillary domination is strict',status=B,source=('PT2021 §5 eqs. (17)–(20) PDF 9–11 text 766–800,813–957,984',),derive='Actual π remainder coefficient between 120 and 120+.19 by candidate density-free bounds; explicit Ma/ma domination at published anchor. No arbitrary parameter recovery.',receipt=('verify.stdout.txt: PT printed anchor comparisons',),gap='Original intermediate (18) is false for some x in (2,3), published-anchor final formulas checked separately.')
add('R-PT-theta-intermediate',r,321,R,'Source auxiliary (18) used in original §5: |theta(x)/x−1| <=(2−log 2)/2 for 2<x<=599.','2<x<=599.','Non-strict',status=F,source=('PT2021 (18) PDF 10 text 849–851',),derive='theta(2.9)=log 2 by direct prime enumeration.',receipt=('verify.stdout.txt: PT Section 5 (18)',),gap='x=2.9: relative discrepancy .76098... > .65342....',retained=('R-original-PT-sec5','R-bF'))
add('R-profile-gain',r,330,R,'R4/R5 nested over common domain; strict improvement on L>=168.82 for the constructed profiles.','Common profile domain L>=35; strict gain L>=168.82.','Strict improvement on late ray',ass=mixed,source=(DENS,CH,DTH),derive='Use B0 floor f0, B1 D1+J1, and non-increase of shifted w even below strict comparison onset.',code=(393,397,400),receipt=('bounds.exit.txt',),gain='D1+J1 strictly reduces u and never increases shifted loss.',base='Constructed profiles only; not best arithmetic inequality or every source-optimized substitution.')

add('M-normalizations',m,3,M,'M, B3 exact series constants; Z_raw=log Q_raw-gamma-log L, E1=sum 1/p-log L-M, Eell=sum log(p)/p-L+B3; P,Q have opposite log errors.','x>1, empty prime data for 1<x<2.','Identities',source=(DME,),derive='Expand all powers in product; exact source constants rather than rounded decimals.',code=((fm,93),(fm,94),(fm,105)),receipt=('finite.stdout.txt 1',))
add('M-M2',m,183,M,'A=e-K, Z=e/L-integral(e W); integrate W against -K\' to preserve sign.','x>=2.','Identities with included prime-power endpoint',source=(DME,APP),derive='Partial summation with appropriate normalization and tail; correction preserves all atoms.',code=(318,321,333),receipt=('bounds.exit.txt',))
add('M-pp-identity',m,194,M,'Eell=A+Cell, E1=Z+C1, Zraw=Z+CP; all corrections nonnegative, CP restricts p<=x.','x>=2.','Identities; p^m>x strict in tails',source=(DME,),derive='Exactly distinguish truncated prime powers versus all powers of each included prime.')
for lf,u,c in [(199,'18','1.34'),(204,'17.8','1.37')]:
    add('M-pp-'+u,m,lf,M,'Cell <= '+c+' exp(-L/2), CP<=C1<='+c+' exp(-L/2)/L.', 'L>='+u+'.','Non-strict',source=(DTH,),derive='Square term by θ partial summation. Higher powers by θ upper, sum individually until 7, bound through floor L/log2 and then geometric tail. Monotonic rescaling.',code=(326,370,371),receipt=('bounds.stdout.txt 55',))
add('M-M4',m,224,M,'U=d+k_j+p, LV=d+(1+1/L)k_j+(1/L+2/L²)J_k+p. Weighted <=U and log/reciprocal <=V; products <=e^V-1<=V/(1-V) for V<1.','L>=17.8 with correct pp coefficient and valid endpoint d; V<1 for rational conversion.','Non-strict',ass=mixed,source=(APP,DME,DTH),derive='Apply M2 and decreasing |W\'|. Opposite product signs both covered, U<=LV.',code=(318,333,341),receipt=('bounds.exit.txt',),gain='M4 uses smaller D1 and high K part, with same 1/L factor and no extra comparable D integral.')
for lf in range(28,42):
    u,c,z=fields(mp[lf-1])
    add('M-power-'+u,m,lf,M,f'M1 simultaneous first 3 errors <= C x^-a / L and weighted <= C x^-a. B0 (C={c},a=1/8); D02 (C={z},a=5/32).',
        f'Real L>={u}, matched.','Non-strict errors; strict domination of B1 envelope',ass=mixed,source=(DENS,PERT,APP,DTH,DME),
        derive='M4 through LV/(1-V); scale by e^(aL), each piece decreases after 170; paired ratio (C1/C0)e^(-L/32) strictly decreases.',
        code=(341,415,420,421),receipt=(f'bounds.stdout.txt {59+lf-28}', 'bounds.exit.txt'),
        num='Outward upper endpoint below displayed constant and ratio below 1 at same left endpoint.',
        gain='Thin cutoff improves exponent while increasing upper rounded coefficient.',
        base=f'Matched ray {u}; C rises {c}→{z}, exponent improves by 1/32; B1 strictly better throughout.')
add('M-cont-param',m,43,M,'Parametrized M1 constant e^(a u)u V(u)/(1-V(u)) for any u>=170; extra certified endpoint values at u=1500,2500,5000,10000.', 'All real u>=170; associated L>=u.','Non-strict',ass=mixed,source=(DENS,PERT,APP),derive='Same monotonic transfer; use outward printed upper decimals in extra branches.',code=(341,406),receipt=('bounds.stdout.txt 59–76',),gain='Replace endpoint cutoff and compare paired shapes with matched onset when specified.')
for lf,u in [(73,1500),(74,2500),(75,5000),(76,10000)]:
    add('M-replay-power-'+str(u),'replay.txt',lf,M,f'Exact upward M4 endpoint triples (weighted/log/relative), B0 then D02: {pages("replay.txt")[lf-1]}. Third coefficient covers all as in M1.',f'L>={u}.','Non-strict',ass=mixed,source=(DENS,PERT,APP),derive='Literal printed endpoint triples in replay, same e^(a L)-scaled monotonicity.',code=(341,406),receipt=(f'bounds.stdout.txt {lf}',),gain='D02 lowers the endpoint at the same exponent-floor comparison after accounting for distinct powers.')
add('M-limsup',m,46,M,'Scaled limsup coefficients .010444096(1+1/H) and .146302424(1+1/H) for B0/B1; scale by Lx^a in unweighted/relative channels and x^a weighted.', 'L→∞.','Non-strict limsup',ass=mixed,source=(DENS,PERT,APP),derive='Use S5 continuous bound and tighter high K, vanishing rescaled drift and K integrals multiplied by 1/L. exp conversion asymptotic factor 1.',code=(413,414),receipt=('bounds.exit.txt',),gain='Smaller cutoff changes asymptotic exponent; coefficients are not claims of optimality.')
add('M-no-density',m,57,M,'Same errors <=.0626 L x^-a in first 3 channels and <=.0626 L² x^-a weighted; a=1/8,5/32 respectively.','All real L>=300.','Non-strict',ass=mixed,source=(PERT,APP,DTH,DME),derive='Use S1 and S8 without Table 8, divide scaled tests by additional L², retain actual relative conversion.',code=(408,411,412),receipt=('bounds.exit.txt','verify.stdout.txt matched density-free ratio'),gain='Same coefficient and L powers on matched ray; improvement ratio e^(-L/32).')
for cid,lf,target,coef,u in [('recip',66,'|E1|','.2/L^3','2278383'),('weighted',67,'|Eell|','.3/L^2','912560'),('products',68,'both normalized absolute relative product errors','.2/L^3','2278382')]:
    add('M-old-'+cid,m,lf,M,target+' <= '+coef,'Real x>='+u+'.','Non-strict',status=B,source=(DME,),derive='Readback confirmed precise real thresholds and normalizations. Retained in pointwise minima; Remark 5.8 not numerical.')
for lf,tag,err,p,br,coef in [(75,'Q','|e^Zraw-1|',2278379,'(2.710,2.713)','.2/L³'),(76,'P','|e^-Zraw-1|',2278379,'(2.574,2.577)','.2/L³'),(77,'E1','|E1|',2278379,'(3.111,3.115)','.2/L³'),(78,'Eell','|Eell|',912559,'(.997,.998)','.3/L²')]:
    add('M-root-'+tag,m,lf,M,f'Least real onset {p}+t with t in {br} for {err}<={coef}, equality at root.',f'Closed real ray x>={p}+t.', 'Non-strict; equality at onset',source=(DME,DTH),derive='No prime in local interval, small positive normalized sign (negative raw P sign before absolute value), strict derivative of scaled metric, failures immediately below, inherited old bound takes over exactly.',
        code=((fm,45),(fm,78),(fm,97),(fm,105),(fm,115)),receipt=(f'finite.stdout.txt {lf-73}',),
        num='Exact sieve through 54e6; directed normalizing constants and bracket metric.',
        base='Input-independent earlier onset at exactly same coefficient/normalization as Dusart.')
for lf in range(104,111):
    u,c=fields(mp[lf-1])
    add('M-log-'+u,m,lf,M,f'Each of first three errors <= {c}/L³, weighted <= {c}/L².',f'Real L>={u}.','Non-strict',source=(CH,M9,APP,DTH,DENS),derive='CH2 branches on compact cells with correct early domain; tail D0 beyond 220, monotone powers.',code=(425,431,438,443,450),receipt=(f'bounds.stdout.txt {lf-27}',),num='Cell coverage [u,220] and tail threshold at 220.')
for lf in range(121,128):
    c,x,y,z=fields(mp[lf-1])
    add('M-finite-'+c,m,lf,M,f'Products <= {c}/L³ from x={x}, reciprocals same from x={y}, weighted <= {c}/L² from x={z}.',
        f'Three closed real rays respectively x>={x}, x>={y}, x>={z}.','Non-strict',source=(DTH,CH,M9,DENS),derive='Sieve cells with monotone raw sums; certify onsets by last bad-cell right edges; join first analytic .1 ray before 54e6.',
        code=((fm,47),(fm,53),(fm,118),(fm,131),(fm,136),(b,427)),receipt=('finite.stdout.txt 6','bounds.stdout.txt 77'),num='Exact integer sieve, fixed point log errors and all real mesh cells.')
add('M-finite-refined',m,138,M,'Raw sums/bracketing intervals of finite cells can be used directly instead of rounded constant-row metrics.','Real 500000<=x<=54000000.','Closed enclosures',source=(DTH,),derive='Keep both endpoint sums and entire smooth interval; convert normalized logarithms.',code=((fm,118),(fm,128)),receipt=('finite.exit.txt',))
add('M-constants',m,141,M,'Enclose gamma, M, B3 via fixed-point sums and explicit θ tail at N=54e6.','Normalization independent of x.','Closed enclosures',source=(DTH,DME),derive='Fixed-point floor/ceil alternating logs, trapezoid gamma, integrated geometric square tail, exact B3 integral plus δ guard.',code=((fm,7),(fm,18),(fm,36),(fm,56),(fm,81),(fm,93)),receipt=('finite.stdout.txt 1',))
for lf,tag,statement,dom in [(330,'Eell','Eell>.054 exp(-L/2)','18<=L<=log(1e13)'),(331,'E1-Z','E1 and Zraw>.06 exp(-L/2)/L; Q normalized >1 and P normalized <1; use 1-exp(-u) for P','20.8<=L<=log(1e13)')]:
    add('M-signed-'+tag,m,lf,M,statement,dom,'Strict lower bounds',source=(M9,DTH,APP),derive='Use signed CH2 lower, S8 upper and square-tail lower; no unproven signs from exploration.',code=(372,375,377,379),receipt=('bounds.exit.txt',))
add('M-envel-empty',m,257,M,'Exact empty sums and both raw products equal 1.','1<x<2.','Identities',derive='No primes in range; include 2 at x=2.')
add('M-envel-fks5.2',m,270,M,'Included bound Eψ(x)<=2 L^(3/2) exp(-.8476836 sqrt L) on FKS Lemma 5.2 original domain where candidate intersects I_e.', 'Candidate x>=2 intersected with 0<L<=2100; original 0<L<=2100.','Non-strict',status=F,
    source=('FKS Lemma 5.2, PDF p.17 text 1928–1942',),derive='Read actual coefficient 2 and quantifiers, not larger Cor. 1.4; counterexample uses exact psi at 2.',
    gap='At x=2 bound <.571, but |psi(2)/2−1|=1-log2/2>.6534; also fails at 2.1. The 1<x<2 empty-product convention is not affected.',
    receipt=('verify.stdout.txt FKS Lemma 5.2',),retained=('M-envelope-valid','M-env-gain','M-FKS-cor14'))
add('M-envelope-literal',m,255,M,'Whole declared pointwise construction with every listed original inclusion gives a valid enclosure, including full printed FKS Lemma 5.2 domain.','All x>1, split at 2.','Closed enclosures',status=I,source=(CH,DME,'FKS Lemma 5.2 original text 1928–1942'),
    derive='Mathematical interval transfers are valid on true inputs, but I_e is not an enclosure when intersecting this branch near 2.',
    gap='Omit the faulty small-x FKS branch or prove a correct restricted source domain. No counterexample asserted for other numerical M bounds.',
    retained=('M-envelope-valid','M-envel-empty','M-env-gain'))
add('M-envelope-valid',m,274,M,'Pointwise minimum/intersection of valid source, spectral, signed and early branches with the A/Z/K/theta transfers and exact relative mapping.','x>=2, retaining each legitimate source-specific threshold and excluding false Lemma 5.2 use near 2.','Closed enclosures',ass=mixed,source=(APP,CH,DTH,DME,DENS),
    derive='All interval transfers checked; integral convergence via S4 or S1/S8; tail rule strict p>y, includes atom p=2 when needed, products preserve reciprocal signs. This is the surviving subportfolio, not the faulty clause.',
    gain='Nest D and high K when using D02; retain all valid B0 alternatives.')
add('M-envel-tail-rule',m,301,M,'Prime-power bounds via decreasing weight and θ tail rule, with geometric remainder 3.001*2^-m0 and log tail additional divisor (m0+1)log2.','x>=2, y>=2 or use y=2 and add 2 atom, m0>=2.','Identity and non-strict upper bounds',source=(DTH,),derive='Partial summation of theta=t+t f, endpoint belongs to excluded interval. Subtract tails for CP cutoff and take positive intersections.')
add('M-envel-product-map',m,313,M,'Relative Q max(exp(u)-1,1-exp(l)); relative P max(exp(-l)-1,1-exp(-u)) for a true [l,u] log interval.','All admissible real x and enclosed logs.','Non-strict upper bounds',derive='Monotone exponential and maximum magnitude at an endpoint; no reversal between P and Q.')
for cid,lf,st,dm,src,drv in [
    ('M-envel-CH2','264','Original signed and symmetric e,A branches, and unified Cor.1.3','x>max(T,1e9) for 1.2, 1e7<=T<=H; x>=1 for 1.3',CH,'Keep two different normalizations and explicit strict domain.'),
    ('M-Dusart-psi','268','Dusart Prop. 3.2/Table 1 and Thm. 3.3 psi bounds','Each L>=b for step rows; x>=2 for Thm. 3.3','Dusart pp.7–9 text 455–475,482–765','Read each source threshold; comparison only covers the listed explicit table results, not arbitrary new parameter optimization.'),
    ('M-PT-psi','269','PT Theorem 1 Table 1 psi step and sqrt-log formulas','Every listed L>=X','PT2021 Thm 1 pp.2–3 text 77–95,135–201','Keep source at literature trust despite noted older truncation difficulties.'),
    ('M-FKS-cor14','270','FKS Cor.1.4 bound with 9.22022, not 2, for all x>2','x>2','FKS Cor 1.4 PDF 2 text 140–144','Exact original strict x/inequality; no .618 alternative.'),
    ('M-FKS-table5','271','FKS Table 5 explicit ε(x0) step bounds','Each listed ray L>=log x0 at original table trust','FKS Thm 1.1 p.2 text 113–117, Table 5 pp.21–22 text 2307–2575','Thm quantifier >1000; printed first table value at 1000 is independently dominated by applicable CH2.'),
    ('M-FKS-table6','271','FKS Table 6 explicit A(x0) (L/R)^(3/2) exp(-2 sqrt(L/R)), R=5.5666305','Each listed ray L>=log x0 at original table trust','FKS Thm 1.2 p.2 text 118–135, Table 6 p.23 text 2581–2747','Correct functional normalization and onsets, no unconfirmed alternative.'),
    ('M-theta-retained','275','Subtract prime-power drift and intersect with Dusart/FiniteRH/PT theta branches','Powers upper x>0, better lower x>=121; each theta threshold independently','Dusart 4.2–4.5 pp.11–13 text 959–1137; PT Cor. 1 text 98–117 (Table 1), Lemma 6 text 802–805; FiniteRH Cor. 1 text 138–146','Upper A+.1 in PT; finite ends respected.')
]:
    add(cid,m,int(lf),M,st,dm+'.','As in original sources',status=B,source=(src,),derive=drv)
add('M-env-gain',m,359,M,'Every channel in the constructed valid M envelope strictly improves under D02 throughout L>=168.82.','Common real ray L>=168.82.','Strict dominance (valid listed branches only)',ass=mixed,
    source=(CH,DENS,'Comparison source tables in review.md'),derive='B0 f0,F contain symmetric core after theta correction, integral interval contains zero. Directed D1/M4 endpoint less than both components, monotone ratios afterwards. No claims about uncomputed source instantiations.',
    code=(393,395,400,405),receipt=('bounds.exit.txt','verify.stdout.txt old-source floor anchors'),gain='Replacement D1 endpoint with same source B0 branches retained, plus D02 high K cut.')
add('M-equal-exp',m,413,M,'At matched exponent 1/8, B1 provides common coefficient .002, with /L in first three and no /L in weighted; B0 constructed floor prevents that coefficient on any entire ray within the method.','L>=170 for new bound; B0 floor for large ray.','Non-strict errors, strict comparative gain',ass=mixed,source=(DENS,APP),derive='Convert the 170 M1 row by factor exp(-L/32) and compare to B0 F floor; not a bound on true arithmetic performance.',code=(422,),receipt=('bounds.exit.txt',),gain='Use stronger cutoff then discharge threshold with the same output exponent.')
# Headline readback and implementation-specific claims (distinct physical locations).
add('Head-R',ov,8,R,'Sharp connected sign ray, R1 k=2 m=80.7 onsets 197/49, R1 k=3 m=1412 onsets 253.65/211.11.','As in R-root, R-onset-85, R-onset-92.','Strict except root equality',ass=mixed,source=(FINITE,CH,PERT,DENS,DTH),derive='Both headline high-order gains use signed supplement; exact sign from B0 density-free and finite literature.',code=(248,296),receipt=('bounds.stdout.txt 40–41,54',),gain='Cutoff affects higher-order certified margins, not exact sign onset.')
add('Head-M',ov,19,M,'Simultaneous .256857 at exponent 5/32 from 200, vs .018312 at exponent 1/8, and late strict gain from 168.82; earlier exact onsets independent.', 'Power row L>=200; strict envelope comparison L>=168.82; four local onsets above.','Non-strict individual power bound; strict comparison',ass=mixed,source=(DENS,CH,DME),derive='Use M-power-200 and M-env-gain on their real domains; small-x false inclusion unrelated.',code=(393,415),receipt=('bounds.stdout.txt 64','finite.stdout.txt 2–5'),gain='Genuine matched gain through D02 cut (B1 exponent 5/32); old smaller coefficient with weaker exponent.')
add('Head-S',ov,26,both,'Cutoff transfer, absolute endpoint estimate and two-pole once-integrated identity with density-free fallback.', 'Domains S-cut, S1, S4, S7.','As stated in corresponding claims',ass=mixed,source=(ZERO,PERT,DENS,APP),derive='Subordinate proof claims S-cut to S8; no time-varying T* integration.',gain='Spectral cutoff propagates into both families.')
add('I-arithmetic',b,8,both,'I: directed 48-digit endpoint +,-,*, reciprocal; exp and ln enclosed by adjacent decimals; Machin pi via 100-term bracketing alternating series.','Interval arithmetic on actual real arguments; positive logs, nonzero denominators.','Outward closed intervals',derive='Per-operation rounding and copy_negate (no lossy default negation). All subdivisions use shared midpoint and stop after actual bounds; no claim of arbitrary numeric contexts.',code=(8,17,23,31,44,54),receipt=('verify.stdout.txt interpreter and identity','bounds.exit.txt','finite.exit.txt'))
add('R-count-code',b,283,R,'Quotient sieve and actual endpoint function E*x/x.ln()*q-p*p use floor count of n/e and both exact prime counts.', 'Integer sieve to n and floor(n/e), inserted on [n,n+1).','Exact integer counts, interval sign bounds',derive='Descending closed quotient set invariant. Flooring with int on positive arguments certified equal.',code=(283,298,301,303),receipt=('bounds.stdout.txt 54','verify.stdout.txt endpoints'))
add('R-numeric-code',b,214,R,'Actual ram.verify cell residual resmain(l,r,k)-loss, special scaling if m==c_k, plus separate signed bridge.', 'Onset through 450, analytic continuation after 450; bridge through upper log endpoint for test only.', 'Interval lower > target at every admitted cell',derive='Read actual ablation flags and score rows separately; do not substitute symmetric ROWS for refined IMPROVED.',code=(196,210,214,225,238,248,262),receipt=('bounds.stdout.txt 2–53',))
add('R-failed-profile-tests',b,310,R,'lastnot calculates actual symmetric mesh R5 residual at selected B0 points, below chosen targets; attempts.md 53–57 also discusses a failed signed 81 trial.', 'Only labeled points from 461–464 and L=168.718 for signed trial.','Strict insufficiency test for constructed profiles only',status=E,derive='Does not bound actual G from above or assert a failed search is mathematical falsehood.',code=(310,461),receipt=('bounds.stdout.txt 84–91','verify.stdout.txt Failed proposed coefficient 81'))
add('M-numeric-code',b,333,M,'Actual mux returns (d+K+p, [d+(1+1/L)K+(1/L+2/L²)J+p]/L); den_limit scales weighted/log/relative separately.','M4 domains; C_j endpoints at u>=170; early real cells and fallback as tested.','Outward enclosures',derive='Code K and J summed from prescribed exponent pair list. V/(1−V) in actual product certificate.',code=(318,333,341,406,430),receipt=('bounds.stdout.txt 55–83',))
add('M-finite-code',fm,118,M,'Actual finite metrics use interval between endpoint raw sums, subtract full log image, multiply right log powers and track last failing right endpoint.','All cells [500000,54000000] and actual local brackets; see finite statements for proven rays.','Outward upper and strict replay tests',derive='No sampling assumption; righthand closed inclusion; prime sieve exact, fixed point outward logs.',code=((fm,53),(fm,117),(fm,119),(fm,123),(fm,128),(fm,133)),receipt=('finite.stdout.txt 1–6',))
add('I-S4-code',b,86,both,'ds evaluates the two positive-mixture spectral bounds using w=exp(-L/3200), x0 from w^800 to w^400, with separate B1 head at i=2699 and B0 tail at i=2799. B_i is a running min of actual 48-digit S3 outward right endpoints. S5 not implemented by ds.','Real L>=40 for arithmetic error bound; formulas may be computed elsewhere.','Outward interval enclosures',ass=mixed,source=(PERT,DENS),derive='Checked actual exponents, indexing and mass at both terminal bins; code eval does not claim that T* is a constant.',code=(67,75,86,93,96),receipt=('bounds.exit.txt','bounds.stdout.txt crossover and M1 rows'),gain='B1 stops the common density array at the thinner cutoff.')
for line,target,detail in [
 (197, 'symmetric k=0,m=0 at 39.25/39.25', 'refined at 39.15/39.15; separate density-free 39.25 survives'),
 (198, 'symmetric k=0,m=1 at 42.75/42.75', 'refined at 42.6/42.6'),
 (203, 'symmetric k=3,m=1412 at 253.75/211.25', 'refined at 253.65/211.11'),
 (205, 'symmetric k=4,m=13985 at 288/236.6', 'refined at 287.93/236.52'),
 (206, 'symmetric k=5,m=145450 at 322.85/262.5', 'same B0 and refined B1 at 262.45'),
 (210, 'symmetric k=2, L>=50 with m=7.8/80', 'written fixed row uses 8.6/80.7')]:
    add('R-redundant-sym-'+str(line),b,line,R,target+'.','As in stated log-onsets.','Strict',ass=mixed,status=E,source=(PERT,DENS,CH),derive='Replay checked, '+detail+'.',code=(214,225,239),receipt=('bounds.stdout.txt 2–35',))
add('M-fks52-survives',m,270,M,'Valid restriction of the FKS Lemma 5.2 numerical curve with coefficient 2.','3<=x<=exp(2100).','Non-strict',status=B,source=('FKS Lemma 5.2 original PDF p.17 text 1928–1942','Dusart Thm. 3.3 PDF p.7 text 458–475'),derive='On [log 3,40] use .77 and endpoint minima for the unimodal FKS shape. Later reuse the two explicitly quoted epsilon bounds on (40,1000] and (1000,2100].',receipt=('verify.stdout.txt FKS restricted-domain anchors',))
add('M-conversion-code',fm,128,M,'Actual finite metric absz/(1-absz), plus analytic Mertens rational conversions with 1-V denominator; positive on all material executed cells/tests.','Finite real cells [500000,54000000], M4 compact/endpoint uses; continuous tails governed by V decreasing.','Strict denominator positivity',derive='Observe actual division in unchanged locked code and ensure denominator lower endpoint >0. Same stdout; no general V>=1 application.',code=((fm,128),(b,348),(b,395),(b,412),(b,443),(b,451)),receipt=('conversion.stdout.txt','conversion.exit.txt'))
# The controller requires each claim record to carry one requested family.
# Common dependencies are referenced in both families, with unique IDs;
# duplicating the references does not count them as independent results.
shared_ids={q['claim_id'] for q in claims if q['family']==both}
family_code={R:'R',M:'M'}
def family_id(cid,family):
    return cid+'-'+family_code[family] if cid in shared_ids else cid
expanded=[]
for q in claims:
    for name in ((R,M) if q['family']==both else (q['family'],)):
        rec=dict(q,family=name,claim_id=family_id(q['claim_id'],name))
        rec['retained_valid_branches']=[family_id(cid,name) for cid in q['retained_valid_branches']]
        expanded.append(rec)
claims=expanded
bad={F,I}
fam={}
for name in (R,M):
    cohort=[q for q in claims if q['family']==name]
    fam[name]=dict(strongest_supported_portfolio=[q['claim_id'] for q in cohort if q['M_status'] in (S,B)],
                   rejected_or_incomplete_claims=[q['claim_id'] for q in cohort if q['M_status'] in bad],
                   remaining_assessment_work=[],
                   summary=('Sharp sign with inherited integer statement and verified real root; all R1 tables including signed refinements and density-free fallback, with strict late constructed-profile comparison.' if name==R else 'All M1 rows plus density-free alternative, exact early onsets, finite/log/signed branches and valid late strict comparison retained. Full literal small-x FKS intersection is not established.'))
review=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=index['candidate_id'],assessment_complete=True,all_claims_inventoried=True,
    reviewed_source_hashes=dict(candidate=index['candidate_files'],originals=orig),
    source_bibliography=orig,actual_effort='Read and hashed exact candidate files and original PDFs/extractions, checked proofs/cells/tails and source statements; ran both locked computations and ancillary checks. No exact aggregate effort counter, original zero census, large inherited sieve or formal build.',
    verification_commands=[
        '/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out /work/review_candidate',
        'cd /work/review_candidate; /usr/bin/python3.10 -B bounds.py all > /work/submission/bounds.stdout.txt 2> /work/submission/bounds.stderr.txt; printf status to bounds.exit.txt',
        'cd /work/review_candidate; /usr/bin/python3.10 -B finite_m.py > /work/submission/finite.stdout.txt 2> /work/submission/finite.stderr.txt; printf status to finite.exit.txt',
        'cd /work/submission; /usr/bin/python3.10 -B verify_review.py > verify.stdout.txt 2> verify.stderr.txt; printf status to verify.exit.txt',
        'cd /work/submission; /usr/bin/python3.10 -B verify_conversion.py > conversion.stdout.txt 2> conversion.stderr.txt; printf status to conversion.exit.txt',
        'See exact shell snippets in review.md. All verification commands non-login /bin/bash; both locked program receipts matched byte for byte.'],
    family_assessments=fam,claims=claims,no_other_arm_or_ranking_seen=True,original_candidate_bytes_changed=False,
    new_core_math_salvage_performed=False,formal_and_pv='Not claimed or tested. Paper-only runtime. Directed numerical and source literature trust are not formal validation.',
    restart_notes='See review.md for checkpoints, exact source locations and receipts. Both mathematical assessments finished. No other input stage reconstructed.')
put('review.json',review)
put('STAGE_STATUS.json',dict(ready_for_review=True,families={n:dict(status=S,claim_files=['review.md','review.json']) for n in fam},serious_attempts_documented=True))
payloads=sorted(p for p in P.iterdir() if p.name!='LOCK.json')
assert all(p.is_file() and not p.is_symlink() for p in payloads)
put('LOCK.json',dict(files=[dict(path=p.name,sha256=digest(p)) for p in payloads]))
print(len(claims),'claims;', len(payloads),'locked payloads')
