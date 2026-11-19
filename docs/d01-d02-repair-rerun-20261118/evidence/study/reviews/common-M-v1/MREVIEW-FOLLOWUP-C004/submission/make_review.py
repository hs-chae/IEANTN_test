from pathlib import Path
import json,re,hashlib
O=Path('/work/submission')
C=Path('/work/c004')
idx=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
sources=json.loads(Path('/task/SOURCE_INDEX.json').read_text())['sources']
files={r['original_name']:r for r in idx['candidate_files']}
checkpoints=json.loads((O/'source-checkpoints.json').read_text())
rows=[]
OK='supported_at_stated_trust_tier'
BASE='baseline_retained'
TIE='equivalent_or_weaker'
GA='Ramanujan'
ME='Mertens'
DS=['OpenAIQRH Theorem 1.1 PDF p.4','FiniteRH Theorem 1 PDF p.2','FKS §2, Thm. 2.7, Cor. 2.9 (2.17), PDF pp.4–8 and Table 8 p.26','FKS Theorem 3.2 and Remark 3.3 PDF p.8','PlattTrudgian2021 Lemma 2 PDF p.4']
FP=['FiniteRH Cor. 1 p.4 (psi and theta)','CH2 Cor. 1.2–1.3 p.3 and Prop. 9.1 pp.34–36, (7.2) p.22','Dusart2018 §5.1 p.13, Prop. 4.3 p.12, Cor. 4.5 p.13, Thm. 5.1 proof p.15, Cor. 5.2 pp.15–16']
DP=['DudekPlatt2015 §3.1 p.8 and Lemma 3.4 p.10','DudekPlatt2015 Thms. 1.2–1.3 p.2','PlattTrudgian2021 Thm. 2 p.3']
DU=['Dusart2018 Thms. 5.6, 5.7, 5.9 pp.17–20']
MT=FP[:2]+['Dusart2018 Thm. 3.3 p.7, Prop. 4.3 p.12, Cor. 4.5 p.13']+DU
V='No formal object supplied or claimed; optional Lean and kernel evidence not checked; not source-first PV.'
def loc(name,l):
 if isinstance(l,int): z=[l,l]
 else: z=list(l)
 r=files[name]
 packet=Path('/task',r['packet_name'])
 body=packet.read_bytes()
 assert hashlib.sha256(body).hexdigest()==r['sha256']
 assert body==(C/name).read_bytes()
 assert 0<z[0]<=z[-1]<=len(body.split(b'\n'))
 return {'file':r['packet_name'],'physical_LF':z[0],'sha256':r['sha256']}
def end_lf(l):
 return l if isinstance(l,int) else list(l)[-1]
def span(name,l):
 return {**loc(name,l),'original_file':name,'physical_LF_end':end_lf(l)}

def add(id,f,n,l,s,dom,strict,src,der,code=(),ob='None additional.',receipts=(),status=OK,comp='Same theorem under B0 and B0+D01; no D02 available.',inp=False,trust=None,kind='real',others=(),aliases=(),port=True):
 row={'claim_id':id,'family':f,'written_source':loc(n,l),'written_source_extent':span(n,l),'exact_statement':s,'assumptions':'Permitted common original-paper conclusions with their original hypotheses and computation trust, and the explicitly checked candidate deductions; D01 is not a premise.' if not inp else 'Exact D01 assumption on the stated input tail, only for this ablation branch.',
 'full_domain':dom,'strictness':strict,'real_or_integer':kind,'baseline_comparison':comp,'source_locators':src,'derivation_check':der,
 'numerical_obligations':ob,'actual_verification_receipts':list(receipts),'retained_valid_branches':list(others),'M_status':status,
 'precise_gap_or_counterexample':None,'propagation':{'input_used':'D01 only in the dominated same-map ablation' if inp else 'None; B0 only',
 'where_it_changes_proof':'Changes the integrand of the absolute Abel map, to a larger envelope; improves no endpoint.' if inp else 'No proof or endpoint changes upon adding D01.', 'matched_comparison':comp},
 'V_status':V+(' Ordinary original-source replay observed.' if receipts else ''),'remaining_trust':trust or 'Original literature trust for invoked results; mathematical derivation and directed numerical replay where listed.',
 'implemented_readbacks':[span(*x) for x in code],'additional_written_locators':[span(*x) for x in aliases],
 'primary_supported_portfolio_member':port}
 rows.append(row)
 return row
def codes(*r):return [('verify.py',i) for i in r]
for f,t in [(GA,'R'),(ME,'M')]:
 add(t+'-D',f,'density.md',(3,16),'Absolute relative psi error at most exp(-L/8)d(L), d(L)=.0106 L/(L-92)+(.01L^2+1.865)exp(-3L/40)+2.091 L exp(-L/8); d decreases and is <.021,.017,.016,.012 at 200,250,300,800.', 'All real L>=200 (endpoint included).','Weak D cap; strict listed endpoint constants.',DS,'Review §1: split zero bands, weighted count integral, negative logarithmic derivative comparison and Perron remainder.',codes((84,97)), 'Perron height inequalities and Table 8 constants; exact B(.875), derivative and d checks.',('ram.receipt','source-checkpoints.json','checks.stdout'),aliases=(('candidate.md',(3,13)),('density.md',(25,90))))
 add(t+'-D01-tie',f,'density.md',(13,21),'B0 implies the exact D01 (1/64)x^(7/8)L^2 majorant; adding it does not enlarge the set of attainable consequences.', 'All real x>=exp(200) for the input; all matched theorem domains for implication of premises.', 'Input weak; B0 proves strictly stronger pointwise.',DS,'Review §1: .021<625<=L^2/64 yields logical substitution of the missing premise.',status=TIE,comp='Identical deductive strength; conditional on original QRH remaining available. No extrapolation to D02.',others=(t+'-D',),aliases=(('candidate.md',(3,13)),('STAGE_STATUS.json',1)))
add('R-root-local',GA,'ramanujan.md',(10,23),'n=38358837682, pi(n)=1644673232, pi(x/e)=632207037 throughout [n,n+1], unique r in n+(.21792636,.21792637) satisfying the printed equation, and R(x) has the sign of x-r on [n,n+1).','Real x in [n,n+1) for local signs, x/e cell also at n+1.','Strict bracket/sign off root; equality at r.',['Elementary prime count and log monotonicity; no imported prime count.'],'Review §2: ordered floor-quotient prime sieve, monotonic coefficient and opposite directed signs.',codes((219,241)),'Prime counts, fixed floor of x/e, bracket.',('ram.receipt','root.stdout','checks.stdout'),aliases=(('candidate.md',(17,22)),('certificates.md',(39,49))))
add('R-integer-bridge',GA,'ramanujan.md',(23,27),'R(x)>0 for reals in the unit cells based at m=n+1,...,10^11-1 (and at 10^11).','[38358837683,10^11] real; each integer success through 10^11.','Strict.',DP,'Review §2: inherit integer computation, monotone positive multiplier and shifted count, constant unshifted count in each half-open cell.',ob='Independent full sweep unnecessary at original trust.',status=BASE)
add('R-finite-bridge',GA,'ramanujan.md',(27,33),'R(x)>0 by published finite verification on [10^11,1.15*10^16].','Entire closed real interval.','Strict.',DP,'Uses Lemma 3.4 as literature computational result, not full-RH Theorem 1.3.',trust='Published finite computation (not independently reproduced).',status=BASE)
add('R-real-ray',GA,'ramanujan.md',(15,33),'R(x)>0 for every real x>r, and R(x)>=0 for x>=r with R(r)=0. The open onset r is exact.','(r,infinity) and [r,infinity) respectively.','Strict off r; weak with equality at r.',DP+FP+DS,'Review §2: local test, integer-to-real bridge, published real interval, exp(36.6)<1.15e16, connected analytic gap and v4 tail.',codes((232,241),(246,276)),'Real joins and strict cell and tail tests.',('checks.stdout','ram.receipt','gap.stdout','trade.stdout'),comp='Extends the retained old rays and fixes literal PT near-n real reading; itself a B0 theorem.',others=('R-root-local','R-integer-bridge','R-finite-bridge','R-ray-36.6'),aliases=(('candidate.md',(17,22)),))
add('R-integer-ray',GA,'ramanujan.md',(15,17),'38358837683 is the least integer onset of the strict Ramanujan inequality.', 'All integers from 38358837683, fails at predecessor.','Strict on ray.',DP+FP+DS,'Review §2: connected real result and negative value at n.',codes((232,241),(246,276)),'Replay root and joins.',('root.stdout','ram.receipt'),kind='integer',others=('R-real-ray',))
add('R-PT-endpoint',GA,'ramanujan.md',(35,42),'The printed Platt–Trudgian early interval cannot literally hold for all reals; its integer early part and [n+1,e^58] hold by the joined proof.', '(n,r) for negative signs; [n+1,e^58] for positive signs, in particular its integers.','Strict.',DP,'Exact example: x=38358837682.1 has R(x)<-7900000. This is a source counterexample, not a false candidate branch.',codes((232,241)), 'Directed counterexample evaluation with replayed counts.',('root.stdout','checks.stdout'),others=('R-real-ray',))
add('R-old-9658',GA,'ramanujan.md',(32,33),'Dudek–Platt original unconditional Ray R>0 from exp(9658).','All real x>=exp(9658).','Strict.',DP,'Source comparison retained; also implied by the connected real result.',status=BASE)
add('R-old-3915',GA,'gap-results.md',(28,30),'The old sign-only ray from exp(3915) is retained, and certified G>1 starts already at exp(43.16).','x>=exp(3915) for old sign; x>=exp(43.16) for target.','Strict.',DP+FP+DS,'Source sign formulation has no quantitative positive margin by itself; candidate supplies the stronger joined proof independently of its early printed endpoint.',codes((246,276)), 'See R-ray-43.16.',('gap.stdout','trade.stdout'),status=BASE,others=('R-ray-43.16',))
add('R-Ei',GA,'ramanujan.md',(56,71),'S(t)<exp(-t)li(exp t)<U(t) with factorial order 24 and upper term 5*25!/t^26; tU(t)<1.04 from 36.', 't>=35, second inequality t>=36.', 'Strict.',['Dusart2018 §5.1 p.13 normalization.'],'Review §2: series enclosure anchor, explicit differential residuals and integrating factor.',codes((104,120),(151,168)),'Finite exact interval anchors.',('ram.receipt',))
rbs=[
 ('ABEL',(84,94),'Anchored theta-to-pi transfer with K_b and upper C exp(at)/((a-2/b)t²) for each directed integrand cap.','x>=600 and t>=b (anchoring in t>=log 600); a>2/b.',(100,114)),
 ('v1',(96,100),'Absolute normalized pi error <=.039789(t²+2t)exp(-t/2)+5t exp(-t).','log(600)<=t<=58.',(100,114)),
 ('v2',(101,108),'Absolute pi residual bound v2=1.05e-12(1+1.04/t)+(115+248/t)exp(-t/2)+7e-11(t/58)exp(58-t).','t>=58.',(143,144)),
 ('v3',(109,114),'Absolute pi residual bound v3=.022(1+1.16/t)exp(-t/8)+1.5e-12(t/200)exp(200-t).','t>=200.',(145,146)),
 ('v4',(109,114),'Absolute pi residual bound v4=.0161(1+1.16/t)exp(-t/8)+2e-18(t/300)exp(300-t).','t>=300.',(147,150)),
 ('vc',(115,128),'Directional vc minimum over ten heights: A(1+1.11/t)+(C+side)(1+2.48/t)exp(-t/2)+K(t/21)exp(21-t), sides 1.06 and -.97.','Stated use 21<=t<=75; derivation valid for t>=21, including actual first cells to right of 75.',(122,131)),
 ('vJ',(132,165),'Directional weighted average vJ as printed, with C+1.08/C-1, anchor scale at y=e^21 and 50 absolute J_{1/2} allowance.','35<=t<=58 under the proof; CLI begins at 35 and selects v2 from 58.',(132,142)),
 ('sign',(75,82),'Upper directional error v_+=0 using sourced pi<li.','36.6<=t<=39.47, unshifted only.','cut')]
for tag,L,s,dom,code in rbs:
 add('R-'+tag,GA,'ramanujan.md',L,s,dom,'Majorants weak; underlying sign strict where used.',FP+(DS if tag in ['v3','v4'] else []),'Review §2 directional transfers: each source endpoint, power correction and anchor checked; vc right-boundary usage covered by same ray proof.',codes(code if code!='cut' else (189,199),(175,181)),'Constants and respective switch points.',('ram.receipt','checks.stdout'))
add('R-envelope',GA,'ramanujan.md',(169,197),'G(t)>t^6(S(t-1)/t-U(t)^2)-t^5 v_-(t-1)/(t-1)-t^4 v_+(t)(2tU(t)+v_+(t)); retain maximum of valid pieces.', 't>=36.6 for analytic envelope; max with root and each stated profile on its own domain.','Strict on available branches (0 only from x>r).',FP+DS,'Review §2: exact normalization and shifted floor, nonnegative upper square, algebraic lower polynomial and directed whole cells.',codes((151,218)),'The code checks the smaller degree-52 minorant and upper factor 2.08, not exact nonpolynomial envelope.',('ram.receipt','gap.stdout','trade.stdout'),others=('R-real-ray',),aliases=(('gap-results.md',(3,8)),))
rays=[('36.6','0'),('36.7','.065'),('36.8','.10'),('36.99','.20'),('39.61','.25'),('39.7','.27'),('40','.385'),('40.5','.50'),('41','.64'),('41.93','.80'),('42','.815'),('43','.979'),('43.16','1')]
for l,(a,c) in enumerate(rays,14):
 add('R-ray-'+a,GA,'gap-results.md',l,'G(L)>'+c+' (equivalently R(x)>x² times that margin divided by L^6).','Closed real log ray L>='+a+'.','Strict.',FP+DS,'Review §2: earliest partial cell(s), subsequent supported margins and handoff at 49 and 400; no finite window extrapolated.',codes((183,218),(246,276)),'Read closed intervals in gap/trade outputs, and final tail dominance.',('gap.stdout','trade.stdout','ram.receipt'),comp='New secondary B0 ray; at matching margins D01 produces no change.',aliases=(('gap-results.md',(46,52)),)+((('candidate.md',(23,25)),) if a in ('36.99','43.16') else ()))
windows=[('37','39.47','.21'),('37.2','39.47','.29'),('37.3','39.47','.33'),('38','39.47','.57'),('39','39.47','.82'),('45','65','1.18'),('46','60','1.24'),('48','59','1.28')]
for l,(a,b,c) in enumerate(windows,37):
 add('R-window-'+a,GA,'gap-results.md',l,'G(L)>'+c,'Closed L in ['+a+','+b+']','Strict.',FP,'Review §2: compare the signed exact cells on this whole window, with separate t,t-1 thresholds.',codes((183,205),(253,270)),'Every cell enclosure and branch cut in the stated window.',('gap.stdout','ram.receipt'),comp='Finite-window strength tradeoff, not a full-ray extension; no D01 change.')
for tag,L,a,b,c in [('39.47-join',(48,49),'39.47','39.7','.20'),('0-join',(50,52),'36.75','36.8','0'),('03-join',(50,52),'36.8','37','.03'),('1-join',(50,52),'43.2','49','1')]:
 add('R-'+tag,GA,'gap-results.md',L,'Support for the joined rows: G(L)>'+c+' on this implemented subinterval.','Closed ['+a+','+b+']','Strict.',FP,'Whole-cell certificates include the edges (positive error included immediately on right side of sign cut).',codes((253,270)),'Subinterval checks.',('gap.stdout',),port=False)
polys=[('49','infinity','[1,13.69]'),('55-145','145','[1,14,115]'),('55-175','175','[1,14,40]'),('62','106','[1,14,145,1000]'),('215','infinity','[1,14,120]'),('240','infinity','[1,14,145,850]'),('265','infinity','[1,14,145,1412,7000]'),('300','infinity','[1,14,145,1412,13985]'),('325','infinity','[1,14,145,1412,13985,145450]'),('400','infinity','[1,14,145,1412,13985,145450,1500000]'),('550','infinity','M_11'),('850','infinity','M_18+15700000000000000000000/L^19')]
for l,(tag,b,c) in enumerate(polys,62):
 a=tag.split('-')[0]
 add('R-poly-'+tag,GA,'gap-results.md',l,'G(L) exceeds '+c+' (lists mean reciprocal-log polynomial).', 'L in ['+a+','+b+(')' if b=='infinity' else ']'),'Strict.',FP+DS,
 'Review §2: residual polynomial after exact subtraction, plus '+('dedicated analytic scaled tail test.' if int(a)>=400 else 'whole-cell test to end of domain or 400, then common coefficientwise tail for rays only.'),codes((160,218),(251,251),(262,276)), 'Actual target '+c+' checked (weaker order-18 check is not the degree-19 proof).',('ram.receipt','gap.stdout','trade.stdout'),aliases=(('candidate.md',(23,27)),('gap-results.md',(75,82))))
add('R-850-weaker-test',GA,'verify.py',(272,276),'G>M_18 at 850 and beyond (also a consequence of the stronger written row).','L>=850.','Strict.',FP+DS,'Independent weaker tail code path; dominance by R-poly-850 is retained.',codes((207,218)),'Tail check.',('gap.stdout',),others=('R-poly-850',),port=False)
add('R-orders',GA,'orders.md',(3,60),'For every integer j>=0 the exact algorithm returns integer a_j and G(L)>sum_{k=0}^j g_k/L^k for all L>=a_j; g_k is the exact factorial convolution difference.', 'All integers j>=0, all real L>=a_j.','Strict.',DS+FP,'Review §2: coefficient positivity, ODE barriers tested at a-1, all-ray final error monotonicity, eventual positivity as the doubling mesh increases.',(('orders.py',(7,43)),),'Exact rational all-order test; replay six orders only as sanity checks, not a proof by sampling.',('orders.stdout','other.receipt'),kind='integer order; real argument',aliases=(('candidate.md',(25,27)),('gap-results.md',(75,79))))

for tag,x,s,sr in [('P','2278382','|e^gamma L P-1|<=.2/L^3','Thm. 5.9'),('Q','2278382','|e^-gamma Q/L-1|<=.2/L^3','Thm. 5.9'),('S','2278383','|sum_{p<=x}1/p-log L-M|<=.2/L^3','Thm. 5.6'),('W','912560','|sum_{p<=x}log(p)/p-L+B_3|<=.3/L^2','Thm. 5.7')]:
 add('M-original-'+tag,ME,'mertens.md',(21,25),s,'x>='+x+' inclusive.','Weak.',DU,'Review §3: direct exact source normalization and original domain; retain in pointwise minimum.',status=BASE,comp='Original threshold and strength retained, no D01 reliance.',trust='Published analytic and finite estimates at original trust.')
add('M-normalization',ME,'mertens.md',(3,13),'Exact signed S,W,Z and raw reciprocal P,Q with Euler, Meissel–Mertens and B_3 constants as written.','x>1, empty products/sums for 1<x<2.','Identities.',DU,'Review §3: exact normalizations, no decimal substitution.',(('sieve.cpp',(70,97)),),others=('M-original-P','M-original-Q'))
add('M-finite-method',ME,'certificates.md',(51,134),'Fixed-scale integer segmented certificate with exact interval gamma, M and B_3, yields whole-real normalized error caps for S,W,Z.','100000<=x<=195730000000; prefix constants through 10^8.','Weak upper caps.',DU,'Review §3: segmented Eratosthenes and endpoint order; bound each integer approximation, constant tail and monotone continuous trend. The stated bare 2^53 and 2^25 guards alone do not imply signed cubic range, but tighter mesh and original Dusart endpoint ranges prove it for the locked inputs (ancillary, no code change).',
 (('tables.py',(1,16)),('sieve.cpp',(8,132))),'Full ordinary streaming replay; verify actual hexadecimal file hashes and independently justify bounds.',('prime.receipt','sieve.stdout','checks.stdout'),aliases=(('mertens.md',(26,33)),))
add('M-finite-constants',ME,'sieve-results.txt',1,'Exact interval numerators for gamma, M, B3 at scale 2^58: '+(C/'sieve-results.txt').read_text().splitlines()[0].split(': ')[1], 'Global constants, no x restriction.','Weak endpoints.',DU,'Review §3: trapezoid harmonic limit with N_gamma=2^18 and rigorously bounded H=10^8 correction tails.',(('tables.py',(8,16)),('sieve.cpp',(66,77))),'Original candidate commands and stream first pass.',('prime.receipt','sieve.stdout'))
for l,line in enumerate((C/'sieve-results.txt').read_text().splitlines()[2:],3):
 a,b,s,w,z=re.findall('[0-9]+',line.replace('/10000',''))
 add('M-bin-'+a,ME,'sieve-results.txt',l,'L^3|S|<='+s+'/10000, L^2|W|<='+w+'/10000, L^3|Z|<='+z+'/10000; both relative product errors <=exp('+z+'/(10000L^3))-1.','All real x in ['+a+','+b+'], both endpoints.','Weak.',DU,'Review §3: original streaming algorithm and real-cell argument; enclosure of Z converted to both actual relative ratios.',(('sieve.cpp',(78,132)),),'Replay of every certified cell up to the last endpoint, including branch boundaries.',('sieve.stdout','prime.receipt','checks.stdout'),comp='Retain stronger local choices (especially original branches near their thresholds). Matched D01 change zero.',aliases=(('mertens.md',(26,33)),))
for x,m,w,p in [('2500000','.20','.213',52),('4000000','.161','.172',53),('20000000','.090','.096',54),('50000000','.057','.062',55),('100000000','.057','.060',55)]:
 add('M-suffix-'+x,ME,'mertens.md',p,'Both relative product errors and |S| <= '+m+'/L^3; |W| <= '+w+'/L^2.','All real x>='+x+' inclusive.','Weak (sufficient tests have strict slack).',MT+DS,'Review §3: suffix maxima across every bin, conservative product conversion at log onset, and .051 analytic join.',(('sieve.cpp',(96,132)),('mcheck.py',(13,32))),'Suffix conversion and join; recorded separately from individual table caps.',('sieve.stdout','mcheck.stdout','checks.stdout'),comp='Earlier/smaller error tradeoffs against inherited .2 and .3 on matched domains; D01 changes nothing.',aliases=(('mertens.md',(50,61)),)+((('candidate.md',(28,37)),) if x=='50000000' else ()))
for i,(a,b,c) in enumerate([('26','30','.051'),('30','40','.010'),('40','58','.0004'),('58','100','.00000011'),('100','210','.000000047')],1):
 add('M-CH-cell-'+a,ME,'mertens.md',(205,219),'Scaled log/product and sum caps <'+c+' on the indicated CH2 finite cell; full relative conversion included.', 'Closed log interval ['+a+','+b+'].','Strict.',MT,'Review §3: analytic sign, height check, left/right evaluations of decreasing/increasing summands with product conversion.',(('mcheck.py',(4,17)),),'Exact interval computations at the analytic cell endpoints.',('mcheck.stdout','other.receipt'),port=False)
 add('M-log-ray-'+a,ME,'mertens.md',(34,38),'Both relative product errors and |S| < '+c+'/L^3; |W| < '+c+'/L^2.','All real L>='+a+'.','Strict.',MT+DS,'Review §3: chain of tested CH2 cells and the decreasing density end join at 210.',(('mcheck.py',(4,18)),('mcheck.py',(21,32))),'Five cells, last join 210; finite sweep ends strictly later than exp(26).',('mcheck.stdout','sieve.stdout','other.receipt'),comp='Whole B0 ray strictly beats original log powers on matched domain; D01 changes nothing.',aliases=(('mertens.md',(205,219)),))
for l,(a,w,h) in enumerate([('200','.190','.191'),('300','.145','.145'),('800','.109','.109')],43):
 add('M-power-'+a,ME,'mertens.md',l,'|W| < '+w+' exp(-L/8); |S| and both relative product errors < '+h+' exp(-L/8)/L.', 'All real L>='+a+'.','Strict.',DS+['Dusart2018 Prop. 4.3 p.12 and Cor. 4.5 p.13'],'Review §3: bound d(u) by d(L), apply PP then convert ratios. Scaled correction decreases and relative denominator increases.',(('mcheck.py',(21,32)),),'Exact left endpoint inequalities with density and PP and comparison to original log powers.',('mcheck.stdout','other.receipt'),comp='At each matching onset c L^2 exp(-L/8) decreases and improves original log powers; retain other locally stronger branches. No new D01 use.',aliases=(('mertens.md',(39,48)),('mertens.md',(221,231))))
add('M-psi-FiniteRH',ME,'mertens.md',(77,82),'Symmetric normalized psi interval with radius exp(-u/2)u^2/(8 pi).','59<exp(u)<=2.169e25.','Weak.', ['FiniteRH Cor.1 PDF p.4'],'Direct original psi branch, not θ range and not the π line.',status=BASE)
add('M-psi-CH1.2',ME,'mertens.md',(88,98),'CH2 normalized psi center (pi/T)coth(pi/T)-1 and radius A_T+C_T exp(-u/2).','exp(u)>max(T,10^9), all heights 10^7<=T<=3000175332800.','Weak.',FP,'Read exact normalized source formula with domain. The T range is allowed by FiniteRH.',(('mcheck.py',(4,10)),),status=BASE)
add('M-psi-CH1.3',ME,'mertens.md',(81,82),'Normalized relative psi radius pi/(3e12)+113.67 exp(-u/2).','exp(u)>=1.','Weak.',FP,'Direct original branch, not an integrable standalone bound on the infinite Abel map.',status=BASE)
add('M-psi-CH9.3',ME,'mertens.md',(81,82),'CH2 Cor. 9.3 bounds (9.3) and (9.4) in the original domain, transferred to relative psi intervals.','x>=2 (candidate envelope) with T=2pi^2 sqrt(x)/log(x)>=10^7 and verified RH through T.','Weak.',['CH2 Cor. 9.3 p.36; FiniteRH Thm.1 p.2'],'Review §3: retain original T(x) condition; on x>=2 it forces x>10^9 and x>T. The small-x artifact of the source statement is outside this proof-bearing domain.',status=BASE)
add('M-psi-Dusart-3.2',ME,'mertens.md',83,'Symmetric radius from Dusart (3.3), or the value epsilon in each Table 1 row.','x>=exp(b_0) for the chosen allowed row/parameters.','Weak.',['Dusart2018 Prop. 3.2, Table 1 pp.7–9'],'Original normalization and row-dependent threshold retained.',status=BASE)
add('M-psi-Dusart-3.3',ME,'mertens.md',83,'Symmetric radii eta_k/L^k with eta_k=.77,.85,1.66,8.16,59.18 for k=0 through 4.','All x>=2.','Strict underlying; weak interval.', ['Dusart2018 Thm. 3.3 p.7'],'Direct relative original formula and exact thresholds; also provides crude |E(y)|<=y in the sigma tail.',status=BASE)
add('M-psi-FKS-1.1',ME,'mertens.md',(84,86),'FKS (4.1) or Table 5 relative bound epsilon(x_0).','x>=x_0 with log x_0>1000, .9<sigma_2<1, 2<=c<=30 and N,K>=1; keep table conditions.','Weak.',['FKS Thm. 1.1 p.3, (4.1) p.15, Table 5 p.22'],'Optional intersection at original hypotheses only; no use at L=1000 from the theorem stated with strict onset.',status=BASE)
add('M-psi-FKS-1.2',ME,'mertens.md',(84,86),'FKS (1.6) relative cap A(x0)(L/R)^(3/2) exp(-2 sqrt(L/R)).','x>=x_0 with log x_0>1000, original zero-free region parameter R<=5.573412; Table 6 specifically R=5.5666305.','Weak.',['FKS Thm. 1.2 p.3, (5.2) p.16, Table 6 p.23'],'Optional intersection with the original source normalization and R, not a changed computation.',status=BASE)
add('M-psi-FKS-1.4',ME,'mertens.md',(84,86),'Relative cap 9.22022 L^(3/2) exp(-.8476836 sqrt(L)).','x>2.','Strict underlying.',['FKS Cor. 1.4 p.3'],'Direct original optional branch.',status=BASE)
add('M-theta',ME,'mertens.md',(106,112),'Intersect original theta intervals and I_psi minus the prime-power correction interval, including both usable lower Dusart bounds.','x>=2 for use in envelope; each original theta row/finite RH domain separately; correction lower bounds from 121 and 0 otherwise.','Weak enclosures.',FP+['Dusart2018 Thm. 4.2 p.12'],'Review §3: direct relation theta=psi-D_p and exact one-sided endpoint subtraction.')
add('M-T0-T1',ME,'mertens.md',(114,128),'Abel interval map T_j enclosing F,U from psi and W,S from theta as displayed.','All x>=2, integrals over u>=L; enforce original domains pointwise.','Weak.',MT+DS,'Review §3: right-continuous parts; limiting constants via original sum/product formulas and PP tails; only D ensures direct tail integrability of adopted intersection (D is B0).')
add('M-PP-identities',ME,'mertens.md',(130,147),'S=U+J1, W=F+J0, Z=U+J1-C_x=S-C_x; J_j integral with negative endpoint and smooth positive tail; 0<=C_x<=1/floor x, 0<=J1-C_x<=J1.','All x>=2 as used, actual prime-power tail excludes equality at x.','Identities and weak bounds.',DU+MT,'Review §3: compare exact prime-power series with constants and log product; telescope beyond floor x and apply sign-correct parts. Optional Dusart p.20 refinement only where applicable.')
add('M-PP',ME,'mertens.md',(148,156),'0<=J0<=1.001 exp(-L/2)+2.67 exp(-2L/3); 0<=J1-C_x<=J1<=J0/L.','First bound x>=121 inclusive; tail weight relation also all x>1.','Weak.',MT,'Review §3: subtract lower endpoint and integrate upper correction with exact weights; then use log(p^k)>log(x).',(('mcheck.py',(9,10)),('mcheck.py',(24,26))))
add('M-F-CH',ME,'mertens.md',(158,161),'Direct |F|<=A_T+C_T exp(-L/2), intersect with T0(Ipsi).','Height family and x>max(T,10^9) of CH2 Cor.1.2.','Weak.',MT,'Read normalized F directly from CH2, not via absolute Abel bound.',(('mcheck.py',(4,10)),))
add('M-U-from-F',ME,'mertens.md',(160,163),'U=F/L-integral_L^infty F(e^u)/u^2 du; use F interval with opposing integral signs.','x>=2, suitable F interval pointwise.','Identity and weak enclosure.',MT+DS,'Review §3: same Abel kernels and vanishing infinity limit, hence a valid retained branch even without CH2 direct U bound.')
add('M-U-weighted',ME,'mertens.md',(164,189),'U lies in [-K-pi^2/(3T^2 L^2),K] where K=(A_T+C_T exp(-L/2))/L+3 exp(-99L)/L.','x>max(T,10^9) and T in full verified height family, integrating 1<sigma<=100 with an absolute tail above 100.','Weak.',MT+DS,'Review §3: Euler product and normalization of B_sigma, uniform CH2, exact Fubini kernel, negative coth center and bounded sigma tail.',(('mcheck.py',(4,10)),),'Arithmetic specialization plus analytic unbounded sigma tail.',('mcheck.stdout',))
add('M-envelope',ME,'mertens.md',(191,201),'Intersect all stated applicable intervals and original relative outputs, with exact signed product maxima and optional inverse log interval maps.','Every real x>1 (empty below 2), each branch restricted to its own domain.','Weak as envelope; the listed strict comparisons remain strict.',DS+DU+MT,'Review §3: signed interval maps, logs of positive endpoints, and independent normalized ratios exp(-Z),exp(Z). General mathematical specification; no separate complete oracle.',(('mcheck.py',(4,32)),('sieve.cpp',(94,132))),receipts=('sieve.stdout','mcheck.stdout'),others=('M-U-weighted','M-PP','M-T0-T1','M-original-P','M-original-Q'),aliases=(('mertens.md',(69,72)),('candidate.md',(28,38))))
add('M-D01-only-maps',ME,'mertens.md',(233,240),'Using only D01 in the absolute Abel maps gives |F| <= (9L^2+128L+1024)exp(-L/8)/64, |U| <= (9L+72)exp(-L/8)/64 before PP.', 'All real L>=200.','Weak.',DS,'Review §3: exact exponential polynomial integrals, dominated pointwise before transfer by B0 (D).',status=TIE,comp='Same tail and kernels; D01-only input estimate strictly weaker, no endpoint improvement; no deduction about D02.',inp=True,others=('M-D','M-power-200'))

for row in rows:
 if row['claim_id']=='M-finite-method':
  row['actual_verification_receipts']+=['ubsan.receipt']
  row['precise_gap_or_counterexample']='No remaining proof gap: signed cubic guard alone was insufficient in abbreviated written range argument; see review §3 for a tighter bound on the same exact executed algorithm.'
 if row['claim_id']=='R-vc':
  row['precise_gap_or_counterexample']='No invalid use: executable includes left endpoint 75, and the analytically proved inequality is valid slightly beyond 75 as used there.'
 if row['claim_id']=='R-PT-endpoint':
  row['precise_gap_or_counterexample']='Counterexample to literal original-paper statement only (not submitted as a true real branch): x=38358837682.1, certified R<-7900000.'
 if row['claim_id']=='M-psi-CH9.3':
  row['precise_gap_or_counterexample']='Literal original Cor. 9.3 fails at x=1.0000001 (verified-height condition holds but psi=0, RHS<1e-14); candidate uses only x>=2 with its T condition. No candidate gap.'
 if row['claim_id']=='M-envelope':
  row['propagation']['where_it_changes_proof']='No D01 use: B0 density bound assures Abel integrability and the final analytic join.'
 if row['claim_id']=='R-envelope':
  row['propagation']['where_it_changes_proof']='No D01 use: B0 density bound feeds v3,v4 and their separate shifted arguments.'

sums={
GA:'Supported: exact real onset and integer onset, retained literature bridges, all strict constant and reciprocal-log profiles and cell windows, nonpolynomial envelope and arbitrary-order algorithm. No D01 increment.',
ME:'Supported: all original relative product and sum thresholds, all 20 finite bins and suffix rays, CH2/density rays, signed transfers and relative product envelope. No D01 increment.'}
receipt_names=[p.name for p in O.iterdir() if p.suffix=='.receipt']
report={'schema':'FOLLOWUP_MATHEMATICAL_REVIEW_V1','candidate_id':'FOLLOWUP-C004','input_stage':'D01',
'assessment_complete':True,'all_claims_inventoried':True,'no_other_arm_or_ranking_seen':True,'new_core_math_salvage_performed':False,
'original_candidate_bytes_changed':False,'reviewed_source_hashes':{'candidate':{k:r['sha256'] for k,r in files.items()},
'originals':{r['source_id']:{k:r[k+'_sha256'] for k in ('pdf','text')} for r in sources}},
'source_bibliography':sources,'actual_effort_and_verification_commands':{p:(O/p).read_text() for p in sorted(receipt_names)},
'reproduction':{'restore':'/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out /work/c004',
'review_driver':'/usr/bin/python3.10 /work/submission/replay.py ram, other, prime (one group at a time or concurrently)',
'ancillary':'/usr/bin/python3.10 -B /work/submission/checks.py; see checks.receipt',
'machine_mesh':'Unchanged source stream over [100000,195730000000], including every reported bin boundary; prime count 7842936328, cells 7453651.',
'ordinary_execution_only':True,
'published_trust_not_replayed':['OpenAIQRH proof','FiniteRH theorem computations','FKS estimate tables','Dudek–Platt real sweep and integer calculation','Dusart published computations and source sign']},
'formal_notice':'No Lean or Blueprint artifact in the paper-only packet; optional formal evidence not checked. Ordinary GCC/Python and an extra GCC UBSan execution only.',
'family_assessments':{},'claims':rows}
for f in (GA,ME):
 member=[r for r in rows if r['family']==f]
 report['family_assessments'][f]={'strongest_supported_portfolio':[r['claim_id'] for r in member if r['primary_supported_portfolio_member'] and r['M_status'] in (OK,BASE)],
 'rejected_or_incomplete_claims':[],'remaining_assessment_work':[],'summary':sums[f],
 'additional_input_status':'no_additional_improvement'}
assert len({r['claim_id'] for r in rows})==len(rows)
(O/'review.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
stage={'ready_for_review':True,'families':{f:{'status':OK,'claim_files':['review.md','review.json']} for f in (GA,ME)},'serious_attempts_documented':True}
(O/'STAGE_STATUS.json').write_text(json.dumps(stage,indent=2)+'\n')
print('rows',len(rows),{f:sum(r['family']==f for r in rows) for f in sums})
