#!/usr/bin/python3.10
"""Bind independently assessed claims to exact supplied physical LF and SHA256."""
from pathlib import Path
import json, hashlib, re
T=Path('/task'); P=Path(__file__).resolve().parent
idx=json.loads((T/'CANDIDATE_INDEX.json').read_text())
meta={int(e['packet_name'][10:13]):e for e in idx['candidate_files']}
lines={i:(T/e['packet_name']).read_bytes().decode().split('\n') for i,e in meta.items()}
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def loc(f,a,b=None):
 e=meta[f]
 assert 0<a<=(b or a)<=len(lines[f])
 return dict(file=e['packet_name'],physical_LF=a,physical_LF_end=b or a,sha256=e['sha256'],restored_name=e['original_name'])
src=json.loads((P/'source-checkpoints.json').read_text())
R='Ramanujan'; M='Mertens'
S='supported_at_stated_trust_tier'; B='baseline_retained'; E='equivalent_or_weaker'
DS='Dusart2018'; CH='CH2'; FK='FKS'; FH='PlattTrudgianFiniteRH'; PT='PlattTrudgian2021'; DP='DudekPlatt2015'; QR='OpenAIQRH'
density=[QR+' Theorem 1.1 p.4 for B0',FH+' Theorem 1 p.2',FK+' Cor. 2.9 (2.17) pp.7–8/Table 8 p.26 and Theorem 3.2 p.8',PT+' Lemma 2 p.4']
li=[DS+' §5.1 p.13, proof of 5.1 p.15 and Cor. 5.2 pp.15–16',FH+' Cor. 1 p.4',CH+' Cor. 1.2–1.3 p.3 and Prop. 9.1 pp.34–36',DS+' Prop. 4.3 and Cor. 4.5 pp.12–13']
ms=[DS+' Theorems 5.6,5.7,5.9 pp.17–20',DS+' Prop. 4.3 and Cor. 4.5 pp.12–13']
weighted=ms+[CH+' Cor. 1.2 p.3, (7.2) p.22 and Prop. 9.1 pp.34–36',FH+' Theorem 1 p.2']
base='B0 = cumulative seven originals at their exact hypotheses and published-computation trust.'
new='B0 + exact FOLLOWUP-D02: all real x>=e^200, |psi(x)-x| <= x^(27/32)(log x)^2/64.'
code={'gap':('verify.py-gap.log',(47,160,276)),'trade':('verify.py-trade.log',(47,207,251)),
      'root':('verify.py-gap.log',(47,219,241)),'local':('localgap.py-localgap.py.log',(26,5,39)),
      'oldorders':('orders.py-50.log',(37,7,48)),'claims':('claims.py-orders.log',(15,5,88)),
      'early':('claims.py-orders.log',(21,5,42)), 'mnew':('mnew.py-mnew.py.log',(34,4,56)),
      'mfinite':('mfinite.py-mfinite.py.log',(32,6,50)), 'mcheck':('mcheck.py-mcheck.py.log',(28,4,32)),
      'comp':('comparison.py-comparison.py.log',(17,4,48)), 'c++':('sieve-run.stdout',(44,8,132)),
      'anc':('ancillary.log',None)}
claims=[]
def add(id,f,ff,stmt,domain,why,*,sources=(),impl=(),runs=(),ass=base,strict='non-strict or identity as written',kind='real x',status=S,prop=None,keep=(),gap=None):
 written=loc(*ff)
 rec=[dict(payload=code[r][0],sha256=sha(P/code[r][0]),status=0) for r in runs]
 formulas=[loc(*t) for t in impl]+[loc(*code[r][1]) for r in runs if code[r][1]]
 if prop is None:
  prop=dict(input_used='B0 only',where_it_changes_proof='No hypothetical input used here.',matched_comparison='Same consequence under B0+D01 and B0+D02; optional improvements may coexist.')
 if isinstance(prop,tuple):
  prop=dict(zip(('input_used','where_it_changes_proof','matched_comparison'),prop))
 act='\n'.join(lines[ff[0]][ff[1]-1:(ff[-1] if len(ff)>2 else ff[1])])
 claims.append(dict(claim_id=id,family=f,written_source=written,written_excerpt=act,exact_statement=stmt,assumptions=ass,full_domain=domain,strictness=strict,real_or_integer=kind,
  baseline_comparison=prop['matched_comparison'],source_locators=list(sources),derivation_check=why,
  numerical_obligations=('Exact directed endpoint/cell certificates plus analytic domain/monotonicity checks in review.md.' if runs else 'Analytic/source verification; no independent numerical sample used as theorem.'),
  actual_verification_receipts=rec,implemented_source=formulas,implemented_readback=('The bound, inputs and directions at these code locators are separately audited in the corresponding review.md section; no external project oracle.' if formulas else 'Written mathematical/source result; no standalone executable theorem.'),
  retained_valid_branches=list(keep), M_status=status,precise_gap_or_counterexample=gap,propagation=prop,
  V_status='Not formal-checked; paper-only runtime, no Lean/Blueprint source or source-first PV. Ordinary replay only where indicated.',
  remaining_trust='Pinned originals including published computations, written derivations, and interpreter/compiler trust for exact ordinary replay as applicable.'))
def spec(where,match):return ('D02 in the new column',where,match)
def tbl(f,i): return [s.strip() for s in lines[f][i-1].strip().strip('|').split('|')]
for f in (R,M):
 p=f[0]+'-' if f==R else 'M-'
 add(p+'D',f,(20,3,90),'|psi(x)-x|/x <= e^(-t/8)d(t), with d(t) as displayed; decreasing, checked caps .021,.017,.016,.012 at 200,250,300,800','t>=200','Quartic-log cutoff T=e^(t/4); layer identity plus density tail and low reciprocal-zero bound.',sources=density,impl=[(47,84,99)],runs=['gap'])
 add(p+'D01-tie',f,(20,13,21),'B0 implies the exact D01 |psi-x| <= x^(7/8)t^2/64; no extra deductive strength. D02 independently implies D01 on the same ray.','Every real t>=200 for implication; all theorems for substitution','d(t)<.021<200^2/64; direct comparison of exponents for D02.',sources=density,status=E,prop=('D01 redundancy','B0 proves the full hypothetical D01 premise.','Same achievable domains and strengths, not a discovery baseline.'))
 add(p+'D02-zeta',f,(18,16,41),'D02 implies zeta has no zeros with Re s>27/32; neither boundary-line exclusion nor extension to general Hecke L-functions.','Complex open half-plane','Euler/Stieltjes Mellin transform, local integral domination and nonzero zero residues.',sources=[QR+' Theorem 1.1 p.4; (12.1) p.85, Prop. 20.3 and conclusion pp.195–197'],kind='complex zeta statement from real-x input',ass=new,prop=spec('Mellin continuation removes the tail amplitude and finite initial segment from the spectral deduction.','New b=27/32 versus B0 b=7/8; no logical independence asserted.'))
 for i,a,b,s in [('reciprocal',59,75,'Density tail (1), including a cutoff at an ordinate.'),('high-local',77,113,'Absolute high-strip model and local layer cap (2), decreasing true scaled sum.'),('high-coarse',114,135,'Coarser two-band cap (3), and its minimum with (2).'),('residual',137,181,'Whole-real approximation (4) by infinite high strip, termwise residual monotonicity (5).')]:
  add(p+'spectral-'+i,f,(18,a,b),s,'Y>=H and A(s)>q/v for (1); t>=150 otherwise','Positive layers, conservative truncation by T, original all-real formula, and termwise derivative checks; endpoints included.',sources=density,impl=[(19,7,75)],runs=['claims'],ass=base+' Either spectral column; D02 required for b=27/32.',prop=spec('Only the right strip coordinate b changes; scaled residual and final band updated.','Matched spectral implementation differs by 1/32 in final power.'))
 add(p+'zeta-recovers-exact-D02',f,(42,18,27),'Re s>27/32 zero exclusion implies exact D02 psi input by the furnished density/Perron bound.','every t>=200','Absolute high strip plus residual <.28 in scaled units at 200, freezes and is below t²/64.',sources=density,impl=[(15,74)],runs=['claims'],ass=base+' Zeta zero exclusion in Re s>27/32.')
# Shared old gap metadata
root_src=[DP+' §3.1 pp.8–10, Lemma 3.4 p.10',PT+' Theorem 2 p.3']
for z in [
 ('root-local',10,23,'Both near-root counts and unique zero in n+(.21792636,.21792637); sign of x-r','[n,n+1) (shift count also at n+1)','root'),
 ('integer-bridge',23,27,'Use the last integer failure through 10^11 and extend along each real unit cell','n+1<=x<=10^11',None),
 ('finite-bridge',27,33,'Inherited finite real strict positivity, overlapping the analytic cover','[10^11,1.15*10^16]',None),
 ('real-ray',15,33,'R>0 on x>r; R(r)=0; R>=0 on x>=r','Exact strict open ray, and closed nonnegative ray','root'),
 ('integer-ray',15,17,'Least integer strict onset 38358837683','integer x>=38358837683','root'),
 ('PT-endpoint',35,42,'Reject only the literal noninteger early reading of original PT; keep integer range, and real range from n+1','(n,r) fails; valid [n+1,e^58]','anc'),
 ('old-9658',32,33,'Unconditional source strict Ramanujan inequality','x>=e^9658',None),
 ('old-3915',35,42,'Original PT late strict tail, also independently covered by candidate analytic tail','x>=e^3915',None)]:
 k,a,b,s,d,r=z
 add('R-'+k,R,(39,a,b),s,d,'See review.md root and finite joins. Use the last integer counterexample, monotonic real extension, published finite bridge and analytic overlap as applicable.',
 sources=root_src+[DP+' Theorem 1.2 p.2'],runs=[r] if r else [],status=B if k in ('integer-bridge','finite-bridge','old-9658','old-3915') else S,
 kind='integer x' if k=='integer-ray' else 'real x',strict='Strict positivity or explicit equality/nonnegativity as stated',
 gap='Original literal real reading (not an active candidate claim): x=38358837682.1, R<-7900000.' if k=='PT-endpoint' else None)
for a,b,s,k,d in [(20,21,'New analytic positivity from log 36.53 with already-valid tail overlap','analytic-36.53','t>=36.53'),
 (22,25,'R(x)>67000000(x-r)','local-linear','r<x<n+1'),
 (26,37,'G(t)>.000007','local-integer-cells','38358837683<=x<=38358847682')]:
 add('R-'+k,R,(38,a,b),s,d,'Independent real-domain endpoint monotonicity; analytic early join or local counted unit cells, as applicable.',sources=li,runs=['early','claims'] if k.startswith('analytic') else ['local','root'],strict='strict')
for k,a,b,s,d,i,j in [
 ('Ei',56,71,'PV Li strict 24th-order barriers S<f<U and tU<1.04','t>=35 (tU from 36)',104,168),
 ('ABEL',84,94,'Anchored theta-to-counting transfer and exponential rate integral bound','x>=600, log anchor b<=t and a>2/b',100,150),
 ('v1',96,100,'Symmetric kt²-based v1 transfer','log600<=t<=58',100,114),
 ('v2',101,108,'Symmetric 1.05e-12 + square-root and anchor v2','t>=58',103,144),
 ('v3',109,114,'Symmetric v3 bound using old D','t>=200',143,146),
 ('v4',109,114,'Symmetric v4 bound using old D','t>=300',147,150),
 ('vc',115,128,'Directional C+1.06,C-.97 bound with ten CH2 heights','21<=t<=75 claimed, same proof valid above 75',122,131),
 ('vJ',132,165,'Directional bound by CH2 weight averaging, C+1.08 and C-1','35<=t<=58',132,142),
 ('sign',75,82,'Unshifted positive normalized counting error bounded by 0','36.6<=t<=39.47',189,194),
 ('envelope',169,209,'Strict pointwise Li barrier lower envelope and valid-domain maximum with table branches','t>=36.6 for this analytic envelope (root branch separate)','160',218)]:
 add('R-'+k,R,(39,a,b),s,d,'PV, exact Abel endpoints, applicable heights and directional counts checked in review.md.',sources=li,impl=[(47,int(i),j)],runs=['gap'])
add('R-early-vJ',R,(38,61,83),'Updated directional averaged cap with enlarged heights, actual Jcor, square lower 1+2/t+8/t² and extended sign cut.','35<=counting log argument<=58; unshifted sign up to 39.471 in early certificate','Both directions and monotonicity checked, with each source’s hypotheses.',sources=li,runs=['early','claims'])
for i in range(14,27):
 a,v=tbl(23,i)
 add('R-ray-'+a,R,(23,i),'G(t)>'+v.split()[0],f't>={a}','Trade prefix, stronger closed cells through 49, polynomial to 400, common degree-six tail thereafter.',sources=li+density,runs=['gap','trade'],strict='strict')
for i in range(37,45):
 d,v=tbl(23,i)
 add('R-window-'+str(i),R,(23,i),'G(t)>'+v,'closed log '+d,'Whole-cell signed polynomial residual with separate x/e budget; no extension beyond window.',sources=li,runs=['gap'],strict='strict')
for i in range(62,74):
 d,v=tbl(23,i)
 add('R-poly-'+str(i),R,(23,i),'G(t)>'+v,'inclusive log domain '+d,'Positive shifted expansion minus upper square; exact finite cells and tail where stated. Stronger 850 coefficient uses trade.',sources=li+density,runs=['gap','trade'],strict='strict')
for i,s,d in [(254,'G>0','[36.75,36.8]'),(254,'G>.03','[36.8,37]'),(257,'G>.20','[39.47,39.7]'),(260,'G>1','[43.2,49]'),(274,'G>M18','[850,infinity)')]:
 add('R-internal-'+s,R,(47,i),s,'log '+d,'Retained implemented subtest; necessary joins or weaker than an explicit final row.',sources=li,runs=['gap'],strict='strict')
add('R-orders',R,(36,3,60),'For every integer j>=0 use exact terminating orders.py to get a_j and G(t)>M_j(t) for t>=a_j.','integer j>=0 and real t>=a_j','Positivity of next coefficient; variation of constants checked at a-1, monotonic errors and doubling termination.',sources=li+density,runs=['oldorders'],strict='strict')
for i in range(47,54):
 cols=tbl(38,i)
 for a,c in [cols[:2],cols[2:]]:
  if a:
   add('R-early-'+a,R,(38,i),'G(t)>'+c,'t>='+a,'Exact early cells through 43.16 then old G>1 branch.',sources=li,runs=['early','claims','gap','trade'],strict='strict')
for a,z,c in [('44.7','65','1.18'),('45.1','65','1.22'),('46','63','1.25'),('47.1','59','1.28'),('48.01','53','1.30')]:
 add('R-new-window-'+a,R,(38,58),'G(t)>'+c,f'{a}<=t<={z}','Certified by early.run, no extrapolation.',sources=li,runs=['early','claims'],strict='strict')
for k,i,j,s,d in [
 ('theta-anchored',261,284,'C_theta and symmetric V_a counting cap (8), min over valid anchors and combine old directed caps','a>=150, t>=a for each anchor'),
 ('pointwise',286,299,'Exact-Li signed lower envelope (9) and symmetric absolute-error variant; retain older maxima','t>=151, both shifted and unshifted arguments validated'),
 ('barrier48',299,333,'Strict Li barriers at 110 and degree-100 gap polynomial; finite tests and monotone tail errors','t>=110 for barriers, >=151 when using both new scaled counting budgets'),
 ('fallback',345,361,'Direct D02 counting plus .051 t^6 exp(-5t/32) absolute Li gap','counting t>=200, scaled sharper cap t>=220, gap t>=221')]:
 add('R-'+k,R,(18,i,j),s,d,'Review §New counting branch; separate proof-bearing theta/counting domains and Li normalization.',sources=li+density,impl=[(19,90,152)],runs=['claims','comp'] if k=='fallback' else ['claims'],
     ass=new if k=='fallback' else base+' D02 needed only for b=27/32 branch.',prop=spec('Direct t² psi majorant from 200.' if k=='fallback' else 'Replace b=7/8 with 27/32 in spectral theta cap and shifted/unshifted Abel transfers.','New spectral branch tighter where the density-free fallback overlaps.' if k=='fallback' else 'Take all older branches; smaller furnished Li budget from 171.'))
add('R-Li-dominance',R,(38,99,124),'D02 exact-Li lower envelope improves strictly over furnished matched B0 counting budgets.','all t>=171, both t-1,t>=170','Anchor 165 rescaled at 170 <.33, compared to both inherited floors and .005e^(-s/8), algebraically on the whole ray.',sources=li+density,runs=['claims'],ass=new,strict='strict',prop=spec('D02 narrows the absolute counting budgets in both directions.','Strict saving on the matched furnished Li branch; not an optimal bound across all deductions.'))
for i in range(132,140):
 a,c0,c2=tbl(38,i)
 for b,c in [('B0',c0),('D02',c2)]:
  add(f'R-Li-{a}-{b}',R,(38,i),f'|G-Li gap| < {c} t^4 exp(-(1-b)t)','t>='+a,'Frozen budget at shifted onset, monotone in powered units.',sources=li+density,runs=['claims'],ass=new if b=='D02' else base,strict='strict',prop=spec('b determines exponent and error transfer.',f'Matched {c0} exp(-t/8) vs {c2} exp(-5t/32); at 200 ratio <.028 throughout.') if b=='D02' else None)
for i in range(157,173):
 a,c,b=tbl(38,i)
 add('R-adv-'+str(i),R,(38,i),'G(t)>'+c,'t>='+a,'Early B0 through 150 if needed, exact degree-100 closed cells and monotone whole tail.',sources=li+density,runs=['early','claims'],ass=new if b=='D02' else base,strict='strict',prop=spec('D02 changes the collar and tail, not any early B0 proof.','Matched M2 222/188; third coefficient 2/64 at log 49. Tradeoffs retained.') if b=='D02' else None)
for i in range(181,190):
 cols=tbl(38,i)
 for j,a,b in [cols[:3],cols[3:]]:
  if j:
   for pm,d in [('B0',a),('D02',b)]:
    add(f'R-order-{j}-{pm}',R,(38,i),'G(t)>M_'+j,'t>='+d,'Exact high-order tail, using full upper square and separate anchor valid at t-1.',sources=li+density,runs=['claims'],ass=new if pm=='D02' else base,strict='strict',prop=spec('Decreased residual from changed b opens earlier monotonic tail.',f'Fixed M_{j}: B0>= {a}, D02>= {b} sufficient log onsets.') if pm=='D02' else None)
for i,b,c,m in [(215,'B0',37,'.14'),(216,'D02',28,'.07'),(217,'D02',37,'.18')]:
 add(f'R-all-linear-{i}',R,(38,i),'G(t)>M_j+'+m+'(j+5)!/t^(j+1)',f'integer j>=35, real t>={c}(j+5)','Moving anchor factorial barrier, scaled square and counting budgets for all orders.',sources=li+density,runs=['claims','anc'],strict='strict',kind='integer order j and real x',ass=new if b=='D02' else base,
 prop=spec('D02 changes D(ce^(1-alpha*c))^n through exponent alpha.', 'Fixed .07 slope 37→28; slope 37 margin .14→.18.') if b=='D02' else None)
add('R-general-slope',R,(38,223,229),'Margin .05 with c>=27, rho=c exp(1-alpha c)<1, n>=40 and D rho^n<=.116 (D=.57 D02 or .042 B0).','integer j>=35 with n=j+5, real t>=cn for each eligible rational c','Closed shifted onset and monotone order tail using the stated test; terminates per eligible c.',sources=li+density,runs=['claims','anc'],kind='integer order and real x',strict='strict',ass=base+' D02 required only for changed alpha.',prop=spec('Changes both the exponent and furnished counting coefficient.','Sufficient family of slopes, not an optimized slope.'))
add('R-gap-converse',R,(42,49,112),'Any eventual one-sided exact-Li lower gap G>=Lcal-O(t^4 exp(-(1-b)t)) implies zero-freeness of zeta in Re s>b. At b=27/32 equivalent under B0 to D02.','1/2<b<1, eventual whole real ray','Positive-part recurrence, nonnegative Mellin abscissa argument; no two-sided counting premise assumed.',sources=li+density,impl=[(15,87)],prop=spec('Converse targets the exponent of the D02 spectral branch.','A B0 proof of this shape at 27/32 would imply exact D02; no independence assertion.'))

# Old and new Mertens branches
for k,a,c,sh in [('P',2278382,'.2','/t^3'),('Q',2278382,'.2','/t^3'),('S',2278383,'.2','/t^3'),('W',912560,'.3','/t^2')]:
 add('M-original-'+k,M,(30,21,25),f'{k} normalized absolute error <= {c}{sh}',f'x>={a}','Direct relative or exact normalized residual, not a log-product approximation.',sources=ms,status=B)
add('M-normalization',M,(30,3,13),'Four exact normalized errors and exact M, B3, gamma, Z; empty products and sums on (1,2).','every real x>1','Dusart normalization and raw reciprocal product identity. The 5.6 and 5.9 onsets differ.',sources=ms,impl=[(29,3,23)])
add('M-finite-method',M,(13,51,134),'Full segmented arithmetic finite certificate, using outward signed residuals and closed real-cell extensions.','100000<=x<=195730000000','Exact sieve and analytic rounding/range proof plus executed complete stream; see signed cubic range detail in review.md.',sources=ms,runs=['c++'],impl=[(45,3,16)])
add('M-finite-constants',M,(43,1),'Gamma, M, B3 intervals from emitted numerator pairs at scale 2^58.','fixed mathematical constants','Harmonic trapezoidal anchor; finite prime-power sums through 1e8 and explicit all-integer tails.',sources=ms,runs=['c++'],impl=[(45,3,16)])
for i in range(3,23):
 s=lines[43][i-1]
 lo,hi,wS,wW,wZ=re.search(r'\[(\d+),(\d+)\].*: (\d+) (\d+) (\d+)',s).groups()
 add('M-bin-'+lo,M,(43,i),f't³|S| <= {wS}/10000; t²|W| <= {wW}/10000; t³|Z| <= {wZ}/10000; relative errors <= exp({wZ}/(10000 t³))-1.',f'{lo}<=x<={hi} closed','Monotone residual interval and right-log power in the complete replay; product conversion accompanies written row.',sources=ms,runs=['c++'],impl=[(30,26,33)])
for a,v,w,i in [(2500000,'.20','.213',52),(4000000,'.161','.172',53),(20000000,'.090','.096',54),(50000000,'.057','.062',55),(100000000,'.057','.060',55)]:
 add('M-suffix-'+str(a),M,(30,i),f'Both products and |S| <= {v}/t³, |W| <= {w}/t²',f'x>={a}','Suffix maximum after product conversion and join to common analytic .051 at e^26.',sources=weighted,runs=['c++','anc','mcheck'])
for a,b,c in [(26,30,'.051'),(30,40,'.010'),(40,58,'.0004'),(58,100,'.00000011'),(100,210,'.000000047')]:
 add(f'M-CH-cell-{a}',M,(30,205,219),f'Common scaled cap < {c} for relative products and two sums.',f'closed {a}<=t<={b}','CH2 cell increasing and decreasing terms tested at their respective endpoints, exact relative conversion.',sources=weighted,runs=['mcheck'],strict='strict')
 add(f'M-log-ray-{a}',M,(30,34,38),f'Common scaled cap < {c} for relative products and two sums.',f't>={a}','Nested CH2 cells and density-tail join at 210.',sources=weighted+density,runs=['mcheck'],strict='strict')
for i,a,w,h in [(43,200,'.190','.191'),(44,300,'.145','.145'),(45,800,'.109','.109')]:
 add('M-power-'+str(a),M,(30,i),f'|W|<{w}exp(-t/8); other three <{h}exp(-t/8)/t',f't>={a}','Old D plus monotone absolute Abel kernel, PP correction, and reciprocal-product conversion.',sources=weighted+density,runs=['mcheck'],strict='strict')
for k,a,b,s,d,so in [
 ('FiniteRH',81,82,'Symmetric psi radius t² exp(-t/2)/(8 pi)','59<x<=2.169e25',FH+' Cor. 1 p.4'),
 ('CH1.2',88,98,'CH2 psi interval center (pi/T)coth(pi/T)-1, radius A_T+C_T exp(-t/2)','T>=1e7 verified through T; x>max(T,1e9)',CH+' Cor. 1.2 p.3'),
 ('CH1.3',81,82,'CH2 psi radius pi/(3e12)+113.67 exp(-t/2)','x>=2 in this envelope',CH+' Cor. 1.3 p.3'),
 ('CH9.3',81,82,'CH2 (9.3),(9.4) psi cap on its working region','x>=2 and T=2 pi² sqrt(x)/log x>=1e7 verified through T',CH+' Cor. 9.3 and proof p.36'),
 ('Dusart-3.2',83,83,'Dusart Prop. 3.2 (3.3) or Table 1 epsilon','x>=exp(b0), corresponding parameters',DS+' (3.3) pp.6–7, Table 1 pp.8–9'),
 ('Dusart-3.3',83,83,'Psi symmetric eta_k/t^k with eta=.77,.85,1.66,8.16,59.18','x>=2',DS+' Theorem 3.3 p.7'),
 ('FKS-1.1',84,86,'FKS (4.1) or Table 5 relative cap at eligible x0','log x0>1000, x>=x0; original parameters',FK+' Thm. 1.1, (4.1), Table 5'),
 ('FKS-1.2',84,86,'A(x0)(t/R)^(3/2) exp(-2 sqrt(t/R))','log x0>1000, x>=x0, lawful R<=5.573412 (tabulated 5.5666305)',FK+' Thm. 1.2, (1.6),(5.2), Table 6'),
 ('FKS-1.4',84,86,'9.22022 t^(3/2) exp(-.8476836 sqrt(t))','x>2',FK+' Cor. 1.4 PDF pp.2–3')]:
 add('M-psi-'+k,M,(30,a,b),s,d,'Source formula and hypothesis readback; retained in compatible intersections. See scope in review.md.',sources=[so],status=B,
 gap='Original literal near-one statement fails at x=1.0000001; excluded from all uses by candidate x>=2.' if k=='CH9.3' else None)
add('M-PT-envelope',M,(29,159,165),'Allow PT PNT Theorem 1 psi and Corollary 1 theta branches in the cumulative Chebyshev intersection.','actual table rows t>=X>=1000 with their own parameters','Check normalizations A vs A+.1, R=5.573412 and separate tabulated relative psi epsilon.',sources=[PT+' Theorem 1/Cor. 1 pp.2–3 and Table 1 p.3'],status=B)
for k,a,b,s,d,so in [
 ('theta',106,112,'Intersection of applicable original theta caps and psi with directed D_p correction.','x>=2; .9999sqrt x and second Dusart lower from 121',ms+[DS+' Thm.4.2 p.12 and FiniteRH Cor.1 p.4']),
 ('T0-T1',114,128,'Signed Abel map for F,U from psi and W,S from theta.','x>=2; integral to infinity with density cap',ms+density),
 ('PP-identities',130,147,'S=U+J1, W=F+J0, Z=U+J1-C_x=S-C_x, endpoint-minus-integral relation for J tails and telescoped C_x bound.','x>=2',ms),
 ('PP',148,156,'J0<=1.001 exp(-t/2)+2.67 exp(-2t/3), 0<=J1c<=J1<=J0/t.','first upper bound x>=121, other relationships x>=2',ms),
 ('F-CH',158,161,'Direct absolute F radius A_T+C_T exp(-t/2).','x>max(T,1e9), verified T>=1e7',weighted),
 ('U-from-F',161,163,'U=F/t-int_t^infty F(e^u)/u² du.','x>=2',weighted),
 ('U-weighted',164,189,'U in [-K-pi²/(3T²t²),K], K=(A_T+C_T exp(-t/2)+3exp(-99t))/t.','x>max(T,1e9), verified T>=1e7',weighted),
 ('envelope',191,201,'Whole-domain signed intersection, exact distinct relative product maxima and optional reverse log update.','x>=2 (empty branch on (1,2))',weighted+density)]:
 add('M-'+k,M,(30,a,b),s,d,'Exact Stieltjes/series or pointwise interval reasoning checked in review.md, not a finite-grid theorem.',sources=so,
     impl=[(28,4,17)] if k in ('U-weighted','F-CH') else [])
add('M-D01-only-maps',M,(30,233,241),'The two absolute-Abel D01-only maps are (9t²+128t+1024)e^(-t/8)/64 and (9t+72)e^(-t/8)/64 before correction.','t>=200','Direct integration; dominated by B0 antecedent on entire tail.',sources=ms+density,status=E,prop=('D01 direct substitution','Only changes a loose hypothesized cap, which is implied by better B0.','Never improves the same weight transfer with B0.'))
for k,a,b,s,d in [
 ('osc-weight',183,220,'(6) numerical F,U cap with same high-strip magnitude and 1/H suppression inside integrals; frozen scaled ray.','a>=150, t>=a'),
 ('common-CM',221,240,'Common C_M(a;b) (7) in e^(-alpha t) units for W and e^(-alpha t)/t for three others; and common log-power shape after t² scaling.','a>=150, t>=a'),
 ('fallback',242,257,'Direct-input absolute Abel formulas in displayed polynomial-log forms before PP and relative conversion.','t>=200'),
 ('fallback-rounded',336,343,'.123 t² exp(-5t/32) for W and .123 t exp(-5t/32) for others.','t>=200')]:
 add('M-new-'+k,M,(18,a,b),s,d,'High-strip oscillatory integrals plus integrated residual; direct-input branch instead integrates u² or u+1, with PP/product conversion when stated.',sources=weighted+density,
     impl=[(19,76,89)] if 'fallback' not in k else [(17,43,48)],runs=['mnew'] if 'fallback' not in k else ['comp'],
     ass=new if 'fallback' in k else base+' D02 needed only for b=27/32.',
     prop=spec('Use improved spectral right edge in same analytic transfer.' if 'fallback' not in k else 'Direct hypothesized psi amplitude from log 200.','Same B0 used as control; direct fallback weaker where spectral branch is used.'))
for i in range(35,44):
 cols=tbl(29,i)
 for a,c in [cols[:2],cols[2:]]:
  if a:
   add('M-D02-power-'+a,M,(29,i),f'Common strict coefficient {c} in e^(-5t/32) units for W and e^(-5t/32)/t for other three.','t>='+a,'Freeze (7), includes directed log-to-relative conversion.',sources=weighted+density,runs=['mnew'],ass=new,strict='strict',
     prop=spec('Replace b in high-strip/weighted cap and exponential.','At same starts 200,300,800 compare absolute caps, not bare coefficients in different units.'))
for a,c in [('200','.01831'),('300','.01474'),('800','.01187')]:
 add('M-B0-power-'+a,M,(29,45,58),f'Strict common coefficient {c} in e^(-t/8) weighted units or e^(-t/8)/t other units.','t>='+a,'Same method, replacing b with 7/8; tighter than inherited absolute Abel coefficient.',sources=weighted+density,runs=['mnew'],strict='strict')
for i in range(71,81):
 a,b,d=tbl(29,i)
 for pm,c in [('B0',b),('D02',d)]:
  if c:
   add(f'M-log-{pm}-{a}',M,(29,i),f'Common strict cap coefficient {c} in t^(-2) weighted or t^(-3) other units.','t>='+a,'Quarter-log CH2 minimum cells and/or spectral ray with monotone log-power conversion.',sources=weighted+density,runs=['mnew'],ass=new if pm=='D02' else base,strict='strict',
       prop=spec('Changed tail switch gives lower whole-ray maximum.',f'Fixed log onset {a}: {b} B0 versus {d} D02.') if pm=='D02' else None)
for a,c,pm,i in [('201','1e-8','B0',82),('177','1e-8','D02',83),('220','1e-9','B0',84),('192','1e-9','D02',84),('230','3e-10','B0',85),('200','3e-10','D02',85),('175','1.182e-8','D02',86)]:
 add(f'M-small-log-{pm}-{a}',M,(29,i),f'Common cap coefficient {c} in t^(-2) weighted or t^(-3) other units.','t>='+a,'Frozen left spectral cap times monotone log power.',sources=weighted+density,runs=['mnew'],ass=new if pm=='D02' else base,strict='strict',
  prop=spec('D02 exponent gives earlier same-strength ray.','Matched B0/D02 at 1e-8: 201/177; 1e-9: 220/192; 3e-10: 230/200.') if pm=='D02' else None)
add('M-logbin-join',M,(29,87,92),'Common .0503 log-power cap already on x>=9750000000.','real x>=9750000000','Last old finite bin overlaps new log 26 ray, with strict slack after product conversion.',sources=weighted,runs=['c++','anc','mnew'],strict='strict')
for i in range(124,130):
 d,s,w,p,q=tbl(29,i)
 add('M-small-bin-'+str(i),M,(29,i),f'Coefficients /10000 S:{s} W:{w} EP:{p} EQ:{q}, in t^(-2) for W and t^(-3) for others.','closed x '+d,'Eratosthenes prefix + directed trends, bin endpoints, and separate directed exponentials.',sources=ms,runs=['mfinite','c++'])
add('M-envelope-D02',M,(29,151,181),'Extend every valid signed/finite/direct B0 envelope with D02 caps (6),(7), intersect before signed product conversion when applicable.','all real x>1; each branch only on its exact domain','Cumulative intervals, no extrapolation; ordinary written envelope, not an executable oracle.',sources=weighted+density,runs=['mnew','mfinite'],ass=new,prop=spec('Add valid spectral intervals without discarding B0.','No worse anywhere; supports strict comparison of furnished branches from 169.'))
add('M-dominance-169',M,(29,183,271),'D02 .300 cap below d=min(1.03e-12,.004e^(-t/8)) (or d/t) while stated evaluated B0 signed budgets preserve the d-centered allowance.','every t>=169','Checked all furnished floor branches, shifts, signed Abel, log-power caps and exact relative conversion. Not all conceivable Dusart reoptimizations.',sources=weighted+density+[PT+' Table 1',FK+' (2.1),(3.8),(4.1),(5.2)',DS+' (3.3) Table 1, Theorems 3.3/4.2'],runs=['mnew','comp'],ass=new,strict='strict on stated model budget comparisons',
 prop=spec('Finite and B0 spectral floor comparisons on matched domains.', 'Strict improvement of supplied budgets, not a lower bound on true errors or possible B0 theorems.'))
for s in ('EP','EQ','S','W'):
 add('M-converse-'+s,M,(42,8,47),f'Eventual {s} bound of O(x^(-eta)'+(')' if s=='W' else '/log x)')+' implies no zeta zeros in Re s>b. At b=27/32 B0 plus this shape recovers exact D02.',
     '1/2<b<1, eta=1-b, eventual whole real ray','Normalize each error separately to F by logs or prime-power identities and weight transfer, then holomorphic Mellin continuation.',sources=ms+density,
     prop=spec('Converse addresses the changed spectral exponent.','A B0 proof of this shape would recover D02, not prove its independence.'))
# Auxiliary tests and superseded claims are keyed separately from mathematical main branches.
for i,a,c,k,b in [(33,'47.68','M1',2,'D02'),(49,'223','M2',3,'B0'),(49,'189','M2',3,'D02'),(49,'256','M3',4,'B0'),(49,'213','M3',4,'D02'),(49,'290','M4',5,'B0')]:
 add(f'R-aux-{a}-{b}',R,(15,i),'Implemented auxiliary G>'+c,'t>='+a,'Pure tail or connected corroborating certificate; does not displace stronger displayed rows.',sources=li+density,runs=['claims'],ass=new if b=='D02' else base,strict='strict')
hist=json.loads((T/meta[2]['packet_name']).read_text())
summary={
 R:'Supported exact open strict-positivity ray and closed nonnegative endpoint, retained original ranges, B0 local/early gains, connected D02 exact-Li and reciprocal-power profiles, explicit and arbitrary orders, and the one-sided converse.',
 M:'Supported closed finite bins down to 2 and exact empty branch, signed original/analytic envelopes with both product conversions and prime sums, matched D02 power/log ray improvements and four separate converses.'}
family={}
for f in (R,M):
 rr=[q for q in claims if q['family']==f]
 family[f]=dict(strongest_supported_portfolio=[q['claim_id'] for q in rr if q['M_status'] in (S,B) and '-aux-' not in q['claim_id'] and '-internal-' not in q['claim_id']],
      rejected_or_incomplete_claims=[],remaining_assessment_work=[],summary=summary[f])
assert len({q['claim_id'] for q in claims})==len(claims)
doc=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=idx['candidate_id'], input_stage='D02',assessment_complete=True,all_claims_inventoried=True,
 reviewed_source_hashes=dict(candidate_payloads=idx['candidate_files'],papers=src['originals'],policy=src['packet_policy_hashes']),
 source_bibliography=src['originals'],actual_effort_and_verification_commands=json.loads((P/'replay_receipts.json').read_text()),
 family_assessments=family,claims=claims,no_other_arm_or_ranking_seen=True,new_core_math_salvage_performed=False,original_candidate_bytes_changed=False,
 own_history_scope='Exact own history read for coverage; no prior status used as mathematical premise.',
 historical_registry_row_count=len(hist['claims']),
 excluded_nonclaims=['Historical unassessed checkpoint manifests and own verdicts','Failed sufficient tests clearly not submitted as final rays; see review.md and ancillary.log.',
 'Original literal early-real PT reading and literal CH2 near-one reading, never imported on the failing domains.',
 'False explanatory comment lambda>alpha in d02.py physical LF 84; proof and executable use lambda>0.'],
 formal_notice='Paper-only run; Lean, Blueprint, kernel checks and source-first PV not performed. Source/code review and ordinary exact replay recorded separately.')
(P/'review.json').write_text(json.dumps(doc,indent=2,ensure_ascii=False)+'\n')
print('Rows:',len(claims), {f:sum(q['family']==f for q in claims) for f in family})

