"""Build machine-readable inventory and lock from the assessed file-level evidence."""
from pathlib import Path
import hashlib,json,re,ast
D=Path(__file__).resolve().parent
P=Path('/task')
idx=json.loads((P/'CANDIDATE_INDEX.json').read_text())
sources=json.loads((P/'SOURCE_INDEX.json').read_text())['sources']
files={r['original_name']:r for r in idx['candidate_files']}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def lines(f): return (P/files[f]['packet_name']).read_bytes().decode().split('\n')
def loc(s):
    f,n=s.split(':')
    c=n.split('-')
    a,b=int(c[0]),int(c[-1])
    assert 0<a<=b<=len(lines(f)),s
    return dict(file=f,physical_LF=a,physical_LF_end=b,sha256=files[f]['sha256'],packet_name=files[f]['packet_name'])
def dump(name,obj): (D/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
for r in files.values():
    assert sha(P/r['packet_name'])==r['sha256']
for r in sources:
    for k in ('pdf','text'): assert sha(Path('/corpus/originals')/r[k])==r[k+'_sha256']
S='supported_at_stated_trust_tier'; B='baseline_retained'; Q='equivalent_or_weaker'
X='false_with_specific_counterexample'; I='incomplete_with_specific_missing_step'
A={
 'density': 'FKS PDF pp.4–5 Lemma 2.1/(2.1), Remark 2.2, Cor. 2.3/Table 1; pp.7–8 Cor. 2.9/(2.17), p.26 Table 8; Dusart PDF p.5 Thm 2.3; FiniteRH PDF p.2 Thm 1.',
 'perron':'FKS PDF p.8 Thm 3.2/(3.2) admissible row and Remark 3.3; OpenAIQRH PDF p.4 Thm 1.1.',
 'prime':'PT2021 PDF p.8 quoted finite π comparison; pp.7–8 (11), p.9 Lemma 6; FiniteRH PDF p.4 Cor. 1, p.5 §3.3; Dusart PDF pp.11–13 Thm 4.2, Cor. 4.5; CH2 PDF p.3 Cor. 1.3.',
 'sign':'PT2021 PDF p.3 Thm 2 and pp.9–11 §5 (integer restriction only on finite range); Dudek–Platt PDF pp.8–10 §3.1 computation/Lemma 3.4; p.2 Thm 1.2.',
 'cf':'CH2 PDF p.3 Cor. 1.2–1.3; pp.35–36 Lemma 9.2 and Cor. 9.3/(9.4); FiniteRH PDF pp.2,4 Thm 1, Cor. 1; FKS PDF p.2 Cor. 1.4.',
 'smooth':'CH2 PDF pp.40–43,46 (A.2–A.5), Cor. B.2, (B.9); FKS §2 for separated heights; Dusart pp.12–13 Prop. 4.3, Cor. 4.5.',
 'mertens':'Dusart PDF pp.17–20 Thms 5.6, 5.7, 5.9 and (5.7); PDF pp.11–12 Thm 4.2 k=2, η=.2 for finite tape tail.',
 'hi':'Dusart PDF p.5 Thms 2.3–2.4, FKS PDF pp.2,8 Cor. 1.4/Thm 3.2; CH2 PDF p.3 Cor. 1.3, Dusart Cor. 4.5.'
}
C=[]
def add(id,f,src,statement,domain,checks,code='',refs='',status=S,comp=None,gap='',strict='as stated',ass='B0; no full RH',related=(),prior=False):
    C.append(dict(claim_id=id,family=f,written_source=loc(src),
      exact_statement=statement,assumptions=ass,full_domain=domain,
      strictness=strict,real_or_integer='real and inclusive prime convention unless expressly designated integer/open in full_domain',
      baseline_comparison=comp or 'Within-method B0 and B0+D01 identical by exact implication; D02 unavailable. Preserve matched-domain comparisons in review.md.',
      source_locators=[A[k] for k in refs.split()],
      derivation_check=checks,
      numerical_obligations='See directed verification and domain analysis in review.md; an endpoint is used on a ray only with an analytic monotonicity/split proof.',
      actual_verification_receipts=[v for v in code.split('|') if v and ':' not in v],
      executable_readback=[loc(v) for v in code.split('|') if ':' in v],
      retained_valid_branches=list(related),
      M_status=status,precise_gap_or_counterexample=gap,
      propagation=dict(input_used='D01 only in the alternative tradeoff if QRH is removed, not an extra B0 premise' if id in ('Shared.reverse','R.direct','R.no-density') else 'none beyond B0',
          where_it_changes_proof='No change versus cumulative B0; for alternative no-QRH route only, substitute the mounted cap or its Mellin strip consequence.' if id in ('Shared.reverse','R.direct','R.no-density') else 'No additional assumption invocation or endpoint gain relative to B0.',
          matched_comparison='Same strength and domain under B0 and B0+D01; no available D02 result in this review.'),
      V_status='written source and executable/ordinary arithmetic where applicable; no formal Lean or source-first PV checked or claimed',
      remaining_trust='Admitted original literature including published computations as used; reviewed integer/rational arithmetic plus ordinary interpreter/compiler semantics, not independently certified originals.',
      historical_or_comparator_only=prior))
def r(*a,**kw):return add(a[0],'Ramanujan',*a[1:],**kw)
def m(*a,**kw):return add(a[0],'Mertens',*a[1:],**kw)
def j(*a,**kw):
    # One canonical row per shared theorem; both family summaries reference it.
    add(a[0],'Ramanujan',*a[1:],**kw)
    C[-1]['also_applies_to']=['Mertens']
pc='port.stdout|portDus.stdout'
mc='M.stdout|MDus.stdout'
older='secondary.stdout|ancillary_old.stdout|ancillary.stdout'
j('Shared.reciprocal','candidate.md:26-41','Conjugate-counted reciprocal sum up to cutoff < y²/6+3; off-line right half above H ≤ y²/12+1.','T*<e^y with T*>100 in the first bound; second bound uses the empty sum if cutoff≤H.','Reflection and one-sided height limits as in review §1.','analytic_check.py:29-34|'+older,'density')
j('Shared.redundancy','candidate.md:43-59','Exact D01 |ψ(x)−x|≤x^(7/8)log²x/64, actually strict, from the originals; all cumulative B0 and B0+D01 frontiers tie.','All real log x≥200.','Signed formula at e^(L/4), decreasing scaled coefficient, exact check at 200.','portfolio_check.py:127|'+pc+'|ancillary.stdout','perron density',strict='strict stronger result')
j('Shared.reverse','candidate.md:61-71','Mounted D01 alone implies no nontrivial zeta zero with β>7/8; makes no claim about β=7/8.','Re s>7/8 excluding the pole at 1.','Normally convergent Mellin integral using hypothesis exactly from 200, meromorphic continuation; compact prefix entire.',refs='perron',ass='D01 for this alternative, with standard zeta identities')
j('Shared.screen','candidate.md:73-121','W(s), running-min mass bound B(L), and |ψ(x)−x|/x ≤ exp(−L/8) C(L) with the stated weights and remainder.','Real L≥180; densities at T≥H, strict β>s, boundary β=b included in final bin.','Abel mass summation/binning; signed formula at exp(.45L); Horner expansion matches formula.','portfolio_check.py:9-43|refine.py:6-11|'+pc,'density perron')
j('Shared.ceilings','candidate.md:122-132','C decreases to w_last<.00673; bound .01361,.012902,.012329,.0105496,.0096255,.0086767,.0073709 at 180,190,200,250,300,400,1000 respectively; θ adds ≤3exp(−L/2).','Closed whole rays starting at the listed points.','All terms decreasing analytically; each specified endpoint directed-bound checked.','portfolio_check.py:119-130|'+pc,'density perron prime')
j('Shared.Dusart','candidate.md:142-145','Dusart-only density variant gives .01361 from 180 and limiting coefficient <.00673; variant 190 and 200 tests use .012904/.0123291 ceilings.','Real L≥180.','Independent from Table 8; signed FKS formula and reciprocal counts remain.','portfolio_check.py:21-29|portfolio_check.py:119-126|portDus.stdout','density perron',ass='B0 without needing FKS Table 8')
j('Shared.PS','historical_d01_candidate.md:86-107','Optional archived J+B screen <.023exp(−L/8).','Real L≥190.','FKS coarse grid and extra high-tail bound; dominated as a simple coefficient but formula remains lawful.','analytic_check.py:16-35|ancillary_old.stdout','density perron',status=Q)
j('Shared.A1','historical_d01_refined.md:12-41','Optional archived finer J*+B* screen <.021exp(−L/8), limiting coefficient <.01055.','Real L≥189.5.','Expanded density moment integral; decreasing after power scaling.','refine.py:6-26|ancillary_old.stdout','density perron',status=Q)
r('R.sign','ramanujan.md:12-18','Unique r in (N,N+1) with e r·632207037/log r=1644673232²; R(r)=0 and R(x)>0 for x>r; least integer start N+1; strict decimal bracket exactly as written.','Open real ray x>r and integer n≥38358837683; equality at r.','Quotient sieve, constant states; published integer interval lifts to reals and quantitative tail overlaps.','endpoint_check.py:7-65|secondary.stdout|ancillary.stdout','sign prime',related=('R.real-cell','R.m28.15'))
r('R.real-cell','ramanujan.md:19-22','R≥67000000(x−r) on [r,N+1]; for x≥N+1 with n=floor x≤e^58, R>e(x/L−n/log n)π(n/e).','Closed first unit subsegment, then all reals satisfying the floor condition.','Strict derivative lower bound and monotone lift with R(n)>0, including integer x.','endpoint_check.py:61-65|secondary.stdout','sign',strict='first ≥; second >')
r('R.literal-source-edge','ramanujan.md:257-268','Quoted PT2021 literal real statement R>0 throughout N<x≤e^58; rejected by candidate itself.','All purported reals N<x≤e^58.','Exact two constant prime counts, rational log and e enclosure.','endpoint_check.py:46-61|ancillary.stdout','sign',status=X,gap='At x=38358837682.1, −8100000<R(x)<−7900000; integer restriction unaffected.',related=('R.sign','R.real-cell'),prior=True)
r('R.original-rays','ramanujan.md:275-279','Original large positivity rays L≥3915 and L≥9658. Full-RH Dudek–Platt integer theorem is only separately reported.','Real inclusive large rays; full-RH separate integer comparator not assumed.','Retained originals overridden on common domains by stronger quantitative R.',refs='sign',status=B)
r('R.PV','ramanujan.md:91-112','Strict normalized PV Li bracket ell<Le^(−L)li_PV(e^L)<u; alternative remainder 2·18!/L^18+Le^(−L/2).','Real L≥27; alternative at L≥180.','Geometric moment expansion, truncated tail, two normalizations and exact coefficient sum.','analytic_check.py:37-45|portfolio_check.py:109-116|'+pc,'prime')
for id,lf,dom,formula,read,reason in [
 ('B','117-118','27≤L≤43.7','D_B=g(L)e^(−L/2)+4Le^(−L)','44-46','Quoted stronger finite π estimate and normalization'),
 ('f','119-126','27≤L≤58','D_f=(L²+2L)e^(−L/2)/(8π)+1354Le^(−L)','47-48','Finite θ integrated above 599; constant prefix includes lower endpoint and PV shift'),
 ('c','127-139','L≥27','D_c=A0+117e^(−L/2)+h_c as written','49-52','Anchored residual from 20 via exponent derivatives'),
 ('p','140-149','L≥180','D_p=C(L)e^(−L/8)+3e^(−L/2)+min(h_c,h_p), or anchored integral of the pointwise minimum','61-69','Spectral boundary, both residual choices and positive-prefix guard at 180'),
 ('direct','150-156','L≥200','D_d=(L²+8L/7)e^(−L/8)/64+3e^(−L/2)(1+1/(.49L))+7e−15(L/200)e^(200−L)','70-74','Integrate direct cap, log-square cancellation and residual guard'),
 ('osc','157-176','L≥58; spectral boundary only L≥180','h_s as written, available as residual minimum','53-69','J1 absolute-continuity integration by parts, power allowances and exact prefix factors'),
 ('optional','177-180','PT estimate for L≥2000, E_U L≥2839, E_C L≥38','PT finite-free large Li₂ comparison plus optional E_U/E_C and PV guard','75-89','Lawful additional written options; not required by numerical grid'),
 ('one-side','182-189','28≤L≤43.7','D_+≤3Le^(−L); compare only allowed minima','84-89','θ sign through entire integral to x; checker uses it through 43 only')
]:
 r('R.'+id,'ramanujan.md:'+lf,formula,dom,reason,'portfolio_check.py:'+read+'|'+pc,'prime cf perron',strict='error majorant ≤')
r('R.shaped','ramanujan.md:190-200','Strict lower shaped gap with both saved π bounds at L and L−1; upper counterpart with lower square endpoint clipped at zero.','Real L≥28.','Shifted normalization gives L/(L−1); positive upper square endpoint.','portfolio_check.py:75-102|'+pc,'prime')
r('R.old-finite-pi','historical_d01_candidate.md:118-143','Archived finite absolute normalized π bound D_f=L²e^(−L/2)/(8π) on 20≤L≤58 as allegedly from finite RH.','Archived real log domain 20≤L≤58.','Printed source π carries another log power after normalization; full RH estimate has different premises.','analytic_check.py:46-50','prime',status=I,gap='Withdrawn historical proof: missing a valid finite π estimate at asserted strength and normalization; not an inequality counterexample.',related=('R.B','R.f','R.shaped'),prior=True)
for lf,a,k in [(32,'28.15','.01'),(33,'28.35','.10'),(34,'28.65','.25'),(35,'29.15','.50'),(36,'30','.80'),(37,'30.8','1'),(38,'49','1+14/L+22/L²')]:
 r('R.m'+a,'ramanujan.md:'+str(lf),f'L^6 R(e^L)/e^(2L)>{k}.',f'Real L≥{a}.','Closed shifted cells, positive polynomial and monotone analytic tail.','portfolio_check.py:84-154|'+pc,'prime perron density',strict='>')
for lo,hi,k,lf in [(35,43.7,20,40),(49,180,30,41),(50,164,90,41)]:
 r('R.bounded'+str(k),'ramanujan.md:'+str(lf),f'Normalized gap >1+14/L+{k}/L².',f'Closed real [{lo},{hi}] in L.','Separate finite main-reserve/positive loss certificate.','portfolio_check.py:138-145|'+pc+'|portPrefix.stdout','prime',ass='B0; also certified QRH-free on the listed bounded domain')
for t,k in [(219,3),(253,4),(286,5),(320,6),(355,7),(391,8),(426,9),(467,10),(508,11),(552,12),(595,13)]:
 r('R.poly'+str(k),'ramanujan.md:'+('54' if t<=391 else '55')+'-63',f'Normalized gap strictly above Σ_(j=0..{k-1}) a_(4+j)/L^j with the stated factorial coefficients.',f'Inclusive real L≥{t}.','Positive omitted main coefficients, directed one-end comparison of scaled loss, decreasing analytic loss thereafter.','portfolio_check.py:90-102|portfolio_check.py:149-154|'+pc+'|ancillary.stdout','prime density perron',strict='>',comp='Both density choices certified. Earlier smaller k keeps smaller onset. Earlier 225/260/330/400 delayed for same respective polynomial; B0+D01 unchanged.')
r('R.no-density','ramanujan.md:46-47','Normalized gap >1+3/L without any density table or density estimate.','Real L≥50.','CH2 until 275, both shifted arguments use direct input-form at and after 275.','portfolio_check.py:155-158|'+pc,'prime perron',ass='B0 without density estimates (or D01 in place of QRH for this direct branch)',strict='>')
r('R.stability','ramanujan.md:65-68','exπ((x/e)(1−(1+12/L)/L⁴))/L−π(x)²>.19x²/L⁷.','Real L≥58.','Both perturbed arguments checked; log integral and two π residuals subtract from +22 shape.','portfolio_check.py:159-166|'+pc,'prime perron density',strict='>')
r('R.old-margins','historical_d01_refined.md:59-109','Older +4.25/L² profile, four polynomial onsets 225/260/330/400 and .10 shrink reserve; also old original +12/L from 58.','First and last and stability from L=58; four archived whole-ray starts as written.','All follow as inequalities from strictly stronger current branches, not the disused historical finite π proof.','portfolio_check.py:142-166|'+pc,'prime perron density',status=Q,related=('R.m49','R.stability','R.poly3','R.poly4','R.poly5','R.poly6'))
r('R.U-prefix','ramanujan.md:283-286','All quoted low margins through L=180 also proven without QRH.','Intersection of each listed log range with L≤180.','Prefix flag omits h_s and the spectral choices; common finite estimates only.','portfolio_check.py:75-82|portfolio_check.py:131-148|portPrefix.stdout','prime',ass='B0 without QRH; no D01')
r('R.U-60','historical_d02_candidate.md:182-186','QRH-free normalized gap >1+14/L+60/L² on bounded interval (not archived stronger-input full ray).','Real 50≤L≤169.','Original E_C/E_RH positive polynomial interval replay with no A branch.','ray_check.py:129-135|ancillary.stdout','prime',ass='B0 without QRH; no D01')
r('R.U-signed','historical_d02_extensions.md:25-38','QRH-free finite small normalized margin >.1.','Real 37.5≤L≤39.45.','Use finite θ and sign for residual; dominated by the stronger current QRH-free low margin.','extra_check.py:55-67|secondary.stdout','prime',status=Q,ass='B0 without QRH; no D01')
r('R.U-theta','historical_d02_extensions.md:40-88','|θ(e^v)/e^v−1|≤.321/v⁴.','Real v≥2834.','Plateau verified by decreasing joint height weight, upper rectangles, analytic suffix.','extra_check.py:6-35|secondary.stdout','hi',ass='B0 without QRH; no D01')
r('R.U-E','historical_d02_extensions.md:90-101','E_U centered Li₂ normalized upper count bound as written; E_C alternative from CH2.','E_U real L≥2839; E_C L≥38.','Split at L/2; bound boundary and residual and normalize.','extra_check.py:36-46|ray_check.py:103-117|secondary.stdout','hi prime',ass='B0 without QRH; no D01')
r('R.U-hi','ramanujan.md:287-302','Normalized real gap >.03 for L≥2840.','Real inclusive L≥2840.','L and L−1 in E_U domain; one-end .322 loss and polynomial excess, with monotone tail.','extra_check.py:36-47|secondary.stdout','hi prime',ass='B0 without QRH; no D01',comp='Strict strengthening and earlier onset vs L≥3915 at same QRH-free trust; not an input gain.')
r('R.U-mid','ramanujan.md:287-296','Normalized gap >.004 for 169≤L≤753.','Closed real L interval.','Shifted E_C and finite cells (width .5).','extra_check.py:48-53|secondary.stdout','prime',ass='B0 without QRH; no D01')
r('R.U-connected','ramanujan.md:303-306','QRH-free R>0 on (r,e^753]∪[e^2840,∞).','Real two pieces, left endpoint r excluded.','Paper-backed finite handoff, QRH-free prefix then both independently verified unconditional intervals. No missing claim in (753,2840) in weaker premise set.','portPrefix.stdout|secondary.stdout','prime sign hi',ass='B0 without QRH; no D01')

m('M.def','mertens_current.md:3-16','Exact M,B3 definitions and natural-log centered errors; for deltaQ in [l,u], normalized Q,P in [e^l,e^u],[e^(−u),e^(−l)]; max absolute relative error=e^|deltaQ|−1.','Products and sums at x≥2, inclusive prime state.','Dusart constants and reciprocal conversion.','mertens_check.py:91-109|Msieve.stdout','mertens')
for id,lf,text,dom in [
 ('raw','142-144','CH2 A0+113.67u; FiniteRH L²u/(8π); FKS 9.22022L^(3/2)e^(−.8476836√L) on actual source ranges','CH2 x≥1; FiniteRH 59<x≤2.169e25; FKS x>2'),
 ('computed','145-149','Negative/positive ψ errors .751u,.791u','10^4≤x≤10^13'),
 ('inverse','150-163','Signed ψ error sides ((g(L)−m)u+(7L+2)e^(−L), a u+b v)','18.42≤L≤43.7'),
 ('optimized-height','164-175','CH2 Cor.9.3 improved log curve and general T envelope π/(T−1)+(π/T)²/3+(q²−q/3)u/(2π)','34≤L≤59.5 for 9.3; Cor.1.2 when 10^7≤T≤3000175332800 and x>max(T,10^9)'),
 ('spectral','176-179','Use current sampled-certified but globally monotone screen C(L)e^(−L/8); optionally old PS/A1 minima.','Current L≥180 and older at their declared domains')
]:
 m('M.psi-'+id,'mertens_current.md:'+lf,text,dom,'Exact domains/signs and factors read back in review §3; no extrapolation of a local curve.','mertens_new.py:6-23|mertens_new.py:76-89|'+mc,'cf prime perron density',strict='upper estimates ≤')
m('M.PrimePowers','mertens_current.md:131-136','m e^(−L/2)≤(ψ−θ)/x≤a e^(−L/2)+b e^(−2L/3), m=.9999, a=1.000000147, b=1.78.','x≥121.','Combines exact original lower and upper bounds.','mertens_new.py:6-6','smooth')
m('M.J1','mertens_current.md:183-207','Smoothed J1(L)=∫_L^∞ eψ(t)dt equals zero series with 1/[ρ(ρ−1)], minus log(2π)e^−L, plus trivial-zero series precisely as written.','L>0 (quantitative branch uses L≥18.42).','Integrated Perron kernel and contour shift with absolute zero weights; convergence also QRH-free.',refs='smooth')
m('M.J2','mertens_current.md:209-252','Bounds j,j2; further primitive J2′=−J1. Twice-smoothed weighted-tail bound K j+2|K′|j2; sharpened off-line k(L) via B(L)/H, or constant 7e−12 off-line without QRH.','Quantitative portfolio L≥18.42, sharpened k for L≥180.','CH2 logarithmic derivative weight identity; inverse squares, integration by parts twice and vanishing limits.','refine.py:73-77|mertens_new.py:25-32|mertens_new.py:55-64|ancillary.stdout|'+mc,'smooth density perron')
m('M.Abels','mertens_current.md:256-274','Exact Abel identities for U1−L+γ and U0−log L−γ; add D1,D0,DQ as written; 0≤τ≤1/(2floor x)≤e^−L.','Real x≥2; tail over strict powers/prime states >x.','Constants fixed by Dusart plus convergent omitted power tails; endpoint convention correct.',refs='mertens smooth')
m('M.signed','mertens_current.md:275-297','Signed product and sum intervals from the recorded D1,D0,DQ endpoints and the observed or bounded ψ boundary and smoothed residual. Optional CH2 U1 bound and Abel transfer.','Real L≥18.42 for displayed signed numerical envelopes.','Square and cube power integrals with positive residual; log conversion exact. Code uses a deliberately weaker one-sided loss for its uniform tests.','mertens_new.py:25-37|'+mc,'cf smooth mertens')
m('M.theta-min','mertens_current.md:384-414','Exact θ signed transfers for δV,δS,δQ; direct θ and smoothed ψ pointwise minima, and archived d_U option including signs on available domain.','All identities x≥2; d_U x≥10^8; sign savings only on original finite domains.','Abel and fixed constants, including small x sign only over finite part of tail.','ray_check.py:147-203|secondary.stdout','prime cf mertens')
m('M.little-o','mertens_current.md:416-434','Any indicated little-o improvement forces ψ−x=o(x^(7/8)) and excludes β=7/8; strict power improvement with fixed log loss reduces the strip.','As x→∞; bounded regions harmless.','Reverse Abel on U1/U0, conversion of relative errors to log at zero, compact prefix drops from ε test. Does not assert existence of boundary zeros.',refs='perron mertens')
m('M.limit','mertens_current.md:56-62','Limsup of errors scaled by Lx^(1/8), or x^(1/8) for δV, at most .00673; earlier .0211 branch dominated.','As x→∞ for limsup, full original branch domain for comparison.','Boundary coefficient w_last and primed residual add at most factor 1+1/H.','portfolio_check.py:126-126|mertens_new.py:55-64|ancillary.stdout','density perron smooth')
for lf,start,coef,free in [
 (27,'10^8','.0671',1),(28,'5·10^7','.061',1),(29,'e^23.7 (thus also 2·10^10)','.0077',1),
 (30,'e^26','.0029',1),(31,'e^28','.00124',1),(32,'e^29.9','.00061',1),
 (33,'e^43.7','.00021',1),(34,'e^43.7','.000042',0),(35,'e^47','.000012',0),(36,'e^59.5','2·10^−7',0)]:
 m('M.poly'+str(lf),'mertens_current.md:'+str(lf),
   f'Both absolute relative products and |δS| <{coef}/L³; |δV| <{coef}/L².',
   f'Inclusive real x≥{start}.','Closed log-cell proof and analytic handoffs; finite tapes also used on first .061 prefix.',
   'mertens_new.py:25-54|mertens_new.py:66-103|mertens_new.py:127-133|audit_summaries.py:27-36|'+mc+'|audit.stdout|secondary.stdout',
   'cf smooth mertens prime',ass='B0 without QRH, no D01' if free else 'B0 including QRH',strict='>')
 C[-1]['strictness']='strict upper bounds (<)'
for lf,start,coef in [(38,'x=300000','.0149'),(40,'x=500000','.013163'),(46,'L=190','.012903'),(47,'L=200','.01233'),(48,'L=250','.01055'),(49,'L=300','.009626'),(50,'L=400','.008677'),(51,'L=1000','.007371'),(54,'x=500000','.013166 (Dusart-only)'),(54,'L=190','.012905 (Dusart-only)')]:
 m('M.power'+str(lf)+('-190' if lf==54 and start=='L=190' else ''),'mertens_current.md:'+str(lf),
   f'Power envelope coefficient {coef}: first three bounds c x^(−1/8)/L, weighted bound c x^(−1/8).',
   f'Inclusive real ray starting {start}.','Finite bands, CH2 bridge and monotone spectral continuation or later variant spectral ray.',
   'mertens_new.py:55-64|mertens_new.py:104-126|portfolio_check.py:119-126|'+mc,
   'cf perron density smooth',strict='strict upper bounds (<)',comp='Compare both shapes pointwise on matched domains; strictly beats the older .0211 power coefficient on its ray; D01 adds nothing.')
for i,(fx,lf,c,start) in enumerate([
 ('P,Q',94,'.199972897',2278382),('S',95,'.199928568',2278383),('V',95,'.299999703',912560),
 ('P,Q',102,'.2',2278382),('S',103,'.2',2278383),('V',103,'.3',912560)
]):
 m(('M.matched' if i<3 else 'M.original')+str(i%3),'mertens_current.md:'+str(lf)+'-'+str(99 if i<3 else 104),
   f'{fx} coefficient {c} in its stated L scale.',f'Real x≥{start}.',
   'Matched-domain band maximum then analytic join; valid stronger Python V bound separately retained.' if i<3 else 'Dusart original symmetric comparator, used only on its domain.',
   'audit_summaries.py:30-36|finite20b.stdout|audit.stdout' if i<3 else '',
   'mertens cf',status=S if i<3 else B,strict='non-strict absolute upper bound')
for i,(c,d,a) in enumerate([('.01','P,Q,S',10099524684),('.01','V',10148219812),('.02','all four',1133202783),('.07','V',40890944),('.09','P,Q,S',18337513)]):
 m('M.onsetExample'+str(i),'mertens_current.md:81-88',f'{c} coefficient in correct scale for {d}.',f'Real x≥{a}.','Last-failed-cell rule and strict join, not a sharp onset claim.',
   'finite20b.stdout|finite100m.stdout|audit.stdout','mertens cf',strict='strict upper bound')
for name,lf,b in [
 ('products','108-112','2278381.711141839 < x* < 2278381.711141843'),
 ('reciprocal-sum','113-118','2278382.1129 < x* < 2278382.1130'),
 ('weighted','113-118','912559.9973 < x* < 912559.9974')
]:
 m('M.sharp-'+name,'mertens_current.md:'+lf,
   f'Earliest inclusive real onset for original non-strict {name} bound is fixed-prime-state root; {b}.',
   'Closed real ray starting at root; first qualifying integer unchanged.',
   'Right endpoint composite, increasing L, strictly decreasing scaled positive error, signs in directed bracket, original tails beyond unit.',
   'mertens_check.py:167-231|Msieve.stdout','mertens',strict='non-strict envelope with equality at root')
m('M.withdrawn299999','mertens_current.md:126-127','Historical trial |δV|≤.299999/L² from 912560 is false.','Purported real x≥912560.','Exact ψ-independent constant interval and prime state.','mertens_check.py:228-231|Msieve.stdout|ancillary.stdout','mertens',status=X,gap='At x=912560 scaled signed error is strictly in (.2999993,.2999995).',related=('M.matched2','M.old-sharper'),prior=True)
m('M.old-sharper','historical_d02_mertens.md:19-30','Old .199999 products and reciprocal sum; .2999995 weighted, on the original individual domains.','Real x≥2278382,2278383,912560 respectively.','Exact narrower constants and fixed-state monotone tests; V branch stronger than both rounded C++ variants.',
   'mertens_check.py:118-165|mertens_check.py:253-284|Msieve.stdout','mertens cf',strict='non-strict')
m('M.old-analytic','historical_d02_mertens.md:68-133','Archived QRH-free signed d_U (integral form) and strict .125 products/S, .135 V for x≥10^8.','Real x≥10^8.','Tail starts at correct log-domain; signs to 39 in archived proof, and positive exponential estimates on cells.',
   'ray_check.py:145-203|secondary.stdout','hi cf prime mertens',ass='B0 minus QRH, no A',status=S)
m('M.old-PS','historical_d01_candidate.md:49-76','Earlier M1 asymmetric smoothing and strict .170/L³ on L≥22 and .235/L² on L≥21 as written.','Real L≥21 for M1; respective ray for each coefficient.','Lawful finite ψ source, single integration by parts, old screened tail. New constant rows generally stronger.', 'analytic_check.py:103-128|ancillary_old.stdout','cf smooth mertens')
m('M.old-refined','historical_d01_refined.md:124-218','Optional old refined smoothing and asymmetric transfer; .044 at L≥26; .0211 product, .02101 prime-sum scaled branches from 189.5.','Real L≥21 formulas; indicated subrays for constants.','One integration plus sharper critical-line weight; Abel via U1 alternative remains valid. Numerical old ψ branches use the stated finite ψ (not historical incorrect π).',
   'refine.py:73-105|ancillary_old.stdout','cf smooth mertens density')
m('M.finite26-examples','finite.md:18-37','.199972897/.199928568/.299999705 full original rays; .1 from 30m, .044 from 500m, enlarged x≥300000 .453 first three/.488 weighted, .19 products/S from 3451809.','Individual inclusive real rays listed.','Matched band maxima and last failed endpoint rule plus analytic tail. Stronger present-day branches retained.',
   'finite_opt.cpp:194-233|finite26.stdout|M.stdout','mertens cf')
m('M.finite24-examples','finite.md:61-80','Old .088 on L≥24; old full-domain .199980 and .199929; .145 products/S and .155 weighted from 6000000; .453/.488 from 300000.','Inclusive real rays as stated.','Archived optimized executable and analytic handoff. Earlier source version does not reproduce the finer tape; exact later own source does.',
   'D01__SUBMITTED_007.cpp:101-222|exact24.stdout|ancillary_old.stdout','mertens cf')
m('M.finite-mechanism','finite.md:82-145','Whole-real-block integer sieve/envelope, logarithm and constant enclosures (old closed bands and new half-open bands distinguished).','Finite certificates exactly on their proven intervals.','Sieve invariant and log/power/weighted tails checked independently of equality of transcripts.',
   'finite_opt.cpp:13-233|D01__SUBMITTED_007.cpp:13-222|exact24.stdout|finite26.stdout|finite100m.stdout|finite20b.stdout','mertens')
m('M.Python-mechanism','historical_d02_mertens.md:135-199','Old closed-cell and exact-state refinement proof, harmonic γ and partial-summation tail constants.','10000≤x≤10^8; constants use θ on t≥10^8.','Atanh interval plus step-monotonicity; constants from independent θ comparison, actual exact sieve verified.',
   'mertens_check.py:22-284|Msieve.stdout|secondary.stdout','mertens cf')
for tape,trans,read,n,join in [
 ('finite100m.txt','finite100m.stdout','finite_opt.cpp:194-233',100000000,7),
 ('finite20b.txt','finite20b.stdout','finite_opt.cpp:194-233',20000000000,1),
 ('finite26.txt','finite26.stdout','finite_opt.cpp:194-233',195729609429,1),
 ('D01__SUBMITTED_008.txt','exact24.stdout','D01__SUBMITTED_007.cpp:189-222',26489122130,9)
]:
 old=tape.startswith('D01')
 for lf,line in enumerate(lines(tape),1):
    z=re.fullmatch(r'\[(\d+),(\d+)\] : (\d+) (\d+) (\d+)',line)
    if z:
        a,b,*c=map(int,z.groups())
        domain=f'[{a},{b}'+(']' if b==n or old else ')')
        m(f'M.band.{tape}.{lf}',f'{tape}:{lf}',f'Scaled ceilings {c} in units '+('10^−6' if old else '10^−9')+' for both products, S, V respectively.',
          f'Real x∈{domain}.','Entire cells supported by monotone-prefix enclosure and scaled maximum, not interpolation.',read+'|'+trans,'mertens',strict='≤ for each')
    z=re.fullmatch(r'(\d+) : (\d+) (\d+) (\d+)',line)
    if z:
        k,*e=map(int,z.groups())
        for col,v in zip(('P,Q','S','V'),e):
            start=v or 300000
            cross=tape=='finite100m.txt' and k==6 and col in ('P,Q','S')
            whole=(k>=join or cross) and start<n
            m(f'M.threshold.{tape}.{k}.{col}',f'{tape}:{lf}',
              f'{col}: last failed cell end {v}, threshold {k}/100 in the relevant scale'+('; yields an inclusive full-ray bound with the analytic join.' if whole else '; diagnostic only as a candidate whole-ray onset from this tape.'),
              f'Real x≥{start}'+(' throughout the ray.' if whole else f' only through {n} if start is below the terminal endpoint; no whole-ray assertion from this row alone.'),
              ('Cross-tape join: the medium tape already succeeds in this column at 10^8 and joins .0077.' if cross else 'Conservative last failed endpoint. Independent analytic join applied only on certified threshold rows.'),
              read+'|'+trans+'|M.stdout'+('|finite20b.stdout' if cross else ''),'mertens cf',status=S if whole else Q,strict='strict on covered successful cells; diagnostic is not an error violation')
for lf,i in [(7,0),(8,1),(9,2)]:
 for coef,start in ast.literal_eval(lines('mertens_results.txt')[lf-1][2:]):
    m(f'M.Python-row.{i}.{coef}',f'mertens_results.txt:{lf}',f'Column {i} normalized error ≤{coef}/10^6.',f'Real x≥{start}.',
      'Closed cells and exact-state fallback, then QRH-free tail from 10^8.','mertens_check.py:118-165|Msieve.stdout|M.stdout','mertens cf',strict='≤')
m('M.secondary-theta','secondary.md:7-11','|θ(e^L)e^−L−1|<.01317e^−L/8, including Dusart-only.','Real L≥180.','CH2 to 186.03 then spectral; both endpoints and tail checked.',
  'secondary_check.py:9-13|secondary.stdout|'+mc,'cf smooth density perron')
m('M.secondary-interval','secondary.md:12-20','π(x+.02635x^(7/8))−π(x)>.0000099 x^(7/8)/log(x+.02635x^(7/8)).','Real x≥e^180.','Concave endpoint estimate, strict theta reserve, divide by maximum prime weight.',
  'secondary_check.py:19-20|secondary.stdout','cf smooth density')
m('M.secondary-A5','secondary.md:21-27','Retained historical A5: at g=x^(5/8)(log x)^14, π(x+g)−π(x)>.6g/log(x+g).','Real x≥e^100000.','Common-zero cancellation, bin counts and absolute high-strip tails. Detail in historical_d01_refined.md LF264–344, no Dusart-only claim here.',
  'refine.py:107-122|secondary.stdout','perron density smooth')
m('M.secondary-max','secondary.md:29-54','Normalized maximum n/φ(n) for integers 1≤n≤N differs from loglog N by <.02635(log N)^−1/8; σ/n bounded above by same max majorant.','Real loglog N≥181, optimizing over integers n.','Primorial cardinality and endpoint θ and Q, shift logarithm bounded strictly.',
  'secondary_check.py:14-19|secondary.stdout|'+mc,'mertens cf smooth')
m('M.secondary-fixed','secondary.md:56-79','Fixed primorial log error bounded by J_K+(2a u+1.5b v)/L+τ+2w²/L, giving limsup ≤.00673/H<2.25e−15 on Lx^(1/8) relative scale.','Real L≥180; limsup at infinity.','Exact subtraction cancels boundary w/L, leaving squared error; integrate prime powers, apply exponentiation.',
  'mertens_new.py:55-64|ancillary.stdout|'+mc,'mertens smooth density')
for id,src,description,dom,relation in [
 ('prior-A4','historical_d01_refined.md:222-253','Earlier extremal error .0424 from loglog N=190, with σ/n corollary.','Real loglog N≥190.','M.secondary-max'),
 ('prior-short','historical_d01_refined.md:255-262','Earlier length .0421 x^(7/8), reserve .00007 x^(7/8)/log y.','Real L≥190.','M.secondary-interval')
]:
 m('M.'+id,src,description,dom,'Archived theta/product envelopes and tangent inequalities; valid at B0 strip. Shorter length and a different reserve retain meaningful distinction.', 'refine.py:91-104|ancillary_old.stdout','mertens density smooth',related=(relation,))

# Bind actual command receipts to immutable stdout/stderr. Historical comparison
# failure is not silently normalized; the right corresponding source is used.
transcript_pairs={
 'finite100m':'finite100m.txt','finite20b':'finite20b.txt','finite26':'finite26.txt',
 'finite24':'D01__SUBMITTED_008.txt','exact24':'D01__SUBMITTED_008.txt',
 'port':'ram_replay.txt','portDus':'ram_dusart_replay.txt','portPrefix':'prefix_replay.txt',
 'M':'mertens_replay.txt','MDus':'mertens_dusart_replay.txt','Msieve':'mertens_results.txt','audit':'summary_replay.txt'}
receipts={}
for name in ('python_runs.txt','finite_runs.txt','older_runs.txt','exact24_runs.txt','finite24_run.txt'):
    for s in (D/name).read_text().splitlines():
        a,rc=s.rsplit(' ',1); a=ast.literal_eval(a);rc=int(rc)
        if name=='python_runs.txt':
            label={'portfolio_check.py':'port','mertens_new.py':'M','audit_summaries.py':'audit',
                   'mertens_check.py':'Msieve','secondary_check.py':'secondary'}[a[2]]
            if a[-1]=='--dusart-only':label+='Dus'
            if a[-1]=='--qrh-free-prefix':label+='Prefix'
        elif name=='finite_runs.txt':
            label='compile' if a[0]=='/usr/bin/g++' else {'100000000':'finite100m','20000000000':'finite20b'}[a[1]]
        elif name=='older_runs.txt':
            label='older24_compile' if a[0]=='/usr/bin/g++' else 'older24' if len(a)==1 else 'ancillary_old' if a[2]=='-c' else 'older_count'
        elif name=='exact24_runs.txt':label='exact24_compile' if len(a)>1 else 'exact24'
        else:label='finite24'
        receipts[label]=dict(argv=a,exit=rc)
receipts['finite26']=dict(argv=['/work/finite019'],exit=0,receipt='finite26_status.txt')
receipts['ancillary']=dict(argv=['/usr/bin/python3.10','-B','/work/submission/ancillary_verify.py'],exit=int((D/'ancillary.status').read_text()),env='PYTHONPATH=/work/exact019')
for name,rec in receipts.items():
    rec['cwd']='/work/exact019'
    for kind in ('stdout','stderr'):
        path=D/(name+'.'+kind)
        rec[kind]=dict(file=path.name,sha256=sha(path),bytes=path.stat().st_size)
    if name in transcript_pairs:
        f=files[transcript_pairs[name]]
        rec['candidate_match']=dict(file=f['original_name'],sha256=f['sha256'],byte_equal=f['sha256']==rec['stdout']['sha256'])
assert all(rec['exit']==0 for rec in receipts.values())
assert all(rec['candidate_match']['byte_equal'] for n,rec in receipts.items() if n in transcript_pairs and n!='finite24')
assert not receipts['finite24']['candidate_match']['byte_equal']
dump('evidence.json',dict(replay='replay_review.py',compiler='g++ Ubuntu 11.4.0-1ubuntu1~22.04.3; GNU __int128 extension; asserts enabled',interpreter='/usr/bin/python3.10',originals=sources,command_receipts=receipts,
    exact_hashes_for_inputs={x:sha(P/x) for x in ('INPUT_CONTRACT.json','CANDIDATE_INDEX.json','RUNTIME_PATHS.json','OWN_HISTORY_DISCLOSURE.json','SOURCE_INDEX.json','REVIEW_SCHEMA.md','OPERATING_NOTICES.md')},
    initial_command='pwd; ls -l /task/INPUT_CONTRACT.json /task/RUNTIME_PATHS.json /task/CANDIDATE_INDEX.json: cwd confirmed, exit 127 due to missing ls, shell locale warning; Python pathlib confirmation followed.',
    recovery='Older finite24 initial replay of coarser D01__SUBMITTED_005.cpp (smaller default, then explicit N) did not match. Exact D01__SUBMITTED_007.cpp reproduces the supplied fine 24 tape. Both trials preserved.'))
families={}
for name,msg in [('Ramanujan','Sharp real/open and integer/inclusive onset at original literature trust, improved quantitative whole rays and QRH-free pieces; no incremental D01 gain.'),('Mertens','All four quantities: signed and relative-product envelopes, finite and analytic whole rays, sharp original benchmark real onsets; no incremental D01 gain.')]:
    subset=[c for c in C if c['family']==name]
    families[name]=dict(common_dependency_claim_ids=[c['claim_id'] for c in C if c.get('also_applies_to') and (c['family']==name or name in c['also_applies_to'])],
      strongest_supported_portfolio=[c['claim_id'] for c in subset if c['M_status']==S],
      rejected_or_incomplete_claims=[c['claim_id'] for c in subset if c['M_status'] in (X,I)],
      retained_baselines_or_weaker=[c['claim_id'] for c in subset if c['M_status'] in (Q,B)],
      remaining_assessment_work=[],summary=msg)
dump('review.json',dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=idx['candidate_id'],
  assessment_complete=True,all_claims_inventoried=True,reviewed_source_hashes={**{k:v['sha256'] for k,v in files.items()},**{r[k]:r[k+'_sha256'] for r in sources for k in ('pdf','text')}},
  source_bibliography=sources,actual_effort_and_verification_commands=receipts,
  family_assessments=families,claims=C,no_other_arm_or_ranking_seen=True,new_core_math_salvage_performed=False,original_candidate_bytes_changed=False,
  own_history_disclosure='Not blind to disclosed exact own history. Earlier statuses are never premises; archived D02 stronger-input statements and withdrawn early attempts are not current claims.',
  excluded_historical_premise_branches=[loc('restart.md:3-14'),loc('historical_d02_candidate.md:51-123'),loc('historical_d02_candidate.md:240-251'),loc('historical_d02_extensions.md:112-227')],
  scope='No independent check of the source-published zero or large prime-count computations; no Lean/formal/source-first PV.',
  propagation_assessment='B0 implies exactly the hypothetical real-ray D01 assumption. Hence deleting D01 preserves every supported bound, onset and tradeoff. B0 comparison is within-method; no B0+D02 premise is available.'))
dump('STAGE_STATUS.json',dict(ready_for_review=True,families={k:dict(status=S,claim_files=['review.md','review.json']) for k in families},serious_attempts_documented=True))
(D/'LOCK.json').write_text(json.dumps({'files':[dict(path=p.name,sha256=sha(p)) for p in sorted(D.iterdir()) if p.name!='LOCK.json' and p.is_file() and not p.is_symlink()]},separators=(',',':'))+'\n')
