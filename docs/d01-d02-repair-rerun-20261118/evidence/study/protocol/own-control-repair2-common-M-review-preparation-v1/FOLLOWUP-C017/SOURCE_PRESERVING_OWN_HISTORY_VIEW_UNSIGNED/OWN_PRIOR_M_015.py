"""Build exact physical-LF inventory from packet bytes and independent assessment."""
import json, re, hashlib, sys, zipfile
from pathlib import Path
S=Path(__file__).resolve().parent
C=Path(sys.argv[1] if len(sys.argv)>1 else '/work/c017')
def read(p): return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,obj,pretty=False):
    (S/name).write_text(json.dumps(obj,ensure_ascii=False,indent=2 if pretty else None)+'\n')
idx=read(Path('/task/CANDIDATE_INDEX.json'))
D={a['original_name']:a for a in idx['candidate_files']}
assert all(sha(C/n)==a['sha256'] for n,a in D.items())
source=read(Path('/task/SOURCE_INDEX.json'))
z=zipfile.ZipFile(C/'prior_candidate.zip')
old=read(C/'prior_review_inventory.json')['claims']
V='No formal Lean/Blueprint or PV checked; written proof and ordinary interval/integer arithmetic only.'
OK='supported_at_stated_trust_tier'
BASE='baseline_retained'
WEAK='equivalent_or_weaker'
FALSE='false_with_specific_counterexample'
OPEN='incomplete_with_specific_missing_step'
T='Named original literature at its exact hypotheses, written derivation and replayed Decimal/finite-integer checks as applicable.'
D02='B0 plus exact PsiMajorant: |psi(x)-x| <= x^(27/32)(log x)^2/64 for every real x>=exp(200).'
B0='B0 (seven named originals at source trust), also valid under D02.'
rnotes={
'C-cap':'Shared proof; continue the Euler-log-derivative integral, with local normal convergence only in the open half-plane beyond the cap. Preserve QRH and checked finite height. See review.md Shared spectral input.',
'C-density':'Shared proof; double the positive-side count, integrate its upper estimate against -w prime, distinguish full positive weight, and verify low constants from named table and square tail. See review.md Shared spectral input.',
'C-layer':'Shared proof; reflection and conjugation with multiplicity; extra right-layer count charged at the left endpoint. Nonnegative collected coefficients. See review.md Shared spectral input.',
'C-smoothing':'Shared proof; integrated classical midpoint explicit formula and squeeze using monotonicity for right-hand values. Raw hypothesis used directly only at u>=200. See review.md Shared spectral input.',
'C-cont':'Shared proof; log derivative in s at most 97 yields geometric integration and exp-normalized monotonicity; scaled at both shifted arguments when used. See review.md Shared spectral input.',
'C-primitive':'Shared proof; a second frequency denominator from integration and an absolute square-weight majorant. See review.md Shared spectral input.',
'C-original':'Shared branches, verified transcription against original tables and formulas, with exact gates. At 1000 the conditional FKS recipe need not be extended to its closed boundary: the selected B0 spectral cap estimates imply those printed bounds anyway.',
'R-J':'J minus V by Stieltjes summation and one more frequency denominator; subtract the lower square mass .988 or add the upper T on the appropriate side.',
'R-Buethe':'Finite original quote and PV normalization allowance; use at both shifted and unshifted logs only in its own domain.',
'R-theta':'PT lemma and theta integral below/above 600; the 1255 constant includes the early contribution.',
'R-signed':'Only the unconditional sign quote (DP p.8), not the accompanying other-side RH estimate; V differs by <2.',
'R-PTpi':'Normalize the original PT estimate by v/x without changing its log cutoff.',
'R-point':'Take independent minima then the positive upper square bracket; log x/e evaluated at L-1.',
'R-anchor':'Derivative remainder and positive anchor residuals at 24,32,50; allowance factors and V series tail checked.',
'R-poly':'Use the shifted series coefficients, keep negative interior terms, discard only the positive omitted tail. Strict on eligible logs; optional N=30 can use L>=51.',
'R-asym':'For any fixed desired order use a larger fixed truncation and the exponentially small pi half-width; not convergence of a factorial series.',
'R-int':'Inherited restricted integer outcome: the DP p.8 concrete last integer plus Lemma 3.4 as reported. Not a fresh historical computation or acceptance of the real stepping lemma.',
'R-original-real-refuted':'Verified constant prime counts and interval sign. This is a refutation of the printed PT real statement, not a false candidate theorem.',
'R-local-root':'Exact distinct-floor count and right-hand conventions; R strictly increases on [n,n+1]; numerical sign enclosure at both endpoints of the root bracket.',
'R-connected':'Integer bridge at literature trust plus real interpolation by monotone positive factor and shifted count; strict local root and closed analytic tail.',
'R-tail-original':'Keep the original strict tails at their stated source trust, independently subsumed by the new ray. RH-only extension is excluded.',
'R-envelope-gain':'Selected pointwise analytic profile; shorter D02 cap cannot raise any retained width, and strict upper-side gain passes the branch-specific B0 floor. Does not claim other B0 proofs impossible.',
'M-norm':'Exact relative product normalization and the two prime-sum constants, with both reciprocity and signs as in the named originals.',
'M-M1':'Stieltjes normalizations, cancellation of zero denominators for weighted tail, absolute square-frequency convergence, signed endpoint gates.',
'M-general-sigma':'Use CH2 9.1 within its original rectangle, integrate centered tail, add center shift only to minus side of Z0, and bound sigma>=100 analytically.',
'M-direct-D02':'Correct direct partial summation but dominated by the inferred cap; retained as a within-input comparison only.',
'M-powers':'Stieltjes endpoint/interior with opposite signs and alternating integral bounds, open prime-power cutoffs, valid monotone normalized coefficient.',
'M-M2':'Exact prime-power corrections and two monotone exponential images of signed log interval, not treating logarithmic error as relative error.',
'M-envelope':'Componentwise minimum, exact finite pointwise prefix (within sieve domain), empty prime list below 2, switch finite estimates off at their own cutoffs.',
'M-theta':'Integrate the eligible theta bounds with opposite signs; subtract T0 only for the product then exponentiate.',
'M-pi-general':'Stieltjes subtraction yields the signed endpoint plus derivative tail and continuous main correction in log Q; exact reference V and vanishing limits.',
'M-pi-simple':'Explicit finite Büthe width through B plus separate CH2/spectral tail; coded reciprocal and weighted transfers with correct log conversion.',
'M-power-limit':'Nonincreasing normalized pointwise power coefficient and allowance; limits are upper coefficients of the estimating method.',
'M-power-167-join':'Same h=5e-13 at both endpoints with convexity; uniform allowances and correct product conversion are <.276000000008.',
'M-separation':'Use monotone matched ratio and common estimating-formula barriers; full domain, not samples and not an obstruction to all B0 proofs.',
'M-three-pieces':'Each finite-to-tail log join uses its own estimate and whole-interval derivative or endpoint-factor bound. The ancillary check supplies the full medium-range product exponent denominator.',
'M-cheap-join':'Use U0 upper in place of U1/u and differentiate the positive exponential-polynomial factors; joined at 25 million.',
'M-finite-sieve':'Exact finite normalizers via corrected trapezoids and source theta tails. Check both sides of prime events with derivative guards and real x on the entire slabs.',
'M-finite-only':'Historical scope of first fine sweep only; the current extension supplies the later whole-ray joins.'
}
def L(file,line,end=None,archive=False):
    obj={'file':file,'physical_LF':line,'sha256':D[file]['sha256']}
    if end is not None:obj['end_physical_LF']=end
    return obj
def loc_read(l):
    for i in range(l['physical_LF']-1, len((C/l['file']).read_bytes().split(b'\n'))):
        return (C/l['file']).read_bytes().split(b'\n')[i].decode()
    raise ValueError(l)
ARCH={'ramanujan.md':'OWN_ORIGINAL_021.md','finite.md':'OWN_ORIGINAL_010.md'}
def migrate(a,arch=False):
    n=a['file']; x=a['physical_LF']; y=a.get('end_physical_LF')
    if arch and n in ARCH:
        assert z.read(n)==(C/ARCH[n]).read_bytes()
        return L(ARCH[n],x,y)
    def loc(f,k):
        if f=='ramanujan.md':return k+(4 if 9<=k<=143 else 6 if k>143 else 0)
        if f=='mertens.md':return k+6 if k>=16 else k
        if f=='finite.md':return k if k<=65 else k+1
        if f=='candidate.md':return k if k<12 else 42 if k==12 else k+30
        return k
    return L(n,loc(n,x),loc(n,y) if y is not None else None)
def refs(*tpl):return [L(*t) for t in tpl]
def code_text(ref):
    # Exact physical code and location from locked bytes.
    n=ref['file']; a=ref['physical_LF']; b=ref.get('end_physical_LF',a)
    return '\n'.join((C/n).read_text().split('\n')[a-1:b])
def receipt(*names):
    return [n+'_receipt.json' for n in dict.fromkeys(names)]
def row(id,fam,where,st,domain,*,strict='strict',ass=B0,source='See review.md named originals and corresponding dependencies.',impl=(),aliases=(),check='',num='',rec=(),status=OK,gap='',keep=(),bc='Common B0 result, also available under D02; not propagation.',gain=None,obj='real',role='active statement'):
    return dict(claim_id=id,family=fam,written_source=where,written_readback=loc_read(where),also_written_at=list(aliases),actual_implementation=list(impl),
                exact_statement=st,assumptions=ass,full_domain=domain,strictness=strict,real_or_integer=obj,baseline_comparison=bc,source_locators=source,
                derivation_check=check,numerical_obligations=num,actual_verification_receipts=receipt(*rec),retained_valid_branches=list(keep),
                M_status=status,precise_gap_or_counterexample=gap,propagation=gain or dict(input_used='B0 only or common across both inputs',where_it_changes_proof='No new input is needed for this branch.',matched_comparison=bc),
                V_status=V,remaining_trust=T,claim_role=role)
def prop(txt):
    return dict(input_used='D02',where_it_changes_proof='Meromorphic continuation gives beta<=27/32, shortening the right-zero density layer relative to the independent cap beta<=7/8. This yields a=5/32 rather than 1/8; compare two actual proofs with the same method and all incumbents retained.',matched_comparison=txt)
def shared(txt):
    return dict(input_used='B0 and D02 compared',where_it_changes_proof='B0 already has QRH and finite RH height; the same formula takes the D02 cap derived from its additional PsiMajorant only for the D02 specialization.',matched_comparison=txt)
def old_receipts(id,file):
    if file=='source_tables.json' or id=='C-original':return ('source_audit','ancillary','certify')
    if id.startswith(('M-finite','M-zoom')):return ('finite_mertens','finite_joins','finite_zoom','ancillary','certify')
    if id.startswith(('R-local','R-connected','R-int','R-original-real')):return ('endpoint','certify')
    if id in ('M-power-167-join','M-separation','M-pi-simple','M-three-pieces'):return ('certify','ancillary')
    return ('certify',)
claims=[]
for a in old:
    id=a['claim_id']; fn=a['written_source']['file']; hist=id in ('R-regularity','M-finite-only')
    s=migrate(a['written_source'],hist)
    al=[migrate(k,hist) for k in a.get('also_written_at',[]) if not(hist and k['file']=='candidate.md')]
    im=[migrate(k) for k in a.get('actual_implementation',[])]
    im=[v for v in im if v['file'].endswith(('.py','.json'))]
    check=rnotes.get(id)
    if id=='R-regularity':check='Historical and withdrawn. Left/right remainder jump at L=32 is positive and the local pi brackets are continuous and the upper one positive, forcing a jump in the negative square.'
    if check is None:
        if fn=='source_tables.json':check='Exact row transcribed against pinned original page; applicable domain and analytic envelope comparison checked. Numerical origin retained at literature trust.'
        elif id.startswith(('R-early','R-fixed','R-high')):check='Strict closed-ray lower profile. Directed left-onset inequality including shifted log; the scaled penalty nonincrease and positive allowance derivative give the full tail. Early rows additionally use closed interval slabs.'
        elif id.startswith('M-original'):check='The exact Dusart endpoint and relative/additive normalization are retained with the original non-strict bound.'
        elif id.startswith('M-zoom'):check='Replayed strict signed root bracket in a constant-prime slab; check later endpoints plus whole-ray tail.'
        elif fn=='portfolio.json' and id.startswith('M-'):
            check='Each row matched to interval certificate, including guards through all real slabs, and to its analytic continuation. No numerical point sample substitutes for ray monotonicity.'
        else: check='Independently read written formula and exact implementation with source/domain conditions as detailed in review.md.'
    status=(FALSE if id=='R-regularity' else WEAK if id=='M-direct-D02' else
            BASE if fn=='source_tables.json' or id in ('C-original','R-Buethe','R-signed','R-PTpi','R-tail-original','R-int') or id.startswith('M-original') else OK)
    role='own historical scope, not an operative claimed inequality' if hist else ('source alternative' if status==BASE else 'retained active statement')
    rr=old_receipts(id,fn)
    if id=='R-regularity':rr=('repair_joins','ancillary')
    if fn=='portfolio.json' and id.startswith('M-'):
        rr=('finite_mertens','finite_joins','finite_zoom','ancillary','certify') if 'finite' in id.lower() or 'trade' in id.lower() else ('certify','ancillary')
    if id.startswith('R-high'):rr=('certify','ancillary')
    gap=''
    if id=='R-regularity':gap='False archived continuity at L=32 by nonzero one-sided jump, with the remainder difference in (6.8283e-12,6.8284e-12). Current R2 is explicitly piecewise.'
    if id=='M-finite-only':gap='Original finite sweep alone did not prove a tail .10 or weighted .11 from the fine onsets. Current 60-million extension plus valid tail covers those rays.'
    ass=a['assumptions']
    cb=a['baseline_comparison']
    gain=None
    if 'D02' in id or id in ('C-cap','R-envelope-gain','M-separation','M-power-167-join'):
        gain=prop(cb)
    elif id.startswith('C-') or id in ('R-J','R-point','R-poly','M-M1','M-M2','M-power-limit'):
        gain=shared(cb)
    r=row(id,a['family'],s,a['exact_statement'],a['full_domain'],strict=a['strictness'],ass=ass,source=a['source_locators'].replace('FKS PDF p.3','FKS PDF p.2'),impl=im,aliases=al,
          check=check,num=a['numerical_obligations'],rec=rr,status=status,gap=gap,bc=cb,gain=gain,obj=a['real_or_integer'],role=role,
          keep=('R-poly','R-piecewise','R-continuous-tail') if id=='R-regularity' else ('M-extension-join',) if id=='M-finite-only' else a['retained_valid_branches'])
    if id.startswith('C-'):r['applies_to_families']=['Ramanujan','Mertens']
    if id=='R-connected' or id=='R-int':r['remaining_trust']+=' Historical integer computation is not independently reexecuted.'
    claims.append(r)
def add(*args,**kw):claims.append(row(*args,**kw))
add('R-piecewise','Ramanujan',L('ramanujan.md',145,149),'The old R2 strict lower profile is piecewise, with a discontinuity at L=32; neither bound needs continuity.',
    'Original R2 domains: L>=25 for N=20, L>=51 for N=30; discontinuity of the N=20 choice.',strict='strict inequality, nonzero jump',
    impl=refs(('profiles.py',189,200),('repair_joins.py',30,34)),aliases=refs(('repair.md',11,23),('candidate.md',14,18)),
    check='Finite pi guards are continuous at L=32 and L-1=31; square bracket is positive, so the nonzero remainder jump implies a nonzero profile jump.',rec=('repair_joins','ancillary'))
add('C-secant-count','Ramanujan',L('repair_spectrum.md',10,60),'D* and D*_h integrate K_s and its damped version; upper degree-4 Taylor moments and convexity certify clipped-node chords with whole transition panel.',
    's in [.77,b], t>=H; fixed 0<h<=.1, u>=100 when applied; default used u>=140.',strict='non-strict',
    source='Dusart2018 p.5 Theorem 2.3; FKS pp.4–5 Lemma 2.1; see C-density.',
    impl=refs(('repair_spectral.py',5,48)),check='Approximated integrals use positive moments; convexity of true integral in s yields chord bound, with whole-panel W case.',rec=('repair_spectral','ancillary'),gain=shared('Layer refinement available to both caps, before D02 propagation.'))
claims[-1]['applies_to_families']=['Ramanujan','Mertens']
add('C-secant-psi','Ramanujan',L('repair_spectrum.md',62,94),'New E_sec bounds |psi(e^u)e^-u-1|. Default a-normalized form decreases from 140, u^m form decreases from max(140,(m+4)/a); fixed-h normalized form is convex; default limit M(b) after normalizing.',
    'Default u>=140; fixed 0<h<=.1, u>=100; both caps inclusive.',
    strict='non-strict', source='Sharing spectral.md integrated Dusart (2.1), density, B0 cap and finite-height premises.',
    impl=refs(('repair_spectral.py',50,67)),check='Integrate the piecewise-linear derivative measure. Positive modes; U derivative loss <=4/u; shorten upper cap monotonically.',rec=('repair_spectral','ancillary'),gain=shared('New refined estimate in both inputs, shorter cap in D02.'))
claims[-1]['applies_to_families']=['Ramanujan','Mertens']
add('R-anchor64','Ramanujan',L('repair_applications.md',39,52),'At anchor 128 the positive V residual is <6e7; use r_64(v)=6e7 v e^-v+(128/62)65!/v^65.',
    'Real v>=128.',strict='strict lower; upper remainder non-strict',source='V normalization PT2021 p.7 (11); elementary analytic remainder.',
    impl=refs(('repair_r.py',14,21),('profiles.py',202,213)),check='Positive anchor and derivative comparison, no additional search.',rec=('repair_r','ancillary'))
for N in (30,64):
    add('R-continuous-tail'+('' if N==30 else '-64'),'Ramanujan',L('repair_applications.md',54,68),f'Continuous strict lower profile at N={N}: x^2/L^2 times positive projected polynomial minus positive penalty, with min(default E_h,E_cont,E_sec) and fixed remainder.',
        'Real L>=141, both L and L-1 admitted.',source='C-secant-psi, C-primitive, R-anchor/R-anchor64 and R-J.',
        impl=refs(('repair_r.py',20,39)),check='All analytic widths continuous, fixed anchors, no finite guards. Charge negative terms; preserve earlier R1/R2.',rec=('repair_r','ancillary'),gain=shared('Both use same new profile with respective cap.'))
add('R-tail-certificate','Ramanujan',L('repair_applications.md',70,83),'With m<=d_k, the derivative test and strict onset comparison certify the corresponding whole R3 ray.',
    'L>=141 and L-1>=(k+6)/a with checked coefficient hypotheses, N=30 or 64 as stated.',
    impl=refs(('repair_r.py',38,63)),check='Scale by L^(k+2); spectral and remainder scores and negative charges decrease; derivative loss decreases. Bisection finds sufficient points only.',rec=('repair_r','ancillary'),gain=shared('Same monotonic certificate with respective cap and threshold.'))
add('R-refined-fixed-obstruction','Ramanujan',L('repair_applications.md',101,110),'At L=190,225,250,300 the larger D02 target exceeds the selected B0 certifying formula even with refined spectral term; no arithmetic upper bound asserted.',
    'Four real fixed log onsets; both shifted and unshifted widths tested.',strict='strict certificate failure, not arithmetic failure',
    impl=refs(('certify.py',44,53),('certify.py',108,122),('repair_spectral.py',91,95)),
    check='Original barrier .004 e^-v/8 below revised B0 last coefficient >.0066. Exact V comparison at selected endpoints.',rec=('certify','repair_spectral','ancillary'),gain=prop('Fixed-onset comparisons against same refined B0 method.'))
add('R-refined-point','Ramanujan',L('repair_applications.md',112,129),'The refined analytic R1 with retained eligible bounds improves strictly in D02 over matched B0 for L>=166.4.',
    'Real closed log ray; upper at L, lower at L-1.',ass=D02,source='C-primitive, C-secant-psi, M-refined-point, R-Buethe/R-theta/R-PTpi with separate cutoff on each argument.',
    impl=refs(('repair_evaluate.py',15,19),('repair_evaluate.py',44,51)),check='Strict separation at L on positive upper bracket; nonincrease at L-1. Not a claim for maximum with all uniform branches.',
    rec=('certify','repair_spectral','ancillary'),gain=prop('Old strict comparison at 167; refined at 166.4.'))
add('R-code-x-mode','Ramanujan',L('repair_evaluate.py',31,35),'Illustrative x-mode lower-profile evaluator returns a lower bound for true R/(x^2/L^6).',
    'Integral or nonintegral x represented by positive decimal; branch L>=141 and nondegenerate interval log, including x=10^70.',
    strict='asserted lower bound; false even non-strict',impl=refs(('repair_evaluate.py',31,39),('repair_evaluate.py',82,92)),aliases=refs(('repair_evaluate.py',1),('repair_applications.md',54,68)),
    check='Read actual expression versus written penalty and correct point-log formula.',num='Reversed written R1 gives outward upper bound on true gap at the same argument.',
    rec=('evaluator_counterexample','ancillary'),status=FALSE,gap='At x=10^70 both code outputs are >737000000 while true scaled R<1.1. A sliced Horner sum already scaled by L^4 is multiplied by L^4 again.',
    keep=('R-continuous-tail','R-continuous-tail-64','R-refined-point','R-tail-certificate','R-eval-log-example'),role='actual implemented formula, not the written theorem')
add('R-eval-log-example','Ramanujan',L('repair_eval_run.txt',3,7),'At exact log input 200 the illustrative evaluator takes the correct point-log branch and gives the stated lower endpoints.',
    'Single exact real log 200 for both caps.',strict='ordinary lower bounds',impl=refs(('repair_evaluate.py',31,35),('repair_evaluate.py',44,51)),check='Point-mode path uses the correctly normalized margin_new, not the x-mode branch.',rec=('repair_evaluate',),gain=shared('Illustrative point only, not a ray proof.'))
add('M-refined-power-coefficient','Mertens',L('repair_spectrum.md',96,116),'Default refined common power-safe coefficient z exp(z e^-au/u) is nonincreasing and limits below .006665 (B0), .11625 (D02), with 21/H allowance.',
    'Real u>=140.',strict='weak monotonicity, strict limit estimates',impl=refs(('repair_spectral.py',69,77),('repair_spectral.py',91,103),('repair_evaluate.py',71,79)),
    source='M-M1, M-M2, C-secant-psi',check='Explicit square-frequency and prime-power allowance, exponential conversion of log widths; see main review.',rec=('repair_spectral','ancillary'),
    gain=shared('Do not compare normalized constants without the differing exponential rates.'))
add('M-refined-early-bridge','Mertens',L('repair_spectrum.md',136,144),'For D02 the fixed-choice slabs prove .235 for all four scaled errors from 166.4, with default .234 join at 184.',
    'Real closed slabs [166.4,167], [167,168], then quarter-log slabs through 184 and default tail.',ass=D02,
    impl=refs(('repair_spectral.py',104,122)),check='Same h and layer at two ends of each slab, convex normalized bound, conversion at left log.',rec=('repair_spectral','ancillary'),
    gain=prop('Earlier .235 ray than prior .277 onset and matched strict separation from B0.'))
add('M-refined-ratio','Mertens',L('repair_spectrum.md',146,148),'On matched closed u>=200 the D02/B0 simple envelope ratio is (.21614/.01228)exp(-u/32)<.0341 and strictly decreases.',
    'Real u>=200.',ass=D02,impl=refs(('repair_spectral.py',130,131)),check='Compare exact common units of four bounds and derivative of exponential ratio.',rec=('repair_spectral',),gain=prop('Fixed matched onset 200.'))
add('M-refined-point','Mertens',L('repair_spectrum.md',149,175),'Strict D02 improvement for the selected refined common pointwise spectra and their signed four-error envelope, not an inherent arithmetic limitation of B0.',
    'Real u>=166.4, including both early slabs and subsequent tail.',ass=D02,source='CH2 pp.3,34–36, Dusart prime-power bounds, C-original and C-secant-psi.',
    impl=refs(('repair_spectral.py',123,131),('certify.py',43,81),('repair_evaluate.py',71,79)),check='B0 h-split floor and shape/step comparisons, fixed D02 early boxes and power ratios; signed prime-power subtractions and exponential conversion do not consume slack.',
    rec=('repair_spectral','certify','ancillary'),gain=prop('Refined strict pointwise onset 166.4 versus prior 167; exact finite branch already expired.'))
add('M-block-prefix','Mertens',L('repair_applications.md',146,165),'New 60-million block scan bounds actual prime prefixes and all four normalized errors at every real point of each closed block; exact finite pointwise prefixes also allowed.',
    'Closed blocks of 128 on [10 million,60 million], actual pointwise prefix for 2<=x<=60 million.',
    strict='non-strict enclosure, strict coefficient tests',source='Dusart2018 4.2 for normalizer tail; exact finite sieve.',impl=refs(('repair_finite.py',8,53)),
    check='Monotone raw prefixes, pre/post updates and outward actual log interval; uses independently replayed normalizers.',rec=('finite_mertens','repair_finite','ancillary'))
add('M-extension-join','Mertens',L('repair_applications.md',167,185),'New tail at 60 million joins all new finite rays; normalized coefficients <.077911 and <.081342 for first three/weighted respectively.',
    'Real x>=60000000 for the displayed coefficient bounds through log(10^13), then existing smaller tails.',
    impl=refs(('repair_spectral.py',133,142),('repair_joins.py',8,28)),source='CH2 p.35 Lemma 9.2, M-powers, M-cheap-join and M-three-pieces.',
    check='Two different U0 and U1 upper bounds, guard u>=17, monotonic coefficients and all joins included. Does not prove .08 weighted by this test.',rec=('repair_spectral','repair_joins','ancillary'))
add('M-code-medium-conversion','Mertens',L('certify.py',170,175),'Numeric certificate for medium-range product conversion with stated generic expm1(D)<=D exp(D).',
    'Four distinct left endpoints from log(10^13) through 40.',
    impl=refs(('certify.py',170,175),('mertens.py',82,92)),check='The certifier exponent omits the denominator present in D. The stronger expression j exp(j/u^3) with full denominator independently passes all claimed constants.',
    rec=('certify','ancillary'),keep=('M-three-pieces','M-pi-simple'),role='certificate formula readback and resolved ancillary obligation')
add('M-eval-log-example','Mertens',L('repair_eval_run.txt',1,7),'At log input 200 the refined illustrative Mertens evaluator computes the stated four normalized-error upper endpoints.',
    'Single exact log 200 for both caps.',strict='ordinary non-strict upper enclosures',impl=refs(('repair_evaluate.py',54,80)),
    check='Coded M formulas take signed log endpoints and exact relative transformations; finite illustrative example is not a ray argument.',rec=('repair_evaluate',),gain=shared('Matched example only; monotonic proof elsewhere.'))
p=read(C/'repair_portfolio.json')
rp='repair_portfolio.json'
def loc_array(k,i,width):
    lines=(C/rp).read_text().split('\n')
    start=next(j+1 for j,line in enumerate(lines) if line.startswith('  "'+k+'"'))
    return L(rp,start+2+(width+2)*i,start+(width+2)*(i+1))
for i,(k,m,b,d) in enumerate(p['ramanujan_full_k_coefficient_B0_D02']):
    bc=f'Same strict order {k} full coefficient {m}: B0 L>={b}, D02 L>={d}; sufficient within-method onsets.'
    for cap,lo in (('B0',b),('D02',d)):
        add(f'R-refined-full-{k}-{cap}','Ramanujan',loc_array('ramanujan_full_k_coefficient_B0_D02',i,4),f'Strict R3 order {k}, m={m}, at L>={lo} ({cap}).',
            f'Real x with L>= {lo}, closed onset.',ass=B0 if cap=='B0' else D02,source='C-secant-psi plus R-J, R-anchor/anchor64, monotonic tail comparison.',
            impl=refs(('repair_r.py',38,63),('repair_r.py',83,87),('repair_portfolio.py',10,22),('repair_evaluate.py',36,39)),
            aliases=refs(('repair_applications.md',85,99),('repair_r_full_run.txt',2+i)),
            check='Matched coefficient sign, strict verified left endpoint, scaled penalty and derivative hypotheses. N=30 for 6..29, N=64 for 30..62.',num='Exact plus/minus projection, interval onset and derivative test.',rec=('repair_r','repair_portfolio','ancillary'),bc=bc,gain=prop(bc) if cap=='D02' else None)
for i,(k,m,l,oldl) in enumerate(p['ramanujan_early_k_m_current_previous']):
    add(f'R-refined-early-{i}','Ramanujan',loc_array('ramanujan_early_k_m_current_previous',i,4),f'Strict R3 order {k}, m={m}, from L={l} replacing sufficient B0 onset {oldl}.',
        f'Real closed log ray L>={l}; independently of D02.',source='R-J, R-poly, finite pi and CH2 sources, original B0 tail.',
        impl=refs(('repair_r.py',65,81),('profiles.py',193,200),('repair_evaluate.py',26,30)),aliases=refs(('repair_applications.md',16+i)),
        check='All additional closed .0002 boxes checked through old onset; original proof extends beyond.',rec=('repair_r','certify','repair_portfolio'),bc=f'B0 arithmetic gain: sufficient onset {oldl} -> {l} at same m.')
for i,(l,k,cap,m) in enumerate(p['ramanujan_fixed_L_k_800b_m']):
    t='B0' if cap=='700' else 'D02'
    bc=f'Matched fixed L={l} and k={k}; coefficient pair {p["ramanujan_fixed_L_k_800b_m"][i//2*2][-1]} / {p["ramanujan_fixed_L_k_800b_m"][i//2*2+1][-1]} (B0/D02).'
    add(f'R-refined-fixed-{l}-{t}','Ramanujan',loc_array('ramanujan_fixed_L_k_800b_m',i,4),f'Strict R3 order {k}, m={m}, from L={l} for {t}.',
        f'Real closed log ray L>={l}.',ass=B0 if t=='B0' else D02,source='C-secant-psi, R-tail-certificate and R-refined-fixed-obstruction.',
        impl=refs(('repair_r.py',88,94),('repair_evaluate.py',40,43)),aliases=refs(('repair_applications.md',101,110)),
        check='Left end derivative and penalty check with fixed coefficient and common cap recipe.',rec=('repair_r','certify','repair_portfolio'),bc=bc,gain=prop(bc) if t=='D02' else None)
for i,(l,B,d) in enumerate(p['mertens_power_L_B0_D02']):
    bc=(f'B0 C={B}, D02 C={d} at matched u>={l}; ratio (C_D/C_0)exp(-u/32) on that ray.' if (B and d) else
        'Mixed comparison: no matched refined simple row at this onset for the other input; compare whole eligible pointwise envelopes or later common onset.')
    for t,c in (('B0',B),('D02',d)):
        if c is None:continue
        a='1/8' if t=='B0' else '5/32'
        add(f'M-refined-power-{l}-{t}','Mertens',loc_array('mertens_power_L_B0_D02',i,3),
            f'First three errors <{c}x^(-{a})/u, weighted error <{c}x^(-{a}) ({t}).',
            f'Real closed log ray u>={l}.',ass=B0 if t=='B0' else D02,
            impl=refs(('repair_spectral.py',82,122),('repair_evaluate.py',65,70)),aliases=refs(('repair_spectrum.md',123+i)),source='M-refined-power-coefficient and closed bridges if needed.',
            check='Strict left value with allowance and full conversion; monotone tail (fixed h convex slabs for .235).',rec=('repair_spectral','repair_portfolio','ancillary'),bc=bc,gain=prop(bc) if t=='D02' else None)
for i,(c,*ons) in enumerate(p['mertens_common_C_P_Q_reciprocal_weighted_onset']):
    for j,l in enumerate(ons):
        pi=('P','Q','reciprocal sum','weighted sum')[j]; units=2 if j==3 else 3
        add(f'M-extended-{c}-{j}','Mertens',loc_array('mertens_common_C_P_Q_reciprocal_weighted_onset',i,5),
            f'{pi} error <{c}/u^{units} on x>={l}.',f'Real closed x ray x>={l}.',
            source='M-block-prefix plus M-extension-join, and M-finite-sieve for fine .11/.10 onset joins.',
            impl=refs(('repair_finite.py',25,53),('repair_joins.py',8,28),('repair_portfolio.py',15,24),('repair_evaluate.py',60,64)),
            aliases=refs(('repair_applications.md',138+i)),check='Real block enclosure after last uncertified endpoint or earlier fine sweep meeting extension. All analytic tail pieces have strict room.',
            rec=('finite_mertens','repair_finite','repair_joins','repair_spectral','repair_portfolio','ancillary'))
# Individually index finite theta source rows as dependencies, including the harmless weak k=0 use.
for ordinal,(x,k,eta,line) in enumerate([(1,0,'1',4),(2,1,'1.2323',4),(908994923,1,'.001',4),(2,2,'3.965',5),(3594641,2,'.2',5),(122568683,2,'.05',5),(7713133853,2,'.01',6),(2,3,'20.83',6),(32321,3,'10',6),(89967803,3,'1',7),(158822621,3,'.78',7),(767135587,3,'.5',7),(2,4,'151.3',8)]):
    add('M-theta-source-'+str(ordinal),'Mertens',L('mertens.py',line),f'Dusart theta row used with k={k}, eta={eta}, onset {x}.',
        f'Real x>={x}.',strict='non-strict enclosure used by code',source='Dusart2018 original PDF p.11 Theorem 4.2; use k=0 weak and clamp to zero if needed.',
        impl=refs(('mertens.py',3,17),('mertens.py',64,75)),aliases=refs(('mertens.md',131,137),('mertens.md',189,206)),
        check='Constants and guards match. For k=0 near 1, weak inequality is direct from theta(t)=0 on [1,2); not importing a false strict statement.',status=BASE)
assert len(set(r['claim_id'] for r in claims))==len(claims)
for r in claims:
    # Bind short exact implementation readbacks separately from mathematical statements,
    # while not duplicating entire long certificate modules for each scalar row.
    r['implementation_first_line']=[loc_read(x) for x in r['actual_implementation']]
    if not r['actual_implementation']:r['implementation_scope']='Written/formula-only or original quotation; no separate proof-assistant implementation.'
    for w in [r['written_source'],*r['also_written_at'],*r['actual_implementation']]:
        assert w['physical_LF']>0 and w.get('end_physical_LF',w['physical_LF'])<=len((C/w['file']).read_bytes().split(b'\n')),w
    assert all((S/f).exists() for f in r['actual_verification_receipts'])
def relevant(fam):return [r for r in claims if r['family']==fam]
def ids(fam,cond):return [r['claim_id'] for r in relevant(fam) if cond(r['claim_id'])]
claims_R=ids('Ramanujan',lambda id:id.startswith(('R-refined-full','R-refined-fixed','R-refined-early','R-continuous','R-refined-point')) and id!='R-refined-fixed-obstruction')+['R-connected','R-local-root','R-point','R-poly','R-asym']
claims_M=ids('Mertens',lambda id:id.startswith(('M-extended-','M-refined-','M-zoom')))+['M-envelope','M-block-prefix','M-extension-join','M-theta','M-pi-general','M-pi-simple','M-general-sigma']
commands=[]
for f in sorted(S.glob('*_receipt.json')):
    j=read(f)
    commands.append({k:j[k] for k in ('command','cwd','status','elapsed_seconds','stdout_sha256','stderr_sha256')}|{'receipt':f.name})
review=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=idx['candidate_id'],input_stage='D02',
    assessment_complete=True,all_claims_inventoried=True,reviewed_source_hashes=D,source_bibliography=source['sources'],
    actual_verification_commands=commands,verification_effort={'restore':['/usr/bin/python3.10','/task/RESTORE_CANDIDATE.py','--out','/work/c017'],
       'shell':'/bin/bash non-login','proof_kernel':'None supplied or used','original_papers':'14 exact PDF/text hash matches; proof and formulas read in original page-marked extractions','observed_full_sweeps':'25,000,000 event and 60,000,000 block sweeps independently reexecuted at original parameters','additional_input':'No D01; no assumptions other than seven common originals and exact D02.',
       'historical_assessment_scope':'Retained disclosed own earlier source and comparison inventory. Statement identities and associations mapped from the own packet; previous verdicts not used as premises; independent mathematical/source evaluation and material replays in this submission.'},
    family_assessments={
     'Ramanujan':dict(strongest_supported_portfolio=claims_R,rejected_or_incomplete_claims=['R-code-x-mode'],historical_withdrawals=['R-regularity'],remaining_assessment_work=[],summary='Supported written terminal real sign ray (published integer bridge at literature trust), early common margins, refined D02 full orders 6..62 and matched pointwise gain. False x-mode evaluator separate from valid paper bounds; no formal PV.'),
     'Mertens':dict(strongest_supported_portfolio=claims_M,rejected_or_incomplete_claims=[],remaining_assessment_work=[],summary='All written common and D02 bounds supported. Finite 25M prime slabs and 60M blocks include real endpoints. Full product conversion denominator checked independently; literature/ordinary arithmetic tier only.')},
    shared_dependencies=[r['claim_id'] for r in claims if r.get('applies_to_families')],claims=claims,
    no_other_arm_or_ranking_seen=True,new_core_math_salvage_performed=False,original_candidate_bytes_changed=False)
save('review.json',review)
save('STAGE_STATUS.json',dict(ready_for_review=True,families={f:dict(status='supported_at_stated_trust_tier',claim_files=['review.md','review.json']) for f in ('Ramanujan','Mertens')},serious_attempts_documented=True),True)
print(len(claims),'claims', (S/'review.json').stat().st_size, 'bytes')
