"""Build keyed registry from exact receipts and audited theorem metadata.
Historical registry used for indexing old statements and code locations only."""
from pathlib import Path
from fractions import Fraction
import ast, json, hashlib, re
d=Path(__file__).resolve().parent
p=Path('/work/review_exact')
task=Path('/task')
ix=json.loads((task/'CANDIDATE_INDEX.json').read_text())
bib=json.loads((task/'SOURCE_INDEX.json').read_text())['sources']
nm={x['original_name']:x for x in ix['candidate_files']}
hm={x['sha256']:x['original_name'] for x in ix['candidate_files']}
def lines(n): return (p/n).read_bytes().decode().split('\n')
def loc(n,a,b=None):
    x=nm[n]
    assert 0<a<=len(lines(n)) and (b is None or a<=b<=len(lines(n)))
    return dict(file=x['packet_name'],original_name=n,physical_LF=a,sha256=x['sha256'],**({'end_physical_LF':b} if b and b!=a else {}))
def remap(x):
    n=hm[x['sha256']]
    if n=='D01_LOCKED_mertens.md': n='mertens.md'
    return loc(n,x['physical_LF'],x.get('end_physical_LF'))
def raw(a):
    return '\n'.join(lines(a['original_name'])[a['physical_LF']-1:a.get('end_physical_LF',a['physical_LF'])])
def code(q):
    a=loc(*q);return {'source':a,'physical_readback':raw(a)}
claims=[]; trials=[]
ok='supported_at_stated_trust_tier'; weak='equivalent_or_weaker'; base='baseline_retained'
false='false_with_specific_counterexample'
B0='B0: exact cumulative seven originals on their lawful domains; no full RH.'
B2='Exact D02 input, in addition to B0 (all-real direct psi input from exp(200)).'
global_source=[
 'OpenAIQRH p.4 Thm.1.1 and next paragraph, text LF255–262',
 'PT PNT pp.3–4 Thm.2 and Lemmas 2,4, text LF205–257',
 'PT FiniteRH p.2 Thm.1 and p.4 Cor.1, text LF48–49,138–150; p.4 PDF objects 112/114',
 'FKS Thm.3.2 p.8, Cor.2.9 p.7, Table 8 p.26 (.77 block), text LF586–608,631–642,3139–3258',
 'Dusart Thm.2.3 PDF p.5 LF245–257; (2.1) pp.3–4 LF171–189',
 'CH2 p.3 Cor.1.2/1.3, p.35 Lemma 9.2, p.36 (9.2), p.43 (B.1) Lemma B.1, text LF193–239,5216–5223,5273–5306,6133–6144',
 'Dusart Prop.4.3 p.12 Cor.4.5 p.13, Thm.5.1 proof p.15 LF1049–1056,1129–1152,1280–1285']
msource=[
 'Dusart Thms.5.6/5.7/5.9 pp.17–20 LF1476–1502,1552–1583,1637–1661',
 'Dusart Thm.4.2 p.11 LF959–1010; Thm.3.3 p.7 LF458–475 and Table 1 pp.8–9 LF482–765',
 'PT PNT Thm.1/Cor.1 pp.2–3 LF77–117,135–201; FKS Thms.1.1/1.2/Cor.1.4 p.2 LF113–143']
def receipt(stage,ff=()):
    return [loc(*f) for f in ff]+[stage+'.'+e for e in ('stdout','stderr','exit')] if stage else [loc(*f) for f in ff]
def add(cid,fam,target,statement,domain,strict,drv,*,input='B0',compare=None,status=ok,cs=(),rec=(),stage='replay02',sl=None,retain=(),gap=None,typ='real',ob=None,srcclass='active candidate assertion'):
    a=loc(*target)
    propagation={'input_used':input,'where_it_changes_proof':
     'Mellin exclusion, then density endpoint and signed integrated-zero terms with new cap (both shifted arguments for gap); only uses direct pointwise input from exp(200).' if input=='D02'
     else 'No added input is required. Exact D01 is already implied by B0.',
      'matched_comparison':compare or 'B0 and B0+D01 coincide; independently valid branch retained under D02.'}
    c=dict(claim_id=cid,family=fam,written_source=a,exact_written_readback=raw(a),source_class=srcclass,
           exact_statement=statement, assumptions=[B0]+([B2] if input=='D02' else []), full_domain=domain,strictness=strict,real_or_integer=typ,
           baseline_comparison=propagation['matched_comparison'],source_locators=sl or global_source+(msource if fam=='Mertens' else []),
           derivation_check=drv,numerical_obligations=ob or ('Exact finite checks at the stated parameters and analytic extension where indicated.' if stage else 'Written deduction at the listed source trust.'),
           implemented_readbacks=[code(q) for q in cs],actual_verification_receipts=receipt(stage,rec),retained_valid_branches=list(retain),M_status=status,
           precise_gap_or_counterexample=gap,propagation=propagation,
           V_status='No Lean or Blueprint correspondence supplied; not checked. Not kernel arithmetic or source-first PV.',
           remaining_trust='Permitted original statements incl. source finite computations, written analysis, and ordinary exact executable arithmetic where used.')
    claims.append(c);return c

R='Ramanujan';M='Mertens'
old=json.loads((p/'D01_M_REVIEW_review.json').read_text())
oldids=json.loads((p/'OWN_D01_VALIDATED_FLOOR.json').read_text())['validated_claim_ids_by_family']
assert set(sum(oldids.values(),[]))=={c['claim_id'] for c in old['claims']} and len(old['claims'])==155
old_weak={'M-direct-D01','M-coarse','M-abs-200','M-abs-400','M-abs-810','R-extra-15','R-extra-23','R-extra-30','R-extra-31'}
old_baselines={'C-CH-RH-sign','R-source-DP','R-source-PT','M-source-E_1','M-source-E_P','M-source-E_Q','M-source-E_w'}
for h in old['claims']:
    k=h['claim_id'];a=remap(h['written_source'])
    t=(a['original_name'],a['physical_LF'],a.get('end_physical_LF'))
    src=[s.replace('pp.3–4','p.2') if 'Thms.1.1' in s and s.startswith('FKS') else s for s in h['source_locators']]
    # These are the actual new review commands, not the quoted old receipts.
    outs=[]
    for z in h['actual_verification_receipts']:
        if isinstance(z,dict) and 'sha256' in z:
            rr=remap(z);outs.append((rr['original_name'],rr['physical_LF'],rr.get('end_physical_LF')))
    codes=[]
    for z in h.get('implemented_readbacks',[]):
        rr=remap(z['source']);codes.append((rr['original_name'],rr['physical_LF'],rr.get('end_physical_LF')))
    st=weak if k in old_weak else base if k in old_baselines else ok
    proof="Independently checked against current exact text/code and originals; "+h['derivation_check']
    cmpstr='Unchanged in B0+D01 or B0+D02; no additional assumption used. '+h['baseline_comparison']
    cmpstr=cmpstr.replace('B01','D01')
    statement=h['exact_statement']
    for before,after in [('A021:','ramanujan.md:'),('A017:','mertens.md:'),('A004:','certify.py:'),('A013:','gap_envelope.txt:')]:
        statement=statement.replace(before,after);proof=proof.replace(before,after)
    dom=h['full_domain']; strict=h['strictness']; typ=h['real_or_integer']
    if k=='R-source-PT-real-excluded':
        statement='Candidate correctly refutes the literal early real PT interval. At B+1/8, −10^7<R<−10^6; no such assertion is inherited.'
        dom='Counterexample x=38358837682+1/8 in the literal quoted real interval.'
        proof='Exact counts on [B,B+1) and rational log/exp sign check in edge/audit. PT integer restriction and corrected real ray survive.'
    if k=='R-sharp': proof+=' New analytic continuation from 36.60 also overlaps; inherited proof uses 36.85.'
    if k=='M-theta-envelope': src=list(dict.fromkeys(src+msource))
    c=add(k,h['family'],t,statement,dom,strict,proof,status=st,compare=cmpstr,cs=codes,rec=outs,
          stage='audit' if k=='R-source-PT-real-excluded' else 'replay01' if outs or codes else None,sl=src,typ=typ,ob=h['numerical_obligations'])
    c['history_status_not_used']=True
    if k=='R-source-DP':
        c['assumptions']=[B0,'Full RH only for the separately quoted source Thm.1.3; not invoked as an unconditional premise.']
    if a['original_name']=='mertens.md':
        c['retained_exact_own_written_locator']=loc('D01_LOCKED_mertens.md',t[1],t[2])
add('R-quoted-literal-PT',R,('ramanujan.md',52),'Quoted literal (not endorsed) PT claim R>0 for B<x≤exp(58).',
    'Real B<x≤exp(58).','Strict','Frozen counts and monotonic crossing; exact counterexample check.',
    status=false,srcclass='quoted original, explicitly excluded',stage='audit',cs=(('edge.py',19,53),),
    rec=(('edge_result.txt',1,3),),gap='At x=306870701457/8 exact arithmetic gives −10^7<R(x)<−10^6.',retain=('R-source-PT','R-sharp','R-source-PT-real-excluded'))

for fam in [R,M]:
    c=add(fam[0]+'2-cap',fam,('analytic02.md',7,12),'Every nontrivial zero has real part ≤27/32 under D02.',
      'Entire nontrivial strip, all heights; equality not excluded.','Weak cap','Euler product → locally normally convergent Mellin integral → meromorphic uniqueness; pole residue at a zero cannot vanish.',
      input='D02',stage=None,typ='complex zero locus',compare='7/8 cap from B0; D01 redundant; 27/32 applies at all heights and changes explicit formula even for x<exp(200).')
    c['source_locators']+=['Exact INPUT_CONTRACT.json (candidate member 007; real x≥exp(200)).']
    add(fam[0]+'2-slab',fam,('analytic02.md',14,37),'Pointwise ψ relative endpoint bound: low .036u² exp(−(1−s)u), Perron 2.091u exp(−.47u), positive slab telescoping or continuous layers using the chosen cap.',
      'All real u≥100 in discrete branches; continuous branches at u≥100 and u≥their indicated onset >M; direct D02 branch u≥200.',
      'Weak bound','Density ∫N/t², quartic majorant for 3<r<4, nested positive weights, terminal cap included; piecewise continuous extensions charged from each segment.',input='D02',
      cs=(('density.py',12,54),('density.py',55,89)),rec=(('global02_result.txt',8),),
      compare='Same admissibility, supported with either cap in the same-method ablation; D02 moves slab terminal point and survival rate.')
    add(fam[0]+'2-integral',fam,('analytic02.md',39,62),'Signed integrated-zero bounds (60) for I_w, w=1,k, using .0503 and 5.8e-12 reciprocal-square sums and trivial term 1.84e^(−L).',
      'All real L≥20, either cap.','Two inclusive bounds','Summable compact double series, then tail termwise by two inverse ordinate powers. Rounded count with source Rosser bands; no moving T* in an integral.',
      input='D02',cs=(('osc02.py',5,22),),rec=(('global02_result.txt',8),),
      compare='Same L² argument under B0; high-ordinate exponential changes with D02, low part finite RH unchanged.')

add('R2-exact-profile',R,('ramanujan02.md',12),'R(x)=632207037*e*x/L−1644673232² on the real post-root subinterval.',
    'Real ξ<x<38358837683.','Exact equality; positive there','Both counts constant on the half-open unit interval, with strict positivity after root.',
    stage='replay01',cs=(('edge.py',31,53),),rec=(('edge_result.txt',1,3),))
add('R2-signed-q',R,('ramanujan02.md',51,67),'Signed normalized π discrepancies from endpoint V, integrated U, and separate power losses; enhanced lower bound of form (2).',
    'Transfer valid for u≥20 using source domains; executable qosc from u≥34; actual gap branches use L and L−1 in proved domains.',
    'Weak bounds','Absolute and signed new transfers checked separately; anchor 400003, upper endpoint power subtraction, and termq guards match executable.',
    input='D02',cs=(('gap02.py',6,65),('gap02.py',99,109)),rec=(('global02_result.txt',8),),
    compare='Both caps valid; only D02 slablayer/oscillatory high terms and optional direct branch improve the D02-specific boxes.')
add('R2-poly-engine',R,('ramanujan02.md',69,79),'General N Li residual/coefficients; cell enclosures and monotone scaled tail extend rational certificate to real rays.',
    'Guard L−1≥V; whole active endpoint domains, tail guards as written.','Strict conclusion on PASS','Series enclosure, positive residual integral, exact shifted cell and convolution penalty; use nonnegative coefficient residuals and scale by L^(N−4).',
    cs=(('gap02.py',67,127),),rec=(('order_d2.txt',1,20),),
    compare='Same engine under both caps; numerical rows separate propagation.')
z0='z=1/L, r=R L^6/x²'
for n,inp in [('b0','B0'),('d2','D02')]:
    f='window_'+n+'.txt';status_by_line=lines('window_b0.txt')
    for i,x in enumerate(lines(f),1):
        m=re.match(r'(RAY PASS|WINDOW PASS) (\S+) (\S+) (\S+) (.*)',x)
        if m:
            kind,b,l,h,a=m.groups();poly=tuple(map(str,ast.literal_eval(a)))
            a0=status_by_line[i-1].startswith(kind)
            comp=('Identical target/domain PASS under B0, with no D02 propagation credit.' if a0 else
                  'B0 same-target test fails (not a counterexample). New cap relaxes intermediate two-argument error and certifies the connected ray.') if inp=='D02' else 'Original-input branch, with no D01 propagation; closed-window strength retained at its own domain.'
            J=f'all real L≥{l}' if kind=='RAY PASS' else f'all real L in [{l},{h}]'
            add(f'R2-window-{n}-{i}',R,(f,i),f'r>sum(p_i z^i) with p={poly}; {z0}.',J,'Strict at all real points incl. onset',
                f'Closed cells [{l},{h}] plus '+(f'guarded strict tail from {h}.' if kind=='RAY PASS' else 'no claimed tail.'),
                input=inp,status=weak if inp=='D02' and a0 else ok,compare=comp,cs=(('windows02.py',4,20),('gap02.py',83,127)),rec=((f,i),))
        elif x.startswith(('FAIL','TAIL FAIL')):
            trials.append({'source':loc(f,i),'readback':x,'classification':'Failed sufficient test only, not a final claim or counterexample; byte-replayed.'})
    f='order_'+n+'.txt'
    other=lines('order_b0.txt' if n=='d2' else 'order_d2.txt')
    for i,x in enumerate(lines(f),1):
        if not x:continue
        kind,b,xpar=x.split(' ',2)
        if kind=='ORDER':
            count,N,j=xpar.split()
            desc=f'r>P_{count}(1/L) with P specified in ramanujan02.md:5–7, auxiliary truncation N={N}.'
        else:
            co,j=xpar.rsplit(' ',1);desc=f'r>sum(p_i/L^i) with p={co}.'
        jother=other[i-1].rsplit(' ',1)[1]
        cb0,cb2=(j,jother) if n=='b0' else (jother,j)
        add(f'R2-order-{n}-{i}',R,(f,i),desc,f'All real L≥{j}.','Strict incl. onset',
          f'Guarded positive-term penalty compared at J={j}; sign propagates analytically.',
          input=inp,compare=f'Matched polynomial: B0 onset {cb0}, B0+D02 onset {cb2}; sufficient (not optimal).',
          cs=(('search02.py',11,20),('gap02.py',83,111)),rec=((f,i),))
for i,x in enumerate(lines('global02_result.txt'),1):
    if not x.startswith('VARIABLE'):continue
    _,_,b,a,m,j=x.split()
    inp='B0' if b=='7/8' else 'D02'
    add(f'R2-growing-{a}',R,('ramanujan02.md',34+i),f'r>P_m(1/L), m=floor(L/{a}), m0={m}.',f'All real L≥{j}, incl. order transitions.',
      'Strict','Omitted positive coefficient, normalized three ratios decreasing from m0. Verified units and truncation anchor.',
      input=inp,compare='Compare rate floor(L/a) and initial domain together; D02 supports smaller a. From L≥4000 a=32 dominates all three B0 variable choices.',
      cs=(('global02.py',20,28),),rec=(('global02_result.txt',i),))
for n,a,b,c in [('B0',46,'1/8','.048'),('D02',47,'5/32','.87')]:
    add('R2-model-'+n,R,('ramanujan02.md',a),f'|r−H(L)|<{c} L^4 exp(−{b} L).','All real L≥176.','Strict two-sided',
      'Absolute normalized π bounds at both arguments, bounded A, including shifted multiple and square term. Scale decreases from 175, respectively 176.',
      input=n,compare='D02/B0 bound ratio (.87/.048)exp(−L/32) strictly <1 from 176 onward.',
      cs=(('global02.py',6,18),('gap02.py',74,82)),rec=(('global02_result.txt',8),))

add('R2-model-dominance',R,('comparison02.md',20),'New D02 model lower bound surpasses each retained B0 form-(2) lower bound.',
    'All real L≥181; the B0 sign branch is not active.','Strict formula comparison',
    'Retained B0 q boxes have coefficient ≥.005 at both arguments (ψ endpoint floor .006, shift <.001); A≥1, giving ≥.015 scaled penalty. D02 error .87 exp(−L/32) is smaller there.',
    input='D02',compare='Restriction to listed model bounds; keep independent polynomial profiles.',
    cs=(('global02.py',29,38),),rec=(('global02_result.txt',8),))
add('R2-deep-dominance',R,('comparison02.md',22,27),'D02 floor(L/32) polynomial is strictly larger than B0 tabulated and growing-order polynomials; within the retained B0 endpoint-box method no degree with at least that many coefficients is certified there.',
    'All real L≥4000; only the identified comparator methods.','Strict formula comparison',
    'Positive coefficients and degree inequality; separate upper bound for H−P_m via shift tail and lower square, then compared to necessary penalty with factorial integral and m=floor(L/32).',
    input='D02',compare='Not a global impossibility for B0; tests fixed-order method as well as tabulated and variable profiles.',
    cs=(('global02.py',41,48),),rec=(('global02_result.txt',8),))
add('R2-max',R,('ramanujan02.md',49),'Take pointwise maximum of all applicable bounds with strictness supplied by a strict realizing branch.',
    'Union of the displayed domains in both generations.','Weak unless realized by a strict branch',
    'Intersection of valid lower claims preserves every surviving branch.',input='D02',stage=None)
add('R2-withdrawn-15000',R,('ramanujan02.md',96),'Withdrawn trial with fifth coefficient 15000 eventually exceeds r.',
    'Counterexample to proposed eventual lower profile; violation at L=10000 and asymptotically.','Strict violation',
    'The fifth coefficient exceeds 13985; explicit exact check at L=10000. This is the candidate’s valid refutation, not an endorsed trial-theorem.',stage='audit',
    retain=('R2-order-d2-20','R2-order-b0-20'),srcclass='candidate refutation of withdrawn trial')

add('M2-signed-transforms',M,('mertens02.md',16,25),'Intersect the new ψ and θ signed intervals using signed I_w, exact corrected power tails, and exact separate relative-product transforms.',
    'Real L≥20; endpoint boxes at their individual source domains; inherited envelope for x≥1000.',
    'Weak bounds','The strictly-above-x tails, lower bound on A_pow and small positive C subtraction, power integral lower and upper bounds, plus signed max formula were checked.',
    input='D02',compare='Valid for either cap. D02 changes high-ordinate I_w and V endpoint; finite sign, prime-power and normalization ingredients are independent.',
    cs=(('osc02.py',24,86),),rec=(('m02_result.txt',35,45),))
add('M2-coefficient',M,('mertens02.md',29,34),'Functional decreasing power coefficient for all four normalized errors (Cw, Cd and Cd/(1−Cd exp(−cL)/L)); limiting discrete branch from final slab plus 5.8e−12.',
    'Real L≥150 at active positive branches satisfying scaled derivative guard and positive denominator.',
    'Weak majorants','Verified endpoint rate, weight Lk, positive power corrections, log-to-relative conversion and decreasing coefficients. Use actual analytic formulas, not rounding floors.',
    input='D02',compare='Same formulas with B0 cap; D02 changes rates and discrete/layer constants.',
    cs=(('osc02.py',87,101),),rec=(('m02_result.txt',1,34),))
add('M2-direct-input',M,('mertens02.md',34),'Direct D02 insertion gives weighted coefficient [L²+L²/c+2L/c²+2/c³]/64 and reciprocal/log-product [L+(L+1)/c+1/c²]/64 outside exp(−cL), plus power corrections.',
    'Real L≥200, c=5/32; relative bounds require a separate conversion.',
    'Weak majorants','Evaluate ∫u²e^(−cu) and ∫(u+1)e^(−cu) and add endpoint. No use of this loose integral in unified power certificate.',
    input='D02',status=weak,stage=None,compare='Main weighted endpoint alone ≥625 scaled, versus <.226 from cap-based density on this ray.')
add('M2-conversions',M,('mertens02.md',12),'Generic power weakening and inverse-log conversion: C exp(−(c−d)J)x^(−d), d≤c; C J^k exp(−cJ)/L^k if J≥k/c for G_M.',
    'Real L≥J with the recorded guards.','Weak bounds','The scaled exponential or L^k exp(−cL) is decreasing. Interpret underlying sum/product factors as in G_M.',stage=None)
add('M2-envelope',M,('mertens02.md',25),'Pointwise minimum across all applicable interval/published/block/cutoff/power branches, respecting exact nonlinear product transformations.',
    'All real x≥1000, with each branch restricted to its own full domain.','Weak bounds',
    'Both signs preserved for each arithmetic quantity; valid minima with all old and new overlaps, no assertion of a finite block beyond its N.',
    input='D02',stage=None,compare='Whole-domain non-worsening by retaining B0 and strict formula comparison from L=180 only.')
add('M2-dominance',M,('comparison02.md',7,14),'D02 bounds are non-worsening on x≥1000 and strictly smaller than the identified B0 formula envelopes for each of the four errors on L≥180.',
    'All real x≥1000; strict comparison only at L≥180.','Comparison of bound formulas',
    'B0 endpoint coefficient floors verified; testing v(L)=δ and v=0 above it with power shifts gives admissible box values, not an actual prime function. Direct published/rounded constants also exceed the comparison scale.',
    input='D02',compare='Against retained B0 formulas including signed minima and lawful original competitors, not all possible deductions.',
    cs=(('global02.py',29,38),('global02.py',48)),rec=(('global02_result.txt',8),),
    sl=global_source+msource+['FKS (2.1),(3.4),(3.8),(4.1),(5.2), Table 5 PDF p.22 LF2307–2575.'])

for i,s in enumerate(lines('m02_result.txt'),1):
    if not s:continue
    tag,b,*stuff=s.replace(' PASS ',' ').split()
    inp='B0' if b=='7/8' or tag=='BRIDGE' else 'D02'
    if tag=='ONSET':
        err,b,j=(b,*stuff); inp='B0' if b=='7/8' else 'D02'
        pair=lines('m02_result.txt')[i] if inp=='B0' else lines('m02_result.txt')[i-2]
        jother=pair.rsplit(' ',1)[1]; cb0,cb2=(j,jother) if inp=='B0' else (jother,j)
        desc=f'G_M≤{err}'; domain=f'All real L≥{j}.'
        deriv='Positive scaled monotone coefficient, so the endpoint test proves the fixed target on the whole ray.'
        comp=f'Fixed target {err}: B0 sufficient onset {cb0}, D02 {cb2}.'
        cod=(('m02check.py',70,78),('osc02.py',87,101))
    elif tag=='TAIL':
        j,c=stuff
        desc=f'G_M≤({c}) exp(−(1−{b})L)';domain=f'All real L≥{j}.'
        deriv='Rational test of decreasing scaled coefficient at J. Product conversion denominator positive, valid thereafter.'
        comp='Keep onset/strength tradeoffs; compare at a common onset by changing rate with the explicit exponential factor.'
        if Fraction(j)==200:
            comp='At 200 matched old/B0 coefficients .019354/.01283 at rate 1/8; D02 .22528 at 5/32 gives <.000435 at rate 1/8 on whole ray.'
        cod=(('m02check.py',50,59),('osc02.py',87,101))
    elif tag=='BRIDGE':
        c,=stuff;desc=f'max(L³E_1,L³E_P,L³E_Q,L²E_w)≤{c}'
        domain=f'All real L≥{b}.'
        deriv='Closed 1/64-width cells (up to 150); analytic decreasing inverse-log scaling beyond.'
        comp='B0 secondary improvement; old separate .0667/.0726 valid from 20. No D02 use.'
        cod=(('m02check.py',6,26),('m02check.py',60,66))
    elif tag=='UNIFIED':
        sig,j,c=stuff
        desc=f'G_M≤{c} exp(−{sig}L)';domain='All real L≥20.'
        deriv=f'Cells to 58, plateau plus decaying terms to {j}, decreasing scaled density tail thereafter.'
        comp='B0 bound .01370 at matching 1/8; D02 bounds .00141 at 1/8 and .270 at 5/32, crossing at 32 log(.270/.00141).'
        cod=(('m02check.py',6,17),('m02check.py',31,48),('m02check.py',67,69))
    else: raise ValueError(s)
    add(f'M2-numeric-{i}',M,('m02_result.txt',i),desc,domain,'Non-strict bound (checked with slack)',
        deriv,input=inp,compare=comp,cs=cod,rec=(('m02_result.txt',i),))
add('M2-finite-engine',M,('mertens02.md',38,40),'Extend exact interval sieve proof to N=2100000000 using proven gamma, M, B3 intervals and monotone normalized errors on clipped gaps.',
    'Real x in [40000000,2100000000]; terminal N composite.','Non-strict finite enclosures',
    'Proper arithmetic scales and signs, signed 128-bit headroom, least-prime marking, and both endpoints/jump sides checked. Infinite normalizations are reused from the old computation, with actual tails proved.',
    cs=(('finite02.cpp',9,54),('finite02.cpp',57,84),('finite02.cpp',99,153)),
    rec=(('finite02_result.txt',1,84),('finite_final.txt',15,17)),
    sl=['Dusart Thm.4.2 p.11 LF959–1010; Dusart Thms.5.6,5.7 pp.17–19 LF1476–1502,1552–1583.'])
for i,s in enumerate(lines('finite02_result.txt'),1):
    if 6<=i<=16:
        l,h,*v=s.split();dom=f'All real x in [{l},{h}].'
        add(f'M2-block-{l}',M,('finite02_result.txt',i),f'(L³E_1,L³E_P,L³E_Q,L²E_w)≤10^−4 times {v} componentwise.',dom,'Non-strict',
            'Scaled monotone signed errors between successive primes; evaluate clipped endpoints with outward integer balls.',
            cs=(('finite02.cpp',57,64),('finite02.cpp',99,123),('finite02.cpp',145,149)),rec=(('finite02_result.txt',i),),
            sl=['Dusart Thms.4.2,5.6,5.7: normalization tail and exact constant definitions; review.md §3.'])
    elif 17<=i<=84:
        _,col,val,_,last=s.split();c=int(col);v=int(val);x=int(last)+1
        # Every one of the new recorded constants is >= .0196.
        assert v>=196 and x>=40000000
        add(f'M2-margin-{col}-{val}',M,('finite02_result.txt',i),
            f'Column {col} ({["E_1","E_P","E_Q","E_w"][c]}) times L^{3 if c<3 else 2} ≤ {val}·10^−4.',
            f'All real x≥{x} via verified finite interval through 2100000000 and .0196 bridge from exp(21.45).','Non-strict',
            'The last conservative rejected endpoint is not an actual failure. Take its successor as the sufficient integer-valued real left endpoint and overlap the closed analytic ray.',
            cs=(('finite02.cpp',60,64),('finite02.cpp',109,122),('finite02.cpp',151,152)),rec=(('finite02_result.txt',i),('m02_result.txt',40)),
            sl=['Dusart Thm.4.2 p.11 and Thms.5.6/5.7 pp.17–19; analytic bridge ingredients in review.md §3.'])
for i,x,a,b,c in [(1,200000000,'.033','.035',None),(2,1122470708,'.0200','.0200',1124118894),(3,1123726104,'.0196','.0196',1126951622)]:
    add(f'M2-finite-ray-example-{i}',M,('mertens02.md',40),
        f'L³E_i≤{a} for i=1,P,Q from x={x}; L²E_w≤{b} from x={c or x}.',
        'Entire indicated real rays.', 'Non-strict',
        'Finite row/suffix of clipped interval maxima, then .0196 bridge on common domain.',
        cs=(('finite02.cpp',99,123),('m02check.py',60,66)),
        rec=(('finite02_result.txt',6,84),('m02_result.txt',40)))

# Explicit pointers for prose summaries, no double counting as new results.
summary_aliases=[
    {'source':loc('README.md',3,7),'readback':raw(loc('README.md',3,7)),'scope':'Summary of both active portfolios and verification trust.'},
    {'source':loc('ramanujan02.md',13,29),'readback':raw(loc('ramanujan02.md',13,29)),'scope':'Same ORDER, COEFFICIENT and RAY/WINDOW statements/items indexed individually.'},
    {'source':loc('mertens02.md',3,12),'readback':raw(loc('mertens02.md',3,12)),'scope':'Normalizations/retentions, unified power envelopes and matched example receipts.'},
    {'source':loc('D01_README.md',3,9),'readback':raw(loc('D01_README.md',3,9)),'scope':'Own retained proof summary, not a new assumption.'},
    {'source':loc('OWN_SOURCE_LOCATOR_CORRIGENDUM.json',1,36),'scope':'Only source pointer corrected; both versions bound.'}]
for f in ['gap_envelope.txt','gap_attempt.txt','gap_final.txt','gap_refined.txt']:
    for i,s in enumerate(lines(f),1):
        if s.startswith('FAIL'):
            trials.append({'source':loc(f,i),'readback':s,'classification':'Sufficient certificate failed only. '+('Replayed final method.' if f=='gap_envelope.txt' else 'Historical experiment, not a final proof or current-source transcript.')})
trials.append({'source':loc('ramanujan02.md',96),'classification':'Withdrawn fifth coefficient 15000, genuine counterexample supplied by audit.py; valid candidate refutation, not a failure of the retained theorem.'})
trust='supported_at_stated_trust_tier'
portfolioR=['R-sharp','R2-exact-profile','R-early-lower','R2-max','R-any-m','R2-model-B0','R2-model-D02','R2-model-dominance','R2-deep-dominance']+[
 c['claim_id'] for c in claims if c['claim_id'].startswith(('R2-window-','R2-order-','R2-growing-')) and c['M_status']==ok]
portfolioM=['M-pointwise','M2-envelope','M2-dominance','M2-coefficient','M-theta-envelope','M-W','M-CH80','M-bridge']+[
 c['claim_id'] for c in claims if c['claim_id'].startswith(('M2-numeric-','M2-block-','M2-margin-','M-sharp-','M-block-','M-margin-','M-osc-'))]
fams={R:dict(strongest_supported_portfolio=portfolioR,rejected_or_incomplete_claims=[],excluded_original_source_overstatement=['R-quoted-literal-PT'],
             remaining_assessment_work=[],summary='Active claims supported. Genuine D02 strength/onset gains via zero cap; retain early analytic windows, growing/fixed profiles, exact corrected real and integer sign onsets. Inherited integer result at literature trust.'),
      M:dict(strongest_supported_portfolio=portfolioM,rejected_or_incomplete_claims=[],remaining_assessment_work=[],
             summary='Active claims supported. D02 improves cap-driven power tails and matched target onsets. Input-independent exact finite and analytic joins plus four sharp real crossings are retained. Relative product and sum envelopes checked separately.')}

def save(n,obj): (d/n).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
assert len({c['claim_id'] for c in claims})==len(claims)
assert all((d/(n+'.exit')).read_text().strip()=='0' for n in ('replay01','replay02','audit','environment'))
# Share identical exact code excerpts across claim rows without losing source identities.
impl={}
for c in claims:
    for q in c['implemented_readbacks']:
        a=q['source']
        k=f"{a['file']}:{a['physical_LF']}-{a.get('end_physical_LF',a['physical_LF'])}"
        impl[k]=q['physical_readback']
        q.pop('physical_readback')
        q['physical_readback_key']=k
save('implementation_readbacks.json',impl)
save('review.json',dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=ix['candidate_id'],
 assessment_complete=True,all_claims_inventoried=True,
 reviewed_source_hashes={x['packet_name']:x['sha256'] for x in ix['candidate_files']},
 source_bibliography=bib,summary_aliases=summary_aliases,implementation_readbacks_file='implementation_readbacks.json',
 actual_effort='Exact casewise mathematical audit, original formula readback, both replays incl. finite computations; no claim of externally measured total token/wall usage.',
 verification_commands=[
  '/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out /work/review_exact',
  'cd /work/review_exact && /usr/bin/python3.10 -B replay.py',
  'cd /work/review_exact && /usr/bin/python3.10 -B replay02.py --finite',
  'cd /work/submission && /usr/bin/python3.10 -B audit.py /work/review_exact'],
 verification_evidence_file_sha256={x.name:hashlib.sha256(x.read_bytes()).hexdigest() for x in sorted(d.iterdir()) if x.suffix in ('.stdout','.stderr','.exit')},
 family_assessments=fams,claims=claims,unsuccessful_or_withdrawn_trials=trials,
 no_other_arm_or_ranking_seen=True,new_core_math_salvage_performed=False,original_candidate_bytes_changed=False))
save('STAGE_STATUS.json',dict(ready_for_review=True,families={f:dict(status=trust,claim_files=['review.md','review.json']) for f in fams},
                              serious_attempts_documented=True))
print(len(claims),'independently assessed rows;',len(trials),'trial entries')
