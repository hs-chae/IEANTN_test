"""Machine inventory from literal locked rows and D01 crosswalk identities."""
import re,json,hashlib
from fractions import Fraction as F
from pathlib import Path
p=Path('/work/review-input')
out=Path('/work/submission')
idx=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
by={d['original_name']:d for d in idx['candidate_files']}
papers=json.loads(Path('/task/SOURCE_INDEX.json').read_text())['sources']
def sha(x):return hashlib.sha256(x.read_bytes()).hexdigest()
def loc(file,a,z=None):
    d=by[file]
    assert 0<a<=(z or a)<=len((p/file).read_bytes().splitlines())+1,(file,a,z)
    return dict(file=file,packet_name=d['packet_name'],physical_LF=a,last_physical_LF=z or a,sha256=d['sha256'])
def lines(name):
    return list(enumerate((p/name).read_text().split('\n'),1))
for file,d in by.items():
    assert sha(p/file)==d['sha256']
for s in papers:
    for k in ('pdf','text'):
        assert sha(Path('/corpus/originals',s[k]))==s[k+'_sha256']

S='supported_at_stated_trust_tier'
W='equivalent_or_weaker'
B='baseline_retained'
BAD='false_with_specific_counterexample'
INC='incomplete_with_specific_missing_step'
V='Not checked; no Lean/Blueprint or source-first PV here.'
trust='Published premises + ordinary directed computation where indicated; see review.md.'
qsrc=[
 'OpenAIQRH PDF p.4 Thm.1.1; pp.84–85 Prop.11.3',
 'PlattTrudgianFiniteRH PDF p.2 Thm.1',
 'FKS PDF pp.4–5 Cor.2.3/(2.1)/Table 1; pp.7–8 Cor.2.9/(2.17) and Thm.3.2/(3.2); p.26 first-block Table 8',
 'Dusart2018 PDF pp.12–13 Prop.4.3/Cor.4.5; PT2021 p.2 (5)']
rsrc=qsrc+[
 'Dusart2018 PDF pp.13–15 §5.1/PV li and proof of Thm.5.1',
 'CH2 PDF p.3 Cor.1.2–1.3, p.35 Lemma 9.2, p.36 Cor.9.3 on large branch',
 'PlattTrudgianFiniteRH p.4 Cor.1 theta; PT2021 p.9 Lemma 6']
msrc=qsrc+[
 'Dusart2018 PDF p.11 Thm.4.2, pp.17–20 Thms.5.6,5.7,5.9',
 'CH2 PDF p.3 Cor.1.2–1.3, p.34 Prop.9.1, p.35 Lemma 9.2',
 'PlattTrudgianFiniteRH p.4 Cor.1 theta; PT2021 p.9 Lemma 6']
old0='B0 entails the disclosed D01 condition on x≥exp(200); same lawful consequence envelopes, no independent blind B0 run.'
d02where='D02 makes the Mellin tail holomorphic on Re(s)>27/32; clipping the shared cap and residual bins at b=27/32 changes the proof at v≥100.'
claims=[]
def add(cid,fam,f,a,z,statement,domain,strict,model,refs=(),ass='B0',compare=None,status=S,gap=None,keep=(),where=None,other=(),num=None,sl=None):
    source=rsrc if fam=='Ramanujan' else msrc
    use=ass in ('B2','paired','strip-conditional')
    claims.append(dict(
        claim_id=cid,family=fam,written_source=loc(f,a,z),other_written_sources=[loc(*t) for t in other],
        implemented_formula_readbacks=[loc(*t) for t in refs],
        exact_statement=statement,full_domain=domain,strictness=strict,real_or_integer='real except explicitly finite integer counting or discrete parameters',
        assumptions={'B0':'B0 only, seven pinned originals at stated hypotheses.',
                     'B2':'B0 plus exact D02; see premise_summary.',
                     'paired':'Paired B0 / B0+D02; see premise_summary.',
                     'strip-conditional':'Specified strip only as deduced from B0 or B2; boundary not excluded.'}[ass],
        baseline_comparison='See propagation.matched_comparison.',
        source_locators=sl or ([source[2], ('See source_locator_groups.R and review §§1–2.' if fam=='Ramanujan' else 'See source_locator_groups.M and review §§1,3.')]),derivation_check=model,
        numerical_obligations=num or ('See cited cells/tests and their entire domain in review.md.' if evidence else 'Analytic, or published result at source trust; no new arithmetic required.'),
        actual_verification_receipts=evidence.copy(),retained_valid_branches=list(keep),M_status=status,precise_gap_or_counterexample=gap,
        propagation=dict(input_used=use,where_it_changes_proof=where or (d02where if use else 'No additional input enters this branch.'),matched_comparison=compare or old0),
        V_status=V,remaining_trust='See trust_tier.'))
new='evidence_new.json:'
old='evidence_old.json:'
aux='evidence_aux.json:'
def ev(*spec):
    global evidence
    evidence=list(spec)
oldmaps={}
def old_sources(r):
    q=r['source_locators']
    key=next((k for k,v in oldmaps.items() if v==q),None)
    if key is None:
        key='prior-interface-'+str(len(oldmaps)+1)
        oldmaps[key]=q
    return ['See source_locator_groups.'+key+'; source verification is in review.md.']
history=json.loads((p/'D01_M_REVIEW_review.json').read_text())
floor=json.loads((p/'OWN_D01_VALIDATED_FLOOR.json').read_text())
ids={x for group in floor['validated_claim_ids_by_family'].values() for x in group}
assert len(ids)==436==len(history['claims'])-2
proofnames={
 'psi.md':'§1: reciprocal-height partial summation, .8 split, 92 derivative, cutoff/domain and v=200 monotonicity.',
 'candidate.md':'§1: compared disclosed coefficient v²/64>=625 with the verified B0 .020.',
 'ramanujan.md':'§2: corrected integer/real endpoint and independent PV, signed-history and shifted polynomial/ray checks.',
 'repair.md':'§1–3: .78 continuous cap, per-cutoff rates, combined mode, shifted error and finite bridge checks.',
 'mertens.md':'§3: exact normalizations, signed tails, event-state/analytic joins, and phase/limits as separately inventoried.',
 'repair.out':'§2 or §3: n=32 reserve at tested endpoint, or decreasing normalized coefficient test; full-real ray.',
 'mertens.out':'§3: 250-million event-state and .10 analytic-tail checks; flag is not the join.',
 'm_poly_2b.out':'§3: 2-billion event-state and .063 analytic-tail checks.',
 'repair_mpoly.out':'§3: 4-billion event-state and .0391 analytic-tail checks; .047 uses join, not flag.',
 'prior_mertens.md':'§3: exact limit recomputed from written/implemented multipliers, withdrawn historical statement only.'}
proofev={
 'psi.md':[old+'ranu',old+'mcert',aux+'aux'],
 'candidate.md':[old+'ranu',old+'mcert'],
 'ramanujan.md':[old+'endpoint',old+'ranu',old+'higher',aux+'old_aux'],
 'repair.md':[old+'repair',aux+'old_aux'],
 'mertens.md':[old+'mcert','evidence_scan_mertens.json:mertens','evidence_scan_mertens.json:witness',aux+'old_aux'],
 'repair.out':[old+'repair'],
 'mertens.out':[old+'mcert','evidence_scan_mertens.json:mertens'],
 'm_poly_2b.out':[old+'m_poly_2b','evidence_scan_m_poly_2b.json:m_poly_2b'],
 'repair_mpoly.out':[old+'repair_mpoly','evidence_scan_repair_mpoly.json:repair_mpoly'],
 'prior_mertens.md':[old+'mcert',aux+'aux']}
def remap(d):
    f=d['file']
    if f=='candidate.md': f='D01_candidate.md'
    q=loc(f,d['physical_LF'],d.get('last_physical_LF'))
    assert q['sha256']==d['sha256'],(f,d)
    return q
for r in history['claims']:
    w=r['written_source'];f=w['file'];cid=r['claim_id']
    ev(*proofev[f])
    status=(B if cid in ('R-original-DP','R-original-PT','M-Dusart-D1','M-Dusart-D2','M-Dusart-P','M-Dusart-Q')
            else W if re.match(r'M-poly-2b-(18|19|20|21|22|23|24)-',cid)
            else BAD if cid not in ids else S)
    gap,ret=None,()
    if cid=='R-published-literal-real':
        gap='Quoted original, not a current assertion: at x=38358837682+.21792 the directed quotient-count evaluation gives R<0.'
        ret=('R-exact-real','R-integer')
    elif cid=='M-old-exact-limit-archived':
        gap='Withdrawn historical assertion: the coefficient has the unique exact limit (1+2/(3e12))*.010445, exceeding .010445 by the exact positive quantity 2*.010445/(3e12).'
        ret=('M-old-exact-limit-corrected','M-refined-transfer')
    elif cid=='M-signed-theta':
        ret=('M-signed-D1D2','M-CH2-low-component')
    actual=remap(w)
    domain=r['full_domain']
    model=proofnames[f]
    if cid=='M-signed-theta':
        domain+='; only valid source branches, exclude literal near-one CH2 Cor.9.3 (9.3).'
        model+=' See separate rejected literal near-one clause M-CH2-low-component; no effect on any certified rays.'
    if f in ('mertens.out','m_poly_2b.out','repair_mpoly.out'):
        line=dict(lines(f))[w['physical_LF']]
        m=re.match(r'(\d+)/(\d+): joins (\d+) (\d+) (\d+);',line)
        assert m
        den,c0,d1,pro,d2=m.groups()
        assert int(den)>0 and int(c0)>0
        n={'D1':d1,'P':pro,'Q':pro,'D2':d2}[cid.split('-')[-1]]
        assert n in domain
    add(cid,r['family'],actual['file'],actual['physical_LF'],actual['last_physical_LF'],
        r['exact_statement'],domain,r['strictness'],model,status=status,gap=gap,keep=ret,
        compare=('Same exact coefficient and onset as rechecked longer scan.' if status==W else old0),
        sl=old_sources(r))
    claims[-1].update(other_written_sources=[remap(x) for x in r['other_written_sources']],
        implemented_formula_readbacks=[remap(x) for x in r['implemented_formula_readbacks']],
        scope=('quoted_source' if cid=='R-published-literal-real' else 'withdrawn_history' if cid=='M-old-exact-limit-archived' else 'active_retained'),
        real_or_integer=r['real_or_integer'])
    if status==B:
        claims[-1]['remaining_trust']='Identified named original at published trust; finite Mertens onsets also reproduced or improved at ordinary directed trust.'

ev(aux+'aux','evidence_source.json:source_pdf')
add('M-CH2-low-component','Mertens','mertens.md',78,78,
    'Optional literal (9.3) branch: |ψ(x)−x|≤sqrt(x)L²/(8π) whenever x>1 and 10^7≤T=2π²sqrt(x)/L≤H.',
    'Literal printed domain; failure on near-one component','≤','§3: verify counterexample and source proof hypothesis.',
    status=BAD,gap='At x=1.0000001, T lies between 10^7 and 3e12 but ψ=0 and the claimed upper bound is below 1e-13. Cor.1.2 needed x>max(T,10^9).',
    keep=('M-signed-theta','M-finite-pointwise'),other=(('mertens2.md',47,49),),sl=['CH2 PDF p.36 Cor.9.3 (9.3), (9.4), LF5336–5363; p.3 Cor.1.2 LF193–222.'])
claims[-1]['scope']='rejected_literal_optional_branch_only'
ev()
for fam,prefix in [('Ramanujan','R'),('Mertens','M')]:
    add(prefix+'-D02-strip',fam,'spectral2.md',6,14,
        'Exact D02 permits analytic continuation of −ζ′/ζ to Re s>27/32 away from 1. Every nontrivial zero has Re ρ≤27/32, with no boundary exclusion.',
        'All nontrivial zeta zeros; D02 enters only for x≥exp(200)','closed β upper bound; excluded half-plane open',
        '§1: Euler product, locally normal Mellin integral, meromorphic identity and nonzero log-derivative residues.',
        ass='B2',compare='B0 b=7/8; B2 b=27/32; B0+D01 is B0 in logical strength for this comparison.',
        other=(('candidate.md',5,5),))
ev(new+'spectral',new+'refine2',aux+'aux')
for fam,prefix in [('Ramanujan','R'),('Mertens','M')]:
    for key,file,l,u,stmt,domain,refs,strict in [
        ('cap','spectral2.md',18,46,'First-block FKS density and layer cap (1)–(2) with coarse limits .0104436237 (B0), .146555285475 (B2); strict physical high-mode reduction on clipping.','s in [.70,b], y≥log H where a bound uses density; v≥100 for compared applications.',(('spectral.py',4,69),),'non-strict upper, strict comparison'),
        ('remainder','spectral2.md',50,81,'Four all-real explicit-formula residuals, |ψ(e^v)/e^v−1−V(v)|≤e^(−δv) min_cut sum_i d_i, and listed decay/past growth rates. Each term covers its full bin and omitted β boundary.','real v≥100; corresponding e^v≥121 for signed powers.',(('spectral.py',74,120),('spectral.py',130,144)),'≤'),
        ('new-cap-exact','spectral2.md',83,87,'Running infimum of exact integral density bounds, with K in [.010443618317,.010443618318] and [.146288736863,.146288736866]; replacing tangent bin integral also improves the majorants.','v≥100 in applications, entire density and cutoff domains.',(('refine2.py',4,9),('refine2.py',34,43)),'non-strict bounds; strict improvement where stated for bounding functions'),
        ('new-cap-fine','spectral2.md',85,85,'Taylor degree 12, ≤.001 subintervals, b2 node and 10^−12 upward rounding give fine cap everywhere no larger than coarse. K0=.010443618318 and K2=.146288736869.','v≥100 for uses; cap s∈[.70,b].',(('refine2.py',11,32),),'≤ and exact limits'),
        ('clipped-old','spectral2.md',89,89,'Clipped inherited .78 spectral variant at b2 retains the valid original tail/past kernels; old domains preserved and bounding functions improved.','v≥100, R both arguments must qualify.',(('repair_cert.py',42,100),('spectral.py',74,96)),'≤; comparison of bounding functions only')]:
        add(prefix+'-D02-'+key,fam,file,l,u,stmt,domain,strict,'§1: checked cap and signed transfer interfaces on all domains, not interpolation of arithmetic observations.',
            refs,ass='paired',compare='Fixed kernel and matching cutoffs/caps; compare in physical units at same arguments. Other lawful minima and maxima retained.')
ev(new+'spectral',aux+'aux')
add('R-D02-pi-profile','Ramanujan','ramanujan2.md',43,59,
    'PV normalized r bounded by e^(−δv)Q_b(v) with (3); signed positive side may subtract .9999e^(−v(1/2−δ)) inside coefficient. Q_b decreases to K_b.',
    'real v≥100; signed subtraction on same domain','≤ and equal limit',
    '§2: phase past integration, rates, powers and old history. In the positive-side bound drop the nonpositive past prime-power integral.',
    (('spectral.py',101,120),('cert.py',93,117)),ass='paired',
    compare='Same physical kernels and actual v for B0/B2; intersect old absolute and signed errors on each argument.')
for key,stmt,l,u,strict in [
    ('rational','Strict gap profile (4) using rational factorial barriers and separate signed r_±.',61,67,'>'),
    ('polynomial','Strict P_N minus shifted error profile, with exact C_i through N and positive omitted terms.',69,74,'>'),
    ('exact-li','Exact PV endpoints substituted for A_N,U_N in (4) allow a non-strict lower profile.',61,67,'≥')]:
    ev(new+'higher2',old+'ranu',new+'order192')
    add('R-D02-'+key,'Ramanujan','ramanujan2.md',l,u,stmt,
        'real L with each L and L−1 in its error domain, and v≥certified anchor at both arguments for barrier branches',
        strict,'§2: exact squaring, ODE barriers at the anchor and positive binomial expansion.',
        (('higher2.py',9,34),('higher2.py',42,54)),ass='paired',
        compare='Apply new and old errors on exact domains; retain every higher lower profile at a given x.')
ev(new+'higher2',new+'order192',new+'mid2',old+'ranu')
add('R-all-orders-anchors','Ramanujan','ramanujan2.md',69,80,
    'Strict factorial brackets on tested anchor rays; eventual strict brackets and sufficient strict T_{k,C_k} ray for every fixed k, without a numerical onset beyond the computed orders.',
    'Real v≥2N+5 for tested anchors, L≥2N+6 when used at L−1; sufficiently large real L for uncomputed fixed orders.',
    'strict','§2: residual signs, PV bracket, and exponential convolution split for eventual fixed-order anchors.',
    (('higher2.py',9,34),('order192.py',13,22),('mid2.py',50,57)),ass='paired')
Rcompare='At fixed k and c, B0 versus B2 sufficient real onsets; keep both repeated bounds and the earlier/stronger tradeoffs. No claim of least onset.'
rrefs=(('higher2.py',13,34),('higher2.py',37,80),('spectral.py',101,120))
ev(new+'higher2')
for i,z in lines('higher2.out'):
    if z.startswith('frozen Q'):
        add('R-frozen-Q-'+str(i),'Ramanujan','higher2.out',i,i,z,
            'real v≥100, each listed coefficient usable from its own v onward','≤',
            '§2: normalized Q_b decreases, and rounded base numbers cover the entire intervals.',
            (('higher2.py',37,47),('spectral.py',101,120)),ass='B2' if '27/32' in z else 'B0',compare=Rcompare,
            other=(('ramanujan2.md',75,80),))
    m=re.match(r'(sixth coefficient|exact order|half 128) and a,N,j (7/8|27/32) (\S+) (\d+) (\d+) (\d+)',z)
    if not m:continue
    kind,b,v,a,N,j=m.groups()
    k,c=(6,v) if kind=='sixth coefficient' else (int(v),('C_128/2' if kind=='half 128' else f'C_{v}'))
    add(f'R-higher2-{i}','Ramanujan','higher2.out',i,i,
        f'G(L)>T_{{{k},{c}}}(L) using N={N}, j={j}.',f'real L≥{a} (inclusive)','>',
        '§2: strict directed endpoint, decreasing shifted loss, increasing reserve.',rrefs,ass='B2' if b=='27/32' else 'B0',
        compare=Rcompare,other=(('ramanujan2.md',24,37),))
ev(new+'compare2',aux+'aux')
for i,z in lines('compare2.out'):
    if z.startswith('paired margin'):
        add(f'R-P48-match-{i}','Ramanujan','compare2.out',i,i,z,
            'Two bounding functions at the stated real L (not assertions of crossover from samples).','enclosed lower envelope values',
            '§2: exact P48, separate arguments, min of absolute error envelopes and rounding.',
            (('compare2.py',8,27),('joins2.py',8,12)),ass='paired',
            compare='Same P48, same argument; B2 can lower the cost but plateau or old bounds can tie.',
            other=(('ramanujan2.md',39,39),))
    if z.startswith('rational k'):
        add(f'R-rational-match-{i}','Ramanujan','compare2.out',i,i,z,
            'real L≥ each exact Fraction onset; coefficient is C_k if shown as dash.','strict >T_{k,c}',
            '§2: exact hundredth-onset retest using the same frozen coefficient and ray monotonicity.',rrefs+(('compare2.py',29,49),),
            ass='paired',compare=Rcompare,other=(('ramanujan2.md',24,37),))
ev(new+'order192')
for i,z in lines('order192.out'):
    m=re.fullmatch(r'order (\d+) (exact|half) B0 and D02 hundredths (\d+) (\d+)',z)
    if not m:continue
    k,c,a,b=m.groups()
    add(f'R-order192-{i}','Ramanujan','order192.out',i,i,
        f'G>T_{{{k},'+('C_k/2' if c=='half' else 'C_k')+'} with N=192, j=min(k+1,192).',
        f'B0 real L≥{F(a)/100}; B2 real L≥{F(b)/100}.','strict >',
        '§2: anchor 389, high-precision outward sign comparisons and monotone full-ray proof.',
        rrefs+(('order192.py',3,22),),ass='paired',compare=Rcompare,other=(('ramanujan2.md',24,24),))
ev(new+'joins2',old+'repair',old+'ranu')
for i,(a,c,b,j) in enumerate([('47.15','0','B0','47.17 (older bound)'),('47.6','8','B0','191'),
    ('48','40','B2','166'),('49.2','80','B2','170'),('49.6','80.25','B2','171')],16):
    add(f'R-connected-{i}','Ramanujan','ramanujan2.md',i,i,f'G>1+14/L+{c}/L².',
        f'Real L≥{a}, join at {j}.','strict >','§2: early finite cells, midrange shifted cells to analytic cutoff, and overlapping strict tail or retained branch.',
        (('early2.py',42,79),('joins2.py',8,63),('higher2.py',42,54)),ass=b,
        compare='B0 has connected coefficients 0 and 8, also fixed-c tail onsets 192,197 for c=40,80 in higher2.out. B2 extends the connected stronger reserve, not the last sign crossing.',
        other=(('candidate.md',9,9),))
earlyouts=[('36.688','.001'),('36.692','.003'),('36.694','.004'),('36.712','.013'),('36.715','.014'),('36.772','.040'),('36.780','.043'),('36.863','.080'),('36.98','.137'),('37.02','.155'),('37.05','.163'),('42.615','1')]
for i,(a,c) in enumerate(earlyouts,92):
    add(f'R-early-ray-{i}','Ramanujan','ramanujan2.md',i,i,f'G>{c}.',f'real L≥{a}', 'strict >',
        '§2: full-cell check with shifted error, overlap with stronger new/inherited margins as in table.',
        (('early2.py',42,79),('joins2.py',45,56)),compare='Input-independent earlier onset at same positive margin; does not change exact last failure.')
for i,(a,z,c) in enumerate([('39.46','39.47','.885'),('48','55.5','1.305'),('49','54','1.31'),('50','52','1.32'),
        ('54','124','T_{6,C_6}(L)'),('58','88','T_{7,C_7}(L)')],1):
    add(f'R-finite-new-{i}','Ramanujan','ramanujan2.md',105,105,f'G>{c}.',f'real L in [{a},{z}]','strict >',
        '§2: full early cells and, where needed, grid past 58. Not advertised as unbounded.',
        (('early2.py',42,79),('joins2.py',21,63)),compare='Input-independent finite tradeoff; no whole-ray extension across unchecked log interval.')
ev(new+'mid2')
for i,(a,c) in enumerate(zip(('28','28.2','28.5','29','29.5','30','30.6','30.9'),('.01','.12','.28','.50','.69','.85','1','1.06')),1):
    add(f'R-mid-{i}','Ramanujan','ramanujan2.md',105,105,f'G>{c}.',f'real L∈[{a},30.93]','strict >',
        '§2: actual N=10 anchor, prime-count history at 1e4, sign at x and CH2 signed bounds at x/e.',
        (('mid2.py',8,57),),compare='Input independent; no quantitative connected ray claimed across the subsequent gap.')
ev(new+'joins2')
add('R-closed-joins-dependencies','Ramanujan','ramanujan2.md',84,86,
    'All closed finite cells in joins2.out, including two-sided [39.47,40] with G>.163, and v≥100 shortened plateau bound for both shifted arguments when available.',
    'Actual logged intervals and endpoints exactly as in joins2.out; terminal ray checks at 166,170,171,191.',
    'strict interval results','§2: eligible branch on full cells; interval Horner for the whole polynomial, no discarded failed cells.',
    (('early2.py',7,79),('joins2.py',8,63)),ass='paired',compare='Early portions B0; B2 enters only at the late join via spectral r.',
    other=(('joins2.out',1,29),))
ev(new+'spectral')
add('R-slope-necessity','Ramanujan','ramanujan2.md',109,109,
    'A two-sided o(L⁴e^(−δL)) remainder in the normalized Li-gap approximation would exclude boundary zeros at Re ρ=b. No one-sided impossibility claimed.',
    'as real L→∞; conditional on proposed remainder','necessary implication',
    '§2 + §3: normalized contracting r recurrence, inverse partial summation and Abelian pole test.',
    (('spectral.py',101,120),),ass='strip-conditional',compare='B2 changes the examined slope from 1/8 to 5/32; neither closes the boundary.')
ev(new+'spectral',new+'m2',new+'extra2')
for key,l,u,stmt,domain,strict in [
    ('weighted-profile',51,69,'Endpoint-minus-tail from ψ to S,Φ using cancellation of ρ; add separate B,C,C−J to get the two sums and normalized log product.','real L≥100 for spectral expansions; B^+ from x≥121; underlying sums at all x>1.','non-strict'),
    ('pointwise-sign',47,49,'Intersect new spectral ψ/θ signed envelopes with all valid older ones and direct D02 only at v≥200; use separate exact e^{±Z} envelopes.','real x>1 using applicable branches and the correctly restricted CH2 sources','non-strict bounds'),
    ('normalized-c',64,71,'Y_i, c_i and c_1/(1−z) for sums and relative products; z<1; monotone; limits K_b (coarse/fine/integral separately).','real L≥100','≤ and exact limits of bounds'),
    ('hybrid',75,89,'Damping in tail integral of S, at most 𝒯_b(V)/V², and intermediate hybrid D2≤A+B^+, L·max(|D1|,|Z|)≤A(2−L/V)+L𝒯/V²+B^+ with pointwise/signed alternatives.','real 100≤L≤V for stated hybrids, V≥100; forward bound for all V≥100','absolute non-strict bounds'),
    ('slope-necessity',103,107,'o(e^(−δL)) for D2 or o(e^(−δL)/L) for any other target necessarily excludes zeros at Re ρ=b.','as real L→∞, under the proposed improvement','necessary implication')]:
    add('M-D02-'+key,'Mertens','mertens2.md',l,u,stmt,domain,strict,
        '§3: preserved normalizations, phase/Rate integration, inverse signed log transformations, positivity and monotonicity.',
        (('spectral.py',101,128),('m2.py',5,83)),ass='paired',
        compare='B0/B2 physical bound comparisons at matched arguments through the improved strip and tails, with older valid branches retained.')
forms={'D2':'|D2|','D1':'|D1|','P':'|exp(−Z)−1|','Q':'|exp(Z)−1|'}
def mcoef(root,f,line,last,a,c,sh,ass,refs,cmp,oth=(),strict='<'):
    for y,label in forms.items():
        expr=sh[0] if y=='D2' else sh[1]
        add(f'{root}-{y}','Mertens',f,line,last,f'{label} {strict} {c}{expr}.',a,strict,
            '§3: applicable finite bounds and exact overlap plus monotone analytic tails, correctly converting signed log products.',
            refs,ass=ass,compare=cmp,other=oth)
mr=(('spectral.py',98,128),('m2.py',23,83))
cmat='Same shape and threshold comparison between B0/B2 where stated; if shapes differ use rescaling and monotone maxima. Retain all lower-coefficient/later-onset tradeoffs.'
ev(new+'m2',new+'extra2','evidence_scan_mertens.json:mertens')
for i,a,b,c in [(17,'14','B0','.018865'),(18,'14','B2','.0083')]:
    mcoef('M-connected-'+str(i),'mertens2.md',i,i,'real L≥'+a,c,(' exp(−L/8)',' exp(−L/8)/L'),b,mr+(('extra2.py',3,10),),cmat)
mcoef('M-connected-B0-coarse','m2.out',2,2,'real L≥14','.01890',(' exp(−L/8)',' exp(−L/8)/L'),'B0',mr,cmat)
ev(new+'m2',new+'extra2',aux+'aux')
for j,(a,c) in enumerate(zip((170,175,180,190,200,250,300,500),
    ('.00145','.00120','.00100','.00070','.00049','.000090','.000018','.000000030')),16):
    mcoef(f'M-same-slope-{j}','m2.out',j,j,f'real L≥{a}',c,(' exp(−L/8)',' exp(−L/8)/L'),'B2',
         mr+(('m2.py',150,157),),cmat,(('mertens2.md',19 if j<20 else 20,19 if j<20 else 20),))
for file,line0,job,seq in [('m2.out',24,'m2',[(172,'.29'),(205,'.25'),(316,'.2'),(526,'.175'),(4048,'.15'),(31348,'.147')]),
    ('extra2.out',10,'extra2',[(171,'.290'),(204,'.25'),(314,'.20'),(519,'.175'),(3649,'.15'),(18933,'.147'),(63740,'.1465')])]:
    ev(new+job)
    for j,(a,c) in enumerate(seq,line0):
        mcoef(f'M-fast-{job}-{j}',file,j,j,f'real L≥{a}',c,(' exp(−5L/32)',' exp(−5L/32)/L'),'B2',
            mr+((('extra2.py',3,25) if job=='extra2' else ('m2.py',159,167)),),cmat,(('mertens2.md',21,24),))
ev(new+'m2')
powrows=[(3,61,None,'.0000051'),(4,'57.6','.00134','.000851'),(5,55,'.253','.144'),(6,52,'48','24.3')]
for i,(m,a,c0,c2) in enumerate(powrows,39):
    for b,c in [('B0',c0),('B2',c2)]:
        if c is None:continue
        mcoef(f'M-invlog-{m}-{b}','mertens2.md',i,i,f'real L≥{a}',c,(f'/L^{m}',f'/L^{m+1}'),b,mr,cmat)
ev(new+'m2',new+'extra2',aux+'aux')
mcoef('M-extra-log-200','mertens2.md',45,45,'real L≥200','.098',(' exp(−L/8)/L',' exp(−L/8)/L²'),'B2',
    (('extra2.py',21,25),('m2.py',150,157)),cmat)
add('M-continuous-m','Mertens','mertens2.md',44,45,
    'Fast coefficient c at a implies matched slope 1/8 with m extra log powers and coefficient c·u^m e^(−u/32), u=max(a,32m), for every m≥0.',
    'real L≥a>0 with fast branch at a and arbitrary real m≥0','inherits original bound strictness',
    '§3: compare the scaled ratio at the exact maximum by derivative, no grid.',ass='B2',compare=cmat)
add('M-factor-20','Mertens','mertens2.md',45,45,
    'At slope 1/8, .00049 branch beats all reported B0 absolute spectral coefficient functions by >20 and is stronger than the rounded plateau and polynomial estimates.',
    'real L≥200','strict comparisons of bounds',
    '§3: compare to limiting K for all spectral functions; decreasing L² exp(−L/8) and exp(−L/8) for other bounds.',
    (('m2.py',150,157),('extra2.py',21,25)),ass='B2',compare=cmat)
for i,(y,co,fi) in enumerate([('D1','115.9567,115.9568','115.9899,115.9900'),('D2','199.5221,199.5222','199.5729,199.5730'),
    ('P','115.2993,115.2994','115.3334,115.3335'),('Q','115.8036,115.8037','115.8357,115.8358')],28):
    for c,z in [('.29446',co),('.29389',fi)]:
        ev(new+('m2' if c=='.29446' else 'extra2'),new+'normalize_replay','evidence_scan_mertens.json:mertens')
        add(f'M-small-root-{c}-{y}','Mertens','mertens2.md',i,i,
            f'{forms[y]}≤{c} exp(−5L/32)'+('' if y=='D2' else '/L')+
            f' on the final real ray starting at unique equality root in ({z}); strict after, strict violation immediately before.',
            f'real x≥root in ({z}); magnitudes at post-jump states',
            '≤ at root and > left (violation); strict < after',
            '§3: prime cells to 22030; last flagged cell frozen; signed derivative negative, both endpoints bracket; then checked analytic overlaps.',
            (('m2.py',23,64),('m2.py',85,148),('extra2.py',3,10)),ass='B2',compare='For fixed slope, earlier coarse roots vs smaller coefficient on common domain; D02 enters in tail, not the small root computation.',other=(('candidate.md',10,10),))
ev(new+'spectral')
for i,z in lines('spectral.out'):
    m=re.fullmatch(r'M/pi paired: v, c0, r0, c2, r2 (\d+) (\S+) (\S+) (\S+) (\S+)',z)
    if not m:continue
    a,c0,r0,c2,r2=m.groups()
    for b,c,r,d in [('B0',c0,r0,'1/8'),('B2',c2,r2,'5/32')]:
        mcoef(f'M-spectral-rounded-{i}-{b}','spectral.out',i,i,f'real L≥{a}',c,(f' exp(−({d})L)',f' exp(−({d})L)/L'),b,
            (('spectral.py',101,154),),cmat)
        add(f'R-spectral-rounded-{i}-{b}','Ramanujan','spectral.out',i,i,
            f'|r(v)|≤{r} exp(−({d})v), in the PV normalization.',
            f'real v≥{a}; at shifted argument must separately satisfy v≥{a}.','≤',
            '§1–2: frozen upper Q coefficient and all-ray monotonicity.',
            (('spectral.py',101,154),),ass=b,compare=Rcompare)
ev(new+'lowpoly2','evidence_scan_lowpoly2.json:lowpoly2')
for i,c,n1,n2 in [(7,'.0378',187513357,190405273),(8,'.0380',187511879,190400939),(9,'.0381',187511393,190400827),
    (10,'.0382',187510369,189449081),(11,'.0383',187510327,189448933),(12,'.0385',187499419,189448201),(13,'.0390',180639383,188200153)]:
    for y,label in forms.items():
        po=2 if y=='D2' else 3
        a=n2 if y=='D2' else n1
        add(f'M-lowpoly2-{i}-{y}','Mertens','lowpoly2.md',i,i,f'{label}≤{c}/L^{po}.',
            f'real x≥{a} inclusive','≤',
            '§3: directed pre/post cells through 4e9 and signed analytic joins from L=22.109.',
            (('lowpoly2.cc',41,104),('lowpoly2.py',5,67)),compare='Input-independent tradeoff versus inherited .0391 and larger coefficients.',
            other=(('lowpoly2_scan.out',i+7,i+7),))
for y,label in forms.items():
    add(f'M-.0375-finite-{y}','Mertens','lowpoly2.md',15,19,f'{label}≤.0375/L^{2 if y=="D2" else 3} only on the verified scan interval.',
        f'real x in [{190409327 if y=="D2" else 187523779},4000000000]',
        '≤','§3: finite scan succeeds; first analytic sufficient check fails, so no extrapolation.',
        (('lowpoly2.cc',41,104),('lowpoly2.py',60,67)),
        compare='Only finite tradeoff (no whole-ray .0375 bound claimed).',
        other=(('lowpoly2_scan.out',13,13),))
# Preserve exact source row boundaries in machine-readable form, no new arithmetic.
assert len({r['claim_id'] for r in claims})==len(claims)
def family(f):
    return dict(strongest_supported_portfolio=[r['claim_id'] for r in claims if r['family']==f and r['M_status'] in (S,B,W)],
        rejected_or_incomplete_claims=[r['claim_id'] for r in claims if r['family']==f and r['M_status'] in (BAD,INC)],
        remaining_assessment_work=[],
        factual_summary=('Both branches required for the real endpoint and all new B0/B2 Taylor and finite-join profiles are checked. The near-left quoted PT source assertion is not used.' if f=='Ramanujan'
                         else 'All numerical whole rays, separate relative products, normalizations, signed transfers, eight new and four old exact onsets and polynomial/spectral inequalities checked. Reject the literal optional CH2 near-1 source clause; the withdrawn historical limit is excluded.'))
gs=['new','old','aux','source','scan_mertens','scan_m_poly_2b','scan_repair_mpoly','scan_lowpoly2']
for g in gs:
    rs=json.loads((out/f'evidence_{g}.json').read_text())
    assert all(v['status']==0 for v in rs.values())
    assert all(v.get('identical',True) or j=='ranu' for j,v in rs.items())
    if g=='new':
        assert len(rs)==11 and 'not certified .0375' in rs['lowpoly2']['stdout'] and rs['lowpoly2']['stdout'].count('New Mertens all-ray polynomial join:')==7
    if g=='old':
        assert len(rs)==7 and rs['ranu']['stdout'].splitlines()[:-1]==(p/'ranu.out').read_text().splitlines()[:-1]
    if g.startswith('scan_'):
        assert g.removeprefix('scan_') in rs and 'binary_sha256' in rs[g.removeprefix('scan_')]
result=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=idx['candidate_id'],input_stage='D02',
    assessment_complete=True,all_claims_inventoried=True,
    reviewed_source_hashes=idx['candidate_files'],source_bibliography=papers,
    premise_summary='B0 is the seven pinned originals at their exact published hypotheses/trust, including QRH. D02: all real x>=exp(200), |ψ(x)−x|<=x^(27/32)L²/64. No full RH.',
    actual_effort_and_verification_commands=[
        'Non-login /bin/bash; /usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out /work/review-input',
        *[f'/usr/bin/python3.10 -B /work/submission/replay.py {g}: see evidence_{g}.json' for g in gs],
        'Manually read original pinned PDF extractions; audited the PDF streams for CH2/FKS typography; checked all digests.',
        'Independent symbolic checks and exact row-by-row certificate readback, see review.md and checks.py.'
    ],
    family_assessments={f:family(f) for f in ('Ramanujan','Mertens')},claims=claims,
    own_history_disclosure='OWN_ONLY; crosswalk identifiers and exact claim metadata read from supplied own history; no previous status accepted as mathematical premise.',
    no_other_arm_or_ranking_seen=True,new_core_math_salvage_performed=False,original_candidate_bytes_changed=False,
    formal_status=V,trust_tier=trust,source_locator_groups={'R':rsrc,'M':msrc,**oldmaps})
# Compact rows for portability, readable individual records.
with (out/'review.json').open('w') as g:
    result.pop('claims')
    for c in claims:
        # The packet names of executable links are redundantly in reviewed_source_hashes.
        for q in c['implemented_formula_readbacks']:
            q.pop('packet_name',None)
    g.write(json.dumps(result,indent=2,ensure_ascii=False)[:-2]+',\n  "claims":[\n')
    g.write(',\n'.join('    '+json.dumps(c,ensure_ascii=False,separators=(',',':')) for c in claims))
    g.write('\n  ]\n}\n')
assert json.loads((out/'review.json').read_text())['assessment_complete']
print('claims',len(claims),'bytes', (out/'review.json').stat().st_size)
