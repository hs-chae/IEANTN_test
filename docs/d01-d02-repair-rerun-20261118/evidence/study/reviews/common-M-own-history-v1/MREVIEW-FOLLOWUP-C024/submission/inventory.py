"""Build the review registry; historical statement metadata is not evidence.
Run in /work/submission after the receipt files exist.
"""
import hashlib, json, re
from pathlib import Path
from fractions import Fraction as F
p=Path('/work/reviewer_exact')
def j(path):return json.loads(Path(path).read_text())
idx=j('/task/CANDIDATE_INDEX.json')
rows=idx['candidate_files']
byname={r['original_name']:r for r in rows}
def loc(n,a,z=None,formula=None):
    r=byname[n]
    assert 1<=a<=(z or a)<=len((p/n).read_bytes().split(b'\n'))
    d=dict(file=r['packet_name'],original_basename=n,physical_LF=a,sha256=r['sha256'])
    if z:d['physical_LF_last']=z
    if formula:d['formula']=formula
    aliases=[e['packet_name'] for e in rows if e['sha256']==r['sha256'] and e['packet_name']!=r['packet_name']]
    if aliases:d['identical_packet_aliases']=aliases
    return d
status='supported_at_stated_trust_tier'
V='Written analysis plus ordinary directed arithmetic where indicated; no Lean/Blueprint build, kernel-only proof or source-first PV.'
trust='Stipulated named original results in lawful domains; ordinary arithmetic/compiler and implementation correctness for executed certificates.'
Rsrc='OpenAIQRH Thm 1.1 p.4 for B0; PT2021 Lemma 2 p.4; FiniteRH Thm 1 p.2; FKS §2.1, 3.2 and Cor.2.9/Table 8 pp.7–8,26; Dusart (2.1), Thm 2.3, Thm 4.2 proof and Prop.4.3 pp.3–5,11–12; CH2 Cor.1.2–1.3 p.3, Lemma 9.2 p.35 and B.5/(B.6) p.44.'
Msrc='Dusart Thms 5.6,5.7,5.9 pp.17–20 and (2.1), Thm 4.2/Prop.4.4 pp.3–4,11–13; CH2 Cor.1.3, Lemma 9.2, (B.6),(B.9); FiniteRH Thm 1/Cor.1 pp.2,4; FKS 3.2 and Cor.2.9/Table 8 pp.7–8,26; QRH Thm 1.1 p.4 for the B0 spectral branch.'
claims=[]
scope=j(p/'OWN_D01_VALIDATED_SCOPED_FLOOR.json')
scoped={r['claim_id'] for r in scope['qualified_scope_index']}
quoted={r['claim_id'] for r in scope['nonactive_source_objects']}
assert len(scoped)==247 and len(quoted)==2
old=j(p/'D01_M_REVIEW_review.json')['claims']
assert {r['claim_id'] for r in old}==scoped|quoted
def remap(s):
    n=s['original_basename']
    if n=='candidate.md' and s['sha256']==byname['D01_repaired_candidate.md']['sha256']:
        n='D01_repaired_candidate.md'
    assert byname[n]['sha256']==s['sha256'],s
    return loc(n,s['physical_LF'],s.get('physical_LF_last'),s.get('formula'))
receipt_alias={'audit':'local'}
E=j('evidence.json')
available=set(E['child_receipts'])|{'local','dec','newreplay'}
for ob in old:
    # Copy statement/domain/source pointers as inventory input, not old decision/status.
    keys=('claim_id','family','exact_statement','assumptions','full_domain','strictness',
          'real_or_integer','baseline_comparison','source_locators','numerical_obligations')
    r={k:ob[k] for k in keys}
    i=r['claim_id']; a=r['assumptions']
    r['written_source']=remap(ob['written_source'])
    r['other_written_sources']=[remap(s) for s in ob.get('other_written_sources',[])]
    r['implemented_formula_readbacks']=[remap(s) for s in ob.get('implemented_formula_readbacks',[])]
    used=[receipt_alias.get(t,t) for t in ob.get('actual_verification_receipts',[])]
    # Prior IDs happen to match the launcher step names; link to fresh outputs only.
    assert all(t in available for t in used),(i,used)
    r['actual_verification_receipts']=[f'evidence.json:{t}' for t in used]
    r['derivation_check']=('See current independent review.md: '+(
      'Exact positivity boundary, integer trust and restricted subset / Count transfer and entire-ray certificates'
      if i.startswith('R-') else
      'Current common spectral machinery and Source-to-formula checks' if i.startswith('Shared-') else
      'Scoped ancillary results' if i.startswith('A-') else
      'Exact transfers, signs and spill / Historical finite and analytic atlas')+
      '. Formula-level implementation linked separately when applicable.')
    r['V_status']=V; r['remaining_trust']=trust
    r['role']='scoped inheritance' if i in scoped else 'nonactive history (not a current theorem)'
    if i.startswith('A-'): r['secondary_unscored']=True
    if 'COUNTERFACTUAL' in a:
        r['assumptions']=a.replace('COUNTERFACTUAL only:', 'Historical conditional (matching current D02 only):')
    r['precise_gap_or_counterexample']=''
    r['retained_valid_branches']=[]
    r['M_status']=status
    if i in {'R-PT-late','R-DP-late','R-DP-RH','M-Dusart-products','M-Dusart-u','M-Dusart-j','M-original-kernels'}:
        r['M_status']='baseline_retained'
    if i in {'Shared-strip','Shared-H-redundancy'}:
        r['M_status']='equivalent_or_weaker'
    if i=='R-quoted-false-real':
        r['M_status']='false_with_specific_counterexample'
        r['precise_gap_or_counterexample']='Quoted source only: at 38358837682.1, -7974586<R<-7974585.'
        r['retained_valid_branches']=['R-local','R-integer-transfer','R-PT-late']
    if i=='M-historical-aux-missing':
        r['M_status']='incomplete_with_specific_missing_step'
        r['precise_gap_or_counterexample']='Historical unmodified code skips finite cell clipped to [10000,10007); not a counterexample to the caps.'
        r['retained_valid_branches']=['M-aux-repaired']
    if i=='R-noQRH-union':
        r['limitation']='No assertion on (754,3039.2) in log scale for this premise subset.'
    if i in {'M-old-power-adaptive','M-noQRH-tail','M-D02-tail-finite-analytic'} or i.startswith('M-D02-table'):
        r['actual_verification_receipts'].append('evidence.json:dec')
    d02=any(s in a for s in ('Hprime','27/32','A-D02','H\''))
    d01=any(s in a for s in ('7/8','under H','D01')) and not d02
    if d02:
        use='D02 when the recorded extra premise matches its exact contract; full RH and other conditions not discharged.'
        where= ('Earlier switch, faster exp(−5z/32) or direct majorant after its legal pivot' if i.startswith('R-') else
               'Narrower strip in high-zero point and tail terms, or direct exp(−5t/32)t²/64 after t=200 in the direct branch')
        if i.startswith('R-sensitivity'):
            r['baseline_comparison']='Matching D02 now available; earlier B0 and conditional rows retained, superseded only where new exact rows are stronger.'
    elif d01:
        use='D01 optional only at written hypotheses or as a substitute for QRH if QRH removed.'
        where='No cumulative B0 effect: D01 as written follows from QRH and original reciprocal-zero bounds.'
    else:
        use=False; where='No hypothetical input needed for this branch or not an active theorem.'
    r['propagation']={'input_used':use,'where_it_changes_proof':where,'matched_comparison':r['baseline_comparison']}
    claims.append(r)

def new(cid,fam,source,a,z,txt,domain,impl,proof,rec=(),b=None,
        strict='as displayed', comparison=None, extra=(),num=None, M=status):
    assert all(s in available for s in rec),rec
    ref={'Ramanujan':Rsrc,'Mertens':Msrc}[fam]
    where=('D02 narrows the strip to beta<=27/32; point and integral bounds change on their own domains. No direct hypothesis used below exp(200).'
           if b=='J' else 'No D02 input; common-original calculation or strip-free finite deduction as stated.')
    keys=dict(claim_id=cid,family=fam,written_source=loc(source,a,z),
      other_written_sources=[loc(*s) for s in extra],
      implemented_formula_readbacks=[loc(*s) for s in impl], exact_statement=txt,
      assumptions='B0+D02' if b=='J' else 'B0' if b=='Q' else 'see proof; finite arithmetic or jointly parameterized in original B0 and B0+D02',
      full_domain=domain,strictness=strict,real_or_integer='real',
      baseline_comparison=comparison or ('B0 comparison at b=7/8; preserve all original and retained envelopes by intersection or maximum.' if b=='J' else 'Input-independent relative to cumulative B0; no D01 increment.'),
      source_locators=ref,derivation_check=proof,numerical_obligations=num or ('Exact directed enclosure as linked, plus analytic continuation where applicable.' if rec else 'Analytic verification; no sample inference.'),
      actual_verification_receipts=['evidence.json:'+s for s in rec],
      retained_valid_branches=[],M_status=M,precise_gap_or_counterexample='',
      V_status=V,remaining_trust=trust,
      propagation={'input_used':'D02' if b=='J' else ('parameterized B0 and B0+D02' if b=='both' else False),
        'where_it_changes_proof':where if b!='both' else 'At matched hypotheses use b=7/8 vs 27/32 in the actual spectral terms and preserve older choices.',
        'matched_comparison':comparison or 'Use exact domain and functional shape; no exhaustive B0 optimum.'})
    claims.append(keys)
new('S-D02-strip','Ramanujan','theory_d02.md',3,7,'No nontrivial zeta zero in Re s>27/32; D02 implies old D01.','All nontrivial zeros; hypothetical point estimate is used only for real x>=exp(200).',[],
    'Independent Euler-product/holomorphic-tail check; a zero would force a pole.',b='J',extra=[('candidate.md',3,3)])
new('S-D02-mass','Ramanujan','theory_d02.md',9,25,'Both inverse-m cumulative moment upper bounds, m=1 and 2, for nonnegative ordinate weights; either source and prefix minima.','sigma in [3/4,b] with H and H_f as written.',
    [('spectral.py',3,22,'Exact inflated interval constants and m=1 moment'),('smoothed.py',5,14,'m=2 formula including conjugates')], 'Layer summation and Taylor correction, with exact density/source domains checked.',b='both')
new('S-D02-mesh','Ramanujan','theory_d02.md',27,34,'Nested weighted moment staircase B_(b,m), including beta=b, and point bound exp(−(1−b)t)C_b(t); C_b decreasing.','t>=80 for the point estimate; weighted comparison at positive t.',
    [('spectral.py',23,59,'Positive telescoped weights and FKS point profile'),('smoothed.py',15,34,'Inverse-square weights and Dusart-only fallback')], 'Upper right-step and positive cumulative increments; C_b monotonic termwise on the full ray.',b='both')
new('S-D02-average','Ramanujan','theory_d02.md',36,44,'S_b point bound for every 0<h<=1, and admissible shrinking h with monotone t² S_b after t>=4/(1−b).','t>=80, including jumps.',
    [('smoothed.py',23,29,'Inverse-square kernel and S_b'),('mertens_d02.py',17,28,'Shrinking h and frozen prefactors'),('gap_d02.py',6,9,'Fixed h list for closed boxes')], 'Two one-sided sandwich means, absolutely integrable compactly after termwise integration; least decay k/2, with no asymptotic improvement claimed.',('local',),b='both')
new('S-D02-Jref','Mertens','theory_d02.md',46,58,'Uniform |S_a^*|<=exp(−at)J_ref; minimum with inverse-first moment/H and original J.','t>=80,a>=0 for density refinement; plain J for x>=100.',
    [('spectral.py',63,74,'First moment divided by H'),('smoothed.py',23,26,'Inverse square moment'),('mertens_d02.py',6,16,'Implemented first-moment scaled tail')], 'Distinct point and integrated bounds; high inverse denominator and absolute convergence checked.',b='both')
new('R-D02-carry','Ramanujan','ramanujan_d02.md',69,81,'Oscillatory signed prime-count radius with carry as in gap_d02.py, and legal point/old-radius minima.','z>=24 individually for both x and x/e.',
    [('gap_d02.py',16,39,'Separate signs, finite-cell choice and oscillatory carry'),('gap_d02.py',99,103,'Prefix and low-weight scalar bounds')], 'Abel identity and integration by parts at 16 and z; legal fallback and left dyadic evaluation.',('gap_d02.py-base','gap_d02.py-new'),b='both')
new('R-D02-poly','Ramanujan','ramanujan_d02.md',83,93,'Three anchored li₂ enclosures; full lower expression including square and shifted loss and exact paying-degree tails.','z>=24/55/75 for models N=14/27/37; both z=t and t−1 accordingly.',
    [('gap_d02.py',41,98,'Exact coefficient convolution, finite and monotone tail testers')], 'Anchors propagated by derivative; strict omitted positive terms; scaled tail monotone beyond anchor.',('gap_d02.py-base','gap_d02.py-high','extra_gap.py-far'),b='both')
new('R-D02-boundary','Ramanujan','ramanujan_d02.md',10,12,'Unchanged optimal open sign ray x>r and least integer onset 38358837683; local linear lower margin and left failure.','Open real sign ray and local [n,n+1] as separately stated.',
    [('D01_pi_exact.py',34,55,'Integer counts and local derivative'),('D02_cert.py',114,127,'Tight exact bracket importing D02_count.py')], 'Exact local counts, monotone integer transfer, analytic overlap.',('d01-pi','D02_cert.py','local','ram-base'),b='Q',comparison='B0 already attains sharp endpoint; D02 cannot improve it.',extra=[('candidate.md',5,5)])
def rrow(b,l,k,w,line,rec,prog,start,end):
    cid=f'R-new-{b}-{l}-{k}-{w}'
    c=('Equal degree-6 cap 86 earlier than 50; B0 cap at 50 is 24 from 49.5, prior D02 82.4.'
       if w=='86' else
       'Matched full d6: 185.4 D02 vs B0 217; prior conditional 186.6.' if str(l)=='185.4' else
       'Matched cubic 1412: 209.8 vs B0 253 and prior conditional 212.' if str(l)=='209.8' else
       'Compare the other column at the same degree and full factorial coefficient; all ray-wise adaptive alternatives retained.')
    new(cid,'Ramanujan','ramanujan_d02.md',line,line,
        'R/h > sum_(j=4)^(k−1) d_j/t^(j−4) + w/t^(k−4), k='+str(k)+', w='+str(w)+'; d_j exactly as LF6.',
        'all real t>= '+str(l),[(prog,start,end,f'Actual row {l}, degree {k}, cap {w}; see exact output row.'),
          ('gap_d02.py',63,98,'Finite closed cells and/or monotone pay at certified right anchor')],
        'See Count transfer and entire-ray certificates: both arguments lawful, directed boxes plus paid decreasing error tail.',
        (rec,),b=b,strict='strict at inclusive onset',comparison=c,
        num='See exact output row carrying both box endpoints, or exact printed monotone-only onset. No moved-on fallback accepted.')
for line,k,g in [
 (20,4,'36.57:.002 36.61:.02 36.7:.06 36.88:.14 37:.20 38:.56 40.01:1'),
 (21,5,'45:10.2 47.08:14'),
 (22,6,'47.55:20.5 49.5:24 50:23 170:23 200:115 217:145')]:
    for c in g.split():
        l,w=c.split(':')
        add=l in ('36.57','49.5')
        rrow('Q',l,k,w,line,'extra_gap.py-try' if add else 'gap_d02.py-base',
             'extra_gap.py' if add else 'gap_d02.py',21 if add else 121,25 if add else 123)
for line,k,g in [
 (28,6,'48:48 48.75:76 49:82 49.03:85 49.2:86 50:86 172:108 176:126 185.4:145'),
 (29,7,'189:535 209.8:1412'),(30,8,'235.1:13985'),(31,9,'262:145450'),
 (32,10,'292:1610021'),(33,11,'319:19063832'),(34,12,'348:241691425'),(35,13,'378:3277187246')]:
    for c in g.split():
        l,w=c.split(':')
        add=l in ('49.03','49.2','209.8')
        rrow('J',l,k,w,line,'extra_gap.py-try' if add else 'gap_d02.py-new',
             'extra_gap.py' if add else 'gap_d02.py',21 if add else 124,25 if add else 128)
for k,lq,lj in [(14,530,406),(15,565,445),(16,606,476),(17,648,511),
                (18,682,536),(19,718,567),(20,755,596),(21,794,626),(22,832,655),
                (23,870,685),(24,908,715),(25,950,748),(26,1010,778),(27,1030,807),
                (28,1070,838),(29,1110,870),(30,1150,902),(31,1200,936),(32,1240,968),
                (33,1285,1002),(34,1330,1035),(35,1380,1070),(36,1425,1105)]:
    for b,l in [('Q',lq),('J',lj)]:
        far=k>=27
        rrow(b,l,k,'d'+str(k),k+29,'extra_gap.py-far' if far else 'gap_d02.py-high',
             'extra_gap.py' if far else 'gap_d02.py',5 if far else 130,18 if far else 140)
        claims[-1]['baseline_comparison']=f'Equal full d{k} strength: onset {lq} in B0 and {lj} in B0+D02. B0+D01 does not alter B0.'
        claims[-1]['propagation']['matched_comparison']=claims[-1]['baseline_comparison']
new('R-new-match','Ramanujan','ramanujan_d02.md',37,37,'At t=185 the common degree-6 residual lower expressions satisfy B0 <27 and D02 >144.','t=185 only; no upper bound on actual R.',
    [('compare_d02.py',12,17,'Evaluate checker model residual, not counts')], 'Directed arithmetic distinguishes comparison of models from comparison of true values.',('compare',),b='both')
new('R-new-failed','Ramanujan','ramanujan_d02.md',95,97,'Method failures for w=87 and early full d6; no claim that R violates the test targets.','Trial box near 166.4; point diagnostics 185.25 and 215.5; limited absolute-radius proof.',
    [('extra_gap.py',19,25,'Actual trial failures')], 'Audit exact model point signs for d6 and failure of whole-box sufficient test for 87.',('extra_gap.py-try','local'),b='both')

def mrow(b,l,c,kind,line,n1,n2,rec):
    islog=kind=='log'
    forms='c/t³ and c/t²' if islog else 'c exp(−(1−b)t)/t and c exp(−(1−b)t)'
    new(f'M-new-{kind}-{b}-{l}-{c}','Mertens','m_d02.md',line,line,
        f'Both normalized relative product errors and |u| use first scale, |j| second: {forms}, c={c}.',
        ('all real x>='+str(l)[2:] if str(l).startswith('x=') else 'all real t>='+str(l)),
        [('mertens_d02.py',n1,n2,'Actual chosen cap, normalized analytic radii, relative conversion')],
        'See New tables and exact early power roots: finite clipping if needed, convex joins, decreasing continuation and positive relative conversion.',
        rec,b=b,strict='strict inclusive ray')
for l,c,line in [(170,'.2557',27),(180,'.2402',28),(186,'.2325',29),(200,'.21771',30),
                 (250,'.18611',31),(300,'.16962',32),(500,'.14409',33),(1000,'.12952',34),
                 (2300,'.12258',35),(50000,'.1166',36),(1000000,'.11627',37)]:
    mrow('J',l,c,'power',line,92,101,('mertens_d02.py-analytic',))
for l,c in [('x=560000','.01322'),(200,'.012400'),(300,'.009683'),(1000,'.007418'),
            (2300,'.007024'),(1000000,'.006665')]:
    mrow('Q',l,c,'power',39,76,101,('mertens_d02.py-analytic','repaired','mertens-new'))
mrow('J','x=200','.30','power',21,43,75,('finite-200','mertens_d02.py-analytic','dec','repaired'))
mrow('J','x=285','.25665','power',21,43,101,('finite-285','mertens_d02.py-analytic','dec','repaired'))
mrow('J','x=10000','.25665','power',68,76,101,('mertens_d02.py-analytic','repaired'))
new('M-new-power-119','Mertens','m_d02.md',21,21,'Products and prime reciprocal sum strictly below .25665 x^(−5/32)/t.', 'all real x>=119 (NOT weighted).',
    [('mertens_d02.py',43,75,'Finite mode set (0,1,2)'),('mertens_d02.py',76,91,'Analytic all-four tail from 10000')],
    'Whole cells and use whole analytic tail after exact join.',('finite-119','mertens_d02.py-analytic','dec','repaired'),b='J')
for line,mode,bracket in [
 (16,'Q* and joint products','(1978832961/16777216,989416481/8388608)'),
 (17,'P* alone','(986197315/8388608,1972394631/16777216)'),
 (18,'u','(495622485/4194304,991244971/8388608)'),
 (19,'j and joint four','(186574499/655360,1166090619/4096000)')]:
    wt=line==19
    new(f'M-new-root-{line}','Mertens','m_d02.md',line,line,
        f'Least closed real onset for .25665 narrower-power tolerance for {mode}: exact root in {bracket}.',
        'all x>=its stated exact root; strict for x>root, failure just to its left.',
        [('mertens_d02.py',132 if wt else 155,153 if wt else 182,'Exact gap root tests and monotonic inequalities'),
         ('mertens_d02.py',30,101,'Constants, mode-specific finite cells, convex and decreasing joins')],
        'Fixed prime gap with positive scaled error and negative derivative, then directed finite section plus entire analytic suffix.',
        ('mertens_d02.py-weighted-root' if wt else 'mertens_d02.py-three-roots','finite-285' if wt else 'finite-119',
         'mertens_d02.py-analytic','dec','repaired'),b='J',
        strict='non-strict at exact root, strict to its right',comparison='Earlier conditional .262 from 10000 is beaten in onset and coefficient on the same scale; finite sign test itself is input-independent.',
        extra=[('m_d02.md',41,49),('candidate.md',7,7)])
for line,l,cq,cj in [(55,61,'3.595e-8','2.903e-8'),(56,170,None,'2.18e-8'),
                     (57,180,None,'4.76e-9'),(58,185,None,'2.24e-9'),(59,200,'6.90e-9','2.34e-10'),
                     (60,250,'1.78e-11','1.27e-13')]:
    for b,c in [('Q',cq),('J',cj)]:
        if c:
            mrow(b,l,c,'log',line,103,122,('mertens_d02.py-log',))
            claims[-1]['baseline_comparison']=f'Matched log onset {l}; B0 cap {cq if cq else "inherited envelope only, no new selected row shown"}; D02 {cj}.'
            claims[-1]['propagation']['matched_comparison']=claims[-1]['baseline_comparison']
for t,c in [(98,'.012400'),(117,'.006665'),(200,'.000421')]:
    new(f'M-new-shapes-{t}','Mertens','m_d02.md',39,39,
        f'D02 proves coefficient {c} in B0 exponent shape x^(−1/8)/t or x^(−1/8).','real t>='+str(t),
        [('compare_d02.py',18,24,'Exact exp(−t/32) scale conversion')],
        'Multiply original coefficient by exp(−t/32), which decreases on whole ray.',('compare','mertens_d02.py-analytic'),b='J',strict='strict inclusive')
new('M-new-cross','Mertens','m_d02.md',39,39,'Selected main monomials cross at 32 log(.25665/.01322) in (94,95), D02 smaller only to right; .21771 at 200 beats the listed B0 power caps there and afterward.','shared domains only.',
    [('compare_d02.py',5,8,'Crossover bracket'),('compare_d02.py',18,24,'Scale comparison')], 'Exact ratio and strict decreasing exponential, not sample ordering.',('compare',),b='both')
new('M-new-atlas','Mertens','m_d02.md',64,76,'Signed envelopes with all available source and historical branches, exact reciprocal relative intervals and minimum, including no new claim of global optimality.','each branch on its own written domain.',
    [('mertens_d02.py',6,28,'Spectral and smoothing extra plus relative radius'),('mertens_d02.py',43,75,'Finite certified interval mechanism')],
    'Exact Abel identities, positive spill, legal/independently signed minima, then exponentiate each endpoint as written.',('mertens_d02.py-analytic','mertens_d02.py-log'),b='both')
new('M-new-raw','Mertens','m_d02.md',76,76,'Selected normalized D02 point radius is <raw D02 radius/2800.','real t>=200.',
    [('compare_d02.py',9,11,'Anchor 2800 C_b(200)<625')], 'Increasing t² vs decreasing C_b; point comparison only.',('compare',),b='J',strict='strict')
new('M-D02-center','Mertens','m_d02.md',78,79,'Optional spill centering at each y=x^(1/m): use C_b(log y)*v^b+1.4262 sqrt(v), intersect pointwise with CH2 in the positive kernel.','log y>=80 and v>=y for each cutoff y separately.',
    [('spectral.py',51,59,'Admissible C_b component'),('smoothed.py',30,34,'Inherited c and minimum')],
    'Monotonic normalized C over the entire v-ray; signed Stieltjes boundary uses actual cutoff. No sign inferred.',b='both')
new('M-new-correlated','Mertens','m_d02.md',80,85,'Both coupled differences bounded by J_ref/t+(1/t+2/t²)L_b, for L_b using inverse squares K_b/H.','real t>=80.',
    [('smoothed.py',23,26,'K_b is inverse-square radius, not the Abel error')],
    'Extra reciprocal denominator via signed e^(at)S_a−S_0 and low weight .0462^(3/2)<.00994; integrate a(1+a).',b='both')
new('M-new-limits','Mertens','m_d02.md',87,89,'Observed j scaled above .2707 at x=283 is a witness against extending the stated .25665 weighted cap to that point; wider joins are failed sufficient tests only.','x=283; trial smoothing and finite certificates on described domains.',
    [('mertens_d02.py',132,153,'Weighted fixed-prime calculations used by review')], 'Exact point enclosure for x=283; no theorem of optimality for analytic method.',('local',),b='both')
new('S-new-premise-scope','Mertens','candidate.md',9,13,'Cumulative B0, exact stated retention, no Lean or source-first PV and no exhaustive B0 optimum.','all branches; unchanged separate premises.',
    [], 'Verified exact own-source scope and relinked all active statements; full RH never discharged by these inputs.',
    b='both',M='baseline_retained')

# Independent row-by-row match rather than the launcher's count-of-lines tests.
from math import factorial as fac, comb
def dk(k):
    return sum(fac(i)*comb(k,i)-fac(i)*fac(k-i) for i in range(k+1))
for r in claims:
    rr=re.fullmatch(r'R-new-([QJ])-([0-9.]+)-([0-9]+)-([d.0-9]+)',r['claim_id'])
    if not rr: continue
    b,l,k,w=rr.groups(); l=F(l); k=int(k); w=F(dk(k)) if w.startswith('d') else F(w)
    b={'Q':'7/8','J':'27/32'}[b]
    read=E['child_receipts'][r['actual_verification_receipts'][0].split(':')[1]]['stdout']['text']
    matched=[]
    for line in read.splitlines():
        x=line.split()
        if x[0]!='certified': continue
        if x[1] in {'far','monotone'}:
            _,_,bb,ll,kk,ww=x; U=F(ll)
        else:
            _,bb,ll,uu,kk,ww,cells=x
            U=F(uu)
            assert int(cells)>0 and U>F(ll)
        if (bb,F(ll),int(kk),F(ww))==(b,l,k,w):matched.append(U)
    assert len(matched)==1,(r['claim_id'],matched)
    r['numerical_obligations']+=f' Exact reported right/monotone anchor: {matched[0]}.'

assert len({r['claim_id'] for r in claims})==len(claims)
fa={}
for f in ['Ramanujan','Mertens']:
    fr=[r for r in claims if r['family']==f]
    fa[f]=dict(strongest_supported_portfolio=[r['claim_id'] for r in fr if
              r['M_status'] in (status,'baseline_retained') and not r.get('secondary_unscored')
              and 'failed' not in r['claim_id'] and 'limits' not in r['claim_id']],
             rejected_or_incomplete_claims=[r['claim_id'] for r in fr if r['M_status'] in
                  ('incomplete_with_specific_missing_step','false_with_specific_counterexample')],
             remaining_assessment_work=[],
             summary=('Supported B0 and D02 portfolios with exact unchanged sign root, retained alternative premise sets and inclusive quantitative profiles.'
             if f=='Ramanujan' else
             'Supported signed and absolute atlas with exact separate new power roots, old tolerance roots and joined finite/logarithmic/power envelopes.'))
r=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=idx['candidate_id'],
       assessment_complete=True,all_claims_inventoried=True,
       reviewed_source_hashes={q['packet_name']:q['sha256'] for q in rows},
       source_bibliography=j(p/'SOURCE_INDEX.json')['sources'],
       actual_effort={'commands':[E['restore_command']]+[x['argv'] for x in E['commands']],
                      'evidence':'evidence.json', 'work':'Original formula/domain readbacks, full locked replay, ancillary exact observer/local checks; no estimated tokens.'},
       family_assessments=fa,claims=claims,no_other_arm_or_ranking_seen=True,
       new_core_math_salvage_performed=False,original_candidate_bytes_changed=False,
       own_history_visible=True, inherited_objects={'active':247,'nonactive':2},
       manuscript='review.md',source_checkpoints='source-checkpoints.md')
Path('review.json').write_text(json.dumps(r,indent=1,ensure_ascii=False)+'\n')
print('registry count',len(claims))
