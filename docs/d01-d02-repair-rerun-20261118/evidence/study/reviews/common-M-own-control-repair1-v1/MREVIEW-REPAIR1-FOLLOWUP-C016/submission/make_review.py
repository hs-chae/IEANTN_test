#!/usr/bin/python3.10
"""Assemble independently authored assessments. The own-history map supplies only IDs, wording and locations."""
from pathlib import Path
import json, hashlib
from fractions import Fraction as F

out=Path(__file__).resolve().parent
root=Path('/work/exact-review')
task=Path('/task')
rd=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
idx=rd(task/'CANDIDATE_INDEX.json')['candidate_files']
meta={z['original_name']:z for z in idx}
orig=rd(task/'SOURCE_INDEX.json')['sources']
history=rd(root/'claim_map.json')
for z in idx:
    assert sha(root/z['original_name'])==z['sha256']==sha(task/z['packet_name'])
for z in orig:
    for t in ('pdf','text'): assert sha(Path('/corpus/originals')/z[t])==z[t+'_sha256']
assert sha(root/'OWN_PRIOR_M_013.json')==history['original_inventory_sha256']
support='supported_at_stated_trust_tier'
baseline='baseline_retained'
false='false_with_specific_counterexample'
equiv='equivalent_or_weaker'
P='B0 plus exact D02'
R='Ramanujan'
M='Mertens'
sources={
 'qrh':'OpenAIQRH PDF p.4 Thm.1.1 (text LF255–262), proof conclusion p.197 LF14679–14684',
 'd02':'INPUT_CONTRACT.json, FOLLOWUP-D02 assumption PsiMajorant: coefficient 1/64, beta=27/32, log power=2, real inclusive x>=exp(200)',
 'rh':'PlattTrudgianFiniteRH PDF p.2 Thm.1 LF48–49, p.4 Cor.1 LF138–150, and p.5 signed range LF182–185',
 'density':'FKS PDF p.4 LF272–274, pp.7–8 Thm.2.7 eq.(2.14), Cor.2.9 LF539–545,586–609; PDF p.26 Table 8 first a1=.77 block LF3139–3258',
 'formula':'FKS PDF p.8 Thm.3.2 LF631–642; PlattTrudgian2021 PDF p.4 Lem.2 LF236–246',
 'fks':'FKS PDF p.2 Thms.1.1–1.2, Cor.1.4 LF112–143; Tables 5–6',
 'ch':'CH2 PDF p.3 Cor.1.2–1.3 LF190–240; p.35 Lem.9.2 LF5216–5223',
 'ch9':'CH2 PDF p.36 Cor.9.3 eq.(9.4), LF5336–5355',
 'dus':'Dusart2018 PDF pp.7–8 Prop.3.2/Theorem 3.3 LF455–475, Table 1; p.11 Thm.4.2 LF959–1010; p.13 Cor.4.5 LF1132–1137',
 'pnt':'PlattTrudgian2021 PDF pp.2–3 Thm.1/Cor.1 and Table 1 LF77–118,135–201; p.3 Cor.2 LF127–134 with p.7 LF544–557; p.9 Lem.6 LF801–807',
 'oldr':'DudekPlatt2015 PDF p.2 Thm.1.2 LF53; p.8 §3.1 LF591–594, p.10 Lem.3.4 LF698–714; PlattTrudgian2021 PDF p.3 Thm.2 LF205–212',
 'oldm':'Dusart2018 PDF p.17 Thm.5.6 LF1479–1505, pp.18–19 Thm.5.7 LF1555–1586, p.19 Thm.5.9 LF1640–1664'
}
sp=('qrh','rh','density','formula','d02')
oldp=('oldr',)
early=('rh','pnt','ch9','dus')
rs=sp+early+('ch',)
ms=sp+('dus','oldm','ch')
mid=('ch','rh','dus','oldm','density','formula','qrh')
defined=tuple()
catalog={
 'cap0':(('qrh',),'Published closed cap derived from open zero-free half-plane; no equality exclusion.',[]),
 'cap1':(('d02',),'Mellin logarithmic-derivative identity; normal convergence strictly to the right of the cap.',[]),
 'density':(('rh','density','qrh','d02'),'Abel tail integration with cubic and concavity, then conjugate-inclusive running-min bin mass bound.', [('cert.py',60,87)]),
 'S':(sp+('ch',),'All-real FKS explicit formula; T admissible and both low-zero pieces independently bounded; CH Cor.1.3 padded separately.', [('cert.py',85,89),('endpoint.py',4,11)]),
 'D':(sp,'Add only omitted high-part tail; v>=62 implies T>=H. Bound integrated tail with the two padded coefficients.', [('mertens.py',45,50),('mertens.py',97,102)]),
 'seeds':(('rh','pnt','ch','ch9','dus','fks','d02'),'Cumulative optional source intervals and true domains; CH2 Cor.1.2 psi centering retained or padded, PNT integral from 2 not PV li; unweighted constant plateaux switched before infinity.', [('cert.py',88,90),('mertens.py',10,24)]),
 'local':(defined,'Exact quotient survivors and strict signs; monotone e*x/log x gives the unique zero and bracket.', [('pcount.cpp',7,20),('endpoint.py',12,25)]),
 'PNT-literally-false':(oldp,'Quoted source claim rejected by candidate; exact counts remain constant at the counterexample and both brackets.', [('pcount.cpp',7,20),('endpoint.py',12,25)]),
 'inherited-integer':(oldp,'Original finite computation reports integer conclusion; monotone floor lift with right-continuous counts.',[]),
 'inherited-real':(oldp,'Published finite sign result, not arbitrary-fraction independent application of its stepping lemma. Requires original literature computation tier.',[]),
 'old-tails':(oldp,'Separate distant rays; no import of full RH. Contained in the new analytic sign ray.',[]),
 'permanent':(oldp+early,'Local root plus floor lift, finite literature bridge and strict overlapping analytic tail.', [('pcount.cpp',7,20),('endpoint.py',12,25),('ram_early.py',30,35),('cert.py',188,214)]),
 'main':(defined,'Stieltjes transport, exact shifted normalization and ODE, algebraic residual coefficients and directed series at 34.', [('cert.py',121,159)]),
 'R3':(rs,'Square nonnegative upper count and subtract shifted lower-count loss with fifth power of L/(L−1); signed branch only on legal theta interval.', [('cert.py',96,131)]),
 'R3-osc':(rs,'Integrate each high zero by parts on [62,v] and keep both boundaries. Shift independently. Piecewise past kernel controlled.', [('repair_ram.py',22,42)]),
 'CH-bridge':(early,'CH2 (9.4), exact optimized T; per-argument height and finite positive transport, monotonic endpoint factors.', [('ram_early.py',3,18),('ram_early.py',30,40)]),
 'transport-gain':(rs,'Positive weighted bin rates still monotone in bin endpoint, and S1 transport beats CH floor after common terms are canceled.', [('cert.py',98,120),('mertens.py',109,114)]),
 'constant-limit':(rs,'Fixed-order integration by parts for F and expansion of both smooth arguments, exponential transported errors vanish.',[]),
 'higher-order':(rs,'Positive g_(N+1) for fixed N from binomial reciprocals bound and factorial series; smooth slack eventually positive. No numerical onset asserted.',[]),
 'definitions':(('oldm',),'Read exact Stieltjes centers and both relative product normalizations, not decimal constants.',[]),
 'old-product':(('oldm',),'Official theorem both products at exact relative normalization and inclusive x=2278382.',[]),
 'old-reciprocal':(('oldm',),'Official theorem reciprocal sum around log L+M and inclusive x=2278383.',[]),
 'old-weighted':(('oldm',),'Official theorem weighted sum around L−B3 and inclusive x=912560.',[]),
 'M1':(('oldm','density','formula','qrh'),'Stieltjes endpoint-minus-tail identities, convergent spectral tails and Abel/Laurent normalization of Euler constant.',[]),
 'M2':(('oldm',),'Exactly add omitted positive powers; subtract all logarithmic powers for primes beyond x in log normalized inverse product.',[]),
 'M3':(('dus',),'Correct lower endpoint of D from theta at sqrt(x), upper integral of D, Stieltjes over (x,infty), and nonnegative lower refinements.', [('mertens.py',25,31)]),
 'positive-transfers':(ms,'Signed/absolute legal theta and psi kernels, CH weighted bound in dv/v², preservation of convergence and normalizations.', [('mertens.py',14,44),('anchor.py',28,46)]),
 'M4-M5':(ms,'High component integrated first, changes 1/rho to 1/(rho−1); remaining W integral costs at most 2/(HL).', [('mertens.py',45,57)]),
 'M6':(ms,'Use exp(B_l)−1 for absolute errors of both reciprocal products and reciprocal sum; code larger B_l/(1−B_l), checked <1 where needed.', [('mertens.py',45,62)]),
 'at200':(ms,'Directed rescaled M6 budgets read at fixed L=200; primary values independently bounded in audit_checks.json.', [('mertens.py',45,62),('mertens.py',103,108)]),
 'fixed-prodR':(ms,'Monotonic M6 budgets, original fixed-error point tests suffice for all larger L.', [('mertens.py',45,62),('mertens.py',92,96)]),
 'fixed-G':(ms,'Monotonic M6 weighted budget, exact endpoint test with no tail sampling.', [('mertens.py',45,62),('mertens.py',92,96)]),
 'cross':(ms,'Exact ratio and restricted pairwise crossing; monotone tail beats inverse-log budgets on L>=200.', [('mertens.py',80,95),('mertens.py',109,116)]),
 'raw':(ms,'Exact integrals of positive polynomial times exponential, legal from L=200; strict dominance by the S1 seed and clean oscillatory budgets.', [('cert.py',89,92),('mertens.py',109,114)]),
 'budget-floor':(ms,'Lower bound on the same-method budget only, via last coefficient of the positive exponential mixture.', [('mertens.py',109,116)]),
 'full-pointwise':(ms,'Independent signed intervals for each observable, monotone log and exp conversions at signed endpoints, minima on legal domains only.', [('anchor.py',18,27),('mertens.py',51,62)]),
 'bridge-basic':(mid,'Switched positive kernels and separately bounded closed strips through 200, then M0 inverse-log comparison.', [('mertens.py',10,44),('mertens.py',63,79),('mertens.py',115,116)]),
 'bridge-strong':(mid,'Signed anchor and small-height U and W with exact K join; corrected upward pad; then valid M0 at 200.', [('anchor.py',12,72),('mertens.py',51,62)]),
 'sieve':(('dus','oldm'),'Exact integer sieve with adverse pads, positive series truncations, both sides of jumps, exact start and terminal N.', [('mertens.cpp',15,110)]),
}
def loc(n,a,b=None):
    z=meta[n]
    s=(root/n).read_text().split('\n')
    b=a if b is None else b
    assert 1<=a<=b<=len(s),(n,a,b)
    return dict(file=n,packet_file=z['packet_name'],physical_LF=a,physical_LF_end=b,sha256=z['sha256'])
docs={}
checks={}
for p in sorted(out.glob('replay_*.json')):
    j=rd(p)
    for i,r in enumerate(j['runs'],1):
        if 'cmd' in r:
            checks[(tuple(r['cmd']),r['cwd'])]=(p.name,i,r)
            alias=r.get('expected')
            if alias: docs.setdefault(alias,[]).append((p.name,i,r))
            if not alias: docs.setdefault(r['cmd'][-1],[]).append((p.name,i,r))
docs['audit_checks.json']=[('audit_checks.json',1,rd(out/'audit_checks.json'))]
def receipts(keys):
    result=[]
    for k in keys:
        assert k in docs, k
        for f,i,r in docs[k]:
            assert r['status']==0 and r.get('byte_equal',True),r
            result.append(dict(file=f,run_index=i,status=r['status'],stdout_sha256=r['stdout_sha256'],byte_equal_locked_receipt=r.get('byte_equal')))
    return result

claims=[]
def add(cid,family,n,a,b,st,domain,model,*,status=support,keys=(),prop=None,base=None,strict=None,gap=None,ret=(),hist=None,supplement=(),work=None):
    ss,proof,codes=model
    if prop is None:
        prop=dict(input_used='B0',where_it_changes_proof='No D02 dependence.',matched_comparison='Retained on B0 and B0 + D02 as an identical branch.')
    if strict is None:
        strict=('Not an inequality, or as specified in exact statement.' if '≤' not in st and '>' not in st else 'Non-strict where ≤, strict where >; stated inclusive starts unless indicated.')
    rec=receipts(keys)
    author_given='Published original source/computation where cited; ordinary verified readback using exact integer or Decimal operations where applicable, as detailed in review.md.'
    if status==false: author_given='Quoted original-paper assertion, not a premise; specific rechecked counterexample.'
    if work is None: work='Replay and the whole-domain bridge/tail proof described above.' if rec else 'No new certificate required for this step.'
    row=dict(claim_id=cid,family=family,written_source=loc(n,a,b),exact_statement=st,
        assumptions='B0 where stated, and precisely B0 + D02 where stated; no D01 or full RH.' if prop['input_used']!='B0' else 'B0; inherited on the cumulative D02 stage.',
        full_domain=domain,strictness=strict,real_or_integer='Real arguments except when statement explicitly concerns integer endpoints/prime counts or complex zeta variables.',
        baseline_comparison=base or prop['matched_comparison'],
        source_locators=[sources[k] for k in ss],derivation_check=proof,
        implemented_readback=[loc(*c) for c in codes],other_written_locators=[loc(*z) for z in supplement],
        numerical_obligations=work,actual_verification_receipts=rec,retained_valid_branches=list(ret),
        M_status=status,precise_gap_or_counterexample=gap,
        propagation=prop,V_status='not checked (paper-only runtime); no Lean/kernel execution or source-first PV claimed',
        remaining_trust=author_given)
    if hist: row['own_prior_written_source']=hist
    claims.append(row)

def prop(kind='S',comparison=''):
    where={
        'cap':'Mellin continuation from the legal D02 psi ray, permitting a smaller global cap.',
        'S':'Replace 7/8 by 27/32 in high-zero mass bins before positive transport; no change to finite seeds.',
        'R':'Smaller high-zero budget at each of L and L−1, same smooth part and block/tail tests; retain B0 minima.',
        'osc':'Tighter Z and decay in D before oscillatory transport, same smooth part and identical finite branches.',
        'M':'Smaller high-zero exponential mixture and omitted-tail budget before oscillatory transport in M4–M6; retain signed and finite branches.',
        'envelope':'On D02 admit also the improved cap and raw bound where legal, preserving every legal B0 branch.',
        'raw':'Direct PsiMajorant only at L>=200; cap consequence enters separate branch earlier.',
    }[kind]
    return dict(input_used=P,where_it_changes_proof=where,matched_comparison=comparison or 'Same-method cap ablation, not a blind baseline: 7/8 vs 27/32. D01 unavailable.')
def model(key):return catalog[key]
def logs_for(key):
    if key in ('local','PNT-literally-false'): return ('endpoint_receipt.txt','audit_checks.json')
    if key=='permanent': return ('endpoint_receipt.txt','early_receipt.txt','ram_receipt.txt')
    if key in ('main','R3','CH-bridge'): return ('early_receipt.txt','ram_receipt.txt')
    if key=='R3-osc':return ('repair_ram_receipt.txt',)
    if key=='S':return ('endpoint_receipt.txt','mertens_receipt.txt')
    if key in ('D','M4-M5','M6','fixed-prodR','fixed-G','cross','raw','budget-floor'):return ('mertens_receipt.txt',)
    if key in ('at200','transport-gain'):return ('mertens_receipt.txt','audit_checks.json')
    if key=='bridge-basic':return ('mertens_receipt.txt',)
    if key=='bridge-strong':return ('anchor_receipt.txt','sieve_receipt.txt','mertens_receipt.txt')
    if key=='sieve':return ('sieve_receipt.txt',)
    return ()
fixedr=(rs,'Per-block directed residual minus all legal transported losses, with an analytic scaled-loss ray from tested tail cutoff.', [('cert.py',98,131),('cert.py',161,214),('ram_early.py',3,40)])
highr=(rs,'Strict scaled-loss tail test against the first residual coefficient from H_27; uses L−1 as well as L.', [('cert.py',173,186),('cert.py',215,230)])
power=(ms,'Directed pure budget at exact start; with spectral and prime-power exponential gaps all rescaled summands decrease on the whole ray.', [('mertens.py',45,62),('mertens.py',80,91)])
finite=(mid,'Integer interval starts test the actual point, both sides of every prime jump and terminal N; signed slopes give real interpolation; continuous .0223 or sharper bridge and spectral tail.', [('mertens.cpp',67,110),('anchor.py',18,72),('mertens.py',80,91)])
repM=(mid,'New tighter M from analytic tail enclosure and exact finite sums; both sides of old-to-new gap verified with post-a sum, monotonic between consecutive primes, then use independently checked old connected ray.', [('repair_m.cpp',23,63),('repair_m.py',19,72),('mertens.cpp',67,110),('anchor.py',18,72)])
repR=(rs,'For order 70 same ODE with directed new start. Scaled oscillatory tail checks first residual, and for 100/H6 closed strips use min of old block and decreasing oscillatory loss.', [('repair_ram.py',7,103),('cert.py',143,159)])
spec_range={'density':(17,40),'S':(42,50),'D':(52,61),'seeds':(63,67)}
for e in history['entries']:
    cid=e['id']
    family=e['family']
    suffix=cid[2:]
    z=e['current_locator']
    old=e['prior_locator']
    oldloc=loc(old['file'],old['LF'],old['LF_end'])
    assert oldloc['sha256']==old['sha256'],old
    n,a,b=z['file'],z['LF'],z['LF_end']
    if suffix in spec_range: a,b=spec_range[suffix]
    st,dom=e['prior_statement'],e['prior_domain']
    p=None
    status=support
    gap=None
    extra=[]
    retained=[]
    if suffix=='cap1': p=prop('cap')
    if suffix in ('density','S','D'):p=prop()
    if suffix in ('seeds','R3','R3-osc','positive-transfers','full-pointwise'):p=prop('envelope')
    if suffix=='transport-gain':p=prop('R','Same positive transport at each cap; also strict improvement vs CH at v>=200, both arguments at L>=201.')
    if suffix in ('M4-M5','M6','at200','fixed-prodR','fixed-G','cross','budget-floor'):p=prop('M',st if suffix in ('at200','fixed-prodR','fixed-G','cross','budget-floor') else '')
    if suffix=='raw':p=prop('raw')
    if suffix.startswith('inherited-') or suffix in ('cap0','old-tails','old-product','old-reciprocal','old-weighted'):
        status=baseline
    if suffix=='inherited-real':
        gap='No independent source trace; original Lem.3.4 at literature tier. Lem.3.3 fractional stepping proof alone does not give the coverage.'
    if suffix=='permanent':
        gap='Literature trust for the two large finite sections; wholly independent conclusion without that trust stops short of the complete connected ray.'
        extra.append(('repair_results.md',85,85))
    if suffix=='PNT-literally-false':
        status=false
        gap='At x=38358837682.001, R is enclosed in [−14669304.472,−14669304.471]. This source clause is explicitly rejected, not asserted.'
        retained=['R-local','R-permanent','R-margin-0','R-old-tails']
    if suffix=='full-pointwise':
        st='Full signed per-observable interval intersections (M1–M6, legal original bounds, connected finite rows), direction-correct relative and inverse-log conversions. Includes all repairs.'
        dom='Real x>1 for definitions, each component only on its stated legal domain.'
    if suffix in catalog: md=catalog[suffix]; ks=logs_for(suffix)
    elif suffix.startswith('margin-') or suffix.startswith('finite-'):
        md=fixedr; ks=('ram_receipt.txt','early_receipt.txt','high_receipt.txt')
        if suffix.startswith('margin-') and int(suffix.split('-')[-1])>=36:p=prop('R',st)
        if suffix=='margin-0':extra.append(('ramanujan.md',113,113))
        if suffix=='finite-78-short': n,a,b='ram_early.py',40,40; extra.append(('ramanujan.md',113,113))
    elif suffix.startswith('H'):
        md=highr; ks=('high_receipt.txt','ram_receipt.txt'); p=prop('R',st)
        extra.append(('ramanujan.md',46,46))
    elif suffix.startswith('power-'):
        md=power; ks=('mertens_receipt.txt',); p=prop('M',st+' Compare on overlap by exact ratio exp(−L/32) times coefficient ratio.')
    elif suffix.startswith('inv-'):
        md=finite; ks=('sieve_receipt.txt','anchor_receipt.txt','mertens_receipt.txt')
        extra.append(('mertens.md',17,38))
    elif suffix.startswith('print-gap-'):
        md=repM; ks=('repair_m_receipt.txt','sieve_receipt.txt','anchor_receipt.txt')
        gap='Historical proof alone lacked the interval up to the old sieve cutoff; current repair covers it with an even earlier start. The historical sufficient-test failure is not a counterexample.'
        retained=['M-repaired-'+str({26:6,27:7,28:8}[int(suffix.split('-')[-1])])]
    else: raise AssertionError(e)
    add(cid,family,n,a,b,st,dom,md,status=status,keys=ks,prop=p,gap=gap,ret=retained,hist=oldloc,supplement=extra)

for i,l in enumerate((root/'repair_m_receipt.txt').read_text().split('\n'),1):
    if not l.startswith('reciprocal '): continue
    tag,c,aa,bb,ot,old,nt,new=l.split()
    st=f'|reciprocal prime-sum error| <= ({c})/L³ at every real x >= {int(new)//1000}.{int(new)%1000:03d}.'
    add(f'M-repaired-{i}',M,'repair_m_receipt.txt',i,i,st,st.split(' at every ')[1],repM,keys=('repair_m_receipt.txt','sieve_receipt.txt','anchor_receipt.txt','mertens_receipt.txt'),strict='Non-strict bound and inclusive real start.',supplement=[('repair_results.md',7,15),('repair_results.md',47,49)],base=f'B0 improvement at same coefficient: old start {old}/1000, new {new}/1000. Both preserved on D02.')
add('M-repair-M-constant',M,'repair_results.md',19,45,'.26149721284629719<M<.26149721284881525 with tighter directed receipt interval.','Exact M (constant).',repM,keys=('repair_m_receipt.txt','audit_checks.json'))
for n,earlyfile,codes,lines in [('14','sieve14_receipt.txt',[('sieve14.py',3,7),('bridge14.py',7,14)],(53,56)),('opt','sieve_opt_receipt.txt',[('sieve_opt.py',3,7),('bridge_opt.py',4,21)],(59,61))]:
    for i,l in enumerate((root/earlyfile).read_text().split('\n'),1):
        if not l.startswith('form'):continue
        t=l.split()
        k=int(t[1]); c=t[3]; x=t[-1]
        st=f'{["Both normalized relative product errors","Absolute reciprocal prime-sum error","Absolute weighted prime-sum error"][k]} <= ({c})/L^{2 if k==2 else 3}.'
        add(f'M-new-{n}-{k}',M,'repair_results.md',*lines,st,f'All real x >= {x}/1000, inclusive.',(mid,finite[1]+' Correct signed pad and per-observable bridge where relevant.',finite[2]+codes),keys=(earlyfile,'sieve_receipt.txt','mertens_receipt.txt',('bridge14_receipt.txt' if n=='14' else 'bridge_opt_receipt.txt')),supplement=[(earlyfile,i,i)],strict='Non-strict error bound on inclusive real ray.',base='B0 improvement adds a smaller coefficient at a later start without deleting earlier-domain rows.')
    add('M-new-bridge-'+n,M,'repair_results.md',*lines,'Parametrized full continuation at the prescribed normalized error coefficients from N to infinity.', 'All real x>=2000000000, with every join included.',(mid,finite[1]+' New branch uses the corrected anchor and valid spectral tail beyond 200.',codes+[('anchor.py',18,46)]),keys=(('bridge14_receipt.txt' if n=='14' else 'bridge_opt_receipt.txt'),'mertens_receipt.txt'))
for i,l in enumerate((root/'m_tail_extra_receipt.txt').read_text().split('\n'),1):
    if l.startswith('clean'):
        _,m,v,c=l.split()
        aa=['1/8','5/32'][int(m)]
        st=f'On B{m} all first-group errors <= {c} x^(−{aa})/L and weighted error <= {c} x^(−{aa}).'
        pp=prop('M') if m=='1' else None
    elif l.startswith('fixed'):
        _,m,k,t,v,_=l.split()
        st=f'On B{m} the {"both product errors and reciprocal prime-sum error" if k=="first" else "weighted prime-sum error"} <= {t}.'
        pp=prop('M','Same target and matched M6 operator: products/reciprocal 1485/8 vs 2667/16; weighted 190 vs 1357/8.') if m=='1' else None
    else:continue
    add(f'M-extra-tail-{i}',M,'repair_results.md',57,57,st,f'Every real L >= {v} inclusive on B{m}.',(ms,power[1],[('m_tail_extra.py',3,30),('mertens.py',45,62)]),keys=('m_tail_extra_receipt.txt',),prop=pp,supplement=[('m_tail_extra_receipt.txt',i,i)],strict='Non-strict bound on inclusive ray.')
add('M-extra-tail-dominance',M,'repair_results.md',57,57,'B1 .25973 budget dominates matched B0 .018791 budget and also the .01 B0 spectral budget floor.','Every real L>=200.',(ms,'Use ratios with exp(−L/32); strict at 200 and decreasing thereafter.',[('m_tail_extra.py',28,30),('mertens.py',109,116)]),keys=('m_tail_extra_receipt.txt','mertens_receipt.txt'),prop=prop('M','Matched clean ratios at every L>=200, not an optimal B0 comparison.'),strict='Strict budget comparison, not a lower bound on true errors.')
add('R-ode70',R,'repair_results.md',87,87,'L^4 C > H_70 on the stated ray.','All real L>=95 inclusive.',repR,keys=('repair_ram_receipt.txt',))
for i,l in enumerate((root/'repair_ram_receipt.txt').read_text().split('\n'),1):
    if l.startswith('profile '):
        _,k,b0,b1=l.split()
        a=71+i
        assert f'H_{{{k}}}' in (root/'repair_results.md').read_text().split('\n')[a-1]
        st=f'r(x)>H_{k}(L)'
    elif i in (13,15):
        if i==13: k='100';a=71;b0='3199/16';b1='2749/16';st='r(x)>1+14/L+100/L²'
        else: k='6';a=72;b0='3529/16';b1='2987/16';st='r(x)>H_6(L)'
    else:continue
    add('R-repair-'+k,R,'repair_results.md',a,a,st,f'All real L>= {b0} on B0 and >= {b1} on B1, inclusively.',repR,keys=('repair_ram_receipt.txt','ram_receipt.txt'),prop=prop('osc',f'Matched lower profile {st} from L={b0} vs {b1}, incl., same algorithm/parameters except cap.'),supplement=[('repair_ram_receipt.txt',i,i if i<=12 else i+1),('candidate.md',7,7)] if k in ('100','69') else [('repair_ram_receipt.txt',i,i if i<=12 else i+1)])
add('R-fixed49-refined',R,'repair_results.md',93,93,'r(x)>1+14/L+c/L² with c=7.5 on B0 and c=79.9 on B1.','Every real L>=49.1, inclusive.',(rs,'CH2 block extension to 58; both shifted/unshifted loss bounds, adaptively bisected blocks to 240, monotone spectral-only ray thereafter.', [('fixed49.py',5,37),('ram_early.py',3,18),('cert.py',98,131),('cert.py',173,186)]),keys=('fixed49_receipt.txt','early_receipt.txt','ram_receipt.txt'),prop=prop('R','At matched L>=49.1 the tested c rises from 7.5 to 79.9; CH proof of the initial blocks is the same.'),supplement=[('candidate.md',7,7)])
add('M-P-interval',M,'mertens.md',149,149,'Given Y in [y_-,y_+], |exp(gamma)L P-1| <= max(exp(-y_-)-1,1-exp(-y_+)); an observed relative delta<1 gives the negative of [log(1-delta),log(1+delta)] for Y.','Real x>1 on legal Y intervals.',model('full-pointwise'),strict='Non-strict except prerequisite delta<1.')
add('M-Q-interval',M,'mertens.md',149,149,'Given Y in [y_-,y_+], |exp(-gamma)Q/L-1| <= max(exp(y_+)-1,1-exp(y_-)); an observed relative delta<1 gives [log(1-delta),log(1+delta)] for Y.','Real x>1 on legal Y intervals.',model('full-pointwise'),strict='Non-strict except prerequisite delta<1.')
add('M-main-summary',M,'candidate.md',8,8,'All four observables have B0 early inverse-log and B0/B1 improved spectral rays; strongest new inverse-log coefficients and stable matched power comparison.', 'Each component on inclusive real ray specified in detailed inventory.',(ms,'See M6 and every finite / repaired branch; same operator at both caps with all B0 branches retained.',[('mertens.py',45,62),('m_tail_extra.py',3,30),('bridge_opt.py',4,21)]),status=equiv,keys=('m_tail_extra_receipt.txt','sieve_opt_receipt.txt','repair_m_receipt.txt'),prop=prop('M'),ret=['M-M6','M-extra-tail-dominance','M-new-opt-0','M-new-opt-1','M-new-opt-2','M-bridge-strong'])
add('R-main-summary',R,'candidate.md',7,10,'Ramanujan advertised earliest analytic sign, exact permanent real root, matched improved 100 margin, 49.1 coefficients and H_69 branch.', 'Each component on its stated real or integer ray, see underlying rows.',(rs+oldp,'Summary of separately assessed full-width rows and literature sign bridge.',[('repair_ram.py',62,103),('fixed49.py',5,37),('endpoint.py',12,25)]),status=equiv,keys=('endpoint_receipt.txt','repair_ram_receipt.txt','fixed49_receipt.txt','early_receipt.txt'),prop=prop('osc'),ret=['R-margin-0','R-local','R-permanent','R-repair-100','R-repair-69','R-fixed49-refined'])

for r in claims:
    if r['claim_id'] in ('R-PNT-literally-false','R-inherited-integer','R-inherited-real','R-permanent'):
        r['remaining_trust']+=' Local unit interval is independently replayed; huge finite signs retained as quoted original literature results.'
    if r['claim_id']=='M-M6':
        r['numerical_obligations']='Endpoint-directed clean and fixed-error checks, plus termwise nonincrease on the resulting rays; exact M6 applies on L>=62 without 1/(1−B_l).'
assert len({r['claim_id'] for r in claims})==len(claims)
kept={}
for family in (R,M):
    kept[family]=[r['claim_id'] for r in claims if r['family']==family and r['M_status'] in (support, baseline)]
runs=[]
for (cmd,cwd),(file,i,r) in checks.items():
    runs.append(dict(cmd=list(cmd),cwd=cwd,file=file,run_index=i,status=r['status'],elapsed_s=r.get('elapsed_s'),stdout_sha256=r['stdout_sha256'],stderr_sha256=r['stderr_sha256']))
runs.append({k:v for k,v in docs['audit_checks.json'][0][2].items() if k not in ('stdout','stderr')})
d=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id='FOLLOWUP-C016',
    assessment_complete=True,all_claims_inventoried=True,
    reviewed_source_hashes={z['original_name']:z['sha256'] for z in idx},
    source_bibliography=orig,source_locators=sources,
    actual_verification_commands=runs,
    observed_tool_effort={'candidate_payloads_verified':len(idx),'original_pdf_text_pairs_verified':len(orig),'claims':len(claims),'program_run_records':len(runs),'formal_build_attempted':False,'whole_domain_reduction':'Proofs in review.md accompanying numerical and exact sieve evidence.'},
    family_assessments={
        R:dict(strongest_supported_portfolio=kept[R],rejected_or_incomplete_claims=['R-PNT-literally-false'],remaining_assessment_work=[],summary='All current Ramanujan mathematical branches supported at stated trust. Quoted literal original real onset is false and excluded; connected ray uses stipulated original finite literature computations. All earlier margins retained, with improved matched rays and fixed-onset gains.'),
        M:dict(strongest_supported_portfolio=kept[M],rejected_or_incomplete_claims=[],remaining_assessment_work=[],summary='All present early, intermediate and tail bounds are supported at stated trust. Three exact historical gaps closed by the current same-domain repaired enclosure, with further 17 reciprocal starts, independent B0 inverse-log improvements and cap-dependent B1 power improvements for all observables.')
    },claims=claims,
    no_other_arm_or_ranking_seen=True,new_core_math_salvage_performed=False,original_candidate_bytes_changed=False,
    formal_evidence='No project Lean in this runtime. No Lean/kernel or source-first PV check or claim; separate from mathematical support.',
    own_history='Own 142-object map used for inventory/locations only; independently reassessed with original papers and current executions. No status or earlier review output used as a premise.',
    input_comparison='B0 cumulative seven originals; B1=B0+D02. D01 unavailable. B0 reconstruction means same-method ablation, not blind baseline discovery.',
    caveat='Library rounding and compiler execution at ordinary computation trust; source PDF identities verified, line-numbered original extracts used; large published computations not independently rerun.')
(out/'review.json').write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
(out/'STAGE_STATUS.json').write_text(json.dumps(dict(ready_for_review=True,families={k:dict(status=support,claim_files=['review.md','review.json']) for k in (R,M)},serious_attempts_documented=True),indent=2)+'\n')
print(len(claims),'claims',len(runs),'commands')
