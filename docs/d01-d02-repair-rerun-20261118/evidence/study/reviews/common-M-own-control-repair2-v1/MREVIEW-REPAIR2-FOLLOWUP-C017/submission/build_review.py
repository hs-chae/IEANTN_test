"""Bind independently assessed claims to exact locked names/physical LF and receipts."""
from pathlib import Path
import hashlib, json, re, sys
from zipfile import ZipFile
S=Path(__file__).resolve().parent
A=Path(sys.argv[1] if len(sys.argv)>1 else '/work/exact')
T=Path('/task')
H=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_text())
dump=lambda p,j:p.write_text(json.dumps(j,ensure_ascii=False,separators=(',',':'))+'\n')
idx=read(T/'CANDIDATE_INDEX.json')
src=read(T/'SOURCE_INDEX.json')['sources']
index={r['original_name']:r for r in idx['candidate_files']}
for name,r in index.items():
    assert H((A/name).read_bytes())==r['sha256']
packet={r['packet_name']:r for r in idx['candidate_files']}
archive_packet={
 'prior_candidate.zip!ramanujan.md':'CANDIDATE_090.md',
 'prior_candidate.zip!finite.md':'CANDIDATE_088.md',
 'before_own_repair.zip!repair_evaluate.py':'CANDIDATE_083.py',
}
def bind(f,l,r=None):
    if '!' in f:
        z,p=f.split('!',1)
        with ZipFile(A/z) as zf: b=zf.read(p)
        hh=H(b)
    else:
        hh=index[f]['sha256'] if f in index else H((T/f).read_bytes())
    canonical=archive_packet[f] if '!' in f else index[f]['packet_name'] if f in index else f
    data=(T/canonical).read_bytes()
    assert H(data)==hh
    n=data.count(b'\n')+int(bool(data) and not data.endswith(b'\n'))
    assert 1<=l<=n,(canonical,l,n)
    if r is not None: r=min(r,n)
    return dict(file=canonical,physical_LF=l,sha256=hh,**({'end_physical_LF':r} if r is not None else {}))
def refs(*vs): return [bind(*v) for v in vs]
def locs(fd):
    f=fd['file']
    if f=='OWN_ORIGINAL_021.md': f='prior_candidate.zip!ramanujan.md'
    if f=='OWN_ORIGINAL_010.md': f='prior_candidate.zip!finite.md'
    return bind(f,fd['physical_LF'],fd.get('end_physical_LF'))

SOURCES={
 'S1':'OpenAIQRH PDF p.4 Thm 1.1 and p.7 reflection; FiniteRH p.2 Thm 1; INPUT_CONTRACT.json',
 'S2':'Dusart PDF pp.3–5 (2.1), Thm 2.3; FKS pp.4–5 (2.1), Rem. 2.2 and Table 1; CH2 pp.43–44 §B.1, Lemma B.5',
 'S3':'CH2 pp.3,34–36 Cors.1.2/1.3, Prop.9.1, Lemma 9.2; FiniteRH p.4 Cor.1; Dusart pp.7–9 Props./Tables; FKS p.2 and pp.21–23, PT pp.2–3',
 'R1':'PT p.7 (11), p.8 finite pi bound, pp.9–10 Lemma 6, p.3 Cor. 2; Dudek–Platt p.8 sign check; Dusart Thm 4.2, Prop. 4.4 proof; CH2 Lemma 9.2',
 'R2':'PT p.7 (11); self-contained anchors/polynomial; shared S',
 'R3':'PT pp.3,7–10; Dusart PDF pp.11–13; CH2 pp.3,35; shared S',
 'R4':'Dudek–Platt p.2 Thm 1.2, pp.8–10 §3.1, Lemmas 3.3/3.4; PT p.3 Thm 2, p.11 tail proof',
 'R5':'Shared S and PT pi alternatives in R1, supplemented by selected comparison barriers',
 'M1':'Dusart PDF pp.17–19 Thms 5.6/5.7/5.9; CH2 pp.3,34–36 Cor.1.2/1.3, Prop.9.1, Lemma 9.2',
 'M2':'Dusart PDF p.11 Thm 4.2, pp.12–13 Props. 4.3/4.4, Cor.4.5, pp.17–19 (5.7), Thm 5.7; PT pp.7–8; CH2 p.3',
 'M3':'CH2 pp.3,35; PT p.8 finite li comparison; shared S and Dusart Thm 4.2, Prop.4.4',
 'M4':'Shared S; CH2 pp.3,34–36; Dusart Thm 4.2, Prop. 4.4',
 'M5':'Dusart PDF pp.11,17–19 Thms 4.2,5.6/5.7/5.9; analytic joins M3/M4, plus exact arithmetic',
}
checks={
 'S1':'Locally normal convergence of Euler integral leaves only pole at 1; symmetry supplies inclusive lower cap, finite RH unchanged.',
 'S2':'Check count normalization and derivative measure; pair reflection and signs, integrate positive excess. Average explicit formula in L²; primitive is absolutely summable after integration. Default derivative and secant convexity checked.',
 'S3':'Checked printed whole-ray table rows, real and finite guards and normalization; see S in review.md and exact cell receipts.',
 'R1':'Check signed J weights and partial summation, separately eligible widths at L and L−1. Upper count is nonnegative before squaring.',
 'R2':'Strict factorial anchors and derivative remainder; positive infinite tail dropped, negative finite terms retained; check v=L,L−1 separately.',
 'R3':'Closed compact slabs plus scaled analytic derivative test on full tails; exact polynomial coefficients and both shifted penalties screened. See R3 in review.md.',
 'R4':'Exact local counts plus monotone interpolation of inherited integer sign and overlap with strict B0 analytic tail. See R4.',
 'R5':'Selected formula comparisons with B0 endpoint barriers; narrower cap and primitive, positive square, and correctly scaled Horner interval for code.',
 'M1':'Check exact constants, Stieltjes endpoint convention, frequency cancellation and signed CH2 sigma branch. See M1.',
 'M2':'Prime-power signs and integrability of tail transfers; exact exponential images rather than swapping log with relative error.',
 'M3':'Decreasing scaled majorants on each closed analytic piece; finite cutoff joined to integrable true power bounds. See M3.',
 'M4':'Default ratio monotonicity, convex fixed-width slabs, signed transfers and legal product conversion; matched ratio exp(−u/32).',
 'M5':'Exact prefixes and guards for real prime slabs or full interval blocks, then analytic overlap and infinite tail; see M3–M5.',
}
default_receipt={
 'S1':['source_audit'],'S2':['certify','repair_spectral','second_m'],
 'S3':['source_audit','check_evidence'],'R1':['certify','evaluate-log_200'],
 'R2':['certify','repair_joins','repair_r'],'R3':['certify','repair_r','second_r','compact_r'],
 'R4':['source_audit','endpoint','root_zoom','certify'],'R5':['certify','fixed_x_check','second_m','ancillary'],
 'M1':['source_audit','certify'],'M2':['certify','repair_evaluate-log_200'],
 'M3':['certify','repair_joins','second_m'],'M4':['certify','repair_spectral','second_m'],
 'M5':['finite_mertens','finite_joins','finite_zoom','repair_finite','second_finite','power_prefix','second_m'],
}
ok='supported_at_stated_trust_tier'; base='baseline_retained'; weak='equivalent_or_weaker'; false='false_with_specific_counterexample'
rows=[]
def add(id,family,w,statement,dom,g,impl=(),tier='B0',strict='as written', status=ok, gap=None,
        receipts=None,role='active statement',comparison=None,also=(), source=None, readback=None):
    if receipts is None: receipts=default_receipt[g]
    if comparison is None:
        if tier=='B0+D02':
            comparison='Same target/normalization and B0 cap 7/8; the submitted matched onset or coefficient (see corresponding portfolio row).'
        else: comparison='Common/B0 result or incumbent; no incremental D02 credit.'
    prop={'input_used':'exact PsiMajorant' if 'D02' in tier else 'none beyond common B0',
          'where_it_changes_proof':('Cap 27/32 instead of 7/8, hence normalized damping exponent 5/32 instead of 1/8, via S1; direct use on u>=200 only for the raw branch.' if 'D02' in tier else 'Not a D02 propagation claim.'),
          'matched_comparison':comparison}
    bw=bind(*w) if isinstance(w,tuple) else w
    if readback is None:
        f=bw['file']
        if '!' in f:
            z,n=f.split('!'); zz=ZipFile(A/z); payload=zz.read(n); zz.close()
        else: payload=(T/f).read_bytes() if (A/f).exists() else (T/f).read_bytes()
        ls=payload.decode().split('\n')
        j=bw['physical_LF']
        readback=' '.join(x.strip() for x in ls[j-1:min(j+2,bw.get('end_physical_LF',j))]).strip()
    rows.append(dict(claim_id=id,family=family,written_source=bw,exact_statement=statement,
       full_domain=dom,strictness=strict,real_or_integer=('integer then real interpolation' if id in ('R-int','R-connected') else ('zeros with multiplicity' if id=='C-cap' else 'real')),
       assumptions=tier,claim_role=role,source_locators=source or SOURCES[g],
       written_readback=readback,also_written_at=list(also),actual_implementation=list(impl),
       baseline_comparison=comparison,derivation_check=checks[g],
       numerical_obligations='See review.md §'+g+' and receipts.',
       actual_verification_receipts=[p+'.stdout' for p in receipts],
       retained_valid_branches=('Both active portfolios; historical issue not a dependency.' if status==false else 'All eligible maxima/minima retained.'),
       M_status=status,precise_gap_or_counterexample=gap,propagation=prop,
       V_status='Not checked; no Lean/PV claim.',
       remaining_trust='Pinned literature; Decimal/integer execution where used.'))

# Own prior 666-item catalogue is used strictly as catalogue metadata: identity, statement,
# domain and code locators. No historical verdict, derivation, or receipt is imported.
targets=read(A/'OWN_PRIOR_M_023.json')['claims']
def group(i):
    if i=='C-cap':return 'S1'
    if i=='C-original' or i.startswith(('C-source-', 'M-theta-source-')):return 'S3'
    if i.startswith('C-'):return 'S2'
    if i.startswith(('R-int','R-original-real','R-local-root','R-connected','R-tail-original')):return 'R4'
    if any(s in i for s in ('envelope-gain','obstruction','refined-point','code-x-mode','eval-log-example')) and i.startswith('R-'):return 'R5'
    if i.startswith(('R-anchor','R-poly','R-regular','R-piece','R-asym','R-continuous-tail')):return 'R2'
    if i in ('R-J','R-Buethe','R-theta','R-signed','R-PTpi','R-point'):return 'R1'
    if i.startswith('R-'):return 'R3'
    if i.startswith(('M-norm','M-M1','M-original','M-general-sigma','M-direct-D02')):return 'M1'
    if i.startswith(('M-M2','M-powers','M-envelope','M-theta','M-pi','M-eval-log')):return 'M2'
    if i.startswith(('M-log','M-three','M-cheap','M-extension-join','M-code-medium')):return 'M3'
    if i.startswith(('M-power','M-refined','M-separation')):return 'M4'
    return 'M5'
B0inc={'C-original','R-Buethe','R-signed','R-PTpi','R-int','R-tail-original'}
tierboth={'C-cap','C-density','C-layer','C-smoothing','C-cont','C-primitive','C-secant-count','C-secant-psi',
          'R-J','R-point','R-poly','R-asym','R-tail-certificate','R-continuous-tail','R-continuous-tail-64','R-code-x-mode',
          'M-M1','M-M2','M-envelope','M-refined-power-coefficient','M-eval-log-example','R-eval-log-example'}
propdirect={'R-envelope-gain','R-refined-point','M-separation','M-refined-point','M-refined-ratio','M-refined-early-bridge','M-power-167-join','M-direct-D02'}
tableloc={}
for l in (S/'check_evidence.stdout').read_text().splitlines():
    if not l.startswith('table row '):continue
    m=re.match(r'table row (\d+) (\d+) (.*) (\S+\.txt) (\d+) (\[.*\])',l)
    assert m,l
    j=int(m[1]); tag=m[3]
    # order in the receipt is all steps, then all shapes.
    tableloc.setdefault('steps',[]).append(f'{tag}; original {m[4]} LF {m[5]}, cells {m[6]}')
assert len(tableloc['steps'])==122+41

for t in targets:
    i=t['claim_id'];g=group(i)
    st=t['exact_statement'];dom=t['full_domain']; w=locs(t['written_source'])
    role='source alternative' if i in B0inc or i.startswith(('C-source-','M-original-','M-theta-source-')) else 'active/retained statement'
    status=base if role=='source alternative' else ok
    gap=None; source=None; comp=None; rp=None
    if i.endswith('-D02') or i in propdirect: tier='B0+D02'
    elif i in tierboth: tier='B0 or B0+D02, as indicated'
    else: tier='B0'
    if i.startswith('C-source-'):
        _,_,which,x=i.split('-'); j=int(x)
        if which=='steps': source=tableloc['steps'][j]
        else: source=tableloc['steps'][122+j] if j<41 else 'FKS PDF p.2 Cor.1.4; executable duplicate restricted to u>=1'
    if i.startswith('M-theta-source-'): source='Dusart2018 PDF p.11 Thm 4.2; executable t=max(0,1−delta); use weak k=0 at x=1'
    if i in ('R-regularity','R-code-x-mode','M-code-medium-conversion','M-finite-only','R-eval-log-example','M-eval-log-example'):
        if i=='R-regularity':
            role='withdrawn historical assertion'; status=false
            gap='L=32: left-minus-right N20 remainder in (6.8283e−12,6.8284e−12), yielding a jump in the negative square at the common positive bracket.'
            rp=['repair_joins']
        if i=='R-code-x-mode':
            w=bind('before_own_repair.zip!repair_evaluate.py',31,35)
            role='superseded historical implementation'; status=false
            gap='x=10^70: old scaled lower endpoints >737000000, true scaled R<1.1 by reversed normalized pi bounds.'
            rp=['ancillary','fixed_x_check']
        if i=='M-code-medium-conversion':
            w=bind('certify.py',170,173);st='Live medium-range product conversion uses q=(z+u²e^(−u))/(1−e^(−u)) in both factors q exp(q/u³).'
        if i=='M-finite-only':status=weak; role='qualified old finite-only result; now joined by the extensions'
        if i in ('R-eval-log-example','M-eval-log-example'):
            role='retained historical point-log illustration, not the latest evaluator output'
            rp=['historical_log','repair_evaluate-log_200']
    if i=='M-direct-D02':
        status=weak;comp='Lawful direct transfer but dominated by spectral D02 from u>=200; not credited as new propagation.'
    if i in ('R-refined-point','R-envelope-gain','M-refined-point','M-separation'):
        comp='Strict separation of that selected mathematical estimate, not every conceivable common bound or all numerical maxima.'
    if i=='R-PTpi': st='For v>=2000 both normalized pi error sides can use 235 v^1.52 exp(−.8 sqrt(v)), with V=int_2^x 1/log.'
    if i=='R-connected':dom='Exact terminal ray (r,infinity) for strict positivity; equality at r, nonnegative ray [r,infinity); integer last failure n.'
    if i=='M-refined-power-coefficient': rp=['repair_spectral','ancillary']
    if i.startswith('M-zoom-'): dom=dom.replace('replay_finite_zoom.py.txt','finite_zoom.stdout')
    impl=[locs(q) for q in t['actual_implementation'] if isinstance(q,dict) and 'file'in q]
    if i=='R-code-x-mode':impl=refs(('before_own_repair.zip!repair_evaluate.py',31,35),('before_own_repair.zip!repair_evaluate.py',82,92))
    if i=='M-code-medium-conversion':impl=refs(('certify.py',170,179),('mertens.py',78,92))
    if i=='R-J':impl=refs(('profiles.py',17,18),('profiles.py',141,150))
    if i=='R-connected':impl=refs(('endpoint.py',16,40),('root_zoom.py',5,29),('certify.py',124,139))
    if i=='R-regularity':impl=refs(('profiles.py',189,200),('repair_joins.py',22,26))
    extras=[locs(q) for q in t['also_written_at'] if isinstance(q,dict) and 'file'in q and q['file']!='candidate.md']
    # Do not recycle obsolete line numbers into moved live documents.
    add(i,t['family'],w,st,dom,g,impl,tier,t['strictness'], status,gap,rp,role,comp,extras,source)

# New rows: direct enumeration of the latest locked table with its physical LF.
p='second_portfolio.json'
tab=read(A/p)
ls=(A/p).read_text().split('\n')
def table_lines(key):
    i=next(i for i,l in enumerate(ls) if l.startswith('  "'+key+'"'))
    starts=[]; stop=i+1
    while not ls[stop].startswith('  ]'):
        if ls[stop]=='    [': starts.append(stop+1)
        stop+=1
    assert len(starts)==len(tab[key])
    return zip(starts,tab[key])
for pos,(line,r) in enumerate(table_lines('R_uniform')):
    k,m,L,cap=r; tier='B0' if cap==700 else 'B0+D02'
    if pos<114: mode='default monotone'; ex='second_r'; imp=('second_r.py',22,88)
    elif pos<122: mode='fixed-onset default'; ex='second_r'; imp=('second_r.py',22,94)
    else: mode='compact joined'; ex='compact_r';imp=('compact_r.py',6,47)
    add(f'R-loglayer-{pos:03}', 'Ramanujan',(p,line,line+5),
        f'Strict R3 order {k}, terminal coefficient {m}, at L>={L} ({tier}; {mode}).',
        f'Every real x>=exp({L}), including equality at the onset.', 'R3',
        refs(imp,('second_portfolio.py',11,29),('repair_evaluate.py',52,54)),
        tier,'strict',receipts=[ex,'second_portfolio'],also=refs(('own_repair.md',148,192)))
errnames=['P relative','Q relative','reciprocal sum','weighted sum']
for pos,(line,(L,C,cap)) in enumerate(table_lines('M_power')):
    tier='B0' if cap==700 else 'B0+D02'; a='1/8' if cap==700 else '5/32'
    for j,err in enumerate(errnames):
        add(f'M-loglayer-power-{pos:02}-{j}','Mertens',(p,line,line+4),
            f'{err} absolute error < {C} x^(-{a})'+('/u' if j<3 else '')+f' for L>={L}.',
            f'Closed real x>=exp({L}).','M4',
            refs(('second_m.py',12,67),('repair_evaluate.py',86,89)),
            tier,'strict',receipts=['second_m','second_portfolio'],also=refs(('own_repair.md',234,252)))
for pos,(line,(C,*on)) in enumerate(table_lines('M_finite')):
    for j,(x,err) in enumerate(zip(on,errnames)):
        add(f'M-newblock-{pos}-{j}','Mertens',(p,line,line+6),
            f'{err} absolute error < {C}/u^{3 if j<3 else 2} from x={x}.',
            f'Every real x>={x}; inclusive.', 'M5', refs(('second_finite.py',13,53),('second_m.py',81,90),('repair_evaluate.py',82,85)),
            'B0','strict',receipts=['second_finite','second_m','second_portfolio'],also=refs(('own_repair.md',368+2+pos)))
for pos,(line,(cap,C,*on)) in enumerate(table_lines('M_power_prefix')):
    tier='B0' if cap==700 else 'B0+D02'; a='1/8' if cap==700 else '5/32'
    for j,(x,err) in enumerate(zip(on,errnames)):
        add(f'M-power-prefix-{pos}-{j}','Mertens',(p,line,line+7),
            f'{err} absolute error < {C} x^(-{a})'+('/u' if j<3 else '')+f' from x={x}.',
            f'Every real x>={x}; inclusive.', 'M5', refs(('power_prefix.py',11,59),('repair_evaluate.py',90,95)),
            tier,'strict',receipts=['power_prefix','finite_mertens','second_m'],also=refs(('own_repair.md',325+pos)),
            comparison='Finite-prefix proof common arithmetic, matched tail exponent conditional; these uniform powers are a tradeoff, not universal improvement at small x.')

def extra(id,family,f,l,r,st,dom,g,im,tier='B0',strict='as written',rp=None,status=ok,gap=None,source=None):
    add(id,family,(f,l,r),st,dom,g,refs(*im),tier,strict, status,gap,rp,source=source)
Bx='B0 or B0+D02, as indicated'
extra('S-log-count','Ramanujan','own_repair.md',72,121,
      'Logarithmic count integrated upper via degree-four upper and degree-six lower moments; convex true nodes plus safe transition clipping.',
      's in [.77,b], y>=0, default h and fixed 0<h<=.1.','S2',[('log_layer.py',5,42),('log_layer.py',58,75)],Bx)
extra('S-log-high','Mertens','own_repair.md',123,144,
      'Undoubled full high weight using FKS count difference, smooth J prime derivative term and Rosser remainder.',
      't>=H, 0<h<=.1; H endpoint atom treated by left limit.','S2',[('log_layer.py',44,56)],Bx)
extra('S-log-psi','Mertens','own_repair.md',108,121,
      'E_log bounds normalized right-continuous psi; fixed-width convex normalized layer, decreasing unscaled, default scaled monotone.',
      'Fixed widths as stated at u>=100; default u>=140; original scaled-ray guards.','S2',[('log_layer.py',58,91)],Bx)
extra('R-live-x-mode','Ramanujan','own_repair.md',19,56,
      'Live x-mode lower R/(x²/L^6) endpoint, with sliced Horner scaled once and R1 scaled on full expression.',
      'Supported executable decimal x inputs with log enclosure satisfying guards; no R output below log onset 25.','R5',
      [('repair_evaluate.py',27,63),('repair_evaluate.py',107,117),('fixed_x_check.py',1,33)],Bx,rp=['fixed_x_check','ancillary'])
extra('R-new-point-poly','Ramanujan','own_repair.md',148,157,
      'Strict unscaled positive polynomial minus cost with E_log menu, fixed anchor N=30 or N=64.',
      'All real L>=141, including L−1=140 at the left join.','R3',[('second_r.py',19,62)],Bx,'strict',rp=['second_r'])
extra('R-new-compact-join','Ramanujan','own_repair.md',172,192,
      'Unscaled penalty is monotone; use right positive polynomial and r^k p(l) on every compact closed slab, then default tail.',
      'Individual closed compact slabs and overlaps in compact_r.stdout; real.','R3',[('compact_r.py',6,47)],Bx,'strict',rp=['compact_r','second_r'])
extra('R-new-point-gain','Ramanujan','own_repair.md',193,207,
      'Strict improvement of designated R1 lower profile, retaining all valid independent alternatives.',
      'All real L>=166.1; upper L strict, lower L−1 nonworse.','R5',[('repair_evaluate.py',20,25),('repair_evaluate.py',55,62),('second_m.py',69,84)],
      'B0+D02','strict',rp=['second_m','ancillary'])
extra('R-new-b0-obstruction','Ramanujan','own_repair.md',201,207,
      'Selected B0 uncertainty obstruction (.004) survives added finite-box menu; not an arithmetic limitation.',
      'v>=189 for barrier; four named fixed L onsets for obstruction.','R5',[('second_m.py',69,77),('certify.py',108,122)],Bx,rp=['second_m','certify'])
extra('R-root-precision','Ramanujan','own_repair.md',209,224,
      'Unique last zero within strict open decimal bracket (...71678638,...71678639) of width 1e-32; exact integer last failure unchanged.',
      'Real [n,n+1] bracket; entire terminal ray per R-connected.','R4',[('root_zoom.py',5,29)],rp=['root_zoom','endpoint','certify'])
extra('M-live-conversion','Mertens','own_repair.md',58,69,
      'Certified medium q retains denominator in both occurrences; finite import no longer changes parent CLI precision.',
      'All analytic medium joins, CLI log and x modes at supported precision.','M3',[('certify.py',170,179),('finite_mertens.py',40,49),('repair_evaluate.py',65,75)],rp=['certify','fixed_x_check'])
extra('M-new-power-limit','Mertens','own_repair.md',254,257,
      'Latest default power majorant limiting coefficients <.0066610 B0, <.1154620 D02 with primitive allowance.',
      'Default power coefficient as u tends to infinity.','M4',[('log_layer.py',84,93),('second_m.py',59,62)],Bx,'strict',rp=['second_m'])
extra('M-new-power-joins','Mertens','own_repair.md',257,282,
      'Compact .125 same-width slabs, CH2 middle convex joins, and .117 inverse-log bridge on [17,32].',
      'B0 [17,32],[32,185]; D02 [17,32],[32,166]; five bridges in second_m.py and closed default joins.',
      'M4',[('second_m.py',18,58)],Bx,'strict',rp=['second_m','certify'])
extra('M-power-cross','Mertens','own_repair.md',282,287,
      'Extended power coefficients cross at 32 log(.22775/.01239) in (93.16,93.18); latest u>=200 ratio <.03353 and decreasing.',
      'Matched closed log rays u>=17 and u>=200, respectively.','M4',[('second_m.py',63,67)],'B0+D02','strict',rp=['second_m'])
extra('M-new-point-gain','Mertens','own_repair.md',289,316,
      'Strict separation by D02 of all four selected explicit estimating envelopes, not all possible B0 proofs.',
      'Every real u>=166.1 via [166.1,167], [167,168] and the later power ray.',
      'M4',[('second_m.py',69,84),('repair_evaluate.py',96,104)],'B0+D02','strict',rp=['second_m','certify','ancillary'])
extra('M-new-prefix-join','Mertens','own_repair.md',327,360,
      'Monotonicity of signed power-normalized errors on certified prime slabs, or entire slab interval; actual next prime 500009 joins to old maxima and analytic ray.',
      'Real x from each power-prefix onset through 500009 to exp(17), and analytic tail.',
      'M5',[('power_prefix.py',8,59)],Bx,'strict',rp=['finite_mertens','power_prefix','second_m'])
extra('M-new-block-proof','Mertens','own_repair.md',375,400,
      'Every width 128 closed block from 30m to 100m encloses raw and normalized errors; analytic headroom joins bad-block right endpoints.',
      'Real [30000000,100000000] and analytic joins on closed rays.',
      'M5',[('second_finite.py',13,53),('second_m.py',82,94)],rp=['second_finite','second_m','certify'])
extra('M-new-query','Mertens','own_repair.md',402,407,
      'Pointwise exact finite arithmetic through 100m can join analytic minima; inclusive p<=floor(x).',
      'Supported real decimal inputs 1<x<=100000000; below 2 empty counts as usual.',
      'M5',[('finite_query.py',5,26),('repair_evaluate.py',65,71)],rp=['finite_query-10007','finite_mertens'])
extra('R-printed-original-real','Ramanujan','ramanujan.md',248,264,
      'Quoted PT Theorem 2 original printed strict real sign for n<x<=exp(58); not claimed by the candidate.',
      'The quoted early real interval; not the surviving e^3915 tail.',
      'R4',[('endpoint.py',16,31)],status=false,gap='At x=38358837682.1 exact counts 1644673232 and 632207037 give R<−7974585.',rp=['endpoint'])
# Separate baseline literal boundary issue, without calling the weakened implemented theta bound false.
extra('M-theta-k0-literal-source','Mertens','mertens.py',3,11,
      'Quoted strict k=0 Dusart theta table at printed xk=1 (only weak bound employed by candidate).',
      'Quoted range 1<=x<2; candidate theta lower convention is max(0,1−delta).','S3',
      [('mertens.py',9,11)],status=false,gap='theta(1)=0 implies |theta(1)−1|=1, not <1; the weak endpoint and all candidate transfers survive.',
      source='Dusart2018 PDF p.11 Thm 4.2, k=0 row')

cmds={}
for p in sorted(S.glob('*.status')):
    n=p.stem
    if n=='table_first_attempt':continue
    a=n.split('-')
    if n=='historical_log': c='/usr/bin/python3.10 /work/submission/historical_log.py'
    elif n=='ancillary': c='/usr/bin/python3.10 /work/submission/ancillary.py'
    elif n=='check_evidence': c='/usr/bin/python3.10 /work/submission/check_evidence.py /work/exact'
    else: c='/usr/bin/python3.10 '+a[0]+'.py'+(' '+a[1].replace('_',' ') if len(a)>1 else '')
    cmds[n]={'command':c,'cwd':'/work/exact','status':int(p.read_text()), 'stdout':H(p.with_suffix('.stdout').read_bytes()), 'stderr':H(p.with_suffix('.stderr').read_bytes())}
required=set(k.removesuffix('.stdout') for c in rows for k in c['actual_verification_receipts'])
assert required<=cmds.keys(), required-cmds.keys()
assert all(x['status']==0 for x in cmds.values())
assert len({c['claim_id'] for c in rows})==len(rows)
# Explicit active strongest identifiers (earlier and weaker branches remain listed).
Rstrong=['R-connected','R-root-precision','R-live-x-mode','R-new-point-gain','R-new-point-poly']
Rstrong+= [c['claim_id'] for c in rows if c['claim_id'].startswith(('R-loglayer-','R-refined-early-'))]
Mstrong=['M-new-point-gain','M-new-power-limit','M-new-query','M-envelope']
Mstrong+= [c['claim_id'] for c in rows if c['claim_id'].startswith(('M-loglayer-power-','M-newblock-','M-power-prefix-'))]

fam={
 'Ramanujan':dict(strongest_supported_portfolio=Rstrong,
      rejected_or_incomplete_claims=['R-regularity','R-code-x-mode','R-printed-original-real'],
      remaining_assessment_work=[], summary='Connected exact sign ray and strict analytic lower margins, with conditional shifts/gains at matched order and onset. Negative entries are historical/source assertions, not live theorem failures.'),
 'Mertens':dict(strongest_supported_portfolio=Mstrong,
      rejected_or_incomplete_claims=['M-theta-k0-literal-source'],remaining_assessment_work=[],
      summary='Both reciprocals and both prime sums supported with all real joins, B0 finite improvements and conditional spectral exponent gain. The strict k=0 source endpoint is not an employed premise.')}
review={'schema':'FOLLOWUP_MATHEMATICAL_REVIEW_V1','candidate_id':idx['candidate_id'],
 'input_stage':'D02','assessment_complete':True,'all_claims_inventoried':True,
 'reviewed_source_hashes':{v['packet_name']:v['sha256'] for v in index.values()},
 'source_bibliography':src,'actual_verification_commands':cmds,
 'family_assessments':fam,'claims':rows,'no_other_arm_or_ranking_seen':True,
 'new_core_math_salvage_performed':False,'original_candidate_bytes_changed':False,
 'own_history_policy':'Use identifiers as catalogue metadata; do not inherit mathematical verdicts or code replays. Structured locators use exact /task filenames, including the separately supplied byte-identical copies of the three historical archive members; prose preserves archive/member and original-name cross-references.',
 'verification_effort':{'method':'Independent original-source checks and analytic walkthrough plus local Python 3.10 directed-arithmetic replay.',
 'exact_restore':'/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out /work/exact',
 'reproduce':'reproduce.sh, check_evidence.py, ancillary.py, review.md',
 'trust':'Neither Lean nor source-first PV checked; inherited literature computations not reverified. No D01 premise.'}}
# Exact formula/code readbacks, deduplicated so oversized repeated code is not
# required in each claim row. These are the claims' implemented formulae, not Lean.
codes={}
for c in rows:
    for w in c['actual_implementation']:
        f=w['file']; l=w['physical_LF']; r=w.get('end_physical_LF',l)
        key=f+':'+str(l)+'–'+str(r)
        if key in codes: continue
        if '!' in f:
            z,n=f.split('!'); zz=ZipFile(A/z); payload=zz.read(n); zz.close()
        else: payload=(T/f).read_bytes()
        a=payload.decode().split('\n')
        assert 1<=l<=len(a),(key,len(a))
        codes[key]={'source':w,'physical_LF_text':a[l-1:r]}
dump(S/'code_readbacks.json',codes)
review['implemented_formula_readbacks']='code_readbacks.json, keyed by file:start–end (same line keys as actual_implementation).'
fullR={}
for pos,(k,m,L,cap) in enumerate(tab['R_uniform']):
    if pos<114 or 122<=pos<136:
        d=fullR.setdefault(k,{'coefficient':m})
        capkey=str(cap)
        if capkey not in d or __import__('decimal').Decimal(L)<__import__('decimal').Decimal(d[capkey]):
            d[capkey]=L
review['matched_latest_full_R3_onsets']=fullR
review['matched_latest_M_power_coefficients']={str(L):{str(cap):C for l,C,cap in tab['M_power'] if l==L}
    for L in sorted(set(l for l,C,cap in tab['M_power']))}
review['quoted_source_and_history_distinction']={
   'R-printed-original-real':'Refuted quotation, not asserted by candidate.',
   'M-theta-k0-literal-source':'Refuted strict source reading; actual candidate uses valid weak bound.',
   'R-regularity':'Withdrawn.',
   'R-code-x-mode':'Superseded; live check is R-live-x-mode.'}

dump(S/'review.json',review)
stage={'ready_for_review':True,'families':{k:{'status':ok,'claim_files':['review.md','review.json']} for k in fam},
       'serious_attempts_documented':True}
dump(S/'STAGE_STATUS.json',stage)
dump(S/'LOCK.json',{'files':[{'path':p.name,'sha256':H(p.read_bytes())} for p in sorted(S.iterdir()) if p.is_file() and p.name!='LOCK.json']})
print('review rows',len(rows),'bytes',(S/'review.json').stat().st_size)
