from pathlib import Path
from hashlib import sha256
import json, re, sys
root=Path('/task')
out=Path(__file__).resolve().parent
rest=Path(sys.argv[1] if len(sys.argv)>1 else '/work/locked')
def get(p):return json.loads(p.read_text())
def h(p):return sha256(p.read_bytes()).hexdigest()
index=get(root/'CANDIDATE_INDEX.json')
byname={r['original_name']:r for r in index['candidate_files']}
byhash={r['sha256']:r for r in index['candidate_files']}
for n,r in byname.items():
    assert h(rest/n)==h(root/r['packet_name'])==r['sha256']
def src(n,a,b=None,include=True):
    r=byname[n]
    ls=(rest/n).read_bytes().decode().split('\n')
    assert 1<=a<=(b if b else a)<=len(ls),(n,a,b,len(ls))
    d=dict(file=r['packet_name'],original_filename=n, physical_LF=a,sha256=r['sha256'])
    if b is not None:d['through_physical_LF']=b
    if include:d['literal_lines']=ls[a-1:(b if b else a)]
    return d
B0='B0: the seven supplied originals, at their exact applicable hypotheses and named literature/computation tier, not full RH'
D02=B0+' + the supplied inclusive real direct-ψ bound exp(200), exponent 27/32, coefficient 1/64, log power 2'
readback_catalog={}
V='Paper-only; no project Lean/Blueprint checked, no kernel or source-first PV claim'
M='supported_at_stated_trust_tier'
BASE='baseline_retained'
EQ='equivalent_or_weaker'
BAD='false_with_specific_counterexample'
GAP='incomplete_with_specific_missing_step'
srcdens=['FKS PDF p.4 LF269–274, p.7 Cor.2.9 and (2.17) LF586–608, p.26 Table 8 LF3139–3258 (first block, a1=.77)', 'FKS PDF p.8 Thm.3.2 LF631–642', 'CH2 p.43 LF6133–6181 Lemma B.1/Cor.B.2; p.41 (A.2); p.46 (B.9) LF6801–6820', 'PT PNT p.4 Lemma 2 LF236–246; PT FiniteRH p.2 Thm.1 LF48–50; OpenAIQRH p.4 Thm.1.1 LF255–262']
srcplateau=['CH2 p.3 Cor.1.2 LF193–222 (denominator T−1, verified PDF page object 51 stream 204), Cor.1.3 LF226–240; p.35 Lemma 9.2 LF5216–5223']
srcpi=['PT PNT p.7 (11), p.8 LF695–705 finite π against offset-li; pp.9–10 LF802–812 Lemma 6 θ', 'PT FiniteRH p.4 Cor.1 LF138–150 (π normalized cube), p.5 LF182–185 sign', 'CH2 p.35 LF5216–5223 finite ψ; Dusart PDF pp.12–13 Prop.4.3 and Cor.4.5']
srcsign=['DP p.2 Thm.1.2/Thm.1.3 LF53–55, p.10 Lemma 3.4 LF698–714','PT PNT PDF p.3 Thm.2 LF205–212']
srcm=['Dusart pp.17–20 Thms.5.6,5.7,5.9 and proof bounds LF1476–1722; p.11 Thm.4.2 LF959–1010; pp.12–13 Prop.4.3/Cor.4.5']
srccompare=srcdens+srcplateau+srcpi+srcsign+srcm+['PT PNT Thm.1/Table 1 pp.2–3 LF77–95,135–201; FKS Thms.1.1/1.2 and Cor.1.4 p.2 LF113–143, Tables 5/6']
claims=[]
def row(cid,f,n,a,b,st,dom,impl,checks,receipts,*,prem=B0,strict='as stated',status=M,baseline='Within-method comparison, see review.md',where='',gap=None,sources=None,integer=False,secondary=False,scope='current'):
    w=src(n,a,b)
    reads=[]
    for p in impl:
        d=src(*p)
        key=d['file']+':'+str(d['physical_LF'])+'-'+str(d.get('through_physical_LF',d['physical_LF']))
        readback_catalog[key]=d
        reads.append({**{k:v for k,v in d.items() if k!='literal_lines'}, 'readback_key':key})
    claims.append(dict(claim_id=cid,family=f,written_source=w,exact_statement=st,assumptions=prem,full_domain=dom,
       strictness=strict,real_or_integer='integer' if integer else 'real arguments (inclusive counts/sums) or stated complex strip',
       baseline_comparison=baseline,source_locators=sources or (srcdens+srcplateau+(srcpi if f=='Ramanujan' else srcm)),
       derivation_check=checks,numerical_obligations='Read actual algorithm and verify directed bounds and complete finite coverage/analytic monotonicity where required; see proof, implementation and receipts.',
       actual_verification_receipts=receipts,retained_valid_branches='All other eligible supported leaves at their exact endpoints survive in the appropriate signed intersection or max/min.',
       M_status=status,precise_gap_or_counterexample=gap,
       propagation=dict(input_used=prem==D02,where_it_changes_proof=where or 'None (B0, retained comparison or source status)',matched_comparison=baseline),
       V_status=V,remaining_trust='Named original theorems and original published numerical results at literature trust, plus ordinary checked execution where cited and written analysis; no new external premise.',implementation_readbacks=reads,
       scope=scope,secondary=secondary))
# Shared results enter both families, not independent tests.
for f in ('Ramanujan','Mertens'):
    pre=f[0]+'02-'
    row(pre+'strip',f,'D02_PROOF.md',5,15,'D02 implies β≤27/32 for all nontrivial ζ zeros; conversely under B0 this strip implies the exact D02 contract. Finite RH remains separate.',
        'Re s>27/32 zero exclusion; reverse for all real L≥200',[('d02_density_new.py',85,94),('d02_m_checks.py',31,42)],
        'Pole-subtracted integral is holomorphic locally uniformly. Reverse via decreasing F and F(200)<.260 versus 625.',
        ['run_d02_density_new.py.txt','run_d02_m_checks.py.txt'],prem=D02,where='Closed strip shortened before any local prime transfer.',
        baseline='B0 and B0+D01 only use 7/8 in same proof; no logical independence from B0 claimed.')
    row(pre+'density-moments',f,'D02_PROOF.md',19,51,'Two directed reciprocal moment bounds, with initial-band subtraction and eligible full closed staircase clip; strict majorant improvement over same B0 quadrature.',
        's in [.70,b], t≥H; moment orders 1,2; L>0', [('d02_density_new.py',38,83),('d01_cert.py',31,51)],
        'Cor.2.9 closed row, positive ordinate; Tonelli, quartic integral, separate two-sided count error, running min, and clipped layer integral.',
        ['run_d02_density_new.py.txt','supplement_receipt.txt'],prem=D02,where='D02 clips positive portion above 27/32; initial-band quadrature improvement also available with B0.', baseline='Same nodes/weights through b, additional positive interval for B0; not an assertion about actual zero mass.')
    row(pre+'psi-coefficient',f,'D02_PROOF.md',55,61,'Relative ψ ≤ F_d(L)e^(−dL), with decreasing factored F_d and <.260 e^(−5L/32) from 200.',
        'all real L≥40 for function; L≥200 for .260',[('d02_density_new.py',85,94),('d02_m_checks.py',31,42)],
        'FKS real-x truncation; low β sum and high first moment, with monotonic coefficients.',
        ['run_d02_density_new.py.txt','run_d02_m_checks.py.txt'],prem=D02,where='Only high-β moment changes.',baseline='Improves on raw D02 log² coefficient; original 1/8 coefficient remains as B0 comparison.')
    row(pre+'CH2-plateau',f,'D02_PROOF.md',63,68,'Relative ψ ≤q+113.669378e^(−L/2), q=1.047136353e−12; keep original signed CH2 interval on its own domain.',
        'all real L≥40 for new rounded leaf; original x>max(T,10^9), T≥10^7 and finite RH through T',
        [('d02_density_new.py',6,11),('d02_density_new.py',113,115)],
        'Original p.3 fraction denominator T−1, not favorable −1/x. Using π_upper/(H−1)+(π_upper/H)^2 < exact same q is sufficient, checked separately. Signed leaf uses true radius.',
        ['original_pdf_objects.txt','supplement_receipt.txt'],secondary=True,sources=srcplateau,baseline='B0 refinement with exact H, no propagation.')
    row(pre+'CH2-paraphrase',f,'D02_PROOF.md',68,None,'Favorable −e^(−L) radius term attributed to CH2 Cor.1.2 (only the source-paraphrase fragment, not the symmetric cap).',
        'same L≥40 use of finite-RH through exact H',[('d02_density_new.py',113,115)],
        'The actual relative radius has π/(T−1), not this term.', ['original_pdf_objects.txt','supplement_receipt.txt'],
        status=GAP,scope='source-paraphrase not used as an independent theorem',
        gap='No such signed improvement follows from Cor.1.2. Use the authentic signed radius. The rounded symmetric cap is supported separately by a directed check with the actual denominator.',sources=srcplateau)
    row(pre+'primitive',f,'D02_PROOF.md',70,78,'|Uψ(L)|≤.0463e^(−L/2)+J_d(L)e^(−dL)+2e^(−L), J=(13e^(−(.3−d)L)+B2)/H; high term may instead use 3.2e−12e^(−dL).',
        'all proof-bearing L≥18, including integration from 18,29.9,40; primitive identity holds L≥0',
        [('d02_density_new.py',89,92),('d02_density_new.py',101,112),('d01_smooth.py',70,84)],
        'Absolutely convergent Laplace identity, exact both-sign reciprocal differences, Tonelli; high unfactored coefficient is sum of exponentials with rates d to .30.',
        ['run_d02_density_new.py.txt','replay_analytic.jsonl'],prem=D02,where='High second-moment spectral tail shrinks.',baseline='B0 rate 1/8 version remains and crude fallback is legal.')
# Current Ramanujan dependencies and targets.
r='D02_RAMANUJAN.md'; F='Ramanujan'
ramfinite=[('d02_ram_new.py',8,53),('d02_ram_checks.py',10,43)]
ramtail=[('d02_ram_new.py',55,101),('d02_ram_checks.py',48,68)]
ramn=['run_d02_ram_checks.py.txt','run_d02_ram_checks.py_finite.txt']
row('R02-convolution',F,r,44,56,'Signed Δ−dθ bracket using .155, 2.6J_d, .074, 2.36 and signed 1.9998 convolution; subtract Dusart prime powers from eligible ψ leaf for dθ.',
    'real u≥40, with θ finite leaf only where eligible', [('d02_ram_new.py',8,24),('ram_repair.py',240,258)],'Partial summation at s=29.9; integration by parts with each rate ≤.3, literal signed terms and directed anchor constants.',
    ['run_d02_density_new.py.txt','replay_ram.jsonl','anchor_checks.txt'],prem=D02,where='High J and local F shrink; old anchor charges unchanged.')
for N,B,A in [(20,40,170),(40,64,100),(80,128,11000)]:
    row(f'R02-li-{N}',F,r,58,63,f'H_{N}(u)≤u PV-li(e^u)e^(−u)≤H_N+V_N, anchor B={B}, A={A}',f'all real u≥{B}',
        [('d02_ram_new.py',55,74)],'Exact positive PV series residual at B; derivative comparison gives remainder cost B/(B−N−2).',ramn,secondary=True)
row('R02-two-argument',F,r,65,79,'Use eligible positive F_- and F_+ separately at L and L−1 in the lower and upper R L²/x² bracket; fixed-order debit as written.',
    'real L>1 wherever both argument brackets apply (new convolution at L≥41 for both)',ramfinite+ramtail,
    'Algebraic rescaling and monotonic square; signed finite costs, frozen-tail h_A, and positive inputs checked.',ramn,prem=D02,where='Both shifted and unshifted spectral caps update.')
for a,b,z,l in [('47.647',None,'8.39',16),('48.27',None,40,16),('47.677',None,10,17),('48.49',None,50,17),('47.955',None,25,18),('49',None,70,18),('48',None,27,19),('49.30',None,80,19),('49.31',None,'80.6',20),('171.85',None,100,20),('172',None,100,21),('176',None,119,21),('180',None,133,22),('176','187',120,24)]:
    domain=f'[{a},{b or "∞"}) in L' if b is None else f'[{a},{b}] in L'
    row(f'R02-quad-{a}-{z}',F,r,l,None,f'Y>1+14/L+{z}/L²',domain,ramfinite+ramtail,
       'Directed closed cells through 172 then +93 tail for earlier entries; direct frozen onset comparisons for later rays; finite +120 only checked on [176,187].',
       ramn,prem=D02,strict='strict lower; all finite endpoints inclusive',where='New F and J reduce independent costs at both arguments; plateau switch is earlier.',
       baseline='Compare exact eligible old B0/D01 pointwise branches, including disconnected +100 [50,158] and connected +8.34.')
for a,b,z in [('52.99','123',0),('56','106',1050),('56','105',1060)]:
    row(f'R02-cubic-{z}',F,r,26,None,f'Y>1+14/L+145/L²+{z}/L³',f'all real L∈[{a},{b}]',
       ramfinite,'For 145 alone overlap [52.99,122] and [53,123]; other cubic branches have individually checked tops.',ramn,prem=D02,
       strict='strict lower, closed domain',where='Same D02 clipped error caps; early B0 finite π and θ headroom is retained.',baseline='Old +1050 finite to 105; compare overlapping ranges separately.')
onsets=[
(7,36,'187 211.5 237 263 289 316 343 369 396 423 451 478 505 535'),
(21,37,'559 587 614 641 669 696 724 751 778 806 833 861 888 916 943 971 998 1026 1053 1083.9'),
(41,38,'1108 1136 1163 1191 1218 1246 1273 1301 1328 1356 1383 1411 1439 1466 1494 1521 1549 1576 1604 1631 1659 1687 1714 1742 1769 1797 1824 1852 1879 1907 1935 1962 1990 2017 2045 2073 2100 2128 2155 2185.9')]
for j0,l,s in onsets:
    for j,a in enumerate(s.split(),j0):
        row(f'R02-full-{j}',F,r,l,None,f'Y>∑_(k=4)^{j-1} C_k/L^(k−4), C_k given at LF32',f'all real L≥{a}',ramtail,
           'Subtract target before scaling; shift expansion nonnegative through N, pay square tail and shifted/unshifted debits; L^N scaled negative magnitudes decrease.',
           ramn,prem=D02,strict='strict lower, closed ray',where='Smaller F and J and faster exponential leave positive factorial slack.',
           baseline=('B0 full +145 from L=221' if j==7 else 'B0 same estimator fails at 559 (shifted debit alone)' if j==21 else 'Matched strength and valid B0 onsets retained, no claims of global optimality.'))
for j,a,half,prem in [(20,546,True,D02),(40,1096,True,D02),(80,2197,True,D02),(80,2889,False,B0),(80,2899,True,B0)]:
    row(f'R02-{a}-'+('half' if half else 'full'),F,r,40,None,f'Y>∑_(k=4)^{j-1} C_k/L^(k−4)'+(f'+C_{j}/(2L^{j-4})' if half else ''),
      f'all real L≥{a}',ramtail,'Keep residual half C_j as positive scaled allowance where selected; same monotonic tail proof.',ramn,prem=prem,secondary=prem==B0,
      strict='strict lower, closed ray',where='Reduced spectral debits for D02 version' if prem==D02 else '',
      baseline='For j=40 half-term old B0 1431; for j=80 compare 2197/2899 at same half-term.')
for i,(c,a,prem) in enumerate([('28',3000,D02),('27.8',6700,D02),('27.7',19000,D02),('27.65',190000,D02),('38',3000,B0),('37',12000,B0),('36.9',40000,B0)],95):
    row(f'R02-variable-{c}',F,r,i,None,'Y>∑_(k=4)^(n−1) C_k/L^(k−4)+C_n/(2L^(n−4))',f'all real L≥{a}, every integer 40≤n≤L/{c}',
        [('d02_variable.py',5,32),('d02_ram_new.py',81,88)],
        'Split li at exp(u/2); analytic uniform square-tail and factorial exponential gap; total normalized cost <1/4 at onset and decreases.', ['run_d02_variable.py.txt'],
        prem=prem,secondary=prem==B0,strict='strict lower, include both L and integer n boundaries',
        where='Larger spectral exponent permits smaller c at comparable onset.' if prem==D02 else '',
        baseline='Compare c=28 vs c=38 at L=3000 and other onset/strength tradeoffs.')
for a,b,z in [('27.704',None,'.04'),('28.17',None,'.30'),('29.105',None,'.70'),('30.577',None,'1'),('27.8',None,'.098'),('28.3',None,'.367'),('29.2',None,'.734'),('34.3','43.7','1.406'),('30.75','388','1.037'),('30.714','477.005','1.03')]:
    row(f'R02-early-{a}-{z}',F,r,125 if z=='1.03' else 123,None,f'Y>{z}',f'all real L≥{a}' if b is None else f'all real L∈[{a},{b}]',
      [('early_new.py',9,69),('d02_variable.py',33,46),('ram_repair.py',196,238)],
      'PV residual and signed whole cells meet earlier supported tails; [30.75,388] uses +16 and then +145; [388,477.005] uses retained B0 j=9.',
      ['run_early_new.py.txt','run_d02_variable.py.txt','replay_ram.jsonl','supplement_receipt.txt'],secondary=True,sources=srcpi+srcdens,
      strict='strict lower, closed endpoints',baseline='Input-independent early B0 improvements; finite 1.03 not the archived false infinite assertion.')
row('R02-global-scope-correction',F,'D02_SCOPE_CORRECTION.json',1,None,'At L=1000 B0 implies Y<1.015, refuting inherited global Y>1.03; replace with finite [30.714,477.005].','counterexample at x=e^1000; replacement closed slab',
    [('d02_variable.py',33,46)],'Directed upper two-argument bracket with positive lower π input; numerical bound 1.01414642614.', ['run_d02_variable.py.txt','run_early_new.py.txt'],
    secondary=True,baseline='Removes false prior global constant but no other supported profile.')
row('R02-matched-debit',F,'D02_COMPARISON.md',14,None,'B0 matched j=21 sufficient recipe fails at 559; connected +80.6 needs reduced late-plateau cost in the written independent method.', 'point checks at 559 and 189.12; not a lower bound for prime error',
    [('d02_ram_checks.py',49,56),('d02_ram_new.py',25,35)],'Directed lower bound on shift debit for j=21, and exact B0 implemented sufficient allowance at the plateau.',ramn+['supplement_receipt.txt'],prem=D02,
    where='D02 reduces shifted and unshifted spectral debits.',baseline='Within-method ablation (not blind discovery or impossibility for B0).')

# Current Mertens proofs and targets.
m='D02_MERTENS.md'; F='Mertens'
mc=[('d02_m_new.py',6,47),('d02_m_checks.py',3,42),('d02_m_checks.py',54,73)]
mr=['run_d02_m_checks.py.txt','supplement_receipt.txt']
for cid,a,b,st,dom,der in [
 ('identities',3,11,'Inclusive P,Q,Z_Q,D1,D2 with Dusart centers and separate relative errors','x≥2','The centers are as printed in Dusart; both products are normalized against their own reference.'),
 ('signed',56,78,'Signed D_j envelopes using endpoint ψ, positive modeled bias B_j, signed ξ interval and I_j','L≥18; each pointwise ψ source only on its eligible domain','Stieltjes on (x,∞), prime-power difference, twice-integrated primitive zero modes, and exact trivial bound.'),
 ('weighted-endpoint',80,86,'DΛ=dψ−Uψ; D2 can use the weighted endpoint without ψ integral debit, and D1 residual is −U/L²−∫Uw1\u0027','L≥18 with each original weighted endpoint only on its eligible domain','Pole expansion fixes ∫dψ=−γ−1; integrate against the primitive with derivative of w1, preserving two signs.'),
 ('log-tail',88,96,'Exact Z_Q=D1−T1, directed reciprocal-square and higher-power tail and separate exponential conversion','x≥2 for identities/conversion; stronger tail L≥18, new density θ branch L≥40','Open-at-x prime tail sums; e^u−1 and 1−e^l for Q, inverse exponential for P.'),
 ('D1-to-D2',98,102,'|D2|≤LA(L)+∫_L^∞A(v)dv for any eligible D1 ray; integrate pointwise minimum and optional new last power leaf','real x≥2 with chosen D1 envelopes valid throughout [L,∞)','dD2=v dD1, vanish at infinity via Dusart, and exact finite step integration; new power leaf can lower the integral only where smaller.'),
 ('common-E',104,115,'Explicit common E(L) bounds L|D1|, L|Z_Q|, |D2|; relative product upper radius E/L divided by 1−E/L','L≥40 for E; relative conversion where E/L<1','Opposite signed endpoint/ξ-integral effects, crude tail correction, and safe exponential conversion; convex scaled plateau plus decreasing factored power.')]:
    conditional=cid in ('signed','weighted-endpoint','D1-to-D2','common-E')
    row('M02-'+cid,F,m,a,b,st.replace(r'\u0027',"'"),dom,mc if cid in ('signed','common-E') else [],
     der,mr if cid in ('signed','common-E','weighted-endpoint') else [],prem=D02 if conditional else B0,
     where='Use the new endpoint or primitive cap if better; identity/transfer itself holds already with B0.' if conditional else '',
     baseline='Pointwise minimum/intersection with all old eligible leaves, without stripping their original guards.')
for l,a,k,prem in [(19,'59.99','4.27e-8',B0),(20,'60.15','4e-8',B0),(21,'60.34','3.75e-8',B0),
                   (22,'60.855','2.9873e-8',D02),(23,'171','2.16e-8',D02),(24,'172','1.86e-8',D02),
                   (25,'176.18','1e-8',D02),(26,'180','5.59e-9',D02),(27,'184.2','3e-9',D02),
                   (28,'191.5','1e-9',D02),(29,'200','2.79e-10',D02)]:
    row('M02-log-'+a,F,m,l,None,f'E_Q,E_P,|D1|≤{k}/L³, |D2|≤{k}/L²',f'all real L≥{a}',mc,
         'Convex L²E and separate denominator at left on plateau through 168.901 or 189.13; decreasing power variant thereafter; later branch onsets use only the latter.',
         mr,prem=prem,secondary=prem==B0,strict='weak upper bounds, closed rays',
         where='Clipped F,J make earlier plateau-to-power join possible.' if prem==D02 else '',
         baseline='Matched old 4.3e−8 at 64.4 and 3.8e−8 at 74; B0 recipe at 188 exceeds 3.7009e−8, no proof of arbitrary B0 inferiority.')
powrows=[(37,169,'.300102'),(38,170,'.298321'),(39,190,'.269799'),(40,200,'.259244'),(41,250,'.225620'),(42,400,'.188868'),(43,600,'.173283'),
         (37,1000,'.162328'),(38,2500,'.152450'),(39,10000,'.147651'),(40,100000,'.146183'),(41,1000000,'.146038'),(42,5000000,'.146025')]
for l,a,k,dp in [(l,a,k,D02) for l,a,k in powrows]+[(45,5000000,'.010443',B0)]:
    d='5/32' if dp==D02 else '1/8'
    row(f'M02-power-{a}-{d}',F,m,l,None,f'E_Q,E_P,|D1|≤{k} x^(−{d})/L, |D2|≤{k} x^(−{d})',f'all real L≥{a}',mc,
        'All factored radius terms nonincreasing; denominator positive at A and increasing; exact directed endpoint.',
        mr,prem=dp,secondary=dp==B0,strict='weak upper bounds, closed rays',where='Clip at b and factor faster decaying exp(−5L/32).' if dp==D02 else '',
        baseline='In old exponent units .300102e^(−L/32)<.001527 on L≥169 versus old nonuniform coefficients >.01044. Compare only on common domains.')
for l,a,d,p,k in [(49,200,'9/64',1,'2.279'),(49,400,'1/8',2,'.11262'),(50,500,'1/8',3,'3.668'),(50,600,'1/8',3,'.26928')]:
    row(f'M02-trade-{a}',F,m,l,None,f'E_Q,E_P,|D1|≤{k}x^(−{d})/L^{p+1}, |D2|≤{k}x^(−{d})/L^{p}',f'all real L≥{a}',mc,
        'Use decreasing U and multiplication by L^p e^(−(5/32−d\u0027)L) past its maximum.'.replace(r'\u0027',"'"),mr,
        prem=D02,strict='weak upper bounds, closed rays',where='Spend D02 exponential gain on log factor.',baseline='Tradeoffs, not better than exact nonuniform D02 power envelope.')
row('M02-matched-log',F,m,115,None,'At L=188 the B0 symmetric recipe is >3.7009e−8 in log units; D02 whole 2.9873e−8 ray is stronger in matched recipe.',
    'point L=188 and common log rays', [('d02_m_checks.py',31,42)], 'Both B0 ψ caps at 188 ≥q; directed lower bound for its radius, not arithmetic error.',mr,
    prem=D02,where='Earlier spectral switch clips the B0 plateau contribution.',baseline='Not a limitation on other B0 proofs.')
row('M02-matched-FKS',F,'D02_COMPARISON.md',16,None,'The .300102 exp(−5L/32) relative ψ majorant beats basic FKS Cor.1.4 ψ cap throughout L≥169.',
    'all real L≥169',[('d02_m_checks.py',38,42)],'Exact left check and negative log-ratio derivative; other FKS table branches keep their domains.',mr,
    prem=D02,where='Faster power decay from strip.',baseline='Comparison to basic FKS ψ cap, not all B0 proofs or a direct comparison to another product theorem.',
    sources=['FKS p.2 Cor.1.4 LF140–143 (x>2)']+srcdens)
for label,a,b,k,dp in [('B0-85.7','log 3','85.7','.1',B0),('D02-86.99','log 3','86.99','.1',D02),
                     ('D02-86.5','84.5','86.5','.35',D02),('D02-86.75','84.5','86.75','.23',D02),('D02-87.15','log 3','87.15','0',D02)]:
    row('M02-prim-pos-'+label,F,m,119,None,f'V_y−1>{k}e^(−L/2)/L',f'all real y≥3 with L∈[{a},{b}]',
        [('d02_m_new.py',48,56),('d02_m_checks.py',60,63),('d01_smooth.py',91,123)],
        'Recenter exactly, preserve entire positive prime-power integral, convex tangent bound; high negative sqrt-weighted spectral debit at right. For lower start log 3 join old route at 84.5.',
        mr+['replay_analytic.jsonl'],prem=dp,secondary=dp==B0,strict='strict lower, closed slab',
        where='Smaller primitive high moment extends positivity.' if dp==D02 else '',
        baseline='.1 from log 3 to 84.5 old, B0 now 85.7, D02 now 86.99; no infinite-ray sign.')
row('M02-small-y-unnormalized',F,m,119,None,'Q(y)>e^γ log θ(y) on the first prime plateau, no positive-denominator relative claim there.',
    'real 2≤y<3',[], 'θ=log 2<1, so log θ<0 and Q>0.',[],secondary=True,strict='strict; right end excluded for this explanation')
prim=[(133,170,'6.063e-14','1.91e-13'),(134,180,'5.785e-14','8.234e-14'),(135,190,'5.554e-14','6.022e-14'),(136,200,'5.361e-14','5.451e-14'),
      (137,210,'5.196e-14','5.213e-14'),(138,230,'4.931e-14','4.931e-14'),(139,400,'4.005e-14','4.005e-14'),(140,1000,'3.470e-14','3.470e-14')]
for l,a,lo,hi in prim:
    row(f'M02-prim-power-{a}',F,m,l,None,f'−{lo} y^(−5/32)/L < V_y−1 < {hi} y^(−5/32)/L',f'all real L≥{a}',
        [('d02_m_new.py',58,73),('d02_m_checks.py',64,70)],
        'Local square debit only on positive side; subtract T only on negative side; log conversion and full-ray decrease verified.',mr,
        prem=D02,strict='strict, closed rays',where='Strip improves residual primitive and squared local terms while changing exponent.',baseline='Keep older 1/8 primorial leaves; compare in same units and eligible domains.')
    row(f'M02-general-{a}',F,m,144,150,f'n/φ(n), σ(n)/n < e^γ log log n × [1+{hi}(1+5ε)^(5/32)(log n)^(−5/32)/(log log n−log(1+5ε))], ε=10^−12',
        f'integer n≥primorial indexed by e^{a}(1+3ε)',[('d02_m_new.py',58,73),('d02_m_checks.py',64,70)],
        'From primorial positive bound plus short real prime gap and last-prime threshold. log n<θ(p_next)<(1+5ε)y.',
        mr,prem=D02,integer=True,strict='strict upper, inclusive integer threshold',where='Correlated consequence of D02 primorial ray, not new evidence.',
        baseline='Older general upper bounds have different last-prime thresholds and 1/8 exponent.')
row('M02-envelope',F,m,152,154,'At x≥2 pointwise minimum of all eligible absolute bounds, signed intersection then separate product conversion; integrate where applicable.',
    'real x≥2 with every component retaining its own scope',[], 'Order of intersection and exponentiation preserves signed improvements; do not extend local leaves before/after declared domains.',
    mr,prem=D02,where='D02 permits additional eligible leaves without discarding B0.',baseline='No globally optimal envelope over arbitrary B0 proofs.',sources=srccompare)
row('R02-envelope','Ramanujan','D02_COMPARISON.md',14,None,'Pointwise maximum of eligible lower bounds and minimum of eligible upper bounds; no change to finite RH or full RH guards.',
    'real x>1 with each shifted/unshifted eligibility domain as stated',ramfinite+ramtail,'All actual branches separately retain their domains; strict lower margins stay strict on eligible finite subsets and rays.',
    ramn,prem=D02,where='New branches added alongside every valid B0 leaf.',baseline='Quantitative enhancement on PT high sign ray; exact optimal sign endpoint retained.',sources=srccompare)

# Own history: take identity and scopes, independently assign statuses and proof group.
history=get(rest/'D01_M_REVIEW_review.json')
floor=get(rest/'OWN_D01_VALIDATED_SCOPED_FLOOR.json')
active={r['claim_id'] for r in floor['qualified_scope_index']}
assert len(active)==294 and len(history['claims'])==300
retired=[]
baseline_ids={'R-DP-window','R-PT-floored','R-PT-tail','R-DP-tail','R-DP-RH-comparator',
              'M-Dusart-D1','M-Dusart-D2','M-Dusart-products','M-Dusart-analytic-branches','M-original-source-min'}
dominated_ids={'redundancy-Ramanujan','redundancy-Mertens','R-old-tiny','R-old-plus12','R-old-plus13-target',
                'M-old-011-link','M-old-early-0','M-old-early-1','M-old-weighted-0165'}
def classify(cid,n):
    if cid.startswith('redundancy') or n in ('d01_candidate.md','density_refine.md','d02_smoothing.md','d01_smooth.md'):
        if cid.startswith(('R-old-','R1')):
            return 'Exact order-12 offset-li anchor and eligible quote/θ leaves; independent shifted and unshifted R1 estimate, closed cell or tail scaling with positive coefficient slack.', ['replay_ram.jsonl','replay_analytic.jsonl','anchor_checks.txt'],srcpi+srcdens+srcplateau
        if cid.startswith(('A-','M-')):
            return 'Absolute primitive, signed tangent prime-power bound and/or re-centered primorial cancellation; verify specific endpoints or finite prime plateaux and, for integer bounds, last-prime threshold.', ['replay_analytic.jsonl','anchor_checks.txt'],srcdens+srcm+srcplateau
        return 'B0 original QRH and finite RH, legal FKS truncation, directed density integral and staircase; primitive and smoothing only with justified zero sums/interchanges.', ['replay_analytic.jsonl','anchor_checks.txt','run_d02_density_new.py.txt'],srcdens+srcplateau
    if cid.startswith(('R-PT','R-DP','R-local','R-final','R-bridge')):
        return 'Directed local plateau and shifted/unshifted counts; optimum and joins as in review.md. Published sign theorem windows at their source trust; DP full RH comparator is not unconditional.', ['replay_sign.jsonl','anchor_checks.txt','supplement_receipt.txt'],srcsign
    if cid.startswith(('R-old-tiny','R-old-plus12','R-old-plus13')):
        return 'Follows on exact original target domain by domination by retained constant 1 or positive quadratic B0 bound, not by the older π-square implementation.', ['replay_ram.jsonl','run_early_new.py.txt'],srcpi+srcdens
    if cid.startswith('R') or n=='ram_high.md':
        return 'Corrected direct π cube or eligible θ, offset, signed-anchor or spectral leaves. Independent shifted/unshifted eligible full-cell debits or factorial tail monotonicity; correct u=40 attribution. Apply actual tail available at each onset.', ['replay_ram.jsonl','anchor_checks.txt','run_d02_variable.py.txt'],srcpi+srcdens+srcplateau
    if cid in baseline_ids:
        return 'Retain original normalizations and exact hypotheses. Partial summation yields row-dependent analytic bounds; convert products after signed log subtraction.', [],srccompare
    if n=='d01_mertens.md':
        return 'Prime-prefix bounds on closed cells; integrate PT π only to exp(40), transfer the CH2 weighted endpoint on plateau, and use fixed-height integrated estimate followed by the power tail.', ['replay_smallfinite.jsonl','replay_analytic.jsonl'],srcm+srcpi+srcplateau+srcdens
    if cid.startswith(('M-step-','M-new-finite','M-old-early','M-weight-onset','M-cone','M-old-weighted','M-old-011')):
        return 'Exact plateaux or prefix cells at stated x intervals with correct divisors and tail correction; use only the verified suffix and join the eligible analytic tail, or use exact weighted transfer.', ['replay_early.jsonl','replay_coarse1.jsonl','replay_coarse2.jsonl','replay_analytic.jsonl'],srcm+srcpi+srcplateau
    if n in ('mertens_postreview.md','mertens_repair.md','d02_mertens.md','d02_candidate.md'):
        return 'Independent signed ψ bias/prime-tail algebra and original bounds, eligible threshold joins, directed exponentiation/monotone rays, or Stieltjes weighted transfer. Do not revive the old conditional branch as B0.', ['replay_analytic.jsonl','anchor_checks.txt','replay_coarse1.jsonl','replay_coarse2.jsonl','replay_early.jsonl'],srcm+srcpi+srcplateau+srcdens
    if n=='d01_arithmetic.md':
        return 'From B0 θ endpoint, concavity for short intervals and cancellation at primorials; last prime threshold checked before replacing y by log n.', ['replay_analytic.jsonl'],srcdens+srcm
    return 'Independent verification of definitions/scoping and taking eligible pointwise extrema; original source constants and precision as in review.md.', ['replay_analytic.jsonl','anchor_checks.txt'],srccompare
for c in history['claims']:
    cid=c['claim_id'];fam=c['family'];w=c['written_source'];n=byhash[w['sha256']]['original_name']
    a=w['physical_LF']; assert w['original_filename']==n or w['original_filename'] in (n.removesuffix('.txt'),n.removesuffix('.md.txt'))
    if cid not in active:
        why=('Withdrawn: wrong direct π normalization; actual source gives cube. Not established false.' if cid=='R-pi-finite-log2-withdrawn' else
             'Superseded bracket. Corrected version omits historical direct square and optional h1+m1.' if cid=='R-old-alt-uncorrected' else
             'Disclosed raw conditional history, not reactivated by D02_COMPARISON LF20. 27/32 now available for the current proofs; no numerical claim from this superseded artifact imported.')
        retired.append(dict(claim_id=cid,family=fam,written_source=src(n,a),exact_statement=c['exact_statement'],disposition=why))
        continue
    st=M; gap=None; scope='retained qualified own history'
    if cid in baseline_ids:st=BASE
    if cid in dominated_ids:st=EQ
    if cid=='R-stronger-constant-3':
        st=BAD;gap='At x=e^1000, B0 two-sided method gives Y≤1.01414642614<1.015<1.03; archived global assertion expressly corrected in D02_SCOPE_CORRECTION.json; finite replacement R02-early-30.714-1.03.';scope='false archived scope, expressly not current'
    if cid=='R-PT-literal':
        st=BAD;gap='At x=38358837682+1/5, exact local counts and directed root log check give −1220000<R<−1200000; quoted as refuted source assertion, not candidate premise.';scope='quoted refuted source assertion'
    # Readback: remap implementation locators by actual digest and physical source.
    im=[]
    for d in c.get('implementation_readbacks',[]):
        rr=byhash.get(d['sha256'])
        if not rr: continue
        im.append((rr['original_name'],d['physical_LF'],d.get('through_physical_LF')))
    chk,receipt,loc=classify(cid,n)
    olddom=c['full_domain']
    if cid=='R-DP-RH-comparator':olddom='largest failing integer N=38358837682; positive for integers n>N, conditional on full RH'
    if cid=='R-DP-window':olddom='closed real [10^11,1.15·10^16]'
    if cid=='R-stronger-constant-3':
        receipt+=['run_d02_variable.py.txt'];chk='The finite test through 191 does not prove a constant 1.03 along a lower profile tending to 1. A directed B0 upper bound at 1000 refutes the archived wider scope.'
    if cid=='R-PT-literal':chk='Exact local R comparison; retain separately integer restriction and high tail.'
    if cid in ('R-old-tiny','R-old-plus12','R-old-plus13-target'):
        im=[('ram_repair.py',196,238)]
    if cid in ('M-old-early-0','M-old-early-1','M-old-011-link','M-old-weighted-0165'):
        chk+=' The later same-strength onset is implied by the supported earlier or tighter bound.'
    if cid.startswith('A-') or cid.startswith(('M-old-sqrt','M-step-','M-new-finite','M-weight-onset')):
        chk+=' Match exact quoted and implemented endpoint/divisor, not a status bit.'
    row(cid,fam,n,a,None,c['exact_statement'],olddom,im,chk,receipt,prem=c['assumptions'],
        baseline='Retained exact scoped B0 or original result; none of this old floor obtains additional-input gain from redundant D01.',
        status=st,strict=c['strictness'],scope=scope,gap=gap,sources=loc)
    claims[-1]['real_or_integer']=c['real_or_integer']
    claims[-1]['numerical_obligations']=c['numerical_obligations']
    if st==BAD:claims[-1]['retained_valid_branches']=('PT integer-floor leaf and high tail' if cid=='R-PT-literal' else 'Current finite [30.714,477.005] and independent constant 1 ray')
assert len(retired)==6
assert len({r['claim_id'] for r in claims})==len(claims)
base=get(root/'SOURCE_INDEX.json')
families={}
for fam in ('Ramanujan','Mertens'):
    good=[c for c in claims if c['family']==fam and c['M_status'] in (M,BASE,EQ)]
    families[fam]=dict(
      strongest_supported_portfolio=[c['claim_id'] for c in good if c['M_status']!=EQ],
      rejected_or_incomplete_claims=[c['claim_id'] for c in claims if c['family']==fam and c['M_status'] in (BAD,GAP)],
      remaining_assessment_work=[],
      summary= ('Exact optimal sign retained, corrected old false infinite 1.03 scope, connected +80.6 and separate +100 ray, fixed and variable-order D02 improvements plus whole B0 floor.' if fam=='Ramanujan'
            else 'Supported both relative products and both normalized sums, including paired logarithmic and power joins, pointwise signed intersections, earlier B0 thresholds, primorial and integer consequences. Authentic CH2 radius preserves the written plateau cap.'))
doc=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=index['candidate_id'],
    assessment_complete=True,all_claims_inventoried=True,
    reviewed_source_hashes={**{r['packet_name']:r['sha256'] for r in byname.values()},**{r[k]:r[k+'_sha256'] for r in base['sources'] for k in ('pdf','text')}},
    source_bibliography=base['sources'],
    actual_effort_and_verification_commands={'commands':'replay_instructions.txt','receipts':[p.name for p in sorted(out.iterdir()) if p.name.startswith(('run_','runner_','replay_','supplement_receipt','anchor_checks','original_pdf_objects','pdf_layout'))],
         'usage_counters':'No authoritative generated-token count available; all material current and inherited certificate groups rerun, not the originals’ published finite computations.'},
    family_assessments=families,
    claims=claims,implementation_literal_readback_catalog=readback_catalog,no_other_arm_or_ranking_seen=True,new_core_math_salvage_performed=False,original_candidate_bytes_changed=False,
    own_history_scope='OWN_ONLY; original scopes, zero use of earlier verdicts as premises',inactive_own_history=retired,
    verification_scope=V,ancillary_checks='Exact proof transfers, source normalization and same-constant CH2 rounding, no new core construction or parameter search.')
(out/'review.json').write_text(json.dumps(doc,ensure_ascii=False,indent=1)+'\n')
stage=dict(ready_for_review=True,
  families={f:dict(status=M,claim_files=['review.md','review.json']) for f in families},serious_attempts_documented=True)
(out/'STAGE_STATUS.json').write_text(json.dumps(stage,indent=1)+'\n')
print('current and retained',len(claims),'historical inactive',len(retired))
