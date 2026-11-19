import ast,json,re,hashlib
from decimal import Decimal as D
from pathlib import Path
S=Path('/work/submission');T=Path('/task');C=Path('/work/c')
def get(f):return json.loads(f.read_text())
index=get(T/'CANDIDATE_INDEX.json')
source=get(T/'SOURCE_INDEX.json')
cand={v['original_name']:v for v in index['candidate_files']}
def line(f,l):return (C/f).read_text().split('\n')[l-1]
def loc(f,l,e=None):
 line(f,e or l)
 return dict(file=f,packet_file=cand[f]['packet_name'],physical_LF=l,physical_LF_end=e or l,sha256=cand[f]['sha256'])
def remap(m):
 x=loc(m['original_name'],m['physical_LF'],m.get('physical_LF_end'));assert x['sha256']==m['sha256'];return x
R='Ramanujan';M='Mertens';F='D02_PROOF.md';P='d02_check.py'
OK='supported_at_stated_trust_tier'
B='OpenAIQRH Thm.1.1 p.4; FiniteRH Thm.1 p.2; FKS Thm.3.2 p.8; PT PNT Lem.2 p.4; CH2 Cor.1.2–1.3 p.3, Appendix A pp.40–41, B.3 p.43, B.5 p.44, B.8 pp.46–47'
RR='Dusart Thm.5.1/Cor.5.2 pp.14–15; FiniteRH Cor.1 p.4 and §3.3 p.5; '+B
MM='Dusart Thm.4.2 p.11, Cor.4.5 p.13 and Thms.5.6–5.9 pp.17–20; CH2 Lem.9.2 p.35; '+B
DEN='FKS Cor.2.9 (2.17) pp.7–8/upper Table 8 p.26'
EARLY='PT PNT Thm.2 p.3; DP p.2 Galway report/Thm.1.2; DP §3.1 and Lem.3.4 pp.8–10'
def cod(*pairs):return [loc(*p) for p in pairs]
rows=[]
def row(id,f,w,ex,dom,der,read=(),i=0,d=False,comp=None,src=None,st=OK,gap=None,scope='active',strict=None,num=None,re=None,real='real'):
 if src is None:src=RR if f==R else MM
 if d:src+='; '+DEN
 if comp is None:comp='Same B0+B0-derived D01 on matched domains; retain all eligible alternatives.' if not i else 'Matched B0 same-method exponent 1/8 versus 5/32; compare exact rows, not optimality.'
 rows.append(dict(claim_id=id,family=f,written_source=w,exact_statement=ex,full_domain=dom,
   assumptions='B0'+(' + exact D02' if i else '')+(' (published density corollary/table trust)' if d else ''),
   strictness=strict or ('strict on stated domain, boundaries as given' if f==R else 'non-strict, inclusive'),real_or_integer=real,
   derivation_check=der,source_locators=src,baseline_comparison=comp,numerical_obligations=num or 'Directed tests where readback indicates; full-domain analysis in review.md.',
   implemented_readbacks=list(read),actual_verification_receipts=re or 'receipt_blocks.txt, receipt_hashes.txt, audit_summary.txt and resumption.stdout; signed/analytic branches in review.md',
   retained_valid_branches='Keep all eligible basic, finite, signed and original alternatives in maxima/minima.',
   M_status=st,precise_gap_or_counterexample=gap,scope=scope,
   propagation=dict(input_used='D02' if i else 'none (B0)',where_it_changes_proof='Mellin zero-edge improvement propagates through pointwise/integrated spectral terms.' if i else 'No additional premise. D01 redundant (foundation.md 7–11).',matched_comparison=comp),
   V_status='Ordinary executable evidence where indicated; Lean not supplied/checked; no source-first PV',
   remaining_trust='As stated in review.md: pinned analytic/literature and ordinary runtime; density additionally trusts Cor.2.9 and Table 8.' if d else 'As stated in review.md: pinned analytic/literature and ordinary runtime as applicable. Long published sieve not independently rerun.'))
old=get(T/'SUPPORT_001.json')['claims']
active=get(C/'OWN_D01_VALIDATED_FLOOR.json')['validated_claim_ids_by_family']
active=set(active[R]+active[M])
assert len(old)==772 and len(active)==770
for c in old:
 id=c['claim_id'];f=c['family'];w=remap(c['written_source']);file=w['file'];l=w['physical_LF'];d=False;src=None
 st=OK;scope='active';gap=None
 if id.startswith('S-'):
  what=id.split('-')[1];d=what in ['q','QD'];src=B
  der={'D01':'B0 Perron .005 at 200 and monotonic after normalization; D01 redundant.',
       'QB':'Reflected positive part and valid adjustable Perron T; log derivative and normalized parabola.',
       'q':'Reciprocal density Stieltjes tail with exponential log majorant and layer absorption.',
       'QD':'Integrated degree-four Taylor and two-slope layer; monotone tail.',
       'D':'Signed integrated Perron residues and squared denominators; Laplace kernel.',
       'Dstar':'ξ identity, positive summands and finite-height low zero weight .0463.',
       'CH':'Original finite-height/signed scopes, exact coth centering, and separate FKS Thms.1.1–1.2/Cor.1.4 p.2, Tables 5–6 pp.22–23.',
       'CHtrial':'Three capped CH2 truncations on eligible domain.'}[what]
 elif f==R:
  der='Calibrated Taylor R3 shifted at L−1, closed-cell and/or monotone tail checks.'
  if id.startswith(('R-window','R-tail')):d='basic' not in id and not id.endswith('1b') and id not in ['R-window-old-2','R-window-old-3','R-window-old-4','R-window-new-2','R-window-new-4']
  if id.startswith('R-tail-new-'):
   j=int(id.split('-')[-1]);a=ast.literal_eval(line(file,l).split(': ',1)[1])[j];assert c['full_domain']==f'L≥{a}'
  if id in ['R-cell','R-connected','R-sawtooth','R-sawtooth-int','R-source-tails','R-old-source-real','R-retired-pi']:
   src=EARLY+'; '+RR;der='Exact local counts, monotonicity and proper open real/inclusive integer boundaries; the long published reported integer signs are at literature trust.'
  if id=='R-old-source-real':st='false_with_specific_counterexample';gap='R(38358837682.1)∈(−7974585.083,−7974585.082).';scope='quoted_not_active'
  if id=='R-retired-pi':st='incomplete_with_specific_missing_step';gap='FiniteRH p.4 π line has log², confirmed by PDF stream 114; no stated source for log¹ on its domain.';scope='withdrawn_not_active'
  if id=='R-source-tails':st='baseline_retained';der='Source eventual rays also subsumed by independent basic positivity proof.'
  if id.startswith('R-R') or id=='R-pointwise-repair':der='PV li normalization, R1 integration by parts, R2 prime powers and signed eligibility; R3 shifted Taylor.'
  if id=='R-asymptotic':der='Fixed asymptotic Taylor expansion and exponentially small arithmetic errors.'
  if id=='R-failed-tests':der='Insufficient tests reproduced, not counterexamples.'
 else:
  der='M1 and W/W3, directed coefficients, eligible positive product denominator, complete analytic joins.'
  d='density' in id or 'power-oldD' in id or 'power-newD' in id or id.startswith('M-limit') or id=='M-power-old400'
  if id.startswith('M-source-'):st='baseline_retained';der='Original inclusive thresholds and exact normalizations read back.'
  if id.startswith('M-frontier'):
   k,tag=id.split('-')[-2:];a,*onsets=line(file,l).split();assert k==a and onsets[['w','r','P','Q'].index(tag)] in c['full_domain']
   der='Exact gap endpoint tests with directional product conversion and floor bins; post-256m join <.045.'
  if file=='mertens.md' and 24<=l<=47:
   a,b,v=[s.strip() for s in line(file,l).strip('|').split('|')];assert a in c['full_domain'] and (v if id.endswith('-w') else b.split()[0]) in c['exact_statement']
   der='64m sieve exact fixed-point endpoints including rational starts; full post-sieve analytical join.'
  if 'constant' in id or 'finite-pointwise' in id:der='Harmonic trapezoid and Stieltjes constant tail bounds, exact finite pointwise sums.'
  if id in ('M-M1','M-M2','M-log-tail','M-theta-option','M-Z1-option','M-envelope','M-envelope-repair','M-W3','M-normalization'):
   der='Right-endpoint Stieltjes identities, eligible tail kernels and exponentials of signed endpoint bounds.'
  if id=='M-trials':der='Actual finite_trials sufficient-test failures, not counterexamples.'
 assert (id in active)==(scope=='active')
 row(id,f,w,c['exact_statement'],c['full_domain'],der,[remap(m) for m in c['implemented_readbacks']],d=d,src=src,st=st,gap=gap,scope=scope,strict=c['strictness'],real=c['real_or_integer'],re='first-pass old exit 0; twelve byte matches in receipt_hashes.txt; review.md')
def new(id,f,l,e,ex,dom,der,r=(),**kw):row(id,f,loc(F,l,e),ex,dom,der,r,**kw)
for f,t in [(R,'R'),(M,'M')]:
 new('D02-edge-'+t,f,15,21,'Every nontrivial zeta zero has β≤27/32','all ordinates','Mellin continuation and pole argument, not strict at edge.',i=1,strict='non-strict')
 for i in [0,1]:
  a=['1/8','5/32'][i]
  ss=[
  ('basic-Perron',25,35,f'|E|/x≤exp(−{a}L)B_i,c(L), c=4.3,4.4,4.5,4.6,4.65,4.7,6,8; log derivative bound at c=4.65','L≥40; slope L≥199','Positive reflected weight and FKS cutoff eligibility.',[(26,45),(60,72)],False),
  ('W1',39,69,'r=1 weighted density integral, edge ceiling, slopes and layer bound','.75≤s≤b_i; layer L≥110','Stieltjes density integral and five-term Taylor; slope enclosures and edge limit.',[(17,58)],True),
  ('W2',39,69,'r=2 weighted density integral, edge ceiling, slopes and layer bound','.75≤s≤b_i; layer L≥110','Stieltjes density integral and five-term Taylor; slope enclosures and edge limit.',[(390,413)],True),
  ('Q',71,76,f'|E|/x≤Q_i(L)exp(−{a}L); Q_i decreases to D_1,i','L≥110','Three zero groups, correct exponent and Perron truncation.',[(47,58)],True),
  ('d',80,86,'d_i bounds |D|/x² and signed weighted tails with x^−u and log multipliers','x≥2, u≥0','Integrated residues and signed tail kernel.',[(74,78)],False),
  ('dhat',88,92,'Improved d̂_i in both integrated bounds and log tail','x≥2, u≥0','Reflect high squared weight; enlarged low-zero coefficient.',[],False),
  ('d2',93,97,'Improved d_i^(2) in both integrated bounds and log tail','L≥110, u≥0','Split high off-line square weight at .75; density-layer theorem.',[(390,422)],True),
  ('smoothed-basic',99,105,f'|E|/x≤2.451e−6 exp(−{a}L/2)','L≥110','Monotone ψ interval averages and d̂_i.',[(362,388)],False),
  ('smoothed-density',106,106,'|E|/x≤2.000001 sqrt(d_i^(2)(L−1e−7))','L≥111','Both averaging endpoints in correct log domain and δ small.',[(399,422)],True)]
  for tag,l,e,ex,dom,der,c,d in ss:new(f'{tag}-{t}-{i}',f,l,e,ex,dom,der,cod(*[(P,x,y) for x,y in c]),i=i,d=d,strict='non-strict')
 new('D02-psi-envelope-'+t,f,108,108,'Intersect all eligible signed and symmetric ψ alternatives; direct D02 only at L≥200, dominated there by basic normalized power.','Each option on its precise original domain','Intersection; .0020012 < 1/64 gives the direct comparison.',cod((P,60,72),(P,335,350)),i=1,strict='non-strict')
for i in [0,1]:
 new(f'R-error-{i}',R,150,170,'I_i and both A± prime-count errors, signed upper and k=2,3,4 improvement','L≥34 with precise source thresholds for each option','Integrated R1 and correct Dusart power bounds.',cod((P,74,95),(P,209,230)),i=i,strict='non-strict')
 new(f'R-envelope-{i}',R,172,176,'Two-sided g interval via L⁵ shifted lower/upper π and L⁶ square of unshifted upper/lower π, count lower clamped to zero; take all strict profiles too.','Every L where both arguments eligible','Monotone square; preserve strictness only of strict branches.',cod((P,80,89)),i=i,strict='non-strict interval')
 new(f'R-centered-{i}',R,176,188,f'|g−G|≤{[".061",".86"][i]}L⁴ exp(−a_iL)','L≥201','Correct caps on both arguments, shifted term and square-loss constants.',cod((P,441,450)),i=i,d=True,strict='non-strict',comp='D02/B0 shape ratio <.026379 at 201, decreasing thereafter.')
 new(f'R-Taylor-{i}',R,190,199,'Taylor bracketing for orders 20,50,100,160,210 at stated anchors; R3 and scaled monotone loss / surplus','Above anchors, shifted R3 and tail eligibility as stated','Strict binomial remainder and derivative test; all coefficients exact.',cod((P,91,146),('check.py',162,164)),i=i)
 new(f'M-pointwise-{i}',M,227,243,'Complete signed M1, W3/log-tail, θ and centered Λ/n options; absolute endpoint exp bounds and product minima','x≥2, exact option-specific applicability','Signed integral subtraction, right-counted tails, separate product signs.',i=i)
new('R-sharp-retained',R,117,117,'r in (N+.217926,N+.217927), R(r)=0, R(x)>0 for x>r, inclusive integer onset N+1','all x>r; at r equality','Exact local certificate and published integer cases join the analytic proof.',cod(('check.py',206,220),('small_end.cpp',8,26)),src=EARLY,re='audit_summary.txt and resumption.stdout, plus literature trust')
new('R-limit-D02-stage',R,146,170,'g(L)→1, hence no larger constant strict margin on a ray','L→∞','Fixed-order Taylor expansion gives 1+14/L+O(L^−2).',strict='limit/exclusion')
rays={}
for l in range(27,31):
 m=re.fullmatch(r'ray (\d) (density|basic) m=0\.\.205 (.*)',line('d02_rays.txt',l));i=int(m[1]);mode=m[2];a=ast.literal_eval(m[3])
 rays[i,mode]=a;assert len(a)==206
 for j,v in enumerate(a):row(f'R-new-ray-{i}-{mode}-{j}',R,loc('d02_rays.txt',l),f'g>P_{j}',f'L≥{v}','Directed Taylor surplus comparison and decreasing scaled losses.',cod((P,91,146)),i=i,d=mode=='density',comp=f'Same {mode} B0 pure-tail endpoint {rays[0,mode][j]}; preserve any earlier joined compact onset.')
for l in list(range(1,13))+list(range(14,26)):
 m=re.fullmatch(r'compact (\d) (\d+) (.*)',line('d02_rays.txt',l));i,j=int(m[1]),int(m[2])
 for k,(a,b) in enumerate(ast.literal_eval(m[3])):
  row(f'R-compact-density-{i}-{j}-{k}',R,loc('d02_rays.txt',l),f'g>P_{j}',f'{a}≤L≤{b}','Directed n=50 closed cells covering the full window.',cod((P,148,166)),i=i,d=True)
  if j>=2 and D(b)>=rays[i,'density'][j]:
   new(f'R-joined-density-{i}-{j}',R,119,126,f'g>P_{j}',f'L≥{a}',f'Closed window to {b} overlaps infinite tail from {rays[i,"density"][j]}.',cod((P,97,135),(P,148,166)),i=i,d=True)
for l in range(3,11):
 m=re.match(r'smoothed table-free compact (\d) (\d+) (.*)',line('d02_smooth.txt',l));i,j=int(m[1]),int(m[2])
 for k,(a,b) in enumerate(ast.literal_eval(m[3].replace('Decimal(','('))):
  row(f'R-compact-basic-{i}-{j}-{k}',R,loc('d02_smooth.txt',l),f'g>P_{j}',f'{a}≤L≤{b}','Touching closed table-free smoothing cells.',cod((P,362,388)),i=i)
  if i:new(f'R-joined-basic-{j}',R,128,128,f'g>P_{j}',f'L≥{a if j>1 else "47.040"}',f'Window [{a},{b}] joins at {rays[1,"basic"][j]}; P1 overlaps the earlier window.',cod((P,97,135),(P,362,388)),i=1,comp='B0 basic P1 still has a hiatus; B0 density P1 already starts 47.040. Compare basic onsets at fixed order for the other profiles.')
for l in range(1,5):
 a,b=ast.literal_eval(line('d02_earliest.txt',l).split(' [',1)[1].replace('Decimal(','(').join(['[','']))[0]
 row(f'R-early-window-{l}',R,loc('d02_earliest.txt',l),f'g>P_{l}',f'{a}≤L≤{b}','Early CH2/π signed/power improvements, closed cells.',cod((P,209,230),(P,248,258)))
new('R-B0-P2-window-extended',R,119,119,'g>P2','52.075≤L≤125.25','Join old through 125.20 and new [111,125.25].',cod((P,148,166),('repair_check.py',150,163)),d=True)
for j,(c,v) in enumerate(ast.literal_eval(line('d02_final_extras.txt',27).split(': ',1)[1])):
 row(f'R-early-margin-{j}',R,loc('d02_final_extras.txt',27),f'g>{c}',f'L≥{v}','Closed early certificate to 47.05 meets inherited >1 ray.',cod((P,232,246)))
for j,(v,c) in enumerate(zip('36.786 36.988 37.554 37.790 38.520 38.682 39.394 39.504'.split(),'.124 .212 .430 .509 .716 .756 .904 .924'.split())):
 new(f'R-fixed-onset-{j}',R,146,146,f'g>{c}',f'L≥{v}','Verified whole-ray margin at no later onset, not just point value.',cod((P,232,246)))
for v,j,k in [(200,1,2),(400,7,10)]:
 new(f'R-profile-comparison-{v}',R,126,126,f'Certified P_{k} vs matched P_{j} lower profile',f'L≥{v}','Exact inclusion in verified high-profile rays, not impossibility of further B0 gains.',cod((P,97,135),(P,148,166)),i=1,d=True)
def mert(id,w,i,d,c,v,shape,rr,comp=None):
 vec={'S':'(L^−2,L^−3,L^−3,L^−3)','D':'exp(−a_iL)(1,L^−1,L^−1,L^−1)','B':'exp(−a_iL)(L²,L,L,L)'}[shape]
 row(id,M,w,f'(|w|,|r|,|exp(−z)−1|,|exp(z)−1|)≤{c}·{vec}',f'L≥{v}','M1/W3 and positive product conversion. Use normalized monotone tail or backward compact maxima and post-420 join.',rr,i=i,d=d,comp=comp)
mt={}
for file,l,i,d,shape,rev,co in [
 ('d02_coeff.txt',1,0,1,'D',0,(168,199)),('d02_coeff.txt',2,0,1,'S',0,(200,208)),
 ('d02_coeff.txt',3,1,1,'D',0,(168,199)),('d02_coeff.txt',4,1,1,'S',0,(200,208)),
 ('d02_coeff.txt',16,0,1,'S',1,(301,321)),('d02_coeff.txt',17,1,1,'S',1,(301,321)),
 ('d02_coeff.txt',18,1,1,'D',1,(322,334)),
 ('d02_basic_mid.txt',1,0,0,'S',0,(424,439)),('d02_basic_mid.txt',2,1,0,'S',0,(424,439))]:
 vals=ast.literal_eval('['+line(file,l).split(' [',1)[1]); vals=[(b,a) for a,b in vals] if rev else vals
 mt[file,l]=dict(vals)
 for j,(v,c) in enumerate(vals):
  comp=None
  if shape=='S' and i:
   other=mt.get((file,2 if l==4 else 1),{})
   comp=(f'Matched L≥{v}: B0 {other[v]}, D02 {c}.' if v in other else 'Fixed coefficient inversion compared with B0 row 16 in d02_coeff.txt.')
  mert(f'M-{file}-{l}-{j}',loc(file,l),i,d,c,v,shape,cod((P,*co)),comp)
for i,l in [(0,216),(1,217)]:
 for v in [170,180,190,200,220,240,300,400]:
  c0=mt['d02_coeff.txt',2][v];c1=mt['d02_coeff.txt',4][v]
  mert(f'M-table-{i}-{v}',loc(F,l),i,True,[c0,c1][i],v,'S',cod((P,200,208)),f'Matched B0 {c0} and D02 {c1}.')
for i,c in enumerate(['.001285','.0020012']):
 mert(f'M-basic-uniform-{i}',loc(F,221),i,False,c,40,'B',cod((P,335,350)),'Matched basic ratio D02/B0 <.446190 at 40 and decreases.')
 new(f'M-limit-basic-{i}',M,221,253,'Basic normalized majorant limit a_i²/(4π)','L→∞','Positive part eventually active and all other normalized terms vanish.',cod((P,335,360)),i=i,strict='limit')
 new(f'M-limit-density-{i}',M,222,222,'Limiting density majorant with d^(2) at most D_{1,i}+D_{2,i}','L→∞','F_i→1; remaining normalized terms vanish; not actual error limit.',cod((P,26,35),(P,390,422)),i=i,d=True,strict='limit')
for k,(v,c) in enumerate([(1200,'.001999291'),(5000,'.001963277')]):mert(f'M-basic-late-{k}',loc(F,221),1,False,c,v,'B',cod((P,351,360)))
for k,(v,c) in enumerate([(200,'.266350'),(400,'.188769'),('1050.68','.16'),('3643.22','.15')]):
 mert(f'M-density-power-{k}',loc(F,222),1,True,c,v,'D',cod((P,189,199),(P,322,334)),'At common L≥200 .266350 D02 vs .018830 B0 ratio <.027307 at 200 and decreases.')
for j,(c,b,v) in enumerate([('1e−8','200.38','176.39'),('1e−10','239.07','206.99'),('1e−12','277.67','237.62'),('1e−18','392.71','329.20')]):
 new(f'M-matched-inverse-{j}',M,219,219,f'Common scaled strength {c}',f'B0 L≥{b}, D02 L≥{v}','Directed endpoints and normalized monotone tails.',cod((P,301,321)),i=1,d=True,comp=f'Matched strength {c}: onset {b}→{v}.')
mert('M-basic-mid-comparison',loc(F,219),1,False,'9.727e−10',230,'S',cod((P,424,439)),'Matched B0 basic 5.771e−8 from same 230.')
for j,(field,c,k) in enumerate([('|w|','1.916','.07738'),('other three relative/absolute errors','1.8292','.07388')]):
 new(f'M-strip-{j}',M,223,259,f'{field}≤{c} exp(−L/2)'+('/L' if j else ''),'64000000≤x≤1e13','Signed θ and square-boundary sieve, even log-kernel truncation.',cod((P,260,299)),comp='B0 secondary improvement over 1.939.')
 new(f'M-strip-ray-{j}',M,223,259,f'{field}≤{k}/L^{2+j}','x≥64000000','Decreasing scale factor and inherited <.0097 join.',cod((P,260,299),('repair_mertens.py',47,73)),comp='B0 secondary improvement over .07815.')
new('M-shape-law',M,225,225,'Power/exponent ratio tests on monotone pieces and weakening exponent at common onset','applicable matched rays','Differentiate log ratio; comparison whole domain.',i=1)
new('M-converse-spectral',M,265,265,'Any faster exponent a1+ε<1/2 for w,r or either relative product would exclude zeta zeros on D02 edge','asymptotic x→∞','Partial summation, product log and tail, then Mellin; conditional only.',strict='conditional implication')
for f,l,id in [(R,263,'R-obstacle'),(M,264,'M-trial')]:
 new(id,f,l,l,'Reported failure/smoother trials are diagnostic, not arithmetic counterexamples or proofs of whole windows','stated diagnostic domains','Numerical tests and analytical rate comparisons as in review.md.',i=1,scope='diagnostic',strict='no additional theorem')
assert len(set(d['claim_id'] for d in rows))==len(rows)
out=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=index['candidate_id'],assessment_complete=True,all_claims_inventoried=True,
 reviewed_source_hashes={m['packet_name']:m['sha256'] for m in index['candidate_files']+index['support_files']},
 source_bibliography=source['sources'],actual_effort_verification_commands=(S/'evidence_commands.txt').read_text(),
 no_other_arm_or_ranking_seen=True,original_candidate_bytes_changed=False,new_core_math_salvage_performed=False,
 family_assessments={},claims=rows)
for f,summary in [(R,'Exact inherited positivity boundary at literature trust, new B0 fixed margins and D02 joined basic P1, higher profiles and centered error.'),(M,'Signed finite and analytic envelopes and both prime sums; stronger D02 scales and exponents, and B0 finite strip gains.')]:
 a=[d for d in rows if d['family']==f and d['scope']=='active']
 out['family_assessments'][f]=dict(strongest_supported_portfolio=[d['claim_id'] for d in a if d['M_status'] in [OK,'baseline_retained']],rejected_or_incomplete_claims=[d['claim_id'] for d in a if d['M_status'] not in [OK,'baseline_retained']],remaining_assessment_work=[],summary=summary)
(S/'review.json').write_text(json.dumps(out,ensure_ascii=False,separators=(',',':'))+'\n')
print(len(rows))
