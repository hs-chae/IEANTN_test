#!/usr/bin/python3.10
import hashlib,json,re
from pathlib import Path
p=Path('/work/c018'); o=Path('/work/submission');t=Path('/task')
J=lambda f:json.loads(f.read_text())
idx=J(t/'CANDIDATE_INDEX.json'); bib=J(t/'SOURCE_INDEX.json')['sources']
S={x['original_name']:x for x in idx['candidate_files']}
C='candidate.md'; A='repair.md'; R='Ramanujan'; M='Mertens'; F='finite-proof.md'
ok='supported_at_stated_trust_tier'; old='baseline_retained';bad='false_with_specific_counterexample';miss='incomplete_with_specific_missing_step'
qsrc=['OpenAIQRH Theorem 1.1 PDF p.4 LF255–262','FiniteRH Theorem 1 PDF p.2 LF47–49','Dusart Theorem 2.3 PDF p.5 LF245–257','FKS Theorem 3.2 PDF p.8 LF631–642','PT Lemma 2 PDF p.4 LF235–246','Dusart Theorem 4.2, Proposition 4.3, Corollary 4.5 PDF pp.11–13 LF959–1010,1049–1056,1132–1137']
fks='FKS Corollary 2.9 (2.17) pp.7–8 LF586–608/Table 8 first panel p.26 LF3139–3258'
rsrc=qsrc+['FiniteRH Cor.1, §3.3 PDF pp.4–5 LF138–150,182–185','CH2 Corollaries 1.2–1.3 PDF p.3 LF190–240 and (9.2) p.36 LF5273–5305']
msrc=qsrc+['Dusart Thms 5.6–5.7,5.9 PDF pp.17–19 LF1479–1505,1555–1586,1640–1664','CH2 Corollaries 1.2–1.3 p.3 LF190–240, Lemma 9.2 p.35 LF5216–5266']
sourcecomp=['FKS Thms 1.1–1.2, Cor.1.4/Table 5–6 pp.2,22–23 LF113–143,2324–2575,2598–2747; Lemma 5.2 p.17 LF1928–1942','PT Thm1/Cor.1/Table 1 and (18) pp.2–3,10 LF77–117,142–201,813–904','Dusart Thm3.3/Table 1 pp.7–9 LF458–475,489–728,742–765','CH2 (10.3) p.38 LF5565–5570']
rprog=[('verify.py',84,183),('certify.py',7,50),('higher.py',4,32)]
rrprog=[('ramref.py',6,84),('refine.py',7,44)]
mprog=[('mertens.py',4,50),('certify.py',53,97)]
mmprog=[('refine.py',7,104),('refine.py',105,176)]
cprog=[('comparison.py',7,74)]
fprog=[('finite.c',13,114)]
spect=[('verify.py',52,113)]
cap='From D02 Mellin continuation, cap 7/8→27/32, cap atoms retained; spectral terms/rates change; finite data and original hypotheses unchanged.'
b0='Original common source statements at original hypotheses, including QRH where used; no full RH'
d02=b0+' plus exact D02 for all real x>=exp(200), |psi(x)−x|<=x^(27/32)(log x)^2/64'
trust='Written mathematics and supplied originals including their inherited computations; ordinary exact-integer or outward arithmetic for replay, no Lean/Blueprint source or PV.'
def loc(f,n,z=None):
 a=S[f]
 return dict(file=f,packet_file=a['packet_name'],physical_LF=n,physical_LF_scope=z if z is not None else n,sha256=a['sha256'])
def linen(f,n):return (p/f).read_text().split('\n')[n-1]
rows=[]
def add(id,fam,f,n,statement,domain,*,scope=None,st=ok,inp='none (B0)',chg=None,cmp=None,
    src=None,ck=None,nb=None,rc=(),code=(),sn='Non-strict unless equality is specified.',ri='real',gap=None,hist=False,retain=()):
 if src is None:src=rsrc if fam==R else msrc
 if chg is None:chg=cap if 'D02' in inp else 'Original-input result, retained under D02.'
 if cmp is None:cmp='Within-method B0/D02 comparison, not optimality or blind baseline.' if 'D02' in inp else 'Retain B0 branch in both premise sets.'
 if not ck or not nb:
  ck=ck or ('Both log arguments independently gated; entire-cell coefficient cancellation and first-unused-positive-term tail, as in review.md.' if fam==R else 'Scale and use decreasing nonnegative spectral/remainder envelopes; check both sums and convert via signed exponentials, as in review.md.')
  nb=nb or 'Exact endpoints, denominator/domain tests and outward slacks in the cited receipts, where applicable.'
 rows.append(dict(claim_id=id,family=fam,written_source=loc(f,n,scope),written_LF_text=linen(f,n),exact_statement=statement,
  assumptions=(b0+'; only the 27/32 alternative assumes D02: '+d02 if inp=='B0 with alternative D02 cap' else d02 if inp=='D02' else b0),full_domain=domain,strictness=sn,real_or_integer=ri,baseline_comparison=cmp,
  source_locators=src,derivation_check=ck,numerical_obligations=nb,
  actual_verification_receipts=list(rc),implemented_formula_sources=[loc(f1,i,f'{i}–{j}') for f1,i,j in code],
  retained_valid_branches=list(retain),M_status=st,precise_gap_or_counterexample=gap,
  propagation=dict(input_used=inp,where_it_changes_proof=chg,matched_comparison=cmp),
  V_status='not checked: no project Lean/Blueprint; ordinary execution only',remaining_trust=trust,history_only=hist))
# Earlier manifest is used only as a locator/name crosswalk. Each category below
# is assigned an independent derivation/trust and the current replay that verifies it.
history=J(p/'OWN_PRIOR_M_019.json')
cross=[]
rb=['certify-R-0.out','certify-R-1.out','higher-0.out','higher-1.out']
mb=['certify-M-0.out','certify-M-1.out','refine-0.out','refine-1.out','comparison-0.out','comparison-1.out']
an=['ancillary-0.out','ancillary-1.out']
for h in history['claims']:
 id=h['claim_id'];fam=h['family']; w=h['written_source'];f=w['file'];n=w['physical_LF'];z=w['physical_LF_scope']
 hf='OWN_ORIGINAL_007.md' if f==C else f
 assert S[hf]['sha256']==w['sha256']
 cross.append(dict(prior_id=id,prior_source=loc(hf,n,z),current_or_retired_id=id))
 text=h['exact_statement'];domain=h['full_domain'];code=[];rc=[];ck='';gap=None;hist=False;sn=h['strictness'];st=ok
 inp='none (B0)';src=rsrc if fam==R else msrc
 if domain is None:domain='As written; inclusive at the finite start unless specified otherwise.'
 if id.startswith(('RQ-','MQ-')):
  inp='B0 with alternative D02 cap';code=spect;rc=rb+an
  if id.endswith('-cap'):
   code=[];text='QRH cap 7/8; the exact D02 hypothesis implies Re rho<=27/32 without excluding boundary.'
   ck='Euler product and meromorphic log derivative; integral holomorphic on strict half-plane after subtracting pole.'
  elif 'density' in id:
   ck='Cumulative ordinate integral: use positive Taylor moments, running minima, and include cap atoms in the last mesh cell.'
   if id.endswith('default'):
    text='Corrected FKS optional density 6.1727,7.7979,8.2,8.6,9,9.4,9.8,10.2,10.7,11.1 and B=5, or Dusart; at literature trust from Cor. 2.9.'
    src=src+[fks]
  else:
   ck='All-real Perron with stated T, doubled one-sign reciprocal reflection budget, exact subtraction of high-mass baseline; Dusart Dplus for θ.'
 elif id.startswith('R-'):
  code=rprog;rc=rb
  if id in ['R-last','R-local','R-literature-real-failure']:
   code=[('endpoint.py',8,67)];rc=['endpoint.out']+an+(rb if id=='R-last' else [])
   ck='Verified exact prime counts on [n,n+1] and monotone formula with rational bracket. Strict real positivity from inherited integers and closed [36.9,37] bridge, where relevant.'
  if id=='R-literature-real-failure':
   ck='Literal PT early real clause disproved by direct R(38358837682.1)<−7974585; no use as premise.'
  if id.startswith(('R-DP','R-PT')) or id=='R-PI-boxes':
   rc=[];code=[];st=old
   ck='Original result at stated domain, with separately gated shifted argument/normalizer when applicable. The unused literal PT early real clause is excluded.'
  if id in ['R-R-formula','R-R-formula-default']:
   inp='B0 with alternative D02 cap'
   ck='Enclose signed π errors relative to I2; upper square and lower shifted count, full negative square tail and cancellation. Corrected density if selected.'
  if id.endswith(('-1','-D02')):inp='D02'
  if id=='R-diagnostics':
   rc=['diagnostics-0.out','diagnostics-1.out']+an
   ck='Negative sufficient slack only; no counterexample to actual π inequality.'
  src=src+list(h['source_locators'])
 else:
  rc=mb;code=mprog+mmprog
  if id.startswith('M-sign-split'):
   inp='B0 with alternative D02 cap'
   if id.endswith('default'):
    text='Active signed (M) with corrected optional FKS mesh and 130/60 omitted-high tail.'
    src=src+[fks]
   ck='Coarse ordinate-tail positive integral and parts on signed high zeros; low spectrum and Perron remainder separately.'
  elif id.startswith(('M-witness','M-constants-finite')):
   code=fprog;rc=['finite.out'];ck='Sieve and fixed-point outward prime-cell enclosures; integer witness inward conversion. Dusart θ bound supplies constant tails past N.'
  elif id.startswith(('M-analytic','M-finite')):
   code=mprog+fprog;rc=['certify-M-1.out','finite.out'];ck='Real prime cells to 20,000,000 and overlapping analytic log cells via CH2 to 200; monotone L² scaled tail thereafter. Original only.'
  elif id.startswith('M-Dusart-'):
   st=old;code=[];rc=[];ck='Exact distinct original inclusive real thresholds, original constants and relative product normalizers.'
  elif id.startswith(('M-ratio','M-guard','M-targets','M-crossover')):
   inp='D02';code=cprog+mmprog;rc=mb+an
   ck='Checked all-output radii; exact decreasing e^(−L/32) ratio on common domain. Guard uses original source domains, cap/terminal floors and controlled corrections; targets use whole-ray coefficients.'
  elif id.startswith('M-power-'):
   if id.startswith('M-power-1-'):inp='D02'
   if id.endswith('-ram'):
    f='repaired-M-legacy-ram-only.txt';code=mprog;rc=['certify-M-1.out']
   elif int(id.split('-')[-1])>=600:
    code=cprog;rc=['comparison-0.out','comparison-1.out']
  elif id in ['M-source-tables','M-boxes-valid']:
   code=cprog+mmprog;rc=mb+an;src=src+sourcecomp
   ck='Gated original estimates, signed endpoint minus integral of opposite bound, apply conversion only to final valid log radius; restricted FKS repair excludes low failure.'
  elif id in ['M-continuous-C','M-limsup']:
   inp='B0 with alternative D02 cap';code=cprog+mmprog
   ck='Real-part integral with slope <105, and for exact limsup apply exact zero kernel plus dominated convergence and cap-atom bound before negligible product conversion.'
  elif id=='M-direct-D02':
   inp='D02';code=[];rc=an;ck='Integrate u² and u+1 against e^(−au) directly only on L>=200; retained but not used as improvement.'
  elif id in ['M-centers-K','M-tail-products']:
   ck='Parts on (x,∞) with right-continuous endpoints; convergent prime powers give constants and exact log/tail relations. Exponentiate signed log endpoints.'
  elif id in ['M-source-small-false','M-boxes-false']:
   f=hf;hist=True;st=bad;rc=an;code=[];src=src+sourcecomp
   gap=('L=.01, x<2: true relative psi error 1, asserted envelope is <.002.' if id=='M-source-small-false' else 'L=1e−20: bound <20 by integrating 2u^(3/2) through 4 and 59.18/u^4 after; actual W1=−log L−γ>45.')
   ck='Concrete counterexample; retired at repair.md LF10, not used in current envelope.'
  src=list(dict.fromkeys(src+list(h['source_locators'])))
 if id.startswith('M-guard') or id=='M-ratio-default':sn='Strict ordering of valid bound radii, not of true errors.'
 if id=='M-source-tables':text='Gated Chebyshev portfolio, including independently repaired FKS Lemma 5.2 solely on [.85,2100], exact empty sums when x<2; no old false branch.'
 add(id,fam,f,n,text,domain,scope=z,st=st,inp=inp,src=src,ck=ck,rc=rc,code=code,sn=sn,ri=h['real_or_integer'],gap=gap,hist=hist)
# Review each genuinely new table row/connected result at its exact active anchor.
rref=['ramref-0.out','ramref-1.out']+rb
rvals=[('.1','36.94',None),('.5','38',None),('.9','39.56',None),('1','40.16',None),('P1+14/L²','47.45',None),('P1+19/L²','48',None),('P1+42/L²',None,'48'),('P1+82/L²',None,'53'),
 ('P2','216.55','185.6'),('P3','250','209.95'),('P4','285','236'),('P5','319','262'),('P6','355','288'),('P7','392','316'),
 ('P8','426','341'),('P9','462','368'),('P10','498','395'),('P12','571','449'),('P15','680','531'),('P20','862','667')]
for ln,(z,a,b) in enumerate(rvals,19):
 for i,L in enumerate((a,b)):
  if L is None:continue
  cmp=f'B0/B1 sufficient onsets {a}/{b}.' if a and b else ('B0 test not sufficient on same ray (see negative test at 187).' if i else 'B0 branch common to both; no gain.')
  add(f'R-new-{ln}-{i}',R,A,ln,f'G>{z}',f'L>={L}, inclusive for real x=e^L.',inp='D02' if i else 'none (B0)',cmp=cmp,
      rc=rref,code=rrprog+rprog,sn='Strict inequality, inclusive onset.')
for name,z,domain,i in [('p2','P2','52.3<=L<=125',0),('p3','P3','57.7<=L<=91',0),('p4','P4','63.8<=L<=71.8',0),
 ('200-0','P1+116.6/L²','L>=200',0),('200-1','P2+1240/L³','L>=200',1),('240-0','P2+1320/L³','L>=240',0),('240-1','P4+67000/L⁵','L>=240',1)]:
 add('R-new-'+name,R,A,40,f'G>{z}',domain+' as real log domain, endpoints included.',sn='Strict.',inp='D02' if i else 'none (B0)',
     cmp='Retain stronger bounded choices; compare coefficient vectors at each fixed matched ray.' ,rc=rref,code=rrprog+rprog)
add('R-refined-transfer',R,A,42,'Quarter-width log windows and safe upper one-sided input; late π error multiplier 1+1/(L/3−4).',
    'Upper sign shortcut only through L=43.74; late L>=120 per count argument, including L−1 when actual argument is shifted.',
    inp='B0 with alternative D02 cap',scope='42–47',rc=rref,code=rrprog+rprog,
    ck='FiniteRH one-sided report on theta and full-cell domain gating. Integrate (L/u)^2<=e^{4(L−u)/L} on [L/2,L] (all constituent rates <=2/3).')
mnew=[
 {103:(150,'.01751'),104:(160,'.01593'),105:(170,'.01476'),106:(180,'.01386'),107:(190,'.01314'),109:(200,'.01256'),110:(210,'.01207'),111:(220,'.01166'),112:(250,'.01075'),113:(300,'.00981'),114:(400,'.00884'),115:(600,'.00808'),116:(1000,'.00745'),117:(2000,'.00704'),118:(4000,'.00685'),119:(10000,'.006735')},
 {103:(130,'.416'),104:(140,'.353'),105:(150,'.311'),106:(160,'.282'),107:(169,'.263'),108:(170,'.261'),109:(180,'.245'),110:(185,'.238'),111:(190,'.232'),112:(200,'.221'),113:(210,'.213'),114:(220,'.205'),115:(250,'.189'),116:(300,'.172'),117:(400,'.155'),118:(600,'.141'),119:(1000,'.130'),120:(2000,'.123'),121:(4000,'.120'),122:(10000,'.1175')}]
scaled='L|maximal unweighted absolute error| (both relative products and E1), and |Ew|'
for i,tab in enumerate(mnew):
 for ln,(L,v) in tab.items():
  add(f'M-new-{i}-{L}',M,A,ln,f'{scaled}, each <= {v} exp(−{["L/8","5L/32"][i]}).',f'All real L>={L}, inclusive.',
      inp='D02' if i else 'none (B0)',cmp='Take the minimum against all applicable baseline/other exponent rows; matched crossover algebra retained.',
      rc=['refine-0.out','refine-1.out'],code=mmprog)
for i,text in enumerate(['.01343 exp(−L/8)','.265 exp(−5L/32)']):
 add('M-connected-'+str(i),M,A,124,f'Each scaled all-output error <= {text}.',
    'Products x>=2278382, E1 x>=2278383, Ew x>=912560, inclusive and real.',scope='124–130',inp='D02' if i else 'none (B0)',
    ck='Convexity endpoints through L=50; CH2 and exact weighted kernel split to L=185.8/167.75 plus valid spectral bounds beyond. Explicit log cap for product conversion.',rc=['refine-1.out'],code=mmprog)
for j,L,v in [(1,'18.05','.08'),(1,'18.15','.077'),(1,'20','.037'),(0,'17.95','.079'),(0,'18','.0774'),(0,'20','.035')]:
 add(f'M-new-poly-{j}-{L}',M,A,132,f'{"Each product relative error and |E1|" if j else "|Ew|"} <= {v}/L^{3 if j else 2}.',
   f'All real L>={L}, inclusive.',ck='Use improved Dminus at x>=121 in closed cells; CH2 and spectral joins to 200; drop subtraction in decreasing tail.',rc=['refine-1.out'],code=[('refine.py',160,175)])
for id,n,z,text,domain,ck in [
 ('refined-split',51,81,'Stratified real-part omitted-zero estimates and (M*) signed kernel.','u,L>=130 for mesh, >=600 for used continuous branch.',
  'Real-part-cell density integral with rates 1−t+d/2 and 1−t+1/2. Exact kernel endpoint cancellation gives integral of e^((rho−1)u)/u^j. Complex parts yields minimum multipliers, absolute convergence and cap limsup.'),
 ('refined-continuous',83,88,'Full-height quartic moment slope <105; caps <.006664 and <.116246.','L>105 for continuous spectral mass; used from 600.',
  'Geometric ratios bound mean index in quartic moment, then real-part integration gives L/(L−105); exact kernel controls limsup.'),
 ('refined-signed-powers',90,95,'Stronger Dminus, full T_j nonnegative lower tails, unscaled product-tail subtraction.','x>=121, zero lower fallback below.',
  'Dusart Prop.4.3, decreasing eta and lower u^-k exponential, subtract upper endpoint then A in unscaled product. No separate signed-envelope executable claimed.'),
 ('restricted-FKS',10,10,'FKS Lemma 5.2 radius restricted to [.85,2100].','[.85,2100] real, includes boundaries.',
  'On [.85,1] exact psi=log2; [1,40] endpoint minimum >.77 and Dusart 3.3; strict original step values above 40 and 1000 gated with preceding interval at equality.'),
 ('refined-comparison',134,134,'Matched row ratio (.221/.01256)e^(−L/32)<.035; target 1e−14 at 223/197 and 1e−18 at 295/255.','L>=200 for ratio; inclusive stated target rays.',
  'Use valid all-output scaled rows and decreasing endpoint ratios; same matched error scale.'),
 ('refined-guard',136,136,'Strict dominance over enumerated B0 envelope for all four scaled radii from L=169.','All real L>=169.',
  'Original endpoint floor g=min(1.047e−12,.005e^(−L/8)), monotone source ratios, mesh and continuous floors. Corrections/log conversion lose <.02g; B1 already below .9g and both ratios decrease.')]:
  add('M-'+id,M,A,n,text,domain,scope=f'{n}–{z}',
      inp='none (B0)' if id in ['refined-signed-powers','restricted-FKS'] else 'B0 with alternative D02 cap',
      ck=ck,src=msrc+(sourcecomp if id in ['restricted-FKS','refined-guard'] else []),rc=['refine-1.out']+an,code=mmprog+(cprog if 'guard' in id else []))
# Retired incorrect proof variants are not active rejected inequalities.
for fam,pre in [(R,'RQ'),(M,'MQ')]:
 for id,n,z in [('density-default',107,107),('psi-B-default',124,140)]:
  add('hist-'+pre+'-'+id,fam,'OWN_ORIGINAL_007.md',n,'Historical default density 5/6.3 or its dependent bound, retired.',
    'Old two bands [.70,.75), [.75,.80); dependent explicit-formula u>=60.',scope=f'{n}–{z}',hist=True,st=miss,
    src=[fks],ck='Compare original lower two table constants directly.',gap='No source justification for 5 and 6.3; original Table 8 has 6.1727 and 7.7979.',
    rc=an,code=[('OWN_ORIGINAL_024.py',52,70)],retain=[pre+'-'+id])
add('hist-M-sign-split-default',M,'OWN_ORIGINAL_007.md',228,'Old unsupported 106/60 coarse proof, not active numerical rows.', 'Old L>=60.',scope='228–250',hist=True,st=miss,
 src=[fks],gap='Old 106 used first-band density 5. Corrected proof needs 130 via submitted inequality (60 remains valid); refined proof separately restores tight constants.',
 rc=an,code=[('OWN_ORIGINAL_022.py',11,21)],retain=['M-sign-split-default','M-refined-split'])
add('hist-R-R-formula-default',R,'OWN_ORIGINAL_007.md',154,'Old unsupported default numerical branch propagated under-transcribed density.','L>=36.9, with spectral gates.',hist=True,st=miss,
 src=rsrc+[fks],gap='Original density constants are larger; algebra survives with corrected or independent Dusart proof.',retain=['R-R-formula','R-R-formula-default'])
add('quoted-PT-real',R,C,208,'Literal early PT real clause, explicitly unused/disproved.','38358837682<x<=e^58',hist=True,st=bad,
 src=['PT Theorem 2 PDF p.3 LF205–212'],gap='At x=38358837682.1, R<−7974585 by exact counts and outward e/log.',rc=an,retain=['R-last'])
for x in cross:
 ids={r['claim_id'] for r in rows}
 if 'hist-'+x['prior_id'] in ids:x['history_only_original_gap_id']='hist-'+x['prior_id']
assert len(cross)==153 and len({x['claim_id'] for x in rows})==len(rows)
def family(f):
 return dict(strongest_supported_portfolio=[x['claim_id'] for x in rows if x['family']==f and not x['history_only'] and x['M_status'] in (ok,old)],
 rejected_or_incomplete_claims=[x['claim_id'] for x in rows if x['family']==f and not x['history_only'] and x['M_status'] in (bad,miss)],
 retired_or_disputed_nonpremises=[x['claim_id'] for x in rows if x['family']==f and x['history_only']],remaining_assessment_work=[],
 summary=('Exact strict real sign ray and all earlier/later matched margin branches, with no D02 improvement to the last actual failure.' if f==R else 'Old and refined rows, finite/log joins, signed transfers, two reciprocals and related sums; strict matched enumerated guard at L=169.'))
hashf=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
actual=J(o/'receipts.json')
assert len(actual)==20, len(actual)
for r in actual:assert r['status']==(1 if r['name']=='audit' else 0)
assert len((o/'ancillary.status').read_text().splitlines())==2
for line in (o/'ancillary.status').read_text().splitlines():
 i,v=line.split();assert v=='0'
 n='ancillary-'+i
 actual.append(dict(name=n,argv=['/usr/bin/python3.10','/work/submission/ancillary.py'],cwd=str(o),env={'LC_ALL':'C','RAM_ONLY':i},status=int(v),stdout_sha256=hashf(o/(n+'.out')),stderr_sha256=hashf(o/(n+'.err'))))
for i in (0,1):assert 'not certified' not in (o/f'ramref-{i}.out').read_text()
catalog={}
for row in rows:
 for a in row['implemented_formula_sources']:
  key=a['file']+':'+str(a['physical_LF_scope'])
  lo,hi=map(int,a['physical_LF_scope'].split('–'))
  if key not in catalog:catalog[key]=dict(source=a,exact_LF_text=(p/a['file']).read_text().split('\n')[lo-1:hi])
  a['readback_key']=key
review=dict(implemented_formulas_catalog=catalog,schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=idx['candidate_id'],assessment_complete=True,all_claims_inventoried=True,
 reviewed_source_hashes={r[k]:r[k+'_sha256'] for r in bib for k in ['pdf','text']},source_bibliography=bib,exact_input=J(t/'INPUT_CONTRACT.json'),
 candidate_files=idx['candidate_files'],actual_effort_and_verification_commands=actual,finite_binary_sha256=(o/'binary-sha256.txt').read_text().strip(),
 family_assessments={f:family(f) for f in (R,M)},claims=rows,own_history_claim_crosswalk=cross,no_other_arm_or_ranking_seen=True,
 new_core_math_salvage_performed=False,original_candidate_bytes_changed=False,not_blind_to_disclosed_own_history=True,
 prep_and_limits='Used exact candidate restoration and original PDF/text pairs. B0 is within-method including common QRH, D01 unavailable. Raw audit.py missing historical projection index; wrapper verifies actual supplied history. Executor reset required byte-exact local restoration and rerun. No project Lean/Blueprint or source-first PV.')
(o/'review.json').write_text(json.dumps(review,indent=2,ensure_ascii=False)+'\n')
(o/'STAGE_STATUS.json').write_text(json.dumps(dict(ready_for_review=True,families={f:dict(status=ok,claim_files=['review.md','review.json']) for f in (R,M)},serious_attempts_documented=True),indent=2)+'\n')
print('INVENTORY',len(rows), 'historical crosswalk',len(cross))
