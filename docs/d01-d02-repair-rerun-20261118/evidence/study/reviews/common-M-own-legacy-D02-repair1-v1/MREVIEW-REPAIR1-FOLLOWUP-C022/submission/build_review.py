#!/usr/bin/python3.10
"""Assemble the independent audit. Own review JSON is read as a statement/locator
inventory only, never to assign mathematical status or carry over evidence."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json, re, ast
from replay_review import MATCH, OLD, SPEC, NEW
D=Path('/work/submission')
C=Path('/work/exact')
idx=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
rows={r['original_name']:r for r in idx['candidate_files']}
byhash={}
for r in rows.values(): byhash.setdefault(r['sha256'], []).append(r['original_name'])
def lines(n):return (C/n).read_text().split('\n')
def dig(p):return sha256(p.read_bytes()).hexdigest()
def loc(f,a,b=None):
    if not (1<=a<=len(lines(f)) and (b is None or a<=b<=len(lines(f)))): raise ValueError((f,a,b))
    t=rows[f]
    return {'file':f,'physical_LF':a,'physical_LF_end':b or a,'sha256':t['sha256'],'packet_name':t['packet_name']}
def stale(w):
    f=w['file']; h=w['sha256']
    if f not in rows or rows[f]['sha256']!=h: f=byhash[h][0]
    return loc(f,w['physical_LF'],w.get('physical_LF_end'))
S='supported_at_stated_trust_tier'
B='baseline_retained'
W='equivalent_or_weaker'
G='incomplete_with_specific_missing_step'
F='false_with_specific_counterexample'
R='Ramanujan'
M='Mertens'
E='E=max(L times both absolute relative product errors, L|delta_S|, |delta_V|)'
v='Written and ordinary arithmetic; no Lean/PV'
trust='Original literature/computations and ordinary runtime'
src={
'strip':['OpenAIQRH p.4 Thm 1.1 (LF255–262)','/task/INPUT_CONTRACT.json: PsiMajorant','FKS §2 p.4'],
'screen':['FKS pp.4–5 (2.1)/Cor.2.3/Table 1; pp.7–8 Cor.2.9/(2.17); p.26 Table 8 first panel only; Thm.3.2 (3.2) p.8','FiniteRH p.2 Thm.1','Dusart p.5 Thm.2.3, p.13 Cor.4.5'],
'smooth':['CH2 pp.40–42 App.A, p.43 Cor.B.2, p.46 (B.9)','Dusart p.13 Cor.4.5','FKS p.2 Cor.1.4 and p.5 (2.1)'],
'count':['PT2021 p.8 finite pi quotation; p.9 Lemma 6','FiniteRH p.4 Cor.1, p.5 §3.3','CH2 p.3 Cor.1.2–1.3, p.35 Lemma 9.2','Dusart p.13 Cor.4.5'],
'rootR':['PT2021 p.3 Thm.2 and §5 pp.8–11 (low interval integers only)','Dudek–Platt v1 p.2 Thms.1.2–1.3'],
'M':['Dusart pp.17–20 Thms.5.6–5.9 and p.13 Cor.4.5','CH2 p.3 Cor.1.2–1.3, pp.35–36 Lem.9.2/Cor.9.3','FiniteRH p.4 Cor.1/p.5 §3.3'],
'finite':['Dusart pp.11–12 Thm.4.2 and pp.17–20 Thms.5.6–5.9'],
'Qfree':['Dusart p.5 Thms.2.3–2.4; FKS pp.2,5,8 Cor.1.4, (2.1), Thm.3.2; CH2 p.3 Cor.1.3']
}
rec={
'R':['d02ram_repair_replay.out','current-replay.status','ancillary.stdout'],
'M':['d02m_repair_replay.out','d02finite_replay.out','current-replay.status'],
'r':['endpoint_check_repair_replay.out','ancillary.stdout'],
's':['d02secondary_repair_replay.out','d02m_repair_replay.out'],
'D01R':['portfolio_check.stdout','ramDus.stdout','prefix.stdout','ancillary.stdout','extra_check.stdout'],
'D01M':['mertens_new.stdout','mertensDus.stdout','finite26.stdout','finite20b.stdout','finite100m.stdout','mertens_check.stdout','audit_summaries.stdout'],
'limits':['repair_limits_repair_replay.out','current-replay.status']
}
D02='B0+D02; no full RH'
B0='B0 and stated computation'
nq='Non-QRH originals and ordinary computation'
history=[]
claim=[]
def add(id, fam, locat, st, dom, assume, status=S, kind='R', sources='count', 
        read=(), dcheck='', why='', prop='', match='', strict='as written', retains=(), active=True):
    if not match: match=('B0 and B0+D01 identical by logical implication; D02 improves only where specified.'
                          if assume==D02 else 'Same on matched cumulative domains.')
    if not prop: prop='No added premise.'
    refs=[loc(*p) for p in read]
    claim.append(dict(claim_id=id, family=fam, written_source=loc(*locat), exact_statement=st, assumptions=assume,
        full_domain=dom,strictness=strict,real_or_integer='Real except as specified',
        baseline_comparison=match,source_locators=src[sources],executable_readback=refs,
        derivation_check=dcheck,numerical_obligations='See receipts and whole-domain proof.',
        actual_verification_receipts=rec[kind],retained_valid_branches=list(retains),M_status=status,
        precise_gap_or_counterexample=why,propagation=dict(input_used='D02' if prop!='No added premise.' else 'none',
            where_it_changes_proof=prop,matched_comparison=match),V_status=v,remaining_trust=trust,
        active_conclusion=active))
    return claim[-1]
# Current shared mathematical inputs, and their literal implementation locators.
for fam in (R,M):
    t=fam[0]
    for key,a,b,statement,domain,sc,code,check in [
      ('strip',60,75,'D02 implies every nontrivial zeta zero has beta<=27/32, not boundary exclusion.','All nontrivial zeros; A used only on x>=e^200','strip',(), 'Mellin normal convergence; residue of log derivative; review §1.'),
      ('moments',93,134,'Jensen integrated moment W_m(s;c,d) bounds 2 sum_{beta>s,gamma>0} gamma^(-m) for m=1,2.','s in screened intervals from .72 through cap; height from H','screen',(('d02screen.py',5,46),),'H admissible; affine powers, positive Jensen measure; no second panel.'),
      ('chord',136,196,'Terminal Dusart chord plus optional regular same-block chords; B1 sharp <= B1; limits w_b<.116297 (m=1), <2.506e-14 (m=2).','L>=155 for use in applications; screened moment itself L>0','screen',(('d02screen.py',49,105),),'Proof by convexification of exact integrated bound; weights and terminal allowance positive.'),
      ('recip',200,224,'Signed explicit formula at c*=.35; total reciprocal <= y²/6+3 and off-line right half <= (y²-h²)/12+.1, with second bound sharpened at c*=.27.','real L>=155; auxiliary heights satisfy y>=h','screen',(('d02screen.py',108,124),('d02screen.py',135,157)),'Original FKS theorem and log product; reflection, inclusive limit.'),
      ('C',226,268,'|e_psi(L)|<=e^(-aL) C(L), min of .35 and sharper .27 curve for D02, and theta adds 3e^(-L/2).','real L>=155','screen',(('d02screen.py',108,128),),'Monotone scaled screened curve and legal cutoff; no unsmoothed double payment.'),
      ('C168',263,265,'At and above 168 the absolute psi relative allowance is strictly smaller than A0.','real L>=168','screen',(('d02m.py',119,125),),'Decreasing bound from closed endpoint.'),
      ('C200',264,268,'C<.215402 from L=200; <.213 from 204, not asserted at 200.','real L>= respective start','screen',(('d02m.py',173,184),),'Combined guard exceeds C and passes the two rows.'),
      ('triangle',292,304,'Density-free FKS cutoff .19 gives |e_psi|<.0034 L² e^(-aL).','real L>=155','screen',(('d02screen.py',130,157),),'Reciprocal sums only; exact T validity and monotone normalized guard.'),
      ('J',306,338,'Exact J1 residue sum, J2 further primitive, and positive j,j2 allowances in terms of m=2 screen.','L>=18.42 quantitative; refined k from 155; coarse prefix from 20 as written','smooth',(('d02screen.py',126,128),('d02m.py',8,13),('refine.py',73,77)),'Absolute integrated kernel derivation; CH2 reciprocal-square bound; all joins and trivial signs checked.')]:
        p=('Replace 7/8 cap and e^(-L/8) by 27/32 and e^(-5L/32) in the convergent off-line moments or screened unsmoothed terms, without evaluating A below e^200.')
        add('D02.'+t+'.'+key,fam,('D02.md',a,b),statement,domain,D02,kind=t,sources=sc,read=code,dcheck=check,prop=p)
    add('D02.'+t+'.D01-tie',fam,('D02.md',76,89),'B0 implies exact D01 and hence ties B0+D01 on all matched domains.','real L>=200 for implied input',B0,B,kind=t,sources='screen',read=(('d02screen.py',161,164),),dcheck='Scaled coefficient decreases and is <1/64 at left endpoint.')
    add('D02.'+t+'.CH2H',fam,('D02.md',270,289),'Full-height CH2 A_H+d_H e^(-L/2) and weighted counterpart π/(H−1)+d_H e^(-L/2), strictly better than the two Cor.1.3 error allowances on their overlap.','real x>H (strict)',nq,kind='limits',sources='count',read=(('repair_limits.py',6,12),),dcheck='Cor.1.2 at verified H; correct coth recentering and strict open domain.')
# Ramanujan claims.
def rr(id,line,statement,domain,code=(148,222),assume=D02,p='Faster screened count errors at both log arguments through the transition and tail.',match='',section='R',end=None,status=S,check='See review §2: closed cells plus scaled monotone tails; count at both arguments.'):
    return add('D02.R.'+id,R,('D02_R.md',line,end),statement,domain,assume,status,kind=section,sources='count',read=(('d02ram.py',*code),),dcheck=check,prop=p,match=match,strict='strict lower profile unless comparator/formula specifies otherwise')
add('D02.R.sign',R,('D02_R.md',11,29),'R>0 exactly as a sharp open ray x>r; R(r)=0; r in the written 20-decimal bracket; least integer start N+1.','real x>r; equality at r; integer n>=38358837683',B0,B,kind='r',sources='rootR',read=(('endpoint_check.py',25,66),),dcheck='Exact quotient sieve and strict derivative on first unit; publication used only at integers and overlaps analytic continuation.')
for line,on,z in zip(range(39,45),['27.8','27.95','28.24','28.77','29.60','30.45'],['.01','.10','.25','.50','.80','1']):
    rr('early'+on,line,f'G(L)>{z}',f'L>={on}',(61,80),B0,'No added premise.','The new extensions through 30.8 use even QRH-free premises; inherited whole ray joins at 30.8.')
for line,on,k in zip(range(56,63),['49','49.5','169.2','172.1','177','182','185.21'],['65.56','83.11','90.95','110.29','130.28','141.03','145']):
    rr('K'+k,line,f'G(L)>1+14/L+{k}/L²',f'L>={on}',(159,170),match='Keep B0 K=22 from 49 and K=90 on [50,164]; fixed 145 starts at 219 in inherited B0 and 217 in same-method integer-log test; profiles compared on intersections.')
for i,(on,u) in enumerate([('185.3',18),('185.5',54),(186,140),(188,436),(190,667),(195,1046),(200,1249),(205,1358),(207,1385)]):
    rr('third'+str(on),(73 if i<4 else 74),f'G(L)>1+14/L+145/L²+{u}/L³',f'L>={on}',(171,175),end=75)
rr('asymptotic-K',77,'If K>145 is fixed the two-correction lower profile cannot hold eventually.','L->infinity',(5,20),B0,'No added premise.',end=78,check='Finite-order asymptotic expansion from the two-sided error envelope.')
rr('raw',79,'G(L)>1+12.5/L without density or inferred strip','L>=49, raw hypothesis only on both arguments beyond 222',(191,203),D02,'Use A directly in exact anchored count estimate starting at 200; CH2 finite cells to 222.','Old density-free 1+3/L from 50; both smaller-premise alternatives retained.',end=83)
explicit={3:99,4:100,5:101,6:102,7:103,8:104,9:105,10:106,11:107,12:108,13:109,14:110,16:111,20:112,24:113,28:114,32:115,36:116}
for i,t in enumerate(lines('repair_r_results.txt')[35:69],36):
    k,N,on,base=map(int,t.split()[:4]); assert i==33+k
    exact=f'G(L)>sum_(j=0..{k-1}) a_(4+j)/L^j (factorial coefficients D02_R.md LF85–91; N={N} in check)'
    st=rr('poly'+str(k),explicit.get(k,118),exact,f'L>={on}',(113,142),match=f'B0=B0+D01 same-method sufficient onset {base} at matched strength (failure of that test at {on}, not inequality false).')
    if k not in explicit: st['written_source']=loc('repair_r_results.txt',i); st['linked_declaration']=loc('D02_R.md',118,123)
    st['actual_verification_receipts']=['d02ram_repair_replay.out LF'+str(i),'current-replay.status']
    st=rr('B0poly'+str(k),explicit.get(k,118),exact,f'L>={base}',(113,142),B0,'No added premise.',f'Within-method B0 cap comparator, D02 at {on}; do not treat as independent baseline search.',status=B)
    if k not in explicit: st['written_source']=loc('repair_r_results.txt',i); st['linked_declaration']=loc('D02_R.md',118,123)
    st['actual_verification_receipts']=['d02ram_repair_replay.out LF'+str(i),'current-replay.status']
for key,L,n,label in [('uniform32','32n',6,130),('uniformc','27.6443n−4 log n−2',20,132)]:
    rr(key,label,'G(L)>sum_(j=4..n−1) a_j/L^(j−4) for each integer n in range',f'integer n>={n}, real L>={L}',(204,218),check='Uniform factorial remainder and n-dependent monotonicity, review §2; not extrapolation of discrete table.')
for key,ln,s,margin,dom in [('shift67.7',143,'(1+13/L+67.7/L²)/L^4','x²/L^8','L>=58'),('shift68',144,'(1+13/L+68/L²)/L^4','.74 x²/L^8','L>=58'),('shift12',145,'(1+12/L)/L^4','(1+69/L)x²/L^7','L>=58'),('shift68pieces',148,'(1+13/L+68/L²)/L^4','x²/L^8','L in [58,167] or [172,infinity)')]:
    rr(key,ln,f'R_y>{margin} for y=(x/e)(1−s), s={s}',dom,(176,190),match='Keep inherited 12-only .19 margin; cutoffs use actual log y; failed 68 central margin-1 reserve not refutation.',check='Shifted cost and log y domain; per-cell closed join, separately monotone upper errors on tail.')
rr('shift-limit',155,'No eventually positive shifted family if alpha>13 or alpha=13 and beta>131 at fixed parameters.','L->infinity',(85,91),B0,'No added premise.',end=157,check='Expand exact Li difference at the shifted argument.')
for id,a,b,st,do,co,bs in [
 ('PV',161,173,'Exact PV centered count formula, constant 2/log2−li(2).','x>=2',(34,44),B0),
 ('D2',175,202,'D2=e^(-at)C+3e^(-t/2)+H_s as written; CH2 boundary plus H_s alternate.','t>=155 for D2, t>=58 for CH2 branch',(34,59),D02),
 ('Draw',204,212,'D_raw=(t²+t/b)e^(-at)/64+3e^(-t/2)(1+1/(.49t))+7e−15(t/200)e^(200−t).','t>=200',(144,146),D02),
 ('signed-low',214,245,'Upper 3t e^(-t) under theta sign, lower magnitude D_low^- as written on its interval.','2<=exp(t)<=10^19 upper; [20,29.9] lower',(61,80),nq),
 ('two-sided',247,257,'F-centered lower envelope (252) and upper counterpart using clipped square; all fixed asymptotic orders.','where both log arguments meet chosen bounds',(73,80),D02),
 ('D2dom',258,269,'D2<.245e^(-at) from t=175 and improved named B0 shaped errors at both arguments from L=176.','t>=175; L>=176 for gap',(204,210),D02),
 ('rem',273,304,'Strict normalized li bracket P_N−f_Ne^(1−t)<F<P_N+d_N and factorial coefficient formula.','integer N>=17 in finite tables, t>N+1; arbitrary order as stated',(5,20),B0),
 ('loss',306,345,'Explicit E_N, E_pi, strict polynomial lower envelope and closed cell / L^N tail method.','those intervals and tails in §3',(22,32),D02),
 ('caps',400,407,'D2 coefficient .24 from t=180 and .144 from 535; derived count allowances .79 and .47.','t>= starts; two arguments applied at L>=192 or >=536 respectively',(204,211),D02)
 ]: rr(id,a,st,do,co,bs,'No added premise.' if bs in (B0,nq) else 'Use the relevant bound at both x and x/e; A changes spectral rate or the direct integral.',end=b,status=S)
# Current Mertens.
def mm(id,line,st,do,code=(151,205),assume=D02,p='In the bridge/tail, use off-line spectral rate 5/32 and the lawful paired-pole screen; finite observations unchanged.',match='',end=None,status=S,check='Review §3: log normalization, relative conversion, finite overlaps and monotone analytic tail.',kind='M',srcid='M',ret=()):
    return add('D02.M.'+id,M,('D02_M.md',line,end),st,do,assume,status,kind=kind,sources=srcid,read=(('d02m.py',*code),),dcheck=check,prop=p,match=match,strict='strict in numeric E rows except symbolic or explicit non-strict bounds',retains=ret)
for i,(x,al,c) in enumerate([(180223318,'1/8','.001354'),(300000,'9/64','.018643'),(300000,'5/32','.256707')],30):
    mm('whole'+al,i,f'{E}<{c} x^(-{al})',f'real x>={x}',match='Compared on overlap via exact power-ratio threshold; against B0 .0149, do not compare just coefficients.')
for i,(L,c) in enumerate([(168,'.256418'),(170,'.252899'),(175,'.244823'),(180,'.237637'),(190,'.225412'),(200,'.215402'),(225,'.196863'),(250,'.184130'),(300,'.167809'),(400,'.151060'),(600,'.137363'),(1000,'.128081')],64):
    mm('fast.'+str(L),i,f'{E}<{c} x^(-5/32)',f'L>={L}',(173,182),match='At matched L>=175 dominates the named B0 1/8 power screen; below that apply exact intersection of domains and envelopes.')
for i,(L,c) in enumerate([(173,'.248838'),(175,'.245767'),(185,'.232384'),(195,'.221577'),(204,'.213'),(205,'.212654'),(228,'.195899'),(181,'.238698'),(180,'.239'),(1000,'.129304')]):
    r0=mm('fast.extra.'+str(L)+c,77,f'{E}<{c} x^(-5/32)',f'L>={L}',(173,182),end=82)
    if L==181 or c=='.239':
        r0['written_source']=loc('repair_m_results.txt',24 if L==181 else 30)
        r0['linked_declaration']=loc('D02_M.md',77,82)
for L,c in [(168,'.261492'),(175,'.249146'),(180,'.241556'),(200,'.218341'),(250,'.186256')]:
    mm('dusart.'+str(L),84,f'{E}<{c} x^(-5/32) with Dusart-only density',f'L>={L}',(183,184),end=86,match='Less density provenance (still FKS signed formula); preserve alongside sharper first-panel variant.')
for i,(L,q,c) in enumerate([('59.5',2,'5.30e-8'),('60.98',2,'2.951e-8'),('59.5',3,'4.952e-6'),('59.5',4,'.0008311'),('59.5',5,'.13950'),('59.5',6,'23.412')],93):
    mm('log'+str(q)+'.'+L,i,f'{E}<{c}/L^{q}',f'L>={L}',(155,172),B0 if i==93 else D02,
       'No added premise.' if i==93 else 'D02 cuts the unsmoothed payment in the 167.84 bridge and high ray.',
       'B0 log-square 5.30e−8 from 59.5; D02 smaller 2.951e−8 from 60.98; the smaller old target passes only later.')
for q,c in enumerate(['2.944e-8','4.935e-6','.0008274','.13872','23.257'],2):
    mm('logLate'+str(q),100,f'{E}<{c}/L^{q}','L>=168',(185,192),end=102)
mm('mixed',103,f'{E}<=Z(L0)L0^q exp((alpha−a)L0) x^(-alpha)/L^q','L>=L0>=155, q>=0, alpha<=a, q<=(a−alpha)L0',(15,21),end=107)
mm('allLog',109,f'{E}<23.412 T0^(q−6)(v/T0)^q exp(−a(v−T0))/L^q','real L>=59.5, real q>=6, T0=167.84, v=max(T0,q/a)',(164,172),end=119)
for al,c,L in [('1/8','.001323',169),('9/64','.018165',171),('5/32','.249412',173)]:
    mm('late'+al,52,f'{E}<{c}x^(-{al})',f'L>={L}',(185,192),end=55)
for al,c,x in [('1/8','.001323',250000000),('9/64','.018165',300000),('5/32','.249412',300000)]:
    mm('bounded'+al,47,f'{E}<{c}x^(-{al})',f'{x}<=x<=e^59.5',(90,108),nq,'No added premise.',end=55)
for ln,s in enumerate(lines('repair_tape.txt'),1):
    if 28<=ln<=39:
        k,x,y,z=map(int,s.replace(':','').split())
        for j,(n,vv) in enumerate(zip([x,y,z],['P,Q','S','V'])):
            r=mm('level'+str(k)+'.'+vv,47 if k<=1350 else 34,
                 f'Scaled {vv} error ({E} component) < {k}/10^6 x^(-1/8)',
                 f'x>={n}' if k>=1354 else f'{n}<=x<=e^59.5',(167,205),D02 if k>=1354 else nq,
                 'D02 supplies whole-ray extension beyond e^59.5 where stated.' if k>=1354 else 'No added premise.',
                 end=55,ret=('D02.M.late1/8',))
            r['written_source']=loc('repair_tape.txt',ln);r['linked_declaration']=loc('D02_M.md',34 if k>=1354 else 47,45 if k>=1354 else 52)
            r['executable_readback']+=[loc('d02finite_repair.cpp',198,239)]
for key,a,b,st,domain,code,assume in [
 ('normalize',3,20,'Definitions and signed product exponentiation, common E; correct M,B3.','x>=2 in proof-bearing domains',(15,21),B0),
 ('Abel',138,159,'Exact U_i transfer and prime-power corrections at all jumps; alternative theta transfer.','real x>=2',(15,21),B0),
 ('JK',161,177,'|integral e_psi K|<=Kj+2|K′|j2; better off-line term after D02.','L>=18.42',(8,13),D02),
 ('signed',179,195,'Separate signed delta_V,delta_S,delta_Q and exponential product intervals; preserve observed-boundary case.','L>=18.42; screen starts 155; direct A at 200',(61,71),D02),
 ('actual-corrections',209,233,'Sharper Abel brackets for k=2,3 and elementary remainders k>=4 as written.','L>=18.42; use inputs at each y root on matching domain',(8,13),B0),
 ('Z',237,281,'Joint pole cancellation gives Z=z/(1−ze^(-aL)/L), E<=Z e^(-aL); intersects with signed intervals.','L>=155',(15,42),D02),
 ('limit',277,281,'limsup x^(5/32) E<.116297.','as x->infinity',(15,21),D02),
 ('bridge',285,316,'Convex scaled CH2 bridge through 167.84 and monotone scaled Z thereafter; B0 split at 188.','each closed interval and the respective tails',(151,172),D02),
 ('finitejoin',318,370,'Finite pre-jump/terminal tape guards and required analytic real overlap, as written.','finite26 to 100M; repair tape to 250M, finite20b to 20B; closed analytic cells to L=59.5',(61,117),B0),
 ('dominance',383,423,'Dominance over named B0 boundary allowances from 175; B0 transition cost near 184; exact power/log crossover rules.','L>=175 or matched domains as stated',(119,135),D02),
 ('boundary',425,452,'Possible boundary harmonics at beta=b, denominators rho and rho−1 and inverse obstruction to little-o.','L->infinity; conditional not an existence assertion',(15,21),D02)
 ]:
    mm(key,a,st,domain,code,assume,'No added premise.' if assume==B0 else 'D02 changes off-line exponent/screen and remaining spectral boundary.',end=b)
add('D02.M.general-kernel',M,('D02_M.md',197,208),'Literal general kernel inequality with only decreasing differentiable f>=0 and tf(t)->0.', 'y in the bound domain',B0,G,kind='M',sources='M',dcheck='Abel verifies it for the actual convergent kernels.',why='Need integral finiteness: f(t)=1/(t log t) on [2,infinity) satisfies the written size conditions but both terms diverge; the absolute difference is undefined. Not a counterexample to the actual correction bracket.',retains=('D02.M.actual-corrections',))
for key,dom,mline in [('products','[r_P,infinity)',121),('reciprocal-sum','[r_S,infinity)',124),('weighted','[r_V,infinity)',124)]:
    mm('sharp.'+key,mline,'Exact original benchmark sharp '+key+' root in the stated bracket, equality allowed.',dom,assume=B0,p='No added premise.',end=133,status=B,kind='D01M',check='Fixed-prime-state derivative; matching Dusart starts and finite tie/counterexample evidence.')
# Secondary rows.
def sec(id,a,b,st,do,co,scope='D02 changes the spectral exponent used in the quantitative bound.'):
    add('D02.sec.'+id,M,('D02_secondary.md',a,b),st,do,D02,kind='s',sources='screen',read=(co,),dcheck='Review §4: complete stated whole-domain derivation.',prop=scope)
sec('primorial',8,12,'Specified primorial relative error <3.273e−13 x^(−a)/L.','L>=155',('d02m.py',137,149))
sec('limsup',13,15,'Specified primorial limsup in Lx^a scale <2.506e−14.','x->infinity',('d02m.py',137,149))
for L,c in [(169,'.513'),(174,'.4982')]:
    sec('extreme'+str(L),51,73,f'|e^−γ max_(1<=n<=N) n/phi(n)−log log N|<{c}(log N)^(-a); corresponding sigma/n upper bound.',f'real log log N>={L}, n integer',('d02secondary.py',19,28))
for ln,(L,C0,g,m) in enumerate([(168,'.256418','.514','.0011'),(180,'.237637','.476','.0007'),(200,'.215402','.432','.0011'),(173,'.248838','.499','.000999'),(185,'.232384','.465','.00023'),(204,'.212','.426','.00069')],81):
    sec('short'+str(L),ln,ln,f'At y=x+{g}x^b, pi(y)−pi(x)>{m}x^b/log y using theta cap {C0}.',f'L>={L}',('d02secondary.py',7,18))
sec('correlated',96,194,'At y=x+g, g=x^(5/8)L^(207/20), pi(y)−pi(x)>.81g/log y.','L>=100000',('d02secondary.py',29,44),'Difference of common spectral terms with smaller right cap permits smaller log length than B0 L^14 at the same onset and relative margin.')
# Independently audit every band and threshold from exact finite tape output.
tapes={
 'finite100m.txt':('finite100m.stdout','finite_opt.cpp',10**8,7,10**9,3),
 'finite20b.txt':('finite20b.stdout','finite_opt.cpp',2*10**10,1,10**9,3),
 'finite26.txt':('finite26.stdout','finite_opt.cpp',195729609429,1,10**9,3),
 'D01__SUBMITTED_008.txt':('old-007.stdout','D01__SUBMITTED_007.cpp',26489122130,9,10**6,2),
 'repair_tape.txt':('d02finite_replay.out','d02finite_repair.cpp',250000000,4,10**9,3)
}
bandpat=re.compile(r'\[(\d+),(\d+)\] : (\d+) (\d+) (\d+)')
thrpat=re.compile(r'(\d+) : (\d+) (\d+) (\d+)')
def bands(n):
    st,out,fin,ray,unit,first=tapes[n]
    assert (D/st).read_bytes()==(C/n).read_bytes()
    band=[];threshold=[]
    at='repair' if n=='repair_tape.txt' else 'old'
    power=False
    for i,s in enumerate(lines(n),1):
        if s.startswith('New shape:'): power=True
        if s.startswith('k/100'): power=False
        if (m:=bandpat.fullmatch(s)): band.append((i,*map(int,m.groups())))
        if (m:=thrpat.fullmatch(s)) and not power: threshold.append((i,*map(int,m.groups())))
    assert band[0][0]==first and band[0][1]==300000 and band[-1][2]==fin
    assert all(a<b for _,a,b,*v in band)
    assert all(l[2]==r[1] for l,r in zip(band,band[1:]))
    assert [v[1] for v in threshold]==list(range(1,31))
    return band,threshold
for n,(out,code,N,ray,unit,first) in tapes.items():
    bs,ts=bands(n)
    for i,a,b,p,s,w in bs:
        row=add(('D02' if n=='repair_tape.txt' else 'M')+('.M' if n=='repair_tape.txt' else '')+'.band.'+n+'.'+str(i),M,(n,i),
         f'Both products <= {p}/{unit}/L³, reciprocal sum <= {s}/{unit}/L³, weighted sum <= {w}/{unit}/L² (absolute errors).',
         f'[{a},{b}'+(']' if b==N or unit==10**6 else ')'),nq,S if n=='repair_tape.txt' else B,kind='D01M',sources='finite',
         read=((code,13,254 if code=='d02finite_repair.cpp' else 233 if code=='finite_opt.cpp' else 219),),dcheck='Fixed-point prime-state enclosure of entire band, normalized at right log end (review §3).',strict='non-strict reported ceilings')
        row['actual_verification_receipts']=[out]
    long_ts=bands('finite20b.txt')[1] if n=='repair_tape.txt' else []
    for i,k,*x in ts:
        for j,(t,comp) in enumerate(zip(x,['P,Q','S','V'])):
            field={'P,Q':'max of the two relative product errors','S':'|delta_S|','V':'|delta_V|'}[comp]
            q=2 if j==2 else 3
            if t==N:
                st=f'{comp}: last failed right endpoint is terminal {N} for guard {k}/100/L^{q}; diagnostic, no suffix certified.'
                d='No nonempty passing suffix is established by this row.'
                status=W
            else:
                t0=max(300000,t); whole=k>=ray
                if n=='finite100m.txt' and k==6 and j<2:
                    assert max(b[3+j] for b in bands('finite20b.txt')[0] if b[2]>N)<60000000
                    whole=True
                if n=='repair_tape.txt' and whole: assert long_ts[k-1][j+2]<N
                st=f'{field} < {k}/100/L^{q}; tape last failed right endpoint {t} (sentinel zero means none).'
                d=f'real x>={t0}'+('' if whole else f' and x<={N} only in this row')
                status=(S if n=='repair_tape.txt' else B) if whole else W
            rid=f'M.threshold.{n}.{k}.{comp}' if n!='repair_tape.txt' else f'D02.M.threshold{k}.{comp}'
            r=add(rid,M,(n,i),st,d,nq,status,kind='D01M',sources='finite',read=((code,186,254 if code=='d02finite_repair.cpp' else 233 if code=='finite_opt.cpp' else 219),),
                  dcheck='Strict guard, not a failure witness for a true inequality. Continue only with the written passing analytic or finite splice.',
                  strict='strict passing suffix if nonempty; no inequality from a terminal failure')
            r['actual_verification_receipts']=[out,'mertens_new.stdout']
for j in range(3):
    for c,x in ast.literal_eval(lines('mertens_results.txt')[6+j].split(' ',1)[1]):
        name=['both relative products','reciprocal sum','weighted sum'][j]
        q=2 if j==2 else 3
        r=add(f'M.Python-row.{j}.{c}',M,('mertens_results.txt',7+j),
            f'Absolute {name} error(s) <= {c}/10^6/L^{q}.',f'x>={x}',nq,B,kind='D01M',sources='finite',
            read=(('mertens_check.py',118,231),('mertens_check.py',233,284),('ray_check.py',145,203)),
            dcheck='Whole finite closed cells or monotonic exactly-constant prime states, then .125/.135 original-input ray from 1e8.',strict='non-strict')
# Other inherited results: exact statement metadata used as locator, with independently checked
# arithmetic status and source mapping. It does not import any old derivation or verdict.
own=json.loads((C/'D01_M_REVIEW_review.json').read_text())['claims']
exist={r['claim_id'] for r in claim}
for p in own:
    id=p['claim_id']
    if id in exist:continue
    w=stale(p['written_source']);f=w['file'];a=w['physical_LF'];z=w['physical_LF_end']
    fam=p['family']; kind='D01R' if fam==R else 'D01M'
    sc='count' if fam==R else 'M'
    st=p['exact_statement'];domain=p['full_domain']
    status=B; why=''; act=True
    code=[]
    for t in p.get('executable_readback',[]):
        j=stale(t);code.append((j['file'],j['physical_LF'],j['physical_LF_end']))
    cs='Review §2: original-input proof/inherited valid comparator, evaluated at both arguments in the correct domains.' if fam==R else 'Review §3: exact normalization, finite/monotone ray and strict/non-strict check on original domain.'
    if id.startswith('Shared.'):
        sc='screen';cs='Review §1: lawful first panel/Dusart, signed FKS truncation or Mellin proof. No old status used as a premise.'
    if id.startswith('R.U-'): sc='Qfree';cs='Review §2 QRH-free branch: original finite theta and CH2, effective zero-free and density only where used, directed replay of entire compact domain and decreasing tail.'
    if id in ('R.sign','R.real-cell','R.literal-source-edge','R.original-rays'):
        sc='rootR';kind='r';cs='Review §2 integer/real endpoint and quotient check, preserving literature trust.'
    if id=='R.literal-source-edge':
        status=F;act=False;why='At N+1/10, both counts are constant and −8100000<R<−7900000. The candidate rejects this literal source edge and retains integers.'
    if id=='R.old-finite-pi':
        status=G;act=False;why='Printed FiniteRH Cor.1 pi has log² not log in absolute error (normalized log³); full RH alternative not available. Superseded by lawful theta transfer and quoted finite pi comparison.'
    if id=='M.withdrawn299999':
        status=F;act=False;why='Positive L² delta_V lies in (.2999993,.2999995) at x=912560. This is an asserted refutation, not a positive bound.'
    if id.startswith('M.secondary') or id.startswith('M.prior-'):
        cs='Review §4 and original-input secondary.md: use correct first-panel cap, periodic strip cancellation or primorial/θ comparison.'
    r=add(id,fam,(f,a,z),st,domain,p['assumptions'],status,kind=kind,sources=sc,read=code,dcheck=cs,why=why,active=act,strict=p['strictness'])
    if id.startswith('M.secondary') or id.startswith('M.prior-') or id in ('M.old-PS','M.old-refined','M.old-analytic','R.U-60','R.U-hi','R.U-mid','R.U-connected'):
        r['actual_verification_receipts']+=['secondary_check.stdout','refine.stdout','ancillary.stdout','ray_check.stdout']
    if id in ('M.sharp-products','M.sharp-reciprocal-sum','M.sharp-weighted','M.withdrawn299999'):r['actual_verification_receipts']+=['ancillary.stdout']
    if id=='R.old-margins':
        r['precise_gap_or_counterexample']='The retained inequalities follow from the stronger repaired B0 proof; the historical finite-pi proof does not license them by itself.'
# Archive explicit D02 source findings without reinstating retired statements.
prior={r['claim_id']:r for r in json.loads((C/'OWN_PRIOR_M_007.json').read_text())['claims']}
ds=json.loads((C/'repair_dispositions.json').read_text())
assert len(ds)==62==len({r['claim_id'] for r in ds})
for d in ds:
    id=d['claim_id']; p=prior[id]
    w=stale(p['written_source'])
    # Preserve exact historical content; the historical review status is not read.
    if 'two-panel' in id:
        result='Literal historical bound is incomplete: the .618 panel lacks an admitted .618 subconvexity proof; the new first-panel minimum is a different function.'
    elif 'Retired tight' in d['disposition']:
        result='No licensed compact-to-tail proof of that older coefficient at the old start; at 167.84 both current upper curves exceed the tighter target. Retain the exact current bounded and later pieces; not a counterexample.'
    elif id.endswith('shift68'):
        result='The current larger shrink has only .746213 closed-cell reserve on the central interval and .797875 at the 167.84 point test for margin 1. Preserve the parts certified at margin 1 and the new connected targets.'
    else:
        result='Assessed historical literal route, not a current claim; reread in light of review §§1–4. The unlicensed older literal consumer cannot prove more than its lawful replacement. For recovered numeric targets use the corresponding current derivation (not the old evidence).'
    history.append(dict(written_source=w, claim_id=id, family=p['family'], exact_statement=p['exact_statement'], full_domain=p['full_domain'], historical_scope=True,
                    candidate_disposition=d['disposition'], current_target=d['now'], independent_source_finding=result))
# Independently read legal historical Dusart-only branch used as comparator, separately scoped.
for id in ('OwnD02.old.A-screen','OwnD02.old.A-gaps','OwnD02.old.M24','OwnD02.old.primorial','OwnD02.old.interval'):
    p=prior[id];w=stale(p['written_source'])
    rr0=add(id,p['family'],(w['file'],w['physical_LF'],w['physical_LF_end']),p['exact_statement'],p['full_domain'],D02,W,kind='limits',sources='screen',
            read=(('ray_check.py',63,143),('extra_check.py',69,102)),
            dcheck='Historical lawful Dusart (2.3) moment-envelope variant with cap 27/32, not the prior C022 two-panel construction. Read as comparator, not a replacement for current exact files.',
            prop='Cap follows from currently mounted D02; not available as a D01-era assumption.',active=False)
    rr0['actual_verification_receipts']=['ray_check.stdout','extra_check.stdout']
assert len({r['claim_id'] for r in claim})==len(claim)
assert {r['claim_id'] for r in own}<={r['claim_id'] for r in claim}
# Programs, status streams, original and executed payload bindings.
eff=[]
def exec_record(name,cmd,scope,out=None,stname=None,deps=()):
    status=stname or name
    return dict(name=name, command=cmd, cwd='/work/exact', environment='LC_ALL=C; assertions enabled',
        covered_domain=scope,dependencies={n:rows[n]['sha256'] for n in deps},
        stdout=out or name+'.stdout',stderr=status+'.stderr',status_file=status+'.status',
        status=int((D/(status+'.status')).read_text()))
eff.append(exec_record('current-replay',['/bin/bash','/work/exact/repair_replay.sh'],
 'Wrapper compiles d02finite_repair.cpp (GCC GNU __int128 extension under -std=c++17); defaults N=250000000, rate 1000000. Runs all five exact current scripts with -B -u, logs redirected per locked wrapper. This is the aggregate status.',deps=('repair_replay.sh','d02finite_repair.cpp','d02ram.py','d02m.py','d02secondary.py','endpoint_check.py','repair_limits.py','d02screen.py','d02rigor.py','mertens_new.py','rigor.py','portfolio_check.py','refine.py','analytic_check.py','mertens_check.py','ray_check.py','finite26.txt','finite20b.txt','d02finite_results.txt','repair_tape.txt')))
GCC=['/usr/bin/g++','-O3','-std=c++17']
eff.append(exec_record('finite-opt-compile',GCC+['finite_opt.cpp','-o','/work/review_finite_opt'],'Compiler invocation',deps=('finite_opt.cpp',)))
for name,params,t in [('finite26',[],'[300000,195729609429], default rate 50000'),('finite20b',['20000000000','200000'],'[300000,20000000000]'),('finite100m',['100000000','1000000'],'[300000,100000000]')]:
    eff.append(exec_record(name,['/work/review_finite_opt']+params,t,deps=('finite_opt.cpp',)))
for n,t in [('007','[300000,26489122130], closed cells, default rate 50000'),('005','[300000,3584912847], rough historic closed cells, default rate 50000')]:
    code=f'D01__SUBMITTED_{n}.cpp'
    eff.append(exec_record('old-'+n+'-compile',GCC+[code,'-o','/work/review-old-'+n],'Compiler invocation',deps=(code,)))
    eff.append(exec_record('old-'+n,['/work/review-old-'+n],t,deps=(code,)))
domain={'portfolio_check':'D01 cells through 191 and all declared monotone tails; cap 7/8','ramDus':'same, without FKS density Table 8','prefix':'D01 QRH-free closed cells through 180','mertens_new':'D01 closed log cells 18.42 through 59.5, analytic joins and shape tails, finite-band reweighting','mertensDus':'same, Dusart-only density','ray_check':'historical A-conditioned and QRH-free cells and tails as in original checker','secondary_check':'archived QRH-free rays, current D01 ancillary/tertiary comparisons and exact sign root','refine':'archived D01 screen coefficients, transition cells, Mertens and correlated interval guards','extra_check':'archived .03/.004 and small signed QRH-free gap, historical .24 D02 extension','audit_summaries':'read exact finite100m,20b,26 bands, onsets and their appropriate joins','mertens_check':'prime sieve to 10^8, 236784 closed cells and historical sharp states, exact constants'}
for n in OLD:
    args=SPEC.get(n,[n+'.py'])
    deps=(args[0],)+tuple(k for k in ('rigor.py','portfolio_check.py','refine.py','analytic_check.py','ray_check.py','mertens_check.py','extra_check.py','endpoint_check.py') if k!=args[0])
    eff.append(exec_record(n,['/usr/bin/python3.10','-B','-u']+args,domain[n],deps=deps))
eff.append(exec_record('ancillary-initial',['/usr/bin/python3.10','-B','/work/submission/ancillary-initial.py','/work/submission/mertens_check.stdout'],'Reviewer guard initially selected incorrect cutoff 30.8 for CH2 lower finite range, failing. Actual branch requires shifted argument <=29.9; 30.8 uses only upper theta sign. No candidate bytes altered.'))
eff.append(exec_record('ancillary',['/usr/bin/python3.10','-B','/work/submission/ancillary.py','/work/submission/mertens_check.stdout'],'Local exact endpoint counterexamples, every candidate/source hash, moment limits, earliest count domains, and same QRH-free K=60 cells. With PYTHONPATH=/work/exact.',deps=('d02screen.py','d02ram.py','endpoint_check.py','mertens_check.py','ray_check.py')))
checks=[]
for a,b in MATCH.items():
    assert (D/a).read_bytes()==(C/b).read_bytes(),(a,b)
    checks.append({'stream':a,'identical_to':loc(b,1),'sha256':dig(D/a)})
assert all(e['status']==0 for e in eff if e['name']!='ancillary-initial')
assert next(e for e in eff if e['name']=='ancillary-initial')['status']==1
evidence=dict(actual_commands=eff, identical_replays=checks, versions={'Python':'3.10.12','GCC':'11.4.0 Ubuntu 11.4.0-1ubuntu1~22.04.3'},
    initial_shell='pwd printed directory; bare ls and cat unavailable, exit 127 and locale warning, remedied via Python pathlib immediately; no mathematical data loss',
    current_wrapper_outputs={
      'd02finite_replay.out':'N=250000000, rate=1000000, full finite guard domains, original wrapper checks exact bytes',
      'd02ram_repair_replay.out':'all early/transition/shift cells, 34 higher-order pairs, analytic tail constants',
      'd02m_repair_replay.out':'closed compact bridges plus tail caps, three finite power joins, normalization and primorial',
      'd02secondary_repair_replay.out':'all listed endpoint power reserve and correlated checks',
      'endpoint_check_repair_replay.out':'exact [N,N+1], both floor counts, derivative and bracket',
      'repair_limits_repair_replay.out':'failed certificate targets, full-height CH2 numeric caps and cutoff exploration'},
    receipts={p.name:{'sha256':dig(p),'bytes':p.stat().st_size} for p in sorted(D.iterdir()) if p.suffix in ('.stdout','.stderr','.out','.status')},
    trust='Ordinary replay plus mathematical proof of the enclosures; not a source-first verification or replay of published prime/zero computations.')
(D/'evidence.json').write_text(json.dumps(evidence,ensure_ascii=False,indent=2)+'\n')
fam={}
for f,summary in [(R,'Both-family conditional gains established; sharp sign benchmark retained. All current strongest branches and distinct weaker-premise options are supported. The historical PT literal real interval is contradicted, not used.'),
                  (M,'Conditional common/signed envelopes and three closed fast-profile joins supported, exact benchmarks unchanged. The optional generic kernel needs integral finiteness; actual kernels and all downstream product/sum conclusions remain supported.')]:
    fam[f]={'strongest_supported_portfolio':[r['claim_id'] for r in claim if r['family']==f and r['active_conclusion'] and r['M_status'] in (B,S)],
        'rejected_or_incomplete_claims':[r['claim_id'] for r in claim if r['family']==f and r['M_status'] in (G,F)],
        'remaining_assessment_work':[],'summary':summary}
j=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=idx['candidate_id'],assessment_complete=True,all_claims_inventoried=True,
       reviewed_source_hashes=idx['candidate_files'],source_bibliography=json.loads(Path('/task/SOURCE_INDEX.json').read_text())['sources'],
       actual_effort_and_verification_commands=eff, evidence_file='evidence.json',family_assessments=fam,claims=claim,
       archived_62_dispositions=history, original_candidate_bytes_changed=False,no_other_arm_or_ranking_seen=True,new_core_math_salvage_performed=False,
       own_history_disclosure='Exact own source and status disclosed; prior verdicts used only to enumerate source, not as mathematical premises. Not blind to own history.',
       input_comparison='Exact dossier B0 implies D01 and is retained cumulatively; A changes cap to 27/32 via Mellin and is directly used only at/above e^200. All named comparisons are matched or clipped to actual domains; within-method B0 ablation is not blind discovery.',
       logic_scope='Reviewed active current and retained D01 evidence, named original statements, and historical qualified/withdrawn D02 targets at their respective scope. No original full computations rerun and no project Lean in runtime.')
# One LF per row in the claims array, bounded size; preserve exact hashes and types.
def compact(o):return json.dumps(o,ensure_ascii=False,separators=(',',':'))
with (D/'review.json').open('w') as out:
    out.write('{\n')
    for k,val in j.items():
        if k!='claims':out.write(compact(k)+':'+compact(val)+',\n')
    out.write('"claims":[\n'+',\n'.join(map(compact,claim))+'\n]}\n')
status={"ready_for_review":True,"families":{R:{"status":S,"claim_files":["review.md","review.json"]},
        M:{"status":S,"claim_files":["review.md","review.json"]}},"serious_attempts_documented":True}
(D/'STAGE_STATUS.json').write_text(json.dumps(status,separators=(',',':'))+'\n')
print('claims',len(claim), Counter(r['M_status'] for r in claim))
print('Review bytes', (D/'review.json').stat().st_size)
