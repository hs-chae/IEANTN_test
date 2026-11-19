"""Generate the claim-level inventory from the locked sources and review decisions."""
from pathlib import Path
from hashlib import sha256
import json, re
P=Path('/task')
index=json.loads((P/'CANDIDATE_INDEX.json').read_text())
source=json.loads((P/'SOURCE_INDEX.json').read_text())
keys={int(r['packet_name'][10:13]):r for r in index['candidate_files']}
def sha(p):return sha256(p.read_bytes()).hexdigest()
for r in keys.values():assert sha(P/r['packet_name'])==r['sha256']
for r in source['sources']:
 for k in ('pdf','text'):assert sha(Path(source['root'])/r[k])==r[k+'_sha256']
def loc(n,l):
 a=keys[n]
 return dict(file=a['packet_name'],original_filename=a['original_name'],physical_LF=l,sha256=a['sha256'])
def excerpt(n,l,end):
 return {**loc(n,l),'through_physical_LF':end,
         'literal_lines':(P/keys[n]['packet_name']).read_text().split('\n')[l-1:end]}
S='supported_at_stated_trust_tier'; I='incomplete_with_specific_missing_step'; B='baseline_retained'; W='equivalent_or_weaker'; F='false_with_specific_counterexample'
qrh='OpenAIQRH PDF p.4 Thm.1.1 LF255–262; PT Finite RH PDF p.2 Thm.1 LF48–50; PT PNT PDF p.4 Lemmas 2,4 LF236–256'
fks='FKS PDF pp.6–8 Thm.2.7, Cor.2.9, Thm.3.2 LF520–527,586–593,631–642; Table 8 first block LF3139–3258'
ch='CH2 PDF p.3 Cor.1.2–1.3 LF193–239 and p.35 Lem.9.2 LF5216–5232'
pz='CH2 Appendix B.1/B.2 LF6133–6182, Eq.(B.9) LF6803–6819, Eq.(A.2) LF5858–5864; Dusart PDF pp.3–4 (2.1) LF171–189'
dus='Dusart PDF pp.11–13 Thm.4.2 LF959–1010, Prop.4.3 LF1049–1056, Cor.4.5 LF1132–1137'
pi='PT PNT PDF p.7 Eq.(11) LF544–558, p.8 LF695–705, pp.9–10 Lem.6 LF802–812; PT Finite RH p.4 Cor.1 LF138–150 and p.5 §3.3 LF171–185'
sg='PT PNT PDF p.3 Thm.2 LF205–212; Dudek–Platt PDF p.2 Thms.1.2–1.3 LF53–55 and p.10 Lem.3.4 LF707–714'
dm='Dusart PDF pp.17–20 Thms.5.6/5.7/5.9 LF1479–1526,1555–1602,1640–1664 and correction LF1722–1725'
ram=[qrh,fks,ch,pz,dus,pi]; mer=[qrh,fks,ch,pz,dus,pi,dm]
families=['Ramanujan','Mertens']
rows=[]
def add(cid,n,line,f,st,dom,method,code=(),reps=(),sources=None,status=S,gap=None,compare=None,strict='as stated',scope='active_or_retained',keep=None,assume=None):
    if sources is None:sources=ram if f==0 else mer
    if assume is None:assume='B0 (only the pinned original analytic and literature-computation inputs in the listed derivation); no full RH and no hypothetical direct ψ bound used'
    rows.append(dict(claim_id=cid,written_source=loc(n,line),family=families[f],
      exact_statement=st,assumptions=assume,full_domain=dom,strictness=strict,
      real_or_integer='integers only' if 'integer only' in dom else ('integer parameter and real auxiliaries' if 'integers n' in dom else 'real arguments (inclusive counts where applicable)'),
      baseline_comparison=compare or 'Available identically under B0 and B0+D01; keep the whole applicable envelope. No B0+D02 input is available.',
      source_locators=sources,derivation_check=method,numerical_obligations=('directed bounds and exact finite checks on stated domains; see the selected implementation and receipts' if code else 'none beyond admitted source or analytical derivation'),
      implementation_readbacks=[excerpt(*a) for a in code],actual_verification_receipts=list(reps),
      retained_valid_branches=keep or 'all other eligible supported branches remain in the pointwise intersection/maximum',
      M_status=status,precise_gap_or_counterexample=gap,scope=scope,
      propagation=dict(input_used=False,where_it_changes_proof='nowhere; B0 implies the exact D01 premise already',matched_comparison='no additional-input difference on the stated domain; 27/32 historical D02 premise unavailable'),
      V_status='paper-only: no project Lean/Blueprint build checked; no kernel or source-first PV asserted',
      remaining_trust='named original-paper conclusions/computations plus ordinary executable exact checks where indicated; no formal semantics/correspondence proof'))
rc=('replay_ram.jsonl: ram_repair',)
rh=('replay_ram.jsonl: ram_high',)
rOld=('replay_ram.jsonl: d01_ram',)
ma=('replay_analytic.jsonl: m_repair, m_postreview, d01_tails and d02_mcheck',)
sig=('replay_sign.jsonl: local-count, root and all eight bridge calls','replay_checks.jsonl')
wc=('replay_analytic.jsonl: d01_cert, d01_smooth, d01_tails and d02_mcheck','replay_checks.jsonl')
for f in (0,1):
 add('redundancy-'+families[f],7,6,f,'B0 implies |ψ(x)−x|≤x^(7/8)(log x)^2/64 on the exact D01 domain; logically identical lawful consequences', 'all real x≥exp(200), then every matched theorem domain', 'FKS T=64exp(L/8), PT reciprocal-sum difference and QRH; also independent stronger density route.',[(29,17,35),(11,95,114)],wc,[qrh,fks],W,compare='Identical premise strength after substitution, not discovery-run ablation.')
add('D01-strip-reverse',10,33,0,'D01 implies no ζ zero in Re s>7/8 (not at equality)', 'open complex half-plane Re s>7/8', 'Euler product logarithmic derivative and holomorphic continuation of the pole-subtracted integral.',sources=[qrh],compare='Same ζ strip as B0; not a Hecke theorem.',assume='D01 alone for the reverse implication (with foundational zeta analysis)')
add('density-original',10,45,0,'F and Cθ from the log-tangent staircase; ψ and θ relative caps F e^(−L/8), Cθ e^(−L/8)', 'L≥40 for F; closed coefficient onsets below', 'Tonelli for 2/t², signed ordinate pairing, staircase telescoping, admissible truncation and monotone coefficients.',[(11,31,97),(23,1,220)],wc)
for n,l,fn,k,A in [(10,18,'ψ','.019535',190),(10,18,'θ','.01955',190),(10,18,'F','.013604',400)]:
 add('density-'+fn+'-'+str(A),n,l,0,fn+' coefficient strictly < '+k+' in units x^(7/8) for absolute prime-count deviations (F dimensionless)',f'L≥{A}','Endpoint arithmetic and monotonicity.',[(11,95,114),(18,76,81)],wc,strict='strict')
add('density-quartic',36,7,0,'Fourth-degree density integral majorant, terminal w<.010454, F* and C* decrease from 40 and give relative ψ and θ radii', 's in [.70,.875], H cutoff; L≥40, used from 185 in the Ramanujan final branch','Negative fifth derivative for q∈(3,4), directed integration and grid running minima; inclusive upper strip.',[(47,105,136)],wc)
add('smoothing-B0',34,19,0,'|ψ(x)/x−1|≤119e^(−L/2)+3.6e−6e^(−L/16)+2e^(−L)', 'L≥18','Use B.1/B.2, finite RH, compact L² explicit formula and one-sided average bounds. Details in review.md.',[(29,6,16),(29,19,26)],wc)
add('truncation-B0',34,31,0,'118e^(−L/2)+[.15916((L/8+3.22)²−26.89²)+3.7284+2.091L/64]e^(−L/8) bounds relative ψ error', 'L≥200','Apply truncation with T=64exp(L/8); when T*<H high debit is omitted and bracket positive.',[(29,17,35)],wc)
add('primitive-S1',20,9,1,'U(t)=−Σρ exp((ρ−1)t)/(ρ(1−ρ))−log(2π)exp(−t)+Σ_{m≥1}exp(−(2m+1)t)/(2m(2m+1))', 't≥0','Laplace transform computation, reciprocal-square absolute convergence and polynomial uniqueness; no half-weight issue for U.',[(21,69,79)],wc,[qrh,pz])
add('primitive-G',20,35,1,'High contribution ≤G(t)exp(−t/8)/H, with G(190)/H<4.49e−15 and G(400)/H<3.20e−15', 't≥0; endpoint coefficients decrease afterwards','Quartic density integral against 4H/t³ and low-β high-ordinate bound 160/H.',[(21,26,52),(21,70,79)],wc)
add('primitive-B0',34,49,1,'Integrated ψ caps at δ=1/8: .085,3.3e−12,2 for w1; .083,3.2e−12,2 for w2', 'L≥18','Absolute summation of integrated modes, then one integration by parts against derivative of w; exponential factors e^(−L/2),e^(−L/8),e^(−L).',[(29,51,61)],wc)
add('primitive-new',43,41,1,'Improved integrated |I1|≤w(L)(.048s+3.3e−12r+2X) and weight-one with .0463,3.2e−12,2; high coefficient 4.5e−15 after 190 in common E', 'L≥18; reduced high term L≥190','Low S1 sum .0463 with derivative ratio, upper direct trivial integral and G switch.',[(41,29,31),(40,31,45)],ma+wc)
add('R-local',14,2,0,'π(N)=π(N+1)=1644673232, π(x/e)=632207037 locally; α∈(38358837682.2179263651446,38358837682.2179263651448) and R>67000000(x−α) after α locally', '[N,N+1] for counts and root; α<x≤N+1 for slope bound','Exact odd sieve, exact e/log/Fractions, derivative; K even.',[(13,10,42),(15,3,14)],sig,[sg],strict='strict rational root and slope bounds; equality at α')
add('R-final-real',7,10,0,'R(x)>0 on the optimal open ray x>α and R(α)=0', 'x>α; equality at α','Local root, exact bridge, DP original interval, and earlier logarithmic margin.',[(15,3,13),(25,45,85),(47,208,219)],sig+rc,[sg]+ram,strict='strict except equality at α',compare='Improves the verified sign coverage of PT between e^58 and e^3915; not an earlier endpoint than the false printed real clause.')
add('R-final-integer',7,12,0,'Optimal integer onset for R>0 is 38358837683', 'integers n≥38358837683 (integer only)','Flooring real result and direct negative R(N).',[(15,3,13),(25,45,85)],sig,[sg],strict='strict')
add('R-bridge',48,41,0,'Independent finite exact bridge R>0 on [38358837683,100000000000]', 'closed real interval as displayed','Ordered Lehmer count, segmented sieve, directed e and concave ex/log x interpolation; flooring within adjacent integers.',[(25,7,85),(28,9,55)],sig,[sg],strict='strict')
add('R-DP-window',48,41,0,'R>0 on [10^11,1.15·10^16] at original computation trust', 'closed real interval as displayed','DP Lem.3.4, original finite computation; not full RH.',sources=[sg],status=B,strict='strict')
add('R-PT-literal',14,4,0,'The quoted PT original literal R>0 for N<x≤e^58 is false; candidate expressly rejects it.', '(N,exp(58)]','Local exact counts and rational R enclosure.',[(13,10,42),(15,3,14)],sig,[sg],F,'x=38358837682+1/5, R in (−1220000,−1200000).','Applies only to the quoted source assertion, not the current candidate sign ray.','strict asserted by source','quoted_and_rejected')
add('R-PT-floored',8,13,0,'The integer portion gives R>0 for [N+1,exp(58)] by flooring', 'closed real interval [N+1,exp(58)]','Retain integer portion at literature trust; independent same-domain consequence of current ray. The false real sliver is not used.',sources=[sg],status=B,strict='strict')
add('R-PT-tail',8,13,0,'PT R>0 for x≥exp(3915)', 'closed real ray x≥exp(3915)','Quoted as separate disjunct and now dominated by current quantitative margins.',sources=[sg],status=B,strict='strict')
add('R-DP-tail',8,13,0,'DP 1.2 original positive ray x≥exp(9658)', 'closed real ray x≥exp(9658)','Published theorem at admitted trust (not use of faulty negative-m derivation as numerical premise in new proof).',sources=[sg],status=B,strict='strict')
add('R-DP-RH-comparator',8,13,0,'DP 1.3 conditional full-RH largest integer failure N', 'integers n≥N (integer only)','Source is exactly conditional; retained only as a comparator, not a premise of candidate.',sources=[sg],status=B,strict='strict for n>N',scope='quoted_conditional_comparator',assume='full RH in original DP Thm.1.3 only')
add('R-li20',48,19,0,'H20≤u li(e^u)e^−u≤H20+V, using split at 40', 'u≥24, alternate V available when u≥40','PV transform gives constant in (0,1); series plus continuous derivative comparison.',[(47,59,78),(47,259,260)],rc)
add('R-pi-finite-offset',48,26,0,'−short(u)≤Δ≤0 from PT finite quote with PV allowance 2', '26≤u≤43.7 (normalization allowance can also be used at u=18)','Use precise x≤10^19 source and Eq.(11); 0<li(2)<2 and original finite sign.',[(47,83,90),(47,242,248)],rc,[pi])
add('R-pi-finite-cube',37,3,0,'|Δ(u)|≤cu³exp(−u/2), c=.0397888', '26≤u≤58','Multiply named printed finite bound by u/x; not log² in normalized units.',[(47,56,58),(47,157,167)],rc,[pi])
add('R-pi-finite-log2-withdrawn',3,26,0,'Historical direct |Δ|≤cu²exp(−u/2) unsupported by cited finite-RH Cor.1; expressly retired.', '26≤u≤58','Not imported into current minimum.',[(2,139,148),(24,62,67),(29,100,110)],('replay_analytic.jsonl: historical d02_mcheck/d02_analytic are arithmetic only',),[pi],I,'Missing a source or derivation giving a single log for absolute π error at the indicated constant and range. Not a counterexample to that bound.',scope='withdrawn_historical')
for cid,n,l,statement,domain,method,block in [
 ('R-pi-early',48,27,'signed lower Δ via negative θ and upper Δ≤−.17exp(−u/2)','26≤u≤29.9 for lower, 27≤u≤29.9 for upper','s=18 signed anchor and exponential derivative ratios',(47,89,90)),
 ('R-pi-early-strong',37,33,'strengthened signed upper Δ with negative .4178 convolution','27≤u≤29.9','Directed b endpoint for magnitude of the negative term; anchor at a.',(47,175,184)),
 ('R-pi-CH2',48,28,'symmetric |Δ|≤h0+m0 with q=1.047198e−12','u≥40','CH2 and θ convolution; at 40 use finite π short estimate + finite θ, not the two log² finite-RH absolute formulas alone.',(47,65,66)),
 ('R-pi-ES',48,28,'symmetric |Δ|≤ES with δ=1/8','u≥40','Smoothed ψ point bound + Dusart then anchor at 40.',(47,137,140)),
 ('R-pi-finite-anchor',48,28,'use finite θ branch with remainder c(u²+2u)exp(−u/2)+3.2u exp(20−u)','40≤u≤58','Integrate only on the finite θ interval, with repaired anchor justification.',(47,141,143)),
 ('R-pi-mstar',48,34,'|Δ−dθ|≤7e^(−u/2)/u+(8e−12)e^(−u/8)/u+3.21u e^(20−u)','u≥40','Abel integration of U, separate powers and two endpoint θ caps.',(47,91,94)),
 ('R-pi-signed-reanchor',37,21,'D from .155,7.2e−12,.074 with signed subtraction of prime power integral for m=Δ−dθ','u≥s=29.9, applied from u=40','Integrated primitive and signs, coefficient checks; local θ has its own eligibility.',(47,145,156)),
 ('R-new-bracket',48,40,'two-sided interval for R L²/x² from F_± at L and L−1','L≥27','Positive lower F arguments allow ordered squaring; actual π cube and θ square only in their separate leaves.',(47,145,184)),
 ('R-old-alt-bracket-corrected',37,39,'historical H20 offset bracket with cube, ES at 1/8, upper sign to 43, no h1+m1','L≥36.98','Pointwise argument from valid corrected leaves; no numerical preservation of invalid historical leaves asserted.',(47,137,167)),
 ('R1',10,71,'x²(D0−ε0)≤R≤x²(D0+ε0), D0=S(L−1)/L−S(L)²; B=min of eligible B_G,B_I,B_H,B_P','L≥30.5, shifted leaf eligibility checked','Separate order-12 analytic enclosure with θ transfer not direct π finite-RH.',(18,25,58)),
 ]:
 add(cid,n,l,0,statement,domain,method,[block],(rOld if cid=='R1' else rc)+('replay_checks.jsonl',))
add('R-old-alt-uncorrected',33,13,0,'Superseded whole comparison using direct finite π square and optionally h1+m1', 'L≥36.98','Normalization readback and historical conditional input scope.',[(24,57,67),(29,100,110)],(),[pi,qrh],I,'Replace direct π leaf with cube; 27/32 premise not available. Corrected alternative is separately supported.',scope='withdrawn_historical')
def prof(cid,n,l,A,j,z,code,rep=rc,end=None,label=None):
 dom=f'L≥{A}' if end is None else f'{A}≤L≤{end}'
 expr=label or f'Y > Σ_{{k=4}}^{{{j-1}}} C_k/L^(k−4) + ({z})/L^({j-4}), Y=R L⁶/x²'
 meth='Directed whole-cell debit with eligible shifted and unshifted branches; connected tail where stated.' if rep==rc else ('Order-40 anchor and full L^40 debit monotonicity.' if rep==rh else 'Independent S12 plus exact uniform losses and all-ray monotonicity.')
 add(cid,n,l,0,expr,dom,meth,[code],rep,strict='strict')
for i,(a,z) in enumerate(zip(['30.5','31','32','33.2'],['.04','.30','.70','1'])):
 prof('R-old-constant-'+str(i),10,8+i,a,4,z,(18,82,104),rOld)
prof('R-old-plus2',10,12,48,6,2,(18,82,104),rOld)
for i,(a0,a,z,h) in enumerate(zip(['27.8','28.3','29.2','30.75'],['27.75','28.24','29.19','30.59'],['.04','.30','.70','1'],['.06','.33','.715','1.03'])):
 prof('R-preexisting-repaired-constant-'+str(i),48,8,a0,4,z,(47,196,199))
 prof('R-earlier-constant-'+str(i),37,48,a,4,z,(47,208,212))
 prof('R-stronger-constant-'+str(i),37,48,a0,4,h,(47,208,212))
for cid,n,l,a,b,j,z in [
 ('R-slab-140',48,8,34.3,43.7,4,'1.40'),('R-slab-1405',37,48,34.3,43.7,4,'1.405'),
 ('R-connected-plus8',48,11,47.7,None,6,8),('R-finite-profile-0',48,11,47.7,191,6,8),('R-finite-profile-1',48,11,47.8,187,6,10),
 ('R-finite-profile-2',48,11,48,184,6,25),('R-finite-profile-3',48,11,50,158,6,100),
 ('R-finite-profile-4',48,11,53,122,7,0),('R-finite-profile-5',48,11,56,106,7,1000),
 ('R-plus8-earlier',37,49,47.64,None,6,8),('R-plus830',37,49,47.645,None,6,'8.30'),
 ('R-plus834',37,49,47.647,None,6,'8.34'),('R-plus10-early-slab',37,49,47.68,187,6,10),
 ('R-plus25-earlier-slab',37,49,47.97,184,6,25),('R-plus1050-slab',37,49,56,105,7,1050),
 ('R-plus10-late',37,49,189.36,None,6,10),('R-plus14-late',37,49,189.9,None,6,14),
 ('R-plus16-tail',37,49,191,None,6,16),('R-rung-plus10',48,11,191,None,6,10)]:
 prof(cid,n,l,a,j,z,(47,196,219),end=b)
for j,a in enumerate([222,255,289,324,359,395,430,466,503,539,575,611,648,687],7):
 prof(f'R-rung-{j}',48,12,a,j,0,(47,203,207))
for j,a in enumerate([223,257,292,327,363,408],7):
 prof(f'R-old-rung-{j}',10,82,a,j,0,(18,98,104),rOld)
for j,a in zip([7,8,9,10,12,15,16,19],[221,254,288,323,394,502,538,647]):
 prof(f'R-improved-rung-{j}',37,50,a,j,0,(47,217,219))
prof('R-rung-C20-half',48,12,1000,20,'1472754152349904001/2',(47,203,207))
for j,a in enumerate([720,757,793,830,866,903,939,976,1013,1049,1086,1122,1159,1196,1232,1269,1306,1342,1379,1419],21):
 prof(f'R-high-rung-{j}',45,7,a,j,0,(46,29,50),rh)
prof('R-high-C40-half',45,11,1431,40,'542983223118033629157634236574003452512389751201/2',(46,29,50),rh)
for cid,n,l,z,a in [('R-old-tiny',33,49,'.00002',36.98),('R-old-plus12',33,90,'1+12/L',48),('R-old-plus13-target',33,49,'1+13/L',48)]:
 add(cid,n,l,0,'Y>'+z,f'L≥{a}','Follows by domination by active constant or quadratic lower bound; not using misnormalized historical proof.',[(47,196,219)],rc,status=W,strict='strict')
add('R-envelope',7,14,0,'pointwise maximum of all eligible lower bounds, minimum of all eligible upper bounds', 'each eligible domain; two-sided bracket on L≥27 and R1 on L≥30.5','Nonempty interval for each eligible bound and all checked domains; not a uniform improvement over every comparator.',reps=rc+rOld)

add('M-identities',7,18,1,'Inclusive P,Q,D1,D2 with named centers; D_j=dθ/L^(2−j)−∫dθ w_j; Z_Q=D1−T', 'x≥2','Partial summation and absolute tail convergence; sign checked for B3, T, and both product ratios.',sources=[dm])
add('M-log-conversion',43,57,1,'Z_Q interval maps to the two stated relative error maxima; symmetric a<1 gives both ≤a/(1−a)', 'x≥2 whenever the log interval or radius is available','Monotone exponentiation for log Q and log P=−log Q; no use of one product error unchanged as the inverse error.',sources=[dm],code=[(38,94,101),(31,55,64)],reps=ma)
for cid,l,k,a,what in [('M-Dusart-D1',1485,'.2/L³',2278383,'|D1|'),('M-Dusart-D2',1564,'.3/L²',912560,'|D2|'),('M-Dusart-products',1640,'.2/L³',2278382,'both relative products')]:
 add(cid,8,14,1,f'{what} ≤ {k} at the original printed threshold',f'x≥{a}','Original normalized theorem at inclusive real argument.',sources=[dm],status=B)
add('M-Dusart-analytic-branches',8,14,1,'retain A1 and A2 from each eligible k>1 in Dusart Thm.4.2, and signed log-product correction', 'each exact Dusart row x≥x_k (other product tail restrictions as stated)','Integrate (v+1)v^(−k−2) and v^(−k), plus endpoint, and exponentiate only after log correction.',sources=[dm,dus],status=B)
add('M-original-source-min',8,15,1,'domain-aware ψ/θ caps from PT, FKS, finite RH, CH2 and Dusart can tighten the signed and absolute envelope', 'each original domain; signed transfers L≥8 or L≥18 as stated','Pointwise radii and source hypotheses verified; no constant ψ plateau directly integrated to infinity.',sources=mer+['PT Thm.1 Table 1 LF77–95; FKS Thms.1.1–1.2, Cor.1.4 LF113–143, Tables 5–6'],status=B)
for i,(a,b,k,kw) in enumerate([(2,1000,2.4,2.4),(1000,72004899338,2,2.1),(1000,1318815735,2,2)]):
 add('M-old-sqrt-'+str(i),16,3 if i==0 else 4,1,f'products and D1 ≤{k}/(sqrt(x)L), D2 ≤{kw}/sqrt(x)',f'closed [{a},{b}]','Whole-cell directed prefix/log/sqrt comparisons; x=1000 composite.',[(21,125,166)] if not i else [(19,139,203)],wc if not i else ('replay_smallfinite.jsonl',))
for i,(a,b,k,kw) in enumerate([(240000,3500000,'.500','.500'),(3500000,13000000,'.199','.230'),(13000000,50000000,'.130','.170'),(50000000,1318815735,'.100','.150')]):
 add('M-old-log-finite-'+str(i),16,12+i,1,f'products and D1 ≤{k}/L³, D2 ≤{kw}/L²',f'closed [{a},{b}]','D01 fixed-point sieve and endpoint bounds, including all jumps.',[(19,156,210)],('replay_smallfinite.jsonl',))
for cid,n,l,st,dom,method,code in [
 ('M-old-PT-slab',16,5,'M1=6.6s/L+4X+7e−9, M2=6.6s+4LX+3e−7, product error ≤e^(M1+X)−1','21≤L≤40','Partial sum to e^40, use right cap and finite π normalization.',(22,41,60)),
 ('M-old-CH2-slab',16,6,'M1=(2D+114.674(1+2/L)s)/L, M2=D+114.674s and product bound by e^(M1+X)−1','40≤L≤190','Weighted CH2 statement and positive missing prime powers, then reverse Stieltjes transfer.',(22,40,54)),
 ('M-old-K',16,26,'for positive differentiable nonincreasing w, |∫_L^∞dθ w|≤w(L)e^(−L/8)K(L), K(190)<8e−9, K(400)<9.1e−15','L≥190','Fixed-cutoff FKS interval, integrated oscillatory modes and exact bands.',(22,8,38)),
 ('M-old-power-function',16,28,'in power units Cθ+(1+1/L)K for D1, Cθ+K for D2, add X to log radius and exponentiate','L≥190','Pointwise endpoint and old K, monotone positive coefficients.',(22,25,38)),
 ('M-S2-signed',20,66,'signed S2 intervals from observed endpoint dθ plus w[J−−S,J++S], minus allowed T for log Q','L≥8','Primitive, convex tangent on weight, actual inclusive endpoint. See review.md.',(21,47,68)),
 ('M-S2-110',20,70,'|D1| ≤1.01D/L using signed absolute comparison','110≤L≤190','Monotone scaled addition to the CH2 plateau, tested at 110.',(21,80,84)),
 ('M-D02-signed',30,30,'B_j−W_j≤D_j≤B_j+U_j and B1−W1−1/(2 floor x)≤Z_Q≤B1+U1 with δ=1/8','L≥18','Use e^(−v/2) signed bias, sum actual ξ bounds, use F_j in corresponding direction.',(29,51,91)),
 ('M-signed-sharpened',43,41,'same D_j and Z_Q signed bias bounds with .048 and stronger S1/G F_j','L≥18','Substitute independently improved absolute signed integration radii; do not take 27/32.',(41,4,15)),
 ('M-sign-Q/P',30,160,'Z_Q>.003s/L, normalized Q>1 and normalized P<1','20≤L≤29.9','Jensen B1≥s/(L+2), split monotone bounds.',(29,80,91)),
 ('M-sign-D2',30,162,'D2>.10s','20≤L≤29.9','Weighted signed cost and positive B2; split monotone bounds.',(29,80,91)),
 ('M-new-T-tail',43,54,'|Σ_{p>x}p^−2−I|≤δ(2xg(x)+I)≤3δ/(xL); .470/(xL)<T<.502/(xL) plus pointwise refinement','L≥18','Stieltjes identity, prime-power upper series and δ=.001 endpoint checks.',(41,61,66)),
 ('M-signed-early-log',43,45,'|D1|,|Z_Q|≤u(L) with BI=1−2/29.9+8/29.9²','18≤L≤29.9','Two integrations by parts and signed subtractive prime-power cost.',(41,4,15)),
 ('M-signed-early-weighted',42,31,'|D2|≤1.837401s+2.67t+3.2e−12r+2X','18≤L≤29.9','Positive leading bias with upper error; reverse sign no larger.',(40,66,69)),
 ('M-signed-PI-slab',42,27,'0≤LD1−Δ,D2−Δ,LZ_Q−Δ≤2.25s and max(|LD1|,|D2|,|LZ_Q|)≤2.25s','29.9≤L≤43.7','Opposite signs, anchor 18 and lower P integral with convexity.',(40,11,29)),
 ('M-common-E',42,39,'max(L|D1|,L|Z_Q|,|D2|)≤E(L) with signed bias and ψ cap','L≥18','Residual signed bounds after removing pure square-root bias and switch at 190.',(40,31,36)),
 ('M-refined-power-function-old',43,74,'U=C*+(1+1/L)[2.0860003e^(−3L/8)+2.67e^(−13L/24)+3.3e−12+2e^(−7L/8)]+Le^(−7L/8); convert U for products','L≥185 where C* applied; displayed old constants start at 190 or later','Monotone cofactor, affordable high and trivial parts.',(41,68,76)),
 ('M-refined-power-function-new',42,46,'U*=F*+(1.0003+.048k)e^(−3L/8)+k[2.67e^(−13L/24)+Z+2e^(−7L/8)]+.502e^(−7L/8), Z drops at 190; relative products use U*/(1−U*e^(−L/8)/L)','L≥185','Monotonicity and strict termwise comparison with old U. Both are available.',(40,31,45)),
 ]:
 add(cid,n,l,1,st,dom,method,[code],ma+wc)
for a,k in [(21,'.083'),(25,'.0161'),(40,'.00051')]:
 add(f'M-old-scaled-ray-{a}',16,8,1,f'all-four strict coefficient {k}, products/D1 in L^−3 and D2 in L^−2',f'L≥{a}','PT slab and weighted CH2 pieces joined to power branch; unscaled log radius controls exponentiation.',[(22,47,61)],wc,strict='strict')
steps=[('2278381.730','.20000'),('2278381.940','.19998'),(3500000,'.180'),(5000000,'.160'),(18100000,'.100'),(111000000,'.060'),(181000000,'.050'),(1125000000,'.030'),(3909288921,'.011'),(4760000000,'.010'),(8500000000,'.009'),(12000000000,'.008'),(16000000000,'.007'),(22000000000,'.006'),(30000000000,'.005'),('exp(27)','.00205'),('exp(32)','.001')]
for i,(a,k) in enumerate(steps):
 if i<4:b=[(31,44,86)]; rep=('replay_early.jsonl: exact',)
 elif i<8:b=[(32,51,115),(29,63,79)]; rep=('replay_early.jsonl: early',)+ma
 elif i<15:b=[(38,51,115),(41,17,49)]; rep=('replay_coarse1.jsonl',)+ma
 else:b=[(41,17,49)]; rep=ma
 add(f'M-step-{11+i}',43,11+i,1,f'both relative products and |D1| ≤{k}/L³ for their eligible domains',f'x≥{a}; additionally x≥2278383 for D1','Exact sufficient certificate where finite; overlap with next finite test or certified analytic branch at a lower point than the finite top.',b,rep)
for i,(a,k,t,c) in enumerate([(3909275995,'.011',9000000000,'22.9'),(38622120594,'.004',90000000000,'25.2'),(103268901665,'.003',170000000000,'25.83'),(149179986112,'.0024',290000000000,'26.35')]):
 add(f'M-new-finite-{i}',42,11+i,1,f'both relative products and |D1| ≤{k}/L³',f'x≥{a}','Terminal prefix-bracket suffix through '+str(t)+'; independently certified analytic log onset '+c+' is before finite top.',[(38,51,115),(40,47,53),(40,70,91)],('replay_coarse1.jsonl' if i==0 else 'replay_coarse2.jsonl',)+ma,compare='Smaller bound or earlier onset at fixed strength on the matched B0 domain; no premise gain.')
add('M-old-011-link',30,74,1,'old .011/L³ at and beyond 4760000000 for both products and D1','x≥4760000000','Loose M finite replay [4200000000,10^10], then analytic from L=23. Also dominated by .010 from the stated real onset.',[(32,51,115),(29,67,79)],('replay_early.jsonl','replay_analytic.jsonl'),status=W)
for i,(a,k) in enumerate([('2278381.750','.2'),('2278381.950','.19998')]):
 add('M-old-early-'+str(i),30,66+i,1,f'both relative products ≤{k}/L³ (no earlier D1 scope)',f'x≥{a}; D1 only from 2278383','Current earlier exact steps imply the historical assertions.',[(31,44,86)],('replay_early.jsonl',),status=W)
for a,k,n,l in [('912559.998','.3',39,6),('912560','.2999999',39,26),('912561','.29998',31,6)]:
 add('M-weight-onset-'+a,43,29,1,f'|D2|≤{k}/L²; direct closed finite interval then by D1 transfer',f'{a}≤x≤2278383; same coefficient continues on x≥2278383','Exponent divisor correct; at the common endpoint and later ≤1.5·.19998=.29997.',[(n,l,42),(31,48,75)],('replay_early.jsonl','replay_checks.jsonl'))
add('M-D2-transfer',43,30,1,'|D2|≤L B(x)+∫_L^∞B(exp v)dv for any eligible D1 absolute envelope', 'x≥2278383 for transferred step bounds','Stieltjes identity with vanishing term at infinity confirmed by printed Dusart baselines. Applies for other true B on their own rays.',sources=[dm])
add('M-old-weighted-0165',27,16,1,'D2 radius .0165/L² from 4760000000','x≥4760000000','1.5 of inherited .011 D1 ray; now stronger branches active.',[(29,67,79)],ma,status=W)
for i,(a,k) in enumerate(zip([3909288921,4760000000,8500000000,12000000000,16000000000,22000000000,30000000000],['.014','.0124','.0111','.0099','.0087','.0075','.0064'])):
 add('M-cone-'+str(i),43,31,1,f'|D2|≤{k}/L²',f'x≥{a}','Single split at L=27 and monotonic log-angle comparison; use upper coefficient after switch.',[(41,50,60)],ma)
for a,k in [(50,'4.4e−6'),(60,'8.2e−8'),(65,'4.3e−8')]:
 add(f'M-old-scaled-{a}',43,49,1,f'all four coefficient {k} for respective log-power errors',f'L≥{a}','Use CH2 θ plateau + integrated majorant through 190 and power tail thereafter.',[(41,79,87)],ma)
for i,(a,k,d) in enumerate([('27','.00205','.002'),('28.39','.001','.00111'),('28.5','.001','.001'),('29.35','.00066','.000734'),('29.45','.00066','.00066'),('30.68','.00050','.00050'),('32.3','.00025','.00025'),('34.4','.00010','.00010'),('36','.00005','.00005'),('46.1','.00002','.00002'),('49.56','.000005','.000005'),('49.97','4.4e-6','4.4e-6'),('59.95','8.2e-8','8.2e-8'),('64.4','4.3e-8','4.3e-8'),('74','3.8e-8','3.8e-8')]):
 for what,c in [('products-D1',k),('D2',d)]:
  add(f'M-new-log-{a}-{what}',42,71+i,1,f'{what} coefficient ≤{c} in log-power units',f'L≥{a}',
      'Early D1/u slab or inherited .00205; weighted early use direct d2=True or integrated D1 table. Later joins at 29.9,43.7,58,190 and power monotonicity.',
      [(40,54,59),(40,66,91),(40,104,115),(40,125,138)],ma)
add('M-weighted-step-formula',42,91,1,'L²|D2|≤1.5K_i−.5L²Σ_{h>i}(K_{h−1}−K_h)/L_h², supremum of left-endpoint caps for a ray', 'L≥first eligible D1 step and as stated on each step','Integrate exact v^−3; uses no value below D1 domain.',[(40,93,102)],ma)
for i,(a,k) in enumerate(zip([3909275995,4760000000,8500000000,12000000000,16000000000,22000000000,30000000000,38622120594,103268901665,149179986112,'27','28.39','29.35','30.68','32.3','34.4','36','46.1','49.56','49.97','59.95','64.4','74'],
    ['.01212','.01104','.00983','.00872','.00763','.00656','.00549','.00445','.00332','.00269','.00224','.00111','.000734','.000550','.000278','.000115','.000061','.000022','.00000572','5.09e-6','1.05e-7','6.27e-8','5.71e-8'])):
 add('M-weighted-step-'+str(a),42,96 if i<10 else 97,1,f'|D2|≤{k}/L²',('L≥' if isinstance(a,str) else 'x≥')+str(a),'Full integrated decreasing step envelope, maximum over all later left endpoint bounds.',[(40,93,102),(40,125,138)],ma)
for i,(a,k) in enumerate([(190,'.01955'),(400,'.01361'),(600,'.01231'),(900,'.01164'),(1300,'.01127'),(2000,'.01099'),(3500,'.01078'),(9000,'.01059'),(12000,'.01055'),(18000,'.01052')]):
 add('M-old-power-'+str(a),43,62+i,1,f'all four errors ≤{k} in power units e^(−L/8)/L or e^(−L/8) for D2',f'L≥{a}','Certified old K or refined C* with symmetric integration and exponentiation; entire tail monotone.',[(22,25,38),(41,68,76)],ma+wc)
for i,(a,k) in enumerate([(185,'.01973'),(187,'.01955'),(190,'.01929'),(250,'.01612'),(400,'.01345'),(600,'.01230'),(900,'.01163'),(1300,'.01125'),(2000,'.01097'),(3500,'.01076'),(9000,'.01058'),(12000,'.01055'),(18000,'.01051'),(100000,'.01047'),(100000,'.010456'),(200000,'.010451'),(500000,'.010447'),(1000000,'.010446'),(5000000,'.0104448')]):
 add(f'M-new-power-{a}-{k}',42,53+i//2 if i<14 else 61,1,f'all four errors ≤{k} in power units e^(−L/8)/L or e^(−L/8) for D2',f'L≥{a}',
  'Directed F* staircase and improved integrated coefficient, including extended grid for final five; unrounded coefficient and log conversion monotone.',
  [(40,38,45),(40,60,65),(40,116,124),(47,105,136)],ma,compare='Earlier onset and/or smaller coefficient in matched B0 power units; keeps both old coefficients and eligible sharper pointwise branches.')
add('M-envelope',42,99,1,'minimum of all eligible absolute caps and intersections of signed caps before exponentiation when helpful', 'x≥2, using each exact endpoint','Complete real-domain floor with multiple valid minima; no claim of optimality or same dominating branch everywhere.',reps=ma+wc)
for cid,n,l,f,st,dom,proof,code in [
 ('A-short',9,5,0,'π(x+.04x^(7/8))−π(x)>.0008x^(7/8)/log(x+.04x^(7/8))','x≥e^190','Both θ endpoints and concavity.',(22,67,69)),
 ('A-eighth',9,6,0,'a prime strictly between n⁸ and (n+1)⁸','integers n>0 with n⁸≥e^190 (integer only)','Use short interval with x=n⁸ and h<8n⁷.',(22,67,69)),
 ('A-primorial-old',9,10,1,'|V_y−1|<9.2e−15 y^(−1/8)/L','L≥400','Recenter at θ and use K with quadratic remainder.',(22,25,38)),
 ('A-primorial-positive',20,76,1,'V_y−1>.10/(sqrt(y)log y), plus Q(y)>e^γ log θ(y) also on y≥2','3≤y≤e^84.5; second inequality 2≤y≤e^84.5','Local cancellation is nonnegative, finite exact prefix check and signed-cell integration.',(21,91,123)),
 ('A-primorial-S3-190',20,81,1,'−4.6e−15 y^(−1/8)/L<V_y−1<1.5e−14 y^(−1/8)/L','L≥190','Signed spectral tails with quadratic remainder and log conversion.',(21,57,90)),
 ('A-primorial-S3-215',20,82,1,'|V_y−1|<4.6e−15 y^(−1/8)/L','L≥215','Same exact monotone tail scaling.',(21,57,90)),
 ('A-primorial-S3-400',20,83,1,'|V_y−1|<3.22e−15 y^(−1/8)/L','L≥400','Same exact monotone tail scaling.',(21,57,90)),
 ('A-general-old',9,14,1,'old general upper factor with 9.2e−15 and denominator log log n−log2 for n/φ(n),σ(n)/n','integers n≥n_(e^401) (integer only)','Largest primorial ordering, consecutive-prime gap and log n<2y.',(22,67,69)),
 ('A-general-216',20,94,1,'general upper bound for n/φ(n),σ(n)/n using coefficient 4.6e−15 and factor 1+10^−12 in log n scale','integers n≥n_(e^216) (integer only)','p_next gap plus θ upper; log n≤(1+10^−12)y and largest primorial; use S3.',(21,85,90)),
 ('A-general-401',20,97,1,'same upper bound with coefficient 3.22e−15','integers n≥n_(e^401) (integer only)','Same comparison using stronger S3.',(21,85,90))]:
 add(cid,n,l,f,st,dom,proof,[code],wc,strict='strict where indicated')
for n,l,f,st in [(27,9,0,'historical A-D02 27/32 conditional +13.9/L from L=48'),(33,9,0,'historical h1+m1 using direct 27/32 input'),(34,31,0,'historical δ=5/32 ψ bounds/smoothing and strip'),(30,25,1,'historical signed Mertens with δ=5/32')]:
 add('history-27over32-'+str(n),n,l,f,st,'original historical domain, not a current assertion','Premise availability audit only; no import of conditional numeric conclusion to current contract.',sources=[qrh,fks],status=I,gap='Would require separate A-D02 hypothesis (27/32), not supplied here. No judgment of falsity or unresolved assessment of an active claim.',scope='noncurrent_conditional_history',assume='unavailable historical A-D02, not current D01')
# Bind dependence/receipt context separately from the statement locations.
for row in rows:
 if row['claim_id'] in {'R-pi-finite-cube','R-pi-finite-log2-withdrawn','R-old-alt-uncorrected'}:
  row['actual_verification_receipts']+=['replay_original_pdf.jsonl: successful p.4 content stream layout check']
 if row['claim_id']=='D01-strip-reverse':
  row['propagation']=dict(input_used=True,where_it_changes_proof='Alternative only: replace admitted ζ portion of QRH by the holomorphic integral under D01; the active envelopes do not use this replacement.',matched_comparison='Same strip and no new consequence relative to B0.')
# Each exact source row carries the proof/trust readback; history is not a premise.
assert len(rows)==len({r['claim_id'] for r in rows})
receipts={}
for p in sorted(Path('.').glob('replay_*.jsonl')):
 receipts[p.name]=dict(file_sha256=sha(p),commands=[dict(line=i,argv=r['argv'],status=r['status'],stdout_sha256=r['stdout_sha256'],stderr_sha256=r['stderr_sha256']) for i,r in enumerate(map(json.loads,p.read_text().splitlines()),1)])
out=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=index['candidate_id'],
 assessment_complete=True,all_claims_inventoried=True,
 reviewed_source_hashes={r['packet_name']:r['sha256'] for r in keys.values()},
 source_bibliography=source['sources'],actual_effort_and_verification_commands=receipts,
 no_other_arm_or_ranking_seen=True,new_core_math_salvage_performed=False,original_candidate_bytes_changed=False,
 own_history_scope='OWN_ONLY; prior assessments are not mathematical premises; no claim of blinding to own history',
 proof_tier='written proofs and ordinary source replay plus original literature; no Lean or source-first PV asserted',
 family_assessments={},claims=rows)
for f in families:
 out['family_assessments'][f]=dict(strongest_supported_portfolio=[r['claim_id'] for r in rows if r['family']==f and r['M_status']==S],
  rejected_or_incomplete_claims=[r['claim_id'] for r in rows if r['family']==f and r['M_status'] in [I,F]],
  remaining_assessment_work=[],not_current_claims=[r['claim_id'] for r in rows if r['family']==f and r['scope'] in ['noncurrent_conditional_history','withdrawn_historical','quoted_and_rejected']],summary=(
  'Optimal open real sign ray and exact integer onset, corrected two-sided brackets, complete closed-cell profiles, tails through half degree 36; withdrawn square and quoted false PT sliver not used.'
  if f=='Ramanujan' else
  'Both relative products and both centered prime sums on real domains, finite and analytic steps and signed/power minima, including refined far coefficients; historical 27/32 input not used.'))
Path('review.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
status={'ready_for_review':True,'families':{f:{'status':S,'claim_files':['review.md','review.json']} for f in families},'serious_attempts_documented':True}
Path('STAGE_STATUS.json').write_text(json.dumps(status,indent=2)+'\n')
print(len(rows),'individually inventoried claims; JSON payload bytes',Path('review.json').stat().st_size)
