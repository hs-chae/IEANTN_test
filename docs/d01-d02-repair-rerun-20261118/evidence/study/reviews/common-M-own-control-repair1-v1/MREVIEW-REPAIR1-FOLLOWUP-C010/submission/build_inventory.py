#!/usr/bin/python3.10
"""Deterministic row/locator inventory generator. Pass restored exact source path."""
import json,sys,hashlib
from pathlib import Path
out=Path(__file__).parent
task=Path('/task')
restore=Path(sys.argv[1])
idx=json.loads((task/'CANDIDATE_INDEX.json').read_text())
bib=json.loads((task/'SOURCE_INDEX.json').read_text())['sources']
src={r['original_name']:r for r in idx['candidate_files']}
def anchor(f,l):
    d=src[f]; data=(restore/f).read_bytes()
    assert hashlib.sha256(data).hexdigest()==d['sha256']
    packet=task/d['packet_name']
    assert packet.read_bytes()==data
    spans=[]
    for span in str(l).split(','):
        bounds=[int(n) for n in span.replace('–','-').split('-')]
        lo,hi=bounds[0],bounds[-1]
        assert 1<=lo<=hi<=len(data.split(b'\n'))
        spans.append([lo,hi])
    first=spans[0][0]
    return dict(file=packet.name,original_file=f,packet_file=packet.name,
                physical_LF=first,physical_LF_spans=spans,sha256=d['sha256'])
def line(f,n):return (restore/f).read_text().split('\n')[n-1]
P='supported_at_stated_trust_tier'
B='baseline_retained'
X='false_with_specific_counterexample'
G='incomplete_with_specific_missing_step'
T='Both (shared dependency)'
R='Ramanujan'; M='Mertens'
Z='OpenAIQRH PDF 4 / LF255–262; FiniteRH PDF 2 / LF48–52; INPUT_CONTRACT.json'
F='FKS PDF 4–5 / LF275–347, PDF 8 / LF631–642'
FD='FKS PDF 7–8 / LF520–608 and PDF 26 / LF3139–3258 (published .77 corollary tier)'
H='CH2 PDF 3 / LF190–240, PDF 35–36 / LF5216–5223,5336–5355; FiniteRH PDF 4 / LF138–150'
K='CH2 Eq. (A.3) LF5892–5906 and B.8/(B.9) LF6744–6819; FKS LF275–313; Dusart 5.7 LF1555–1631'
DP='DudekPlatt arXiv:1407.1901v1 PDF 8 / LF561–563'
PT='PlattTrudgian arXiv:1809.03134v2 PDF 3 / LF205–212, PDF 9 / LF725–805'
Dtheta='Dusart 4.2–4.5 PDF 11–13 / LF959–1010,1049–1056,1095–1137'
Dpi='Dusart 5.1–5.3 LF1188–1214,1309–1355,1388–1401'
PTpi='PT Cor. 2 LF127–131, normalization LF710–712, §5(18)–(20) LF813–985'
DM='Dusart 5.6, 5.7, 5.9 LF1479–1553,1555–1631,1640–1664'
MF='Dusart LF455–475,487–765; PT LF77–118,135–201; FKS LF113–143,1928–1942,2307–2575,2581ff.'
FK='FKS Lemma 5.2/Cor. 1.4 LF1928–1942,140–143,2086–2092; Dusart 3.3 LF458–475'
tier='Allowed original results at exact hypotheses/publication trust; ordinary directed Decimal (where cited), not formal verification.'
density_tier=tier+' Also FKS Cor. 2.9 .77 published conclusion; its proof has the unresolved delta discrepancy.'
claims=[]
def item(cid,f,l,fam,what,domain,proof,sources='',code=(),ev=(),active=True,status=P,tm='B0 and B1',gain='',base='',strict='As displayed (closed enclosures unless a strict > or < is stated).',issue='',ret='',dt=False,mathobj=True):
    assert not any(c['claim_id']==cid for c in claims)
    obs=[]
    for x in ev:
        path=out/x
        obs.append(dict(path=x,sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
    claims.append(dict(claim_id=cid,written_source=anchor(f,l),family=fam,active_candidate_assertion=active,
      exact_statement=what,assumptions=tm,full_domain=domain,strictness=strict,
      real_or_integer=('Real, unless finite integer/spectral data are explicitly identified below.' if mathobj else 'Not applicable.'),
      baseline_comparison=base or ('Matched B0/B1 only; no claim of optimality.' if gain else 'No claimed D02 improvement for this assertion.'),
      source_locators=sources.split(' | ') if sources else [],
      derivation_check=proof,numerical_obligations=['See located code and reproduced receipts; analytic transfer in review.md.'] if code else ['No additional computational obligation beyond stated dependencies.'],
      implemented_formula_locations=[anchor(*c) for c in code],
      actual_verification_receipts=obs,retained_valid_branches=ret or 'Other applicable supported branches retained in the relevant pointwise envelope.',
      M_status=status,precise_gap_or_counterexample=issue,
      propagation=dict(input_used=bool(gain),where_it_changes_proof=gain or 'None (secondary or source-only assertion).',
                       matched_comparison=base or ('B0 at a=1/8 versus B1 at a=5/32 when used for paired gains.' if gain else 'Not a propagation result.')),
      V_status='Not checked: paper-only runtime, no Lean/Blueprint, verified execution or source-first PV artifact.',
      remaining_trust=density_tier if dt else tier))
co=('bounds.stdout',); av=('advance.stdout',); fi=('finite.stdout',); rp=('repair.stdout',); au=('audit.stdout',)
a='Mellin transfer changes b from 7/8 to 27/32 and a from 1/8 to 5/32 in the Perron and high primitive terms.'
sp='Spectral exponent and cutoff change from a0=1/8 to a1=5/32; finite branches and factorial polynomial are retained.'
mp='Same error transfer/relative conversion with changed high-zero cutoff and a0=1/8 versus a1=5/32.'
item('S-cut','spectral.md','3–35',T,'B0 zero cutoff 7/8; B1 cutoff 27/32 plus common finite RH to H=3000175332800.','All nontrivial zeros, cutoff boundary allowed; D02 input only x>=e^200.','See common audit: Mellin continuation makes the B1 cutoff applicable even to small x; no real nontrivial zeros.',Z,gain=a)
item('S-perron','spectral.md','38–48',T,'Explicit Perron transfer with T=exp(L/3), truncation 2.091 L exp(-L/3) and conjugate reciprocal sum.','L>=40, real L.','Admissible parameters and T*>T not needed (can equal T); no common T* presumed.',F,ev=au)
item('S-recip','spectral.md','49–60',T,'Twice the reciprocal sum through T* <= 1.4+.17(L/3+1)(L/3+2)<L^2/16.','L>=40.','Cor. 2.3 at U=100, checked shift and bound at 40, then termwise compare on whole ray.',F,(('bounds.py','175–181'),),co)
item('S1','spectral.md','62–64',T,'D_j*=2.091 L e^(-L/3)+(L^2/16)e^(-a_j L) dominates |e(L)|.','L>=40.','Use just cutoff and reciprocal budget.',Z+' | '+F,(('bounds.py','105–107'),),co,gain=a)
item('S2','spectral.md','66–98',T,'Upper Table 8 density rows and Tonelli integral S2 majorize the twice weighted reciprocal high-real-part tail.','s in [.75,.88] per listed rows and t>=3e12 for density; Tonelli starts at H.','Check published rows and coefficients then integrate t^-2; no low zeros with real part >=s.',FD+' | '+Z,(('bounds.py','66–74'),),co+('pdf_layout.stdout',),dt=True)
item('S3','spectral.md','100–107',T,'Fourth Taylor polynomial upper encloses the S2 integral; third polynomial gives its lower bracket.','Same s range, h=log H, q=5-2s.','Signs of fourth and fifth derivatives; term integration k!/A^(k+1).',FD,(('bounds.py','67–74'),('bounds.py','406–407')),co,dt=True)
item('S4','spectral.md','109–125',T,'Positive tail-weight coarse grid D_j dominates |e|, with D1<D0.','Endpoint L>=40; comparison of formula values L>0.','Running minima and terminal absorbing coefficient preserve zeros on cutoff; no difference of upper bounds treated as an upper bound for bin counts.',FD+' | '+F,(('bounds.py','75–96'),),co,gain=a,dt=True)
item('S5','spectral.md','127–145',T,'Continuous S5 through running infimum valid, no larger than step bound; limiting endpoint coefficient <=B_int(b_j), with S3 anchors .010444096,.146302424.','L>=40 and limit L→infinity.','Nonnegative derivative transfer; dominance by the mesh running weights; one-sided continuity at cutoff.',FD,(('bounds.py','67–74'),('bounds.py','416–417')),co,gain=a,dt=True)
item('S-C','spectral.md','148–158',T,'C(L) at H and signed/symmetric CH2 family plus CH2 1.3 with its own all-x radius.','C when x>H; CH2 1.2 x>max(T,1e9), 1e7<=T<=H; CH2 1.3 x>=1.','Correct coth center and log-square coefficient, zero center for weighted A, explicit upper coth allowance.',H,(('bounds.py','59–65'),('bounds.py','98–100'),('bounds.py','164–166'),('bounds.py','351–355')),co)
item('S6','spectral.md','160–165',T,'CH2 normalized finite square-root improvement F_psi(L) in S6.','34<=L<=58.','Chosen T passes H/1e7 and size constraints at both ends; increasing T.',H,(('bounds.py','115'),('bounds.py','129'),('bounds.py','170–172')),co)
item('S-finite','spectral.md','166–170',T,'FiniteRH/PT square-root theta/psi and CH2 signed .751/.791.','59<x<=2.169e25 for psi, 599<x<=2.169e25 for theta (PT theta to e^58); signed 1e4<=x<=1e13.','Original statements checked; no import of full RH or confusion with finite pi channel.',H+' | '+PT,(('bounds.py','173–174'),('bounds.py','373–375')),co,status=B)
item('S-cross','spectral.md','172–177',T,'Unique C/D_j crossings in (189.023,189.024), (168.795,168.798).','L>=100, coarse D_j only.','C slope <1e-7 (repair.py), mixture slope <=-1/8, checked signs at both ends.',H+' | '+FD,(('repair.py','56–59'),('bounds.py','383–387')),co+rp,gain=a,dt=True)
item('S-direct','spectral.md','177–180',T,'Direct D02 ray majorant is dominated by the B1 D1 branch.','L>=200.','The scaled D1 decreases and already is below .3 at 200; direct coefficient is at least 625.',FD,(('bounds.py','341–349'),('bounds.py','388')),co,status='equivalent_or_weaker',tm='B1',dt=True)
item('S7','spectral.md','184–220',T,'Absolutely convergent once-integrated exact formula S7 for K; L-1-gamma normalization of Perron kernel.','x>1 for identity.','Contour kernel, residues, chosen heights, normalization and absolute convergence checked in review common audit.',K)
item('S8','spectral.md','222–240',T,'|K| <= .047 e^(-L/2)+8e-12 e^(-a_j L)+1.838e^(-L)+e^(-3L).','L>=log2.','Positive real parts via B.9; inverse-square high bound by Tonelli and Rosser; elementary tails checked.',K,(('bounds.py','318–324'),('bounds.py','361–370')),co,gain=a)
item('S8-tight','spectral.md','242–248',T,'High term may be reduced via low/high split with S4/S5; elementary terms may be signed center; limiting M coefficient factor 1+1/H.','L>=log2; limit after scaling applicable envelopes.','Second denominator gives a factor 1/H in high density sector, low sector is negligible at limiting scale.',FD+' | '+K,dt=True,gain=a)
item('A-light','advance.md','12–27',T,'d_light,j=(3.491+.17(Y+1)(Y+2)) exp(-a_jL), Y=a_jL+log L, with limiting endpoint coefficient .17 a_j^2.','L>=40.','Use smaller T=L exp(a_jL), reuse reciprocal budget; no Table 8.',F,(('advance.py','4–8'),('advance.py','146–150')),av,gain=a)
item('A-split','advance.md','29–50',T,'d_split,j splits reciprocal budget at H, including the W_+ convention, and B0 branches remain selectable in B1.','L>=40.','FKS(2.1) at H with closed cutoff limits and finite-RH low term.',Z+' | '+F,(('advance.py','10–17'),),av,gain=a)
item('A-fine','advance.md','144–157',T,'d_fine,j reduces bin width to 1/12800 without weakening valid old grid enclosure.','L>=40.','Common nodes exact, refinement of positive step upper bound; Horner readback with correct first/last exponents.',FD,(('advance.py','19–44'),),av,gain=a,dt=True)
item('A-kernel','advance.md','315–344',M,'Absolute W-weighted tail radius W(L)k_j(L) removes the derivative-budget term of old M4; U unchanged.','Identity L>=log2; V replacement on domain of M4.','Integrate K by parts against e^(-tu) and use |z/(z+t)|<=1, then Fubini. Main coefficient checks still use old M4.',K,ret='M4 remains valid independently of newer transfer.')
item('R-last','ramanujan.md','10–56',R,'Last real failure is equality at r in (38358837682.217926,38358837682.217927); strict R>0 for every x>r. Last integer failure n=38358837682.','Right ray open at r; closed integer ray begins n+1.','Quotient sieve counts A=1644673232, B=632207037; monotonicity on fixed-count cell, then floor extension of publication-trust integer input and analytic sign join.',PT+' | '+DP,(('bounds.py','283–307'),('bounds.py','258–260')),co+au,tm='B0; inherited finite integer assertion',base='Already sharp under B0; D02 does not improve it.',strict='Strict R>0 only to right of r; equality at r and strict failure at n.')
item('R-original-sign','ramanujan.md','39–54',R,'PT finite integer restriction through floor(e^58) and old far analytic sign branches 3915/9658 at original trust; no use of global RH-conditional DP result.','PT integers n+1..floor(e^58); analytic real rays x>=exp(3915), exp(9658).','PT and DP wording checked; actual transfer uses only finite integers then new analytic bounds.',PT+' | DudekPlatt LF45–55,591–715',status=B,tm='B0')
item('R-PT-real-quote','ramanujan.md','42–45',R,'Quoted source literal real claim R>0 on n<x<=e^58 (excluded by candidate).','n<x<=e^58, all real.','The local exact prime counts are constant, so the source statement at the bracket lower endpoint has the opposite sign.',PT,(('bounds.py','296–307'),),co+au,active=False,status=X,issue='At x=38358837682.217926, R(x) in (-24.693,-24.692).',ret='Published finite integer portion at its qualified literature trust.')
item('R2','ramanujan.md','151–164',R,'Factorial polynomial and explicit asymmetric smooth remainder R2, v=10Le^-L+(15/4)21!L^-21.','L>=30.','Anchor series and geometric bound after term 180, derivative/log slope 4/15.',code=(('bounds.py','153–157'),('bounds.py','182–193')),ev=co)
item('R3','ramanujan.md','166–172',R,'Stieltjes center identity for Xi under theta.','x>=2.','Boundary at 2 included; main integral equals specified F.')
item('R-bF','ramanujan.md','175–182',R,'b_F incl. sharper finite endpoint S6 option starting 34.','20<=L<=58; alternate endpoint 34<=L<=58.','PT finite theta plus early 1250 integral and optional endpoint CH2 plus drift.',PT+' | '+H+' | '+Dtheta,(('bounds.py','111–116'),('bounds.py','167–174')),co)
item('R-bC','ramanujan.md','183–191',R,'b_C=λ(1+10/(9L))+114.671001(1+2.5/L)e^-L/2+1.78(1+30/(7L))e^-2L/3+3100Le^-L.','L>=20.','Initial finite theta then CH2/drift, lower log slope of each integral.',H+' | '+Dtheta,(('bounds.py','102–104'),('bounds.py','167–169')),co+au)
item('R-bD','ramanujan.md','192–211',R,'b_D uses (1+1.63/L)D_j, (1+2.23/L) and (1+3.53/L) times drift, and 4e7 Le^-L; same with S1/continuous S5.','L>=40.','Use slope 1-a-2/40>=.6167 for endpoint mix; continuous integrand is a positive mixture.',F+' | '+Dtheta,(('bounds.py','105–110'),('bounds.py','169')),co,gain=sp)
item('R-split-transfer','advance.md','110–140',R,'Split replaces b_D factor 1.63 by 2.23; other drift/asymmetric budgets unchanged, with cell and tail monotonicity on used ranges.','L>=40 for transfer; used certificate ranges from 315/238 at shifted arguments; tail unshifted L>=450.','Nondecreasing high coefficient permits comparison in integral; low exp exponent 1/2; split derivative and log allocations checked.',F+' | '+Dtheta,(('advance.py','46–73'),('advance.py','151–158')),av,gain=sp)
item('R4','ramanujan.md','213–247',R,'Signed upper u=max(0,min(b,d+J-V)) and lower magnitude w=min(b,d+J+U_2); optional u=0 through 1.2e17 on early signed premise.','L>=34, finite extra sign only within original x range.','Integration by parts with K a.e.; negative drift and endpoint signs, exact early budget; compare li normalizations.',Dtheta+' | '+K+' | '+DP,(('bounds.py','125–151'),('bounds.py','389–391'),('advance.py','50–73')),co+av,gain=sp)
item('R5','ramanujan.md','255–278',R,'Strict R5 polynomial/signed profile, symmetric profile and exact rational main expression, plus S5 option.','L>=35, L-1>=34.','Binomial factorial coefficients; positive omitted terms; exact rational option uses strict shifted smooth remainder. Max of valid lower bounds.',code=(('bounds.py','153–163'),('bounds.py','225–239'),('advance.py','75–88')),ev=co+av,gain=sp,strict='Strict > including real left endpoints.')
item('R-tail','ramanujan.md','280–309',R,'Inclusive cells split on shifted applicability; analytic monotone tail using scaled losses and optional extra scaling when m=c_k.','Through 450 plus [450,infty); deep k>8 uses 650 as in advance.md.','Positive terms, rates and dropping negative terms justified; first fourteen coefficients nonnegative. Both x and x/e checked.',code=(('bounds.py','214–240'),('advance.py','75–88')),ev=co+av+au)
item('R-limit','ramanujan.md','122–128',R,'G→1; no whole-ray constant margin >1. Symmetric point checks are only certificate obstructions.','L→infinity; no claim about one point or other proof method.','Two-sided center and expansion, leading coefficient 1, all scaled errors vanish.',code=(('bounds.py','310–316'),('bounds.py','465–469')),ev=co)
for n in list(range(76,105))+list(range(112,119)):
    txt=line('ramanujan.md',n)
    parts=txt.strip('|').split('|'); assert len(parts)==4 and txt.startswith('|')
    fixed=n>=112
    if fixed:
        k,on,b0,b1=parts
        st=f'R1 strict prefix order {k}, common log onset {on}, m={b0} in B0 and m={b1} in B1.'
    else:
        k,m,b0,b1=parts
        st=f'R1 strict prefix order {k}, m={m}, log onsets {b0} B0 and {b1} B1.'
    opt=n in [76,81,86,89,96,99,102,112]
    code=(('bounds.py','195–212'),('bounds.py','214–245'))+((('bounds.py','248–256'),) if opt else ())
    item(f'R1-{n}','ramanujan.md',n,R,st,'Real closed ray(s) from stated log-onset(s), strict lower inequality.',
         'Finite and monotone-tail replay; '+('uses IMPROVED and/or stronger applicable row, not just the symmetric table.' if opt else 'raw rows or stronger applicable rows as described in review.md.'),
         F+' | '+H+' | '+FD,code,co,dt=True,gain=sp if b0!=b1 else '',base='Matched onsets/strengths as listed; in fixed rows retain earlier table maxima.')
for n,on,m,end in [(135,'36.55','0','infinity'),(135,'36.64','.05','infinity'),(136,'36.75','.1','infinity'),(136,'36.88','.16','infinity'),(138,'36.98','.2','log(1.2e17)'),(139,'39','.8','log(1.2e17)')]:
    item('R-bridge-'+on,'ramanujan.md',n,R,f'G>{m} from {on} through {end}.',f'Closed real log range [{on},{end}] (infinity denotes a ray).',
         'Inherited signed upper at x only; shifted lower R4 and finite cells; 39.32 .16 ray bridges if infinite.',DP+' | '+H,(('bounds.py','248–256'),('bounds.py','262–281')),co,tm='B0 (B1 inherits)')
for k,m,u0,u1 in [(0,0,39.25,39.25),(2,145,360,275),(3,1412,405,326)]:
    item('R-fallback-'+str(k),'ramanujan.md','144–147',R,f'Density-free R1 k={k}, m={m} from log {u0}/{u1}.','Closed real ray(s) at the specified pair.',
         'Same coefficient/cell proof, D_j* on fallback, symmetric finite-height before it.',F+' | '+H,(('bounds.py','214–240'),('bounds.py','258–260')),co,gain=sp if u0!=u1 else '')
item('R-fallback-extra','bounds.py','258–260',R,'Replay-only redundant k=1,m=7 from log 46.6 (both).','Closed real ray.','Same fallback verification; stronger k=1 row retained.',F,(('bounds.py','214–240'),),co)
for n,k,m,b0,b1,lbl in [(107,2,145,316,239,'split'),(108,3,1412,353,268,'split'),(181,2,'80.9','196.58','48.95','fine'),(182,3,1412,'253.55','211.04','fine')]+[(i,*line('advance.md',i).strip('| ').split(' | '),'deep') for i in range(205,212)]:
    item(f'RA-{n}','advance.md',n,R,f'{lbl.capitalize()} R1 k={k}, m={m}, B0/B1 log onsets {b0}/{b1}.','Closed real log-rays, strict lower bounds.',
        'R2–R5 applied using the indicated refined or split transfer, with actual finite cells, shifted arguments and monotone scaled tails.',
        (F if lbl=='split' else FD)+' | '+H,(('advance.py','46–88'),('advance.py','208–218')),av,dt=(lbl!='split'),gain=sp,base=f'Matched sufficient equal-margin onsets {b0} versus {b1}.')
item('R-fine-fixed','advance.md','187–195',R,'At fixed log onset 50, B1 m=80.9 for k=2. Attempted 81 from 49 fails as a constructed profile test.','L>=50 for gain, example L=168.72 for profile diagnostic.','48.95 row covers full ray; diagnostic concerns profile, not actual gap; optional explore list omits exact 168.72, audited separately.',FD,(('advance.py','90–92'),('advance.py','208–213'),('advance.py','219–225')),av+au,dt=True,gain=sp)
item('R-Dusart-direct','ramanujan.md','320–334',R,'Direct pi intervals from Dusart 5.1/5.2/5.3 usable in combined portfolio.','5.1 symmetric x>=4e9, upper x>1. 5.2 lower >=17/599/88789, upper x>1. 5.3 lower >=5393/468049 and upper >e^1.112/>5.6. Apply to each argument separately.','Correct formulas/endpoints; stricter shifted onset whenever both needed.',Dpi,status=B)
item('R-PT-cor2','ramanujan.md','324–330',R,'PT Cor. 2 relative Xi radius 235 L^1.52 e^(-.8sqrt L) at its integral-from-2 center.','Argument log >=2000; both arguments usable at L>=2001.','Correct conversion to Xi; translate by (2/log2)L e^-L when comparing with F.',PTpi,status=B)
item('R-PT-small-quote','repair.md','69–71',R,'Quoted first piece of PT §5(18) claims small relative theta allowance 1-log2/2.','2<x<=599.','False source estimate explicitly not used.',PTpi,(('repair.py','24–27'),),rp+au,active=False,status=X,issue='x=2.9 has theta=log2 and relative error exceeding printed upper by >.10755.')
item('R-PT-small','repair.md','72–78',R,'Sharp corrected uniform relative theta allowance 1-log2/3.','2<x<=599, supremum at 3 from left.','Monotone theta/x between jumps; exact primality and directed one-sided endpoints.',PTpi,(('repair.py','27–35'),),rp)
item('R-PT-anchor','repair.md','80–122',R,'Retain published m_a,M_a as coefficients of L^-5 in Xi-P4 at U=3914 without using false theta premise.','Argument log >=3914; at both Ramanujan arguments L>=3915.','Independent candidate method dominates these numeric expressions using R2/R3 density-free; 120<L^5(Xi-P4)<120+.19; bound -C2, compare bracket >=B.',PTpi,(('repair.py','36–51'),('advance.py','204–206')),rp+av+('pdf_layout.stdout',))
for cid,file,l,on,case,num in [('R-strict-coarse','ramanujan.md','336–350','168.82','constructed R4–R5','bounds'),('R-strict-fine','advance.md','222–295','168.745','combined including direct upper endpoints','advance'),('R-strict-split','advance.md','297–311','342','combined using density-free improvement','advance')]:
    item(cid,file,l,R,f'Strict B1 improvement of {case} from L={on}.',f'Whole closed ray L>={on}; nesting by retaining B0 before it.',
         'Old upper error above f0-V (direct upper endpoints also separated in the combined claim), new upper below F*. Strict unshifted square shrinkage and nonworse shifted lower.',
         Dpi+' | '+PTpi+' | '+H,((num+'.py','394–407' if num=='bounds' else '175–206'),),(num+'.stdout',)+au,gain=sp,dt=cid!='R-strict-split',
         base='Strict comparison to specified old envelope, not to all attainable B0 proofs.')

item('M-norm','mertens.md','3–13',M,'Exact M=gamma+sum_p(log(1-1/p)+1/p), B3=gamma+sum_{m>=2,p}log(p)/p^m; both relative products, reciprocals and weighted normalized as written.','Real x>1 with x>=2 for nonempty data.','Raw Q and P reciprocal; log Q normalization gives exp(Zraw), normalized P exp(-Zraw).',DM)
item('M2','mertens.md','171–190',M,'A=e-K, Z=e/L-integral(e W), and integrated-by-parts signed K formula.','x>=2 (right-continuous data).','Partial summation, normalization by prime-power limits, K is absolutely continuous.',DM+' | '+K)
item('M-corr','mertens.md','192–198',M,'E_l=A+C_l, E_1=Z+C_1, Z_raw=Z+C_P, with positive prime-power tails and C_P restricted to p<=x.','x>=2.','Compute added finite versus infinite prime powers in each of the exact normalizations.',DM)
item('M3','mertens.md','199–222',M,'C_l<=1.34e^-L/2, C_P<=C_1<=1.34e^-L/2/L at L>=18; 1.37 at 17.8.','Closed rays at the respective log-onsets.','Square signed theta budget, higher power grouping and geometric tail; decreasing ratios and left checks.',Dtheta,(('bounds.py','326–331'),('bounds.py','371–372')),co)
item('M4','mertens.md','224–240',M,'U=d+k+p, V=[d+(1+1/L)k+(1/L+2/L^2)J_k+p]/L. Bounds |E_l|<=U, |E_1| and |Zraw|<=V.','As applicable for d plus M3 on L>=17.8.','Old M2 integration and decreasing |W prime|. Code mux still uses larger M4; kernel option a strict algebraic improvement.',K+' | '+Dtheta,(('bounds.py','318–339'),),co)
item('M-conversion','mertens.md','230–232,317–327',M,'Exact signed log interval conversions, cheap V/(1-V) only for 0<=V<1.','Applicable log-interval domains; exact exponentials for all finite log endpoints.','Monotonic exponential, comparison of geometric and exponential series; positivity checked explicitly on all numerical uses.',code=(('bounds.py','341–349,394–401,410–415,434–456'),('finite_m.py','119–131'),('advance.py','93–115')),ev=co+fi+av)
for i in range(28,42):
    u,c0,c1=line('mertens.md',i).strip('|').split('|')
    item(f'M1-{i}','mertens.md',i,M,f'M1 products and reciprocal <=C x^-a/L, weighted <=C x^-a, C={c0}/{c1} for B0/B1.',
         f'Closed real L>={u}.','M4 monotone after rescaling; relative output dominates weighted/log budgets in matching units; compare left ratio.',
         FD+' | '+K,(('bounds.py','333–349'),('bounds.py','408–425')),co,dt=True,gain=mp,base=f'B1 row wins on every real L>={u}; ratio ({c1}/{c0}) exp(-L/32).')
item('M1-parameter','mertens.md','43–46,233–239',M,'Continuous-onset coefficients via den_limit; four extra output anchors 1500,2500,5000,10000.','Each arbitrary real onset u>=170; closed ray L>=u.','Use e^(a u)u V(u)/(1-V(u)) as common coefficient; numeric entries are sufficient, not optimal.',
     FD,(('bounds.py','341–349'),('bounds.py','408–409')),co,dt=True,gain=mp)
item('M1-limit','mertens.md','46–49',M,'Coarse limiting constants .010444096(1+1/H), .146302424(1+1/H) in M1 scaled units.','L→infinity, respective scalings.','Use continuous tail S5 and tighter K high term; all smaller exponentials/log factors vanish and expm1 asymptotically linear.',
     FD+' | '+K,(('bounds.py','416–417'),),co,dt=True,gain=mp)
for cid,srcf,lf,c0,c1,det,coo,outt in [
    ('M-fallback','mertens.md','57–61','0.0626','0.0626','S1 scaled by L^-2 and S8; positive bounds monotone from 300.',(('bounds.py','410–415'),),co),
    ('M-light','advance.md','52–72','.003814','.005563','d_light with decreasing positive normalized factors and V<1.',(('advance.py','4–8,93–96,159–165'),),av),
    ('M-split','advance.md','74–100','.00262','.00408','d_split via 440 width-five cells through 2500 and final positive-part tail anchor.',(('advance.py','10–17,98–116,163–165'),),av)]:
    item(cid,srcf,lf,M,f'Density-free C={c0}/{c1} in B0/B1 for products and recips (multiply L x^-a) and weighted (multiply L^2 x^-a).',
         'Real L>=300 inclusive.',det,F+' | '+K,coo,outt,gain=mp,base=f'B1/B0 ratio ({c1}/{c0})exp(-L/32) <1 throughout the matched ray; log penalty versus M1 retained.')
item('M-light-limit','advance.md','67–69',M,'Density-free limsup <=.17 a_j^2 in the light row units.','L→infinity.','Scaled endpoint factor divided by L^2 tends to .17 a_j^2; other factors vanish and conversion linearizes.',F,gain=mp)
item('M-split-limit','advance.md','96–98',M,'Density-free limsup <=c_H^* a_j^2 in the split row units.','L→infinity.','Split high polynomial-log term dominates scaled endpoint bound, lower K and corrections negligible.',F,gain=mp)
for i in range(165,170):
    u,c0,c1=line('advance.md',i).strip('| ').split(' | ')
    item(f'MA-{i}','advance.md',i,M,f'Fine M1 constants {c0}/{c1} for products and recips in x^-a/L and weighted in x^-a.',
         f'Closed real L>={u}.','Same M4 and no finite samples; fine mesh monotonic scaled tail and conversion at left anchor.',FD+' | '+K,
         (('advance.py','19–44,93–96,167–174'),),av,dt=True,gain=mp,
         base=f'B1/B0 ratio ({c1}/{c0})exp(-L/32) <1 throughout L>={u}.')
for i,proof,desc,u in [(66,'5.6','reciprocal .2/L^3',2278383),(67,'5.7','weighted .3/L^2',912560),(68,'5.9','both products .2/L^3',2278382)]:
    item('M-Dusart-'+proof,'mertens.md',i,M,f'Retain published {desc}.',f'Closed real x>={u}.','Checked actual Dusart normalized result and finite domain, not Remark 5.8.',DM,status=B,tm='B0 (and retained in B1)')
for i,desc in [(75,'Q has least .2 ray at 2278379+t, t in (2.710,2.713)'),(76,'P has least .2 ray at 2278379+t, t in (2.574,2.577)'),(77,'reciprocal least .2 ray at 2278379+t, t in (3.111,3.115)'),(78,'weighted least .3 ray at 912559+t, t in (.997,.998)')]:
    item(f'M-local-{i}','mertens.md',i,M,desc,'All real x at or above true local equality root.','Fixed prime data by exact sieve; endpoint signs and strictly negative scaled derivatives; old source ray at its own inclusive onset. Immediate left failures.',
        DM+' | '+Dtheta,(('finite_m.py','34–116'),),fi,tm='B0 (B1 inherits)',strict='Non-strict error bound, exact equality at least onset.')
item('M-finite-constants','mertens.md','129–167',M,'Finite sieve/cell method and exact enclosures of M,B3,gamma by independent tails.','Sieve through 54e6; cell cover [500000,54e6].','Fixed-point logs and power tails checked individually; normalization constants not rounded literature decimals; both error scales controlled by closed cells.',
     Dtheta,(('finite_m.py','7–95,117–141'),),fi)
for i in range(104,111):
    u,c=line('mertens.md',i).strip('|').split('|')
    item(f'M-early-{i}','mertens.md',i,M,f'Both products and recips <= {c}/L^3, weighted <= {c}/L^2.',
         f'Real L>={u} closed.','CH2 finite/signed on its admissible domain, selected CH2 symmetric bounds after; closed cells and monotone tail after 220.',
         H+' | '+FD,(('bounds.py','428–458'),),co,dt=True,tm='B0 (B1 inherits)')
for i in range(121,128):
    c,p,r,w=line('mertens.md',i).strip('|').split('|')
    item(f'M-finite-{i}','mertens.md',i,M,f'Finite-to-ray log coefficient c={c}, product onset {p}, recips {r}, weighted {w}.',
         'Real inclusive rays from each stated integer-valued onset.','Closed cell enclosures through 54e6, overlapping .1 analytic ray from e^17.8. Earlier original .2 rows not weakened.',
         H+' | '+FD+' | '+Dtheta,(('finite_m.py','117–141'),('bounds.py','428–458')),fi+co,dt=True,tm='B0 (B1 inherits)')
item('M-empty','mertens.md','257–260',M,'Exact empty sums and products 1 on 1<x<2.','Real x in (1,2).','No limiting/log approximation outside proof-bearing domain.')
item('M-env-psi','mertens.md','266–277',M,'Full pointwise I_e min of valid spectral and direct-source intervals, including limited FKS Lemma 5.2 and D02 only where applicable.','Real x>=2; each branch at original separate domain.','Cor. 1.2/1.3 and retained original steps, log powers and asymptotic curves read back at original hypotheses; FKS defective small piece removed.',
     MF+' | '+H+' | '+FK,ev=rp,dt=True,gain=mp)
item('M-FKS-quote','repair.md','39–43',M,'Quoted FKS Lemma 5.2 coefficient-2 curve on full printed small-x domain (not used as written).','0<log x<=2100.','Exact psi=log2 at x=2 and 2.1; counterexamples, not candidate final claims.',FK,(('repair.py','4–11'),),rp+au,active=False,status=X,issue='At 2 and 2.1 relative error exceeds g(L) by >.08356 and >.05407, respectively.')
item('M-FKS-repair','repair.md','37–61',M,'Coefficient-2 curve valid on [r_psi,e^2100], r_psi least real onset with r_psi in (2.29012,2.29014).','Real closed finite segment to e^2100; equality at left root.','Derivative on [2,3) and both bracket signs; use .77 on [3,e^40], two reported source steps through log 2100; smaller onset includes local failures.',
     FK,(('repair.py','4–21'),),rp+au)
item('M-FKS-weak','repair.md','62–65',M,'FKS Cor. 1.4 with larger 9.22022 coefficient remains valid; supply valid comparison near 2.','Real x>2.','Dusart .77 dominates needed error near 2; lemma repair and other parts of published corollary cover rest.',
     FK,(('repair.py','22'),),rp,status=B)
item('M-env-theta','mertens.md','278–286',M,'I_K signed-center/high variants and I_f from drift subtraction with direct theta intersections.','Real x>=2; V_theta positive when x>=121, per branch thresholds.', 'All primitive and optional direct theta branches enclose exact quantities under the written domains.',
     Dtheta+' | '+PT+' | '+H+' | '+K,gain=mp)
item('M-env-A','mertens.md','287–290',M,'Weighted lambda A has I_e-I_K, CH2 original A, and direct tail I_e - integral I_e.','Real x>=2 with CH2 own separate domains.','Taking intersections preserves enclosure; exponential endpoint envelope bounds improper integrals.',
     H+' | '+K,gain=mp)
item('M-env-Z','mertens.md','291–296',M,'Z uses M2, M4 without pp, and A(L)/L-integral A/u² or A(L)/L+integral e(1/L-W).','Real x>=2; M4 at own applicability.','Double integral elimination yields both Z identities; interval multiplication respects signs.',K,gain=mp)
item('M-env-sums','mertens.md','297–304',M,'Corrected Z/E1, A/E_l and log-product intersections with direct theta sum tails and p>x removal.','Real x>=2.','Correct source constants and signed kernels; summation includes p=x but tails exclude it.',DM,gain=mp)
item('M-env-powers','mertens.md','305–316',M,'Signed theta weighted tail identity, atom at 2 if y<2, and explicit tail beyond m0.','Real x>=2; y=x^(1/m) or x with y>=2 before atom correction.','Monotone weights, theta estimate on both boundary and integrated terms and geometric domination.',Dtheta)
item('M-env-conv','mertens.md','317–327',M,'Pointwise min of converted log intervals, source-relative, power and finite bounds; tails converge.','On applicable real branches for every x>1.','Take signed conversion before comparing envelopes; optional tighter log kernel plus lower pp signs.',DM+' | '+K,gain=mp)
for cid,f,i,d,u in [
    ('M-signed-weight','mertens.md',334,'E_l>.054 x^-1/2',18),
    ('M-signed-log','mertens.md',335,'E_1,Zraw>.06 x^-1/2/L',20.8),
    ('MA-signed-weight1','advance.md',351,'E_l>.0012 x^-1/2',15.4),
    ('MA-signed-weight2','advance.md',352,'E_l>.0556 x^-1/2',18),
    ('MA-signed-log1','advance.md',353,'E_1,Zraw>.00015 x^-1/2/L',20.6),
    ('MA-signed-log2','advance.md',354,'E_1,Zraw>.0889 x^-1/2/L',20.77)]:
    newer=f=='advance.md'
    item(cid,f,i,M,d,f'Closed real log interval [{u},log(1e13)].',
         'CH2 signed bound plus S8 and signed lower square contribution. '+('Uses absolute Laplace kernel, cubic contribution and directed endpoints.' if newer else 'Uses integrated derivative budget, and excludes product p>x tail.'),
         H+' | '+K+' | '+Dtheta,(('advance.py','118–141'),) if newer else (('bounds.py','373–381'),),av if newer else co,tm='B0 (B1 inherits)')
item('M-one-sided','advance.md','346–363',M,'With positive Zraw on the signed compact ray, normalized P<1<Q and P error <=1-e^-u for log upper u.','New L>=20.6 through log(1e13); old L>=20.8 through same top.','Sign proved by the finite signed branches; exact exponential comparison. Not an all-ray sign.',H,ev=av+co)
for cid,f,l,on,d,prg in [
    ('M-strict-coarse','mertens.md','361–416','168.82','coarse','bounds'),
    ('M-strict-fine','advance.md','222–249','168.745','fine','advance'),
    ('M-strict-split','advance.md','297–311','342','density-free split','advance')]:
    item(cid,f,l,M,f'Strict B1 improvement of all four specified pointwise envelopes using {d} transfer.',
         f'Real L>={on} inclusive; nonstrict nesting by retention elsewhere.',
         'Every B0 branch contains f0 with stated drift allowance and hence F* in scaled units (through product conversion). New U and relative conversion are below F* at anchor and ratios decrease.',
         H+' | '+MF+' | '+DM,((prg+'.py','394–407' if prg=='bounds' else '175–189'),),(prg+'.stdout',)+au,
         gain=mp,dt=('split' not in cid),base='Strict dominance versus the given B0 envelope, not all possible estimates. Split also works without density on comparator side after dependent branches removed.')
item('M-.002','mertens.md','417–424',M,'B1 gives coefficient .002 in the old 1/8 exponent units with same log powers, and the shown B0 envelope cannot certify that constant on a whole ray.','L>=170 closed; latter statement pertains to asymptotic envelope floor.','Use M1 170 B1 row times exp(-L/32); old envelope bounded below by F* in matched units. Not an arithmetic lower bound on the errors.',
     FD,(('bounds.py','425'),),co,gain=mp,dt=True)
item('history-slope','prior_spectral.md',169,T,'Superseded |C prime/C|<1e-8 for L>=100.','L>=100.','Explicit value at 100 exceeds threshold; repair changes threshold to 1e-7.',H,(('repair.py','56–59'),),rp,active=False,status=X,issue='At L=100 ratio is 1.04685980098e-8.')
item('history-M-fks-inclusion','prior_mertens.md',270,M,'Superseded full printed FKS Lemma 5.2 inclusion.','Quoted Lemma 5.2 small domain overlaps x>=2.','False at x=2 and 2.1; branch restricted in current M envelope.',FK,(('repair.py','4–17'),),rp+au,active=False,status=X,issue='Erroneous included upper radius for e at x=2 and x=2.1; see M-FKS-quote.')
item('history-R-anchor','prior_ramanujan.md','319–325',R,'Archived unqualified original PT (19),(20) branch by original argument.','Individually at x and x/e, old §5 anchor.','Original proof uses false small-input theta piece; numerical functions recovered in current repair, no arbitrary anchor claim.',PTpi,(('repair.py','24–51'),),rp,active=False,status=G,issue='Original proof invocation at that point did not justify the small-input estimate; now bypassed by R-PT-anchor.')

# Separate immutable rows for actually implemented numeric branches not verbatim in the prose tables.
for lf,k,m,u0,u1 in [(197,0,'0','39.25','39.25'),(198,0,'1','42.75','42.75'),
    (203,3,'1412','253.75','211.25'),(205,4,'13985','288','236.6'),
    (206,5,'145450','322.85','262.5'),(210,2,'7.8/80','50','50')]:
    item('R-code-symmetric-'+str(lf),'bounds.py',lf,R,
         f'Actually replayed symmetric-only k={k} m={m} with B0/B1 log onsets {u0}/{u1}, superseded or inherited by stronger written profile where applicable.',
         'Closed rays, strict R1.', 'Raw ROWS/FIXED checker has different settings from signed IMPROVED; each checked variant is retained or dominated.',
         F+' | '+FD,(('bounds.py','214–245'),),co,dt=True,gain=sp if u0!=u1 or '/' in m else '')
item('R-code-16','bounds.py',249,R,'Signed G>.16 on both analytic rays from log 39.32.',
     'L>=39.32 inclusive; overlaps the finite signed bridge.', 'Actual IMPROVED ray, used as endpoint glue in G>0/.05/.1/.16.',
     H+' | '+FD,(('bounds.py','214–240,248–256,280'),),co,dt=True)
item('R-integer-DP-crosscheck','ramanujan.md','49–54',R,'Original DP finite integer computation and distinction from global RH conclusion.',
     'Integer restriction separately read for finite ranges through 1e11 and 1.15e16, no RH extrapolation.',
     'As corroboration of inherited PT integer trust, DP LF591–594 plus Lemma 3.4 LF707–714 already reach beyond the beginning of the new analytic sign bridge.',
     'DudekPlatt PDF 2 LF45–55, PDF 8 LF591–594, PDF 10 LF707–715',
     (('bounds.py','281'),),co,status=B,tm='B0; published finite computation statements')
for u in [1500,2500,5000,10000]:
    item('M-implemented-anchor-'+str(u),'bounds.py',408,M,f'Replay-only real onset u={u}, numerical uppers of weighted, log and relative coefficient for the parametric M1 family.',
         f'Closed rays L>={u}.','Anchor is upward using den_limit; inherits scaled monotonic ratios, not claimed optimal.',
         FD,(('bounds.py','341–349,408–409'),),co,dt=True,gain=mp)
for lf,k,x,m in [(466,2,'189.04','8'),(466,2,'199.8','100'),(466,2,'214.7','140'),
                (467,2,'220.4','145'),(467,3,'253.6','1412'),(467,4,'287.8','13985'),
                (468,5,'322.7','145450'),(468,6,'356.3','1600000')]:
    item('R-diagnostic-'+x,'bounds.py',lf,R,f'Constructed B0 symmetric residual below target {m} for k={k} at L={x}.',
         f'Individual numerical obstruction at L={x}, no assertion about the actual arithmetic gap.',
         'Uses lastnot with bC/bD; tests failure of the sufficient lower bound only.',
         FD,(('bounds.py','310–316,465–469'),),co,dt=True,active=True)
item('R-max','ramanujan.md','106–128',R,'Take maximum of all applicable real lower branches; fixed-onset examples do not replace earlier applicable better rows.',
     'Every applicable real log-ray with the correct onset and strictness.','Max of pointwise valid lower bounds; retain sign only where appropriate.',
     ev=co)
for cid,lf,stmt,dom,loc in [
    ('M-CH2-old','266–268,287–290','Original signed psi and centered A intervals of CH2 Cor.1.2/1.3.',
     '1.2 at x>max(T,1e9), 1e7<=T<=H; 1.3 x>=1 (used at x>=2).',H),
    ('M-Dusart-psi','270–271','Dusart Proposition 3.2/Table1 steps and Theorem 3.3 shapes.',
     'Step x>=exp(b0) for the stated table constants or stipulated computable applicable b0; log forms x>=2.',
     'Dusart PDF 8–9 LF455–475,487–765'),
    ('M-PT-psi','271','PT Theorem 1 step bounds and normalized A(L/R)^B exp(-C sqrt(L/R)).',
     'L>=X of each row, R=5.573412.','PT PDF 2–3 LF77–95,135–201'),
    ('M-FKS-table5','274–277','FKS published Table 5 step radii, not freely instantiated general choices.',
     'L>=each respective table onset as published; general formula log x0>1000.','FKS PDF 2 LF113–117, PDF 22 LF2307–2575'),
    ('M-FKS-table6','274–277','FKS published Table 6 asymptotic curve with R=5.5666305.',
     'L>=each respective table onset; general formula log x0>1000.','FKS PDF 2 LF118–135, PDF 23 LF2581ff.'),
    ('M-retained-theta','284–286','Original theta direct estimates available by intersection.',
     'Dusart 4.2 by row; PT Cor.1 by X; PT Lemma 6 599<x<=exp58; FiniteRH Cor.1 599<x<=2.169e25.',
     Dtheta+' | '+PT+' | '+H)]:
    item(cid,'mertens.md',lf,M,stmt,dom,
         'Actual source formulas, domains and normalization reviewed; only original applicable intervals retained.',
         loc,status=B,dt=cid.startswith('M-FKS-table'))
item('cert-arithmetic','candidate.md','48–66',T,'Replay commands, directed-Decimal arithmetic and exact finite integer data; no Lean/PV.',
     'All executed proof-bearing numerical cells, anchors and counts.',
     'Standard-library interval arithmetic actual implementation checked, including transcendental adjacent values and division sign. Zero exit status alone not substituted for interval/analytic cover.',
     code=(('bounds.py','8–59'),('finite_m.py','7–95'),('advance.py','75–88,98–116'),('repair.py','4–59')),
     ev=co+av+fi+rp+au,mathobj=False)

# Headline declarations are aliases (not independent proofs); retain their own exact identities.
headlines=[
  ('9–13',['R-last']),('14–16',['RA-181']),('17–18',['RA-'+str(i) for i in range(205,212)]),
  ('18–20',['RA-107']),('21–26',['MA-166']),('26–29',['R-strict-fine','M-strict-fine','R-strict-split','M-strict-split']),
  ('29–32',['M-split']),('32–33',['M-local-'+str(i) for i in range(75,79)]+['MA-signed-weight1','MA-signed-weight2','MA-signed-log1','MA-signed-log2']),
  ('35–40',['S-cut','S7','A-kernel']),('40–46',['S-cross','R-PT-anchor','M-FKS-repair','M-conversion'])]
# A claim row has exactly one recognized family identity. Preserve each
# shared obligation and its single evidentiary basis in both inventories.
shared_ids={c['claim_id'] for c in claims if c['family']==T}
claims=[dict(c,claim_id=c['claim_id']+suffix,family=fam,
             shared_obligation_id=c['claim_id']) if c['family']==T else c
        for c in claims
        for fam,suffix in ([(R,'-R'),(M,'-M')] if c['family']==T
                           else [(c['family'],'')])]
headlines=[(l,[alias for cid in cs
               for alias in ([cid+'-R',cid+'-M'] if cid in shared_ids else [cid])])
           for l,cs in headlines]
def all_sha():
    return {row[k]:row['sha256'] for row in idx['candidate_files'] for k in ('packet_name','original_name')}
families={}
for fam in (R,M):
    families[fam]=dict(strongest_supported_portfolio=[c['claim_id'] for c in claims if c['family']==fam and c['M_status'] in (P,B) and c['active_candidate_assertion']],
        rejected_or_incomplete_claims=[c['claim_id'] for c in claims if c['family']==fam and c['active_candidate_assertion'] and c['M_status'] in (X,G)],
        excluded_source_or_archived_defects=[c['claim_id'] for c in claims if c['family']==fam and not c['active_candidate_assertion']],
        remaining_assessment_work=[],
        summary=('Strict R1 tradeoff portfolio including deep/fine and split rows plus nested combined profile; exact B0 real sign at inherited finite integer trust.' if fam==R else
                 'Simultaneous M1 and density-free rays, exact local thresholds, refined signed and kernel options, repaired all-domain functional envelope.'))
receipts={}
for p in out.glob('*.stdout'):
    receipts[p.name]=hashlib.sha256(p.read_bytes()).hexdigest()
for p in out.glob('*.stderr'):
    receipts[p.name]=hashlib.sha256(p.read_bytes()).hexdigest()
a=dict(schema='FOLLOWUP_MATHEMATICAL_REVIEW_V1',candidate_id=idx['candidate_id'],
       assessment_complete=True,all_claims_inventoried=True,reviewed_source_hashes=all_sha(),source_bibliography=bib,
       exact_candidate_headline_aliases=[dict(written_source=anchor('candidate.md',l),claims=c) for l,c in headlines],
       assumptions={'B0':'Cumulative seven originals at their exact hypotheses and trust; no full RH.',
                    'B1':'B0 + FOLLOWUP-D02 PsiMajorant, all real x>=e^200; beta=27/32, coefficient 1/64 and log power 2.',
                    'D01':'Unavailable and not assessed.'},
       actual_effort_verification_commands=[
         '/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out /work/exact_c010',
         'cd /work/exact_c010; /usr/bin/python3.10 -B bounds.py all',
         'cd /work/exact_c010; /usr/bin/python3.10 -B finite_m.py',
         'cd /work/exact_c010; /usr/bin/python3.10 -B repair.py',
         'cd /work/exact_c010; /usr/bin/python3.10 -B advance.py certify',
         '/usr/bin/python3.10 -B /work/submission/audit.py /work/exact_c010',
         '/usr/bin/python3.10 -B /work/submission/pdf_layout.py'],
       observed_effort='Four exact candidate computation replays plus reviewer audits; compare source locators and analytic proof in review.md. No aggregate runtime/tokens claimed.',
       computation_receipts=receipts,status_receipt='status.txt',scope_and_commands='replay_instructions.md',
       family_assessments=families,claims=claims,
       source_trust_qualifications=['FKS Cor. 2.9 explicitly asserts published .77 Table 8; proof under printed Theorem 2.7 delta>=1 does not justify the table delta~.309. Strongest density rows supported only at the stated publication tier. Alternatives are individually assessed.',
                                    'PT 2021 finite integer statement retained at qualified original publication trust, independently checked only at local last failure; literal lower real ray counterexample excluded.',
                                    'Other published computations not independently repeated. No full RH, D01 or external source imported.'],
       no_other_arm_or_ranking_seen=True,new_core_math_salvage_performed=False,original_candidate_bytes_changed=False)
ids={c['claim_id'] for c in claims}
assert all(set(c)<=ids for _,c in headlines)
(out/'review.json').write_text(json.dumps(a,indent=2,ensure_ascii=False)+'\n')
status=dict(ready_for_review=True,families={fam:dict(status=P,claim_files=['review.md','review.json']) for fam in (R,M)},serious_attempts_documented=True)
(out/'STAGE_STATUS.json').write_text(json.dumps(status,indent=2)+'\n')
print(len(claims),len((out/'review.json').read_bytes()))
