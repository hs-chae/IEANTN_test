"""Build the review inventory from source identities, exact case tables and replay receipts.
Prior review supplies the transcribed own-claim index only. Status, comparison and evidence
fields are assigned here from the source audit, independent tests and review.md.
"""
import json, hashlib, re
from pathlib import Path
from collections import Counter
P=Path('/work/review-src')
T=Path('/task')
O=Path('/corpus/originals')
S=Path(__file__).resolve().parent
E=Path('/work/receipts')
def sha(raw): return hashlib.sha256(raw).hexdigest()
def enc(o): return json.dumps(o, ensure_ascii=False, separators=(',',':'))+'\n'
def save(n,o): (S/n).write_text(enc(o))
def fj(p): return json.loads(p.read_text())
index=fj(T/'CANDIDATE_INDEX.json')
idx={r['original_name']:r for r in index['candidate_files']}
assert (T/'INPUT_CONTRACT.json').read_bytes()==(P/'INPUT_CONTRACT.json').read_bytes()
for r in idx.values():
    assert sha((P/r['original_name']).read_bytes())==r['sha256']==sha((T/r['packet_name']).read_bytes())
sources=fj(T/'SOURCE_INDEX.json')['sources']
for r in sources:
    for k in ('pdf','text'):
        assert sha((O/r[k]).read_bytes())==r[k+'_sha256']
def loc(f,l,u=None):
    r=idx[f]; u=u or l
    assert 1<=l<=u<=len((P/f).read_bytes().split(b'\n'))
    return {'file':f,'physical_LF':l,'physical_LF_end':u,'sha256':r['sha256'],'packet_name':r['packet_name']}
match={
 'd02ram':'d02ram_results.txt','d02m':'d02m_results.txt','d02finite':'d02finite_results.txt',
 'd02secondary':'d02secondary_results.txt','endpoint_check':'d02endpoint_results.txt','finite26':'finite26.txt',
 'finite20b':'finite20b.txt','finite100m':'finite100m.txt','older24':'D01_M_REVIEW_older24.stdout',
 'exact24':'D01__SUBMITTED_008.txt','mertens_check':'mertens_results.txt','mertens_new':'mertens_replay.txt',
 'portfolio_check':'ram_replay.txt','portDus':'ram_dusart_replay.txt','portFree':'prefix_replay.txt',
 'mertDus':'mertens_dusart_replay.txt','audit_summaries':'summary_replay.txt',
}
contexts={
 'd02ram':'early [27.8,30.8], K and K-tail cells, both count arguments/shifted domain, direct-A [58,222] and tail, higher orders k=3..36',
 'd02m':'finite bridges and q/c starts, old-shape and power reweighting, tail at 167.656, comparison and primorial',
 'd02finite':'[300000,250000000], rate=1000000, e^(L/8) guard by 75000000',
 'd02secondary':'three theta caps and correlated short-interval tail from L=100000',
 'endpoint_check':'N,N+1 with both floor count arguments, bracket and derivative',
 'portfolio_check':'D01 closed log cells and starts in LF109–166; B0 cutoff/derived assumption, transition, polynomial and shift',
 'mertens_new':'D01 signed interval start checks LF76–134 and whole-ray joins as in review',
 'finite26':'[300000,195729609429], rate=50000',
 'finite20b':'[300000,20000000000], rate=200000',
 'finite100m':'[300000,100000000], rate=1000000',
 'older24':'[300000,3584912847], rate=50000',
 'exact24':'[300000,26489122130], rate=50000',
 'mertens_check':'[10000,100000000] plus exact benchmark unit cells and constant-tail arithmetic',
 'portFree':'D01 Ramanujan prefix through L=180, no QRH',
 'extra_check':'R [169,753], [2840,infinity), [37.5,39.45]; original own D02 oscillatory Mertens .24 calculation',
 'ray_check':'own prior spectral and/or R (as called by main) and QRH-free Mertens guard, source joins',
 'panel_audit':'lawful panel restriction, every original D02 endpoint, finite regular and shifted R cells, original B0 and D02 integer log starts',
 'ancillary_final':'lawful panel, exact counterexamples, corrected elementary log remainder, second shift complete on original cells/tail, no-density/old parts and matched comparisons',
 'audit_summaries':'finite band joins and benchmark coefficients',
 'refine':'old first-panel spectral and shifted certificates, gamma, refined M and correlated short intervals',
 'analytic_check':'old arithmetic replay only; invalid historical finite pi citation not restored',
}
receipts={}
for q in sorted(E.glob('*.status')):
    n=q.stem
    cmd=q.with_suffix('.cmd')
    if not cmd.exists() and n=='ancillary': command='PYTHONPATH=/work/firstpanel /usr/bin/python3.10 -B /work/submission/ancillary.py (earlier version, with written factor 2)'
    else: command=cmd.read_text().strip()
    out=q.with_suffix('.out').read_bytes(); err=q.with_suffix('.err').read_bytes()
    wd='/work/firstpanel' if n.endswith('First') or n in ('panel_audit','ancillary','ancillary_final') else '/work/review-src'
    receipts[n]={'command':command,'working_directory':wd,'coverage':contexts.get(n,contexts.get(n.removesuffix('First'),'as invoked in command/source')),'exit':int(q.read_text()),'stdout':out.decode(),'stderr':err.decode(),'stdout_sha256':sha(out),'stderr_sha256':sha(err)}
    if n in match:
        receipts[n].update(candidate_output=loc(match[n],1,len((P/match[n]).read_text().splitlines())),byte_match=out==(P/match[n]).read_bytes())
        assert receipts[n]['byte_match'],n
for n in ['d02ram','d02m','d02secondary','d02finite','finite26','finite20b','finite100m','older24','exact24','mertens_check','mertens_new','mertDus','portfolio_check','portDus','portFree','refine','analytic_check','ray_check','endpoint_check','secondary_check','extra_check','audit_summaries','panel_audit','ancillary_final','compile','compile_new','compile_older','compile_exact']:
    assert receipts[n]['exit']==0,n
for n in ['d02ramFirst','d02mFirst','d02secondaryFirst','ancillary']:
    assert receipts[n]['exit']==1,n
assert "([1.004798" in receipts['ancillary_final']['stdout']
save('evidence.json',{'schema':'C022_INDEPENDENT_REPLAY_V1','working_mode':'Non-login /bin/bash; offline; no original candidate bytes changed',
   'interpreter':'Python 3.10.12 /usr/bin/python3.10','compiler':'Ubuntu g++ 11.4.0 /usr/bin/g++ -O3 -std=c++17; assertions enabled',
   'restore_command':'/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out /work/review-src','source_hash_check':True,
   'panel_variant':{'replacement':'for tab in (old,new):  ->  for tab in (old,):','candidate_sha256':idx['d02screen.py']['sha256'],'variant_sha256':sha(Path('/work/firstpanel/d02screen.py').read_bytes())},
   'ordinary_resources':'quotient count, segmented C++ prime emission and compact interval prefixes/band summaries; Python single 10^8 byte flag sieve; no large regenerated dump retained',
   'first_failures':['initial ls command not present, readability verified by test and then shell glob/pathlib','/bin/cat unavailable, pathlib read all policy files','whole-script panel-deletion aborts and earlier ancillary factor-2 failure retained below'],
   'receipts':receipts,
   'executed_binary_hashes':{j:sha(Path('/work',j).read_bytes()) for j in ['reviewer_finite_opt','reviewer_d02finite','reviewer_exact24','reviewer_older24']}})
OK='supported_at_stated_trust_tier'
NO='incomplete_with_specific_missing_step'
FALSE='false_with_specific_counterexample'
WEAK='equivalent_or_weaker'
BASE='baseline_retained'
V='Written/replay tier; no Lean, Blueprint or source-first PV.'
trust='Pinned sources and ordinary arithmetic (details in review.md).'
C=[]
SC='FKS pp.4–8,26 Lemma 2.1, (2.1), Remark 2.2, Cor.2.3/Table 1, Cor.2.9/(2.17)/Table 8 first panel, Thm.3.2/(3.2); FKS Remark 1.5(2), p.3 for the .618 qualification; Dusart pp.5,12–13 Thm.2.3 and Cor.4.5; FiniteRH Thm.1 p.2.'
SM='CH2 Cor. B.2 and (B.9), pp.43,46, App. A pp.40–42; FKS Cor.1.4 p.2; Dusart Thms.5.6,5.7,5.9 pp.17–20.'
SR='PT2021 Thm.2 p.3, Cor.2 pp.2,8, Lemma 6 p.9, §5 pp.9–11; Dudek–Platt Thms.1.2–1.3 p.2; FiniteRH Cor.1 p.4 and §3.3 p.5; CH2 Cor.1.3 p.3, Lemma 9.2 pp.35–36; Dusart Thm.4.2 and Cor.4.5.'
MF='Dusart pp.11–13,17–20 Thm.4.2 (k=2, eta=.2), Cor.4.5, Thms.5.6–5.9; CH2 Cor.1.3/Lemma 9.2/Cor.9.3; FiniteRH Cor.1/§3.3; PT2021 p.8; FKS Cor.1.4 p.2.'
FKSgap='The locked min uses FKS .618 Table 8 panel. FKS Remark 1.5(2) p.3 treats that numerical input as announced, not established here. No lawful replacement at this target is supplied. '
D01BASE='B0 entails D01 exactly. Keep lawful matched-domain B0 minima.'
D02BASE='Compare to B0 = B0+D01, not to B0 without QRH. Named same-method comparison, not global optimality.'
def add(id,f,l,u,s,domain,fam,*,ass='B0 + D02',status=OK,strict='Strict numeric margin unless expressly non-strict.',base=D02BASE,src=SC,check='',gap='',r=(),code=(),keep=(),use=None,change='',data=None):
    written=loc(f,l,u)
    row=dict(claim_id=id,family=fam,written_source=written,exact_statement=s,assumptions=ass,full_domain=domain,strictness=strict,real_or_integer='Real with inclusive p≤x unless domain specifies integer.',
        baseline_comparison=base,source_locators=src,derivation_check=check or 'Derivation and whole-domain proof checks in review.md; executable formulas below.',
        numerical_obligations='Directed checks with continuous-domain guards; see review.md.',
        actual_verification_receipts=list(r),executable_readback=[loc(*c) for c in code],
        retained_valid_branches=list(keep),M_status=status,precise_gap_or_counterexample=gap,
        propagation={'input_used':use if use is not None else ('D02' if 'D02' in ass else 'none beyond B0'),
                     'where_it_changes_proof':change or ('Smaller 27/32 cap via Mellin; changes off-line term' if 'D02' in ass else 'No added premise used.'),
                     'matched_comparison':base},
        V_status=V,remaining_trust=trust)
    if data: row['supporting_data_source']=loc(*data)
    C.append(row)
    return row
# Independently checked inherited D01 target roster. Retain exact full-domain specifications,
# not old assessments. Rewrite source identities using current packet names for the same bytes.
old=fj(P/'D01_M_REVIEW_review.json')
targets=fj(P/'OWN_COMPLETE_D01_RECHECK_TARGET_INDEX.json')['validated_claim_ids_by_family']
target=set(targets['Mertens']+targets['Ramanujan'])
assert len(target)==644
def old_status(cid):
    if cid=='R.literal-source-edge': return FALSE
    if cid=='R.old-finite-pi': return NO
    if cid in {'Shared.PS','Shared.A1','R.old-margins','R.U-signed'}: return WEAK
    if cid.startswith('M.original') or cid=='R.original-rays': return BASE
    return OK
def old_receipts(cid,f):
    if cid.startswith(('M.threshold','M.band')):
        return [dict(zip(['finite100m.txt','finite20b.txt','finite26.txt','D01__SUBMITTED_008.txt'],['finite100m','finite20b','finite26','exact24']))[f],'mertens_new','audit_summaries']
    if cid.startswith('M.Python-row') or cid.startswith('M.sharp') or cid=='M.Python-mechanism': return ['mertens_check','ray_check','ancillary_final']
    if cid.startswith('R.U-'): return ['portFree','extra_check','ancillary_final']
    if cid.startswith('R.') and ('sign' in cid or cid in {'R.real-cell','R.literal-source-edge'}): return ['endpoint_check','count','ancillary_final','portfolio_check']
    if f in ('historical_d01_refined.md','secondary.md') or cid.startswith(('M.secondary','M.prior')): return ['refine','secondary_check','ancillary_final']
    if cid.startswith(('R.','Shared.')): return ['portfolio_check','portDus','portFree','refine','analytic_check']
    return ['mertens_new','mertDus','ray_check','finite100m','finite20b','finite26','mertens_check','audit_summaries']
diag=0
# Test each printed band/threshold/finite Python data row exactly, independently of the old registry labels.
for o in old['claims']:
    cid=o['claim_id']; f=o['written_source']['file']; a=o['written_source']['physical_LF']; z=o['written_source'].get('physical_LF_end',a)
    assert o['written_source']['sha256']==idx[f]['sha256']
    status=old_status(cid); check='Source, formula, and domain checked; see review.md.'
    gap=''
    if cid.startswith('M.threshold.'):
        m=re.fullmatch(r'M.threshold.(.*)\.(\d+)\.(P,Q|S|V)',cid); assert m
        name,k,col=m.groups(); k=int(k); j=('P,Q','S','V').index(col)
        ln=(P/f).read_text().splitlines()[a-1]; kk,v=ln.split(':'); ends=list(map(int,v.split())); end=ends[j]
        assert int(kk)==k and name==f and str(end) in o['exact_statement']
        diagnostic=(f=='D01__SUBMITTED_008.txt' and k<9) or (f=='finite100m.txt' and (k<6 or k==6 and col=='V'))
        if diagnostic:
            diag+=1;status=WEAK
            check='Replayed exact last-failed endpoint. Retain at finite/comparator scope only under that tape convention. Do not infer a whole-ray proof from this row alone; failure at terminal does not certify a terminal point.'
        else: check='Exact last-failed endpoint replay; the appropriate separately verified finite bands and analytic continuation cover the ray.'
    if cid.startswith('M.band.'):
        ln=(P/f).read_text().splitlines()[a-1]
        ab,v=ln.split(' : '); assert all(s in o['exact_statement'] for s in v.split())
        rj=old_receipts(cid,f)[0]; assert receipts[rj]['stdout'].splitlines()[a-1]==ln
        check='Replayed exact three scaled ceilings; monotone prefix/cell enclosure covers every real point, with the written right-boundary convention.'
    if cid.startswith('M.Python-row.'):
        _,_,j,k=cid.split('.'); j=int(j);k=int(k)
        ln=next(l for l in receipts['mertens_check']['stdout'].splitlines() if l.startswith(f'{j} [('))
        assert re.search(r'\('+str(k)+r', (\d+)\)',ln).group(1) in o['full_domain']
        check='All exact endpoint guards and the independent .125/.135 analytic continuation checked.'
    if cid=='R.literal-source-edge': gap='Archival quoted proposition, explicitly not used: x=38358837682.1 gives R between −8100000 and −7900000.'
    if cid=='R.old-finite-pi': gap='Archival normalized pi bound not implied by FiniteRH Cor.1 (printed log squared in unnormalized estimate) or full-RH Dudek–Platt Thm.3.1 without full RH. Repaired theta-normalized estimates stand.'
    if cid=='M.withdrawn299999':
        status=OK; check='SUPPORTED REFUTATION, not a positive upper bound. At 912560 the positive scaled error is in (.2999993,.2999995), disproving the archived .299999 trial.'
    if cid=='M.old-margins': status=WEAK
    ass=o['assumptions']
    for phrase in ('current stage','D02 unavailable'):
        if phrase in ass: ass=ass.replace(phrase,'historical D01 stage')
    rr=add(cid,f,a,z,o['exact_statement'],o['full_domain'],o['family'],ass=ass,status=status,strict=o['strictness'],base=D01BASE,src=o['source_locators'],check=check,gap=gap,r=old_receipts(cid,f),code=[(v['file'],v['physical_LF'],v.get('physical_LF_end',v['physical_LF'])) for v in o.get('executable_readback',[])],use='none; D01 optional wherever equivalent')
    rr['scope']='D01 retained source object' if cid in target else 'Archival excluded source assertion'
assert diag==40
assert sum(z["M_status"]==WEAK for z in C)==44
assert len(C)==646 and {r['claim_id'] for r in C}==target|{'R.literal-source-edge','R.old-finite-pi'}
# New shared dependencies and separately asserted scalar/certificate readbacks.
R='Ramanujan'; M='Mertens'; d='D02.md'; rr='D02_R.md'; mm='D02_M.md'; sec='D02_secondary.md'
sc=[('d02screen.py',31,86)]
cr=[('d02ram.py',33,104),('d02ram.py',107,195)]
cm=[('d02m.py',7,42),('d02m.py',61,117),('d02m.py',157,187)]
poly='G(L)=L^6 e^(-2L)R(e^L); a_n=Σ binom(n,j)j! − Σ j!(n−j)!. '
for fam in (R,M):
    suf=fam[0]
    add('D02.strip.'+suf,d,49,67,'D02 implies beta≤27/32 by Mellin continuation; no exclusion of the boundary.', 'All nontrivial zeta zeros, using actual input only on x≥e^200.',fam,strict='closed cap',src='OpenAIQRH Thm.1.1 p.4 (B0 comparison); CH2 App.A/B; FKS §2',r=('d02screen',),change='Analytic continuation of the centered Mellin transform uses D02 only above e^200.')
    add('D02.two-panel.'+suf,d,69,88,'Density screen minimizing over both FKS Table 8 panels and Dusart.', 'T≥H and s in written bins up to 27/32 or B0 cap',fam,status=NO,gap=FKSgap,r=('d02screen','d02screenFirst','panel_audit'),code=sc,keep=('D02.legal-screen.'+suf,'D02.terminal.'+suf))
    add('D02.legal-screen.'+suf,d,90,185,'Jensen reciprocal moment m=1,2, final Dusart convex chord, decreasing C from 155 and |e_psi|≤C(L)e^(-aL); theta add 3e^(-L/2). Legal branches use first panel plus Dusart or Dusart alone.', 'L≥155 (moment majorants themselves valid on their stated bins)',fam,strict='non-strict envelope',r=('d02screen','d02screenFirst','panel_audit'),code=sc)
    add('D02.terminal.'+suf,d,137,141,'Limits w_b<.116297 (m=1) and <2.506e-14 (m=2); B0 comparator terminal >.00666.', 'L→∞, at D02 and B0 caps respectively.',fam,r=('d02screenFirst','panel_audit'),code=sc)
    add('D02.reciprocal.'+suf,d,145,169,'FKS admissible truncated signed formula and total/right-off-line reciprocal bounds y²/6+3, (y²−h²)/12+.1.', 'L≥155 at c*=.35; as specified for other admissible cutoffs.',fam,strict='non-strict bounds; original cutoff constraints strict',r=('d02screenFirst',),code=[('d02screen.py',93,110)],use='none for the cutoff/mass inequalities themselves')
    add('D02.triangle.'+suf,d,194,206,'Density-free FKS curve with c*=.19; normalized error <.0034 L² e^(-a L).', 'L≥155',fam,r=('d02screenFirst',),code=[('d02screen.py',88,107)])
    add('D02.at168.'+suf,d,186,188,'New unsmoothed normalized psi allowance below CH2 A0 at 168 and later.', 'L≥168',fam,r=('panel_audit',),code=sc)
    add('D02.at200.'+suf,d,189,192,'Screen scalar C(200)<.213 (hence decreasing cap).', 'L≥200 for a fixed coefficient',fam,status=NO,gap=FKSgap+'Legal C(200)≈.217831, so this sufficient test does not give .213; not a counterexample to a ψ bound.',r=('panel_audit',),code=sc,keep=('D02.at168.'+suf,'D02.legal-screen.'+suf))
    add('D02.primitives.'+suf,d,208,240,'Absolute J1,J2 envelopes with .04620 line, 2e^-L trivial contribution, off-line k e^-aL and k e^-aL/H; coarse no-density and QRH-free alternatives.', 'L≥18.42, refine k from 155, prefix at 20 uses coarse k.',fam,strict='non-strict envelope',src=SM+' '+SC,r=('d02screenFirst','secondary_check','ancillary_final'),code=[('d02m.py',7,13),('d02ram.py',37,43)])
Rold='B0 and B0+D01 same; any earlier prefix gained here uses even the non-QRH originals.'
add('D02.R.sign',rr,11,29,'Exact inherited open sign ray x>r, derivative/real-cell and QRH-free branches retained; no endpoint gain from A.', 'x>r, equality at r, integer x≥38358837683; derivative [r,N+1]',R,ass='B0; QRH-free pieces separately',status=BASE,base=Rold,src=SR,r=('endpoint_check','ancillary_final','portfolio_check'),code=[('endpoint_check.py',25,65)],keep=('R.real-cell','R.U-connected'))
for i,(x,m) in enumerate([('27.8','.01'),('27.95','.10'),('28.24','.25'),('28.77','.50'),('29.60','.80'),('30.45','1')],39):
    add('D02.R.early'+x,rr,i,i,'G(L)>'+m,'real L≥'+x,R,ass='B0, new compact extension independent of QRH',base=Rold,src=SR+' '+SM,r=('d02ram','d02ramFirst','portFree','portfolio_check'),code=[('d02ram.py',61,97),('d02ram.py',141,151)])
for i,(x,k) in enumerate([(49,65),(49.5,83),(169.2,90),(173,110),(178,130),(183,140),(185.5,145)],56):
    add('D02.R.K'+str(k),rr,i,i,f'G(L)>1+14/L+{k}/L²',f'real L≥{x}',R,base=f'{D02BASE} Old K=22 from 49, old whole-ray K=145 from 219; preserve bounded K=90 on [50,164].',src=SR+' '+SC,r=('d02ram','panel_audit'),code=cr,keep=('R.bounded90','R.m49'))
add('D02.R.raw',rr,71,75,'G(L)>1+12.5/L without density or inferred strip.', 'real L≥49; early closed cells then CH2 through 222, A-tail uses L and L−1',R,base='Old no-density 1+3/L from 50; retains weaker premise (no A needed over B0).',src=SR,r=('d02ram','panel_audit'),code=cr,change='Direct A in anchored psi-to-theta-to-pi transfer for t≥200; both arguments meet it on L≥222.')
rline={}
for i,ln in enumerate((P/rr).read_text().splitlines(),1):
    if re.match(r'^\|\d+\|',ln) and 91<=i<=108:rline[int(ln.split('|')[1])]=i
for i,ln in enumerate((P/'d02ram_results.txt').read_text().splitlines(),1):
    if 'fraction of next coefficient left:' not in ln: continue
    k,N,x,y=map(int,ln.split()[:4]); l=rline.get(k,110); data=('d02ram_results.txt',i,i)
    fail=k==7
    hdr=poly+f'G(L)>Σ_(j=0..{k-1}) a_(4+j)/L^j.'
    add(f'D02.R.poly{k}',rr,l,l,hdr,f'real L≥{x}',R,status=NO if fail else OK,base=f'B0 same certificate sufficient at L≥{y}; matched B0 sufficient test fails at {x}.',src=SR+' '+SC,r=('d02ram','panel_audit'),code=cr,data=data,
        gap=(FKSgap+'Legal same-test reserve near −117624 at L=287 for k=7, N=17; supply positive reserve there and decreasing tail, or prove separate bridge.') if fail else '',
        keep=('R.poly7','D02.R.poly8') if fail else ())
    add(f'D02.R.B0poly{k}',rr,l,l,hdr+' B0 same-test comparator.',f'real L≥{y}',R,ass='B0',base=D01BASE,src=SR+' '+SC,r=('panel_audit',),code=cr,data=data,check=f'Admissible screen same-method reserve positive at {y}, negative at predecessor {y-1}; also negative at matched D02 start {x} with named compact alternatives. Not a negative value of G.')
add('D02.R.uniform32',rr,122,124,poly+'G strictly above order n−4 polynomial for integer n≥6, L≥32n.', 'real L≥32n, n≥6',R,src=SR+' '+SC,r=('d02ram','ancillary_final'),code=cr,check='Uniform factorial reserve, count cap at actual smallest shifted argument 191 not the unsupported .24 from 180.')
add('D02.R.uniformc',rr,124,129,poly+'G strictly above order n−4 polynomial for integer n≥20, L≥27.6443 n−4 log n−2.', 'real L≥27.6443n−4log n−2, n≥20',R,src=SR+' '+SC,r=('d02ram','ancillary_final'),code=cr)
add('D02.R.shift68',rr,131,135,'y=(x/e)[1−(1+13/L+68/L²)/L^4]; exπ(y)/L−π(x)^2 > x²/L^8.', 'real L≥58',R,status=NO,gap=FKSgap+'Same-parameter lawful sufficient reserve 0.5913774 on [167,172], target >1. Need shifted count reserve on the uncovered transition (only [58,167] and [172,infinity) certified by these checks).',src=SR+' '+SC,r=('d02ram','d02ramFirst','panel_audit'),code=cr,keep=('D02.R.shift68.pieces','D02.R.shift12','R.stability'))
add('D02.R.shift68.pieces',rr,131,135,'Same first-shift inequality on its independently passing bounded and tail pieces.', 'real 58≤L≤167 or L≥172',R,src=SR+' '+SC,r=('panel_audit',),code=cr)
add('D02.R.shift12',rr,136,142,'y=(x/e)[1−(1+12/L)/L^4]; exπ(y)/L−π(x)^2 > (1+69/L)x²/L^7.', 'real L≥58',R,base='Improves B0 .19 in identical shift and units; direct separate cost readback on the same cells.',src=SR+' '+SC,r=('d02ram','ancillary_final','panel_audit'),code=cr)
add('D02.R.shift-obstruction',rr,143,147,'Within s=(1+alpha/L+beta/L²)/L^4, eventual strict positivity precluded if alpha>13 or alpha=13 and beta>131.', 'Fixed real alpha,beta; large real L',R,ass='B0 sufficient',src=SR+' '+SC,code=cr)
for id,l,u,s,domain,inp in [
 ('PV',151,163,'PV centered count formula with exact constant 2/log2−li(2).','x≥2 when used',False),
 ('spectral-pi',165,190,'Add D2 and smoothed CH2 residual exactly as written, with legal C; valid at each applicable argument.','t≥155 for D2 and ≥58 for CH2 boundary plus h_s',True),
 ('direct-pi',192,200,'Direct A count guard D_raw(t) with 7e-15 anchor at 200.','t≥200',True),
 ('one-sided-pi',202,233,'New lower sign guard D_low^- and upper sign 3t e^-t from theta sign.','20≤t≤29.9 lower; applicable t with 2≤e^t≤10^19 upper',False),
 ('two-sided-G',235,245,'Exact F gap envelope with signed pi bounds, clipped lower squaring for upper formula; all fixed asymptotic orders.','both log arguments in selected domains',True),
 ('remainder',261,281,'Bracket F by P_N−f_N e^(1−t) and P_N+d_N with both remainder options.','integer N≥17 in finite certificates, t>N+1; general factorial proof also for arbitrary orders used',False),
 ('tail',283,333,'Coefficient expansion, omitted square/π loss and closed-cell/L^N monotone tail certificates.','each finite cell and tail on its stated domain',False),
 ('dominance',246,257,'Legal D2 improves named shaped B0 count comparator after t=175, both arguments from L=176.','real t≥175 or real L≥176 as appropriate',True)]:
    add('D02.R.'+id,rr,l,u,s,domain,R,ass='B0 + D02' if inp else 'B0, source-independent calculus where appropriate',src=SR+' '+SC+' '+SM,r=('d02ram','panel_audit','ancillary_final'),code=cr)
for L in [175,180]:
    add(f'D02.R.cap24-{L}',rr,248 if L==175 else 377,251 if L==175 else 382,f'Scalar certificate D2(t)<.24e^(-at) from t={L}.',f't≥{L}',R,status=NO,gap=FKSgap+'Legal screen starts higher. Dominance and order results checked with actual domains in ancillary.py.',r=('panel_audit','ancillary_final'),code=cr,keep=('D02.R.dominance','D02.R.uniform32'))

# Mertens quantitative and analytic rows.
eb='E(x)=max(L|e^-δ_Q−1|, L|e^δ_Q−1|, L|δ_S|, |δ_V|). '
jmsg='Legal convex/monotone bridge uses the same join T=167.656. '
oldshape='B0/D01 named 1/8 envelope has larger coefficient (terminal budget >.00666), not a statement about the actual errors.'
for l,ex,k in [(30,'1/8','.001324'),(31,'9/64','.018165'),(32,'5/32','.249412')]:
    start=180364618 if l==30 else 300000
    cap={30:'.00137881622',31:'.01893193765',32:'.25994636433'}[l]
    add(f'D02.M.common.{ex}',mm,l,l,eb+f'E<{k} x^(-{ex}).',f'real x≥{start}',M,status=NO,gap=FKSgap+jmsg+f'Outgoing bridge test is {cap}, above target. Need admissible continuation beyond the passing bounded cells.',src=SC+' '+MF,r=('d02m','d02finite','panel_audit'),code=cm,keep=(f'D02.M.common.{ex}.finite','D02.M.limit','D02.M.dusart168','D02.M.oldshape.1400.P'))
    add(f'D02.M.common.{ex}.finite',mm,l,l,eb+f'Bounded restriction E<{k} x^(-{ex}).',f'real {start}≤x≤e^59.5',M,ass='B0, no QRH required on these checked portions',src=MF,r=('d02m','d02finite','finite26','finite20b'),code=cm)
powrows=[('1324','179901131','179901131','180364618'),('1325','179900952','179900952','180364438'),('1330','179847789','179847789','180364258'),('1340','179845462','179845462','180361738'),('1350','113370673','113370673','180223498'),('1400','113194280','113194280','179847789'),('1500','110216458','110216788','113190325')]
d02tape=(P/'d02finite_results.txt').read_text().splitlines()
for l,(n,*xs) in enumerate(powrows,43):
    dl=next(i for i,s in enumerate(d02tape,1) if re.match(n+' ',s))
    assert list(map(int,d02tape[dl-1].split(':')[1].split()))==list(map(int,xs))
    for j,(col,x) in enumerate(zip(('P','S','V'),xs)):
        err=['maximum of the two relative product errors','absolute reciprocal sum error','absolute weighted sum error'][j]
        norm='/L' if j<2 else ''
        target=f'{err} < {n}/10^6 ⋅x^(-1/8){norm}.'
        ok=int(n)>=1400
        pid=f'D02.M.oldshape.{n}.{col}'
        add(pid,mm,l,l,target,f'real x≥{x}',M,status=OK if ok else NO,base=oldshape,src=SC+' '+MF,gap='' if ok else FKSgap+jmsg+'Lawful common sufficient upper cap ~.00137881622 exceeds target; no separate valid tail for this component supplied.',
            r=('d02finite','finite20b','d02m','panel_audit','ancillary_final'),code=cm+[('d02finite.cpp',204,229)],data=('d02finite_results.txt',dl,dl),keep=(pid+'.bounded',))
        add(pid+'.bounded',mm,l,l,target,f'real {x}≤x≤e^59.5',M,ass='B0; no QRH needed',base='Finite computation and low analytic certificate are independent of the new input.',src=MF,
            r=('d02finite','finite20b','d02m'),code=cm+[('d02finite.cpp',204,229)],data=('d02finite_results.txt',dl,dl))
add('D02.M.1323',mm,51,54,eb+'E<.001323 x^(-1/8), advertised from e^59.5 and 250000000.', 'real x≥250000000',M,status=NO,base=oldshape,src=SC+' '+MF,gap=FKSgap+jmsg+'Lawful tail test ~.00137881622. Outgoing finite bands/cells through e^59.5 still pass .001323.',r=('d02m','finite20b','panel_audit'),code=cm,keep=('D02.M.1323.compact','D02.M.oldshape.1400.P'))
add('D02.M.1323.compact',mm,51,54,eb+'E<.001323 x^(-1/8) on outgoing finite/analytic piece.', 'real 250000000≤x≤e^59.5',M,ass='B0 without QRH',src=MF,r=('d02m','finite20b'),code=cm)
for l,(L,k) in enumerate([(168,'.248838'),(170,'.245767'),(175,'.238698'),(180,'.232384'),(190,'.221577'),(200,'.212654'),(225,'.195899'),(250,'.184171'),(300,'.168790'),(400,'.152502'),(600,'.138777'),(1000,'.129304')],60):
    sval=next(s.split(' [',1)[1].split(',')[0] for s in receipts['panel_audit']['stdout'].splitlines() if s.startswith(f'M power {L} ['))
    add(f'D02.M.power{L}',mm,l,l,eb+f'E<{k} x^(-5/32).',f'real L≥{L}',M,status=NO if L!=1000 else OK,
        gap=(FKSgap+f'Admissible same-screen normalized envelope at start {L} is approximately {sval}; need proof of the stated constant on the whole ray.') if L!=1000 else '',src=SC+' '+SM,
        r=('d02m','panel_audit'),code=cm,keep=('D02.M.dusart168','D02.M.power1000','D02.M.limit') if L!=1000 else ())
for L,k in [(168,'.261492'),(175,'.249146'),(180,'.241556'),(200,'.218341'),(250,'.186256')]:
    add(f'D02.M.dusart{L}',mm,74,77,eb+f'E<{k} x^(-5/32) with Dusart density only.',f'real L≥{L}',M,ass='B0 + D02; no FKS Table 8 (uses FKS signed formula)',src=SC+' '+SM,r=('d02m','panel_audit'),code=cm,base='At L≥175 dominates named old 1/8 comparator; at 200 beats prior D02 .24 and B0 .01233 after rate comparison.')
add('D02.M.limit',mm,73,74,eb+'limsup x^(5/32) E(x)<.116297.', 'real x→infinity',M,src=SC+' '+SM,r=('d02screenFirst','panel_audit'),code=cm+sc,check='Terminal allowance from Dusart; on legal combined curve residual primitive divided by L tends to zero. Absolute product linearization.')
for l,L,q,c,cap in [
 (90,'59.5',2,'5.30e-8','5.29329381e-8'),(91,'60.98',2,'2.944e-8','3.0678571e-8'),(92,'59.5',3,'4.935e-6','5.14344651e-6'),
 (93,'59.5',4,'.0008274','.000862329667'),(94,'59.5',5,'.13872','.144574743'),(95,'59.5',6,'23.257','24.2388231')]:
    ok=l==90
    add(f'D02.M.q{q}.{L}',mm,l,l,eb+f'E<{c}/L^{q}.',f'real L≥{L}',M,status=OK if ok else NO,
        ass='B0 (CH2 to 188 then inherited screen)' if ok else 'B0 + D02',
        base='5.30e-8 is independent of A and improves the older coarse 2e-7 branch.' if ok else 'B0 named CH2/spectral budget at 184 and fixed-q comparison, not optimality.',
        gap='' if ok else FKSgap+jmsg+f'Admissible outgoing/bridge value {cap} above the target. Need valid upper allowance through the transition.',
        src=SC+' '+SM+' '+MF,r=('d02m','panel_audit','mertens_new'),code=cm,keep=('D02.M.q2.59.5','D02.M.dusart168') if not ok else ())
add('D02.M.log-scaling',mm,97,105,'For q≥0, q≤aL0, coefficient Z(L0)L0^q e^(-aL0) in E≤c/L^q, using legal Z; corresponding mixed shapes pointwise.', 'L≥L0≥155; use the given derivative condition',M,strict='non-strict coefficient from formula',r=('panel_audit',),code=cm)
add('D02.M.sharp',mm,107,122,'Retains P/Q, S, V sharp benchmark roots, non-strict closed rays, and refutation of .299999 at 912560.', 'As in M.sharp-products, M.sharp-reciprocal-sum, M.sharp-weighted',M,ass='B0; original finite and constant-tail inputs',status=BASE,strict='non-strict at root; strict failures immediately below',base=D01BASE,src=MF,r=('mertens_check','ancillary_final'),code=[('mertens_check.py',167,231)],keep=('M.withdrawn299999',))
for ident,l,u,s,domain,inp in [
 ('normal',3,20,'Exact relative normalization of P,Q and both sums with Dusart M,B3.','L>0 whenever factor defined; proof-bearing branch ranges as separately stated',False),
 ('exact-Abel',124,145,'Exact normalized ψ and θ summation identities with omitted distinct powers and τ.', 'All applicable x≥2, including prime-power jumps',False),
 ('prim-tail',147,163,'Kj+2|K′|j_2 by two partial integrations; D02 improvement of old smoothed allowance.', 'L≥18.42',True),
 ('signed',165,181,'Separate signed intervals for δ_V,δ_S,δ_Q and exponentiated P,Q. Retain exact known boundary and lawful minima.', 'L≥18.42, new unsmoothed entry from 155 and raw A from 200',True),
 ('corrections',183,219,'Optional prime-power and τ brackets by partial summation at each root, elementary remaining tail k≥4.', 'L≥18.42 and only use d(y) on its source domain at the required root y',False),
 ('joint-Z',223,265,'Common combined-pole bound E≤e^-aL Z with legal C and moments, including conversion.', 'L≥155',True),
 ('bridge-method',267,301,'Convex finite CH2 bridge, then scaled monotone Z tail; proof for targets whose numerical tests pass.', 'Closed written bridges and corresponding outgoing rays',True),
 ('finite-joins',302,341,'Finite replay and outgoing lower joined cells cover passing reweighted target portions.', 'Through respective [300000,10^8], [75000000,250000000], [250000000,20B] and cells to e^59.5',False),
 ('comparators',353,404,'Named B0 envelope and matched-domain power/log crossovers; D02 legal bound dominates named B0 after 175.', 'Matched domains; L≥175 for the eventual dominance',True),
 ('boundary',406,434,'Leading possible boundary-zero terms and reverse-Abel/Mellin obstruction to little-o, not existence.', 'real x→∞, indicated rate and log factors',True)]:
    add('D02.M.'+ident,mm,l,u,s,domain,M,ass='B0 + D02' if inp else 'B0 and elementary analysis/interval arithmetic',src=MF+' '+SM+' '+SC,r=('d02m','panel_audit','ancillary_final'),code=cm,check='Derivation and exact domain convention checked; see Mertens section of review.md. Legal-input restriction where the screen occurs.')
add('D02.M.cap239',mm,366,373,'Scalar common-envelope cap .239 e^-aL from 175.', 'real L≥175',M,status=NO,gap=FKSgap+'Legal combined scaled test ≈.24758963 at 175. Actual comparison remains via the separately stated Dusart-only .249146.',r=('panel_audit','ancillary_final'),code=cm,keep=('D02.M.comparators','D02.M.dusart175'))
# Each new tape band and each k/100 column (never extrapolate a last failure).
term=250000000
for l,s in enumerate(d02tape,1):
    if s.startswith('['):
        ab,v=s.split(' : '); x,y=map(int,ab[1:-1].split(','))
        add(f'D02.M.band{l}','d02finite_results.txt',l,l,'Exact band ceilings '+v+' in 10^-9 units, scaling L³ for P,Q,S and L² for V.',f'real [{x},{y}'+(']' if y==term else ')'),M,ass='B0; finite integer sieve only with Dusart-tail constants',strict='non-strict reported rounded ceiling',src=MF,r=('d02finite',),code=[('d02finite.cpp',108,254)])
    if re.match(r'^\d{1,2} :',s):
        k,v=s.split(':'); k=int(k)
        for col,x in zip(('P,Q','S','V'),map(int,v.split())):
            ray=k>=4
            dom=f'real x≥{x}' if ray else ('real x in ['+str(x)+',250000000]' if x!=term else 'diagnostic; terminal failure, no passing suffix certified')
            add(f'D02.M.threshold{k}.{col}','d02finite_results.txt',l,l,f'{col}: k/100={k}/100 in old logarithmic scaling; last failed right endpoint {x}.',dom,M,ass='B0, no QRH',status=OK if ray else WEAK,strict='strict on passing subinterval, not a falsity statement on failed cells',src=MF,r=('d02finite','d02m','finite20b','mertens_new'),code=[('d02finite.cpp',204,254),('d02m.py',109,117)],check='Threshold row continued by finite20b and .0077 only where the ray is claimed; other rows record diagnostics or bounded domains.')
# D02 secondary applications (tracked separately from the two primary target scores).
add('D02.M.primorial',sec,8,44,'Specified primorial n_x relative error <6e-13 x^-a/L.', 'real L≥155',M,src=SC+' '+SM,r=('d02m','panel_audit','ancillary_final'),code=[('d02m.py',144,155)],
     check='Locked .25 theta checkpoint unavailable (legal C≈.259946 at T); using its factor 2 is insufficient. Ancillary elementary logarithm-remainder tightening to w²/L at the actual small |w| and legal .26 gives 3.3719e-13; no changed analytic core or new search.')
add('D02.M.primorial-limsup',sec,13,15,'Limsup of L x^a times specified primorial relative error <2.506e-14.', 'real x→∞',M,src=SC+' '+SM,r=('d02screenFirst','ancillary_final'),code=[('d02m.py',144,155)],check='Follows from the legal reciprocal-square terminal bound; other terms vanish.')
add('D02.M.extremum',sec,47,70,'e^-γ max_(1≤n≤N,n integer) n/φ(n) differs from log log N by <.4982(log N)^-a, and corresponding sigma/n upper bound.', 'real loglog N≥169',M,status=NO,
    gap=FKSgap+'The .249 theta and Q caps at 168 used to bracket the extremum are not certified (legal C≈.259316). Need caps adequate for the stated bracket and relative-to-additive conversion.',src=SC+' '+SM,r=('d02secondary','d02secondaryFirst','panel_audit'),code=[('d02secondary.py',9,19)],keep=('M.secondary-max',))
for l,L,c,g,t in [(74,168,'.249','.499','.000999'),(75,180,'.232384','.465','.00023'),(76,200,'.212654','.426','.00069')]:
    add(f'D02.M.interval{L}',sec,l,l,f'For y=x+{g}x^b, π(y)−π(x)>{t}x^b/log y.',f'real L≥{L}',M,status=NO,
        gap=FKSgap+f'Theta cap {c} at {L} fails with licensed screen; endpoint subtraction cannot supply positive reserve with those guards.',r=('d02secondary','d02secondaryFirst','panel_audit'),code=[('d02secondary.py',9,14)],keep=('M.secondary-interval','D02.M.interval-correlated'))
add('D02.M.interval-correlated',sec,89,187,'g=x^(5/8)L^(207/20), π(x+g)−π(x)>.81g/log(x+g).', 'real L≥100000',M,src=SC,r=('d02secondary','d02screenFirst'),code=[('d02secondary.py',20,35)],base='Improves B0 log exponent 14 at the same onset and relative count factor, not absolute counts across different lengths.',
    check='Uses only first-panel upper constants 12,6, and D02 cap in the layer integral; exact start loss <.187620 with monotone tail.')
# Historical comparisons cited in D02: preserve their narrower provenance and actual formulas.
for ident,f,l,u,s,dom,fam,receipt in [
 ('A-screen','historical_d02_candidate.md',51,123,'Prior Dusart-only curve d_A and theta/count transfers; .232 cap at 200, limiting upper .119.','L≥160 (psi), L≥200 for .232; anchored theta/count transfers on stated domains.',R,'ray_check'),
 ('A-gaps','historical_d02_candidate.md',178,188,'Prior |π−Li2| pointwise profile; strict .01 at 39.75 and 1+14/L+60/L² at 50, using exact A where needed.', 'L≥39.75 or ≥50 respectively, QRH-free bounded pieces independently retained',R,'ray_check'),
 ('M24','historical_d02_extensions.md',112,185,'Earlier signed θ-boundary oscillatory tail; common .24 x^(-5/32) bound in E and pointwise limiting coefficient .119+2.51e-14.', 'L≥200',M,'extra_check'),
 ('primorial','historical_d02_extensions.md',187,210,'Old specified primorial magnitude ≤.0069 x^-a/L and limsup ≤2.51e-14.', 'L≥200 for magnitude',M,'extra_check'),
 ('interval','historical_d02_extensions.md',212,226,'Older .465 x^b short interval at L≥200 with >.000999 x^b/(L+.1) count; general unsigned length and eventual (0.238+eta) length.', 'L≥200, eta>0 for eventual length',M,'extra_check')]:
    add('OwnD02.old.'+ident,f,l,u,s,dom,fam,ass='B0 + D02; own archived comparison and indicated valid branch',src=SC+' '+SM+' '+SR,r=(receipt,'d02m','ancillary_final'),status=WEAK if ident!='interval' else OK,
        code=[('ray_check.py',63,143)] if fam==R else [('extra_check.py',69,101)],check='Historical presentation checked against actual ordinary replay and analytic domain. Preserve the proved overlapping results, not earlier verdicts.')
ptrs={r['claim_id'] for r in C}
assert len(ptrs)==len(C)
assert all(set(r['retained_valid_branches'])<=ptrs for r in C)
assert all(set(r['actual_verification_receipts'])<=receipts.keys() for r in C)
fam={}
for kind in (R,M):
    cs=[r for r in C if r['family']==kind or kind==R and r['claim_id'].startswith('Shared.')]
    fam[kind]={'strongest_supported_portfolio':[r['claim_id'] for r in cs if r['M_status'] in (OK,BASE)],
               'rejected_or_incomplete_claims':[r['claim_id'] for r in cs if r['M_status'] in (NO,FALSE)],
               'remaining_assessment_work':[],
               'summary':('Mixed verdict; retain D01, lawful D02 K rays to 145, second shifted profile, all arbitrarily high orders and tested integer-profile rows except k=7 at 287; first shift transition incomplete.' if kind==R else
                 'Mixed verdict; preserve B0/D01 floor and finite tape, legal signed and combined curves, .116297 limsup, Dusart-only D02 table, .129304 from 1000 and earlier .001400/.001500 rays. Stronger numeric transitions and tight constants fail their legal proof requirements.')}
review={'schema':'FOLLOWUP_MATHEMATICAL_REVIEW_V1','candidate_id':index['candidate_id'],'assessment_complete':True,'all_claims_inventoried':True,
    'reviewed_source_hashes':{r['original_name']:r['sha256'] for r in idx.values()}|{r[k]:r[k+'_sha256'] for r in sources for k in ('pdf','text')},
    'source_bibliography':sources,'actual_effort_and_verification_commands':{'evidence':'evidence.json','replay':'replay.sh','commands':{n:r['command'] for n,r in receipts.items()}},
    'family_assessments':fam,'claims':C,'no_other_arm_or_ranking_seen':True,'original_candidate_bytes_changed':False,'new_core_math_salvage_performed':False,
    'ancillary_verification':['Delete non-admitted .618 panel in separate copy, same algorithm/targets/starts','Check actual earliest argument for uniform-order cap and disaggregate shift costs on unchanged cells','Tighten elementary small-log Taylor remainder in fixed primorial proof; not a new analytic core'],
    'own_history_disclosure':fj(T/'OWN_HISTORY_DISCLOSURE.json'),
    'input_comparison':'B0 entails exact D01; A(D02) additive and yields the smaller closed beta ceiling via Mellin. Neither numerical ablation nor inherited proof is a blind B0 discovery baseline. See individual claim rows.',
    'claim_count':len(C),'inherited_recheck_targets':644,'inherited_finite_diagnostics':diag,'inherited_finite_or_comparator_only':44,'excluded_archival_source_objects':2}
save('review.json',review)
save('STAGE_STATUS.json',{'ready_for_review':True,'families':{k:{'status':'incomplete','claim_files':['review.md','review.json']} for k in (R,M)},'serious_attempts_documented':True})
m=S/'review.md'; main=m.read_text().split('## Exact written-source locator index')[0]
used={}
for r in C:
    for a in [r['written_source']]+r['executable_readback']:
        used[a['file']]=a
m.write_text(main+'## Exact written-source locator index\n\nFor disjoint physical-LF ranges and file types, see each row in review.json.\n\n|Restored name|Packet name|SHA-256|\n|---|---|---|\n'+''.join(f"|{f}|{a['packet_name']}|{a['sha256']}|\n" for f,a in sorted(used.items())))
print('review rows',len(C),'M-status frequencies',dict(Counter(r['M_status'] for r in C)))
if __name__=='__main__':
    save('LOCK.json',{'files':[{'path':p.name,'sha256':sha(p.read_bytes())} for p in sorted(S.iterdir()) if p.is_file() and p.name!='LOCK.json']})

