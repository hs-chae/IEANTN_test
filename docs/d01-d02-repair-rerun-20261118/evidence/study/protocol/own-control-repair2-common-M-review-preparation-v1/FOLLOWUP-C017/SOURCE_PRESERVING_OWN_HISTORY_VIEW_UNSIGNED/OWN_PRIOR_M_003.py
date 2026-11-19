"""Independent readback and targeted checks of the locked candidate's proof obligations.
Uses exactly the candidate formulas; only ancillary audit, not a new endpoint search.
Run after replay.py (both finite sweeps required).
"""
import ast, hashlib, json, re, sys, zipfile
from pathlib import Path
from decimal import Decimal as D
S=Path(__file__).resolve().parent
C=Path(next((s for s in sys.argv[1:] if not s.startswith('--')),'/work/c017'))
sys.path.insert(0,str(C))
from profiles import *
from mertens import pi_after_cut, CUT, prime_powers
from repair_spectral import coeff, product_cost, allowance, WINS, sec_norm, finite_tail
from repair_r import verify, margin_new
from finite_joins import nxt
from repair_evaluate import r_augment, newE
def exact(name): return (C/name).read_bytes()
def receipt(name):
    q=json.loads((S/(name+'_receipt.json')).read_text())
    assert q['status']==0 and not q['stderr']
    assert hashlib.sha256(q['stdout'].encode()).hexdigest()==q['stdout_sha256']
    return q['stdout']
def readback():
    idx=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
    assert all(hashlib.sha256(exact(a['original_name'])).hexdigest()==a['sha256'] for a in idx['candidate_files'])
    print('bound candidate files',len(idx['candidate_files']))
    z=zipfile.ZipFile(C/'prior_candidate.zip')
    own=json.loads(exact('OWN_ORIGINAL_SOURCE_LOCK.json'))
    for a in own['files']:
        assert hashlib.sha256(z.read(a['path'])).hexdigest()==a['sha256']
    old=json.loads(exact('prior_review_inventory.json'))
    assert all(hashlib.sha256(z.read(n)).hexdigest()==h['sha256'] for n,h in old['reviewed_source_hashes'].items())
    print('archived own source files checked',len(z.namelist()))
    pairs=dict(source_audit='source_run',certify='analytic_run',endpoint='endpoint_run',
          finite_mertens='finite_run',finite_joins='joins_run',finite_zoom='zoom_run',evaluate='compare_run',
          repair_finite='repair_finite_run',repair_spectral='repair_spectral_run',
          repair_r='repair_r_full_run',repair_joins='repair_joins_run',repair_portfolio='repair_portfolio.json',
          repair_evaluate='repair_eval_run')
    for a,b in pairs.items():
        f=b if b.endswith('.json') else b+'.txt'
        if not (S/(a+'_receipt.json')).exists() and '--fast' in sys.argv:continue
        v=receipt(a)
        print(a,'matches exact locked stdout:',v.encode()==exact(f))
        if v.encode()!=exact(f):
            print('differences',[(i,s,t) for i,(s,t) in enumerate(zip(v.splitlines(),exact(f).decode().splitlines()),1) if s!=t][:5])
def transcription():
    root=Path('/corpus/originals')
    def tab(stem,lo,hi,w,flatten=False):
        a=next(root.glob(stem+'*.txt')).read_text().split('\n')[lo-1:hi]
        assert len(a)%w==0
        out={}
        for j in range(0,len(a),w):
            k,*v=a[j:j+w]
            k=k.replace(' ','')
            out[10**int(k[2:]) if flatten and k in ('106','107','108','109') else int(k)]=v
        return out
    def dec(x):
        return D(x.replace('−','-').replace(' ','').replace('·10','E'))
    ds=tab('Dusart',489,728,6)|tab('Dusart',742,765,6)
    pt=tab('PlattTrudgian1809',142,201,6)
    f5=tab('FKS',2317,2575,7)
    f6=tab('FKS',2593,2747,5,True)
    for u,c,k in SOURCE_DATA['steps']:
        v=ds[u][-1] if k.startswith('Dusart') else pt[u][-1] if k.startswith('PT') else f5[u][-1] if 'Table5' in k else f6[u][2]
        assert dec(v)==D(c),(u,c,v)
    for u,A,B,Cc,R,k in SOURCE_DATA['shapes']:
        expect=pt[u][1:4]+['5.573412'] if k.startswith('PT') else [f6[u][0],'1.5','2','5.5666305'] if 'Table6' in k else ['9.22022','1.5','.8476836','1']
        assert tuple(map(D,(A,B,Cc,R)))==tuple(map(dec,expect))
        # On the listed domains the stated power prefactor is at least 1 and the normalized exponent <1.
        assert I(Cc).r < I(R).power(I('.5')).l
        assert (I(A)*(I(u)/I(R)).power(I(B))).l>1
    print('all source-table transcriptions',len(SOURCE_DATA['steps']),len(SOURCE_DATA['shapes']))
def finite_tables():
    p=json.loads(exact('portfolio.json'))
    s=receipt('finite_mertens')
    start,tail=s.split('Last unproved endpoints (including one-sided prime limits)\n')
    raw,cap=tail.split('Endpoint maxima rounded upward to 0.000001\n')
    last={D(a):ast.literal_eval('['+b) for a,b in (line.split(' [') for line in raw.strip().splitlines())}
    def values(line):return list(map(D,re.findall(r"Decimal\('([^']+)'\)",line)))
    query={D(l.split()[2]):values(l) for l in start.splitlines() if l.startswith('threshold value ')}
    maxima={D(l.split()[0]):values(l) for l in cap.strip().splitlines()}
    roots=[list(map(D,line.split('root bounded by ')[1].split()[:2])) for line in receipt('finite_zoom').splitlines()]
    on=['2278381.575555466','2278381.71114184102','2278382.113038','912559.997437']
    for i,x,c in p['mertens_finite_x']:
        x,c=D(x),D(c)
        assert c>=D('.117') or (i<3 and c>=D('.10994'))
        if x==25000000: continue
        if x in maxima and x in query and max(maxima[x][i],query[x][i])<c:continue
        if any(c>=t and nxt(v[i])<=x for t,v in last.items()):continue
        if x in query and query[x][i]<c and any(c>=t and v[i]<x for t,v in last.items()):continue
        assert x==D(on[i])
        t=D('.3' if i==3 else '.2')
        assert c==t and last[t][i]<roots[i][0]<roots[i][1]<x<nxt(last[t][i])
    q=json.loads(exact('repair_portfolio.json'))
    obs={D(a):list(map(int,b)) for a,*b in (line.split() for line in receipt('repair_finite').splitlines()[1:8])}
    for c,*ons in q['mertens_common_C_P_Q_reciprocal_weighted_onset']:
        c=D(c)
        for i,x in enumerate(map(int,ons)):
            if obs[c][i]==x:continue
            assert nxt(last[c][i])==x<25000000 and obs[c][i]<=25000000
    print('independently matched finite-to-tail table entries:',len(p['mertens_finite_x']),4*len(obs))
def analytic_edges():
    from certify import P
    p=json.loads(exact('portfolio.json'))
    for k,m,B,D02 in p['ramanujan_high']:
        assert P(B,basecap,int(k),m) and P(D02,newcap,int(k),m)
    assert all(j>31 for j,c in enumerate(dN) if c<0)
    u=I(167)
    a=I(5)/32
    assert all((spectral(I(v),newcap,'5e-13')/ef(a,I(v))).r<D('.276') for v in (167,170))
    print('old convex bridge coefficient including allowance and conversion',product_cost(I('.276')+allowance(u,a),u,a))
    for cap,Cmax in ((basecap,'.006665'),(newcap,'.11625')):
        v=coeff(cap)[1]+21/I(H)
        assert v.r<D(Cmax)
        print('refined limiting coefficient with 21/H',cap,v)
    for u,c in ((I(10**13).ln(),'.002'),(I(32),'.0009'),(I(36),'.00027'),(I(40),'.00017')):
        z=I('6.33')*u*u*ef(I('.5'),u)+(4*u+2)*u*u*ef(1,u)+CUT*CUT*pi_after_cut()
        j=(z+u*u*ef(1,u))/(1-ef(1,u))
        y=j*(j/u**3).exp()
        assert y.r<D(c)
        print('pi medium branch (conversion with full denominator)',u,y.r,c)
    for u,C in ((167,'1.03e-12'),(168,'9.5e-13')):
        u=I(u)
        v,h=min(( (product_cost(spectral(u,newcap,h)/ef(a,u)+allowance(u,a),u,a)*ef(a,u)).r,h)
                  for h in ('5e-12','2e-12','1e-12','5e-13','2e-13'))
        print('fixed old comparison box with conversion',u,h,v)
        assert v<D(C)
    F=(PI/I(3000175332800)).l
    assert F>D('1.047e-12')
    for u in (167,168,189,200,1000):
        u=I(u); print('comparison scales',u,(I('.0017')*ef(I('.125'),u)).r,(I('.235')*ef(a,u)).r)
    # Literal recipe cutoffs at log 1000: redundancy does not require treating > as >=.
    u=I(1000)
    q0=I('.014')*ef(I('.125'),u)
    assert q0.r<D('1.3812e-9')
    for t,A,B,Cc,R,k in SOURCE_DATA['shapes']:
        if t==1000 and 'FKS' in k:
            r=u/I(R)
            assert q0.r<(I(A)*r.power(I(B))*ef(I(Cc),r.power(I('.5')))).l
            assert (I('.125')-I(Cc)/(2*I(R).power(I('.5'))*u.power(I('.5')))).l>0
    print('FKS log-1000 recipe-boundary rows redundant under checked B0 cap')
    print('refined power ratio at 200',I('.21614')/I('.01228')*ef(I(1)/32,I(200)))
    for t,h in (('166.4',WINS[0]),('167',WINS[1])):
        v=I(t)
        c=product_cost(sec_norm(v,newcap,h)+allowance(v,a),v,a)*ef(a,v)
        assert c.r<D('1.042e-12')
        print('refined early pointwise absolute comparison',t,h,c.r)
    q=json.loads(exact('repair_portfolio.json'))
    for k,m,B,D02 in q['ramanujan_full_k_coefficient_B0_D02']:
        for cap,v in ((basecap,B),(newcap,D02)):
            k=int(k); v=D(v)
            verify(v,cap,k,k>=30)
            assert margin_new(v,cap,k,k>=30).l>D(m)
    finite_tail()
def code_counterexample():
    x=I('1e70'); u=x.ln()
    def V(v):return v*ef(1,v)*vintegral(v)
    for cap in (basecap,newcap):
        # Reverse the written lower-bound substitutions, both pi sides from the old valid bracket.
        b1,_=p_err(u-1,cap)
        _,b0=p_err(u,cap)
        lo=V(u)-b0
        assert lo.l>0
        hi=(u**4*(u/(u-1)*(V(u-1)+b1)-lo**2)).r
        got=r_augment(u,cap).l
        assert hi<D('1.1') and got>D('737000000')
        print('x=10^70, cap',cap,'proved true scaled R upper',hi,'locked evaluator lower',got)
if __name__=='__main__':
    readback()
    transcription()
    analytic_edges()
    code_counterexample()
    if '--fast' not in sys.argv: finite_tables()
