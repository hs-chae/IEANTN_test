#!/usr/bin/env python3
"""Independent exact checks for the written explicit-window error budget and bridge.
This is rational arithmetic and a reviewed written proof, not Lean or source PV.
"""
import argparse,hashlib,importlib.util,json,math,os,sys
sys.set_int_max_str_digits(1000000)
from fractions import Fraction as Q
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def log_bounds(x):
    need(x>0,'log domain');k=0
    while x>=2:x/=2;k+=1
    while x<1:x*=2;k-=1
    def core(x):
        z=(x-1)/(x+1);term=z;s=Q(0)
        for j in range(50):s+=term/(2*j+1);term*=z*z
        return 2*s,2*s+2*term/(101*(1-z*z))
    l,u=core(x);a,b=core(Q(2));return l+min(k*a,k*b),u+max(k*a,k*b)


def ep(x,n):
    term=total=Q(1)
    for j in range(1,n+1):term*=x/j;total+=term
    return total


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--numerical-receipt',type=Path,required=True)
    ap.add_argument('--fft-source',type=Path,required=True)
    ap.add_argument('--run',type=Path,required=True)
    a=ap.parse_args();need(not os.path.lexists(a.run),'fresh applicability run');a.run.mkdir(parents=True)
    d=json.loads(a.numerical_receipt.read_text())
    need(d['status']=='PASS_INDEPENDENT_GLOBAL_CHORD_NORM_AND_SLAB_ENDPOINT_MARGINS','numerical receipt did not pass')
    v={k:Q(t['exact'])for k,t in d['scalars'].items()}
    U,F0,J,H,A0,V0,V1,mu2,M,R,D=[v[k]for k in ['U','F0','J','H','A0','V0','V1','mu2','M','R','D']]
    need(0<F0<=2 and 0<U<=2 and 0<D<=2 and 0<A0<=2 and 0<M<=2 and 0<=V0<=10 and 0<=V1<=50 and 0<R<=10,'scalar applicability')
    need(sha(a.fft_source)=='abc1161d28e5b415bda13212eccf55487c753b028e613e2d52ac8fd443cd1fe4','FFT source identity')
    sp=importlib.util.spec_from_file_location('pinned_fft_applicability',a.fft_source);fft=importlib.util.module_from_spec(sp);sp.loader.exec_module(fft)
    l5,u5=fft.arctan_bounds(5,40);l239,u239=fft.arctan_bounds(239,40);pl,pu=16*l5-4*u239,16*u5-4*l239
    E21=ep(Q(21),70);E20=ep(Q(20),70);dm=Q(1,50000000)
    need(E21>1050000000 and 21/E21<dm,'d-star applicability')
    need(E20>2*pu/dm,'log(2pi/d-star)<20')
    c=Q(d.get('coefficient','4/5'));need(Q(1,2)<=c<=1,'c domain')
    pole=A0*21*(R*dm/2)**2/(1-R*dm/2)
    g1=(R*V1+2*V0)/(2*pl)
    zeros=dm*(Q(3,10)*g1+12*(2*pu*R*A0+g1))
    cut=10*dm/(2*pl);lowcut=2*A0*cut*(1-log_bounds(cut)[0])
    powers=M*(42+11*dm)**2/(2*log_bounds(Q(2))[0]*E21*(1-5*dm))*(1+R*c*42/(2*(1-6*dm)))
    need(1/(1-9*dm)<2,'support lower endpoint exceeds x/2')
    ymin=E21**2/2;trivial=dm*A0/((E21/2)*(ymin*ymin-1))
    delta_d=Q(42**2,4)/E21;zmax=Q(42)/E21;delta_log=zmax/(2-zmax)
    need(delta_d<Q('1e-6')and delta_log<Q('1e-6'),'scalar linearization errors')
    total=pole+zeros+lowcut+powers+trivial+D*delta_d+U*delta_log
    need(total<Q('.0012'),'complete additive error budget')
    need(4*(1+10*dm/42)/(1-15*dm)<Q('4.00001'),'MV multiplicative envelope')
    margins={k:Q(t['exact'])for k,t in d['margins'].items()};lo=min(margins.values())
    need(lo>0,'endpoint positivity')
    mode=d.get('mode','slab')
    if mode=='slab':
        need(set(margins)=={'42','174'},'slab endpoints');count=lo*E21/(M*174)
    else:
        need(set(margins)=={'42'}and Q(d['leading_margin'])>=0,'ray monotonicity');count=lo*E21/(M*42)
    need(count>1,'original half-open count leaves a prime after removing possible upper endpoint')
    # exp(42)<4e18: e<=partial_10+geometric tail <11/4.
    e_upper=ep(Q(1),10)+Q(1,math.factorial(11))/(1-Q(1,12))
    need(e_upper<Q(11,4)and Q(11,4)**42<4*10**18,'finite source covers analytic join')
    need(ep(Q(1),3)>Q(5,2),'2/e<4/5')
    small=[]
    for x,p,sl in [(4,5,Q(2)),(5,7,Q(11,5)),(7,11,Q(66,25))]:
        need(sl*sl<=x,'lower square-root applicability')
        margin=c*sl*log_bounds(Q(x))[0]-(p-x)
        need(margin>0,'small-x strict endpoint cover')
        need(all(p%k for k in range(2,math.isqrt(p)+1)),'small next-prime primality')
        small.append(dict(x=x,next_prime=p,positive_margin=str(margin)))
    result=dict(status='PASS_FULL_WRITTEN_APPLICABILITY_ERROR_BUDGET_STRICT_ENDPOINT_AND_FINITE_JOIN',mode=mode,coefficient=str(c),
        numerical_receipt_sha256=sha(a.numerical_receipt),controller_sha256=sha(Path(__file__)),
        errors={k:dict(exact=str(z),approx=float(z))for k,z in dict(pole=pole,zeros=zeros,lower_log_cut=lowcut,prime_powers=powers,trivial=trivial,linearization_D=D*delta_d,linearization_log=U*delta_log,total=total).items()},
        strict_half_open_count_lower=dict(exact=str(count),approx=float(count)),small_x=small,
        remaining_assumptions=['Ordinary RH','Guinand-Weil/Mellin formula with the proved affine-window strip-decay applicability','CMS Lemma9 zero count and N(10)=0, with primary correction provenance','Montgomery-Vaughan uniform interval bound as quoted in CMS(6.10)/BR4.3','Historical computational gap bound CMS(1.15), not recomputed here'],
        mathematical_continuum_reason='Slab: positive-U logarithm gives a concave margin, minimized at an endpoint. Ray: nonnegative linear slope plus U log t gives increasing margin; exp(t/2)/t increases for t>=42.',
        strict_endpoint_reason='Use original half-open prime count K>1, then discard at most the possible prime at the upper endpoint; the finite gap bridge is already strict.',
        source_first_PV=False,lean_proof=False)
    tmp=a.run/'RESULT.json.tmp';tmp.write_text(json.dumps(result,indent=2)+'\n');os.link(tmp,a.run/'RESULT.json');tmp.unlink()
    print(json.dumps(dict(status=result['status'],mode=mode,total_additive_error=float(total),strict_count_lower=float(count))))

if __name__=='__main__':main()
