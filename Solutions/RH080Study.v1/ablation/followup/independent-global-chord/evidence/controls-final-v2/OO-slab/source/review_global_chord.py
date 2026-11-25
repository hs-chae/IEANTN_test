#!/usr/bin/env python3
"""Independent written Fap slab recomputation, using a coarse global chord norm.
Reuses only the pinned integer FFT engine, not submitted normfft/readwin/margin.
No source-first PV or Lean theorem is claimed.
"""
import argparse,hashlib,importlib.util,json,os,time
from fractions import Fraction as Q
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def log_bounds(x):
    need(x>0,'log domain')
    k=0
    while x>=2:x/=2;k+=1
    while x<1:x*=2;k-=1
    def core(x):
        z=(x-1)/(x+1);term=z;s=Q(0)
        for j in range(50):s+=term/(2*j+1);term*=z*z
        return 2*s,2*s+2*term/(101*(1-z*z))
    l,u=core(x);a,b=core(Q(2))
    return l+min(k*a,k*b),u+max(k*a,k*b)


def area(l,r):
    if l>=0 and r>=0:return (l+r)/2
    if l<=0 and r<=0:return Q(0)
    return max(l,r)**2/(2*abs(l-r))


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--fft-source',type=Path,required=True)
    ap.add_argument('--witness',type=Path,required=True)
    ap.add_argument('--run',type=Path,required=True)
    ap.add_argument('--grid',type=int,default=131072)
    ap.add_argument('--mode',choices=['slab','ray'],default='slab')
    a=ap.parse_args();need(not os.path.lexists(a.run),'fresh run');a.run.mkdir(parents=True)
    need(sha(a.fft_source)=='abc1161d28e5b415bda13212eccf55487c753b028e613e2d52ac8fd443cd1fe4','FFT pin')
    expected={'slab':'9f545a294f104a1baaeccbb9bf625f6338fc020af9dce9ff7bd34352630a586a','ray':'61f745f27018ea5addbb01c1d583b128b2639b0f101d764136c98c26983c5521'}
    need(sha(a.witness)==expected[a.mode],'Witness pin')
    spec=importlib.util.spec_from_file_location('reviewed_fft',a.fft_source);fft=importlib.util.module_from_spec(spec);spec.loader.exec_module(fft)
    dat=json.loads(a.witness.read_text());vals=dat['coefficients'];scale=dat['scale'];m=dat['m'];G=a.grid;unit=fft.UNIT
    need(type(G)is int and G>=2*len(vals)and G&(G-1)==0,'grid')
    need(scale>0 and unit%scale==0,'input scale')
    nodes=[Q(x,scale)for x in vals]+[Q(0)]
    start=time.monotonic();samples=fft.real_dft([x*(unit//scale)for x in vals],G)
    amplitude=abs(nodes[0])+2*sum(map(abs,nodes[1:]));twiddle=Q(12*G,unit)
    need(Q(4*G,unit)<Q(1,2)and(G.bit_length()-1)*twiddle/2<Q(1,2),'FFT rounding applicability')
    sample_error=2*G*(twiddle*amplitude+Q(2,unit))
    integration_error=Q(80,12*G*G)*sum(j*j*abs(v)for j,v in enumerate(nodes))
    U=Q(sum(map(abs,samples)),G*unit)+sample_error+integration_error
    F0=(nodes[0]+2*sum(nodes[1:]))/m
    J=2*sum(area(nodes[j],nodes[j+1])for j in range(m,len(nodes)-1))/m
    H=max(Q(0),nodes[m])+sum(max(Q(0),max(Q(0),nodes[j+1])-max(Q(0),nodes[j]))for j in range(m,len(nodes)-1))
    A0=(abs(nodes[0])+2*sum(map(abs,nodes[1:])))/m
    slopes=[m*(r-l)for l,r in zip(nodes,nodes[1:])]+[Q(0)]
    V0=2*sum(abs(r-l)for l,r in zip(nodes,nodes[1:]))
    V1=2*(abs(slopes[0])+sum(abs(r-l)for l,r in zip(slopes,slopes[1:])))
    mu2=2*sum(abs(l)*(Q(j*j,2)+Q(j,3)+Q(1,12))+abs(r)*(Q(j*j,2)+Q(2*j,3)+Q(1,4))for j,(l,r)in enumerate(zip(nodes,nodes[1:])))/m**3
    B=Q('4.00001');c=Q(4,5)if a.mode=='slab'else Q('.851062');k=16 if a.mode=='slab'else 1;tau=Q(3,8);D=F0-B*J
    # π > 3.14159265358979323846264338327950288 is independently
    # justified by the pinned engine's rational Machin bounds (rechecked here).
    l5,u5=fft.arctan_bounds(5,40);l239,u239=fft.arctan_bounds(239,40)
    pil,pih=16*l5-4*u239,16*u5-4*l239
    need(pih*pih<10,'pi²<10')
    logk=log_bounds(Q(k))[1];q0=1-2*logk/42
    tl,tu=log_bounds(tau)
    signed_moment=V1/(2*pil*pil)-2*F0*tau*(1-tu)+40*mu2*tau**3*(Q(1,9)-tl/3)
    K=B*J*c*logk/q0+2*B*H/(k*q0)+signed_moment+Q('.0012')
    endpoints=[Q(42),Q(174)]if a.mode=='slab'else[Q(42)]
    margins={str(t):(c*D-U)*t/2+U*log_bounds(c*t/2)[0]-K for t in endpoints}
    if a.mode=='ray':need(c*D>=U,'nonnegative ray slope')
    need(all(v>0 for v in margins.values()),'independent global-chord slab margin')
    scalars=dict(U=U,F0=F0,J=J,H=H,A0=A0,V0=V0,V1=V1,mu2=mu2,M=max(map(abs,nodes)),R=Q(len(nodes)-1,m),D=D,signed_log_moment=signed_moment,
        global_chord_error=integration_error,fft_sample_error=sample_error)
    result=dict(status='PASS_INDEPENDENT_GLOBAL_CHORD_NORM_AND_SLAB_ENDPOINT_MARGINS',
        mode=a.mode,coefficient=str(c),leading_margin=str(c*D-U),scope='Directed rational numerical recomputation plus separately reviewed written continuum argument; not a Lean theorem or PV.',
        source_sha256=sha(a.fft_source),witness_sha256=sha(a.witness),controller_sha256=sha(Path(__file__)),grid=G,seconds=time.monotonic()-start,
        reused='Pinned generic integer FFT/twiddle engine only; no submitted normfft/readwin/margin functions are imported.',
        scalars={k:dict(exact=str(v),approx=float(v))for k,v in scalars.items()},margins={k:dict(exact=str(v),approx=float(v))for k,v in margins.items()})
    tmp=a.run/'RESULT.json.tmp';tmp.write_text(json.dumps(result,indent=2)+'\n');os.link(tmp,a.run/'RESULT.json');tmp.unlink()
    print(json.dumps(dict(status=result['status'],seconds=result['seconds'],U=float(U),signed_log_moment=float(signed_moment),margins={k:float(v)for k,v in margins.items()})))

if __name__=='__main__':main()
